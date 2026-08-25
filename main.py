#!/usr/bin/env python3
"""
HostBot - a production-ready Telegram Python Hosting Bot for Railway.
Single-file edition (all modules merged into one script).

Persistence: a private Telegram GROUP is the only database. No SQLite/local
files are used as the source of truth - everything (users, hosted-bot
metadata, approval history, settings) lives as JSON documents inside that
group, indexed by one pinned "index" message. State is fully reconstructed
from Telegram after every restart/redeploy.

Run with:  BOT_TOKEN=... BOT_DB_GROUP_ID=... ADMIN_ID=... python hostbot.py
"""
from __future__ import annotations

import ast
import asyncio
import hashlib
import io
import json
import logging
import os
import re
import signal
import sys
import threading
import time
import uuid
from collections import defaultdict, deque
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import DefaultDict, Deque, Optional

from telegram import (
    Bot, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaDocument, Update,
)
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application, ApplicationBuilder, CallbackQueryHandler, CommandHandler,
    ContextTypes, MessageHandler, filters,
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
logger = logging.getLogger("hostbot")


# =============================================================================
# CONFIG  (env vars only - never hardcode secrets)
# =============================================================================
def _require_env(name: str) -> str:
    val = os.environ.get(name)
    if not val:
        print(f"FATAL: required environment variable {name} is not set.", file=sys.stderr)
        sys.exit(1)
    return val


def _env_int(name: str, default: int) -> int:
    raw = os.environ.get(name)
    if raw is None or raw == "":
        return default
    try:
        return int(raw)
    except ValueError:
        logger.warning("Env var %s is not a valid int, using default %s", name, default)
        return default


BOT_TOKEN: str = _require_env("BOT_TOKEN")
BOT_DB_GROUP_ID: int = int(_require_env("BOT_DB_GROUP_ID"))
ADMIN_ID: int = int(_require_env("ADMIN_ID"))

ADMIN_PANEL_COMMAND = "admin12"

MAX_UPLOAD_SIZE_BYTES = _env_int("MAX_UPLOAD_SIZE_KB", 512) * 1024
MAX_LOG_SIZE_BYTES = _env_int("MAX_LOG_SIZE_KB", 256) * 1024

FREE_BOT_LIMIT = _env_int("FREE_BOT_LIMIT", 1)
PRIME_BOT_LIMIT = _env_int("PRIME_BOT_LIMIT", 5)

REFERRAL_REWARD_DAYS = _env_int("REFERRAL_REWARD_DAYS", 3)

BOT_CPU_SECONDS_LIMIT = _env_int("BOT_CPU_SECONDS_LIMIT", 3600)
BOT_MEMORY_BYTES_LIMIT = _env_int("BOT_MEMORY_MB_LIMIT", 256) * 1024 * 1024
BOT_MAX_PROCESSES = _env_int("BOT_MAX_SUBPROCESSES", 32)

PIP_INSTALL_TIMEOUT_SECONDS = _env_int("PIP_INSTALL_TIMEOUT_SECONDS", 120)

UPLOAD_RATE_LIMIT_PER_HOUR = _env_int("UPLOAD_RATE_LIMIT_PER_HOUR", 5)
ACTION_RATE_LIMIT_PER_MINUTE = _env_int("ACTION_RATE_LIMIT_PER_MINUTE", 20)

SUPERVISOR_INTERVAL_SECONDS = _env_int("SUPERVISOR_INTERVAL_SECONDS", 15)
INDEX_SAVE_DEBOUNCE_SECONDS = _env_int("INDEX_SAVE_DEBOUNCE_SECONDS", 2)
MAX_AUTO_RESTARTS_PER_HOUR = 5

WORKDIR_ROOT = os.environ.get("WORKDIR_ROOT", os.path.join(os.getcwd(), "hosted_bots"))
os.makedirs(WORKDIR_ROOT, exist_ok=True)

PORT = _env_int("PORT", 8080)

SUBSCRIPTION_CONTACT_TEXT = "Contact Admin for Subscription: @yatharth_78"
ALLOWED_FILENAME_RE = r"^[A-Za-z0-9_\-]{1,64}\.py$"


# =============================================================================
# SECURITY  (filename/path safety, import detection, escaping, rate limits)
# =============================================================================
FILENAME_RE = re.compile(ALLOWED_FILENAME_RE)
PACKAGE_NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,213}[A-Za-z0-9]$|^[A-Za-z0-9]$")

# Flags risky uploads for the admin to see before approving - this does NOT
# by itself make execution safe; subprocess isolation + resource limits do
# the real enforcement below.
SENSITIVE_IMPORTS = {
    "ctypes", "socket", "subprocess", "multiprocessing", "os", "sys",
    "shutil", "pty", "resource", "importlib",
}


def is_safe_filename(filename: str) -> bool:
    if not filename:
        return False
    if os.path.basename(filename) != filename:
        return False
    if ".." in filename or filename.startswith(("/", "\\", "~")):
        return False
    if os.path.isabs(filename):
        return False
    return bool(FILENAME_RE.match(filename))


def safe_join(root: str, filename: str) -> Optional[str]:
    if not is_safe_filename(filename):
        return None
    candidate = os.path.normpath(os.path.join(root, filename))
    root_abs = os.path.abspath(root)
    candidate_abs = os.path.abspath(candidate)
    if not (candidate_abs == root_abs or candidate_abs.startswith(root_abs + os.sep)):
        return None
    return candidate_abs


def detect_imports(source: str) -> list[str]:
    modules: set[str] = set()
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                modules.add(alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom):
            if node.module and node.level == 0:
                modules.add(node.module.split(".")[0])
    return sorted(modules)


def flagged_sensitive_imports(imports: list[str]) -> list[str]:
    return sorted(set(imports) & SENSITIVE_IMPORTS)


def is_valid_source(source: str) -> tuple[bool, str]:
    if not source.strip():
        return False, "File is empty."
    if len(source.encode("utf-8")) > MAX_UPLOAD_SIZE_BYTES:
        return False, f"File exceeds the {MAX_UPLOAD_SIZE_BYTES // 1024} KB limit."
    try:
        ast.parse(source)
    except SyntaxError as e:
        return False, f"Python syntax error: {e}"
    return True, ""


def is_valid_package_name(name: str) -> bool:
    name = name.strip()
    if not name or len(name) > 128:
        return False
    if any(ch in name for ch in " \t\n;&|`$(){}<>\"'\\"):
        return False
    if name.startswith("-"):
        return False
    return bool(PACKAGE_NAME_RE.match(name.split("==")[0].split(">=")[0].split("<=")[0]))


_MDV2_SPECIAL = r"_*[]()~`>#+-=|{}.!"


def escape_markdown_v2(text) -> str:
    if text is None:
        return ""
    text = str(text)
    return re.sub(f"([{re.escape(_MDV2_SPECIAL)}])", r"\\\1", text)


class RateLimiter:
    def __init__(self):
        self._hits: DefaultDict[str, Deque[float]] = defaultdict(deque)

    def allow(self, key: str, max_events: int, window_seconds: int) -> bool:
        now = time.time()
        q = self._hits[key]
        while q and now - q[0] > window_seconds:
            q.popleft()
        if len(q) >= max_events:
            return False
        q.append(now)
        return True

    def retry_after(self, key: str, window_seconds: int) -> int:
        q = self._hits.get(key)
        if not q:
            return 0
        return max(0, int(window_seconds - (time.time() - q[0])))


upload_limiter = RateLimiter()
action_limiter = RateLimiter()


def check_upload_rate(user_id: int) -> tuple[bool, int]:
    ok = upload_limiter.allow(f"upload:{user_id}", UPLOAD_RATE_LIMIT_PER_HOUR, 3600)
    return ok, upload_limiter.retry_after(f"upload:{user_id}", 3600)


def check_action_rate(user_id: int) -> tuple[bool, int]:
    ok = action_limiter.allow(f"action:{user_id}", ACTION_RATE_LIMIT_PER_MINUTE, 60)
    return ok, action_limiter.retry_after(f"action:{user_id}", 60)


# =============================================================================
# SUBSCRIPTIONS  (FREE / PRIME - no payment integration, admin-managed)
# =============================================================================
def is_prime_active(user: dict) -> bool:
    if user.get("plan") != "prime":
        return False
    expiry = user.get("prime_expiry")
    if expiry is None:
        return True
    return time.time() < expiry


def effective_plan(user: dict) -> str:
    return "prime" if is_prime_active(user) else "free"


def reconcile_expiry(user: dict) -> bool:
    if user.get("plan") == "prime" and not is_prime_active(user):
        user["plan"] = "free"
        user["prime_expiry"] = None
        return True
    return False


def bot_limit_for(user: dict) -> int:
    if user.get("bot_limit_override") is not None:
        return user["bot_limit_override"]
    return PRIME_BOT_LIMIT if effective_plan(user) == "prime" else FREE_BOT_LIMIT


def grant_prime(user: dict, days: int, granted_by: int) -> None:
    now = time.time()
    base = user.get("prime_expiry") or now
    if base < now:
        base = now
    user["plan"] = "prime"
    user["prime_expiry"] = base + days * 86400
    user["prime_granted_by"] = granted_by
    user["prime_granted_ts"] = now


def remove_prime(user: dict) -> None:
    user["plan"] = "free"
    user["prime_expiry"] = None


def extend_prime(user: dict, extra_days: int) -> None:
    now = time.time()
    base = user.get("prime_expiry") or now
    if base < now:
        base = now
    user["plan"] = "prime"
    user["prime_expiry"] = base + extra_days * 86400


def set_custom_expiry(user: dict, expiry_ts: float) -> None:
    user["plan"] = "prime"
    user["prime_expiry"] = expiry_ts


def format_status(user: dict) -> str:
    plan = effective_plan(user)
    limit = bot_limit_for(user)
    lines = [f"Plan: {plan.upper()}", f"Bot limit: {limit}"]
    if plan == "prime" and user.get("prime_expiry"):
        remaining = user["prime_expiry"] - time.time()
        days = max(0, int(remaining // 86400))
        hours = max(0, int((remaining % 86400) // 3600))
        lines.append(f"Prime expires in: {days}d {hours}h")
    lines.append("")
    lines.append(SUBSCRIPTION_CONTACT_TEXT)
    return "\n".join(lines)


# =============================================================================
# REFERRAL SYSTEM
# =============================================================================
def make_referral_code(user_id: int) -> str:
    h = hashlib.sha256(f"ref-{user_id}-{BOT_TOKEN[:8]}".encode()).hexdigest()
    return f"{user_id}{h[:6]}"


def make_referral_link(bot_username: str, user_id: int) -> str:
    code = make_referral_code(user_id)
    return f"https://t.me/{bot_username}?start=ref_{code}"


def parse_start_payload(payload: str) -> Optional[str]:
    if payload and payload.startswith("ref_"):
        return payload[len("ref_"):]
    return None


async def apply_referral(storage: "GroupStorage", new_user: dict, referral_code: str) -> tuple[bool, str]:
    referrer_id = storage.user_id_by_referral_code(referral_code)
    if referrer_id is None:
        return False, "Invalid referral code."
    if referrer_id == new_user["user_id"]:
        return False, "Self-referral is not allowed."
    if new_user.get("referred_by") is not None:
        return False, "Referral already recorded for this account."

    referrer = await storage.get_user(referrer_id)
    if referrer is None:
        return False, "Referrer no longer exists."

    new_user["referred_by"] = referrer_id
    referrer["referral_count"] = referrer.get("referral_count", 0) + 1
    extend_prime(referrer, REFERRAL_REWARD_DAYS)
    await storage.save_user(referrer)
    return True, f"Referral applied! Rewarded user {referrer_id} with {REFERRAL_REWARD_DAYS} day(s) of Prime."


# =============================================================================
# STORAGE  (private Telegram group as the persistent database)
# =============================================================================
INDEX_PIN_MARKER = "HOSTBOT_INDEX_V1"
APPROVAL_LOG_MARKER = "HOSTBOT_APPROVAL_LOG_V1"
MAX_APPROVAL_LOG_ENTRIES = 500


def _default_index() -> dict:
    return {
        "marker": INDEX_PIN_MARKER,
        "service_start_ts": time.time(),
        "maintenance_mode": False,
        "next_bot_seq": 1,
        "settings": {
            "free_bot_limit": FREE_BOT_LIMIT,
            "prime_bot_limit": PRIME_BOT_LIMIT,
            "referral_reward_days": REFERRAL_REWARD_DAYS,
        },
        "users": {},
        "bots": {},
        "referral_codes": {},
        "approval_log_ref": None,
        "last_backup_ts": None,
    }


class GroupStorage:
    """Async wrapper around the DB-group persistence protocol.

    - The pinned index document holds only {message_id, file_id} pointers.
    - Each user/bot record is its own small JSON document message.
    - Records are updated in place with edit_message_media (stable message_id).
    - Reads use bot.get_file(file_id) -> download_to_memory, which works even
      with empty RAM right after a redeploy.
    """

    def __init__(self, bot: Bot, group_id: int):
        self.bot = bot
        self.group_id = group_id
        self.index: dict = _default_index()
        self.index_message_id: Optional[int] = None
        self._lock = asyncio.Lock()
        self._dirty = False
        self._save_task: Optional[asyncio.Task] = None

    async def _send_json(self, data: dict, filename: str, caption: str = "") -> tuple[int, str]:
        buf = io.BytesIO(json.dumps(data, indent=2).encode("utf-8"))
        buf.name = filename
        msg = await self.bot.send_document(
            chat_id=self.group_id, document=buf, filename=filename,
            caption=caption[:1024] if caption else None, disable_notification=True,
        )
        return msg.message_id, msg.document.file_id

    async def _edit_json(self, message_id: int, data: dict, filename: str) -> str:
        buf = io.BytesIO(json.dumps(data, indent=2).encode("utf-8"))
        buf.name = filename
        media = InputMediaDocument(media=buf, filename=filename)
        try:
            msg = await self.bot.edit_message_media(chat_id=self.group_id, message_id=message_id, media=media)
            return msg.document.file_id
        except BadRequest as e:
            logger.warning("edit_message_media failed for %s (%s); recreating", message_id, e)
            new_id, file_id = await self._send_json(data, filename)
            return f"__RECREATED__:{new_id}:{file_id}"

    async def _download_json(self, file_id: str) -> dict:
        f = await self.bot.get_file(file_id)
        buf = io.BytesIO()
        await f.download_to_memory(out=buf)
        buf.seek(0)
        return json.loads(buf.read().decode("utf-8"))

    async def bootstrap(self) -> None:
        found = await self._find_pinned_index()
        if found is None:
            logger.info("No existing index found in DB group; creating a new one.")
            self.index = _default_index()
            msg_id, _ = await self._send_json(self.index, "hostbot_index.json",
                                               caption="📌 HostBot persistent index — do not delete.")
            try:
                await self.bot.pin_chat_message(chat_id=self.group_id, message_id=msg_id,
                                                 disable_notification=True)
            except TelegramError as e:
                logger.warning("Could not pin index message: %s", e)
            self.index_message_id = msg_id
        else:
            self.index_message_id, self.index = found
            logger.info("Restored index from pinned message %s", self.index_message_id)

    async def _find_pinned_index(self) -> Optional[tuple[int, dict]]:
        try:
            chat = await self.bot.get_chat(self.group_id)
        except TelegramError as e:
            logger.error("Cannot access DB group: %s", e)
            return None
        pinned = getattr(chat, "pinned_message", None)
        if pinned is None or not pinned.document:
            return None
        try:
            data = await self._download_json(pinned.document.file_id)
        except Exception as e:
            logger.error("Failed to parse pinned index document: %s", e)
            return None
        if data.get("marker") != INDEX_PIN_MARKER:
            return None
        return pinned.message_id, data

    async def save_index(self) -> None:
        async with self._lock:
            file_id = await self._edit_json(self.index_message_id, self.index, "hostbot_index.json")
            if isinstance(file_id, str) and file_id.startswith("__RECREATED__"):
                _, new_id, _fid = file_id.split(":")
                self.index_message_id = int(new_id)
                try:
                    await self.bot.pin_chat_message(chat_id=self.group_id, message_id=self.index_message_id,
                                                      disable_notification=True)
                except TelegramError:
                    pass

    def mark_dirty(self) -> None:
        self._dirty = True
        if self._save_task is None or self._save_task.done():
            self._save_task = asyncio.create_task(self._debounced_save())

    async def _debounced_save(self) -> None:
        await asyncio.sleep(INDEX_SAVE_DEBOUNCE_SECONDS)
        if self._dirty:
            self._dirty = False
            try:
                await self.save_index()
            except Exception:
                logger.exception("Failed to save index")

    async def get_user(self, user_id: int) -> Optional[dict]:
        ref = self.index["users"].get(str(user_id))
        if ref is None:
            return None
        try:
            return await self._download_json(ref["file_id"])
        except Exception:
            logger.exception("Failed to load user %s", user_id)
            return None

    async def create_user(self, record: dict) -> None:
        user_id = record["user_id"]
        msg_id, file_id = await self._send_json(record, f"user_{user_id}.json",
                                                  caption=f"👤 User record {user_id}")
        self.index["users"][str(user_id)] = {"message_id": msg_id, "file_id": file_id}
        code = record.get("referral_code")
        if code:
            self.index["referral_codes"][code] = user_id
        self.mark_dirty()

    async def save_user(self, record: dict) -> None:
        user_id = record["user_id"]
        ref = self.index["users"].get(str(user_id))
        if ref is None:
            await self.create_user(record)
            return
        file_id = await self._edit_json(ref["message_id"], record, f"user_{user_id}.json")
        if isinstance(file_id, str) and file_id.startswith("__RECREATED__"):
            _, new_id, fid = file_id.split(":")
            self.index["users"][str(user_id)] = {"message_id": int(new_id), "file_id": fid}
        self.mark_dirty()

    async def all_user_ids(self) -> list[int]:
        return [int(uid) for uid in self.index["users"].keys()]

    def user_id_by_referral_code(self, code: str) -> Optional[int]:
        return self.index["referral_codes"].get(code)

    async def get_bot(self, bot_id: str) -> Optional[dict]:
        ref = self.index["bots"].get(bot_id)
        if ref is None:
            return None
        try:
            return await self._download_json(ref["file_id"])
        except Exception:
            logger.exception("Failed to load bot record %s", bot_id)
            return None

    async def create_bot(self, record: dict) -> None:
        bot_id = record["bot_id"]
        msg_id, file_id = await self._send_json(record, f"bot_{bot_id}.json",
                                                  caption=f"🤖 Bot record {bot_id} (owner {record['owner_id']})")
        self.index["bots"][bot_id] = {"message_id": msg_id, "file_id": file_id, "owner_id": record["owner_id"]}
        self.mark_dirty()

    async def save_bot(self, record: dict) -> None:
        bot_id = record["bot_id"]
        ref = self.index["bots"].get(bot_id)
        if ref is None:
            await self.create_bot(record)
            return
        file_id = await self._edit_json(ref["message_id"], record, f"bot_{bot_id}.json")
        if isinstance(file_id, str) and file_id.startswith("__RECREATED__"):
            _, new_id, fid = file_id.split(":")
            self.index["bots"][bot_id] = {"message_id": int(new_id), "file_id": fid, "owner_id": record["owner_id"]}
        self.mark_dirty()

    async def delete_bot(self, bot_id: str) -> None:
        ref = self.index["bots"].pop(bot_id, None)
        self.mark_dirty()
        if ref:
            try:
                await self.bot.delete_message(chat_id=self.group_id, message_id=ref["message_id"])
            except TelegramError:
                pass

    def bot_ids_for_owner(self, owner_id: int) -> list[str]:
        return [bid for bid, ref in self.index["bots"].items() if ref["owner_id"] == owner_id]

    def all_bot_ids(self) -> list[str]:
        return list(self.index["bots"].keys())

    async def store_file(self, content: bytes, filename: str, caption: str = "") -> str:
        buf = io.BytesIO(content)
        buf.name = filename
        msg = await self.bot.send_document(chat_id=self.group_id, document=buf, filename=filename,
                                             caption=caption[:1024] if caption else None,
                                             disable_notification=True)
        return msg.document.file_id

    async def download_file(self, file_id: str) -> bytes:
        f = await self.bot.get_file(file_id)
        buf = io.BytesIO()
        await f.download_to_memory(out=buf)
        return buf.getvalue()

    async def append_approval_log(self, entry: dict) -> None:
        ref = self.index.get("approval_log_ref")
        if ref is None:
            log = {"marker": APPROVAL_LOG_MARKER, "entries": [entry]}
            msg_id, file_id = await self._send_json(log, "approval_log.json", caption="📋 Approval history")
            self.index["approval_log_ref"] = {"message_id": msg_id, "file_id": file_id}
            self.mark_dirty()
            return
        try:
            log = await self._download_json(ref["file_id"])
        except Exception:
            log = {"marker": APPROVAL_LOG_MARKER, "entries": []}
        entries = log.get("entries", [])
        entries.append(entry)
        entries = entries[-MAX_APPROVAL_LOG_ENTRIES:]
        log["entries"] = entries
        file_id = await self._edit_json(ref["message_id"], log, "approval_log.json")
        if isinstance(file_id, str) and file_id.startswith("__RECREATED__"):
            _, new_id, fid = file_id.split(":")
            self.index["approval_log_ref"] = {"message_id": int(new_id), "file_id": fid}
        self.mark_dirty()

    async def get_approval_log(self, limit: int = 20) -> list[dict]:
        ref = self.index.get("approval_log_ref")
        if ref is None:
            return []
        try:
            log = await self._download_json(ref["file_id"])
        except Exception:
            return []
        return log.get("entries", [])[-limit:]

    async def backup_snapshot(self) -> str:
        snapshot = dict(self.index)
        snapshot["backup_ts"] = time.time()
        _, file_id = await self._send_json(snapshot, f"backup_{int(time.time())}.json",
                                            caption="💾 Manual backup snapshot")
        self.index["last_backup_ts"] = snapshot["backup_ts"]
        self.mark_dirty()
        return file_id

    async def rebuild_index_from_scratch(self) -> dict:
        """Telegram Bot API cannot list arbitrary chat history, so a true
        rebuild-from-messages isn't possible. This instead prunes any
        reference whose file no longer resolves and reports the result."""
        report = {"users_checked": 0, "users_pruned": 0, "bots_checked": 0, "bots_pruned": 0}
        for uid, ref in list(self.index["users"].items()):
            report["users_checked"] += 1
            try:
                await self.bot.get_file(ref["file_id"])
            except TelegramError:
                del self.index["users"][uid]
                report["users_pruned"] += 1
        for bid, ref in list(self.index["bots"].items()):
            report["bots_checked"] += 1
            try:
                await self.bot.get_file(ref["file_id"])
            except TelegramError:
                del self.index["bots"][bid]
                report["bots_pruned"] += 1
        self.mark_dirty()
        await self.save_index()
        return report


# =============================================================================
# PROCESS MANAGER  (per-user isolated subprocess execution)
# =============================================================================
def _resource_limits_preexec():
    """Runs in the child, right after fork/before exec (POSIX only)."""
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CPU, (BOT_CPU_SECONDS_LIMIT, BOT_CPU_SECONDS_LIMIT))
        resource.setrlimit(resource.RLIMIT_AS, (BOT_MEMORY_BYTES_LIMIT, BOT_MEMORY_BYTES_LIMIT))
        resource.setrlimit(resource.RLIMIT_NPROC, (BOT_MAX_PROCESSES, BOT_MAX_PROCESSES))
        os.setsid()
    except Exception:
        pass  # best effort - some containers restrict this


class RunningBot:
    __slots__ = ("bot_id", "proc", "workdir", "started_ts", "log_path", "owner_id")

    def __init__(self, bot_id, proc, workdir, started_ts, log_path, owner_id):
        self.bot_id = bot_id
        self.proc = proc
        self.workdir = workdir
        self.started_ts = started_ts
        self.log_path = log_path
        self.owner_id = owner_id


class ProcessManager:
    def __init__(self):
        self._running: dict[str, RunningBot] = {}

    def is_running(self, bot_id: str) -> bool:
        rb = self._running.get(bot_id)
        return rb is not None and rb.proc.returncode is None

    def workdir_for(self, owner_id: int, bot_id: str) -> str:
        path = os.path.join(WORKDIR_ROOT, str(owner_id), bot_id)
        os.makedirs(path, exist_ok=True)
        return path

    async def install_requirements(self, workdir: str, requirements_text: str) -> tuple[bool, str]:
        lines = [ln.strip() for ln in requirements_text.splitlines()
                 if ln.strip() and not ln.strip().startswith("#")]
        for ln in lines:
            if not is_valid_package_name(ln):
                return False, f"Rejected unsafe package spec: {ln!r}"
        if not lines:
            return True, "No dependencies to install."
        target = os.path.join(workdir, "site-packages")
        os.makedirs(target, exist_ok=True)
        cmd = [sys.executable, "-m", "pip", "install", "--no-input",
               "--disable-pip-version-check", "--target", target, *lines]
        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT, cwd=workdir,
            )
            try:
                out, _ = await asyncio.wait_for(proc.communicate(), timeout=PIP_INSTALL_TIMEOUT_SECONDS)
            except asyncio.TimeoutError:
                proc.kill()
                return False, "pip install timed out."
            return proc.returncode == 0, out.decode(errors="replace")[-3500:]
        except Exception as e:
            logger.exception("pip install failed")
            return False, f"pip install error: {e}"

    async def list_installed_packages(self, workdir: str) -> list[str]:
        target = os.path.join(workdir, "site-packages")
        if not os.path.isdir(target):
            return []
        names = set()
        for entry in os.listdir(target):
            if entry.endswith(".dist-info") or entry.endswith(".egg-info"):
                names.add(entry.split("-")[0])
        return sorted(names)

    async def start(self, bot_id: str, owner_id: int, script_path: str) -> tuple[bool, str]:
        if self.is_running(bot_id):
            return False, "Already running."
        workdir = self.workdir_for(owner_id, bot_id)
        site_packages = os.path.join(workdir, "site-packages")
        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "PYTHONPATH": site_packages if os.path.isdir(site_packages) else "",
            "PYTHONUNBUFFERED": "1",
            "HOME": workdir,
            "HOSTED_BOT_ID": bot_id,
        }
        log_path = os.path.join(workdir, "output.log")
        try:
            log_f = open(log_path, "ab", buffering=0)
        except OSError as e:
            return False, f"Could not open log file: {e}"

        kwargs = {}
        if os.name == "posix":
            kwargs["preexec_fn"] = _resource_limits_preexec
        try:
            proc = await asyncio.create_subprocess_exec(
                sys.executable, "-u", os.path.basename(script_path),
                cwd=workdir, env=env, stdout=log_f, stderr=log_f, **kwargs,
            )
        except Exception as e:
            log_f.close()
            logger.exception("Failed to start bot %s", bot_id)
            return False, f"Failed to start: {e}"
        finally:
            log_f.close()

        self._running[bot_id] = RunningBot(bot_id, proc, workdir, time.time(), log_path, owner_id)
        return True, "Started."

    async def stop(self, bot_id: str, timeout: float = 5.0) -> tuple[bool, str]:
        rb = self._running.get(bot_id)
        if rb is None or rb.proc.returncode is not None:
            self._running.pop(bot_id, None)
            return False, "Not running."
        pid = rb.proc.pid
        try:
            if os.name == "posix":
                try:
                    os.killpg(os.getpgid(pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
            else:
                rb.proc.terminate()
            try:
                await asyncio.wait_for(rb.proc.wait(), timeout=timeout)
            except asyncio.TimeoutError:
                if os.name == "posix":
                    try:
                        os.killpg(os.getpgid(pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                else:
                    rb.proc.kill()
                await rb.proc.wait()
        finally:
            self._running.pop(bot_id, None)
        return True, "Stopped."

    def pid(self, bot_id: str) -> Optional[int]:
        rb = self._running.get(bot_id)
        return rb.proc.pid if rb else None

    def uptime_seconds(self, bot_id: str) -> Optional[float]:
        rb = self._running.get(bot_id)
        return None if rb is None else time.time() - rb.started_ts

    def read_log_tail(self, bot_id: str, owner_id: int, max_bytes: int = 3500) -> str:
        workdir = self.workdir_for(owner_id, bot_id)
        log_path = os.path.join(workdir, "output.log")
        if not os.path.exists(log_path):
            return "(no logs yet)"
        with open(log_path, "rb") as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - max_bytes))
            data = f.read()
        return data.decode(errors="replace") or "(no logs yet)"

    def clear_log(self, bot_id: str, owner_id: int) -> None:
        workdir = self.workdir_for(owner_id, bot_id)
        try:
            open(os.path.join(workdir, "output.log"), "w").close()
        except OSError:
            pass

    def rotate_log_if_needed(self, bot_id: str, owner_id: int) -> None:
        workdir = self.workdir_for(owner_id, bot_id)
        log_path = os.path.join(workdir, "output.log")
        try:
            if os.path.exists(log_path) and os.path.getsize(log_path) > MAX_LOG_SIZE_BYTES:
                tail = self.read_log_tail(bot_id, owner_id, max_bytes=MAX_LOG_SIZE_BYTES // 2)
                with open(log_path, "w") as f:
                    f.write("...[log rotated]...\n")
                    f.write(tail)
        except OSError:
            pass

    def all_running_ids(self) -> list[str]:
        return [bid for bid, rb in self._running.items() if rb.proc.returncode is None]


process_manager = ProcessManager()


# =============================================================================
# SUPERVISOR  (crash detection, auto-restart, log rotation)
# =============================================================================
class Supervisor:
    def __init__(self, storage: GroupStorage, notifier=None):
        self.storage = storage
        self.notifier = notifier
        self._task: Optional[asyncio.Task] = None
        self._restart_windows: dict[str, list[float]] = {}

    def start(self):
        self._task = asyncio.create_task(self._loop())

    async def stop(self):
        if self._task:
            self._task.cancel()

    async def _loop(self):
        while True:
            try:
                await self._tick()
            except asyncio.CancelledError:
                raise
            except Exception:
                logger.exception("Supervisor tick failed")
            await asyncio.sleep(SUPERVISOR_INTERVAL_SECONDS)

    async def _tick(self):
        for bot_id in list(self.storage.index["bots"].keys()):
            record = await self.storage.get_bot(bot_id)
            if record is None:
                continue
            was_marked_running = record.get("status") == "running"
            is_actually_running = process_manager.is_running(bot_id)

            if was_marked_running and not is_actually_running:
                record["status"] = "crashed"
                record["pid"] = None
                await self.storage.save_bot(record)
                logger.info("Detected crash for bot %s", bot_id)
                if record.get("auto_restart"):
                    await self._maybe_restart(record)
                elif self.notifier:
                    await self.notifier(record["owner_id"], f"⚠️ Your bot '{record['filename']}' crashed.")
            elif is_actually_running:
                process_manager.rotate_log_if_needed(bot_id, record["owner_id"])

    async def _maybe_restart(self, record: dict):
        bot_id = record["bot_id"]
        now = time.time()
        window = self._restart_windows.setdefault(bot_id, [])
        window[:] = [t for t in window if now - t < 3600]
        if len(window) >= MAX_AUTO_RESTARTS_PER_HOUR:
            logger.warning("Bot %s exceeded auto-restart budget, giving up", bot_id)
            if self.notifier:
                await self.notifier(record["owner_id"],
                                     f"🛑 '{record['filename']}' keeps crashing and hit the "
                                     f"auto-restart limit. It has been left stopped.")
            return
        window.append(now)
        record["restart_count"] = record.get("restart_count", 0) + 1
        workdir = process_manager.workdir_for(record["owner_id"], bot_id)
        script_path = os.path.join(workdir, record["filename"])
        ok, msg = await process_manager.start(bot_id, record["owner_id"], script_path)
        record["status"] = "running" if ok else "crashed"
        record["pid"] = process_manager.pid(bot_id)
        record["last_start_ts"] = time.time()
        await self.storage.save_bot(record)
        if self.notifier:
            note = "🔄 Auto-restarted" if ok else f"❌ Auto-restart failed: {msg}"
            await self.notifier(record["owner_id"], f"{note}: '{record['filename']}'")


# =============================================================================
# SHARED HELPER
# =============================================================================
def _storage(context: ContextTypes.DEFAULT_TYPE) -> GroupStorage:
    return context.application.bot_data["storage"]


def _format_duration(seconds: float) -> str:
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


def _back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="menu:main")]])


HELP_TEXT = (
    "📖 Help\n\n"
    "1. Send me a .py file to upload your bot.\n"
    "2. Wait for admin approval (you'll be notified).\n"
    "3. Once approved, use 'My Bots' to Start/Stop/Restart it.\n"
    "4. If your bot needs packages, also send a requirements.txt right "
    "after your .py file, or use 'Manage Packages' from the bot menu.\n\n"
    "Commands:\n"
    "/start - main menu\n"
    "/mybots - list your hosted bots\n"
    "/status - your subscription status\n"
    "/referral - your referral link\n"
    "/help - this message\n"
)


def _bot_status_emoji(status: str) -> str:
    return {"pending": "⏳", "approved": "🟡", "running": "🟢",
            "stopped": "🔴", "rejected": "🚫", "crashed": "💥"}.get(status, "⚪")


# =============================================================================
# USER HANDLERS
# =============================================================================
async def get_or_create_user(context, update: Update) -> tuple[dict, bool]:
    storage = _storage(context)
    tg_user = update.effective_user
    user = await storage.get_user(tg_user.id)
    if user is None:
        user = {
            "user_id": tg_user.id, "username": tg_user.username or "", "joined_ts": time.time(),
            "plan": "free", "prime_expiry": None, "bot_limit_override": None,
            "referral_code": make_referral_code(tg_user.id), "referred_by": None,
            "referral_count": 0, "banned": False,
        }
        await storage.create_user(user)
        return user, True
    changed = reconcile_expiry(user)
    if user.get("username") != (tg_user.username or ""):
        user["username"] = tg_user.username or ""
        changed = True
    if changed:
        await storage.save_user(user)
    return user, False


def main_menu_keyboard(is_admin: bool) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("⬆️ Upload Bot", callback_data="menu:upload"),
         InlineKeyboardButton("🤖 My Bots", callback_data="menu:mybots")],
        [InlineKeyboardButton("💳 Subscription", callback_data="menu:sub"),
         InlineKeyboardButton("🎁 Referral", callback_data="menu:referral")],
        [InlineKeyboardButton("🖥 Server Status", callback_data="menu:server"),
         InlineKeyboardButton("❓ Help", callback_data="menu:help")],
        [InlineKeyboardButton("📩 Contact Admin", callback_data="menu:contact")],
    ]
    if is_admin:
        rows.append([InlineKeyboardButton("🛠 Admin Panel", callback_data="admin:open")])
    return InlineKeyboardMarkup(rows)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, is_new = await get_or_create_user(context, update)
    storage = _storage(context)
    if context.args:
        code = parse_start_payload(context.args[0])
        if code and is_new:
            ok, msg = await apply_referral(storage, user, code)
            if ok:
                await storage.save_user(user)
            await update.message.reply_text(("✅ " if ok else "ℹ️ ") + msg)

    is_admin = update.effective_user.id == ADMIN_ID
    text = ("👋 *Welcome to HostBot\\!*\n\n"
            "Upload a `.py` file and I'll host it for you after admin approval\\.\n\n"
            "Use the menu below to get started\\.")
    await update.message.reply_text(text, parse_mode="MarkdownV2", reply_markup=main_menu_keyboard(is_admin))


async def show_main_menu(update_or_query, context: ContextTypes.DEFAULT_TYPE, edit=False):
    uid = update_or_query.from_user.id if hasattr(update_or_query, "from_user") else update_or_query.effective_user.id
    kb = main_menu_keyboard(uid == ADMIN_ID)
    text = "🏠 *Main Menu*"
    if edit:
        await update_or_query.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    else:
        await update_or_query.message.reply_text(text, parse_mode="MarkdownV2", reply_markup=kb)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(HELP_TEXT)


async def render_my_bots(context, user_id: int):
    storage = _storage(context)
    bot_ids = storage.bot_ids_for_owner(user_id)
    if not bot_ids:
        return "You have no hosted bots yet. Upload a .py file to get started.", None
    rows, lines = [], ["🤖 *Your Bots*\n"]
    for bid in bot_ids:
        rec = await storage.get_bot(bid)
        if rec is None:
            continue
        emoji = _bot_status_emoji(rec["status"])
        lines.append(f"{emoji} `{rec['filename']}` — {rec['status']}")
        rows.append([InlineKeyboardButton(f"{emoji} {rec['filename']}", callback_data=f"bot:info:{bid}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="menu:main")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


def bot_detail_keyboard(rec: dict) -> InlineKeyboardMarkup:
    bid = rec["bot_id"]
    running = rec["status"] == "running"
    rows = []
    if rec["status"] in ("approved", "stopped", "crashed"):
        rows.append([InlineKeyboardButton("▶️ Start", callback_data=f"bot:start:{bid}")])
    if running:
        rows.append([InlineKeyboardButton("⏹ Stop", callback_data=f"bot:stop:{bid}"),
                     InlineKeyboardButton("🔁 Restart", callback_data=f"bot:restart:{bid}")])
    rows.append([InlineKeyboardButton("📜 Logs", callback_data=f"bot:logs:{bid}"),
                 InlineKeyboardButton("🧹 Clear Logs", callback_data=f"bot:clearlogs:{bid}")])
    rows.append([InlineKeyboardButton("📦 Packages", callback_data=f"bot:pkgs:{bid}"),
                 InlineKeyboardButton("⬇️ Download", callback_data=f"bot:download:{bid}")])
    auto = "🔛 Auto-restart: ON" if rec.get("auto_restart") else "🔘 Auto-restart: OFF"
    rows.append([InlineKeyboardButton(auto, callback_data=f"bot:toggleauto:{bid}")])
    rows.append([InlineKeyboardButton("🗑 Delete", callback_data=f"bot:delconfirm:{bid}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="menu:mybots")])
    return InlineKeyboardMarkup(rows)


async def render_bot_detail(context, bid: str):
    storage = _storage(context)
    rec = await storage.get_bot(bid)
    if rec is None:
        return None
    emoji = _bot_status_emoji(rec["status"])
    uptime = process_manager.uptime_seconds(bid)
    uptime_str = _format_duration(uptime) if uptime is not None else "—"
    pid = process_manager.pid(bid) or rec.get("pid") or "—"
    text = (
        f"{emoji} *{escape_markdown_v2(rec['filename'])}*\n\n"
        f"Status: `{rec['status']}`\n"
        f"PID: `{pid}`\n"
        f"Uptime: `{uptime_str}`\n"
        f"Restarts: `{rec.get('restart_count', 0)}`\n"
        f"Uploaded: `{time.strftime('%Y-%m-%d %H:%M', time.gmtime(rec['upload_ts']))} UTC`\n"
        f"Detected imports: `{', '.join(rec.get('imports', [])) or 'none'}`\n"
    )
    if rec["status"] == "rejected":
        text += f"\nRejection reason: {escape_markdown_v2(rec.get('reject_reason', ''))}"
    if rec["status"] == "pending":
        text += "\n_Awaiting admin approval\\._"
    return text, bot_detail_keyboard(rec)


async def cmd_mybots(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await get_or_create_user(context, update)
    text, kb = await render_my_bots(context, update.effective_user.id)
    await update.message.reply_text(text, parse_mode="MarkdownV2" if kb else None, reply_markup=kb)


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, _ = await get_or_create_user(context, update)
    await update.message.reply_text(format_status(user))


async def cmd_referral(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, _ = await get_or_create_user(context, update)
    me = await context.bot.get_me()
    link = make_referral_link(me.username, user["user_id"])
    text = (f"🎁 Your referral link:\n{link}\n\n"
            f"Successful referrals: {user.get('referral_count', 0)}\n"
            f"Reward per referral: {REFERRAL_REWARD_DAYS} day(s) of Prime")
    await update.message.reply_text(text)


async def cmd_server_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    storage = _storage(context)
    start_ts = storage.index.get("service_start_ts", time.time())
    uptime = _format_duration(time.time() - start_ts)
    text = ("🟢 Service Online\n"
            f"⏱ Uptime: {uptime}\n"
            f"🤖 Hosted bots: {len(storage.all_bot_ids())}\n"
            f"▶️ Currently running: {len(process_manager.all_running_ids())}\n"
            f"🛠 Maintenance mode: {'ON' if storage.index.get('maintenance_mode') else 'OFF'}")
    await update.message.reply_text(text)


async def cmd_contact(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"📩 {SUBSCRIPTION_CONTACT_TEXT}")


# =============================================================================
# UPLOAD HANDLER
# =============================================================================
async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, _ = await get_or_create_user(context, update)
    doc = update.message.document
    storage = _storage(context)

    if storage.index.get("maintenance_mode") and update.effective_user.id != ADMIN_ID:
        await update.message.reply_text("🛠 The service is in maintenance mode. Please try again later.")
        return
    if user.get("banned"):
        await update.message.reply_text("🚫 Your account is banned from uploading.")
        return

    filename = doc.file_name or ""

    if filename.lower() == "requirements.txt":
        await _handle_requirements(update, context, doc)
        return

    if not filename.lower().endswith(".py"):
        await update.message.reply_text("❌ Only .py files (and requirements.txt) are accepted.")
        return
    if not is_safe_filename(filename):
        await update.message.reply_text("❌ Invalid filename. Use only letters, numbers, `_` and `-`, ending in `.py`.")
        return

    ok, retry_after = check_upload_rate(user["user_id"])
    if not ok:
        await update.message.reply_text(f"⏳ Upload rate limit reached. Try again in {retry_after}s.")
        return
    if doc.file_size and doc.file_size > MAX_UPLOAD_SIZE_BYTES:
        await update.message.reply_text(f"❌ File too large. Max size is {MAX_UPLOAD_SIZE_BYTES // 1024} KB.")
        return

    existing = storage.bot_ids_for_owner(user["user_id"])
    active = []
    for bid in existing:
        rec = await storage.get_bot(bid)
        if rec and rec["status"] != "rejected":
            active.append(rec)
    limit = bot_limit_for(user)
    if len(active) >= limit:
        await update.message.reply_text(
            f"❌ You've reached your bot limit ({limit}). Upgrade to Prime or remove a bot.\n\n{SUBSCRIPTION_CONTACT_TEXT}")
        return

    tg_file = await doc.get_file()
    raw = await tg_file.download_as_bytearray()
    try:
        source = bytes(raw).decode("utf-8")
    except UnicodeDecodeError:
        await update.message.reply_text("❌ File must be valid UTF-8 Python source.")
        return

    valid, reason = is_valid_source(source)
    if not valid:
        await update.message.reply_text(f"❌ Upload rejected: {reason}")
        return

    imports = detect_imports(source)
    flagged = flagged_sensitive_imports(imports)

    bot_id = uuid.uuid4().hex[:12]
    file_id = await storage.store_file(bytes(raw), filename, caption=f"Uploaded by {user['user_id']}")

    record = {
        "bot_id": bot_id, "owner_id": user["user_id"], "filename": filename, "file_id": file_id,
        "requirements_file_id": None, "size_bytes": len(raw), "imports": imports, "status": "pending",
        "upload_ts": time.time(), "approved_by": None, "approved_ts": None, "reject_reason": None,
        "pid": None, "auto_restart": False, "restart_count": 0, "last_start_ts": None,
        "log_file_id": None, "installed_packages": [],
    }
    await storage.create_bot(record)
    context.user_data["last_uploaded_bot_id"] = bot_id

    await update.message.reply_text(
        "✅ Upload received! It has been sent to the admin for approval.\n"
        "You'll be notified once it's reviewed.\n\n"
        "If your bot needs extra packages, send a requirements.txt now."
    )

    warn = f"\n⚠️ Sensitive imports detected: {', '.join(flagged)}" if flagged else ""
    admin_text = (
        f"🆕 *New bot upload*\n\n"
        f"User ID: `{user['user_id']}`\n"
        f"Username: @{escape_markdown_v2(user.get('username') or 'unknown')}\n"
        f"Filename: `{filename}`\n"
        f"Size: `{len(raw)} bytes`\n"
        f"Imports: `{', '.join(imports) or 'none'}`\n"
        f"Upload time: `{time.strftime('%Y-%m-%d %H:%M:%S UTC')}`"
        + (escape_markdown_v2(warn) if warn else "")
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Approve", callback_data=f"approve:{bot_id}"),
        InlineKeyboardButton("❌ Reject", callback_data=f"reject:{bot_id}"),
    ]])
    try:
        await context.bot.send_document(chat_id=ADMIN_ID, document=file_id, filename=filename,
                                         caption=admin_text, parse_mode="MarkdownV2", reply_markup=kb)
    except Exception:
        logger.exception("Failed to notify admin of new upload")


async def _handle_requirements(update: Update, context: ContextTypes.DEFAULT_TYPE, doc):
    storage = _storage(context)
    user_id = update.effective_user.id
    bot_id = context.user_data.get("last_uploaded_bot_id")
    if not bot_id:
        ids = storage.bot_ids_for_owner(user_id)
        bot_id = ids[-1] if ids else None
    if not bot_id:
        await update.message.reply_text("Upload a .py file first, then send requirements.txt.")
        return
    rec = await storage.get_bot(bot_id)
    if rec is None or rec["owner_id"] != user_id:
        await update.message.reply_text("Couldn't find a matching bot for this requirements.txt.")
        return
    if doc.file_size and doc.file_size > MAX_UPLOAD_SIZE_BYTES:
        await update.message.reply_text("❌ requirements.txt too large.")
        return
    tg_file = await doc.get_file()
    raw = await tg_file.download_as_bytearray()
    file_id = await storage.store_file(bytes(raw), "requirements.txt", caption=f"requirements for bot {bot_id}")
    rec["requirements_file_id"] = file_id
    await storage.save_bot(rec)
    await update.message.reply_text("📦 requirements.txt attached to your latest upload.")


# =============================================================================
# ADMIN HANDLERS
# =============================================================================
def require_admin(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE, *a, **kw):
        uid = update.effective_user.id if update.effective_user else None
        if uid != ADMIN_ID:
            if update.callback_query:
                await update.callback_query.answer("Not authorized.", show_alert=True)
            elif update.message:
                await update.message.reply_text("🚫 Not authorized.")
            return
        return await func(update, context, *a, **kw)
    return wrapper


def admin_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📊 Stats", callback_data="admin:stats"),
         InlineKeyboardButton("🔍 Search User", callback_data="admin:searchuser")],
        [InlineKeyboardButton("🤖 Bots Overview", callback_data="admin:bots"),
         InlineKeyboardButton("📋 Approval History", callback_data="admin:history")],
        [InlineKeyboardButton("📢 Broadcast", callback_data="admin:broadcast"),
         InlineKeyboardButton("🎁 Referral Settings", callback_data="admin:refsettings")],
        [InlineKeyboardButton("🛠 Toggle Maintenance", callback_data="admin:maintenance"),
         InlineKeyboardButton("💾 Backup", callback_data="admin:backup")],
        [InlineKeyboardButton("🩺 DB Health / Rebuild", callback_data="admin:health")],
        [InlineKeyboardButton("⬅️ Back", callback_data="menu:main")],
    ])


@require_admin
async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🛠 *Admin Panel*", parse_mode="MarkdownV2", reply_markup=admin_menu_keyboard())


async def render_stats(context) -> str:
    storage = _storage(context)
    user_ids = await storage.all_user_ids()
    active_prime = 0
    for uid in user_ids:
        u = await storage.get_user(uid)
        if u and is_prime_active(u):
            active_prime += 1
    start_ts = storage.index.get("service_start_ts", time.time())
    uptime = time.time() - start_ts
    h, m = int(uptime // 3600), int((uptime % 3600) // 60)
    return (
        f"📊 *Server Stats*\n\n"
        f"Users: `{len(user_ids)}`\n"
        f"Active Prime subs: `{active_prime}`\n"
        f"Hosted bots: `{len(storage.all_bot_ids())}`\n"
        f"Currently running: `{len(process_manager.all_running_ids())}`\n"
        f"Service uptime: `{h}h {m}m`\n"
        f"Maintenance mode: `{storage.index.get('maintenance_mode', False)}`"
    )


async def render_bots_overview(context):
    storage = _storage(context)
    ids = storage.all_bot_ids()
    lines = [f"🤖 *Bots Overview* \\({len(ids)} total\\)\n"]
    rows = []
    for bid in ids[:25]:
        rec = await storage.get_bot(bid)
        if rec is None:
            continue
        lines.append(f"`{rec['filename']}` — {rec['status']} — owner `{rec['owner_id']}`")
        rows.append([InlineKeyboardButton(f"{rec['filename']} ({rec['status']})", callback_data=f"admin:botview:{bid}")])
    if len(ids) > 25:
        lines.append(f"\n…and {len(ids) - 25} more\\.")
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="admin:open")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def render_user_detail(context, user_id: int):
    storage = _storage(context)
    user = await storage.get_user(user_id)
    if user is None:
        return None
    plan = effective_plan(user)
    bot_ids = storage.bot_ids_for_owner(user_id)
    text = (
        f"👤 *User* `{user_id}`\n"
        f"Username: @{escape_markdown_v2(user.get('username') or 'unknown')}\n"
        f"Plan: `{plan}`\n"
        f"Bots hosted: `{len(bot_ids)}`\n"
        f"Referrals: `{user.get('referral_count', 0)}`\n"
        f"Banned: `{user.get('banned', False)}`\n"
        f"Joined: `{time.strftime('%Y-%m-%d', time.gmtime(user['joined_ts']))}`"
    )
    ban_label = "✅ Unban" if user.get("banned") else "🚫 Ban"
    rows = [
        [InlineKeyboardButton("➕ Give Prime 7d", callback_data=f"admin:giveprime:{user_id}:7"),
         InlineKeyboardButton("➕ Give Prime 30d", callback_data=f"admin:giveprime:{user_id}:30")],
        [InlineKeyboardButton("✏️ Custom Prime days", callback_data=f"admin:customprime:{user_id}"),
         InlineKeyboardButton("📅 Custom expiry", callback_data=f"admin:customexpiry:{user_id}")],
        [InlineKeyboardButton("➖ Remove Prime", callback_data=f"admin:removeprime:{user_id}"),
         InlineKeyboardButton("⏱ Extend 7d", callback_data=f"admin:extendprime:{user_id}:7")],
        [InlineKeyboardButton("🤖 View bots", callback_data=f"admin:userbots:{user_id}"),
         InlineKeyboardButton(ban_label, callback_data=f"admin:toggleban:{user_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data="admin:open")],
    ]
    return text, InlineKeyboardMarkup(rows)


async def render_user_bots(context, user_id: int):
    storage = _storage(context)
    ids = storage.bot_ids_for_owner(user_id)
    lines = [f"🤖 Bots owned by `{user_id}`\n"]
    rows = []
    for bid in ids:
        rec = await storage.get_bot(bid)
        if rec is None:
            continue
        lines.append(f"`{rec['filename']}` — {rec['status']}")
        rows.append([InlineKeyboardButton(f"⏹ Stop {rec['filename']}", callback_data=f"admin:botstop:{bid}"),
                     InlineKeyboardButton("🗑 Delete", callback_data=f"admin:botdel:{bid}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"admin:searchresult:{user_id}")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def render_history(context) -> str:
    storage = _storage(context)
    entries = await storage.get_approval_log(limit=15)
    if not entries:
        return "📋 No approval history yet\\."
    lines = ["📋 *Recent Approval History*\n"]
    for e in reversed(entries):
        ts = time.strftime("%Y-%m-%d %H:%M", time.gmtime(e["ts"]))
        lines.append(f"`{ts}` — {e['action']} — bot `{e['bot_id']}` — owner `{e['owner_id']}`")
    return "\n".join(lines)


def _admin_back_kb():
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="admin:open")]])


# =============================================================================
# CALLBACK ROUTER
# =============================================================================
async def _answer(q, text=None, alert=False):
    try:
        await q.answer(text=text, show_alert=alert)
    except Exception:
        pass


async def _own_bot_or_none(context, q, bid: str):
    storage = _storage(context)
    rec = await storage.get_bot(bid)
    if rec is None:
        await _answer(q, "Bot not found.", True)
        return None
    if rec["owner_id"] != q.from_user.id and q.from_user.id != ADMIN_ID:
        await _answer(q, "Not your bot.", True)
        return None
    return rec


async def dispatch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    data = q.data or ""
    await _answer(q)

    ok, retry = check_action_rate(q.from_user.id)
    if not ok and not data.startswith(("approve:", "reject:")):
        await _answer(q, f"Slow down — try again in {retry}s.", True)
        return

    if data == "menu:main":
        await show_main_menu(q, context, edit=True)
    elif data == "menu:upload":
        await q.edit_message_text("⬆️ Send me a `.py` file to upload your bot\\.", parse_mode="MarkdownV2")
    elif data == "menu:mybots":
        text, kb = await render_my_bots(context, q.from_user.id)
        await q.edit_message_text(text, parse_mode="MarkdownV2" if kb else None, reply_markup=kb)
    elif data == "menu:sub":
        storage = _storage(context)
        user = await storage.get_user(q.from_user.id)
        await q.edit_message_text(format_status(user), reply_markup=_back_kb())
    elif data == "menu:referral":
        storage = _storage(context)
        user = await storage.get_user(q.from_user.id)
        me = await context.bot.get_me()
        link = make_referral_link(me.username, user["user_id"])
        text = (f"🎁 Your referral link:\n{link}\n\n"
                f"Successful referrals: {user.get('referral_count', 0)}\n"
                f"Reward: {REFERRAL_REWARD_DAYS} day(s) Prime each")
        await q.edit_message_text(text, reply_markup=_back_kb())
    elif data == "menu:server":
        storage = _storage(context)
        start_ts = storage.index.get("service_start_ts", time.time())
        uptime = _format_duration(time.time() - start_ts)
        text = (f"🟢 Service Online\n⏱ Uptime: {uptime}\n"
                f"🤖 Hosted bots: {len(storage.all_bot_ids())}\n"
                f"▶️ Running: {len(process_manager.all_running_ids())}")
        await q.edit_message_text(text, reply_markup=_back_kb())
    elif data == "menu:help":
        await q.edit_message_text(HELP_TEXT, reply_markup=_back_kb())
    elif data == "menu:contact":
        await q.edit_message_text(f"📩 {SUBSCRIPTION_CONTACT_TEXT}", reply_markup=_back_kb())
    elif data.startswith("bot:"):
        await _handle_bot_action(q, context, data)
    elif data.startswith("approve:") or data.startswith("reject:"):
        await _handle_approval(q, context, data)
    elif data.startswith("admin:"):
        await _handle_admin(q, context, data)


async def _handle_bot_action(q, context, data: str):
    parts = data.split(":")
    action = parts[1]
    bid = parts[2] if len(parts) > 2 else None
    storage = _storage(context)

    if action == "info":
        result = await render_bot_detail(context, bid)
        if result is None:
            await _answer(q, "Not found.", True)
            return
        text, kb = result
        await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
        return

    rec = await _own_bot_or_none(context, q, bid)
    if rec is None:
        return

    if action == "start":
        if rec["status"] not in ("approved", "stopped", "crashed"):
            await _answer(q, "Bot must be approved before starting.", True)
            return
        workdir = process_manager.workdir_for(rec["owner_id"], bid)
        script_path = os.path.join(workdir, rec["filename"])
        if not os.path.exists(script_path):
            content = await storage.download_file(rec["file_id"])
            with open(script_path, "wb") as f:
                f.write(content)
        ok, msg = await process_manager.start(bid, rec["owner_id"], script_path)
        rec["status"] = "running" if ok else "crashed"
        rec["pid"] = process_manager.pid(bid)
        rec["last_start_ts"] = time.time()
        await storage.save_bot(rec)
        await _answer(q, msg)
    elif action == "stop":
        ok, msg = await process_manager.stop(bid)
        rec["status"] = "stopped"
        rec["pid"] = None
        await storage.save_bot(rec)
        await _answer(q, msg)
    elif action == "restart":
        await process_manager.stop(bid)
        workdir = process_manager.workdir_for(rec["owner_id"], bid)
        script_path = os.path.join(workdir, rec["filename"])
        ok, msg = await process_manager.start(bid, rec["owner_id"], script_path)
        rec["status"] = "running" if ok else "crashed"
        rec["pid"] = process_manager.pid(bid)
        rec["restart_count"] = rec.get("restart_count", 0) + 1
        rec["last_start_ts"] = time.time()
        await storage.save_bot(rec)
        await _answer(q, msg)
    elif action == "logs":
        tail = process_manager.read_log_tail(bid, rec["owner_id"])[-3500:]
        await q.message.reply_text(f"📜 Logs for {rec['filename']}:\n```\n{tail}\n```", parse_mode="Markdown")
        return
    elif action == "clearlogs":
        process_manager.clear_log(bid, rec["owner_id"])
        await _answer(q, "Logs cleared.")
    elif action == "pkgs":
        pkgs = await process_manager.list_installed_packages(process_manager.workdir_for(rec["owner_id"], bid))
        text = ("📦 Installed packages:\n" + ("\n".join(f"- {p}" for p in pkgs) if pkgs else "(none)")) + \
               "\n\nSend requirements.txt to (re)install dependencies."
        await q.message.reply_text(text)
        return
    elif action == "download":
        content = await storage.download_file(rec["file_id"])
        buf = io.BytesIO(content)
        buf.name = rec["filename"]
        await q.message.reply_document(document=buf, filename=rec["filename"])
        return
    elif action == "toggleauto":
        rec["auto_restart"] = not rec.get("auto_restart", False)
        await storage.save_bot(rec)
        await _answer(q, f"Auto-restart {'enabled' if rec['auto_restart'] else 'disabled'}.")
    elif action == "delconfirm":
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Confirm Delete", callback_data=f"bot:deldo:{bid}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"bot:info:{bid}"),
        ]])
        await q.edit_message_text(f"Delete `{rec['filename']}`? This cannot be undone\\.",
                                   parse_mode="MarkdownV2", reply_markup=kb)
        return
    elif action == "deldo":
        await process_manager.stop(bid)
        await storage.delete_bot(bid)
        await q.edit_message_text("🗑 Bot deleted.")
        return

    result = await render_bot_detail(context, bid)
    if result:
        text, kb = result
        try:
            await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
        except Exception:
            pass


async def _handle_approval(q, context, data: str):
    if q.from_user.id != ADMIN_ID:
        await _answer(q, "Not authorized.", True)
        return
    action, bid = data.split(":", 1)
    storage = _storage(context)
    rec = await storage.get_bot(bid)
    if rec is None:
        await _answer(q, "Bot record not found (may have been deleted).", True)
        return
    if rec["status"] != "pending":
        await _answer(q, f"Already processed (status: {rec['status']}).", True)
        return

    if action == "approve":
        rec["status"] = "approved"
        rec["approved_by"] = q.from_user.id
        rec["approved_ts"] = time.time()
        await storage.save_bot(rec)
        await storage.append_approval_log({
            "bot_id": bid, "owner_id": rec["owner_id"], "action": "approved",
            "admin_id": q.from_user.id, "reason": None, "ts": time.time(),
        })
        try:
            await q.edit_message_caption(caption=(q.message.caption or "") + "\n\n✅ APPROVED")
        except Exception:
            pass
        try:
            await context.bot.send_message(rec["owner_id"],
                                            f"✅ Your bot '{rec['filename']}' was approved! Start it from 'My Bots'.")
        except Exception:
            logger.exception("Failed to notify user of approval")
    else:
        context.user_data["pending_action"] = {"type": "reject_reason", "bot_id": bid}
        await q.message.reply_text("✍️ Please reply with the rejection reason:")


async def _handle_admin(q, context, data: str):
    if q.from_user.id != ADMIN_ID:
        await _answer(q, "Not authorized.", True)
        return
    storage = _storage(context)
    parts = data.split(":")
    action = parts[1]

    if action == "open":
        await q.edit_message_text("🛠 *Admin Panel*", parse_mode="MarkdownV2", reply_markup=admin_menu_keyboard())
    elif action == "stats":
        await q.edit_message_text(await render_stats(context), parse_mode="MarkdownV2", reply_markup=_admin_back_kb())
    elif action == "bots":
        text, kb = await render_bots_overview(context)
        await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "botview":
        bid = parts[2]
        rec = await storage.get_bot(bid)
        if rec is None:
            await _answer(q, "Not found.", True)
            return
        text = (f"🤖 `{rec['filename']}`\nOwner: `{rec['owner_id']}`\nStatus: `{rec['status']}`\n"
                f"PID: `{process_manager.pid(bid) or '—'}`")
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("⏹ Stop", callback_data=f"admin:botstop:{bid}"),
             InlineKeyboardButton("🗑 Delete", callback_data=f"admin:botdel:{bid}")],
            [InlineKeyboardButton("⬅️ Back", callback_data="admin:bots")],
        ])
        await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "botstop":
        bid = parts[2]
        rec = await storage.get_bot(bid)
        if rec:
            await process_manager.stop(bid)
            rec["status"] = "stopped"
            rec["pid"] = None
            await storage.save_bot(rec)
        await _answer(q, "Stopped.")
    elif action == "botdel":
        bid = parts[2]
        await process_manager.stop(bid)
        await storage.delete_bot(bid)
        await _answer(q, "Deleted.")
    elif action == "history":
        await q.edit_message_text(await render_history(context), parse_mode="MarkdownV2", reply_markup=_admin_back_kb())
    elif action == "searchuser":
        context.user_data["pending_action"] = {"type": "search_user"}
        await q.message.reply_text("🔍 Send the numeric Telegram user ID to search:")
    elif action == "searchresult":
        uid = int(parts[2])
        result = await render_user_detail(context, uid)
        if result is None:
            await q.edit_message_text("User not found.", reply_markup=_admin_back_kb())
            return
        text, kb = result
        await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "userbots":
        uid = int(parts[2])
        text, kb = await render_user_bots(context, uid)
        await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "giveprime":
        uid, days = int(parts[2]), int(parts[3])
        u = await storage.get_user(uid)
        if u:
            grant_prime(u, days, q.from_user.id)
            await storage.save_user(u)
            await _answer(q, f"Granted {days}d Prime.")
            try:
                await context.bot.send_message(uid, f"🎉 You've been granted {days} day(s) of Prime!")
            except Exception:
                pass
        result = await render_user_detail(context, uid)
        if result:
            text, kb = result
            await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "extendprime":
        uid, days = int(parts[2]), int(parts[3])
        u = await storage.get_user(uid)
        if u:
            extend_prime(u, days)
            await storage.save_user(u)
            await _answer(q, f"Extended by {days}d.")
        result = await render_user_detail(context, uid)
        if result:
            text, kb = result
            await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "removeprime":
        uid = int(parts[2])
        u = await storage.get_user(uid)
        if u:
            remove_prime(u)
            await storage.save_user(u)
            await _answer(q, "Prime removed.")
        result = await render_user_detail(context, uid)
        if result:
            text, kb = result
            await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "customprime":
        uid = int(parts[2])
        context.user_data["pending_action"] = {"type": "custom_prime_days", "user_id": uid}
        await q.message.reply_text("✏️ Send number of Prime days to grant:")
    elif action == "customexpiry":
        uid = int(parts[2])
        context.user_data["pending_action"] = {"type": "custom_expiry", "user_id": uid}
        await q.message.reply_text("📅 Send expiry as YYYY-MM-DD:")
    elif action == "toggleban":
        uid = int(parts[2])
        u = await storage.get_user(uid)
        if u:
            u["banned"] = not u.get("banned", False)
            await storage.save_user(u)
            await _answer(q, f"Ban {'set' if u['banned'] else 'lifted'}.")
        result = await render_user_detail(context, uid)
        if result:
            text, kb = result
            await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    elif action == "broadcast":
        context.user_data["pending_action"] = {"type": "broadcast"}
        await q.message.reply_text("📢 Send the broadcast message text:")
    elif action == "refsettings":
        text = (f"🎁 Referral reward: {REFERRAL_REWARD_DAYS} day(s) Prime per referral.\n"
                f"(Change via REFERRAL_REWARD_DAYS env var and redeploy.)")
        await q.edit_message_text(text, reply_markup=_admin_back_kb())
    elif action == "maintenance":
        storage.index["maintenance_mode"] = not storage.index.get("maintenance_mode", False)
        storage.mark_dirty()
        await storage.save_index()
        await _answer(q, f"Maintenance mode: {storage.index['maintenance_mode']}")
        await q.edit_message_text("🛠 *Admin Panel*", parse_mode="MarkdownV2", reply_markup=admin_menu_keyboard())
    elif action == "backup":
        await storage.backup_snapshot()
        await q.message.reply_text("💾 Backup snapshot saved to the DB group.")
    elif action == "health":
        await q.message.reply_text("🩺 Running index health check / prune…")
        report = await storage.rebuild_index_from_scratch()
        await q.message.reply_text(
            f"Users checked: {report['users_checked']} (pruned {report['users_pruned']})\n"
            f"Bots checked: {report['bots_checked']} (pruned {report['bots_pruned']})"
        )


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    pending = context.user_data.get("pending_action")
    if not pending or update.effective_user.id != ADMIN_ID:
        return
    storage = _storage(context)
    text = update.message.text.strip()
    kind = pending["type"]

    if kind == "reject_reason":
        bid = pending["bot_id"]
        rec = await storage.get_bot(bid)
        context.user_data.pop("pending_action", None)
        if rec is None or rec["status"] != "pending":
            await update.message.reply_text("Bot no longer pending.")
            return
        rec["status"] = "rejected"
        rec["reject_reason"] = text
        rec["approved_by"] = update.effective_user.id
        rec["approved_ts"] = time.time()
        await storage.save_bot(rec)
        await storage.append_approval_log({
            "bot_id": bid, "owner_id": rec["owner_id"], "action": "rejected",
            "admin_id": update.effective_user.id, "reason": text, "ts": time.time(),
        })
        await update.message.reply_text("❌ Rejection recorded and user notified.")
        try:
            await context.bot.send_message(rec["owner_id"],
                                            f"❌ Your bot '{rec['filename']}' was rejected.\nReason: {text}")
        except Exception:
            logger.exception("Failed to notify user of rejection")

    elif kind == "search_user":
        context.user_data.pop("pending_action", None)
        if not text.isdigit():
            await update.message.reply_text("Please send a numeric user ID.")
            return
        result = await render_user_detail(context, int(text))
        if result is None:
            await update.message.reply_text("User not found.")
            return
        msg, kb = result
        await update.message.reply_text(msg, parse_mode="MarkdownV2", reply_markup=kb)

    elif kind == "custom_prime_days":
        context.user_data.pop("pending_action", None)
        uid = pending["user_id"]
        if not text.lstrip("-").isdigit() or int(text) <= 0:
            await update.message.reply_text("Please send a positive integer number of days.")
            return
        u = await storage.get_user(uid)
        if u:
            grant_prime(u, int(text), update.effective_user.id)
            await storage.save_user(u)
            await update.message.reply_text(f"Granted {text} day(s) of Prime to {uid}.")
            try:
                await context.bot.send_message(uid, f"🎉 You've been granted {text} day(s) of Prime!")
            except Exception:
                pass

    elif kind == "custom_expiry":
        context.user_data.pop("pending_action", None)
        uid = pending["user_id"]
        try:
            ts = time.mktime(time.strptime(text, "%Y-%m-%d"))
        except ValueError:
            await update.message.reply_text("Invalid date format. Use YYYY-MM-DD.")
            return
        u = await storage.get_user(uid)
        if u:
            set_custom_expiry(u, ts)
            await storage.save_user(u)
            await update.message.reply_text(f"Set Prime expiry for {uid} to {text}.")

    elif kind == "broadcast":
        context.user_data.pop("pending_action", None)
        ids = await storage.all_user_ids()
        sent, failed = 0, 0
        await update.message.reply_text(f"📢 Broadcasting to {len(ids)} users…")
        for uid in ids:
            try:
                await context.bot.send_message(uid, f"📢 Announcement:\n\n{text}")
                sent += 1
            except Exception:
                failed += 1
        await update.message.reply_text(f"Broadcast done. Sent: {sent}, failed: {failed}.")


# =============================================================================
# HEALTH ENDPOINT  (real, honest health check - no fake keep-alive pings)
# =============================================================================
class _HealthHandler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"OK")


def _run_health_server():
    try:
        HTTPServer(("0.0.0.0", PORT), _HealthHandler).serve_forever()
    except OSError as e:
        logger.warning("Health server could not bind port %s: %s", PORT, e)


# =============================================================================
# STARTUP / SHUTDOWN / WIRING
# =============================================================================
async def _startup_reconciliation(app: Application):
    """RAM is empty after a redeploy; Telegram storage is not. Only bots
    flagged auto_restart are relaunched - everything else stays stopped
    until the owner or admin starts it again."""
    storage: GroupStorage = app.bot_data["storage"]
    relaunched = 0
    for bot_id in storage.all_bot_ids():
        rec = await storage.get_bot(bot_id)
        if rec is None:
            continue
        if rec["status"] == "running":
            rec["status"] = "crashed" if not rec.get("auto_restart") else "stopped"
        if rec.get("auto_restart") and rec["status"] in ("crashed", "stopped", "approved"):
            workdir = process_manager.workdir_for(rec["owner_id"], bot_id)
            script_path = os.path.join(workdir, rec["filename"])
            if not os.path.exists(script_path):
                try:
                    content = await storage.download_file(rec["file_id"])
                    with open(script_path, "wb") as f:
                        f.write(content)
                except Exception:
                    logger.exception("Could not restore script for %s", bot_id)
                    await storage.save_bot(rec)
                    continue
            ok, _ = await process_manager.start(bot_id, rec["owner_id"], script_path)
            rec["status"] = "running" if ok else "crashed"
            rec["pid"] = process_manager.pid(bot_id)
            rec["last_start_ts"] = time.time()
            if ok:
                relaunched += 1
        await storage.save_bot(rec)
    logger.info("Startup reconciliation complete. Relaunched %s auto-restart bot(s).", relaunched)


async def _on_startup(app: Application):
    storage = GroupStorage(app.bot, BOT_DB_GROUP_ID)
    await storage.bootstrap()
    app.bot_data["storage"] = storage

    async def notifier(user_id: int, text: str):
        try:
            await app.bot.send_message(user_id, text)
        except TelegramError:
            pass

    supervisor = Supervisor(storage, notifier=notifier)
    app.bot_data["supervisor"] = supervisor

    await _startup_reconciliation(app)
    supervisor.start()

    threading.Thread(target=_run_health_server, daemon=True).start()
    logger.info("HostBot started. Health endpoint on :%s", PORT)


async def _on_shutdown(app: Application):
    supervisor: Supervisor = app.bot_data.get("supervisor")
    if supervisor:
        await supervisor.stop()
    storage: GroupStorage = app.bot_data.get("storage")
    if storage:
        try:
            await storage.save_index()
        except Exception:
            logger.exception("Failed to persist index on shutdown")
    logger.info("HostBot shutting down gracefully.")


async def _error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    logger.error("Unhandled exception", exc_info=context.error)
    try:
        if isinstance(update, Update) and update.effective_message:
            await update.effective_message.reply_text("⚠️ Something went wrong processing that. The admin has been notified.")
        await context.bot.send_message(ADMIN_ID, f"🐛 Error: {context.error!r}"[:1000])
    except Exception:
        pass


def build_application() -> Application:
    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .post_init(_on_startup)
        .post_shutdown(_on_shutdown)
        .build()
    )

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("mybots", cmd_mybots))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CommandHandler("referral", cmd_referral))
    app.add_handler(CommandHandler("server", cmd_server_status))
    app.add_handler(CommandHandler("contact", cmd_contact))
    app.add_handler(CommandHandler(ADMIN_PANEL_COMMAND, cmd_admin))

    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    app.add_handler(CallbackQueryHandler(dispatch))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))

    app.add_error_handler(_error_handler)
    return app


def main():
    app = build_application()
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
