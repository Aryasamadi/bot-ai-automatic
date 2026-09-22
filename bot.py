# VERSION 10.24.0 — fix insufficient content detection + remove placeholder fallback from publication
import os
import io
import re
import time
import math
import random
import logging
import asyncio
import html
import hashlib
import json
import urllib.parse
import struct
import zlib
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
from difflib import SequenceMatcher
from datetime import datetime, timezone, timedelta
from typing import List, Dict, Any, Optional, Tuple

import pytz
import aiohttp
from dotenv import load_dotenv
from cryptography.fernet import Fernet, InvalidToken

from aiogram import Bot, Dispatcher, Router, F, BaseMiddleware
from aiogram.filters import Command, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    Message, 
    CallbackQuery, 
    TelegramObject,
    ReplyKeyboardMarkup, 
    KeyboardButton, 
    InlineKeyboardMarkup, 
    InlineKeyboardButton,
    BufferedInputFile
)

# بارگذاری متغیرهای محیطی در صورت وجود فایل .env
load_dotenv()

# ============================================================
# بخش تنظیمات و متغیرهای سراسری (Configuration)
# ============================================================
API_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0"))
BOT_USERNAME = os.getenv("BOT_USERNAME", "TechNowAibot")
BUILD_VERSION = "10.24.0-fix-insufficient-content-placeholder"
DEFAULT_MAX_WORKERS = 3
DEFAULT_MAX_AI_WORKERS = 3
AI_VERIFY_ENABLED_DEFAULT = os.getenv("AI_VERIFY_ENABLED", "auto").lower()
AI_PROVIDER_RECHECK_MINUTES = int(os.getenv("AI_PROVIDER_RECHECK_MINUTES", "10"))
BOT_USERNAME_RUNTIME = ""

# تنظیمات اتصال به Cloudflare D1 REST API
CF_ACCOUNT_ID = os.getenv("CF_ACCOUNT_ID")
CF_DATABASE_ID = os.getenv("CF_DATABASE_ID")
CF_API_TOKEN = os.getenv("CF_API_TOKEN")

# تنظیمات مربوط به هوش مصنوعی
AI_API_KEY = os.getenv("AI_API_KEY")
AI_API_URL = os.getenv("AI_API_URL", "https://generativelanguage.googleapis.com/v1beta/openai/chat/completions")
AI_MODEL_NAME = os.getenv("AI_MODEL_NAME", "gemini-1.5-flash")

# تنظیمات اتوماسیون محتوای هوشمند
CHANNEL_ID = os.getenv("CHANNEL_ID", "")
AUTOMATION_ENABLED_DEFAULT = os.getenv("AUTOMATION_ENABLED", "true").lower() in {"1", "true", "yes", "on"}
DEFAULT_SOURCE_INTERVAL_MINUTES = int(os.getenv("DEFAULT_SOURCE_INTERVAL_MINUTES", "15"))
DEFAULT_MAX_DAILY_POSTS = int(os.getenv("MAX_DAILY_POSTS", "6"))
DEFAULT_MIN_CONTENT_SCORE = float(os.getenv("MIN_CONTENT_SCORE", "65"))
MANAGER_SCORE_TOLERANCE = float(os.getenv("MANAGER_SCORE_TOLERANCE", "8"))
DEFAULT_MIN_HOURS_BETWEEN_POSTS = float(os.getenv("MIN_HOURS_BETWEEN_POSTS", "2"))
DEFAULT_MIN_POST_GAP_MINUTES = max(1, int(round(DEFAULT_MIN_HOURS_BETWEEN_POSTS * 60)))
DEFAULT_PUBLISH_START_HOUR = int(os.getenv("PUBLISH_START_HOUR", "8"))
DEFAULT_PUBLISH_END_HOUR = int(os.getenv("PUBLISH_END_HOUR", "23"))
CONTENT_RETENTION_DAYS = int(os.getenv("CONTENT_RETENTION_DAYS", "1"))
# News freshness policy: automation accepts only items with a verifiable publication
# timestamp within this window. Tests may opt into archived items explicitly.
NEWS_FRESHNESS_MAX_HOURS = float(os.getenv("NEWS_FRESHNESS_MAX_HOURS", "24"))
NEWS_PRIORITY_HOURS = float(os.getenv("NEWS_PRIORITY_HOURS", "6"))
NEWS_FRESHNESS_STRICT = os.getenv("NEWS_FRESHNESS_STRICT", "true").lower() in {"1", "true", "yes", "on"}
LOG_RETENTION_DAYS = int(os.getenv("LOG_RETENTION_DAYS", "14"))
AI_PROVIDER_ENCRYPTION_KEY = os.getenv("AI_PROVIDER_ENCRYPTION_KEY", "")
HTTP_USER_AGENT = os.getenv("HTTP_USER_AGENT", "TechNowAI/2.0 (+content automation)")
HTTP_TIMEOUT_SECONDS = int(os.getenv("HTTP_TIMEOUT_SECONDS", "20"))
MAX_HTTP_BYTES = int(os.getenv("MAX_HTTP_BYTES", "1500000"))
MAX_SOURCE_ITEMS_PER_CYCLE = int(os.getenv("MAX_SOURCE_ITEMS_PER_CYCLE", "5"))
MAX_AUTOMATION_SOURCES = max(1, int(os.getenv("MAX_AUTOMATION_SOURCES", "50")))

# تنظیم لاگر برای خطایابی بهتر
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)
HTTP_SESSION: Optional[aiohttp.ClientSession] = None
SETTINGS_CACHE: Dict[str, Tuple[str, float]] = {}
SETTINGS_CACHE_TTL = 20.0
_LIVE_HEALTH_TASKS: Dict[Tuple[int, int], asyncio.Task] = {}
_LIVE_HEALTH_STATE: Dict[Tuple[int, int], Dict[str, Any]] = {}

async def get_http_session() -> aiohttp.ClientSession:
    global HTTP_SESSION
    if HTTP_SESSION is None or HTTP_SESSION.closed:
        HTTP_SESSION = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=HTTP_TIMEOUT_SECONDS))
    return HTTP_SESSION

async def close_http_session():
    global HTTP_SESSION
    if HTTP_SESSION and not HTTP_SESSION.closed:
        await HTTP_SESSION.close()
    HTTP_SESSION = None

# ============================================================
# کلاس ارتباط با دیتابیس Cloudflare D1 REST API
# ============================================================
class D1Database:
    def __init__(self, account_id: str, database_id: str, api_token: str):
        self.account_id = account_id
        self.database_id = database_id
        self.api_token = api_token
        self.url = f"https://api.cloudflare.com/client/v4/accounts/{account_id}/d1/database/{database_id}/query"
        self.headers = {
            "Authorization": f"Bearer {api_token}",
            "Content-Type": "application/json"
        }
        self.session: Optional[aiohttp.ClientSession] = None

    async def start(self):
        if self.session is None or self.session.closed:
            timeout = aiohttp.ClientTimeout(total=HTTP_TIMEOUT_SECONDS)
            self.session = aiohttp.ClientSession(timeout=timeout)

    async def close(self):
        if self.session and not self.session.closed:
            await self.session.close()
        self.session = None

    async def execute(self, sql: str, params: List[Any] = None) -> List[Dict[str, Any]]:
        payload = {"sql": sql}
        if params:
            payload["params"] = params

        session = self.session
        temporary_session = False
        if session is None or session.closed:
            session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=HTTP_TIMEOUT_SECONDS))
            temporary_session = True
        try:
                async with session.post(self.url, headers=self.headers, json=payload) as resp:
                    if resp.status != 200:
                        text = await resp.text()
                        logger.error(f"D1 API Error (status {resp.status}): {text}")
                        raise Exception(f"Cloudflare D1 API returned status {resp.status}: {text}")
                    
                    data = await resp.json()
                    if not data.get("success"):
                        errors = data.get("errors", [])
                        logger.error(f"D1 Query failed: {errors}")
                        raise Exception(f"D1 Query failed: {errors}")
                    
                    result = data.get("result", [])
                    if isinstance(result, list) and len(result) > 0:
                        return result[0].get("results", [])
                    elif isinstance(result, dict):
                        return result.get("results", [])
                    return []
        except Exception as e:
            logger.error(f"Error executing SQL: {sql} with params {params}. Error: {e}")
            raise e
        finally:
            if temporary_session:
                await session.close()

    async def execute_batch(self, queries: List[Dict[str, Any]]) -> List[List[Dict[str, Any]]]:
        session = self.session
        temporary_session = False
        if session is None or session.closed:
            session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=HTTP_TIMEOUT_SECONDS))
            temporary_session = True
        output = []
        try:
            for query in queries:
                    payload = {"sql": query["sql"]}
                    if query.get("params"):
                        payload["params"] = query["params"]

                    async with session.post(self.url, headers=self.headers, json=payload) as resp:
                        if resp.status != 200:
                            text = await resp.text()
                            logger.error(f"D1 Batch API Error (status {resp.status}): {text}")
                            raise Exception(f"Cloudflare D1 Batch API returned status {resp.status}: {text}")
                        
                        data = await resp.json()
                        if not data.get("success"):
                            errors = data.get("errors", [])
                            logger.error(f"D1 Batch Query failed: {errors}")
                            raise Exception(f"D1 Batch Query failed: {errors}")
                        
                        result = data.get("result", [])
                        if isinstance(result, list) and len(result) > 0:
                            output.append(result[0].get("results", []))
                        elif isinstance(result, dict):
                            output.append(result.get("results", []))
                        else:
                            output.append([])
            return output
        except Exception as e:
            logger.error(f"Error executing batch queries. Error: {e}")
            raise e
        finally:
            if temporary_session:
                await session.close()


async def initialize_database(db: D1Database):
    queries = [
        {"sql": "CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, joined_at TEXT, role TEXT DEFAULT 'user', tokens_used INTEGER DEFAULT 0, last_reset_date TEXT)"},
        {"sql": "CREATE TABLE IF NOT EXISTS posts(id INTEGER PRIMARY KEY AUTOINCREMENT, text TEXT, file_id TEXT, media_type TEXT, likes INTEGER DEFAULT 0, dislikes INTEGER DEFAULT 0, views INTEGER DEFAULT 0, deleted INTEGER DEFAULT 0)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_posts_deleted ON posts(deleted)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_posts_text ON posts(text)"},
        {"sql": "CREATE TABLE IF NOT EXISTS user_content_saves(user_id INTEGER NOT NULL, content_type TEXT NOT NULL, content_id INTEGER NOT NULL, folder TEXT NOT NULL, created_at TEXT, PRIMARY KEY(user_id, content_type, content_id))"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_user_content_saves_user_folder ON user_content_saves(user_id, folder)"},
        {"sql": "CREATE TABLE IF NOT EXISTS user_content_votes(user_id INTEGER NOT NULL, content_type TEXT NOT NULL, content_id INTEGER NOT NULL, vote_type TEXT NOT NULL, created_at TEXT, PRIMARY KEY(user_id, content_type, content_id))"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_user_content_votes_content ON user_content_votes(content_type, content_id)"},
        {"sql": "CREATE TABLE IF NOT EXISTS user_states(user_id INTEGER PRIMARY KEY, state TEXT, data TEXT)"},
        {"sql": "CREATE TABLE IF NOT EXISTS processed_updates(update_id INTEGER PRIMARY KEY, processed_at TEXT)"}
    ]
    await db.execute_batch(queries)
    try:
        await db.execute("ALTER TABLE posts ADD COLUMN views INTEGER DEFAULT 0")
    except Exception:
        pass
    try:
        await db.execute("ALTER TABLE users ADD COLUMN tokens_used INTEGER DEFAULT 0")
    except Exception:
        pass
    try:
        await db.execute("ALTER TABLE users ADD COLUMN last_reset_date TEXT")
    except Exception:
        pass



async def migrate_unified_user_interactions(db: D1Database):
    rows=await db.execute("SELECT name FROM sqlite_master WHERE type='table' AND name IN ('saves','votes','article_saves','article_votes')")
    existing={str(r.get('name') or '') for r in rows}
    statements=[]
    if 'saves' in existing:
        statements.append("INSERT OR IGNORE INTO user_content_saves(user_id,content_type,content_id,folder,created_at) SELECT user, 'post', post, folder, NULL FROM saves")
    if 'article_saves' in existing:
        statements.append("INSERT OR IGNORE INTO user_content_saves(user_id,content_type,content_id,folder,created_at) SELECT user_id, 'article', article_id, folder, NULL FROM article_saves")
    if 'votes' in existing:
        statements.append("INSERT OR IGNORE INTO user_content_votes(user_id,content_type,content_id,vote_type,created_at) SELECT user_id, 'post', post_id, vote_type, NULL FROM votes")
    if 'article_votes' in existing:
        statements.append("INSERT OR IGNORE INTO user_content_votes(user_id,content_type,content_id,vote_type,created_at) SELECT user_id, 'article', article_id, vote_type, NULL FROM article_votes")
    for legacy in ('saves','votes','article_saves','article_votes'):
        if legacy in existing: statements.append(f"DROP TABLE IF EXISTS {legacy}")
    for sql in statements:
        try: await db.execute(sql)
        except Exception: pass

# ============================================================
# زیرسیستم اتوماسیون محتوا (Content Automation)
# ============================================================

async def initialize_automation_database(db: D1Database):
    queries = [
        {"sql": "CREATE TABLE IF NOT EXISTS sources(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, url TEXT UNIQUE, feed_url TEXT, category TEXT DEFAULT 'tech', enabled INTEGER DEFAULT 1, interval_minutes INTEGER DEFAULT 15, priority INTEGER DEFAULT 5, last_checked_at TEXT, next_check_at TEXT, last_error TEXT, trust_score REAL DEFAULT 80, created_at TEXT, last_seen_published_at TEXT, last_seen_url TEXT)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_sources_due ON sources(enabled, next_check_at)"},
        {"sql": "CREATE TABLE IF NOT EXISTS source_items(id INTEGER PRIMARY KEY AUTOINCREMENT, source_id INTEGER NOT NULL, canonical_url TEXT NOT NULL, title TEXT, description TEXT, content TEXT, image_url TEXT, published_at TEXT, discovered_at TEXT, content_hash TEXT, status TEXT DEFAULT 'new', score REAL DEFAULT 0, category TEXT, article_id INTEGER, last_error TEXT, retry_after TEXT, UNIQUE(source_id, canonical_url))"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_source_items_status ON source_items(status)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_source_items_hash ON source_items(content_hash)"},
        {"sql": "CREATE TABLE IF NOT EXISTS articles(id INTEGER PRIMARY KEY AUTOINCREMENT, source_item_id INTEGER UNIQUE, title TEXT, channel_text TEXT, body TEXT, source_url TEXT, image_url TEXT, category TEXT, score REAL, status TEXT DEFAULT 'ready', deep_token TEXT UNIQUE, created_at TEXT, verified_at TEXT, published_message_id INTEGER, source_published_at TEXT, deep_views INTEGER DEFAULT 0)"},
        {"sql": "CREATE TABLE IF NOT EXISTS publication_queue(id INTEGER PRIMARY KEY AUTOINCREMENT, article_id INTEGER UNIQUE, scheduled_at TEXT, status TEXT DEFAULT 'queued', attempts INTEGER DEFAULT 0, last_error TEXT, created_at TEXT, published_at TEXT)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_publication_queue_due ON publication_queue(status, scheduled_at)"},
        {"sql": "CREATE TABLE IF NOT EXISTS ai_providers(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE, base_url TEXT, encrypted_api_key TEXT, model_name TEXT, priority INTEGER DEFAULT 10, enabled INTEGER DEFAULT 1, web_enabled INTEGER DEFAULT 0, created_at TEXT, updated_at TEXT, status TEXT DEFAULT 'unknown', last_error TEXT, cooldown_until TEXT, last_checked_at TEXT, last_latency_ms INTEGER DEFAULT 0, consecutive_failures INTEGER DEFAULT 0)"},
        {"sql": "CREATE TABLE IF NOT EXISTS automation_settings(key TEXT PRIMARY KEY, value TEXT)"},
        {"sql": "CREATE TABLE IF NOT EXISTS automation_logs(id INTEGER PRIMARY KEY AUTOINCREMENT, level TEXT, event TEXT, details TEXT, created_at TEXT)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_automation_logs_created ON automation_logs(created_at)"},
        {"sql": "CREATE TABLE IF NOT EXISTS manual_channel_events(id INTEGER PRIMARY KEY AUTOINCREMENT, message_id INTEGER, created_at TEXT)"},
        {"sql": "CREATE TABLE IF NOT EXISTS test_history(id INTEGER PRIMARY KEY AUTOINCREMENT, source_url TEXT, content_hash TEXT, title TEXT, tested_at TEXT)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_test_history_hash ON test_history(content_hash)"},
        {"sql": "CREATE INDEX IF NOT EXISTS idx_test_history_source ON test_history(source_url, tested_at)"}
    ]
    await db.execute_batch(queries)
    # مهاجرت امن برای نصب‌های قبلی
    for sql in [
        "ALTER TABLE ai_providers ADD COLUMN status TEXT DEFAULT 'unknown'",
        "ALTER TABLE ai_providers ADD COLUMN last_error TEXT",
        "ALTER TABLE ai_providers ADD COLUMN cooldown_until TEXT",
        "ALTER TABLE ai_providers ADD COLUMN last_checked_at TEXT",
        "ALTER TABLE ai_providers ADD COLUMN last_latency_ms INTEGER DEFAULT 0",
        "ALTER TABLE ai_providers ADD COLUMN consecutive_failures INTEGER DEFAULT 0",
        "ALTER TABLE ai_providers ADD COLUMN web_enabled INTEGER DEFAULT 0",
        "ALTER TABLE articles ADD COLUMN published_at TEXT",
        "ALTER TABLE articles ADD COLUMN deep_views INTEGER DEFAULT 0",
        "ALTER TABLE articles ADD COLUMN source_published_at TEXT",
        "ALTER TABLE sources ADD COLUMN last_seen_published_at TEXT",
        "ALTER TABLE sources ADD COLUMN last_seen_url TEXT",
        "ALTER TABLE source_items ADD COLUMN retry_after TEXT",
    ]:
        try:
            await db.execute(sql)
        except Exception:
            pass
    defaults = {
        "automation_enabled": "1" if AUTOMATION_ENABLED_DEFAULT else "0",
        "max_daily_posts": str(DEFAULT_MAX_DAILY_POSTS),
        "min_content_score": str(DEFAULT_MIN_CONTENT_SCORE),
        "min_hours_between_posts": str(DEFAULT_MIN_HOURS_BETWEEN_POSTS),
        "min_post_gap_minutes": str(DEFAULT_MIN_POST_GAP_MINUTES),
        "publish_start_hour": str(DEFAULT_PUBLISH_START_HOUR),
        "publish_end_hour": str(DEFAULT_PUBLISH_END_HOUR),
        "default_source_interval": str(DEFAULT_SOURCE_INTERVAL_MINUTES),
        "news_freshness_max_hours": str(int(NEWS_FRESHNESS_MAX_HOURS) if NEWS_FRESHNESS_MAX_HOURS.is_integer() else NEWS_FRESHNESS_MAX_HOURS),
        "news_priority_hours": str(int(NEWS_PRIORITY_HOURS) if NEWS_PRIORITY_HOURS.is_integer() else NEWS_PRIORITY_HOURS),
        "ai_verify_mode": "auto",
        "last_cleanup_at": "",
        "last_manual_channel_post_at": "",
        "channel_id": CHANNEL_ID,
        "channel_username": "",
        "max_workers": str(DEFAULT_MAX_WORKERS),
        "max_ai_workers": str(DEFAULT_MAX_AI_WORKERS),
        "worker_heartbeat_at": "",
        "worker_started_at": "",
        "last_cycle_started_at": "",
        "last_cycle_finished_at": "",
        "last_cycle_result": "",
        "ai_verify_mode": AI_VERIFY_ENABLED_DEFAULT,
        "weight_global": "15",
        "weight_technology": "15",
        "weight_ai": "15",
        "weight_cyber": "15",
        "weight_education": "10",
        "weight_iran": "15",
        "weight_freshness": "10",
        "weight_source": "5",
        "weight_novelty": "10",
        "editorial_prompt_channel": "فقط محتوای فنی و واقعاً ارزشمند برای مخاطب فناوری و هوش مصنوعی را پوشش بده؛ خبرهای سطحی، عمومی، تبلیغاتی، تکراری و پیش‌پاافتاده را کنار بگذار. نکات فنی مهم، قابلیت جدید، تغییر مهم، عدد و جزئیات قابل اتکا را در نسخه کوتاه بیاور.",
        "editorial_prompt_article": "نسخه کامل باید یک محتوای فنی و غنی باشد؛ جزئیات واقعی رویداد، نحوه کار یا فناوری، نکات فنی مهم، زمینه لازم و اثرات قابل فهم را پوشش بده. از حرف‌های کلی، کلیشه‌ای، نتیجه‌گیری شخصی و سؤال‌سازی به جای پاسخ خودداری کن. فقط بر پایه اطلاعات منبع بنویس.",
    }
    for k, v in defaults.items():
        await db.execute("INSERT OR IGNORE INTO automation_settings(key, value) VALUES(?, ?)", [k, v])
    # مهاجرت تنظیم فاصله انتشار: اگر نصب قبلی مقدار ساعتی داشته، همان مقدار به دقیقه منتقل شود.
    try:
        gap_rows = await db.execute("SELECT value FROM automation_settings WHERE key='min_post_gap_minutes'")
        legacy_rows = await db.execute("SELECT value FROM automation_settings WHERE key='min_hours_between_posts'")
        current_gap = float(gap_rows[0].get('value')) if gap_rows and gap_rows[0].get('value') not in (None,'') else 0
        legacy_gap = float(legacy_rows[0].get('value')) if legacy_rows and legacy_rows[0].get('value') not in (None,'') else 0
        if current_gap == DEFAULT_MIN_POST_GAP_MINUTES and legacy_gap > 0 and abs(legacy_gap*60-current_gap) > 0.01:
            await db.execute("UPDATE automation_settings SET value=? WHERE key='min_post_gap_minutes'", [str(int(round(legacy_gap*60)))])
    except Exception:
        pass
    # Provider قدیمی محیطی را از چرخه failover خارج می‌کنیم؛ مدیر فقط مدل‌هایی را که
    # خودش در پنل تست کرده است وارد اتوماسیون می‌کند.
    try:
        await db.execute("UPDATE ai_providers SET enabled=0, status='invalid', last_error='Environment Default disabled by managed-provider mode' WHERE name='Environment Default'")
    except Exception:
        pass
    # Privacy/storage policy: image URLs are transient and never retained in D1.
    try:
        await db.execute("UPDATE source_items SET image_url='' WHERE image_url IS NOT NULL AND image_url!=''")
        await db.execute("UPDATE articles SET image_url='' WHERE image_url IS NOT NULL AND image_url!=''")
        cutoff=(datetime.now(timezone.utc)-timedelta(days=CONTENT_RETENTION_DAYS)).isoformat()
        await db.execute("DELETE FROM source_items WHERE discovered_at < ?", [cutoff])
    except Exception:
        pass


def encrypt_secret(value: str) -> str:
    if not value:
        return ""
    if not AI_PROVIDER_ENCRYPTION_KEY:
        return value
    try:
        return Fernet(AI_PROVIDER_ENCRYPTION_KEY.encode()).encrypt(value.encode()).decode()
    except Exception:
        logger.exception("Failed to encrypt AI provider secret")
        return value


def decrypt_secret(value: str) -> str:
    if not value:
        return ""
    if not AI_PROVIDER_ENCRYPTION_KEY:
        return value
    try:
        return Fernet(AI_PROVIDER_ENCRYPTION_KEY.encode()).decrypt(value.encode()).decode()
    except (InvalidToken, Exception):
        return value


async def get_setting(db: D1Database, key: str, default: str = "") -> str:
    now = time.monotonic()
    cached = SETTINGS_CACHE.get(key)
    if cached and now - cached[1] < SETTINGS_CACHE_TTL:
        return cached[0]
    rows = await db.execute("SELECT value FROM automation_settings WHERE key = ?", [key])
    value = str(rows[0].get("value")) if rows else default
    SETTINGS_CACHE[key] = (value, now)
    return value


async def set_setting(db: D1Database, key: str, value: str):
    await db.execute("INSERT OR REPLACE INTO automation_settings(key, value) VALUES(?, ?)", [key, value])
    SETTINGS_CACHE[key] = (str(value), time.monotonic())


async def get_channel_id(db: D1Database) -> str:
    return (await get_setting(db, "channel_id", CHANNEL_ID)).strip()


async def log_automation(db: D1Database, level: str, event: str, details: str = ""):
    try:
        if len(details) > 2000:
            details = details[:2000]
        await db.execute("INSERT INTO automation_logs(level, event, details, created_at) VALUES(?, ?, ?, ?)", [
            level, event, details, datetime.now(timezone.utc).isoformat()
        ])
    except Exception:
        logger.exception("automation log failed")


async def cleanup_automation_data(db: D1Database):
    now = datetime.now(timezone.utc)
    cutoff_content = (now - timedelta(days=CONTENT_RETENTION_DAYS)).isoformat()
    cutoff_logs = (now - timedelta(days=LOG_RETENTION_DAYS)).isoformat()
    await db.execute("DELETE FROM automation_logs WHERE created_at < ?", [cutoff_logs])
    # source_items is the short-lived duplicate-detection cache. Keep it for one day only.
    # Generated articles remain in `articles` for admin history/editing.
    await db.execute("DELETE FROM source_items WHERE discovered_at < ?", [cutoff_content])
    # Images are transient transport data, never persistent content data.
    await db.execute("UPDATE source_items SET image_url='' WHERE image_url IS NOT NULL AND image_url!=''")
    await db.execute("UPDATE articles SET image_url='' WHERE image_url IS NOT NULL AND image_url!=''")
    await db.execute("DELETE FROM publication_queue WHERE status IN ('published','failed') AND created_at < ?", [cutoff_content])
    await set_setting(db, "last_cleanup_at", now.isoformat())


def normalize_url(url: str) -> str:
    url = (url or "").strip()
    if not url:
        return ""
    parsed = urllib.parse.urlsplit(url if "://" in url else "https://" + url)
    query = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
    query = [(k, v) for k, v in query if not k.lower().startswith(("utm_", "fbclid", "gclid"))]
    return urllib.parse.urlunsplit((parsed.scheme.lower(), parsed.netloc.lower(), parsed.path.rstrip('/') or '/', urllib.parse.urlencode(query), ""))


def same_domain(a: str, b: str) -> bool:
    try:
        return urllib.parse.urlsplit(a).netloc.lower().removeprefix('www.') == urllib.parse.urlsplit(b).netloc.lower().removeprefix('www.')
    except Exception:
        return False


def text_hash(text: str) -> str:
    return hashlib.sha256(re.sub(r"\s+", " ", text or "").strip().lower().encode("utf-8", errors="ignore")).hexdigest()


def normalize_model_text(value: str) -> str:
    """Normalize AI output so escaped newlines never leak into Telegram."""
    if value is None:
        return ""
    text = str(value)
    # Models/gateways sometimes double-escape JSON string content.
    text = text.replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\r", "\n").replace("\\t", "\t")
    # Normalize non-breaking spaces without destroying paragraph boundaries.
    text = text.replace("\u00a0", " ")
    # Excessive blank lines make mobile Telegram posts look robotic.
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n[ \t]+", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()

def strip_html_text(value: str) -> str:
    if not value:
        return ""
    value = normalize_model_text(value)
    value = re.sub(r"<script.*?</script>|<style.*?</style>|<noscript.*?</noscript>", " ", value, flags=re.I | re.S)
    value = re.sub(r"<[^>]+>", " ", value)
    return re.sub(r"\s+", " ", html.unescape(value)).strip()


class SimpleHTMLParser(HTMLParser):
    """سبک و بدون وابستگی برای استخراج داده‌های مقاله و لینک‌ها."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.title = ""
        self.meta = {}
        self.links = []
        self._title_depth = 0
        self._current_link = ""
        self._current_link_text = []
        self._article_depth = 0
        self._paragraph_depth = 0
        self._body_parts = []
        self._skip_depth = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag in {"script", "style", "noscript", "svg"}:
            self._skip_depth += 1
            return
        if self._skip_depth:
            return
        if tag == "title":
            self._title_depth += 1
        if tag == "meta":
            key = attrs.get("property") or attrs.get("name") or attrs.get("itemprop")
            content = attrs.get("content")
            if key and content:
                self.meta[key.lower()] = content.strip()
        if tag == "a":
            href = attrs.get("href") or ""
            self._current_link = href
            self._current_link_text = []
        if tag == "article":
            self._article_depth += 1
        if tag in {"p", "li", "h1", "h2", "h3"}:
            self._paragraph_depth += 1

    def handle_endtag(self, tag):
        if self._skip_depth:
            if tag in {"script", "style", "noscript", "svg"}:
                self._skip_depth -= 1
            return
        if tag == "title" and self._title_depth:
            self._title_depth -= 1
        if tag == "a":
            text = re.sub(r"\s+", " ", " ".join(self._current_link_text)).strip()
            if self._current_link and text:
                self.links.append((self._current_link, text))
            self._current_link = ""
            self._current_link_text = []
        if tag == "article" and self._article_depth:
            self._article_depth -= 1
        if tag in {"p", "li", "h1", "h2", "h3"} and self._paragraph_depth:
            self._paragraph_depth -= 1

    def handle_data(self, data):
        if self._skip_depth:
            return
        data = data.strip()
        if not data:
            return
        if self._title_depth:
            self.title += " " + data
        if self._current_link:
            self._current_link_text.append(data)
        if self._article_depth or self._paragraph_depth:
            self._body_parts.append(data)

    @property
    def body(self):
        return re.sub(r"\s+", " ", " ".join(self._body_parts)).strip()


async def http_get(url: str, session: aiohttp.ClientSession) -> Tuple[str, str]:
    headers={"User-Agent":HTTP_USER_AGENT,"Accept":"text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8","Accept-Language":"fa-IR,fa;q=0.9,en-US;q=0.8,en;q=0.7","Cache-Control":"no-cache"}
    timeout=aiohttp.ClientTimeout(total=HTTP_TIMEOUT_SECONDS)
    last_error=None
    for attempt in range(3):
        try:
            async with session.get(url,headers=headers,timeout=timeout,allow_redirects=True) as resp:
                if resp.status>=400:
                    text=await resp.text(errors="ignore")
                    if resp.status in {429,500,502,503,504} and attempt<2:
                        await asyncio.sleep(0.5*(attempt+1)); continue
                    raise RuntimeError(f"HTTP {resp.status}" + (f": {text[:180]}" if resp.status in {429,500,502,503,504} else ""))
                data=await resp.content.read(MAX_HTTP_BYTES+1)
                if len(data)>MAX_HTTP_BYTES: raise RuntimeError("response too large")
                ctype=resp.headers.get("Content-Type",""); enc=resp.charset or "utf-8"
                return data.decode(enc,errors="ignore"),ctype
        except (aiohttp.ClientError, asyncio.TimeoutError, ConnectionError) as e:
            last_error=e
            if attempt<2:
                await asyncio.sleep(0.5*(attempt+1)); continue
            raise RuntimeError(str(e))
    raise RuntimeError(str(last_error or "request failed"))


def local_name(tag: str) -> str:
    return tag.rsplit('}', 1)[-1].lower()


def xml_child_text(el, names):
    for child in el.iter():
        if local_name(child.tag) in names and child is not el:
            txt = "".join(child.itertext()).strip()
            if txt:
                return html.unescape(txt)
    return ""


def parse_feed(text: str, base_url: str) -> List[Dict[str, Any]]:
    try:
        root = ET.fromstring(text)
    except Exception:
        return []
    items = []
    for el in root.iter():
        if local_name(el.tag) not in {"item", "entry"}:
            continue
        title = xml_child_text(el, {"title"})
        link = ""
        for child in el.iter():
            if local_name(child.tag) == "link":
                href = child.attrib.get("href")
                if href:
                    link = href
                    break
                txt = "".join(child.itertext()).strip()
                if txt:
                    link = txt
                    break
        desc = xml_child_text(el, {"description", "summary", "content"})
        pub = xml_child_text(el, {"pubdate", "published", "updated", "date"})
        image = ""
        for child in el.iter():
            if local_name(child.tag) in {"thumbnail", "content", "image", "enclosure"}:
                u = child.attrib.get("url") or child.attrib.get("href")
                if u:
                    image = u
                    break
        if not link or not title:
            continue
        items.append({"title": strip_html_text(title), "url": urllib.parse.urljoin(base_url, link), "description": strip_html_text(desc), "published_at": pub, "image_url": urllib.parse.urljoin(base_url, image) if image else ""})
    return items


def extract_html_page(html_text: str, url: str) -> Dict[str, Any]:
    p = SimpleHTMLParser()
    p.feed(html_text)
    canonical = p.meta.get("og:url") or p.meta.get("twitter:url") or url
    title = p.meta.get("og:title") or p.meta.get("twitter:title") or p.title
    image = p.meta.get("og:image") or p.meta.get("twitter:image") or ""
    desc = p.meta.get("og:description") or p.meta.get("description") or p.meta.get("twitter:description") or ""
    body = p.body
    links = []
    for href, text in p.links:
        full = normalize_url(urllib.parse.urljoin(url, href))
        if full and same_domain(full, url) and text and len(text) >= 12:
            links.append((full, text[:300]))
    dedup = []
    seen = set()
    for item in links:
        if item[0] not in seen:
            seen.add(item[0]); dedup.append(item)
    published = (p.meta.get("article:published_time") or p.meta.get("datepublished") or p.meta.get("date") or p.meta.get("pubdate") or "").strip()
    if not published:
        m = re.search(r"datePublished\"\s*[:=]\s*\"([^\"]+)\"", html_text, flags=re.I)
        if m: published = m.group(1).strip()
    return {"canonical_url": normalize_url(canonical), "title": strip_html_text(title), "description": strip_html_text(desc), "body": body, "image_url": urllib.parse.urljoin(url, image) if image else "", "published_at": published, "links": dedup}


def article_candidates_from_html(parsed: Dict[str, Any], source_url: str) -> List[Dict[str, Any]]:
    path = urllib.parse.urlsplit(source_url).path.rstrip('/')
    # صفحه ریشه سایت معمولاً صفحه مقاله نیست؛ از آن فقط لینک‌های داخلی را استخراج می‌کنیم.
    if path and len(parsed.get("body", "")) > 700 and parsed.get("title"):
        return [{"title": parsed["title"][:300], "url": parsed["canonical_url"] or source_url, "description": parsed["description"][:1000], "body": parsed["body"][:12000], "image_url": parsed.get("image_url", ""), "published_at": parsed.get("published_at", "")}]
    out = []
    for url, title in parsed.get("links", [])[:MAX_SOURCE_ITEMS_PER_CYCLE]:
        if len(title) < 15:
            continue
        out.append({"title": title, "url": url, "description": "", "body": "", "image_url": "", "published_at": ""})
    return out


def parse_publication_datetime(raw: str) -> Optional[datetime]:
    """Parse common RSS/Atom/ISO date strings into aware UTC datetime."""
    raw = normalize_model_text(raw or "").strip()
    if not raw:
        return None
    candidates = [raw, raw.replace("Z", "+00:00")]
    for value in candidates:
        try:
            dt = datetime.fromisoformat(value)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.astimezone(timezone.utc)
        except Exception:
            pass
    # RFC 2822 / RSS dates
    try:
        from email.utils import parsedate_to_datetime
        dt = parsedate_to_datetime(raw)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        pass
    return None


def candidate_is_fresh(item: Dict[str, Any], now: Optional[datetime] = None, max_hours: float = NEWS_FRESHNESS_MAX_HOURS) -> Tuple[bool, str, Optional[datetime]]:
    now = now or datetime.now(timezone.utc)
    dt = parse_publication_datetime(item.get("published_at") or item.get("source_published_at") or "")
    if not dt:
        return (False, "تاریخ انتشار قابل‌اعتماد نیست", None)
    age_hours = (now - dt).total_seconds() / 3600.0
    if age_hours < -0.5:
        return (False, "تاریخ انتشار آینده/نامعتبر است", dt)
    if age_hours > max_hours:
        return (False, f"محتوا قدیمی است ({age_hours:.1f} ساعت)", dt)
    return (True, f"تازه ({max(0.0, age_hours):.1f} ساعت)", dt)


def freshness_priority(item: Dict[str, Any], now: Optional[datetime] = None, priority_hours: float = NEWS_PRIORITY_HOURS) -> int:
    now=now or datetime.now(timezone.utc)
    dt=parse_publication_datetime(item.get('published_at') or item.get('source_published_at') or '')
    if not dt:
        return 1
    age=(now-dt).total_seconds()/3600.0
    return 0 if age <= priority_hours else 1


def select_latest_fresh_items(items: List[Dict[str, Any]], now: Optional[datetime] = None, max_items: int = MAX_SOURCE_ITEMS_PER_CYCLE) -> Tuple[List[Dict[str, Any]], List[str], Optional[datetime], str]:
    """Keep only the newest items with verifiable timestamps; no geography/language bias."""
    now = now or datetime.now(timezone.utc)
    fresh=[]; diagnostics=[]; newest_dt=None; newest_url=""
    for item in items or []:
        ok, reason, dt = candidate_is_fresh(item, now=now)
        if dt and (newest_dt is None or dt > newest_dt):
            newest_dt=dt; newest_url=normalize_url(item.get("url") or "")
        if ok:
            item=dict(item)
            item["_parsed_published_dt"]=dt
            fresh.append(item)
        else:
            diagnostics.append(f"⏱️ {strip_html_text(str(item.get('title') or ''))[:90]}: {reason}")
    fresh.sort(key=lambda x: (freshness_priority(x, now=now), -(x.get('_parsed_published_dt').timestamp() if x.get('_parsed_published_dt') else 0)))
    for item in fresh:
        item.pop("_parsed_published_dt", None)
    return fresh[:max_items], diagnostics[-10:], newest_dt, newest_url

# ============================================================
# NEW: Insufficient content / paywall detection (replaces length gate)
# ============================================================
PAYWALL_KEYWORDS = [
    "ادامه مطلب", "برای مشاهده", "اشتراک", "محدود", "ثبت نام", "عضویت", 
    "خرید اشتراک", "دسترسی کامل", "متن کامل", "نمایش کامل", "بیشتر بخوانید",
    "continue reading", "subscribe", "sign up", "register", "full access",
    "premium", "paywall", "limited access", "you have reached",
    "already a member", "log in", "login"
]

def is_insufficient_content(title: str, body: str, description: str) -> Tuple[bool, str]:
    """
    Detect if the source content is a paywall teaser or otherwise insufficient.
    Returns (True, reason) if the content should be rejected.
    Accepts genuinely short articles with real information.
    """
    title_plain = strip_html_text(title or "").strip()
    desc_plain = strip_html_text(description or "").strip()
    body_plain = strip_html_text(body or "").strip()
    combined = (title_plain + " " + desc_plain + " " + body_plain).lower()

    # If body is very short (< 20 chars) and title+desc are also short, reject.
    if len(body_plain) < 20 and len(title_plain) < 30 and len(desc_plain) < 50:
        return True, "محتوا بسیار کوتاه و فاقد اطلاعات کافی است"
    
    # Check for paywall keywords in the body/description/title.
    if any(kw in combined for kw in PAYWALL_KEYWORDS):
        # If the body is short and contains such keywords, it's likely a teaser.
        if len(body_plain) < 200:
            return True, "محتوای سرویس اشتراک/پشت پرده است و اطلاعات کافی ندارد"
        # If body is longer but still has paywall phrases, we may still accept if there is real content.
        # For safety, we will reject if body is less than 500 chars and paywall keywords present.
        if len(body_plain) < 500:
            return True, "محتوای سرویس اشتراک/پشت پرده است و اطلاعات کافی ندارد"
    
    # If body length is < 100, but title and desc are informative and no paywall, we might accept.
    if len(body_plain) < 100:
        # Check if title and desc together contain at least 20 words and seem substantive.
        word_count = len(re.findall(r'\w+', title_plain + " " + desc_plain))
        if word_count < 20:
            return True, "محتوا بسیار کوتاه و فاقد اطلاعات کافی است"
    
    # If body has less than 300 characters but contains a date or number, it might still be okay.
    # We'll accept if body has a digit or a date pattern.
    if len(body_plain) < 300:
        if re.search(r'\d{4}[-/]\d{1,2}[-/]\d{1,2}', body_plain) or re.search(r'\d+%', body_plain):
            return False, ""  # Accept: contains numbers/dates
    
    # All good.
    return False, ""

# END new function

async def discover_source_items(source: Dict[str, Any], return_diagnostics: bool = False, use_sitemap: bool = True) -> Any:
    """Discover real articles through several direct methods before giving up.

    Important: a successful feed response is NOT treated as a successful discovery
    if it only contains old items. All direct methods get a chance to contribute,
    then the freshness layer chooses the newest 24h items (0-6h first).
    """
    base = normalize_url(source.get("url", ""))
    session = await get_http_session()
    diagnostics = []
    collected = []
    seen_urls = set()

    def add_items(items, method):
        added = 0
        for item in items or []:
            u = normalize_url(item.get("url") or item.get("canonical_url") or "")
            if not u or u in seen_urls:
                continue
            seen_urls.add(u)
            item = dict(item)
            item["url"] = u
            collected.append(item)
            added += 1
        if added:
            diagnostics.append(f"✅ {method}: {added} مورد دریافت شد")
        return added

    def has_fresh_collected(max_hours: float = NEWS_FRESHNESS_MAX_HOURS) -> bool:
        now=datetime.now(timezone.utc)
        for item in collected:
            dt=parse_publication_datetime(item.get("published_at") or "")
            if dt:
                age=(now-dt).total_seconds()/3600.0
                if -0.5 <= age <= max_hours:
                    return True
        return False

    def result(method="direct"):
        # Keep enough raw items so freshness sorting can choose the best 5 later.
        items = collected[:max(20, MAX_SOURCE_ITEMS_PER_CYCLE * 4)]
        out = {"items": items, "method": method if items else "none", "diagnostics": diagnostics}
        return out if return_diagnostics else out["items"]

    if not base:
        raise RuntimeError("آدرس منبع خالی یا نامعتبر است")

    configured = (source.get("feed_url") or "").strip()
    if configured:
        try:
            feed_text, _ = await http_get(configured, session)
            add_items(parse_feed(feed_text, base), "feed سفارشی")
            if has_fresh_collected():
                return result("configured_feed")
        except Exception as e:
            diagnostics.append(f"⚠️ feed سفارشی: {e}")

    # Always inspect the homepage and every advertised RSS/Atom feed. We do not
    # return early here: an advertised feed may be cached/stale while the homepage
    # or another feed already contains a newer article.
    try:
        homepage_html, _ = await http_get(base, session)
        parsed = extract_html_page(homepage_html, base)
        alternate_feeds = []
        for m in re.finditer(r'<link\b[^>]*>', homepage_html, flags=re.I):
            tag = m.group(0)
            href = re.search(r'href=["\']([^"\']+)', tag, flags=re.I)
            typ = re.search(r'type=["\']([^"\']+)', tag, flags=re.I)
            rel = re.search(r'rel=["\']([^"\']+)', tag, flags=re.I)
            if href and ((typ and any(x in typ.group(1).lower() for x in ("rss", "atom"))) or (rel and "alternate" in rel.group(1).lower())):
                alternate_feeds.append(urllib.parse.urljoin(base, href.group(1)))
        for feed_url in list(dict.fromkeys(alternate_feeds))[:4]:
            try:
                feed_text, _ = await http_get(feed_url, session)
                add_items(parse_feed(feed_text, feed_url), "alternate feed")
            except Exception as e:
                diagnostics.append(f"⚠️ alternate feed: {e}")
        add_items(article_candidates_from_html(parsed, base), "صفحه اصلی")
        if has_fresh_collected():
            return result("homepage_or_alternate_feed")
    except Exception as e:
        diagnostics.append(f"⚠️ صفحه اصلی: {e}")

    # Common feeds are cheap fallbacks and must be checked even when another
    # method already returned something, because that something may be stale.
    for feed_path in ["/feed", "/rss", "/rss.xml", "/feed.xml", "/atom.xml", "/index.xml"]:
        candidate = urllib.parse.urljoin(base + "/", feed_path.lstrip("/"))
        try:
            text, _ = await http_get(candidate, session)
            add_items(parse_feed(text, candidate), f"feed {feed_path}")
            if has_fresh_collected():
                return result(f"common_feed:{feed_path}")
        except Exception:
            # A 404 here is normal; keep the user-facing diagnostics short.
            pass

    wp_url = urllib.parse.urljoin(base + "/", "wp-json/wp/v2/posts?per_page=8&_fields=link,title,excerpt,date,jetpack_featured_media_url")
    try:
        text, _ = await http_get(wp_url, session)
        data = json.loads(text)
        if isinstance(data, list) and data:
            items = []
            for post in data:
                title = strip_html_text(((post.get("title") or {}).get("rendered") or ""))
                url = post.get("link") or ""
                if title and url:
                    items.append({
                        "title": title,
                        "url": url,
                        "description": strip_html_text(((post.get("excerpt") or {}).get("rendered") or "")),
                        "published_at": post.get("date") or "",
                        "image_url": post.get("jetpack_featured_media_url") or ""
                    })
            add_items(items, "WordPress API")
            if has_fresh_collected():
                return result("wordpress_api")
    except Exception:
        pass

    if use_sitemap:
        sitemap = urllib.parse.urljoin(base + "/", "sitemap.xml")
        try:
            sm_text, _ = await http_get(sitemap, session)
            try:
                root = ET.fromstring(sm_text)
                locs = [normalize_url(loc.text.strip()) for loc in root.iter() if local_name(loc.tag) == "loc" and loc.text]
                is_index = local_name(root.tag) == "sitemapindex" or any(local_name(e.tag) == "sitemap" for e in root)
            except Exception as xml_error:
                locs = extract_xml_locs_resilient(sm_text)
                is_index = bool(re.search(r"<sitemap(?:index)?\b", sm_text, re.I))
                diagnostics.append(f"⚠️ XML ناقص بود؛ fallback فعال شد: {xml_error}")
            if is_index:
                child_urls = locs[:6]
                expanded = []
                for child in child_urls:
                    try:
                        ctext, _ = await http_get(child, session)
                        try:
                            cr = ET.fromstring(ctext)
                            expanded.extend(normalize_url(loc.text.strip()) for loc in cr.iter() if local_name(loc.tag) == "loc" and loc.text)
                        except Exception:
                            expanded.extend(extract_xml_locs_resilient(ctext))
                    except Exception as e:
                        diagnostics.append(f"⚠️ child sitemap: {e}")
                locs = expanded or locs
            # Read more than five sitemap URLs, then let the freshness sorter choose.
            candidate_urls = [u for u in locs if u and same_domain(u, base) and u not in seen_urls][:12]

            async def read_one(u):
                try:
                    text, _ = await http_get(u, session)
                    parsed = extract_html_page(text, u)
                    if parsed.get("title"):
                        return {
                            "title": parsed["title"],
                            "url": parsed["canonical_url"] or u,
                            "description": parsed["description"],
                            "body": parsed["body"][:12000],
                            "image_url": parsed["image_url"],
                            "published_at": parsed.get("published_at", "")
                        }
                except Exception:
                    return None
                return None

            sitemap_results = [x for x in await asyncio.gather(*(read_one(u) for u in candidate_urls)) if x]
            add_items(sitemap_results, "sitemap")
        except Exception:
            pass

    if not collected:
        diagnostics.append("🔴 هیچ محتوای مستقیمی از منبع دریافت نشد")
        if return_diagnostics:
            return {"items": [], "method": "none", "diagnostics": diagnostics, "error": "؛ ".join(diagnostics[-8:])}
        raise RuntimeError("source fetch failed: " + ("؛ ".join(diagnostics[-8:]) or "هیچ روش دریافت محتوا موفق نشد"))

    methods = []
    for d in diagnostics:
        if d.startswith("✅"):
            methods.append(d.split(":", 1)[0].replace("✅ ", ""))
    method = "+".join(dict.fromkeys(methods)) or "direct"
    return result(method)

async def enrich_candidate_content(item: Dict[str, Any]) -> Dict[str, Any]:
    if item.get("body") and len(item["body"]) >= 700:
        return item
    session = await get_http_session()
    try:
        text, _ = await http_get(item["url"], session)
        parsed = extract_html_page(text, item["url"])
        item["title"] = item.get("title") or parsed["title"]
        item["description"] = item.get("description") or parsed["description"]
        item["body"] = parsed["body"][:14000]
        item["image_url"] = item.get("image_url") or parsed["image_url"]
        item["links"] = parsed.get("links", [])[:25]
        item["published_at"] = item.get("published_at") or parsed.get("published_at") or ""
        item["url"] = parsed["canonical_url"] or item["url"]
    except Exception:
        pass
    return item

TOPIC_WORDS = re.compile(r"\b(ai|artificial intelligence|machine learning|llm|gpt|gemini|openai|anthropic|claude|robot|cyber|cybersecurity|hack|hacking|malware|ransomware|phishing|zero-day|zero day|exploit|vulnerability|security|technology|tech|software|chip|nvidia|microsoft|google|apple|meta|startup|model|browser|cloud|linux|python|developer|api|data breach|privacy)\b", re.I)

def heuristic_topic_match(title: str, description: str, category: str) -> bool:
    if category.lower() in {"ai", "tech", "technology", "cyber", "security", "education", "edu"}:
        return True
    return bool(TOPIC_WORDS.search((title or "") + " " + (description or "")))


def recent_semantic_similarity(title: str, recent_titles: List[str]) -> float:
    best = 0.0
    a = (title or "").lower()
    for t in recent_titles:
        b = (t or "").lower()
        best = max(best, SequenceMatcher(None, a, b).ratio())
    return best


def parse_json_object(text: str) -> Dict[str, Any]:
    text = (text or "").strip()
    if text.startswith("```"):
        text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.I | re.S).strip()
    def _loads(candidate: str):
        try:
            obj = json.loads(candidate)
            return obj if isinstance(obj, dict) else {}
        except Exception:
            # Recover stray backslashes that are illegal JSON escape sequences.
            repaired = re.sub(r"\\(?![\"/bfnrt]|u[0-9a-fA-F]{4})", lambda m: "\\\\", candidate)
            try:
                obj = json.loads(repaired)
                return obj if isinstance(obj, dict) else {}
            except Exception:
                return {}
    obj = _loads(text)
    if obj:
        return obj
    m = re.search(r"\{.*\}", text, flags=re.S)
    return _loads(m.group(0)) if m else {}


class AIProviderManager:
    """AI provider manager with shared HTTP session, cooldown, failover and basic native protocol support."""
    def __init__(self, db: D1Database, bot: Optional[Bot] = None):
        self.db=db
        self.bot=bot
        self._session: Optional[aiohttp.ClientSession]=None
        self._notify_lock=asyncio.Lock()
        self._last_final_notice=0.0

    async def start(self):
        if self._session is None or self._session.closed:
            self._session=aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=45))

    async def close(self):
        if self._session and not self._session.closed:
            await self._session.close()
        self._session=None

    async def providers(self):
        now=datetime.now(timezone.utc).isoformat()
        return await self.db.execute(
            "SELECT * FROM ai_providers WHERE enabled=1 AND (status IS NULL OR status!='invalid' OR cooldown_until IS NULL OR cooldown_until<=?) ORDER BY priority ASC,id ASC",[now]
        )

    @staticmethod
    def protocol(url:str)->str:
        # Detect wire protocol from URL.
        u=(url or "").lower().rstrip("/")
        if "generativelanguage.googleapis.com" in u:
            if "/openai" in u or "chat/completions" in u:
                return "openai"
            return "gemini"
        if "api.anthropic.com" in u and "/chat/completions" not in u:
            return "anthropic"
        return "openai"

    @staticmethod
    def endpoint(url:str, protocol:str, model:str="")->str:
        u=(url or "").strip().rstrip("/")
        if protocol=="gemini":
            if u.endswith(":generateContent"): return u
            if "/models/" in u: return u+":generateContent"
            return u + f"/models/{urllib.parse.quote(model, safe='')}:generateContent"
        if protocol=="anthropic":
            return u if u.endswith("/messages") else u+"/v1/messages" if not u.endswith("/v1") else u+"/messages"
        if u.endswith("/chat/completions"): return u
        if u.endswith("/v1"): return u+"/chat/completions"
        if u.endswith("/openai"): return u+"/chat/completions"
        return u+"/chat/completions"

    @staticmethod
    def google_openai_endpoint(base_url:str)->str:
        u=(base_url or "").strip().rstrip("/")
        if "generativelanguage.googleapis.com" not in u:
            return ""
        if "/openai" in u:
            return u if u.endswith("/chat/completions") else u+"/chat/completions"
        return "https://generativelanguage.googleapis.com/v1beta/openai/chat/completions"

    @staticmethod
    def _extract_content(protocol:str, data:dict)->str:
        if protocol=="anthropic":
            return "".join((b.get("text","") for b in data.get("content",[]) if isinstance(b,dict) and b.get("type")=="text"))
        if protocol=="gemini":
            parts=[]
            for candidate in data.get("candidates") or []:
                content=candidate.get("content") or {}
                for part in content.get("parts") or []:
                    if isinstance(part,dict) and part.get("text"):
                        parts.append(str(part.get("text")))
            return "".join(parts).strip()
        choice=(data.get("choices") or [{}])[0] or {}
        message=choice.get("message") or {}
        content=message.get("content")
        if isinstance(content,str): return content.strip()
        if isinstance(content,list):
            return "".join(str(x.get("text","")) for x in content if isinstance(x,dict)).strip()
        return str(content or "").strip()

    @staticmethod
    def _empty_response_reason(protocol:str, data:dict)->str:
        if not isinstance(data,dict): return "بدنه پاسخ JSON قابل تشخیص نبود."
        if protocol=="gemini":
            reasons=[]
            pf=data.get("promptFeedback") or {}
            if pf.get("blockReason"): reasons.append(f"promptFeedback.blockReason={pf.get('blockReason')}")
            for c in data.get("candidates") or []:
                if c.get("finishReason"): reasons.append(f"finishReason={c.get('finishReason')}")
                if c.get("finishMessage"): reasons.append(f"finishMessage={c.get('finishMessage')}")
                if c.get("safetyRatings"): reasons.append("safetyRatings=present")
            return "؛ ".join(reasons) or "Gemini پاسخ HTTP موفق داد اما متن قابل استخراجی نداشت."
        if protocol=="anthropic":
            return str(data.get("stop_reason") or data.get("error") or "Anthropic متن قابل استخراجی نداشت.")
        choices=data.get("choices") or []
        if choices:
            c=choices[0] or {}
            return f"finish_reason={c.get('finish_reason') or '-'}؛ message.content خالی است."
        return "پاسخ API فاقد choices بود."

    async def _request(self, provider, messages, temperature, max_tokens, forced_protocol:Optional[str]=None, forced_endpoint:Optional[str]=None):
        await self.start()
        key=decrypt_secret(provider.get("encrypted_api_key") or "")
        model=(provider.get("model_name") or "").strip()
        base=provider.get("base_url") or ""
        protocol=forced_protocol or self.protocol(base)
        endpoint=forced_endpoint or self.endpoint(base,protocol,model)
        headers={"Content-Type":"application/json","User-Agent":HTTP_USER_AGENT}
        started=time.perf_counter()

        if protocol=="anthropic":
            headers["x-api-key"]=key
            headers["anthropic-version"]="2023-06-01"
            system="\n".join(m.get("content","") for m in messages if m.get("role")=="system").strip()
            msgs=[{"role":"assistant" if m.get("role")=="assistant" else "user","content":m.get("content","")} for m in messages if m.get("role")!="system"]
            payload={"model":model,"messages":msgs,"max_tokens":max_tokens,"temperature":temperature}
            if system: payload["system"]=system
        elif protocol=="gemini":
            headers["x-goog-api-key"]=key
            parts=[{"text":m.get("content","")} for m in messages if m.get("role")!="system"]
            payload={"contents":[{"role":"user","parts":parts or [{"text":""}]}],"generationConfig":{"temperature":temperature,"maxOutputTokens":max_tokens}}
            sys="\n".join(m.get("content","") for m in messages if m.get("role")=="system").strip()
            if sys: payload["systemInstruction"]={"parts":[{"text":sys}]}
        else:
            headers["Authorization"]=f"Bearer {key}"
            payload={"model":model,"messages":messages,"temperature":temperature,"max_tokens":max_tokens}

        async with self._session.post(endpoint,headers=headers,json=payload) as resp:
            raw=await resp.text()
            latency=int((time.perf_counter()-started)*1000)
            if resp.status!=200:
                raise RuntimeError(f"HTTP {resp.status} | endpoint={endpoint} | body={raw[:1400]}")
            try: data=json.loads(raw)
            except Exception as e: raise RuntimeError(f"HTTP 200 ولی JSON نامعتبر بود: {e} | body={raw[:900]}")
            content=self._extract_content(protocol,data)
            usage=(data.get("usageMetadata") if protocol=="gemini" else data.get("usage")) or {}
            if not content:
                raise RuntimeError(f"پاسخ مدل خالی بود | protocol={protocol} | model={model} | {self._empty_response_reason(protocol,data)} | response={json.dumps(data,ensure_ascii=False)[:1800]}")
            return content,data,latency,usage,protocol,endpoint

    async def test_provider_values(self, base_url, api_key, model):
        """Universal provider test.

        The test intentionally follows the proven minimal OpenAI-compatible request
        used by the reference bot: model + messages only.  A GET /models preflight is
        NOT required because many gateways disable /models while /chat/completions
        works perfectly.  For Gemini/Anthropic native endpoints we use their native
        wire format.  If the minimal OpenAI-compatible request fails with a 4xx, a
        second compatibility attempt adds temperature/max_tokens so providers that
        require those fields can still be accepted.
        """
        await self.start()
        base=(base_url or "").strip(); key=(api_key or "").strip(); mdl=(model or "").strip()
        if not base:
            return {"ok":False,"stage":"validation","error":"Base URL خالی است."}
        if not key:
            return {"ok":False,"stage":"validation","error":"API Key/Token خالی است."}
        if not mdl:
            return {"ok":False,"stage":"validation","error":"نام دقیق مدل خالی است."}

        detected=self.protocol(base)
        candidates=[(detected,self.endpoint(base,detected,mdl))]
        # Gemini can be supplied either as native v1beta or as Google's official
        # OpenAI-compatible endpoint. Try the alternate wire format too.
        if "generativelanguage.googleapis.com" in base:
            compat=self.google_openai_endpoint(base)
            if compat and all(ep != compat for _,ep in candidates):
                candidates.append(("openai",compat))
            native=self.endpoint("https://generativelanguage.googleapis.com/v1beta","gemini",mdl)
            if all(ep != native for _,ep in candidates):
                candidates.append(("gemini",native))

        diagnostics=[]
        for proto, endpoint in candidates:
            started=time.perf_counter()
            try:
                headers={"Content-Type":"application/json","User-Agent":HTTP_USER_AGENT}
                if proto=="anthropic":
                    headers["x-api-key"]=key
                    headers["anthropic-version"]="2023-06-01"
                    payload={
                        "model":mdl,
                        "messages":[{"role":"user","content":"Reply with exactly: TEST_OK"}],
                        "max_tokens":32,
                    }
                elif proto=="gemini":
                    headers["x-goog-api-key"]=key
                    payload={
                        "contents":[{"role":"user","parts":[{"text":"Reply with exactly: TEST_OK"}]}],
                        "generationConfig":{"maxOutputTokens":32},
                    }
                else:
                    # Deliberately minimal: this is the same compatibility trick as
                    # the reference bot and avoids gateways rejecting optional fields.
                    headers["Authorization"]=f"Bearer {key}"
                    payload={
                        "model":mdl,
                        "messages":[{"role":"user","content":"Reply with exactly: TEST_OK"}],
                    }

                async with self._session.post(endpoint,headers=headers,json=payload,timeout=aiohttp.ClientTimeout(total=30)) as resp:
                    raw=await resp.text()
                    latency=int((time.perf_counter()-started)*1000)
                    try:
                        data=json.loads(raw)
                    except Exception:
                        data={}

                    if resp.status==200:
                        content=self._extract_content(proto,data)
                        if content:
                            return {
                                "ok":True,
                                "latency_ms":latency,
                                "preview":content.strip()[:120],
                                "usage":(data.get("usageMetadata") if proto=="gemini" else data.get("usage")) or {},
                                "protocol":proto,
                                "endpoint":endpoint,
                                "preflight":"skipped_by_design",
                                "diagnostics":diagnostics,
                            }
                        reason=self._empty_response_reason(proto,data)
                        diagnostics.append(f"{proto} HTTP 200 اما پاسخ قابل استخراج نبود: {reason} | response={raw[:1800]}")
                        continue

                    # A second, still conservative OpenAI-compatible attempt. Some
                    # gateways require max_tokens/temperature even though the minimal
                    # request is otherwise valid.
                    if proto=="openai" and resp.status in {400,422}:
                        retry_payload={**payload,"temperature":0,"max_tokens":32}
                        retry_started=time.perf_counter()
                        async with self._session.post(endpoint,headers=headers,json=retry_payload,timeout=aiohttp.ClientTimeout(total=30)) as r2:
                            raw2=await r2.text()
                            retry_latency=int((time.perf_counter()-retry_started)*1000)
                            try: data2=json.loads(raw2)
                            except Exception: data2={}
                            if r2.status==200:
                                content2=self._extract_content("openai",data2)
                                if content2:
                                    return {
                                        "ok":True,
                                        "latency_ms":retry_latency,
                                        "preview":content2.strip()[:120],
                                        "usage":data2.get("usage") or {},
                                        "protocol":"openai",
                                        "endpoint":endpoint,
                                        "preflight":"skipped_by_design",
                                        "diagnostics":diagnostics,
                                        "compat_retry":True,
                                    }
                            diagnostics.append(f"openai retry HTTP {r2.status}: {raw2[:1400]}")
                    diagnostics.append(f"{proto} HTTP {resp.status}: endpoint={endpoint} | body={raw[:1600]}")
            except Exception as e:
                diagnostics.append(f"{proto} {endpoint}: {type(e).__name__}: {str(e)[:1800]}")

        return {
            "ok":False,
            "stage":"request",
            "protocol":detected,
            "endpoint":candidates[0][1] if candidates else "",
            "error":"\n\n".join(diagnostics)[:7000],
            "diagnostics":diagnostics,
        }

    async def test_provider(self, provider_id:int):
        rows=await self.db.execute("SELECT * FROM ai_providers WHERE id=?",[provider_id])
        if not rows: return {"ok":False,"error":"Provider یافت نشد"}
        p=rows[0]
        result=await self.test_provider_values(p.get("base_url",""),decrypt_secret(p.get("encrypted_api_key","")),p.get("model_name",""))
        now=datetime.now(timezone.utc).isoformat()
        if result["ok"]:
            was_unhealthy=bool(p.get("last_error")) or p.get("status") in {"invalid","cooldown"}
            await self.db.execute("UPDATE ai_providers SET status='healthy',last_error=NULL,cooldown_until=NULL,last_checked_at=?,last_latency_ms=?,consecutive_failures=0,updated_at=? WHERE id=?",[now,result.get("latency_ms",0),now,provider_id])
            if was_unhealthy and self.bot and ADMIN_ID:
                try: await self.bot.send_message(ADMIN_ID,f"✅ <b>مدل دوباره فعال شد</b>\n\nModel: <code>{html.escape(str(p.get('model_name')))}</code>\nLatency: {result.get('latency_ms',0)}ms",parse_mode="HTML")
                except Exception: pass
        else:
            error_text=str(result.get("error","") or "")
            kind=self.classify_error(error_text)
            status='invalid' if kind=='invalid' else 'cooldown'
            minutes=AI_PROVIDER_RECHECK_MINUTES if kind=='invalid' else max(3, AI_PROVIDER_RECHECK_MINUTES)
            cooldown=(datetime.now(timezone.utc)+timedelta(minutes=minutes)).isoformat()
            await self.db.execute("UPDATE ai_providers SET status=?,last_error=?,cooldown_until=?,last_checked_at=?,updated_at=? WHERE id=?",[status,error_text[:1200],cooldown,now,now,provider_id])
        return result

    @staticmethod
    def classify_error(msg:str)->str:
        m=msg.lower()
        if any(x in m for x in ("404","model_not_found","401","403","authentication","invalid api")): return "invalid"
        return "temporary"

    async def call(self,messages,temperature=0.2,max_tokens=2500,purpose="generic",progress=None):
        providers=await self.providers()
        if not providers:
            return {"content":"","provider":None,"model":None,"tokens":0,"error":"هیچ مدل فعالی در پنل AI وجود ندارد."}
        errors=[]; tried=0; now=datetime.now(timezone.utc)
        for p in providers:
            cooldown=p.get("cooldown_until") or ""
            if cooldown:
                try:
                    if datetime.fromisoformat(cooldown.replace("Z","+00:00"))>now: continue
                except Exception: pass
            tried+=1
            model_label=str(p.get("model_name") or p.get("name") or "مدل")
            if progress:
                try: await progress(f"🤖 دارم {model_label} را امتحان می‌کنم…")
                except Exception: pass
            try:
                content,data,latency,usage,_,_=await self._request(p,messages,temperature,max_tokens)
                t=datetime.now(timezone.utc).isoformat()
                was_unhealthy=bool(p.get("last_error")) or p.get("status") in {"invalid","cooldown"}
                await self.db.execute("UPDATE ai_providers SET status='healthy',last_error=NULL,cooldown_until=NULL,last_checked_at=?,last_latency_ms=?,consecutive_failures=0,updated_at=? WHERE id=?",[t,latency,t,p["id"]])
                if was_unhealthy and self.bot and ADMIN_ID:
                    try: await self.bot.send_message(ADMIN_ID,f"✅ <b>مدل دوباره فعال شد</b>\n\nModel: <code>{html.escape(str(p.get('model_name')))}</code>\nLatency: {latency}ms",parse_mode="HTML")
                    except Exception: pass
                if progress:
                    try: await progress(f"✅ {model_label} جواب داد؛ دارم نتیجه را آماده می‌کنم…")
                    except Exception: pass
                return {"content":content,"provider":p.get("name"),"model":p.get("model_name"),"tokens":usage.get("total_tokens",0) if isinstance(usage,dict) else 0,"error":None}
            except Exception as e:
                msg=str(e); errors.append(f"{p.get('name')}: {msg[:220]}")
                if progress:
                    try: await progress(f"⚠️ {model_label} جواب نداد؛ دلیل: {msg[:140]}. دارم مدل بعدی را امتحان می‌کنم…")
                    except Exception: pass
                kind=self.classify_error(msg)
                status="invalid" if kind=="invalid" else "cooldown"
                cd=(datetime.now(timezone.utc)+timedelta(minutes=AI_PROVIDER_RECHECK_MINUTES if kind=="invalid" else 5)).isoformat()
                await self.db.execute("UPDATE ai_providers SET status=?,last_error=?,cooldown_until=?,consecutive_failures=COALESCE(consecutive_failures,0)+1,last_checked_at=?,updated_at=? WHERE id=?",[status,msg[:1200],cd,datetime.now(timezone.utc).isoformat(),datetime.now(timezone.utc).isoformat(),p["id"]])
        final=("همه مدل‌ها در cooldown یا نامعتبر هستند." if tried==0 else "تمام مدل‌های قابل استفاده خطا دادند.")+" | "+" | ".join(errors)
        if purpose!="user_chat" and time.time()-self._last_final_notice>600 and self.bot:
            self._last_final_notice=time.time()
            try: await self.bot.send_message(ADMIN_ID,"🚨 خطای نهایی AI\n"+html.escape(final[:1500]))
            except Exception: pass
        return {"content":"","provider":None,"model":None,"tokens":0,"error":final}# ... continued from part 1 ...

async def ai_analyze_candidate(ai: AIProviderManager, item: Dict[str, Any], source: Dict[str, Any], recent_titles: List[str]) -> Dict[str, Any]:
    body = (item.get("body") or item.get("description") or "")[:10000]
    sim = recent_semantic_similarity(item.get("title", ""), recent_titles)
    prompt = f"""تو سردبیر ارشد یک کانال فارسی درباره تکنولوژی، هوش مصنوعی، ابزارها، مدل‌های AI، امنیت سایبری و اخبار مهم فناوری هستی.\n\nمنبع: {source.get('name')}\nدسته منبع: {source.get('category')}\nعنوان: {item.get('title')}\nلینک: {item.get('url')}\nتاریخ انتشار احتمالی: {item.get('published_at')}\nخلاصه/متن: {body}\nشباهت متنی اولیه با عناوین اخیر: {sim:.2f}\n\nبررسی کن آیا این محتوا ارزش انتشار برای فارسی‌زبانان، مخصوصاً ایران، دارد. clickbait، تبلیغ کم‌ارزش، شایعه، محتوای تکراری و خبرهای فاقد ارزش را رد کن. اگر اطلاعات برای تصمیم‌گیری کافی نیست، رد کن.\n\nفقط JSON معتبر برگردان با این فیلدها:\n{{\n  "accept": true/false,\n  "score": 0-100,\n  "category": "ai|tech|cyber|edu|general",\n  "importance_reason": "...",\n  "iran_relevance": 0-10,\n  "freshness": 0-10,\n  "reliability": 0-10,\n  "duplicate_risk": 0-10,\n  "event_date": "...",\n  "why": "..."\n}}"""
    result = await ai.call([{"role": "system", "content": "You are a strict editorial gate. Output JSON only."}, {"role": "user", "content": prompt}], temperature=0.1, max_tokens=900, purpose="candidate_scoring")
    obj = parse_json_object(result.get("content", ""))
    if not obj:
        return {"accept": False, "score": 0, "reason": "AI returned invalid JSON", "ai": result}
    return {**obj, "ai": result}


async def ai_generate_content(ai: AIProviderManager, item: Dict[str, Any], analysis: Dict[str, Any], source: Dict[str, Any]) -> Dict[str, Any]:
    source_text = (item.get("body") or item.get("description") or "")[:14000]
    prompt = f"""برای یک کانال فارسی حرفه‌ای در حوزه تکنولوژی، هوش مصنوعی، ابزارها، مدل‌ها و امنیت سایبری محتوا تولید کن.\n\nمنبع: {source.get('name')}\nURL: {item.get('url')}\nعنوان منبع: {item.get('title')}\nتحلیل قبلی: {json.dumps(analysis, ensure_ascii=False)}\nمتن منبع:\n{source_text}\n\nخروجی فقط JSON معتبر باشد:\n{{\n  "title": "عنوان دقیق و جذاب بدون clickbait",\n  "channel_text": "متن غنی و مستقل برای کانال، ترجیحاً 400 تا 600 کاراکتر، که خود خبر را توضیح دهد و در انتها جای لینک بیشتر داشته باشد. لینک را خودت ننویس.",\n  "article_text": "مقاله عمیق‌تر و مستقل برای داخل ربات. فقط تکرار channel_text نباشد. زمینه، اتفاق اصلی، جزئیات، اهمیت، اثرات، کاربرد، وضعیت کاربران و ایران در صورت ارتباط، محدودیت‌ها و جمع‌بندی را پوشش بده. طول متناسب با موضوع باشد.",\n  "category": "ai|tech|cyber|edu|general",\n  "facts": ["..."],\n  "image_note": "brief reason if source image is suitable"\n}}\n\nدر article_text هیچ ادعای مهمی که از منبع یا تحلیل داده‌ها پشتیبانی نمی‌شود نساز. فارسی طبیعی و خوانا بنویس."""
    result = await ai.call([{"role": "system", "content": "You are an expert Persian technology editor. Output JSON only."}, {"role": "user", "content": prompt}], temperature=0.35, max_tokens=4500, purpose="content_generation")
    obj = parse_json_object(result.get("content", ""))
    if not obj:
        return {"error": "invalid generation JSON", "ai": result}
    return {**obj, "ai": result}


async def ai_verify_content(ai: AIProviderManager, item: Dict[str, Any], generated: Dict[str, Any]) -> Dict[str, Any]:
    prompt = f"""محتوای زیر را با منبع مقایسه کن.\n\nSOURCE:\nعنوان: {item.get('title')}\nURL: {item.get('url')}\nمتن: {(item.get('body') or item.get('description') or '')[:12000]}\n\nGENERATED:\n{json.dumps(generated, ensure_ascii=False)}\n\nفقط JSON معتبر بده:\n{{\n "ok": true/false,\n "issues": ["..."],\n "confidence": 0-100\n}}\n\nهر ادعای ساخته‌شده، تاریخ/عدد نادرست، تناقض، hallucination یا تکرار ضعیف را مشکل بدان."""
    result = await ai.call([{"role": "system", "content": "You are a strict fact-checking editor. Output JSON only."}, {"role": "user", "content": prompt}], temperature=0, max_tokens=1200, purpose="content_verification")
    obj = parse_json_object(result.get("content", ""))
    return obj if obj else {"ok": False, "issues": ["invalid verifier response"], "confidence": 0}


def make_deep_token(article_id: int) -> str:
    return hashlib.sha256(f"techhow-{article_id}-{time.time_ns()}".encode()).hexdigest()[:18]



class TelegramHTMLSanitizer(HTMLParser):
    ALLOWED = {"b","strong","i","em","u","s","del","code","pre","blockquote","a","tg-spoiler"}
    BLOCK = {"p","div","section","article","header","footer","h1","h2","h3","h4","h5","h6","ul","ol","li"}
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.out=[]
    def _newline(self, count=1):
        if not self.out:
            return
        current="".join(self.out)
        target="\n"*count
        if not current.endswith(target):
            self.out.append(target)
    def handle_data(self, data):
        data=str(data or "").replace("\\r\\n","\n").replace("\\n","\n").replace("\\r","\n").replace("\\t","\t").replace("\u00a0"," ")
        data=re.sub(r"\n{3,}","\n\n",data)
        if data:
            self.out.append(html.escape(data, quote=False))
    def handle_starttag(self, tag, attrs):
        tag=tag.lower()
        if tag in self.BLOCK:
            self._newline(2 if tag in {"p","div","section","article","header","footer","h1","h2","h3","h4","h5","h6"} else 1)
            if tag=="li":
                self.out.append("• ")
            return
        if tag not in self.ALLOWED:
            return
        if tag=="a":
            href=dict(attrs).get("href","")
            if href.startswith(("https://","http://","tg://")):
                self.out.append(f'<a href="{html.escape(href,quote=True)}">')
        else:
            self.out.append(f"<{tag}>")
    def handle_startendtag(self, tag, attrs):
        if tag.lower()=="br":
            self._newline(1)
    def handle_endtag(self, tag):
        tag=tag.lower()
        if tag in self.BLOCK:
            self._newline(1)
            return
        if tag in self.ALLOWED and tag!="a":
            self.out.append(f"</{tag}>")
        elif tag=="a":
            self.out.append("</a>")

def sanitize_telegram_html(value: str) -> str:
    value = normalize_model_text(value)
    # Some gateways return escaped HTML tags; restore only Telegram-safe structural tags.
    value = re.sub(r"&lt;\s*(/?\s*(?:blockquote|b|strong|i|em|u|s|del|code|pre|tg-spoiler|a))(.*?)\s*&gt;", r"<\1\2>", value, flags=re.I|re.S)
    value = re.sub(r"<[^>]+>", lambda m: re.sub(r"[\u200e\u200f\u202a-\u202e\u2066-\u2069]", "", m.group(0)), value)
    if not value: return ""
    try:
        p=TelegramHTMLSanitizer(); p.feed(value); p.close()
        result="".join(p.out)
        result=re.sub(r"[ \t]+\n", "\n", result)
        result=re.sub(r"\n[ \t]+", "\n", result)
        result=re.sub(r"\n{3,}", "\n\n", result)
        return result.strip()
    except Exception:
        return html.escape(strip_html_text(value), quote=False)

def plain_len(value: str) -> int:
    return len(strip_html_text(value or ""))

def _format_technical_tokens(text: str) -> str:
    # Add <code> only to clearly technical tokens; never invent facts.
    patterns = [
        r"\b(?:GPT-\d+(?:\.\d+)?|GPT-4o|LLM|API|JSON|Python|JavaScript|TypeScript|HTML|CSS|SQL|HTTP|HTTPS|OAuth|WebSocket|RAG|GPU|CPU|SDK)\b",
        r"\b(?:Generative AI|Machine Learning|Zero[- ]Day|Phishing|Ransomware)\b",
    ]
    out=text
    for pat in patterns:
        out=re.sub(pat, lambda m: f"<code>{m.group(0)}</code>", out, flags=re.I)
    return out

def _normalize_text_blocks(value: str) -> str:
    value=(value or "").replace("\r\n","\n").replace("\r","\n")
    # Convert literal backslash-n sequences from model output into real line breaks.
    value=value.replace("\\n","\n")
    value=re.sub(r"<br\s*/?>","\n",value,flags=re.I)
    value=re.sub(r"[ \t]+"," ",value)
    value=re.sub(r"[ \t]*\n[ \t]*", "\n", value)
    value=re.sub(r"\n{3,}","\n\n",value)
    return value.strip()

def _protect_bidi_latin(text: str) -> str:
    """Protect RTL/LTR runs without ever inserting direction marks inside HTML tags."""
    if not text: return text
    parts=re.split(r"(<[^>]+>)", text, flags=re.I|re.S)
    out=[]
    for part in parts:
        if part.startswith("<") and part.endswith(">"):
            out.append(re.sub(r"[\u200e\u200f\u202a-\u202e\u2066-\u2069]", "", part))
        else:
            out.append(re.sub(r"(?<![A-Za-z0-9])([A-Za-z][A-Za-z0-9@._+/#:-]{1,64})(?![A-Za-z0-9])", lambda m: "\u200e"+m.group(1)+"\u200e", part))
    return "".join(out)

def _split_readable_paragraphs(value: str, max_chars: int = 520) -> List[str]:
    """Split long AI paragraphs into mobile-friendly blocks without changing wording."""
    raw=_normalize_text_blocks(value or "")
    blocks=[x.strip() for x in re.split(r"\n\s*\n+", raw) if strip_html_text(x).strip()]
    if not blocks: return []
    out=[]
    for block in blocks:
        plain=strip_html_text(block).strip()
        if len(plain)<=max_chars:
            out.append(block); continue
        # Sentence-aware split. Keep each chunk intact and avoid single giant paragraphs.
        sentences=re.split(r"(?<=[.!?؟:])\s+", block)
        current=""
        for sent in sentences:
            sent=sent.strip()
            if not sent: continue
            candidate=(current+" "+sent).strip()
            if current and len(strip_html_text(candidate))>max_chars:
                out.append(current.strip()); current=sent
            else:
                current=candidate
        if current: out.append(current.strip())
    return out

def _remove_duplicate_title_from_body(title: str, value: str) -> str:
    text=_normalize_text_blocks(value or "")
    title_plain=strip_html_text(title or "").strip()
    if not text or not title_plain: return text
    blocks=[x.strip() for x in re.split(r"\n\s*\n+", text) if strip_html_text(x).strip()]
    if not blocks: return text
    kept=[]
    # Remove every duplicated title-like leading block, not only the first one.
    skipping=True
    for block in blocks:
        plain=strip_html_text(block).strip()
        sim=SequenceMatcher(None, plain.lower(), title_plain.lower()).ratio() if plain else 0
        looks_like_title=(sim >= 0.72 or (title_plain.lower() in plain.lower() and len(plain) <= max(40,len(title_plain)*1.8)))
        if skipping and looks_like_title:
            continue
        skipping=False
        kept.append(block)
    return "\n\n".join(kept)

def _mandatory_quote_block(paragraphs: List[str], start_index: int = 1) -> Tuple[str, int]:
    """Return one short Telegram-safe quote and the paragraph it replaces."""
    if not paragraphs:
        return "", -1
    order=list(range(start_index,len(paragraphs)))+list(range(0,start_index))
    for idx in order:
        plain=strip_html_text(paragraphs[idx]).strip()
        if len(plain) < 20:
            continue
        sentences=[x.strip() for x in re.split(r"(?<=[.!?؟])\s+", plain) if x.strip()]
        excerpt=next((x for x in sentences if 20 <= len(x) <= 220), "")
        if not excerpt:
            excerpt=plain[:180].rsplit(" ",1)[0]+("…" if len(plain)>180 else "")
        return f"<blockquote>🔎 {html.escape(excerpt, quote=False)}</blockquote>", idx
    return "", -1


def _visualize_plain_paragraphs(title: str, value: str, category: str, article: bool=False) -> str:
    value=_remove_duplicate_title_from_body(title, value or "")
    value=re.sub(r"</?blockquote[^>]*>", "", value, flags=re.I)
    clean=sanitize_telegram_html(_normalize_text_blocks(value))
    plain=strip_html_text(clean)
    if not plain: return ""
    emoji_map={"ai":["🤖","🧠","🔬","⚡","🧩"],"cyber":["🛡️","🔐","🚨","⚠️","🔎"],"tech":["💻","⚙️","🚀","🔎","🧪"],"edu":["📚","💡","🧭","📝","🎓"],"general":["🌐","✨","📌","🔭","🧭"]}
    icons=emoji_map.get(category,emoji_map["tech"])
    paragraphs=_split_readable_paragraphs(clean, max_chars=430 if not article else 560) or [clean]
    out=[f"<b>{icons[0]} {html.escape(strip_html_text(title)[:220])}</b>"]
    quote, quote_index = _mandatory_quote_block(paragraphs, start_index=1)
    last_icon=None
    for i,para in enumerate(paragraphs[:12]):
        pplain=strip_html_text(para).strip()
        title_similarity=SequenceMatcher(None,pplain.lower(),strip_html_text(title).lower()).ratio()
        if not pplain or title_similarity>0.82: continue
        if i==quote_index:
            out.append(quote)
            continue
        icon=icons[i%len(icons)]
        if icon==last_icon: icon=icons[(i+1)%len(icons)]
        last_icon=icon
        has_rich=any(tag in para.lower() for tag in ("<b>","<strong>","<i>","<em>","<u>","<s>","<a ","<pre>","<code>"))
        if has_rich:
            formatted=_protect_bidi_latin(para.strip())
        else:
            formatted=_format_technical_tokens(_protect_bidi_latin(html.escape(pplain,quote=False)))
        if i==1:
            formatted=f"{icon} <b>{formatted}</b>"
        elif i==3 and len(pplain)<=140:
            formatted=f"{icon} <i>{formatted}</i>"
        else:
            formatted=f"{icon} {formatted}"
        out.append(formatted)
    return dedupe_adjacent_emojis("\n\n".join(out))

def ensure_rich_channel_format(title: str, value: str, category: str = "tech") -> str:
    return _visualize_plain_paragraphs(title, clean_channel_copy(value or ""), category, article=False)

def ensure_rich_article_format(title: str, value: str, source_url: str) -> str:
    clean=_normalize_text_blocks(value or "")
    if not strip_html_text(sanitize_telegram_html(clean)):
        # Do not return placeholder; return empty so the pipeline can reject.
        return ""
    return _visualize_plain_paragraphs(title, clean, "tech", article=True)

def remove_article_metadata_blocks(value: str) -> str:
    text=_normalize_text_blocks(value or "")
    text=re.sub(r"(?:<u>)?\s*🔗\s*لینک(?:‌| )های مرتبط.*$","",text,flags=re.I|re.S)
    text=re.sub(r"\n+.*?تاریخ انتشار\s*:.+?(?=\n|$)","",text,flags=re.I)
    text=re.sub(r"\n+<i>⏱.*?پیش</i>","",text,flags=re.I|re.S)
    return _normalize_text_blocks(text)

def dedupe_adjacent_emojis(text: str) -> str:
    """Collapse directly repeated visual emojis while preserving intentional variety."""
    emojis = ["💻","⚙️","🚀","🔎","🤖","🧠","⚡","🔬","🛡️","🔐","🚨","🧩","📚","💡","🧭","📝","🌐","✨","📌","🔭","📱","🔍","🛰️","🧪","🛠️","🎯","📢","📰","🔗"]
    for e in emojis:
        while f"{e} {e}" in text:
            text = text.replace(f"{e} {e}", e)
        while f"{e}{e}" in text:
            text = text.replace(f"{e}{e}", e)
    return text

def clean_channel_copy(value: str) -> str:
    text=normalize_model_text(value or "")
    for pat in [r"(?:📖\s*)?(?:بیشتر بخوانید|ادامه مطلب|برای ادامه(?: متن| مطلب)?(?: روی| از) لینک(?: زیر)? کلیک کنید)\s*", r"(?:روی لینک|از طریق لینک) (?:زیر|بالا) کلیک کنید", r"لینک ادامه مطلب\s*", r"<a\s+href=[^>]+>\s*(?:منبع اصلی|منبع)\s*</a>"]:
        text=re.sub(pat,"",text,flags=re.I|re.S)
    return re.sub(r"\n{3,}","\n\n",text).strip()

def relative_time_label(value: str) -> str:
    """Human-friendly relative age, calculated every time the article is opened."""
    if not value:
        return "زمان نامشخص"
    try:
        dt=datetime.fromisoformat(str(value).replace('Z','+00:00'))
        if dt.tzinfo is None:
            dt=dt.replace(tzinfo=timezone.utc)
        now=datetime.now(timezone.utc)
        seconds=max(0,int((now-dt.astimezone(timezone.utc)).total_seconds()))
        def fa(n:int)->str:
            return str(n).translate(str.maketrans("0123456789","۰۱۲۳۴۵۶۷۸۹"))
        if seconds < 60: return "همین الان"
        minutes=seconds//60
        if minutes < 60: return f"{fa(minutes)} دقیقه پیش"
        hours=minutes//60
        if hours < 24: return f"{fa(hours)} ساعت پیش"
        days=hours//24
        if days < 7: return f"{fa(days)} روز پیش"
        weeks=days//7
        if weeks < 5: return f"{fa(weeks)} هفته پیش"
        months=days//30
        if months < 12: return f"{fa(months)} ماه پیش"
        years=days//365
        return f"{fa(years)} سال پیش"
    except Exception:
        return "زمان نامشخص"

def rich_article_fallback(title: str, text: str, source_url: str = "") -> str:
    """Safe fallback for article formatting when AI output is too short or empty.
    Keeps the article readable and adds only the single primary source link.
    Note: This is only used for tests and manual previews, not for production pipeline.
    """
    clean = sanitize_telegram_html(_normalize_text_blocks(text or ""))
    plain = strip_html_text(clean).strip()
    if not plain:
        plain = "اطلاعات کافی برای تهیه متن کامل از منبع دریافت شد."
    if len(plain) > 3600:
        plain = plain[:3600].rsplit(" ", 1)[0] + "…"
    body = html.escape(plain, quote=False)
    # Restore simple paragraph spacing after escaping; never duplicate adjacent emoji.
    paragraphs = [x.strip() for x in re.split(r"\n\s*\n+", plain) if x.strip()]
    if paragraphs:
        chunks = [f"<b>📰 {html.escape(title[:220], quote=False)}</b>"]
        for i, paragraph in enumerate(paragraphs[:8]):
            safe = html.escape(paragraph, quote=False)
            if i == 0:
                chunks.append(f"🔎 {safe}")
            elif i in (2, 5) and len(paragraph) >= 80:
                chunks.append(f"<blockquote>💡 {safe}</blockquote>")
            else:
                chunks.append(f"📌 {safe}")
        body = "\n\n".join(chunks)
    main = normalize_url(source_url or "")
    if main:
        body = body.rstrip() + f'\n\n<a href="{html.escape(main, quote=True)}">منبع اصلی</a>'
    return dedupe_adjacent_emojis(body)

def rich_channel_fallback(title: str, text: str) -> str:
    clean=strip_html_text(text or "")
    if len(clean)>700: clean=clean[:700].rsplit(" ",1)[0]+"…"
    return f"<b>🔎 {html.escape(title[:180])}</b>\n\n{html.escape(clean)}"

def sanitize_resource_links(raw_links):
    out=[]; seen=set()
    if not isinstance(raw_links,list): return out
    for item in raw_links:
        if not isinstance(item,dict): continue
        url=normalize_url(str(item.get("url") or ""))
        label=strip_html_text(str(item.get("label") or item.get("title") or "")).strip()
        if not url.startswith(("http://","https://")) or not label or url in seen: continue
        seen.add(url); out.append({"label":label[:120],"url":url})
    return out[:5]

def append_resource_links(article_html: str, resource_links, source_url: str = "") -> str:
    """One primary source link + at most one necessary action link; idempotent."""
    clean=remove_article_metadata_blocks(article_html)
    main=normalize_url(source_url or "")
    if main:
        clean=re.sub(r'<a\s+href=["\']'+re.escape(main)+r'["\'][^>]*>.*?</a>', '', clean, flags=re.I|re.S)
    clean=re.sub(r'<a\s+href=["\'][^"\']+["\'][^>]*>\s*(?:منبع اصلی|منبع)\s*</a>', '', clean, flags=re.I|re.S)
    clean=re.sub(r'(?:<u>|<b>|<strong>|<i>|<em>)?\s*🔗?\s*(?:لینک(?:‌| )های مرتبط|منبع اصلی|منبع)\s*(?:</u>|</b>|</strong>|</i>|</em>)?', '', clean, flags=re.I)
    clean=re.sub(r'\n{3,}','\n\n',clean).strip()
    rendered=[]
    if main:
        rendered.append(f'<a href="{html.escape(main,quote=True)}">منبع اصلی</a>')
    for x in sanitize_resource_links(resource_links):
        label=x["label"]; url=normalize_url(x["url"])
        if url==main or not re.search(r"ثبت[-‌ ]?نام|عضویت|دانلود|دریافت|مستندات|docs|register|signup|خرید|قیمت|demo|دمو|مشاهده",label,re.I):
            continue
        rendered.append(f'<a href="{html.escape(url,quote=True)}">{html.escape(label)}</a>')
        break
    return clean.rstrip()+"\n\n"+" · ".join(rendered) if rendered else clean


async def resolve_article_image(db: D1Database, article: dict) -> str:
    # Image URLs are transient transport data. Never persist them in D1.
    source_url=normalize_url(article.get("source_url") or "")
    if not source_url:
        return ""
    try:
        session=await get_http_session()
        raw,_=await http_get(source_url,session)
        parsed=extract_html_page(raw,source_url)
        return normalize_url(parsed.get("image_url") or "")
    except Exception as exc:
        try:
            await log_automation(db,"WARN","article_image_resolution_failed",f"article={article.get('id')} {str(exc)[:220]}")
        except Exception:
            pass
        return ""

def make_article_png(width=1280,height=720):
    # Kept only for backward compatibility; placeholder images are not generated or stored.
    return b""


def extract_xml_locs_resilient(text: str) -> List[str]:
    # بعض سایت‌ها XML ناقص/بزرگ تحویل می‌دهند؛ در این حالت فقط locها را با regex بیرون می‌کشیم.
    found=[]
    for m in re.finditer(r"<loc[^>]*>\s*(.*?)\s*</loc>", text or "", flags=re.I|re.S):
        u=html.unescape(re.sub(r"<[^>]+>","",m.group(1)).strip())
        if u: found.append(normalize_url(u))
    return [u for u in dict.fromkeys(found) if u]


async def discover_for_processing(db: D1Database, source: Dict[str,Any], ai: AIProviderManager, allow_scout=False, include_old=False, advance_cursor=True) -> Dict[str,Any]:
    """Single direct-discovery path used by tests and automation.

    Design goals:
    - only direct RSS/feed/API/homepage/article extraction; no Web Scout;
    - hard freshness window is 24h, with 0-6h handled as priority later;
    - persistent source cursor prevents re-publishing old feed entries even if content tables are cleared;
    - when a source has never been seen before, current fresh items are eligible;
    - after a content-table wipe, the source cursor in `sources` remains the durable boundary.
    """
    direct = await discover_source_items(source, return_diagnostics=True, use_sitemap=True)
    raw_items=list(direct.get('items') or [])
    diagnostics=list(direct.get('diagnostics') or [])
    now=datetime.now(timezone.utc)

    # Homepage/HTML discovery may not expose dates in the feed item; hydrate article pages first.
    needs_hydration=[dict(x) for x in raw_items if not parse_publication_datetime(x.get('published_at') or '') and x.get('url')]
    if needs_hydration:
        hydrated=await asyncio.gather(*(enrich_candidate_content(x) for x in needs_hydration[:MAX_SOURCE_ITEMS_PER_CYCLE]), return_exceptions=True)
        repl={normalize_url(x.get('url') or ''):x for x in hydrated if isinstance(x,dict)}
        for idx,raw in enumerate(raw_items):
            key=normalize_url(raw.get('url') or '')
            if key in repl:
                merged=dict(raw)
                merged.update({k:v for k,v in repl[key].items() if v not in (None,'')})
                raw_items[idx]=merged

    fresh_items, fresh_diag, newest_dt, newest_url = ((raw_items[:MAX_SOURCE_ITEMS_PER_CYCLE], [], None, "") if include_old else select_latest_fresh_items(raw_items, now=now))
    diagnostics.extend(fresh_diag)

    source_id=source.get('id')
    last_seen=parse_publication_datetime(str(source.get('last_seen_published_at') or ''))
    last_url=normalize_url(source.get('last_seen_url') or '')
    unseen=[]
    seen_count=0
    cursor_filtered=0

    for raw in fresh_items:
        u=normalize_url(raw.get('url') or '')
        if not u:
            continue
        pub_dt=parse_publication_datetime(raw.get('published_at') or '')

        exists=await db.execute('SELECT id,status,retry_after FROM source_items WHERE source_id=? AND canonical_url=?',[source_id,u]) if source_id else []
        # Existing rejected/error items are allowed back through after cooldown while still fresh.
        # This means changing the manager's score/weights can take effect without waiting for a new article.
        existing_status=str(exists[0].get('status') or '') if exists else ''
        existing_retry=parse_publication_datetime(str(exists[0].get('retry_after') or '')) if exists else None
        reusable_rejected = bool(exists and existing_status in {'rejected','error'} and (not existing_retry or existing_retry <= now))

        # Durable boundary: this survives deletion of articles/source_items and prevents replay.
        # Rejected/error entries are the only deliberate exception so manager criteria can be changed.
        if not include_old and last_seen and not reusable_rejected:
            if not pub_dt:
                cursor_filtered += 1
                continue
            if pub_dt < last_seen or (pub_dt == last_seen and last_url and u <= last_url):
                cursor_filtered += 1
                continue

        if exists:
            row=exists[0]
            status=str(row.get('status') or '')
            retry_at=parse_publication_datetime(str(row.get('retry_after') or ''))
            if not include_old and retry_at and retry_at > now:
                seen_count += 1
                continue
            if status in {'ready','published','analyzing'} and not include_old:
                seen_count += 1
                continue
            raw=dict(raw)
            raw['_existing_source_item_id']=int(row.get('id') or 0)
            unseen.append(raw)
        else:
            unseen.append(raw)

    # Advance the durable cursor to the newest item actually discovered, even if it was not queued.
    # This prevents a later DB cleanup from resurrecting the same historical feed window.
    if newest_dt and newest_url and not include_old and advance_cursor:
        try:
            await db.execute('UPDATE sources SET last_seen_published_at=?, last_seen_url=? WHERE id=?',[newest_dt.isoformat(),newest_url,source_id])
        except Exception:
            pass

    method=direct.get('method') or 'direct'
    if not unseen and raw_items and not fresh_items:
        method += '+freshness_gate'
    elif cursor_filtered and not unseen:
        method += '+cursor'
    elif unseen:
        method += '+new'
    return {
        'items': unseen[:MAX_SOURCE_ITEMS_PER_CYCLE],
        'method': method,
        'diagnostics': diagnostics,
        'direct_count': len(raw_items),
        'fresh_count': len(fresh_items),
        'seen_count': seen_count,
        'cursor_filtered': cursor_filtered,
        'new_count': len(unseen),
    }


def format_source_publication_date(raw: str) -> str:
    raw=normalize_model_text(raw or "").strip()
    if not raw:
        return ""
    try:
        dt=datetime.fromisoformat(raw.replace("Z","+00:00"))
        return dt.strftime("%Y-%m-%d")
    except Exception:
        m=re.search(r"(20\d{2})[-/](\d{1,2})[-/](\d{1,2})", raw)
        if m:
            return f"{m.group(1)}-{int(m.group(2)):02d}-{int(m.group(3)):02d}"
        return ""

def manager_accepts_score(score: float, min_score: float) -> bool:
    """Manager-first gate with a small tolerance, never a hidden quality veto.
    0/1 remains the intentional "accept all fresh, non-duplicate" mode.
    For normal thresholds we allow a small 8-point margin so one borderline
    score does not unnecessarily starve the queue.
    """
    try:
        score=float(score or 0); minimum=float(min_score or 0)
    except Exception:
        return False
    if minimum <= 1:
        return True
    return score >= max(0.0, minimum - MANAGER_SCORE_TOLERANCE)


def _persian_ratio(text: str) -> float:
    plain=strip_html_text(text or "")
    if not plain:
        return 0.0
    fa=len(re.findall(r"[\u0600-\u06ff]", plain))
    return fa/max(1,len(re.sub(r"\s+","",plain)))

def _latin_ratio(text: str) -> float:
    plain=strip_html_text(text or "")
    if not plain:
        return 0.0
    latin=len(re.findall(r"[A-Za-z]", plain))
    return latin/max(1,len(re.sub(r"\s+","",plain)))

def _needs_persian_rewrite(title: str, channel: str, article: str) -> bool:
    sample=" ".join([title or "", channel or "", article or ""])[:5000]
    return _latin_ratio(sample) > 0.42 and _persian_ratio(sample) < 0.45

async def ai_editorial_process(ai: AIProviderManager,item:Dict[str,Any],source:Dict[str,Any],recent_titles:List[str],weights:Dict[str,float],manager_prompts:Optional[Dict[str,str]]=None,progress=None):
    body=(item.get("body") or item.get("description") or "")[:14000]
    manager_prompts=manager_prompts or {}
    channel_scope=manager_prompts.get("channel") or "تمرکز روی خبرهای فنی و ارزشمند؛ محتوای سطحی و کلیشه‌ای را کنار بگذار."
    article_scope=manager_prompts.get("article") or "نسخه کامل را فنی، غنی و مبتنی بر واقعیت‌های منبع بنویس."
    editorial_schema={
        "accept": True, "score": 0, "global_relevance": 0, "technology_relevance": 0,
        "ai_relevance": 0, "cyber_relevance": 0, "education_relevance": 0, "iran_relevance": 0,
        "freshness": 0, "reliability": 0, "duplicate_risk": 0, "category": "ai|tech|cyber|edu|general",
        "why": "...", "title": "...", "channel_html": "...", "article_html": "...",
        "facts": ["..."], "resource_links": [{"label":"...","url":"https://..."}]
    }
    prompt=f"""تو موتور تحریریه و تولید محتوای یک کانال فارسی حرفه‌ای هستی؛ نه قاضی، نه مفسر سیاسی و نه منتقد.
وظیفه تو این است که از منبع داده‌شده محتوای فنی، غنی، دقیق، بی‌طرف و قابل‌فهم بسازی. انتخاب نهایی فقط بر اساس معیارهای عددی مدیر انجام می‌شود؛ در متن نهایی قضاوت، توصیه یا ارزش‌گذاری ننویس.

موضوعات کانال: فناوری، هوش مصنوعی، ابزارها و مدل‌ها، امنیت سایبری، آموزش و اخبار مهم جهان.
مخاطب: فارسی‌زبان‌ها. زبان یا جغرافیای منبع هیچ اولویتی ندارد؛ فقط کیفیت، ارتباط و تازگی محتوا مهم است.

منبع: {source.get('name')}
عنوان: {item.get('title')}
URL: {item.get('url')}
تاریخ انتشار منبع: {item.get('published_at') or "نامشخص"}
لینک‌های داخل صفحه:
{json.dumps(item.get('links') or [], ensure_ascii=False)[:5000]}
متن منبع:
{body}

وزن‌های تعیین‌شده توسط مدیر:
{json.dumps(weights,ensure_ascii=False)}

دستور محتوایی مدیر برای نسخه کوتاه کانال (حدود 500 کاراکتر):
{channel_scope}

دستور محتوایی مدیر برای نسخه کامل داخل ربات (حدود 2000 کاراکتر):
{article_scope}

این دو دستور فقط مشخص می‌کنند چه اطلاعات و چه نوع محتوایی پوشش داده شود؛ به هیچ وجه قوانین Formatting را تغییر نده. قالب‌بندی وظیفه موتور تولید و ربات است.

اول برای امتیازدهی داخلی، امتیاز 0 تا 100 بده. فیلد accept فقط توضیح داخلی است و دروازه مستقل انتشار نیست؛ تصمیم نهایی را معیارهای عددی مدیر می‌گیرند. صرفاً به‌دلیل کوتاه بودن متن accept=false نده.
تازگی توسط برنامه به‌صورت فنی و مستقل کنترل می‌شود؛ از ساختن تاریخ یا حدس‌زدن آن خودداری کن. مطالب خارج از پنجره ۶ ساعت برنامه اصلاً به این مرحله نمی‌رسند. مقدار accept فقط برای توصیف داخلی پاسخ است و تصمیم انتشار نهایی را برنامه بر اساس امتیاز و تنظیمات مدیر می‌گیرد.
کوتاهی متن منبع، کم بودن پاراگراف‌ها یا یک‌جمله‌ای بودن خلاصه به‌تنهایی دلیل رد محتوا نیست. اگر منبع کوتاه است، بهترین محتوای کوتاه و دقیق ممکن را فقط بر اساس همان اطلاعات تولید کن؛ طول محتوا معیار پذیرش نیست و هرگز جزئیات، عدد یا ادعای ساختگی اضافه نکن.

اگر accept=true، همزمان محتوای نهایی را تولید کن:
1) channel_html: حدود 450 تا 650 کاراکتر «خودِ خبر»؛ نه teaser و نه صرفاً معرفی لینک. ساختار بصری داشته باشد: تیتر/شروع با <b>، حداکثر 1 بخش کوتاه با <i> یا <blockquote> فقط وقتی طبیعی است، پاراگراف‌های کوتاه و 1 تا 3 ایموجی دقیق و مرتبط.
2) article_html: طول ثابت ندارد؛ بسته به غنای منبع کوتاه یا بلند باشد (تقریباً 400 تا 3000 کاراکتر کافی است). اگر منبع کوتاه است، کوتاه و دقیق بمان؛ برای رسیدن به طول مشخص جزئیات نساز. مستقل و غنی‌تر از متن کانال باشد. از تیترهای کوتاه با <b>، پاراگراف‌های کوتاه و در صورت مناسب یک <blockquote> استفاده کن. متن باید برای خواندن در موبایل خوش‌خوان باشد و صرفاً کپی/تکرار channel_html نباشد.
3) title: کوتاه، جذاب و غیرکلیک‌بیتی.
4) category و facts.

قواعد نگارش:
- فارسی روان، دوستانه، عامیانه و خوش‌خوان؛ رسمی و خشک نباش.
- اگر اصطلاح فنی لازم است، معادل فارسی را اول بیاور و اصطلاح انگلیسی را فقط داخل پرانتز یا <code>...</code> قرار بده. پاراگراف کامل انگلیسی ممنوع است؛ فقط نام مدل‌ها، شرکت‌ها، محصولات و اصطلاح‌های فنی شناخته‌شده می‌توانند انگلیسی بمانند.
- در هر پاراگراف اصلی حداکثر یک ایموجی مرتبط داشته باش؛ دو یا چند ایموجی کنار هم نگذار و ایموجی تکراری پشت‌سرهم هم استفاده نکن.
- نسخه کانال باید فاصله‌گذاری طبیعی موبایلی داشته باشد، چند پاراگراف کوتاه داشته باشد و در صورت مناسب یک بخش Quote کوتاه داشته باشد.
- نسخه کانال و نسخه کامل باید حتماً حداقل یک Quote کوتاه و واقعی داشته باشند؛ اگر منبع جمله مستقیمی برای نقل‌قول ندارد، یک جمله عیناً از متن منبع را به‌صورت Quote بیاور، نه اینکه نقل‌قول ساختگی بسازی. نسخه کامل در صورت داشتن متن کافی می‌تواند 2 Quote کوتاه داشته باشد. Quote هرگز نباید کل مقاله یا یک پاراگراف بسیار بزرگ باشد.
- متن را با تیترهای کوتاه Bold، Italic فقط برای کلمه/عبارت کوتاه، Underline در موارد محدود، Code و Quote در جاهای طبیعی خوش‌خوان کن؛ روی یک جمله طولانی Italic نزن و از فرمت‌ها افراطی استفاده نکن.
- اگر کد، دستور، نام API یا عبارت فنی دقیق وجود دارد از <code>...</code> استفاده کن؛ اگر متن شامل قطعه‌کد واقعی است از <pre>...</pre> استفاده کن.
- هیچ‌وقت کاراکترهای متنی "\\n" را برای فاصله‌گذاری خروجی نده؛ برای خط جدید از newline واقعی استفاده کن.
- سؤال‌هایی مثل «هدف چیست؟» یا «چه معنایی دارد؟» را به عنوان سؤال رها نکن؛ پاسخ و اطلاعات موجود در منبع را مستقیم بیان کن.
- هیچ نتیجه‌گیری شخصی یا قضاوتی به کاربر تحمیل نکن.
- «طبق منبع»، «گزارش شده» و «این شرکت گفته» را فقط وقتی لازم است برای نسبت‌دادن ادعا استفاده کن.
- چیزی را که در منبع نیست به عنوان واقعیت نساز.
- channel_html و article_html را با HTML سازگار با Telegram بده؛ Markdown استفاده نکن.
- اگر متن یک سایت، ثبت‌نام، دوره، ابزار، مستندات یا صفحه مشخصی را معرفی کرده و URL آن در «لینک‌های داخل صفحه» وجود دارد، آن را در resource_links برگردان. URL را حدس نزن.
- لینک Deep Link مقاله توسط برنامه اضافه می‌شود؛ در متن کانال هیچ عبارت «ادامه مطلب را از لینک زیر بخوانید» یا مشابه آن ننویس.

فقط JSON معتبر:
{json.dumps(editorial_schema, ensure_ascii=False)}"""
    result=await ai.call([{"role":"system","content":"You are a Persian technology content producer. Be neutral and factual. Return JSON only."},{"role":"user","content":prompt}],0.35,5000,"editorial")
    obj=parse_json_object(result.get("content",""))
    if not obj:
        repair_prompt=("پاسخ زیر را فقط به JSON معتبر تبدیل کن؛ محتوای آن را تغییر نده. فیلدها: accept,score,category,iran_relevance,freshness,reliability,duplicate_risk,why,title,channel_html,article_html,facts.\n\n"+str(result.get("content",""))[:14000])
        retry=await ai.call([{"role":"system","content":"Return valid JSON only."},{"role":"user","content":repair_prompt}],0,4200,"editorial_json_repair")
        obj=parse_json_object(retry.get("content","")); result=retry
    if not obj: return {"error":"پاسخ AI JSON معتبر نبود","ai":result}
    # یک مرحله اصلاح زبانی فقط وقتی لازم است؛ هدف کاهش مصرف توکن و جلوگیری از خروجی انگلیسی است.
    raw_title=strip_html_text(obj.get("title") or item.get("title") or "")[:240]
    raw_ch=str(obj.get("channel_html") or obj.get("channel_text") or "")
    raw_ar=str(obj.get("article_html") or obj.get("article_text") or "")
    if _needs_persian_rewrite(raw_title, raw_ch, raw_ar):
        repair=(
            "متن زیر خروجی تحریریه است اما بخش زیادی انگلیسی شده. فقط بازنویسی فارسی انجام بده و هیچ واقعیتی را تغییر نده. "
            "نام شرکت‌ها، مدل‌ها و اصطلاحات فنی شناخته‌شده را همان‌طور نگه دار. خروجی فقط JSON معتبر با سه کلید title, channel_html, article_html باشد. "
            "قالب Telegram HTML مجاز است و یک Quote کوتاه هم نگه دار/ایجاد کن.\n\n"
            + json.dumps({"title":raw_title,"channel_html":raw_ch,"article_html":raw_ar},ensure_ascii=False)[:20000]
        )
        repaired=await ai.call([{"role":"system","content":"Rewrite to fluent Persian. Return JSON only."},{"role":"user","content":repair}],0.15,4200,"editorial_persian_repair")
        pobj=parse_json_object(repaired.get("content",""))
        if pobj:
            raw_title=strip_html_text(pobj.get("title") or raw_title)[:240]
            raw_ch=str(pobj.get("channel_html") or raw_ch)
            raw_ar=str(pobj.get("article_html") or raw_ar)
            obj["title"]=raw_title; obj["channel_html"]=raw_ch; obj["article_html"]=raw_ar
            result=repaired
    title=raw_title
    category=str(obj.get("category") or source.get("category") or "tech")
    # واحدِ قالب‌بندی قطعی: هر خروجی، حتی اگر AI متن خام داده باشد، یک‌بار از همین renderer عبور می‌کند.
    ch=ensure_rich_channel_format(title, raw_ch, category)
    ar=ensure_rich_article_format(title, raw_ar, item.get("url") or "")
    # If ensure_rich_article_format returns empty (due to no content), we treat as error.
    if not ar:
        return {"error": "تولید محتوای کامل ناموفق بود - خروجی خالی", "ai": result}
    resource_links=sanitize_resource_links(obj.get("resource_links"))
    ar=append_resource_links(ar, resource_links, item.get("url") or "")
    obj["title"]=title; obj["channel_html"]=ch; obj["article_html"]=ar; obj["resource_links"]=resource_links
    # امتیاز نهایی را خود ربات از وزن‌های مدیر محاسبه می‌کند؛ بنابراین تغییر وزن واقعاً اثر دارد.
    dims={
        "global":float(obj.get("global_relevance",5) or 0),
        "technology":float(obj.get("technology_relevance",5) or 0),
        "ai":float(obj.get("ai_relevance",5) or 0),
        "cyber":float(obj.get("cyber_relevance",5) or 0),
        "education":float(obj.get("education_relevance",5) or 0),
        "iran":float(obj.get("iran_relevance",0) or 0),
        "freshness":float(obj.get("freshness",5) or 0),
        "source":max(0,min(10,float(source.get("trust_score") or 80)/10)),
        "novelty":10-max(0,min(10,float(obj.get("duplicate_risk",0) or 0)))
    }
    total_weight=sum(max(0,float(weights.get(k,0))) for k in dims)
    weighted=sum(max(0,min(10,v))*max(0,float(weights.get(k,0))) for k,v in dims.items())
    obj["score"]=round((weighted/(total_weight*10))*100,1) if total_weight else round(float(obj.get("score",0) or 0),1)
    return {**obj,"ai":result}

async def get_manager_editorial_prompts(db: D1Database) -> Dict[str,str]:
    return {
        "channel": await get_setting(db, "editorial_prompt_channel", "فقط محتوای فنی و واقعاً ارزشمند برای مخاطب فناوری و هوش مصنوعی را پوشش بده."),
        "article": await get_setting(db, "editorial_prompt_article", "نسخه کامل باید فنی، غنی و مبتنی بر واقعیت‌های منبع باشد.")
    }

async def add_source(db: D1Database, url: str, category: str = "tech", interval_minutes: Optional[int] = None, priority: int = 5) -> int:
    clean = normalize_url(url)
    if not clean:
        raise ValueError("invalid URL")
    parsed = urllib.parse.urlsplit(clean)
    name = parsed.netloc or clean
    interval = interval_minutes or int(await get_setting(db, "default_source_interval", str(DEFAULT_SOURCE_INTERVAL_MINUTES)))
    now = datetime.now(timezone.utc)
    next_check = now.isoformat()
    res = await db.execute("INSERT INTO sources(name, url, category, enabled, interval_minutes, priority, next_check_at, created_at) VALUES(?, ?, ?, 1, ?, ?, ?, ?) RETURNING id", [name, clean, category, interval, priority, next_check, now.isoformat()])
    source_id = res[0].get("id") if res else 0
    if not source_id:
        source_id = (await db.execute("SELECT id FROM sources WHERE url = ?", [clean]))[0].get("id")
    return int(source_id)


# ============================================================
# MODIFIED fetch_source_cycle with paywall detection and placeholder rejection
# ============================================================
async def fetch_source_cycle(db: D1Database, source: Dict[str,Any], ai: AIProviderManager, progress=None, allow_old_test=False):
    source_id=source['id']; now=datetime.now(timezone.utc)
    stats={'source':source.get('name') or source.get('url'), 'found':0,'seen':0,'candidates':0,'processed':0,'accepted':0,'rejected':0,'errors':0,'queued':0,'method':'','diagnostics':[]}
    try:
        if progress: await progress('discover',f"🔎 {source.get('name')}: در حال بررسی مستقیم سایت و منابع آن…")
        discovery=await discover_for_processing(db,source,ai,allow_scout=False,include_old=allow_old_test)
        items=discovery.get('items') or []
        stats.update({'found':discovery.get('direct_count',0),'seen':discovery.get('seen_count',0),'candidates':len(items),'method':discovery.get('method') or ''})
        stats['diagnostics']=discovery.get('diagnostics')[-10:]
        if progress:
            await progress('discovered',f"🌐 {source.get('name')}: پیدا {stats['found']} · تازه/جدید {stats['candidates']} · مسیر {stats['method'] or 'مستقیم'}")
        if not items:
            next_check=(now+timedelta(minutes=int(source.get('interval_minutes') or DEFAULT_SOURCE_INTERVAL_MINUTES))).isoformat()
            await db.execute('UPDATE sources SET last_checked_at=?,next_check_at=?,last_error=? WHERE id=?',[now.isoformat(),next_check,'; '.join(stats['diagnostics'][-4:])[:1200],source_id])
            return stats
        recent_rows=await db.execute("SELECT title FROM articles WHERE status IN ('published','ready') ORDER BY id DESC LIMIT 50")
        recent_titles=[r.get('title','') for r in recent_rows]
        weight_keys=['global','technology','ai','cyber','education','iran','freshness','source','novelty']
        weights={k:float(await get_setting(db,f'weight_{k}','10')) for k in weight_keys}
        sem=asyncio.Semaphore(max(1,min(4,int(await get_setting(db,'max_ai_workers','3')))))
        async def process_one(raw):
            try:
                raw_title=strip_html_text(raw.get('title',''))[:500]; raw_desc=strip_html_text(raw.get('description',''))[:2000]; raw_url=normalize_url(raw.get('url'))
                if not allow_old_test:
                    fresh_ok, fresh_reason, _fresh_dt = candidate_is_fresh(raw, now=now)
                    if NEWS_FRESHNESS_STRICT and not fresh_ok:
                        return {'processed':0,'rejected':1,'reason':f'freshness: {fresh_reason}'}
                if not raw_url or not raw_title:
                    return {'processed':0,'rejected':1,'reason':'missing'}
                item=await enrich_candidate_content(dict(raw))
                title=strip_html_text(item.get('title') or raw_title)[:500]; url=normalize_url(item.get('url') or raw_url)
                if not url or not title: return {'processed':0,'rejected':1,'reason':'missing'}
                # --- NEW: Check for insufficient content (paywall/snippet) before AI ---
                insufficient, reason = is_insufficient_content(title, item.get('body') or '', item.get('description') or '')
                if insufficient:
                    if progress: await progress('skip', f"⏭️ {title[:60]} → {reason}")
                    return {'processed':0,'rejected':1,'reason':reason}
                async with sem:
                    exists=await db.execute('SELECT id,status,retry_after FROM source_items WHERE source_id=? AND canonical_url=?',[source_id,url])
                    item_id=int(exists[0].get('id') or 0) if exists else 0
                    existing_status=str(exists[0].get('status') or '') if exists else ''
                    retry_at=parse_publication_datetime(str(exists[0].get('retry_after') or '')) if exists else None
                    if exists and not allow_old_test:
                        if retry_at and retry_at > now:
                            return {'processed':0,'rejected':0,'seen':1,'reason':'retry cooldown'}
                        if existing_status in {'ready','published','analyzing'}:
                            return {'processed':0,'rejected':0,'seen':1,'reason':'seen'}
                    body=item.get('body') or item.get('description') or ''
                    body_plain=strip_html_text(body)
                    # Additional check: if body is too short but we already rejected insufficient, so we can still accept if it passed.
                    # But we also need to ensure there is at least some content.
                    if len(body_plain) < 20:
                        return {'processed':0,'rejected':1,'reason':'source_content_too_thin'}
                    content_hash=text_hash(title+' '+body_plain)
                    recent_pub=await db.execute("SELECT id FROM articles WHERE status IN ('published','ready','test') AND source_url=? AND COALESCE(published_at,created_at) >= ? LIMIT 1",[url,(now-timedelta(hours=24)).isoformat()])
                    if recent_pub and not allow_old_test:
                        return {'processed':0,'rejected':0,'seen':1,'reason':'published_url_recently'}
                    recent_hash=await db.execute("SELECT id FROM articles WHERE status IN ('published','ready','test') AND COALESCE(published_at,created_at) >= ? LIMIT 200",[(now-timedelta(hours=24)).isoformat()])
                    if recent_hash and not allow_old_test:
                        recent_bodies=await db.execute("SELECT title,body FROM articles WHERE status IN ('published','ready','test') AND COALESCE(published_at,created_at) >= ? ORDER BY id DESC LIMIT 50",[(now-timedelta(hours=24)).isoformat()])
                        if any(text_hash(str(r.get('title') or '')+' '+str(r.get('body') or ''))==content_hash for r in recent_bodies):
                            return {'processed':0,'rejected':0,'seen':1,'reason':'published_hash_recently'}
                    hash_exists=await db.execute('SELECT id,status,retry_after FROM source_items WHERE content_hash=? LIMIT 1',[content_hash])
                    if hash_exists and not allow_old_test and not item_id:
                        hrow=hash_exists[0]; hstatus=str(hrow.get('status') or '')
                        hretry=parse_publication_datetime(str(hrow.get('retry_after') or ''))
                        if hretry and hretry > now: return {'processed':0,'rejected':0,'seen':1,'reason':'hash cooldown'}
                        if hstatus in {'ready','published','analyzing'}: return {'processed':0,'rejected':0,'seen':1,'reason':'hash'}
                        item_id=int(hrow.get('id') or 0)
                    if item_id:
                        await db.execute("UPDATE source_items SET title=?,description=?,content=?,published_at=?,discovered_at=?,content_hash=?,status='analyzing',last_error=NULL,retry_after=NULL WHERE id=?",
                                          [title,item.get('description','')[:2000],body[:14000],item.get('published_at','')[:100],now.isoformat(),content_hash,item_id])
                    else:
                        ins=await db.execute("INSERT INTO source_items(source_id,canonical_url,title,description,content,image_url,published_at,discovered_at,content_hash,status,category) VALUES(?,?,?,?,?,?,?,?,?,'analyzing',?) RETURNING id",
                            [source_id,url,title,item.get('description','')[:2000],body[:14000],'',item.get('published_at','')[:100],now.isoformat(),content_hash,source.get('category','tech')])
                        item_id=ins[0].get('id') if ins else 0
                    async def ai_report(detail):
                        if progress: await progress('ai', detail)
                    out=await ai_editorial_process(ai,item,source,recent_titles,weights,await get_manager_editorial_prompts(db),progress=ai_report)
                    if out.get('error'):
                        if item_id: await db.execute("UPDATE source_items SET status='error',last_error=?,retry_after=? WHERE id=?",[out['error'][:1200],(now+timedelta(minutes=15)).isoformat(),item_id])
                        return {'processed':1,'errors':1,'reason':out['error'][:220]}
                    score=float(out.get('score',0) or 0); min_score=float(await get_setting(db,'min_content_score',str(DEFAULT_MIN_CONTENT_SCORE)))
                    # Manager controls the gate. Special low-threshold mode is intentional: when the
                    # manager sets the minimum to 0/1, every fresh, non-duplicate item is eligible.
                    # The AI is still used for extraction/formatting; it is not a hidden veto.
                    accept = manager_accepts_score(score, min_score)
                    if not accept:
                        if item_id: await db.execute("UPDATE source_items SET status='rejected',score=?,category=?,last_error=?,retry_after=? WHERE id=?",[score,out.get('category',source.get('category','tech')),str(out.get('why') or 'score below threshold')[:1000],(now+timedelta(minutes=15)).isoformat(),item_id])
                        return {'processed':1,'rejected':1,'score':score,'reason':str(out.get('why') or 'score below threshold')[:220]}
                    verify_mode=await get_setting(db,'ai_verify_mode','auto')
                    need_verify=(verify_mode=='always')
                    if need_verify:
                        verify=await ai_verify_content(ai,item,out)
                        if not verify.get('ok') or float(verify.get('confidence',0) or 0)<80:
                            if item_id: await db.execute("UPDATE source_items SET status='rejected',score=?,last_error=?,retry_after=? WHERE id=?",[score,json.dumps(verify,ensure_ascii=False)[:1200],(now+timedelta(minutes=15)).isoformat(),item_id])
                            return {'processed':1,'rejected':1,'score':score,'reason':'verification'}
                    # Canonical content pipeline: these are rendered exactly once by ai_editorial_process.
                    # Do not reformat/fallback later; re-rendering was the source of inconsistent channel/article output.
                    title_out=strip_html_text(out.get('title') or title)[:500]
                    # از خروجی نهایی AI همان یک renderer اصلی را اجرا می‌کنیم؛ دیگر مسیر خام/متفاوت نداریم.
                    channel_text=ensure_rich_channel_format(title_out, out.get('channel_html') or out.get('channel_text') or body_plain, str(out.get('category') or source.get('category') or 'tech'))
                    article_text=ensure_rich_article_format(title_out, out.get('article_html') or out.get('article_text') or body_plain, url)
                    # IMPORTANT: Ensure article_text is not the placeholder fallback. If it contains the placeholder string, reject.
                    if not article_text or "اطلاعات کافی برای تهیه متن کامل" in article_text:
                        if item_id: await db.execute("UPDATE source_items SET status='error',last_error=?,retry_after=? WHERE id=?",['generation produced fallback placeholder',(now+timedelta(minutes=15)).isoformat(),item_id])
                        return {'processed':1,'errors':1,'reason':'generation fallback placeholder'}
                    channel_text=clean_channel_copy(channel_text)
                    article_text=remove_article_metadata_blocks(article_text)
                    if not strip_html_text(channel_text) or not strip_html_text(article_text):
                        if item_id: await db.execute("UPDATE source_items SET status='error',last_error=?,retry_after=? WHERE id=?",['generation produced no usable rich content',(now+timedelta(minutes=15)).isoformat(),item_id])
                        return {'processed':1,'errors':1,'reason':'generation empty'}
                    if plain_len(article_text)<80:
                        if item_id: await db.execute("UPDATE source_items SET status='error',last_error=?,retry_after=? WHERE id=?",['generation produced no usable text',(now+timedelta(minutes=15)).isoformat(),item_id])
                        return {'processed':1,'errors':1,'reason':'generation empty'}
                    art=await db.execute("INSERT INTO articles(source_item_id,title,channel_text,body,source_url,image_url,category,score,status,created_at,source_published_at) VALUES(?,?,?,?,?,?,?,?,'ready',?,?) RETURNING id",
                        [item_id,title_out,channel_text,article_text[:18000],url,'',out.get('category') or source.get('category','tech'),score,now.isoformat(),item.get('published_at','')[:100]])
                    aid=art[0].get('id') if art else 0
                    token=make_deep_token(int(aid)); await db.execute('UPDATE articles SET deep_token=? WHERE id=?',[token,aid])
                    if item_id: await db.execute("UPDATE source_items SET status='ready',article_id=?,score=?,retry_after=NULL WHERE id=?",[aid,score,item_id])
                    await db.execute("INSERT OR IGNORE INTO publication_queue(article_id,scheduled_at,status,attempts,created_at) VALUES(?,?, 'queued',0,?)",[aid,now.isoformat(),now.isoformat()])
                    return {'processed':1,'accepted':1,'queued':1,'score':score,'reason':'queued'}
            except Exception as e:
                return {'processed':1,'errors':1,'reason':f"{type(e).__name__}: {str(e)[:220]}"}
        results=await asyncio.gather(*(process_one(x) for x in items[:MAX_SOURCE_ITEMS_PER_CYCLE]),return_exceptions=True)
        for r in results:
            if isinstance(r,Exception): stats['errors']+=1
            else:
                for k in ('processed','accepted','rejected','errors','queued','seen'):
                    stats[k]+=int(r.get(k,0) or 0)
        finished=datetime.now(timezone.utc)
        next_check=(finished+timedelta(minutes=int(source.get('interval_minutes') or DEFAULT_SOURCE_INTERVAL_MINUTES))).isoformat()
        await db.execute('UPDATE sources SET last_checked_at=?,next_check_at=?,last_error=NULL WHERE id=?',[finished.isoformat(),next_check,source_id])
        await log_automation(db,'INFO','source_cycle',json.dumps(stats,ensure_ascii=False)[:1800])
        return stats
    except Exception as e:
        stats['errors']+=1; stats['diagnostics'].append(str(e)[:500])
        failed_at=datetime.now(timezone.utc)
        await db.execute('UPDATE sources SET last_checked_at=?,next_check_at=?,last_error=? WHERE id=?',[failed_at.isoformat(),(failed_at+timedelta(minutes=int(source.get('interval_minutes') or DEFAULT_SOURCE_INTERVAL_MINUTES))).isoformat(),str(e)[:1200],source_id])
        await log_automation(db,'ERROR','source_cycle_failed',json.dumps(stats,ensure_ascii=False)[:1600])
        return stats


async def can_publish_now(db: D1Database) -> bool:
    if not await get_channel_id(db):
        return False
    enabled = await get_setting(db, "automation_enabled", "0")
    if enabled != "1":
        return False
    tehran = datetime.now(pytz.timezone("Asia/Tehran"))
    start_h = int(await get_setting(db, "publish_start_hour", str(DEFAULT_PUBLISH_START_HOUR)))
    end_h = int(await get_setting(db, "publish_end_hour", str(DEFAULT_PUBLISH_END_HOUR)))
    hour=tehran.hour
    in_window=(start_h <= hour <= end_h) if start_h <= end_h else (hour >= start_h or hour <= end_h)
    if not in_window:
        return False
    count_rows = await db.execute("SELECT COUNT(*) as c FROM articles WHERE status='published' AND COALESCE(published_at,created_at) >= ?", [tehran.replace(hour=0, minute=0, second=0, microsecond=0).astimezone(timezone.utc).isoformat()])
    max_daily = int(await get_setting(db, "max_daily_posts", str(DEFAULT_MAX_DAILY_POSTS)))
    if (count_rows[0].get("c", 0) if count_rows else 0) >= max_daily:
        return False
    last_manual = await get_setting(db, "last_manual_channel_post_at", "")
    last_pub = await db.execute("SELECT published_at FROM publication_queue WHERE status='published' ORDER BY id DESC LIMIT 1")
    latest_times = [x for x in [last_manual, last_pub[0].get("published_at") if last_pub else ""] if x]
    if latest_times:
        latest = max(latest_times)
        try:
            delta = datetime.now(timezone.utc) - datetime.fromisoformat(latest.replace("Z", "+00:00"))
            min_gap = float(await get_setting(db, "min_post_gap_minutes", str(DEFAULT_MIN_POST_GAP_MINUTES)))
            if delta.total_seconds() < min_gap * 60:
                return False
        except Exception:
            pass
    return True


async def get_runtime_bot_username(bot: Bot) -> str:
    global BOT_USERNAME_RUNTIME
    if BOT_USERNAME_RUNTIME:
        return BOT_USERNAME_RUNTIME
    try:
        me=await bot.get_me()
        BOT_USERNAME_RUNTIME=me.username or BOT_USERNAME.lstrip("@")
    except Exception:
        BOT_USERNAME_RUNTIME=BOT_USERNAME.lstrip("@")
    return BOT_USERNAME_RUNTIME

def _trim_rich_blocks_to_limit(value: str, max_plain_chars: int = 760) -> str:
    clean=sanitize_telegram_html(clean_channel_copy(value or ''))
    if plain_len(clean) <= max_plain_chars:
        return clean
    blocks=[b.strip() for b in re.split(r"\n\s*\n+", clean) if strip_html_text(b).strip()]
    while len(blocks) > 1 and plain_len("\n\n".join(blocks)) > max_plain_chars:
        blocks.pop()
    trimmed="\n\n".join(blocks)
    if plain_len(trimmed) > max_plain_chars:
        plain=strip_html_text(trimmed)[:max_plain_chars].rsplit(' ',1)[0]+"…"
        return html.escape(plain,quote=False)
    return trimmed

def publication_caption(title: str, channel_html: str, deep_link: str) -> str:
    """Build a single rich caption under Telegram's 1024-char caption limit."""
    link=f'<a href="{html.escape(deep_link,quote=True)}">📖 بیشتر بخوانید</a>'
    clean=_trim_rich_blocks_to_limit(channel_html, 760)
    caption=(clean.strip()+"\n\n"+link).strip()
    if len(caption) <= 1024:
        return caption
    # Drop whole rich blocks before ever stripping formatting.
    blocks=[b.strip() for b in re.split(r"\n\s*\n+", sanitize_telegram_html(clean)) if strip_html_text(b).strip()]
    while len(blocks)>1 and len("\n\n".join(blocks)+"\n\n"+link)>1024:
        blocks.pop()
    candidate=("\n\n".join(blocks)+"\n\n"+link).strip()
    if len(candidate) <= 1024:
        return candidate
    # Last-resort: keep Telegram-safe HTML by truncating the current final block as plain text,
    # then escaping only that truncated block. This path is rare because channel content is short.
    plain=strip_html_text("\n\n".join(blocks))
    budget=max(120, 1024-len(strip_html_text(link))-8)
    plain=plain[:budget].rsplit(' ',1)[0]+"…"
    return html.escape(plain,quote=False)+"\n\n"+link


async def publish_next_article(db: D1Database, bot: Bot, force: bool=False) -> bool:
    if force:
        channel_id=await get_channel_id(db)
        if not channel_id: return False
        max_daily=int(await get_setting(db,"max_daily_posts",str(DEFAULT_MAX_DAILY_POSTS)))
        tehran=datetime.now(pytz.timezone("Asia/Tehran"))
        count_rows=await db.execute("SELECT COUNT(*) c FROM articles WHERE status='published' AND COALESCE(published_at,created_at) >= ?",[tehran.replace(hour=0,minute=0,second=0,microsecond=0).astimezone(timezone.utc).isoformat()])
        if (count_rows[0].get("c",0) if count_rows else 0)>=max_daily: return False
    elif not await can_publish_now(db):
        return False
    now_iso=datetime.now(timezone.utc).isoformat()
    schedule_filter="" if force else " AND (q.scheduled_at IS NULL OR q.scheduled_at <= ?)"
    params=[now_iso] if not force else []
    rows=await db.execute("SELECT q.id as queue_id,q.article_id,a.* FROM publication_queue q JOIN articles a ON a.id=q.article_id WHERE q.status='queued' AND a.status='ready'"+schedule_filter+" ORDER BY COALESCE(a.source_published_at,a.created_at) DESC, a.score DESC, q.created_at ASC LIMIT 1",params)
    if not rows:
        return False
    row=rows[0]; queue_id=row["queue_id"]; article_id=row["article_id"]
    await db.execute("UPDATE publication_queue SET status='publishing',attempts=attempts+1 WHERE id=?",[queue_id])
    try:
        token=row.get("deep_token")
        bot_username=await get_runtime_bot_username(bot)
        if not token or not bot_username: raise RuntimeError("deep link token یا نام کاربری ربات تنظیم نشده است")
        deep_link=f"https://t.me/{bot_username}?start=article_{token}"
        channel_id=await get_channel_id(db)
        title_out=str(row.get("title") or "مطلب")
        channel_text=sanitize_telegram_html(row.get("channel_text") or "")
        source_url=normalize_url(row.get("source_url") or "")
        # publication_caption adds exactly one navigation link. Keep channel_text itself clean.
        image_url=await resolve_article_image(db,row)
        sent=None
        if image_url:
            try:
                sent=await bot.send_photo(chat_id=channel_id,photo=image_url,caption=publication_caption(title_out,channel_text,deep_link),parse_mode="HTML")
            except Exception as img_error:
                await log_automation(db,"WARN","source_image_failed",f"article={article_id} {img_error}")
        if sent is None:
            # Never publish an unrelated placeholder image. If the source has no usable image,
            # publish the real formatted text instead.
            sent=await bot.send_message(chat_id=channel_id,text=channel_text[:4096],parse_mode="HTML",disable_web_page_preview=True)
        published_at=datetime.now(timezone.utc).isoformat()
        await db.execute("UPDATE articles SET status='published',published_message_id=?,published_at=? WHERE id=?",[getattr(sent,"message_id",0),published_at,article_id])
        await db.execute("UPDATE publication_queue SET status='published',published_at=? WHERE id=?",[published_at,queue_id])
        await log_automation(db,"INFO","published",f"article={article_id} message={getattr(sent,'message_id',0)} force={force}")
        return True
    except Exception as e:
        attempts=int(row.get("attempts") or 1)
        error_text=str(e)[:1500]
        if attempts < 3:
            retry_at=(datetime.now(timezone.utc)+timedelta(minutes=min(15,5*attempts))).isoformat()
            await db.execute("UPDATE publication_queue SET status='queued',scheduled_at=?,last_error=? WHERE id=?",[retry_at,error_text,queue_id])
        else:
            await db.execute("UPDATE publication_queue SET status='failed',last_error=? WHERE id=?",[error_text,queue_id])
        await db.execute("UPDATE articles SET status='ready' WHERE id=?",[article_id])
        await log_automation(db,"ERROR","publication_failed",f"article={article_id} attempt={attempts} retry={'yes' if attempts < 3 else 'no'} {e}")
        try: await bot.send_message(ADMIN_ID,f"❌ خطا در انتشار خودکار\nArticle: {article_id}\nError: {html.escape(str(e)[:800])}")
        except Exception: pass
        return False

async def recheck_failed_providers(db:D1Database,bot:Bot,manager:AIProviderManager):
    now=datetime.now(timezone.utc).isoformat()
    rows=await db.execute("SELECT id,name,model_name,status,cooldown_until FROM ai_providers WHERE enabled=1 AND status IN ('invalid','cooldown') AND (cooldown_until IS NULL OR cooldown_until <= ?) ORDER BY priority ASC LIMIT 8",[now])
    for p in rows:
        try:
            result=await manager.test_provider(int(p["id"]))
            if result.get("ok"):
                try:
                    await bot.send_message(ADMIN_ID,f"✅ <b>مدل دوباره در دسترس است</b>\n\nProvider: {html.escape(str(p.get('name')))}\nModel: <code>{html.escape(str(p.get('model_name')))}</code>\nLatency: {result.get('latency_ms',0)}ms",parse_mode="HTML")
                except Exception: pass
        except Exception as e:
            await log_automation(db,"ERROR","provider_recheck_failed",f"provider={p.get('id')} {e}")

async def automation_loop(db: D1Database, bot: Bot):
    ai=AIProviderManager(db,bot)
    await set_setting(db,'worker_started_at',datetime.now(timezone.utc).isoformat())
    last_cleanup=0.0; last_provider_recheck=0.0
    try:
        while True:
            loop_started=datetime.now(timezone.utc)
            try:
                await set_setting(db,'worker_heartbeat_at',loop_started.isoformat())
                enabled=await get_setting(db,'automation_enabled','0')
                if enabled=='1':
                    cycle_started=datetime.now(timezone.utc)
                    await set_setting(db,'last_cycle_started_at',cycle_started.isoformat())
                    max_workers=max(1,min(4,int(await get_setting(db,'max_workers','2'))))
                    due_sources=await db.execute("SELECT * FROM sources WHERE enabled=1 AND (next_check_at IS NULL OR next_check_at <= ?) ORDER BY priority ASC,next_check_at ASC LIMIT ?",[cycle_started.isoformat(),MAX_AUTOMATION_SOURCES])
                    # Try publication first, then refill queue, then publish again.
                    await publish_next_article(db,bot)
                    sem=asyncio.Semaphore(max_workers)
                    async def run_source(src):
                        async with sem:
                            await set_setting(db,'worker_heartbeat_at',datetime.now(timezone.utc).isoformat())
                            return await fetch_source_cycle(db,src,ai)
                    results=[]
                    if due_sources:
                        results=await asyncio.gather(*(run_source(src) for src in due_sources),return_exceptions=True)
                    published=await publish_next_article(db,bot)
                    summary={
                        'sources':len(due_sources),
                        'processed':sum((r.get('processed',0) if isinstance(r,dict) else 0) for r in results),
                        'accepted':sum((r.get('accepted',0) if isinstance(r,dict) else 0) for r in results),
                        'rejected':sum((r.get('rejected',0) if isinstance(r,dict) else 0) for r in results),
                        'errors':sum((r.get('errors',0) if isinstance(r,dict) else 0) for r in results),
                        'queued':sum((r.get('queued',0) if isinstance(r,dict) else 0) for r in results),
                        'published':bool(published)
                    }
                    await set_setting(db,'last_cycle_result',json.dumps(summary,ensure_ascii=False))
                    await set_setting(db,'last_cycle_finished_at',datetime.now(timezone.utc).isoformat())
                if time.time()-last_provider_recheck>AI_PROVIDER_RECHECK_MINUTES*60:
                    await recheck_failed_providers(db,bot,ai); last_provider_recheck=time.time()
                if time.time()-last_cleanup>3600:
                    await cleanup_automation_data(db); last_cleanup=time.time()
                await set_setting(db,'worker_heartbeat_at',datetime.now(timezone.utc).isoformat())
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.exception('automation loop error')
                await log_automation(db,'ERROR','automation_loop_failed',str(e)[:1500])
                await set_setting(db,'last_cycle_result',json.dumps({'error':str(e)[:1000]},ensure_ascii=False))
                await set_setting(db,'worker_heartbeat_at',datetime.now(timezone.utc).isoformat())
            await asyncio.sleep(2)
    finally:
        await ai.close()



def format_duration_minutes(value) -> str:
    try: m=max(0,int(float(value)))
    except Exception: m=0
    if m < 60: return f"{m} دقیقه"
    h=m//60; rem=m%60
    return f"{h} ساعت" if rem==0 else f"{h} ساعت و {rem} دقیقه"

async def get_schedule_panel(db:D1Database):
    channel_id=await get_channel_id(db); channel_username=await get_setting(db,"channel_username","")
    shown=html.escape(channel_username) if channel_username else ("✅ کانال خصوصی تنظیم شده" if channel_id else "⛔ تنظیم نشده")
    enabled=(await get_setting(db,"automation_enabled","0"))=="1"
    max_daily=await get_setting(db,"max_daily_posts",str(DEFAULT_MAX_DAILY_POSTS))
    gap=int(float(await get_setting(db,"min_post_gap_minutes",str(DEFAULT_MIN_POST_GAP_MINUTES))))
    src_interval=await get_setting(db,"default_source_interval",str(DEFAULT_SOURCE_INTERVAL_MINUTES))
    workers=await get_setting(db,"max_workers",str(DEFAULT_MAX_WORKERS))
    ai_workers=await get_setting(db,"max_ai_workers",str(DEFAULT_MAX_AI_WORKERS))
    est=await next_publication_estimate(db)
    if est["minutes"]<=0: nxt="آماده انتشار طبق برنامه"
    elif est["minutes"]<60: nxt=f"حدود {est['minutes']} دقیقه دیگر"
    else: nxt=f"حدود {est['minutes']//60} ساعت و {est['minutes']%60} دقیقه دیگر"
    text=("📢 <b>انتشار و زمان‌بندی</b>\n\n"
          f"📢 کانال: <b>{shown}</b>\n"
          f"🤖 اتوماسیون: <b>{'🟢 فعال' if enabled else '🔴 خاموش'}</b>\n\n"
          f"🔢 سقف روزانه: <b>{max_daily}</b> پست\n"
          f"⏱ فاصله انتشار: <b>{format_duration_minutes(gap)}</b>\n"
          f"🌐 فاصله بررسی منابع: <b>{src_interval} دقیقه</b>\n"
          f"🕐 نوبت تقریبی بعدی: <b>{nxt}</b>")
    return text, schedule_menu_kb()

async def automation_report(db: D1Database) -> str:
    settings={
        'enabled':await get_setting(db,'automation_enabled','0'),
        'max_daily':await get_setting(db,'max_daily_posts',str(DEFAULT_MAX_DAILY_POSTS)),
        'min_score':await get_setting(db,'min_content_score',str(DEFAULT_MIN_CONTENT_SCORE)),
        'source_interval':await get_setting(db,'default_source_interval',str(DEFAULT_SOURCE_INTERVAL_MINUTES)),
        'publish_gap':await get_setting(db,'min_post_gap_minutes',str(DEFAULT_MIN_POST_GAP_MINUTES)),
    }
    sources=await db.execute("SELECT COUNT(*) c FROM sources WHERE enabled=1")
    discovered=await db.execute("SELECT COUNT(*) c FROM source_items WHERE discovered_at>=?",[(datetime.now(timezone.utc)-timedelta(days=1)).isoformat()])
    queued=await db.execute("SELECT COUNT(*) c FROM publication_queue WHERE status='queued'")
    published=await db.execute("SELECT COUNT(*) c FROM articles WHERE status='published' AND COALESCE(published_at,created_at)>=?",[datetime.now(timezone.utc).replace(hour=0,minute=0,second=0,microsecond=0).isoformat()])
    rejected=await db.execute("SELECT COUNT(*) c FROM source_items WHERE status='rejected' AND discovered_at>=?",[(datetime.now(timezone.utc)-timedelta(days=1)).isoformat()])
    failed=await db.execute("SELECT COUNT(*) c FROM publication_queue WHERE status='failed' AND created_at>=?",[(datetime.now(timezone.utc)-timedelta(days=1)).isoformat()])
    ready=await db.execute("SELECT COUNT(*) c FROM articles WHERE status='ready'")
    channel=await get_channel_id(db)
    channel_label=await get_setting(db,'channel_username','') or ('کانال خصوصی تنظیم شده' if channel else 'تنظیم نشده')
    hb=await get_setting(db,'worker_heartbeat_at','')
    last_cycle=await get_setting(db,'last_cycle_finished_at','')
    last_started=await get_setting(db,'last_cycle_started_at','')
    result_raw=await get_setting(db,'last_cycle_result','')
    hb_seconds=None
    if hb:
        try: hb_seconds=int((datetime.now(timezone.utc)-datetime.fromisoformat(hb.replace('Z','+00:00'))).total_seconds())
        except Exception: hb_seconds=None
    result_line='هنوز گزارشی ثبت نشده'
    if result_raw:
        try:
            obj=json.loads(result_raw)
            result_line=(f"منابع: {obj.get('sources',0)} · پردازش: {obj.get('processed',0)} · "
                         f"قبول: {obj.get('accepted',0)} · صف: {obj.get('queued',0)} · "
                         f"انتشار: {'بله ✅' if obj.get('published') else 'خیر ⏸'}")
            if obj.get('error'): result_line=f"خطا: {obj.get('error')}"
        except Exception:
            result_line='آخرین نتیجه قابل نمایش نیست'
    hb_label='نامشخص'
    if hb_seconds is not None:
        hb_label=f'{hb_seconds} ثانیه قبل'
        if hb_seconds < 180: hb_label += ' 🟢'
        elif hb_seconds < 600: hb_label += ' 🟡'
        else: hb_label += ' 🔴'
    return (
        "📊 <b>گزارش اتوماسیون</b>\n\n"
        f"{'🟢' if settings['enabled']=='1' else '🔴'} وضعیت: <b>{'فعال' if settings['enabled']=='1' else 'خاموش'}</b>\n"
        f"📢 کانال: <b>{html.escape(channel_label)}</b>\n"
        f"🌐 منابع فعال: <b>{sources[0].get('c',0) if sources else 0}</b>\n"
        f"📰 کشف/ثبت در ۲۴ ساعت: <b>{discovered[0].get('c',0) if discovered else 0}</b>\n"
        f"📥 صف فعلی: <b>{queued[0].get('c',0) if queued else 0}</b>\n"
        f"📝 آماده در آرشیو: <b>{ready[0].get('c',0) if ready else 0}</b>\n"
        f"📢 منتشرشده امروز: <b>{published[0].get('c',0) if published else 0}/{settings['max_daily']}</b>\n"
        f"♻️ ردشده در ۲۴ ساعت: <b>{rejected[0].get('c',0) if rejected else 0}</b>\n"
        f"❌ انتشار ناموفق ۲۴ ساعت: <b>{failed[0].get('c',0) if failed else 0}</b>\n"
        f"⭐ حداقل امتیاز: <b>{settings['min_score']}</b>\n"
        f"⏱ فاصله بررسی منابع: <b>{settings['source_interval']} دقیقه</b>\n"
        f"📢 فاصله انتشار: <b>{format_duration_minutes(settings['publish_gap'])}</b>\n"
        f"💓 Heartbeat: <b>{hb_label}</b>\n"
        f"🕐 آخرین شروع چرخه: <b>{html.escape(last_started or 'هنوز اجرا نشده')}</b>\n"
        f"✅ آخرین پایان چرخه: <b>{html.escape(last_cycle or 'هنوز اجرا نشده')}</b>\n"
        f"📋 آخرین نتیجه: <b>{html.escape(result_line)}</b>"
    )


async def automation_overview(db: D1Database) -> str:
    enabled=await get_setting(db,"automation_enabled","0")=="1"
    sources=await db.execute("SELECT COUNT(*) c FROM sources WHERE enabled=1")
    queued=await db.execute("SELECT COUNT(*) c FROM publication_queue WHERE status='queued'")
    max_daily=await get_setting(db,"max_daily_posts",str(DEFAULT_MAX_DAILY_POSTS))
    gap=await get_setting(db,"min_post_gap_minutes",str(DEFAULT_MIN_POST_GAP_MINUTES))
    interval=await get_setting(db,"default_source_interval",str(DEFAULT_SOURCE_INTERVAL_MINUTES))
    return ("📰 <b>اتوماسیون محتوا</b>\n\n"
            f"🤖 وضعیت: <b>{'🟢 فعال' if enabled else '🔴 خاموش'}</b>\n"
            f"🌐 منابع فعال: <b>{sources[0].get('c',0) if sources else 0}</b>\n"
            f"📥 صف فعلی: <b>{queued[0].get('c',0) if queued else 0}</b>\n"
            f"🔢 سقف روزانه: <b>{max_daily}</b>\n"
            f"⏱ فاصله انتشار: <b>{format_duration_minutes(gap)}</b>\n"
            f"🌐 فاصله بررسی منابع: <b>{interval} دقیقه</b>\n\n"
            "ℹ️ گزارش کامل فقط از دکمه «📊 گزارش» نمایش داده می‌شود.")

def automation_menu_kb(enabled: bool) -> InlineKeyboardMarkup:
    state_text = "⏸ خاموش کردن اتوماسیون" if enabled else "▶️ روشن کردن اتوماسیون"
    state_cb = "auto_off" if enabled else "auto_on"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=state_text, callback_data=state_cb)],
        [InlineKeyboardButton(text="🌐 منابع خبری", callback_data="auto_sources"), InlineKeyboardButton(text="🤖 مدل‌های AI", callback_data="auto_providers")],
        [InlineKeyboardButton(text="📢 انتشار و زمان‌بندی", callback_data="auto_channel"), InlineKeyboardButton(text="🧠 کیفیت محتوا", callback_data="auto_quality")],
        [InlineKeyboardButton(text="🗃 محتوا و داده‌ها", callback_data="auto_content_db")],
        [InlineKeyboardButton(text="🧪 تست و سلامت", callback_data="auto_health"), InlineKeyboardButton(text="📊 گزارش", callback_data="auto_report")],
        [InlineKeyboardButton(text="🔙 پنل اصلی", callback_data="admin_home")]
    ])


def source_list_kb(sources: List[Dict[str, Any]]) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(text="➕ افزودن منبع", callback_data="auto_add_source")]]
    for s in sources[:20]:
        mark = "🟢" if s.get("enabled") else "🔴"
        rows.append([InlineKeyboardButton(text=f"{mark} {s.get('name','source')[:35]}", callback_data=f"source_view_{s['id']}")])
    rows.append([InlineKeyboardButton(text="🔙 بازگشت", callback_data="auto_back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def provider_list_kb(providers: List[Dict[str, Any]]) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(text="➕ افزودن مدل جدید", callback_data="auto_add_provider")],
            [InlineKeyboardButton(text="ℹ️ راهنمای مدیریت مدل‌ها", callback_data="provider_help")]]
    for p in providers[:20]:
        status = p.get('status') or 'unknown'
        mark = {'healthy':'🟢', 'invalid':'🔴', 'cooldown':'🟡'}.get(status, '⚪')
        enabled = 'فعال' if p.get('enabled') else 'خاموش'
        webmark='🌐' if p.get('web_enabled') else ''
        label = f"{mark} #{p['id']} {webmark} {str(p.get('model_name','model'))[:30]} · {enabled}"
        rows.append([InlineKeyboardButton(text=label, callback_data=f"provider_view_{p['id']}")])
    rows.append([InlineKeyboardButton(text="🔙 اتوماسیون محتوا", callback_data="auto_back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def quality_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⭐ حداقل امتیاز انتشار", callback_data="set_min_score")],
        [InlineKeyboardButton(text="🎯 وزن معیارهای محتوا", callback_data="quality_weights")],
        [InlineKeyboardButton(text="✍️ دستورهای تولید محتوا", callback_data="editorial_prompts")],
        [InlineKeyboardButton(text="🔙 اتوماسیون محتوا", callback_data="auto_back")]
    ])


def schedule_menu_kb() -> InlineKeyboardMarkup:
    # The canonical schedule screen stays focused on settings the manager actually uses.
    # Worker/verification internals remain configurable elsewhere and are not mixed into this page.
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔢 سقف تقریبی پست روزانه", callback_data="set_max_daily")],
        [InlineKeyboardButton(text="⏱ حداقل فاصله پست‌ها", callback_data="set_min_gap")],
        [InlineKeyboardButton(text="🌐 فاصله بررسی منابع", callback_data="set_default_interval")],
        [InlineKeyboardButton(text="🚀 همین حالا منتشر کن", callback_data="publish_now")],
        [InlineKeyboardButton(text="🔙 اتوماسیون محتوا", callback_data="auto_back")]
    ])

async def reset_database(db: D1Database):
    queries = [
        {"sql": "DROP TABLE IF EXISTS users"},
        {"sql": "DROP TABLE IF EXISTS posts"},
        {"sql": "DROP TABLE IF EXISTS saves"},
        {"sql": "DROP TABLE IF EXISTS votes"},
        {"sql": "DROP TABLE IF EXISTS article_saves"},
        {"sql": "DROP TABLE IF EXISTS article_votes"},
        {"sql": "DROP TABLE IF EXISTS user_content_saves"},
        {"sql": "DROP TABLE IF EXISTS user_content_votes"},
        {"sql": "DROP TABLE IF EXISTS user_states"},
        {"sql": "DROP TABLE IF EXISTS processed_updates"},
        {"sql": "DROP TABLE IF EXISTS sources"},
        {"sql": "DROP TABLE IF EXISTS source_items"},
        {"sql": "DROP TABLE IF EXISTS articles"},
        {"sql": "DROP TABLE IF EXISTS publication_queue"},
        {"sql": "DROP TABLE IF EXISTS ai_providers"},
        {"sql": "DROP TABLE IF EXISTS automation_settings"},
        {"sql": "DROP TABLE IF EXISTS automation_logs"},
        {"sql": "DROP TABLE IF EXISTS manual_channel_events"},
        {"sql": "DROP TABLE IF EXISTS test_history"}
    ]
    await db.execute_batch(queries)
    await initialize_database(db)
    await migrate_unified_user_interactions(db)
    await initialize_automation_database(db)

# ============================================================
# ماشین وضعیت کاربران (FSM States)
# ============================================================
class BotStates(StatesGroup):
    idle = State()
    ai_chat = State()
    user_chat_admin = State()
    waiting_post_content = State()
    waiting_post_confirm = State()
    waiting_broadcast_content = State()
    waiting_broadcast_confirm = State()
    admin_search_word = State()
    admin_view_all = State()
    admin_post_edit = State()
    admin_source_priority = State()
    admin_content_weight = State()
    user_search_folder = State()
    admin_add_source = State()
    admin_add_provider = State()
    admin_provider_token = State()
    admin_provider_model = State()
    admin_channel_input = State()
    admin_automation_setting = State()
    automation_article_edit = State()

# ============================================================
# بخش کیبوردهای ربات (Keyboards)
# ============================================================
FOLDER_NAMES = {
    "cyber": "🔒 امنیت سایبری",
    "tech": "💻 تکنولوژی و فناوری",
    "ai": "🧠 هوش مصنوعی",
    "edu": "📚 آموزش"
}

def get_main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💾 ذخیره‌های من", callback_data="user_saves"), InlineKeyboardButton(text="👤 پروفایل", callback_data="user_profile")],
        [InlineKeyboardButton(text="❓ راهنما", callback_data="user_help")]
    ])


def get_admin_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📰 اتوماسیون محتوا", callback_data="admin_automation")],
        [InlineKeyboardButton(text="📁 مدیریت محتوای هسته", callback_data="admin_content")],
        [InlineKeyboardButton(text="📢 ارسال همگانی", callback_data="admin_broadcast"),
         InlineKeyboardButton(text="➕ افزودن پست", callback_data="admin_add_post")],
        [InlineKeyboardButton(text="📊 آمار کلی", callback_data="admin_stats")],
        [InlineKeyboardButton(text="👤 حالت کاربری", callback_data="admin_user_mode")]
    ])


def get_admin_back_kb(target="admin_home") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 بازگشت", callback_data=target)]])

def get_exit_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="❌ لغو و بازگشت", callback_data="cancel_state")]])

def get_folder_selection_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text=FOLDER_NAMES["cyber"], callback_data="f_view_cyber"),
                InlineKeyboardButton(text=FOLDER_NAMES["tech"], callback_data="f_view_tech")
            ],
            [
                InlineKeyboardButton(text=FOLDER_NAMES["ai"], callback_data="f_view_ai"),
                InlineKeyboardButton(text=FOLDER_NAMES["edu"], callback_data="f_view_edu")
            ]
        ]
    )

def get_save_to_folder_kb(content_type: str, content_id: int, back_cb: str = "user_saves") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text=FOLDER_NAMES["cyber"], callback_data=f"usave_{content_type}_{content_id}_cyber"),
                InlineKeyboardButton(text=FOLDER_NAMES["tech"], callback_data=f"usave_{content_type}_{content_id}_tech")
            ],
            [
                InlineKeyboardButton(text=FOLDER_NAMES["ai"], callback_data=f"usave_{content_type}_{content_id}_ai"),
                InlineKeyboardButton(text=FOLDER_NAMES["edu"], callback_data=f"usave_{content_type}_{content_id}_edu")
            ],
            [InlineKeyboardButton(text="🔙 برگشت", callback_data=back_cb)]
        ]
    )

def unified_saved_kb(folder: str = "all") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=FOLDER_NAMES["tech"],callback_data="saved_folder_tech"),InlineKeyboardButton(text=FOLDER_NAMES["ai"],callback_data="saved_folder_ai")],
        [InlineKeyboardButton(text=FOLDER_NAMES["cyber"],callback_data="saved_folder_cyber"),InlineKeyboardButton(text=FOLDER_NAMES["edu"],callback_data="saved_folder_edu")],
        [InlineKeyboardButton(text="🗂 همه",callback_data="saved_folder_all")],
        [InlineKeyboardButton(text="🏠 منوی اصلی",callback_data="user_home")]
    ])

def get_post_inline_kb(post_id: int, likes: int, dislikes: int, is_saved: bool) -> InlineKeyboardMarkup:
    save_text = "❌ حذف از ذخیره‌ها" if is_saved else "💾 ذخیره"
    save_cb = f"unsave_{post_id}" if is_saved else f"save_{post_id}"
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text=f"👍 {likes}", callback_data=f"like_{post_id}"),
                InlineKeyboardButton(text=f"👎 {dislikes}", callback_data=f"dis_{post_id}")
            ],
            [InlineKeyboardButton(text=save_text, callback_data=save_cb)],
            [InlineKeyboardButton(text="❓ راهنما", callback_data="user_help"), InlineKeyboardButton(text="🏠 منوی اصلی", callback_data="user_home")]
        ]
    )

def get_article_inline_kb(article_id: int, likes: int, dislikes: int, is_saved: bool) -> InlineKeyboardMarkup:
    save_text="❌ حذف از ذخیره‌ها" if is_saved else "💾 ذخیره"
    save_cb=f"aunsave_{article_id}" if is_saved else f"asave_{article_id}"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"👍 {likes}",callback_data=f"alike_{article_id}"),InlineKeyboardButton(text=f"👎 {dislikes}",callback_data=f"adis_{article_id}")],
        [InlineKeyboardButton(text=save_text,callback_data=save_cb)],
        [InlineKeyboardButton(text="🏠 منوی اصلی",callback_data="user_home")]
    ])

def get_saved_folder_pagination_kb(post_id: int, folder: str, index: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🗑️ حذف", callback_data=f"ask_del_{post_id}_{folder}")],
            [
                InlineKeyboardButton(text="⏮ قبلی", callback_data=f"fpg_prev_{folder}_{index}"),
                InlineKeyboardButton(text="⏭ بعدی", callback_data=f"fpg_next_{folder}_{index}")
            ],
            [InlineKeyboardButton(text="🔍 جستجو", callback_data=f"f_srch_{folder}")]
        ]
    )

def get_saved_folder_search_pagination_kb(post_id: int, folder: str, index: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🗑️ حذف", callback_data=f"ask_del_{post_id}_{folder}")],
            [
                InlineKeyboardButton(text="⏮ قبلی", callback_data=f"fspg_prev_{folder}_{index}"),
                InlineKeyboardButton(text="⏭ بعدی", callback_data=f"fspg_next_{folder}_{index}")
            ],
            [InlineKeyboardButton(text="🔍 جستجوی مجدد", callback_data=f"f_srch_{folder}")]
        ]
    )

def get_confirm_delete_kb(post_id: int, folder: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🗑️ بله، حذفش کن", callback_data=f"f_del_save_{post_id}_{folder}")],
            [InlineKeyboardButton(text="🔙 نه، پشیمون شدم", callback_data=f"cancel_delete_{folder}")]
        ]
    )

def get_confirm_add_post_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ بله، ثبتش کن!", callback_data="conf_add_yes"),
                InlineKeyboardButton(text="❌ خیر، بیخیال شو", callback_data="conf_add_no")
            ]
        ]
    )

def get_confirm_broadcast_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="🚀 بله، ارسال همگانی شود!", callback_data="conf_broad_yes"),
                InlineKeyboardButton(text="❌ لغو", callback_data="conf_broad_no")
            ]
        ]
    )

def get_content_management_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔍 جستجو", callback_data="adm_search_text"),
         InlineKeyboardButton(text="📋 همه محتواها", callback_data="adm_view_all")],
        [InlineKeyboardButton(text="🔙 بازگشت", callback_data="admin_home")]
    ])

def get_admin_search_pagination_kb(post_id: int, index: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⏮ قبلی", callback_data=f"asearch_prev_{index}"),
         InlineKeyboardButton(text="⏭ بعدی", callback_data=f"asearch_next_{index}")],
        [InlineKeyboardButton(text="✏️ ویرایش", callback_data=f"aedit_{post_id}"),
         InlineKeyboardButton(text="📊 آمار", callback_data=f"astats_{post_id}")],
        [InlineKeyboardButton(text="🗑️ حذف", callback_data=f"adelete_{post_id}"),
         InlineKeyboardButton(text="🔙 مدیریت محتوا", callback_data="admin_content")]
    ])

def get_admin_all_posts_kb(posts: list, page: int, total_pages: int) -> InlineKeyboardMarkup:
    rows=[]
    for p in posts:
        rows.append([
            InlineKeyboardButton(text=f"✏️ #{p['id']}",callback_data=f"aedit_{p['id']}"),
            InlineKeyboardButton(text=f"🗑 #{p['id']}",callback_data=f"adelete_{p['id']}")
        ])
    rows.append([
        InlineKeyboardButton(text="⏮ قبلی",callback_data=f"adm_all_page_prev_{page}"),
        InlineKeyboardButton(text=f"{page+1}/{total_pages}",callback_data="noop"),
        InlineKeyboardButton(text="⏭ بعدی",callback_data=f"adm_all_page_next_{page}")
    ])
    rows.append([InlineKeyboardButton(text="🔙 مدیریت محتوا",callback_data="admin_content")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def get_admin_view_all_confirm_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ نمایش",callback_data="adm_view_all_confirm")],
        [InlineKeyboardButton(text="❌ لغو",callback_data="adm_view_all_cancel")]
    ])

def get_help_more_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="💡 بیشتر بهم توضیح بده", callback_data="help_more")]
        ]
    )

def get_help_got_it_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🤓 متوجه شدم!", callback_data="help_got_it")]
        ]
    )

# ============================================================
# بخش‌های کمکی هوش مصنوعی و منطقه زمانی (AI & Zone Utilities)
# ============================================================
def get_tehran_date() -> str:
    tehran_tz = pytz.timezone("Asia/Tehran")
    now_tehran = datetime.now(tehran_tz)
    return now_tehran.strftime("%Y-%m-%d")

async def download_telegram_file_text(bot: Bot, file_id: str) -> str:
    file_info = await bot.get_file(file_id)
    dest = io.BytesIO()
    await bot.download_file(file_info.file_path, destination=dest)
    dest.seek(0)
    text = dest.read().decode('utf-8', errors='ignore')
    if len(text) > 15000:
        text = text[:15000] + "\n\n[حجم فایل زیاد بود، بخشی از آن بررسی شد]"
    return text

async def call_ai_with_history(url: str, api_key: str, model: str, messages: List[Dict[str, str]]) -> Dict[str, Any]:
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json"
    }
    payload = {
        "model": model,
        "messages": messages
    }
    async with aiohttp.ClientSession() as session:
        try:
            async with session.post(url, headers=headers, json=payload) as resp:
                if resp.status != 200:
                    text = await resp.text()
                    return {
                        "content": f"❌ خطا در پاسخ هوش مصنوعی (کد {resp.status}):\n`{text}`",
                        "tokens": 0
                    }
                
                data = await resp.json()
                if "error" in data:
                    err_msg = data["error"].get("message", str(data["error"]))
                    return {
                        "content": f"❌ خطا:\n`{err_msg}`",
                        "tokens": 0
                    }
                
                if "choices" in data and len(data["choices"]) > 0:
                    content = data["choices"][0]["message"]["content"]
                    total_tokens = data.get("usage", {}).get("total_tokens", math.ceil(len(content) / 4))
                    return {
                        "content": content,
                        "tokens": total_tokens
                    }
                return {
                    "content": f"⚠️ پاسخی دریافت نشد:\n`{data}`",
                    "tokens": 0
                }
        except Exception as e:
            return {
                "content": f"❌ خطای ارتباط با سرور هوش مصنوعی: {str(e)}",
                "tokens": 0
            }

# ============================================================
# میدل‌ور ممانعت از اسپم (Rate Limiter Middleware)
# ============================================================
FUNNY_MESSAGES = [
    "آروم‌تر قهرمان! 🏎️",
    "دکمه‌ها گناه دارن، یواش‌تر! 🥺",
    "اسپم نکن مشتی، یکم استراحت کن ☕",
    "سرعتت زیاده! یواش‌تر بران 🛑",
    "آروم‌تر بکوب رو دکمه‌ها دوست من! 🛠️"
]

class RateLimitMiddleware(BaseMiddleware):
    def __init__(self, admin_id: int):
        super().__init__()
        self.admin_id = admin_id
        self.rate_limit_map = {}

    async def __call__(self, handler, event: TelegramObject, data: dict):
        user_id = None
        if isinstance(event, Message) and event.from_user:
            user_id = event.from_user.id
        elif isinstance(event, CallbackQuery) and event.from_user:
            user_id = event.from_user.id
            
        if user_id and user_id != self.admin_id:
            now = time.time()
            last_active = self.rate_limit_map.get(user_id, 0.0)
            if now - last_active < 1.0:
                msg = random.choice(FUNNY_MESSAGES)
                if isinstance(event, Message):
                    await event.answer(msg)
                elif isinstance(event, CallbackQuery):
                    await event.answer(msg, show_alert=True)
                return
            self.rate_limit_map[user_id] = now
            
        return await handler(event, data)

# ============================================================
# ثبت هندلرهای ربات (Telegram Event Handlers)
# ============================================================
router = Router()

async def register_user_if_not_exists(db: D1Database, user_id: int):
    sql = "INSERT OR IGNORE INTO users(id, joined_at) VALUES(?, ?)"
    await db.execute(sql, [user_id, datetime.now(timezone.utc).isoformat()])

async def send_post_content(bot: Bot, chat_id: int, post: dict, reply_markup=None):
    text = post.get("text") or ""
    file_id = post.get("file_id")
    media_type = post.get("media_type")
    
    caption = text if len(text) <= 1024 else text[:1020] + "..."
    
    try:
        if media_type == "photo" and file_id:
            return await bot.send_photo(chat_id=chat_id, photo=file_id, caption=caption, reply_markup=reply_markup)
        elif media_type == "document" and file_id:
            return await bot.send_document(chat_id=chat_id, document=file_id, caption=caption, reply_markup=reply_markup)
        elif media_type == "video" and file_id:
            return await bot.send_video(chat_id=chat_id, video=file_id, caption=caption, reply_markup=reply_markup)
        elif media_type == "audio" and file_id:
            return await bot.send_audio(chat_id=chat_id, audio=file_id, caption=caption, reply_markup=reply_markup)
        else:
            safe_text = text if len(text) <= 4096 else text[:4090] + "..."
            return await bot.send_message(chat_id=chat_id, text=safe_text or "محتوای ارسالی", reply_markup=reply_markup)
    except Exception as e:
        logger.error(f"Error sending post content: {e}")
        return None

# هندلرهای دستورات اصلی که باید بالاتر از بقیه هندلرهای متنی باشند
async def deliver_article_by_token(message: Message, bot: Bot, db: D1Database, token: str) -> bool:
    token=(token or '').strip()
    if token.startswith(('auto_','article_')):
        token=token.split('_',1)[1]
    if not re.fullmatch(r'[A-Za-z0-9_-]{6,64}', token):
        return False
    rows=await db.execute("SELECT * FROM articles WHERE deep_token=? AND status IN ('ready','published','test')",[token])
    if not rows: return False
    article=rows[0]
    article_id=int(article.get('id') or 0)
    try: await db.execute("UPDATE articles SET deep_views=COALESCE(deep_views,0)+1 WHERE id=?",[article_id])
    except Exception: pass

    title=html.escape(str(article.get('title') or 'مطلب'))
    body=_remove_duplicate_title_from_body(article.get('title') or '', remove_article_metadata_blocks(dedupe_adjacent_emojis(sanitize_telegram_html(article.get('body') or ''))))
    source_url=normalize_url(article.get('source_url') or '')
    if source_url and 'منبع اصلی' not in strip_html_text(body):
        body=f"{body.rstrip()}\n\n<a href=\"{html.escape(source_url,quote=True)}\">منبع اصلی</a>"
    relative=relative_time_label(article.get('source_published_at') or article.get('published_at') or '')
    if relative != 'زمان نامشخص':
        body=body.rstrip()+f"\n\n<i>⏱ {relative}</i>"
    full=f"<b>📖 {title}</b>\n\n{body}"

    like_rows=await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='like'",[article_id])
    dislike_rows=await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='dislike'",[article_id])
    save_rows=await db.execute("SELECT folder FROM user_content_saves WHERE user_id=? AND content_type='article' AND content_id=?",[message.from_user.id,article_id])
    kb=get_article_inline_kb(article_id,like_rows[0].get('c',0) if like_rows else 0,dislike_rows[0].get('c',0) if dislike_rows else 0,bool(save_rows))

    image=await resolve_article_image(db,article)
    if image:
        try:
            photo_caption=f"<b>📖 {title}</b>"
            if relative != 'زمان نامشخص':
                photo_caption += f"\n\n<i>⏱ {relative}</i>"
            await bot.send_photo(message.chat.id,photo=image,caption=photo_caption,parse_mode='HTML')
        except Exception:
            pass
    first=True
    for i in range(0,len(full),3800):
        chunk=full[i:i+3800]
        if chunk:
            await message.answer(chunk,parse_mode='HTML',disable_web_page_preview=True,reply_markup=kb if i+3800>=len(full) else None)
            first=False
    return True

@router.message(Command("help"))
async def cmd_help(message: Message):
    await message.answer("🌐 /help • help ➜ راهنما\n📞 /man • man ➜ تماس با مدیر\n🚀 /start • start ➜ شروع\n✨ انتخاب کن و شروع کن 🚀", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 منوی اصلی", callback_data="user_home")]]))

@router.message(Command("man"))
async def cmd_man(message: Message, state: FSMContext):
    await state.set_state(BotStates.user_chat_admin)
    await message.answer("📞 پیام خود را برای مدیریت ارسال کن.", reply_markup=get_exit_menu())

@router.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    user_id = message.from_user.id
    await register_user_if_not_exists(db, user_id)
    await state.set_state(BotStates.idle)
    state_data = await state.get_data()
    
    args = message.text.split()
    if len(args) > 1:
        deep_arg = args[1]
        if deep_arg.startswith(("auto_", "article_")):
            ok=await deliver_article_by_token(message,bot,db,deep_arg)
            if not ok:
                await message.answer("❌ این لینک ادامه مطلب معتبر نیست یا مقاله دیگر در دسترس نیست.", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 منوی اصلی", callback_data="user_home")]]))
            return
        post_id_str = deep_arg
        if post_id_str.isdigit():
            post_id = int(post_id_str)
            post_rows = await db.execute(
                "SELECT text, file_id, media_type, likes, dislikes FROM posts WHERE id = ? AND deleted = 0",
                [post_id]
            )
            if post_rows:
                post = post_rows[0]
                await db.execute("UPDATE posts SET views = views + 1 WHERE id = ?", [post_id])
                save_rows = await db.execute("SELECT folder FROM user_content_saves WHERE user_id = ? AND content_type='post' AND content_id = ?", [user_id, post_id])
                is_saved = len(save_rows) > 0
                
                kb = get_post_inline_kb(post_id, post.get("likes", 0), post.get("dislikes", 0), is_saved)
                await send_post_content(bot, message.chat.id, post, kb)
                return
            else:
                await message.answer("❌ این پست یافت نشد یا حذف شده است.")
                return

    first_name = message.from_user.first_name or "دوست عزیز"
    welcomes = [
        f"سلام {first_name} عزیز! 👋 خیلی خوش اومدی. وقت کاوش تو دنیای تکنولوژیه! 🚀",
        f"درود {first_name}! 🌟 خوشحالیم که اینجایی. آماده‌ای برای مطالب جذاب؟ 📚",
        f"سلام {first_name} جان! 🤖 به پایگاه دانش ما خوش اومدی. بزن بریم که کلی مطلب خفن داریم! 🔥"
    ]
    welcome_text = random.choice(welcomes) + "\n\nاز دکمه های پایین استفاده کنید👇🏻"
    
    admin_mode = state_data.get("admin_mode", "user")
    menu = get_admin_menu() if (user_id == ADMIN_ID and admin_mode != "user") else get_main_menu()
    await message.answer(welcome_text, reply_markup=menu)

@router.message(Command("article"))
async def cmd_article(message: Message, db: D1Database, bot: Bot):
    parts=(message.text or '').split(maxsplit=1)
    if len(parts)<2:
        await message.answer("فرمت: /article TOKEN")
        return
    if not await deliver_article_by_token(message,bot,db,parts[1]):
        await message.answer("❌ مقاله پیدا نشد یا لینک منقضی شده است.")

@router.message(Command("setup_db"))
async def cmd_setup_db(message: Message, db: D1Database):
    if message.from_user.id == ADMIN_ID:
        try:
            await initialize_database(db)
            await message.answer("✅ Database setup completed successfully.")
        except Exception as e:
            await message.answer(f"❌ Error: {str(e)}")

@router.message(Command("reset_db"))
async def cmd_reset_db(message: Message, db: D1Database):
    if message.from_user.id == ADMIN_ID:
        try:
            await reset_database(db)
            await message.answer("✅ Database reset successfully!")
        except Exception as e:
            await message.answer(f"❌ Error: {str(e)}")

@router.message(F.text == "❌ خروج از نشست")
async def cmd_exit_session(message: Message, state: FSMContext):
    data = await state.get_data()
    admin_mode = data.get("admin_mode", "user")
    
    clean_data = {
        "admin_mode": admin_mode,
        "search_count": data.get("search_count", 0),
        "search_window_start": data.get("search_window_start", 0)
    }
    await state.set_state(BotStates.idle)
    await state.set_data(clean_data)
    
    menu = get_admin_menu() if (message.from_user.id == ADMIN_ID and admin_mode != "user") else get_main_menu()
    await message.answer("🚪 خروج از نشست با موفقیت انجام شد!\n", reply_markup=menu)

# ============================================================
# هندلرهای مبتنی بر وضعیت فعال (FSM Messages) - اولویت بالا
# ============================================================
@router.message(StateFilter(BotStates.ai_chat))
async def process_ai_chat(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    user_id = message.from_user.id
    
    providers = await db.execute("SELECT id FROM ai_providers WHERE enabled=1 AND (status IS NULL OR status != 'invalid') LIMIT 1")
    if not providers:
        await message.answer("⚠️ هنوز هیچ مدل فعالی در پنل هوش مصنوعی تنظیم نشده است. از مدیریت، مدل را اضافه و تست کن.")
        return

    today_tehran = get_tehran_date()
    user_rows = await db.execute("SELECT tokens_used, last_reset_date FROM users WHERE id = ?", [user_id])
    
    tokens_used = 0
    last_reset = ""
    if user_rows:
        tokens_used = user_rows[0].get("tokens_used") or 0
        last_reset = user_rows[0].get("last_reset_date") or ""
        
    if last_reset != today_tehran:
        tokens_used = 0
        last_reset = today_tehran
        await db.execute("UPDATE users SET tokens_used = 0, last_reset_date = ? WHERE id = ?", [today_tehran, user_id])
        
    if tokens_used >= 10000:
        await message.answer(
            "⛔ سهمیه ۱۰۰۰۰ توکن شما برای امروز به پایان رسیده است.\n\n⏱️ سهمیه شما ساعت ۰۰:۰۰ بامداد فردا مجدداً فعال خواهد شد. فردا در خدمت شما هستیم! 🔄"
        )
        return

    user_prompt = ""
    if message.text:
        user_prompt = message.text
    elif message.document:
        await message.answer("⏳ در حال خواندن فایل متنی شما...")
        try:
            file_content = await download_telegram_file_text(bot, message.document.file_id)
            caption = f"\nتوضیحات: {message.caption}" if message.caption else ""
            user_prompt = f"لطفاً این فایل را بررسی کن:\n\n```\n{file_content}\n```{caption}"
        except Exception as e:
            await message.answer(f"⚠️ خطا در خواندن فایل:\n{str(e)}")
            return
    else:
        await message.answer("⚠️ لطفاً یک متن یا فایل متنی معتبر ارسال کنید.")
        return

    await bot.send_chat_action(chat_id=message.chat.id, action="typing")
    
    state_data = await state.get_data()
    history = state_data.get("ai_history", [
        {"role": "system", "content": "You are a helpful assistant. Reply clearly in Persian."}
    ])
    history.append({"role": "user", "content": user_prompt})
    
    if len(history) > 11:
        history = [history[0]] + history[-10:]
        
    ai_manager = AIProviderManager(db, bot)
    try:
        ai_result = await ai_manager.call(history, temperature=0.25, max_tokens=3500, purpose="user_chat")
    finally:
        await ai_manager.close()
    if ai_result.get("error") and not ai_result.get("content"):
        await message.answer("⚠️ هیچ مدل فعالی پاسخ نداد.\n\n" + html.escape(ai_result.get("error", "خطای نامشخص"))[:1800])
        return
    
    history.append({"role": "assistant", "content": ai_result["content"]})
    await state.update_data(ai_history=history)
    
    response_text = ai_result["content"]
    max_length = 3900
    for i in range(0, len(response_text), max_length):
        chunk = response_text[i:i+max_length]
        try:
            await message.answer(chunk, parse_mode="Markdown")
        except Exception:
            await message.answer(chunk)
            
    tokens_used += ai_result["tokens"]
    await db.execute("UPDATE users SET tokens_used = ?, last_reset_date = ? WHERE id = ?", [tokens_used, today_tehran, user_id])

@router.message(StateFilter(BotStates.user_chat_admin))
async def process_user_chat_admin(message: Message, state: FSMContext, bot: Bot):
    user_id = message.from_user.id
    if user_id == ADMIN_ID:
        return
        
    hashtag = f"#User_{user_id}"
    caption = message.caption or ""
    
    if message.photo:
        await bot.send_photo(chat_id=ADMIN_ID, photo=message.photo[-1].file_id, caption=f"پیام جدید:\n{hashtag}\n\n{caption}")
    elif message.document:
        await bot.send_document(chat_id=ADMIN_ID, document=message.document.file_id, caption=f"فایل جدید:\n{hashtag}\n\n{caption}")
    elif message.video:
        await bot.send_video(chat_id=ADMIN_ID, video=message.video.file_id, caption=f"ویدیو جدید:\n{hashtag}\n\n{caption}")
    elif message.audio:
        await bot.send_audio(chat_id=ADMIN_ID, audio=message.audio.file_id, caption=f"صوت جدید:\n{hashtag}\n\n{caption}")
    elif message.text:
        await bot.send_message(chat_id=ADMIN_ID, text=f"پیام جدید:\n{hashtag}\n\n{message.text}")

@router.message(StateFilter(BotStates.waiting_post_content))
async def process_add_post_content(message: Message, state: FSMContext, bot: Bot):
    if message.from_user.id != ADMIN_ID:
        return
        
    file_id, media_type = None, None
    caption = message.text or message.caption or ""
    
    if message.photo:
        file_id = message.photo[-1].file_id
        media_type = "photo"
    elif message.document:
        file_id = message.document.file_id
        media_type = "document"
    elif message.video:
        file_id = message.video.file_id
        media_type = "video"
    elif message.audio:
        file_id = message.audio.file_id
        media_type = "audio"
        
    if not file_id and not caption.strip():
        await message.answer("❌ لطفاً متن یا فایل معتبر ارسال کنید.")
        return
        
    await state.update_data(temp_text=caption, temp_file_id=file_id, temp_media_type=media_type)
    await state.set_state(BotStates.waiting_post_confirm)
    
    post_mock = {"text": caption, "file_id": file_id, "media_type": media_type}
    await send_post_content(bot, message.chat.id, post_mock)
    await message.answer("آیا مایلید این محتوا ذخیره گردد؟", reply_markup=get_confirm_add_post_kb())

@router.message(StateFilter(BotStates.waiting_broadcast_content))
async def process_broadcast_content(message: Message, state: FSMContext, bot: Bot):
    if message.from_user.id != ADMIN_ID:
        return
        
    file_id, media_type = None, None
    caption = message.text or message.caption or ""
    
    if message.photo:
        file_id = message.photo[-1].file_id
        media_type = "photo"
    elif message.document:
        file_id = message.document.file_id
        media_type = "document"
    elif message.video:
        file_id = message.video.file_id
        media_type = "video"
    elif message.audio:
        file_id = message.audio.file_id
        media_type = "audio"
        
    if not file_id and not caption.strip():
        await message.answer("❌ لطفاً متن یا فایل معتبر ارسال کنید.")
        return
        
    broadcast_caption = caption + "\n\n#Broadcast"
    await state.update_data(temp_text=broadcast_caption, temp_file_id=file_id, temp_media_type=media_type)
    await state.set_state(BotStates.waiting_broadcast_confirm)
    
    post_mock = {"text": broadcast_caption, "file_id": file_id, "media_type": media_type}
    await send_post_content(bot, message.chat.id, post_mock)
    await message.answer("از ارسال نهایی این پیام به تمامی اعضا مطمئن هستید؟", reply_markup=get_confirm_broadcast_kb())

@router.message(StateFilter(BotStates.user_search_folder))
async def process_user_search_folder(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    query_text = (message.text or "").strip()
    if not query_text:
        return
        
    state_data = await state.get_data()
    folder = state_data.get("folder")
    if not folder:
        await state.set_state(BotStates.idle)
        await message.answer("❌ خطا در پوشه جستجو، لطفاً دوباره از پوشه‌ها وارد شوید.")
        return
        
    now = time.time() * 1000
    WINDOW_MS = 8 * 60 * 60 * 1000
    search_count = state_data.get("search_count", 0)
    window_start = state_data.get("search_window_start", 0)
    
    if now - window_start > WINDOW_MS:
        search_count = 0
        window_start = 0
        
    if search_count >= 5:
        unlock_time_ms = window_start + WINDOW_MS
        tehran_tz = pytz.timezone("Asia/Tehran")
        unlock_dt = datetime.fromtimestamp(unlock_time_ms / 1000, tehran_tz)
        time_str = unlock_dt.strftime("%H:%M")
        day_str = "امروز" if unlock_dt.date() == datetime.now(tehran_tz).date() else "فردا"
        
        await message.answer(f"⏱️ موتور جستجوی اختصاصی شما {day_str} ساعت {time_str} فعال میشه\n\n تا اون موقع می‌تونی دستی پوشه‌هات رو ورق بزنی ! 🕵️‍♂️")
        await state.set_state(BotStates.idle)
        return
        
    if search_count == 0:
        window_start = now
    search_count += 1
    
    await state.update_data(search_count=search_count, search_window_start=window_start)
    
    rows = await db.execute(
        """SELECT posts.id FROM user_content_saves s JOIN posts ON s.content_id = posts.id AND s.content_type='post'
           WHERE s.user_id = ? AND s.folder = ? AND posts.text LIKE ? AND posts.deleted = 0
           ORDER BY posts.id DESC LIMIT 30""",
        [message.from_user.id, folder, f"%{query_text}%"]
    )
    
    if not rows:
        await message.answer("❌ محتوایی با این کلمه پیدا نکردم 🫠\nیه کلمه دیگه بفرست تا دوباره بگردم:")
        return
        
    search_ids = [r["id"] for r in rows]
    await state.update_data(search_ids=search_ids, search_index=0)
    await message.answer(f"🎉 {len(search_ids)} تا مطلب با این کلمه پیدا کردم!\n(هر وقت خواستی جستجو رو عوض کنی، کافیه یه کلمه جدید بفرستی 🔄)")
    
    first_post_id = search_ids[0]
    post_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [first_post_id])
    if post_rows:
        kb = get_saved_folder_search_pagination_kb(first_post_id, folder, 0)
        await send_post_content(bot, message.chat.id, post_rows[0], kb)

# ============================================================
# هندلرهای کمکی، عمومی و منوهای اصلی (FSM Idle/None)
# ============================================================

# ریپلای ادمین فقط در وضعیت idle یا None قابل استفاده است و با وضعیت‌های فعال تداخلی ندارد
@router.message(F.chat.id == ADMIN_ID, F.reply_to_message, StateFilter(None, BotStates.idle))
async def process_admin_replies(message: Message, state: FSMContext, bot: Bot):
    reply_text = message.reply_to_message.text or message.reply_to_message.caption or ""
    match = re.search(r"#User_(\d+)", reply_text)
    if match:
        target_user = int(match.group(1))
        prefix = "پاسخ مدیریت:\n\n"
        caption = message.caption or ""
        
        try:
            if message.photo:
                await bot.send_photo(chat_id=target_user, photo=message.photo[-1].file_id, caption=f"{prefix}{caption}")
            elif message.document:
                await bot.send_document(chat_id=target_user, document=message.document.file_id, caption=f"{prefix}{caption}")
            elif message.video:
                await bot.send_video(chat_id=target_user, video=message.video.file_id, caption=f"{prefix}{caption}")
            elif message.audio:
                await bot.send_audio(chat_id=target_user, audio=message.audio.file_id, caption=f"{prefix}{caption}")
            elif message.text:
                await bot.send_message(chat_id=target_user, text=f"{prefix}{message.text}")
            await message.answer("✅ پاسخ شما با موفقیت ارسال شد.")
        except Exception as e:
            await message.answer(f"❌ خطا در ارسال پیام به کاربر: {e}")

COMMANDS_LIST = [
    "کاربر", "مدیریت", "💾 ذخیره‌های من", "❓ راهنما", "👤 پروفایل", "➕ افزودن پست",
    "📁 مدیریت محتوا", "📊 آمار", "📢 ارسال همگانی", "⚙️ اتوماسیون محتوا"
]

@router.message(F.text.in_(COMMANDS_LIST), StateFilter(None, BotStates.idle))
async def intercept_global_commands(message: Message, state: FSMContext, db: D1Database):
    text = message.text
    user_id = message.from_user.id
    state_data = await state.get_data()
    
    if text == "کاربر":
        await state.update_data(admin_mode="user")
        await message.answer("✅ فاز کاربری فعال شد.", reply_markup=get_main_menu())
        
    elif text == "مدیریت":
        if user_id == ADMIN_ID:
            await state.update_data(admin_mode="admin")
            await message.answer("✅ پنل مدیریت فعال شد.", reply_markup=get_admin_menu())
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")
            
    elif text == "❓ راهنما":
        await message.answer("🌐 /help • راهنما\n📞 /man • تماس با مدیر\n🚀 /start • شروع", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 منوی اصلی", callback_data="user_home")]]))
        
    elif text == "👤 پروفایل":
        rows = await db.execute("SELECT joined_at, role FROM users WHERE id = ?", [user_id])
        joined_str = rows[0].get("joined_at") if rows else None
        user_role_db = rows[0].get("role") if rows else "user"
        
        time_string = "🌱 وضعیت عضویت: تازه وارد"
        join_date_line = ""
        
        if joined_str:
            try:
                joined_dt = datetime.fromisoformat(joined_str).replace(tzinfo=timezone.utc)
                delta = datetime.now(timezone.utc) - joined_dt
                days = max(0, delta.days)
                time_string = f"⏱️ مدت همراهی: {days} روز پیش" if days else "⏱️ مدت همراهی: امروز"
                tehran_tz = pytz.timezone("Asia/Tehran")
                joined_tehran = joined_dt.astimezone(tehran_tz)
                date_str = joined_tehran.strftime("%Y/%m/%d")
                join_date_line = f"📅 تاریخ عضویت: {date_str}\n"
            except Exception:
                pass
                
        saves_count = (await db.execute("SELECT COUNT(*) as c FROM user_content_saves WHERE user_id = ?", [user_id]))[0].get("c", 0)
        likes_count = (await db.execute("SELECT COUNT(*) as c FROM user_content_votes WHERE user_id = ? AND vote_type = 'like'", [user_id]))[0].get("c", 0)
        dislikes_count = (await db.execute("SELECT COUNT(*) as c FROM user_content_votes WHERE user_id = ? AND vote_type = 'dislike'", [user_id]))[0].get("c", 0)
        
        role_display = "مدیر 🌟" if user_role_db == "admin" else "کاربر عادی 🟢"
        first_name_clean = message.from_user.first_name or "عزیز"
        article_saves_count=0
        article_likes_count=0
        profile_text = f"""👤 <b>پروفایل</b> · {html.escape(first_name_clean)}

🗓 <b>عضویت</b>
{join_date_line}{time_string}

📚 <b>فعالیت</b>
💾 ذخیره‌ها: <b>{saves_count + article_saves_count}</b>
👍 لایک‌ها: <b>{likes_count + article_likes_count}</b>
👎 دیس‌لایک‌ها: <b>{dislikes_count}</b>

🔰 <b>{role_display}</b>"""
        await message.answer(profile_text, parse_mode="HTML", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 منوی اصلی", callback_data="user_home")]]))
        
    elif text == "💾 ذخیره‌های من":
        await message.answer("📂 کدوم پوشه رو میخوای باز کنی؟ 👇", reply_markup=get_folder_selection_kb())
        
    elif text == "➕ افزودن پست":
        if user_id == ADMIN_ID:
            await state.set_state(BotStates.waiting_post_content)
            await message.answer("📝 لطفاً متن، تصویر، ویدیو یا سند جدید خود را ارسال کنید:", reply_markup=get_exit_menu())
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")
            
    elif text == "📁 مدیریت محتوا":
        if user_id == ADMIN_ID:
            await message.answer("📂 انتخاب کنید:", reply_markup=get_content_management_kb())
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")
            
    elif text == "📊 آمار":
        if user_id == ADMIN_ID:
            total_users = (await db.execute("SELECT COUNT(*) as c FROM users"))[0].get("c", 0)
            total_likes = (await db.execute("SELECT SUM(likes) as s FROM posts"))[0].get("s") or 0
            total_views = (await db.execute("SELECT SUM(views) as s FROM posts"))[0].get("s") or 0
            active_posts = (await db.execute("SELECT COUNT(*) as c FROM posts WHERE deleted = 0"))[0].get("c", 0)
            total_posts = (await db.execute("SELECT COUNT(*) as c FROM posts"))[0].get("c", 0)
            
            stat_text = f"""📊 آمار کلی ربات:

👥 کل کاربران: {total_users} نفر
📝 کل پست‌ها: {total_posts}
📄 پست‌های فعال: {active_posts}
👁️ مجموع بازدید: {total_views}
👍 مجموع لایک‌ها: {total_likes}"""
            await message.answer(stat_text)
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")
            
    elif text == "📢 ارسال همگانی":
        if user_id == ADMIN_ID:
            await state.set_state(BotStates.waiting_broadcast_content)
            await message.answer("📢 پیام همگانی خود را بفرستید (متن، عکس، ویدیو یا سند):", reply_markup=get_exit_menu())
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")
    elif text == "⚙️ اتوماسیون محتوا":
        if user_id == ADMIN_ID:
            enabled = (await get_setting(db, "automation_enabled", "0")) == "1"
            overview = await automation_overview(db)
            await message.answer(overview, parse_mode="HTML", reply_markup=automation_menu_kb(enabled))
        else:
            await message.answer("⛔ شما دسترسی مدیریت ندارید.")

@router.message(StateFilter(None, BotStates.idle))
async def process_unknown_commands(message: Message, state: FSMContext):
    data=await state.get_data()
    if message.from_user.id==ADMIN_ID and data.get("admin_mode")=="admin":
        await message.answer("❌ دستور نامعتبر است. از منوی همین بخش استفاده کن.",reply_markup=get_admin_menu())
    else:
        await message.answer("❌ دستور نامعتبر است. از منوی همین بخش استفاده کن.",reply_markup=get_main_menu())


# ============================================================
# پنل مدیریت اتوماسیون محتوا
# ============================================================

@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_add_source))
async def admin_add_source_input(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    url = (message.text or "").strip()
    if not url or not re.match(r"^https?://", url, re.I):
        await message.answer("❌ URL معتبر نیست. نمونه:\nhttps://example.com",reply_markup=get_exit_menu())
        return
    try:
        source_id = await add_source(db, url)
        data = await state.get_data()
        panel_id = data.get('panel_message_id')
        await state.set_state(BotStates.idle)
        rows = await db.execute("SELECT * FROM sources ORDER BY priority ASC, id ASC")
        if panel_id:
            try:
                await bot.edit_message_text(chat_id=message.chat.id, message_id=panel_id, text=f"✅ منبع اضافه شد.\n\nشناسه: {source_id}", reply_markup=source_list_kb(rows))
                return
            except Exception:
                pass
        await message.answer(f"✅ منبع با موفقیت اضافه شد.\nشناسه: {source_id}", reply_markup=source_list_kb(rows))
    except Exception as e:
        await message.answer(f"❌ افزودن منبع ناموفق بود:\n{html.escape(str(e))}",reply_markup=get_exit_menu())



@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_automation_setting))
async def admin_automation_setting_input(message:Message,state:FSMContext,db:D1Database,bot:Bot):
    data=await state.get_data(); key=data.get("automation_setting_key"); value=(message.text or "").strip()
    parent=data.get("parent_callback","admin_home")
    try:
        if key=="__source_interval__":
            sid=int(data["source_interval_id"]); value=str(max(1,int(value)))
            await db.execute("UPDATE sources SET interval_minutes=?,next_check_at=? WHERE id=?",[int(value),datetime.now(timezone.utc).isoformat(),sid])
            parent=f"source_view_{sid}"
        elif key=="__source_priority__":
            sid=int(data["source_priority_id"]); value=str(max(1,int(value)))
            await db.execute("UPDATE sources SET priority=? WHERE id=?",[int(value),sid]); parent=f"source_view_{sid}"
        elif key=="__provider_priority__":
            pid=int(data["provider_priority_id"]); value=str(max(1,int(value)))
            await db.execute("UPDATE ai_providers SET priority=?,updated_at=? WHERE id=?",[int(value),datetime.now(timezone.utc).isoformat(),pid]); parent=f"provider_view_{pid}"
        elif key.startswith("weight_"):
            value=str(max(0,min(100,float(value)))); await set_setting(db,key,value); parent="quality_weights"
        elif key in {"max_daily_posts","default_source_interval"}:
            value=str(max(1,int(value)))
            await set_setting(db,key,value)
            if key == "default_source_interval":
                now_interval=datetime.now(timezone.utc).isoformat()
                await db.execute("UPDATE sources SET interval_minutes=?, next_check_at=? WHERE enabled=1",[int(value),now_interval])
        elif key in {"max_workers","max_ai_workers"}:
            value=str(max(1,min(4,int(value)))); await set_setting(db,key,value); parent="auto_schedule"
        elif key=="min_content_score":
            value=str(max(0,min(100,float(value)))); await set_setting(db,key,value)
        elif key in {"editorial_prompt_channel","editorial_prompt_article"}:
            if not value: raise ValueError("پرامپت نمی‌تواند خالی باشد.")
            if len(value)>5000: value=value[:5000]
            await set_setting(db,key,value)
        elif key in {"min_hours_between_posts","min_post_gap_minutes"}:
            minutes=max(1,int(float(value)))
            await set_setting(db,"min_post_gap_minutes",str(minutes))
            # Keep the legacy key only for backward compatibility; the UI reads minutes.
            await set_setting(db,"min_hours_between_posts",str(minutes/60))
        elif key=="ai_verify_mode":
            if value not in {"auto","always","off"}: raise ValueError("auto / always / off")
            await set_setting(db,key,value)
        elif key=="__publish_delay__":
            delay=max(0,min(10080,int(value)))
            row=await db.execute("SELECT article_id FROM publication_queue WHERE status='queued' ORDER BY score DESC,created_at ASC LIMIT 1")
            if not row: raise ValueError("صف انتشار خالی است")
            # برنامه‌ریزی دستی فقط همان اولین آیتم آماده را جابه‌جا می‌کند.
            when=(datetime.now(timezone.utc)+timedelta(minutes=delay)).isoformat()
            await db.execute("UPDATE publication_queue SET scheduled_at=? WHERE article_id=? AND status='queued'",[when,row[0]['article_id']])
        else:
            raise ValueError("setting not supported")
        await state.set_state(BotStates.idle)

        # Render the parent menu back into the original panel message.
        panel_id=data.get("panel_message_id")
        if panel_id:
            if parent=="auto_schedule":
                text,kb=await get_schedule_panel(db)
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode="HTML",reply_markup=kb)
            elif parent=="auto_quality":
                score=await get_setting(db,"min_content_score",str(DEFAULT_MIN_CONTENT_SCORE))
                pch=await get_setting(db,"editorial_prompt_channel","")
                par=await get_setting(db,"editorial_prompt_article","")
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,
                    text=(f"🧠 <b>کیفیت محتوا</b>\n\nحداقل امتیاز: <b>{html.escape(score)}</b>\n"
                          f"✍️ پرامپت کوتاه: <code>{html.escape(pch[:180])}</code>\n"
                          f"📝 پرامپت کامل: <code>{html.escape(par[:180])}</code>"),
                    parse_mode="HTML",reply_markup=quality_menu_kb())
            elif parent=="editorial_prompts":
                ch=await get_setting(db,'editorial_prompt_channel',''); ar=await get_setting(db,'editorial_prompt_article','')
                text=("✍️ <b>دستورهای محتوای تولید</b>\n\n"+f"📌 کوتاه: <code>{html.escape(ch[:260])}</code>\n"+f"📌 کامل: <code>{html.escape(ar[:260])}</code>")
                kb=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='✍️ ویرایش کوتاه',callback_data='set_editorial_prompt_channel')],[InlineKeyboardButton(text='📝 ویرایش کامل',callback_data='set_editorial_prompt_article')],[InlineKeyboardButton(text='♻️ پیش‌فرض',callback_data='editorial_prompts_reset')],[InlineKeyboardButton(text='🔙 کیفیت محتوا',callback_data='auto_quality')]])
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode='HTML',reply_markup=kb)
            elif parent=="quality_weights":
                labels=[("global","🌍 جهانی"),("technology","💻 فناوری"),("ai","🤖 AI"),("cyber","🔐 سایبری"),("education","📚 آموزش"),("iran","🇮🇷 ایران/فارسی"),("freshness","🆕 تازگی"),("source","✅ منبع"),("novelty","♻️ عدم تکرار")]
                text="🎯 <b>وزن معیارها</b>\n\n"+ "\n".join([f"{lab}: <b>{await get_setting(db,'weight_'+k,'10')}</b>" for k,lab in labels])
                rows=[[InlineKeyboardButton(text=lab,callback_data="weight_"+k)] for k,lab in labels]
                rows.append([InlineKeyboardButton(text="🔙 کیفیت محتوا",callback_data="auto_quality")])
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode="HTML",reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))
            elif parent.startswith("source_view_"):
                sid=int(parent.rsplit("_",1)[1]); await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text="✅ تنظیم منبع ذخیره شد.",reply_markup=get_admin_back_kb(parent))
            elif parent.startswith("provider_view_"):
                pid=int(parent.rsplit("_",1)[1]); await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text="✅ تنظیم مدل ذخیره شد.",reply_markup=get_admin_back_kb(parent))
            elif parent=="auto_channel":
                # The current parent for publication settings is the modern schedule panel.
                # Always render that same panel after saving; never return to the legacy row menu.
                text,kb=await get_schedule_panel(db)
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode="HTML",reply_markup=kb)
            else:
                target = parent if parent in {"auto_channel","auto_schedule","auto_quality","quality_weights","auto_providers","auto_sources","editorial_prompts"} else "admin_home"
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text="✅ ذخیره شد.",parse_mode="HTML",reply_markup=get_admin_back_kb(target))
        else:
            await message.answer("✅ ذخیره شد.",reply_markup=get_admin_menu())
    except Exception as e:
        await message.answer(f"❌ مقدار نامعتبر است: {html.escape(str(e))}",parse_mode="HTML",reply_markup=get_admin_back_kb(parent if parent else "admin_home"))


async def render_admin_home(call: CallbackQuery, db: D1Database):
    text=("🛠 <b>پنل مدیریت</b>\n<code>Build: "+BUILD_VERSION+"</code>\n\n"
          "اینجا بخش موردنظر را انتخاب کن.\nبرای سلامت، گزارش و انتشار وارد «اتوماسیون محتوا» شو.")
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=get_admin_menu()); await call.answer()


@router.callback_query(F.data == "admin_home")
async def admin_home(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID:
        await call.answer("دسترسی ندارید", show_alert=True); return
    await render_admin_home(call, db)


@router.callback_query(F.data == "admin_automation")
async def admin_automation(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    enabled = (await get_setting(db, 'automation_enabled', '0')) == '1'
    await call.message.edit_text(await automation_overview(db), parse_mode='HTML', reply_markup=automation_menu_kb(enabled))


@router.callback_query(F.data == "admin_ai")
async def admin_ai(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await auto_providers(call, db)


@router.callback_query(F.data == "admin_sources")
async def admin_sources(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await auto_sources(call, db)


@router.callback_query(F.data == "admin_publish")
async def admin_publish(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await render_channel_panel(call, db)

@router.callback_query(F.data == "admin_quality")
async def admin_quality(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await auto_quality(call, db)

@router.callback_query(F.data == "admin_monitor")
async def admin_monitor(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    users = (await db.execute("SELECT COUNT(*) c FROM users"))[0].get('c',0)
    posts = (await db.execute("SELECT COUNT(*) c FROM posts WHERE deleted=0"))[0].get('c',0)
    views = (await db.execute("SELECT COALESCE(SUM(views),0) s FROM posts"))[0].get('s',0)
    text = f"📊 <b>مرکز آمار هسته</b>\n\n👥 کاربران: {users}\n📝 محتوای هسته: {posts}\n👁 بازدید: {views}"
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔄 بروزرسانی', callback_data='admin_monitor')],[InlineKeyboardButton(text='🔙 پنل اصلی', callback_data='admin_home')]]))
    await call.answer()


@router.callback_query(F.data == "admin_stats")
async def admin_stats(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    users=(await db.execute("SELECT COUNT(*) c FROM users"))[0].get("c",0)
    posts=(await db.execute("SELECT COUNT(*) c FROM posts WHERE deleted=0"))[0].get("c",0)
    views=(await db.execute("SELECT COALESCE(SUM(views),0) s FROM posts"))[0].get("s",0)
    await call.message.edit_text(f"📊 <b>آمار کلی</b>\n\n👥 کاربران: {users}\n📝 محتوای فعال: {posts}\n👁 بازدید: {views}",parse_mode="HTML",reply_markup=get_admin_back_kb("admin_home"))
    await call.answer()

@router.callback_query(F.data == "admin_content")
async def admin_content(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.message.edit_text("📁 <b>مدیریت محتوای هسته</b>\n\nجستجو، مشاهده و حذف محتوا از آرشیو اصلی.", parse_mode='HTML', reply_markup=get_content_management_kb())
    await call.answer()


@router.callback_query(F.data == "admin_add_post")
async def admin_add_post(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await state.set_state(BotStates.waiting_post_content)
    await state.update_data(panel_message_id=call.message.message_id)
    await call.message.edit_text("📝 متن، تصویر، ویدیو یا سند پست را ارسال کن:", reply_markup=get_exit_menu())
    await call.answer()


@router.callback_query(F.data == "admin_broadcast")
async def admin_broadcast(call: CallbackQuery, state: FSMContext):
    if call.from_user.id != ADMIN_ID: return
    await state.set_state(BotStates.waiting_broadcast_content)
    await state.update_data(panel_message_id=call.message.message_id)
    await call.message.edit_text("📢 پیام همگانی را ارسال کن؛ قبل از ارسال نهایی یک مرحله تأیید می‌گیریم.", reply_markup=get_exit_menu())
    await call.answer()


@router.callback_query(F.data == "admin_user_mode")
async def admin_user_mode(call: CallbackQuery, state: FSMContext):
    await state.update_data(admin_mode='user')
    await call.message.edit_text("👤 حالت کاربری فعال شد.", reply_markup=get_main_menu())
    await call.answer()


async def render_channel_panel(call: CallbackQuery, db: D1Database):
    channel_id = await get_channel_id(db)
    channel_username = await get_setting(db, 'channel_username', '')
    if channel_username:
        shown = html.escape(channel_username)
    elif channel_id:
        shown = '✅ کانال خصوصی تنظیم شده (شناسه عددی مخفی)'
    else:
        shown = '⛔ هنوز تنظیم نشده'
    enabled = (await get_setting(db, 'automation_enabled', '0')) == '1'
    max_daily=await get_setting(db,'max_daily_posts',str(DEFAULT_MAX_DAILY_POSTS))
    gap=await get_setting(db,'min_post_gap_minutes',str(DEFAULT_MIN_POST_GAP_MINUTES))
    src_interval=await get_setting(db,'default_source_interval',str(DEFAULT_SOURCE_INTERVAL_MINUTES))
    est=await next_publication_estimate(db)
    if est['minutes']<=0: nxt='آماده انتشار طبق برنامه'
    elif est['minutes']<60: nxt=f"حدود {est['minutes']} دقیقه دیگر"
    else: nxt=f"حدود {est['minutes']//60} ساعت و {est['minutes']%60} دقیقه دیگر"
    text=("📢 <b>انتشار و زمان‌بندی</b>\n\n"
          f"📢 کانال: <b>{shown}</b>\n"
          f"🤖 اتوماسیون: <b>{'🟢 فعال' if enabled else '🔴 خاموش'}</b>\n\n"
          f"🔢 سقف روزانه: <b>{max_daily}</b>\n"
          f"⏱ فاصله انتشار: <b>{format_duration_minutes(gap)}</b>\n"
          f"🌐 فاصله بررسی منابع: <b>{src_interval} دقیقه</b>\n"
          f"🕐 نوبت بعدی: <b>{nxt}</b>\n\n"
          "مدیر فقط فاصله‌ها را تعیین می‌کند؛ نوبت هر محتوا خودکار محاسبه می‌شود.")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='📢 تنظیم/تغییر کانال',callback_data='auto_channel_set')],
        [InlineKeyboardButton(text='🔢 سقف پست روزانه',callback_data='set_max_daily'),InlineKeyboardButton(text='⏱ فاصله انتشار',callback_data='set_min_gap')],
        [InlineKeyboardButton(text='🌐 فاصله بررسی منابع',callback_data='set_default_interval')],
        [InlineKeyboardButton(text='🚀 همین حالا منتشر کن',callback_data='publish_now'),InlineKeyboardButton(text='🧪 تست کانال',callback_data='channel_test')],
        [InlineKeyboardButton(text='🔙 اتوماسیون محتوا',callback_data='auto_back')]
    ])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=kb)

@router.callback_query(F.data == "auto_channel")
async def auto_channel(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    await render_channel_panel(call, db)

@router.callback_query(F.data == "auto_channel_set")
async def auto_channel_set(call: CallbackQuery, state: FSMContext, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    await state.set_state(BotStates.admin_channel_input)
    await state.update_data(panel_message_id=call.message.message_id)
    await call.message.edit_text(
        '📢 <b>تنظیم کانال انتشار</b>\n\n'
        'آیدی کانال یا @username را ارسال کن.\n'
        'مثال: <code>@my_channel</code> یا <code>-1001234567890</code>\n\n'
        'ربات باید در کانال ادمین باشد و اجازه انتشار پیام داشته باشد.',
        parse_mode='HTML', reply_markup=get_exit_menu())

@router.callback_query(F.data == "publish_now")
async def publish_now(call: CallbackQuery, db:D1Database, bot:Bot):
    if call.from_user.id!=ADMIN_ID: return
    await call.answer("🚀 در حال انتشار…")
    try:
        ok=await publish_next_article(db,bot,force=True)
        msg="✅ اولین محتوای آماده همین حالا منتشر شد." if ok else "⏸ محتوای آماده‌ای برای انتشار نیست یا سقف روزانه پر شده است."
    except Exception as e:
        msg="❌ انتشار دستی شکست خورد:\n"+html.escape(str(e)[:1200])
    await call.message.edit_text(msg,parse_mode="HTML",reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 انتشار و زمان‌بندی",callback_data="auto_channel")]]))

@router.callback_query(F.data == "publish_schedule")
async def publish_schedule(call:CallbackQuery,state:FSMContext):
    if call.from_user.id!=ADMIN_ID:return
    await state.set_state(BotStates.admin_automation_setting)
    await state.update_data(automation_setting_key="__publish_delay__",panel_message_id=call.message.message_id,parent_callback="auto_channel")
    await call.message.edit_text("⏱ <b>زمان‌بندی انتشار</b>\n\nچند دقیقه دیگر منتشر شود؟\n\n0 = همین حالا\n2 = دو دقیقه دیگر\n10 = ده دقیقه دیگر\nمثلاً 30",parse_mode="HTML",reply_markup=get_exit_menu()); await call.answer()

@router.callback_query(F.data == "channel_test")
async def channel_test(call: CallbackQuery, db: D1Database, bot: Bot):
    if call.from_user.id != ADMIN_ID: return
    channel_id = await get_channel_id(db)
    if not channel_id:
        await call.answer('کانال هنوز تنظیم نشده است.', show_alert=True); return
    try:
        chat = await bot.get_chat(channel_id)
        me = await bot.get_me()
        member = await bot.get_chat_member(chat.id, me.id)
        status = str(getattr(member, 'status', ''))
        if status not in {'administrator', 'creator'}:
            raise RuntimeError('ربات در کانال ادمین نیست.')
        perms = getattr(member, 'can_post_messages', None)
        if perms is False:
            raise RuntimeError('اجازه انتشار پیام برای ربات فعال نیست.')
        label = '@' + chat.username if getattr(chat, 'username', None) else 'کانال خصوصی'
        await call.message.edit_text(f'✅ <b>کانال سالم است</b>\n\n📢 {html.escape(label)}\n👤 وضعیت ربات: {html.escape(status)}\n📝 اجازه انتشار: ✅', parse_mode='HTML', reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔙 کانال و انتشار', callback_data='auto_channel')]]))
    except Exception as e:
        await call.message.edit_text(f'❌ <b>تست کانال ناموفق بود</b>\n\n{html.escape(str(e)[:1000])}', parse_mode='HTML', reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔙 کانال و انتشار', callback_data='auto_channel')]]))
    await call.answer()

@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_channel_input))
async def admin_channel_input(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    raw = (message.text or '').strip()
    if not raw:
        return
    if raw.startswith('https://t.me/') or raw.startswith('http://t.me/'):
        raw = '@' + raw.rstrip('/').split('/')[-1]
    try:
        chat = await bot.get_chat(raw)
        me = await bot.get_me()
        member = await bot.get_chat_member(chat.id, me.id)
        status = str(getattr(member, 'status', ''))
        if status not in {'administrator', 'creator'}:
            await message.answer('❌ ربات در این کانال ادمین نیست یا دسترسی کافی ندارد. ورودی قبلی باقی است؛ دوباره آیدی/username را بفرست.',reply_markup=get_exit_menu())
            return
        await set_setting(db, 'channel_id', str(chat.id))
        await set_setting(db, 'channel_username', '@' + chat.username if getattr(chat, 'username', None) else '')
        await state.set_state(BotStates.idle)
        label = '@' + chat.username if getattr(chat, 'username', None) else 'کانال خصوصی تنظیم شد'
        panel_id=(await state.get_data()).get('panel_message_id')
        text=f"✅ <b>کانال با موفقیت تنظیم شد.</b>\n\n📢 {html.escape(label)}\n🆔 <code>{chat.id}</code>"
        if panel_id:
            try:
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🧪 تست کانال',callback_data='channel_test')],[InlineKeyboardButton(text='🔙 کانال و انتشار',callback_data='auto_channel')]]))
            except Exception:
                await message.answer(text,parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔙 کانال و انتشار',callback_data='auto_channel')]]))
        else:
            await message.answer(text,parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔙 کانال و انتشار',callback_data='auto_channel')]]))
    except Exception as e:
        await message.answer(f"❌ نتوانستم کانال را تأیید کنم:\n{html.escape(str(e)[:1000])}\n\nآیدی/@username را دوباره بفرست.",reply_markup=get_exit_menu())


@router.callback_query(F.data == "cancel_state")
async def cancel_state(call: CallbackQuery, state: FSMContext, db: D1Database):
    data=await state.get_data(); parent=data.get("parent_callback") or "admin_home"
    await state.set_state(BotStates.idle)
    await state.update_data(panel_message_id=None,provider_base_url=None,provider_token=None,provider_edit_id=None)
    try:
        if parent=="auto_schedule": await auto_schedule(call,db); return
        if parent=="auto_quality": await auto_quality(call,db); return
        if parent=="quality_weights": await quality_weights(call,db); return
        if parent=="auto_channel": await render_channel_panel(call,db); return
        if parent=="auto_providers": await auto_providers(call,db); return
        if parent.startswith("provider_view_"): await provider_view(call,db); return
        if parent.startswith("source_view_"): await source_view(call,db); return
        if parent=="auto_sources": await auto_sources(call,db); return
    except Exception:
        pass
    if call.from_user.id==ADMIN_ID:
        await render_admin_home(call,db)
    else:
        await call.message.edit_text("لغو شد.",reply_markup=get_main_menu()); await call.answer("لغو شد")

@router.callback_query(F.data == "user_home")
async def user_home(call: CallbackQuery):
    await call.message.edit_text("🏠 منوی اصلی کاربر\n\nچه کاری می‌خواهی انجام بدهی؟", reply_markup=get_main_menu())
    await call.answer()


@router.callback_query(F.data == "user_saves")
async def user_saves(call: CallbackQuery, db: D1Database):
    await call.message.edit_text("💾 <b>ذخیره‌های من</b>\n\nهمه مطالب ذخیره‌شده در یک آرشیو یکپارچه قرار دارند.\nیک پوشه را انتخاب کن:", parse_mode="HTML", reply_markup=unified_saved_kb("all"))
    await call.answer()

async def _render_unified_saves(call: CallbackQuery, db: D1Database, folder: str = "all"):
    uid=call.from_user.id
    folder_clause=""; base=[uid]
    if folder != "all": folder_clause=" AND s.folder=?"; base.append(folder)
    posts=await db.execute(f"SELECT p.id,p.text,p.media_type,s.folder FROM user_content_saves s JOIN posts p ON p.id=s.content_id AND s.content_type='post' WHERE s.user_id=? AND p.deleted=0{folder_clause} ORDER BY s.rowid DESC LIMIT 50",base)
    articles=await db.execute(f"SELECT a.id,a.title,a.deep_token,s.folder FROM user_content_saves s JOIN articles a ON a.id=s.content_id AND s.content_type='article' WHERE s.user_id=? AND a.status IN ('ready','published','test'){folder_clause} ORDER BY s.rowid DESC LIMIT 50",base)
    items=[]
    for r in posts:
        txt=strip_html_text(r.get('text') or '').strip().replace('\n',' ')
        items.append((int(r.get('id') or 0), 'post', r.get('folder') or '', txt[:80], f"https://t.me/{BOT_USERNAME_RUNTIME or BOT_USERNAME.lstrip('@')}?start={int(r.get('id') or 0)}"))
    for r in articles:
        title=strip_html_text(r.get('title') or '').strip().replace('\n',' ')
        label=title[:90]
        items.append((int(r.get('id') or 0), 'article', r.get('folder') or '', label, f"https://t.me/{BOT_USERNAME_RUNTIME or BOT_USERNAME.lstrip('@')}?start=article_{r.get('deep_token','')}"))
    items.sort(key=lambda x:x[0], reverse=True)
    items=items[:30]
    label='همه' if folder=='all' else FOLDER_NAMES.get(folder,folder)
    if not items:
        text=f"💾 <b>ذخیره‌های من</b>\n\n📂 پوشه: <b>{html.escape(label)}</b>\n\nفعلاً مطلبی در این بخش ذخیره نکردی."
    else:
        lines=[f"💾 <b>ذخیره‌های من</b> — {html.escape(label)}\n"]
        for i,(_,ctype,_,title,url) in enumerate(items,1):
            icon='📰' if ctype=='article' else '📌'
            lines.append(f"{i}. {icon} <a href=\"{html.escape(url,quote=True)}\">{html.escape(title or 'مطلب بدون عنوان')}</a>")
        text='\n'.join(lines)
    await call.message.edit_text(text,parse_mode='HTML',disable_web_page_preview=True,reply_markup=unified_saved_kb(folder))
    await call.answer()

@router.callback_query(F.data.startswith("saved_folder_"))
async def saved_folder(call: CallbackQuery, db: D1Database):
    folder=call.data.split("saved_folder_",1)[1] or 'all'
    await _render_unified_saves(call,db,folder)

@router.callback_query(F.data == "user_profile")
async def user_profile(call: CallbackQuery, db: D1Database):
    uid = call.from_user.id
    rows = await db.execute("SELECT joined_at, role FROM users WHERE id=?", [uid])
    joined = rows[0].get('joined_at') if rows else ''
    role = rows[0].get('role') if rows else 'user'
    try:
        joined_dt=datetime.fromisoformat(str(joined).replace('Z','+00:00'))
        if joined_dt.tzinfo is None: joined_dt=joined_dt.replace(tzinfo=timezone.utc)
        days=max(0,(datetime.now(timezone.utc)-joined_dt).days)
    except Exception:
        days=0
    legacy_saves=(await db.execute("SELECT COUNT(*) c FROM user_content_saves WHERE user_id=?",[uid]))[0].get('c',0)
    article_saves=0
    likes_legacy=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE user_id=? AND vote_type='like'",[uid]))[0].get('c',0)
    likes_article=0
    dislikes_legacy=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE user_id=? AND vote_type='dislike'",[uid]))[0].get('c',0)
    dislikes_article=0
    total_saves=legacy_saves+article_saves; total_likes=likes_legacy+likes_article; total_dislikes=dislikes_legacy+dislikes_article
    role_display='مدیر 🌟' if role=='admin' else 'کاربر 🟢'
    name=html.escape(call.from_user.first_name or 'دوست عزیز')
    text=(f"👤 <b>پروفایل {name}</b>\n\n"
          f"🗓 <b>عضویت:</b> {days} روز پیش\n"
          f"🔰 <b>نوع حساب:</b> {role_display}\n\n"
          f"💾 <b>ذخیره‌ها:</b> {total_saves}\n"
          f"👍 <b>لایک‌ها:</b> {total_likes}\n"
          f"👎 <b>دیس‌لایک‌ها:</b> {total_dislikes}\n\n"
          "✨ اینجا آمار ساده و کاربردی فعالیتت را می‌بینی.")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💾 ذخیره‌های من",callback_data="user_saves")],
        [InlineKeyboardButton(text="🔙 منوی اصلی",callback_data="user_home")]
    ])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=kb)
    await call.answer()


@router.callback_query(F.data == "user_help")
async def user_help(call: CallbackQuery):
    await call.message.edit_text("❓ <b>راهنما</b>\n\n/start • شروع\n/help • راهنما\n/man • تماس با مدیر", parse_mode="HTML", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 منوی اصلی", callback_data="user_home")]]))
    await call.answer()


@router.callback_query(F.data == "auto_on")
async def auto_on(call: CallbackQuery, db: D1Database):
    await call.answer("اتوماسیون فعال شد")
    await set_setting(db, "automation_enabled", "1")
    await call.message.edit_text(await automation_overview(db), parse_mode='HTML', reply_markup=automation_menu_kb(True))


@router.callback_query(F.data == "auto_off")
async def auto_off(call: CallbackQuery, db: D1Database):
    await call.answer("اتوماسیون خاموش شد")
    await set_setting(db, "automation_enabled", "0")
    await call.message.edit_text(await automation_overview(db), parse_mode='HTML', reply_markup=automation_menu_kb(False))


@router.callback_query(F.data == "auto_back")
async def auto_back(call: CallbackQuery, db: D1Database):
    await call.answer()
    enabled = (await get_setting(db, "automation_enabled", "0")) == "1"
    await call.message.edit_text(await automation_overview(db), parse_mode='HTML', reply_markup=automation_menu_kb(enabled))


@router.callback_query(F.data == "auto_report")
async def auto_report(call:CallbackQuery,db:D1Database):
    if call.from_user.id!=ADMIN_ID:return
    await call.answer()
    await call.message.edit_text(await automation_report(db),parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 بروزرسانی",callback_data="auto_report")],
        [InlineKeyboardButton(text="🔙 اتوماسیون محتوا",callback_data="auto_back")]]))


@router.callback_query(F.data == "auto_sources")
async def auto_sources(call: CallbackQuery, db: D1Database):
    await call.answer()
    rows = await db.execute("SELECT * FROM sources ORDER BY priority ASC, id ASC")
    text = "🌐 منابع محتوا\n\n🟢 فعال = بررسی می‌شود\n🔴 خاموش = بررسی نمی‌شود\n📌 اولویت کمتر = زودتر بررسی\n\n"
    if not rows:
        text += "هنوز منبع اضافه نشده است."
    else:
        for s in rows[:20]:
            text += f"{'🟢' if s.get('enabled') else '🔴'} #{s.get('id')} {s.get('name')} | {s.get('interval_minutes')}m | {s.get('category')}\n"
    await call.message.edit_text(text, reply_markup=source_list_kb(rows))


@router.callback_query(F.data == "auto_add_source")
async def auto_add_source(call: CallbackQuery, state: FSMContext):
    await state.set_state(BotStates.admin_add_source)
    await state.update_data(panel_message_id=call.message.message_id)
    await call.message.edit_text("🌐 URL سایت را بفرست:\n\nمثال: https://example.com", reply_markup=get_exit_menu())
    await call.answer()


@router.callback_query(F.data.startswith("source_view_"))
async def source_view(call: CallbackQuery, db: D1Database):
    await call.answer()
    source_id = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT * FROM sources WHERE id=?", [source_id])
    if not rows:
        await call.answer("منبع یافت نشد", show_alert=True)
        return
    s = rows[0]
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 تست و بررسی اکنون", callback_data=f"source_test_{source_id}")],
        [InlineKeyboardButton(text="🔢 تغییر اولویت", callback_data=f"source_priority_{source_id}")],
        [InlineKeyboardButton(text="⏱ تنظیم فاصله", callback_data=f"source_interval_{source_id}")],
        [InlineKeyboardButton(text="⏸ غیرفعال" if s.get("enabled") else "▶️ فعال", callback_data=f"source_toggle_{source_id}")],
        [InlineKeyboardButton(text="🗑 حذف", callback_data=f"source_delete_{source_id}")],
        [InlineKeyboardButton(text="🔙 منابع", callback_data="auto_sources")]
    ])
    text = f"🌐 #{s['id']} {s.get('name')}\n\nURL: {s.get('url')}\nدسته: {s.get('category')}\nفاصله: {s.get('interval_minutes')} دقیقه\nاولویت: {s.get('priority')}\nآخرین بررسی: {s.get('last_checked_at') or '-'}\nخطا: {s.get('last_error') or '-'}"
    await call.message.edit_text(text, reply_markup=kb)


@router.callback_query(F.data.startswith("source_toggle_"))
async def source_toggle(call: CallbackQuery, db: D1Database):
    source_id = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT enabled FROM sources WHERE id=?", [source_id])
    if rows:
        await db.execute("UPDATE sources SET enabled=? WHERE id=?", [0 if rows[0].get("enabled") else 1, source_id])
    await source_view(call, db)


@router.callback_query(F.data.startswith("source_delete_"))
async def source_delete(call: CallbackQuery, db: D1Database):
    source_id = int(call.data.split("_")[-1])
    await db.execute("DELETE FROM sources WHERE id=?", [source_id])
    await db.execute("DELETE FROM source_items WHERE source_id=?", [source_id])
    rows = await db.execute("SELECT * FROM sources ORDER BY priority ASC, id ASC")
    await call.message.edit_text("✅ منبع حذف شد.", reply_markup=source_list_kb(rows))
    await call.answer("حذف شد")


@router.callback_query(F.data.startswith("source_priority_"))
async def source_priority(call: CallbackQuery, state: FSMContext):
    sid=int(call.data.split("_")[-1])
    await state.set_state(BotStates.admin_automation_setting)
    await state.update_data(automation_setting_key="__source_priority__",source_priority_id=sid,parent_callback=f"source_view_{sid}",panel_message_id=call.message.message_id)
    await call.message.edit_text("🔢 اولویت منبع را عددی بفرست.\nعدد کمتر = اولویت بالاتر.",reply_markup=get_exit_menu())
    await call.answer()

@router.callback_query(F.data.startswith("source_interval_"))
async def source_interval(call: CallbackQuery, state: FSMContext):
    source_id = int(call.data.split("_")[-1])
    await state.update_data(source_interval_id=source_id,panel_message_id=call.message.message_id,parent_callback=f"source_view_{source_id}")
    await state.set_state(BotStates.admin_automation_setting)
    await state.update_data(automation_setting_key="__source_interval__")
    await call.message.edit_text("فاصله بررسی را به دقیقه بفرست. مثلاً 15", reply_markup=get_exit_menu())


@router.callback_query(F.data.startswith("source_test_"))
async def source_test(call: CallbackQuery, db: D1Database):
    source_id = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT * FROM sources WHERE id=?", [source_id])
    if not rows:
        await call.answer("منبع یافت نشد", show_alert=True); return
    await call.answer("در حال بررسی...", show_alert=True)
    # برای تست دستی، از یک provider واقعی استفاده می‌کنیم ولی در DB فقط state منبع ثبت می‌شود.
    try:
        diag=await discover_source_items(rows[0],return_diagnostics=True,use_sitemap=False)
        raw_items=list(diag.get("items") or [])
        now=datetime.now(timezone.utc)
        fresh_items, fresh_diag, _, _ = select_latest_fresh_items(raw_items, now=now)
        titles=[strip_html_text(str(x.get("title") or ""))[:90] for x in fresh_items[:3] if x.get("title")]
        method=str(diag.get('method') or 'none')
        if raw_items:
            marker='🟢' if fresh_items else '🟡'
            text=(f"{marker} <b>تست واقعی منبع</b>\n\n"
                  f"روش: <code>{html.escape(method)}</code>\n"
                  f"پیدا شد: <b>{len(raw_items)}</b>\n"
                  f"تازه در ۲۴ ساعت: <b>{len(fresh_items)}</b>")
            if titles:
                text += "\n\n📰 <b>نمونه:</b>\n" + "\n".join(f"• {html.escape(t)}" for t in titles)
            if fresh_diag:
                text += "\n\nℹ️ " + html.escape(fresh_diag[-1][:500])
        else:
            details='؛ '.join((diag.get('diagnostics') or [])[-4:]) or diag.get('error') or 'بدون نتیجه'
            text="🔴 <b>تست واقعی منبع</b>\n\n"+html.escape(str(details)[:1800])
        await call.message.edit_text(text,parse_mode='HTML',reply_markup=get_admin_back_kb(f"source_view_{source_id}"))
    except Exception as e:
        await db.execute("UPDATE sources SET last_error=? WHERE id=?", [str(e)[:1000], source_id])
        await call.message.edit_text(f"❌ تست منبع ناموفق:\n{html.escape(str(e))}",reply_markup=get_admin_back_kb(f"source_view_{source_id}"))


@router.callback_query(F.data == "auto_providers")
async def auto_providers(call: CallbackQuery, db: D1Database):
    rows = await db.execute("SELECT id,name,base_url,model_name,priority,enabled,web_enabled,status,last_error,last_latency_ms FROM ai_providers ORDER BY priority ASC, id ASC")
    text = "🤖 <b>مدل‌های هوش مصنوعی</b>\n\nهر مدل را باز کن تا ویرایش، تست، فعال/غیرفعال، اولویت‌بندی یا حذفش کنی.\n\n"
    if not rows:
        text += "هیچ Provider فعالی وجود ندارد."
    else:
        for p in rows:
            text += f"{'🟢' if p.get('enabled') else '🔴'} #{p['id']} {p.get('name')} | {p.get('model_name')} | priority={p.get('priority')}\n"
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=provider_list_kb(rows))


@router.callback_query(F.data == "auto_add_provider")
async def auto_add_provider(call: CallbackQuery, state: FSMContext):
    await state.set_state(BotStates.admin_add_provider)
    await state.update_data(provider_draft={},parent_callback="auto_providers",panel_message_id=call.message.message_id)
    await call.message.edit_text(
        "🤖 افزودن مدل جدید\n\n"
        "مرحله ۱ از ۳\n"
        "🔗 Base URL خود را ارسال کنید.\n\n"
        "می‌تواند endpoint کامل /chat/completions باشد یا Base URL استاندارد مثل /v1.",
        reply_markup=get_exit_menu()
    )
    await call.answer()


@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_add_provider))
async def provider_base_input(message: Message, state: FSMContext, bot: Bot):
    base_url = (message.text or '').strip()
    if not re.match(r'^https?://', base_url, re.I):
        await message.answer("❌ Base URL معتبر نیست. باید با http:// یا https:// شروع شود.",reply_markup=get_exit_menu())
        return
    data = await state.get_data()
    panel_id = data.get('panel_message_id')
    await state.update_data(provider_base_url=base_url)
    await state.set_state(BotStates.admin_provider_token)
    text = "🤖 افزودن مدل جدید\n\nمرحله ۲ از ۳\n🔐 توکن/API Key این مدل را ارسال کنید:" 
    if panel_id:
        try:
            await bot.edit_message_text(chat_id=message.chat.id, message_id=panel_id, text=text, reply_markup=get_exit_menu())
            return
        except Exception:
            pass
    await message.answer(text, reply_markup=get_exit_menu())


@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_provider_token))
async def provider_token_input(message: Message, state: FSMContext, bot: Bot):
    token = (message.text or '').strip()
    if len(token) < 4:
        await message.answer("❌ توکن خیلی کوتاه است. دوباره ارسال کنید.",reply_markup=get_exit_menu())
        return
    data = await state.get_data()
    panel_id = data.get('panel_message_id')
    await state.update_data(provider_token=token)
    await state.set_state(BotStates.admin_provider_model)
    text = "🤖 افزودن مدل جدید\n\nمرحله ۳ از ۳\n🧩 نام دقیق Model را دقیقاً همان‌طور که Provider می‌شناسد ارسال کنید:" 
    if panel_id:
        try:
            await bot.edit_message_text(chat_id=message.chat.id, message_id=panel_id, text=text, reply_markup=get_exit_menu())
            return
        except Exception:
            pass
    await message.answer(text, reply_markup=get_exit_menu())


@router.message(F.chat.id == ADMIN_ID, StateFilter(BotStates.admin_provider_model))
async def provider_model_input(message: Message, state: FSMContext, db: D1Database, bot: Bot):
    model = (message.text or '').strip()
    data = await state.get_data()
    base_url = data.get('provider_base_url','')
    token = data.get('provider_token','')
    if not model:
        await message.answer("❌ نام مدل خالی است.",reply_markup=get_exit_menu())
        return
    panel_id = data.get('panel_message_id')
    if panel_id:
        try:
            await bot.edit_message_text(chat_id=message.chat.id, message_id=panel_id, text="🔎 مرحله ۱: بررسی endpoint و نام مدل...\n🧪 مرحله ۲: ارسال یک درخواست واقعی TEST_OK به خود مدل...\n⏳ نتیجه بعد از دریافت پاسخ نمایش داده می‌شود.")
        except Exception:
            await message.answer("🔎 در حال بررسی endpoint و نام مدل...\n🧪 سپس یک درخواست واقعی TEST_OK به مدل ارسال می‌شود...")
    else:
        await message.answer("🧪 در حال تست اتصال و نام دقیق مدل...")
    tester = AIProviderManager(db)
    try:
        result = await tester.test_provider_values(base_url, token, model)
    finally:
        await tester.close()
    if not result.get('ok'):
        parent=data.get("parent_callback","auto_providers")
        panel_id=data.get("panel_message_id")
        await state.set_state(BotStates.idle)
        await state.update_data(provider_base_url=None, provider_token=None, provider_edit_id=None)
        error_text=("❌ این مدل در تست اولیه قبول نشد.\n\n"
            f"HTTP/API: {html.escape(str(result.get('error','unknown'))[:1000])}\n\n"
            "هیچ چیزی ذخیره نشد. این بار واقعاً یک POST آزمایشی به مدل ارسال شد.\n\n"
            "اگر Gemini است، Base URL رسمی OpenAI-compatible: https://generativelanguage.googleapis.com/v1beta/openai/\n"
            "یا Base URL بومی: https://generativelanguage.googleapis.com/v1beta\n"
            "نام مدل باید دقیقاً مطابق مدل در Google AI Studio باشد.")
        kb = provider_list_kb(await db.execute("SELECT id,name,base_url,model_name,priority,enabled,web_enabled,status,last_error,last_latency_ms FROM ai_providers ORDER BY priority ASC,id ASC")) if parent=="auto_providers" else get_admin_back_kb(parent)
        if panel_id:
            try:
                await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=error_text,parse_mode='HTML',reply_markup=kb)
            except Exception:
                await message.answer(error_text,parse_mode='HTML',reply_markup=kb)
        else:
            await message.answer(error_text,parse_mode='HTML',reply_markup=kb)
        return
    now = datetime.now(timezone.utc).isoformat()
    host = urllib.parse.urlsplit(base_url).netloc or 'provider'
    name = f"{model[:80]} | {host[:30]}"[:120]
    edit_id = data.get('provider_edit_id')
    if edit_id:
        # در ویرایش، اولویت و وضعیت فعال قبلی حفظ می‌شود؛ فقط مشخصات اتصال عوض می‌شوند.
        old = await db.execute("SELECT priority,enabled,created_at FROM ai_providers WHERE id=?", [int(edit_id)])
        priority = int(old[0].get('priority') or 10) if old else 10
        await db.execute(
            "UPDATE ai_providers SET name=?, base_url=?, encrypted_api_key=?, model_name=?, updated_at=?, status='healthy', last_error=NULL, cooldown_until=NULL, last_checked_at=?, last_latency_ms=?, consecutive_failures=0 WHERE id=?",
            [name, base_url, encrypt_secret(token), model, now, now, result.get('latency_ms',0), int(edit_id)])
        action_text = f"✏️ مدل #{edit_id} با موفقیت ویرایش و تست شد."
    else:
        count = await db.execute("SELECT COALESCE(MAX(priority),0) AS p FROM ai_providers")
        priority = int(count[0].get('p') or 0) + 10 if count else 10
        await db.execute("INSERT INTO ai_providers(name, base_url, encrypted_api_key, model_name, priority, enabled, web_enabled, created_at, updated_at, status, last_checked_at, last_latency_ms, consecutive_failures) VALUES(?, ?, ?, ?, ?, 1, 0, ?, ?, 'healthy', ?, ?, 0)", [name, base_url, encrypt_secret(token), model, priority, now, now, now, result.get('latency_ms',0)])
        action_text = "➕ مدل جدید با موفقیت اضافه و تست شد."
    await state.set_state(BotStates.idle)
    await state.update_data(provider_base_url=None, provider_token=None, provider_edit_id=None, panel_message_id=None)
    rows = await db.execute("SELECT id,name,base_url,model_name,priority,enabled,web_enabled,status,last_error,last_latency_ms FROM ai_providers ORDER BY priority ASC, id ASC")
    parent=data.get("parent_callback","auto_providers")
    panel_id=data.get("panel_message_id")
    text=f"✅ {action_text}\n\n🤖 Model: <code>{html.escape(model)}</code>\n🔌 Protocol: <code>{html.escape(str(result.get('protocol','auto')))}</code>\n⚡ زمان پاسخ تست واقعی: {result.get('latency_ms',0)}ms\n🧪 پاسخ مدل: <code>{html.escape(str(result.get('preview','TEST_OK'))[:120])}</code>\n🔢 اولویت: {priority}"
    if panel_id:
        try:
            await bot.edit_message_text(chat_id=message.chat.id,message_id=panel_id,text=text,parse_mode='HTML',reply_markup=provider_list_kb(rows) if parent=="auto_providers" else get_admin_back_kb(parent))
        except Exception:
            await message.answer(text,parse_mode='HTML',reply_markup=provider_list_kb(rows))
    else:
        await message.answer(text,parse_mode='HTML',reply_markup=provider_list_kb(rows))


@router.callback_query(F.data.startswith("provider_view_"))
async def provider_view(call: CallbackQuery, db: D1Database):
    await call.answer()
    pid = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT id,name,base_url,model_name,priority,enabled,web_enabled,status,last_error,last_latency_ms,cooldown_until FROM ai_providers WHERE id=?", [pid])
    if not rows:
        await call.answer("Provider یافت نشد", show_alert=True); return
    p = rows[0]
    status = p.get('status') or 'unknown'
    status_text = {'healthy':'🟢 سالم','invalid':'🔴 تنظیمات/مدل نامعتبر','cooldown':'🟡 موقتاً در انتظار','unknown':'⚪ تست نشده'}.get(status,status)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✏️ ویرایش مدل", callback_data=f"provider_edit_{pid}"), InlineKeyboardButton(text="🧪 تست اتصال", callback_data=f"provider_test_{pid}")],
        [InlineKeyboardButton(text="🔢 تغییر اولویت", callback_data=f"provider_priority_{pid}"), InlineKeyboardButton(text="⏸ خاموش" if p.get('enabled') else "▶️ فعال", callback_data=f"provider_toggle_{pid}")],
        [InlineKeyboardButton(text="🌐 Web Scout: خاموش" if not p.get('web_enabled') else "🌐 Web Scout: روشن", callback_data=f"provider_web_toggle_{pid}")],
        [InlineKeyboardButton(text="🗑 حذف مدل", callback_data=f"provider_delete_{pid}" )],
        [InlineKeyboardButton(text="🔙 فهرست مدل‌ها", callback_data="auto_providers")]
    ])
    text = (f"🤖 مدل #{p['id']}\n\nModel: <code>{html.escape(str(p.get('model_name')))}</code>\n"
            f"Base URL: <code>{html.escape(str(p.get('base_url')))}</code>\n"
            f"اولویت: {p.get('priority')}\nWeb Scout: {'🟢 روشن' if p.get('web_enabled') else '⚪ خاموش'}\nوضعیت: {status_text}\n"
            f"Latency: {p.get('last_latency_ms') or 0}ms\n"
            f"آخرین خطا: {html.escape(str(p.get('last_error') or '-'))[:500]}")
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=kb)


@router.callback_query(F.data.startswith("provider_web_toggle_"))
async def provider_web_toggle(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    pid=int(call.data.rsplit("_",1)[-1])
    rows=await db.execute("SELECT web_enabled FROM ai_providers WHERE id=?",[pid])
    if not rows:
        await call.answer("مدل پیدا نشد",show_alert=True); return
    new_value=0 if int(rows[0].get("web_enabled") or 0) else 1
    await db.execute("UPDATE ai_providers SET web_enabled=?,updated_at=? WHERE id=?",[new_value,datetime.now(timezone.utc).isoformat(),pid])
    await call.answer("🌐 Web Scout روشن شد" if new_value else "🌐 Web Scout خاموش شد")
    await provider_view(call,db)

@router.callback_query(F.data == "provider_help")
async def provider_help(call: CallbackQuery):
    await call.answer()
    text = ("🤖 <b>راهنمای مدل‌های هوش مصنوعی</b>\n\n"
            "برای افزودن هر مدل فقط سه چیز لازم است:\n"
            "1️⃣ Base URL\n2️⃣ Token / API Key\n3️⃣ نام دقیق Model\n\n"
            "ربات قبل از ذخیره یک درخواست واقعی آزمایشی می‌فرستد. فقط مدل‌هایی که تستشان موفق باشد ذخیره می‌شوند.\n\n"
            "🔢 عدد اولویت کمتر = اولویت بالاتر\n"
            "🌐 Web Scout فقط برای مدل‌هایی است که واقعاً دسترسی وب/URL دارند؛ روشن کردن این گزینه به‌تنهایی قابلیت وب به API اضافه نمی‌کند.\n"
            "🟡 خطاهای موقت مثل 429/503 باعث cooldown می‌شوند و مدل «خراب» اعلام نمی‌شود.\n"
            "🔴 خطاهایی مثل 404/401/403 به‌عنوان مشکل تنظیمات علامت‌گذاری می‌شوند.\n\n"
            "از صفحه هر مدل می‌توانی آن را ویرایش، تست، فعال/غیرفعال، اولویت‌بندی یا حذف کنی.\n\n"
            "🟦 Gemini / Google AI Studio:\n"
            "OpenAI-compatible Base URL: https://generativelanguage.googleapis.com/v1beta/openai/\n"
            "یا Native Base URL: https://generativelanguage.googleapis.com/v1beta\n"
            "Token همان Gemini API Key است و Model باید دقیقاً نام مدل باشد؛ مثلاً gemini-3.6-flash.\n\n"
            "ربات در افزودن مدل، اول endpoint را بررسی می‌کند و بعد واقعاً TEST_OK را به مدل می‌فرستد؛ اگر Google باشد هر دو مسیر Native و OpenAI-compatible را در صورت نیاز امتحان می‌کند.")
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 فهرست مدل‌ها", callback_data="auto_providers")]]))


@router.callback_query(F.data.startswith("provider_edit_"))
async def provider_edit(call: CallbackQuery, state: FSMContext, db: D1Database):
    pid = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT id,base_url,model_name FROM ai_providers WHERE id=?", [pid])
    if not rows:
        await call.answer("مدل پیدا نشد", show_alert=True); return
    p = rows[0]
    await state.set_state(BotStates.admin_add_provider)
    await state.update_data(provider_edit_id=pid, provider_base_url=None, provider_token=None, panel_message_id=call.message.message_id,parent_callback="provider_view_"+str(pid))
    await call.message.edit_text(
        f"✏️ <b>ویرایش مدل #{pid}</b>\n\n"
        f"مدل فعلی: <code>{html.escape(str(p.get('model_name')))}</code>\n\n"
        "مرحله ۱ از ۳\n🔗 Base URL جدید را ارسال کن.",
        parse_mode='HTML', reply_markup=get_exit_menu())


@router.callback_query(F.data.startswith("provider_test_"))
async def provider_test(call: CallbackQuery, db: D1Database):
    pid = int(call.data.split("_")[-1])
    await call.answer("🧪 در حال تست...", show_alert=False)
    manager = AIProviderManager(db)
    try:
        result = await manager.test_provider(pid)
    finally:
        await manager.close()
    if result.get('ok'):
        await call.message.edit_text(f"✅ تست موفق بود.\n\n⚡ زمان پاسخ: {result.get('latency_ms',0)}ms\n🤖 پاسخ: {html.escape(result.get('preview','OK'))}", reply_markup=get_admin_back_kb(f"provider_view_{pid}"))
    else:
        await call.message.edit_text(f"❌ تست ناموفق بود.\n\n{html.escape(result.get('error','unknown')[:1200])}", reply_markup=get_admin_back_kb(f"provider_view_{pid}"))


@router.callback_query(F.data.startswith("provider_priority_"))
async def provider_priority(call: CallbackQuery, state: FSMContext):
    pid = int(call.data.split("_")[-1])
    await state.set_state(BotStates.admin_automation_setting)
    await state.update_data(automation_setting_key="__provider_priority__", provider_priority_id=pid,parent_callback=f"provider_view_{pid}",panel_message_id=call.message.message_id)
    await call.message.edit_text("🔢 اولویت این مدل را به عدد بفرست.\nعدد کمتر = اولویت بالاتر.", reply_markup=get_exit_menu())


@router.callback_query(F.data.startswith("provider_toggle_"))
async def provider_toggle(call: CallbackQuery, db: D1Database):
    pid = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT enabled FROM ai_providers WHERE id=?", [pid])
    if rows:
        await db.execute("UPDATE ai_providers SET enabled=?, updated_at=? WHERE id=?", [0 if rows[0].get("enabled") else 1, datetime.now(timezone.utc).isoformat(), pid])
    await provider_view(call, db)


@router.callback_query(F.data.regexp(r"^provider_delete_(\d+)$"))
async def provider_delete(call: CallbackQuery, db: D1Database):
    pid = int(call.data.split("_")[-1])
    rows = await db.execute("SELECT id, model_name, name FROM ai_providers WHERE id=?", [pid])
    if not rows:
        await call.answer("مدل پیدا نشد", show_alert=True); return
    p = rows[0]
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🗑️ بله، حذف شود", callback_data=f"provider_delete_confirm_{pid}")],
        [InlineKeyboardButton(text="↩️ لغو", callback_data=f"provider_view_{pid}")]
    ])
    await call.message.edit_text(
        f"⚠️ <b>حذف مدل</b>\n\nمدل: <code>{html.escape(str(p.get('model_name')))}</code>\n\nاین Provider از چرخه Failover حذف خواهد شد. ادامه می‌دهی؟",
        parse_mode='HTML', reply_markup=kb)


@router.callback_query(F.data.regexp(r"^provider_delete_confirm_(\d+)$"))
async def provider_delete_confirm(call: CallbackQuery, db: D1Database):
    pid = int(call.data.split("_")[-1])
    await db.execute("DELETE FROM ai_providers WHERE id=?", [pid])
    rows = await db.execute("SELECT id,name,base_url,model_name,priority,enabled,web_enabled,status,last_error,last_latency_ms FROM ai_providers ORDER BY priority ASC, id ASC")
    await call.message.edit_text("🗑️ <b>مدل حذف شد.</b>\n\nفهرست مدل‌ها:", parse_mode='HTML', reply_markup=provider_list_kb(rows))
    await call.answer("حذف شد")


def automation_content_db_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='📥 مدیریت صف انتشار',callback_data='auto_queue')],
        [InlineKeyboardButton(text='📰 محتوای تولیدشده',callback_data='auto_articles')],
        [InlineKeyboardButton(text='🗄 آمار و پاکسازی دیتای اتوماسیون',callback_data='auto_db')],
        [InlineKeyboardButton(text='🔙 اتوماسیون محتوا',callback_data='auto_back')]
    ])

@router.callback_query(F.data == "auto_content_db")
async def auto_content_db(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    rows=await db.execute("SELECT (SELECT COUNT(*) FROM articles) articles,(SELECT COUNT(*) FROM publication_queue WHERE status='queued') queued,(SELECT COUNT(*) FROM source_items) source_items,(SELECT COUNT(*) FROM test_history) tests")
    r=rows[0] if rows else {}
    text=("🗃 <b>محتوا و داده‌های اتوماسیون</b>\n\n"
          f"📥 صف: <b>{r.get('queued',0)}</b>\n"
          f"📰 مقالات تولیدشده: <b>{r.get('articles',0)}</b>\n"
          f"🔎 آیتم‌های کشف‌شده/حافظه منابع: <b>{r.get('source_items',0)}</b>\n"
          f"🧪 سوابق تست: <b>{r.get('tests',0)}</b>\n\n"
          "منابع و مدل‌های AI پاک نمی‌شوند؛ فقط داده‌های محتوایی اتوماسیون مدیریت می‌شوند.")
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=automation_content_db_kb()); await call.answer()

@router.callback_query(F.data == "auto_db")
async def auto_db(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    rows=await db.execute("SELECT (SELECT COUNT(*) FROM articles) articles,(SELECT COUNT(*) FROM publication_queue) queue_all,(SELECT COUNT(*) FROM source_items) source_items,(SELECT COUNT(*) FROM automation_logs) logs,(SELECT COUNT(*) FROM test_history) tests")
    r=rows[0] if rows else {}
    text=("🗄 <b>دیتای اتوماسیون</b>\n\n"
          f"📰 مقالات: <b>{r.get('articles',0)}</b>\n📥 رکوردهای صف: <b>{r.get('queue_all',0)}</b>\n"
          f"🔎 source items: <b>{r.get('source_items',0)}</b>\n🧪 سوابق تست: <b>{r.get('tests',0)}</b>\n📜 لاگ‌ها: <b>{r.get('logs',0)}</b>\n\n"
          "⚠️ حذف همه داده‌های محتوایی برگشت‌پذیر نیست. منابع، تنظیمات و مدل‌های AI حفظ می‌شوند.")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='🗑️ حذف کل دیتای محتوایی',callback_data='auto_db_delete_confirm')],
        [InlineKeyboardButton(text='🔙 محتوا و داده‌ها',callback_data='auto_content_db')]
    ])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=kb); await call.answer()

@router.callback_query(F.data == "auto_db_delete_confirm")
async def auto_db_delete_confirm(call: CallbackQuery):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='⚠️ بله، همه داده‌ها حذف شود',callback_data='auto_db_delete_yes')],
        [InlineKeyboardButton(text='↩️ لغو',callback_data='auto_db')]
    ])
    await call.message.edit_text("⚠️ <b>تأیید حذف کامل دیتای اتوماسیون</b>\n\nهمه مقالات، صف، آیتم‌های کشف‌شده، سوابق تست و لاگ‌های اتوماسیون حذف می‌شوند. منابع و مدل‌ها باقی می‌مانند.\n\nادامه می‌دهی؟",parse_mode='HTML',reply_markup=kb); await call.answer()

@router.callback_query(F.data == "auto_db_delete_yes")
async def auto_db_delete_yes(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    await db.execute_batch([
        {"sql":"DELETE FROM publication_queue"},
        {"sql":"DELETE FROM articles"},
        {"sql":"DELETE FROM source_items"},
        {"sql":"DELETE FROM test_history"},
        {"sql":"DELETE FROM manual_channel_events"},
        {"sql":"DELETE FROM automation_logs"},
    ])
    now=datetime.now(timezone.utc).isoformat()
    await db.execute("UPDATE sources SET last_checked_at=NULL,next_check_at=?",[now])
    await call.message.edit_text("✅ <b>داده‌های محتوایی اتوماسیون پاک شد.</b>\n\nمنابع، تنظیمات و مدل‌های AI حفظ شدند و چرخه از نو قابل شروع است.",parse_mode='HTML',reply_markup=automation_content_db_kb()); await call.answer("پاکسازی انجام شد")

@router.callback_query(F.data == "auto_quality")
async def auto_quality(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    score = await get_setting(db, 'min_content_score', str(DEFAULT_MIN_CONTENT_SCORE))
    text = (f'🧠 <b>کیفیت محتوا</b>\n\nحداقل امتیاز فعلی: <b>{html.escape(score)}</b> از 100\n\n'
            'این بخش فقط درباره انتخاب و کیفیت خبر است؛ تنظیم زمان و تعداد پست‌ها در بخش «برنامه انتشار» قرار دارد.')
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='⭐ تغییر حداقل امتیاز', callback_data='set_min_score')],
        [InlineKeyboardButton(text='🎯 وزن معیارهای محتوا', callback_data='quality_weights')],
        [InlineKeyboardButton(text='✍️ دستورهای محتوای تولید', callback_data='editorial_prompts')],
        [InlineKeyboardButton(text='🔙 اتوماسیون محتوا', callback_data='auto_back')]
    ])
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=kb)

@router.callback_query(F.data == "quality_about")
async def quality_about(call: CallbackQuery):
    text = ('🧠 <b>معیارهای کیفیت محتوا</b>\n\n'
            '⭐ اهمیت جهانی و فناوری\n'
            '🤖 ارتباط با AI و مدل‌ها\n'
            '🔐 ارزش امنیت سایبری\n'
            '🇮🇷 ارتباط با ایران و فارسی‌زبانان\n'
            '🆕 تازگی و ارزش خبری\n'
            '♻️ تکراری نبودن\n'
            '✅ اعتبار و کیفیت منبع\n\n'
            'محتوای ضعیف یا مبهم منتشر نمی‌شود؛ کیفیت بر تعداد اولویت دارد.')
    await call.message.edit_text(text, parse_mode='HTML', reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🔙 کیفیت محتوا', callback_data='auto_quality')]]))
    await call.answer()

@router.callback_query(F.data == "editorial_prompts")
async def editorial_prompts_panel(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    ch=await get_setting(db,"editorial_prompt_channel","")
    ar=await get_setting(db,"editorial_prompt_article","")
    text=("✍️ <b>دستورهای محتوای تولید</b>\n\n"
          "این دو دستور فقط تعیین می‌کنند چه اطلاعاتی پوشش داده شود.\n"
          "Formatting، ایموجی، Bold، Italic، Quote و زیباسازی را خود ربات انجام می‌دهد.\n\n"
          f"📌 کوتاه (~500): <code>{html.escape(ch[:260])}</code>\n"
          f"📌 کامل (~2000): <code>{html.escape(ar[:260])}</code>")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='✍️ ویرایش دستور کوتاه',callback_data='set_editorial_prompt_channel')],
        [InlineKeyboardButton(text='📝 ویرایش دستور کامل',callback_data='set_editorial_prompt_article')],
        [InlineKeyboardButton(text='♻️ بازگردانی دستور پیش‌فرض',callback_data='editorial_prompts_reset')],
        [InlineKeyboardButton(text='🔙 کیفیت محتوا',callback_data='auto_quality')]
    ])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=kb); await call.answer()

@router.callback_query(F.data == "editorial_prompts_reset")
async def editorial_prompts_reset(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await set_setting(db,'editorial_prompt_channel',"فقط محتوای فنی، دقیق و واقعاً ارزشمند برای مخاطب فناوری و هوش مصنوعی را پوشش بده؛ مطالب سطحی، عمومی، کلیشه‌ای و پیش‌پاافتاده را کنار بگذار. خودِ خبر و جزئیات واقعی را بیان کن.")
    await set_setting(db,'editorial_prompt_article',"مقاله کامل باید فنی، غنی و مبتنی بر اطلاعات واقعی منبع باشد؛ جزئیات، زمینه، نحوه کار، اعداد و اثرات قابل اتکا را توضیح بده. سؤال نساز؛ پاسخ و اطلاعات موجود را مستقیم بیان کن. از کلی‌گویی و قضاوت شخصی پرهیز کن.")
    await editorial_prompts_panel(call,db)

@router.callback_query(F.data == "set_editorial_prompt_channel")
async def set_editorial_prompt_channel(call: CallbackQuery, state: FSMContext, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    current=await get_setting(db,"editorial_prompt_channel","")
    await prompt_for_setting(
        call,state,"editorial_prompt_channel",
        "✍️ <b>پرامپت محتوای کوتاه کانال</b>\n\nاین متن فقط مشخص می‌کند چه چیزهایی در نسخه حدود 500 کاراکتری پوشش داده شود؛ Formatting را تغییر نمی‌دهد.\n\nپرامپت جدید را بفرست.\n\nفعلی:\n<code>"+html.escape(current[:1800])+"</code>",
        "editorial_prompts"
    )

@router.callback_query(F.data == "set_editorial_prompt_article")
async def set_editorial_prompt_article(call: CallbackQuery, state: FSMContext, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    current=await get_setting(db,"editorial_prompt_article","")
    await prompt_for_setting(
        call,state,"editorial_prompt_article",
        "📝 <b>پرامپت محتوای کامل داخل ربات</b>\n\nاین متن فقط مشخص می‌کند چه اطلاعاتی در نسخه حدود 2000 کاراکتری پوشش داده شود؛ Formatting و زیبایی متن وظیفه ربات است.\n\nپرامپت جدید را بفرست.\n\nفعلی:\n<code>"+html.escape(current[:1800])+"</code>",
        "editorial_prompts"
    )

@router.callback_query(F.data == "weight_global")
async def set_weight_global(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_global","🌍 اهمیت جهانی را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_technology")
async def set_weight_technology(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_technology","💻 فناوری را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_ai")
async def set_weight_ai(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_ai","🤖 هوش مصنوعی را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_cyber")
async def set_weight_cyber(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_cyber","🔐 امنیت سایبری را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_education")
async def set_weight_education(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_education","📚 آموزش را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_iran")
async def set_weight_iran(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_iran","🇮🇷 ارتباط ایران/فارسی را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_freshness")
async def set_weight_freshness(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_freshness","🆕 تازگی را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_source")
async def set_weight_source(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_source","✅ اعتبار منبع را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "weight_novelty")
async def set_weight_novelty(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"weight_novelty","♻️ عدم تکرار را به عدد 0 تا 100 بفرست.","quality_weights")

@router.callback_query(F.data == "quality_weights")
async def quality_weights(call:CallbackQuery,db:D1Database):
    await call.answer()
    items=[("global","🌍 اهمیت جهانی"),("technology","💻 فناوری"),("ai","🤖 هوش مصنوعی"),("cyber","🔐 امنیت سایبری"),("education","📚 آموزش"),("iran","🇮🇷 ایران/فارسی"),("freshness","🆕 تازگی"),("source","✅ اعتبار منبع"),("novelty","♻️ عدم تکرار")]
    text="🎯 <b>وزن معیارها</b>\nعدد بالاتر = اهمیت بیشتر.\n\n"; rows=[]
    pairs=[]
    for k,label in items:
        text+=f"{label}: <b>{await get_setting(db,'weight_'+k,'10')}</b>\n"; pairs.append((k,label))
    rows=[]
    for i in range(0,len(pairs),2):
        rows.append([InlineKeyboardButton(text=label,callback_data='weight_'+k) for k,label in pairs[i:i+2]])
    rows.append([InlineKeyboardButton(text="🔙 کیفیت محتوا",callback_data="auto_quality")])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=rows)); await call.answer()

@router.callback_query(F.data == "auto_schedule")
async def auto_schedule(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    text,kb=await get_schedule_panel(db)
    await call.message.edit_text(text,parse_mode="HTML",reply_markup=kb)

@router.callback_query(F.data == "auto_health")
async def auto_health(call:CallbackQuery,db:D1Database,bot:Bot):
    if call.from_user.id!=ADMIN_ID:return
    await call.answer()
    channel=await get_channel_id(db)
    providers=await db.execute("SELECT status,enabled FROM ai_providers")
    healthy=sum(1 for p in providers if p.get('enabled') and p.get('status')=='healthy')
    sources=await db.execute("SELECT COUNT(*) c FROM sources WHERE enabled=1")
    text=(f"🧪 <b>تست و سلامت</b>\n\nD1: {'✅ آماده' if db.session and not db.session.closed else '❌'}\n"
          f"کانال: {'✅ تنظیم شده' if channel else '❌ تنظیم نشده'}\nمدل سالم: {healthy}/{len(providers)}\n"
          f"منبع فعال: {sources[0].get('c',0) if sources else 0}\n\nاز اینجا تست‌ها را مرحله‌به‌مرحله اجرا کن.")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🤖 تست مدل‌ها",callback_data="health_test_ai"),InlineKeyboardButton(text="🌐 تست همه منابع",callback_data="health_test_source")],
        [InlineKeyboardButton(text="🧪 تولید بدون انتشار",callback_data="health_dry_run")],
        [InlineKeyboardButton(text="▶️ اجرای یک چرخه واقعی",callback_data="health_run_cycle")],
        [InlineKeyboardButton(text="📢 تست انتشار واقعی",callback_data="health_test_publish")],
        [InlineKeyboardButton(text="🚦 وضعیت اجرا",callback_data="health_deployment")],
        [InlineKeyboardButton(text="📜 لاگ اتوماسیون",callback_data="health_logs")],
        [InlineKeyboardButton(text="🔄 بروزرسانی",callback_data="auto_health"),InlineKeyboardButton(text="🔙 اتوماسیون",callback_data="auto_back")]
    ])
    await call.message.edit_text(text,parse_mode="HTML",reply_markup=kb); await call.answer()

@router.callback_query(F.data == "health_test_ai")
async def health_test_ai(call:CallbackQuery,db:D1Database):
    rows=await db.execute("SELECT id,name,model_name,priority,status FROM ai_providers WHERE enabled=1 AND status NOT IN ('cooldown') ORDER BY priority ASC,id ASC LIMIT 8")
    if not rows:
        await call.message.edit_text("❌ هیچ مدل فعالی نیست.",reply_markup=get_admin_back_kb("auto_health")); return
    await call.answer("تست مدل‌ها شروع شد…")
    await log_automation(db,"INFO","health_test_ai_started","manual AI provider test")
    await edit_health_progress(call.message,health_progress_block(0,len(rows),"تست مدل‌های AI","هر مدل با درخواست واقعی TEST_OK بررسی می‌شود…"))
    m=AIProviderManager(db, None); results=[]
    try:
        for i,p in enumerate(rows,1):
            await edit_health_progress(call.message,health_progress_block(i,len(rows),"تست مدل‌های AI",f"مدل {i}/{len(rows)}: {p.get('model_name')} را تست می‌کنم…"))
            result=await m.test_provider(int(p['id']))
            if result.get('ok'):
                results.append(f"✅ {html.escape(str(p.get('model_name')))} · {result.get('latency_ms',0)}ms")
            else:
                results.append(f"❌ {html.escape(str(p.get('model_name')))}\n<code>{html.escape(str(result.get('error','unknown'))[:650])}</code>")
    finally: await m.close()
    await log_automation(db,"INFO","health_test_ai_finished",f"providers={len(rows)}")
    await edit_health_progress(call.message,"🧪 <b>نتیجه تست مدل‌های AI</b>\n\n"+"\n".join(results), get_admin_back_kb("auto_health")); await call.answer()

@router.callback_query(F.data == "health_test_source")
async def health_test_source(call:CallbackQuery,db:D1Database,bot:Bot):
    rows=await db.execute("SELECT * FROM sources ORDER BY priority ASC,id ASC")
    if not rows:
        await call.message.edit_text("❌ هیچ منبعی ثبت نشده است.",reply_markup=get_admin_back_kb("auto_health")); return
    await call.answer("تست همه منابع شروع شد…")
    await log_automation(db,"INFO","health_test_sources_started",f"sources={len(rows)}")
    await edit_health_progress(call.message,health_progress_block(0,max(1,len(rows)),"تست همه منابع","در حال بررسی واقعی هر منبع…"))
    ai=AIProviderManager(db,bot); results=[]
    try:
        for i,src in enumerate(rows,1):
            await edit_health_progress(call.message,health_progress_block(i,len(rows),"تست همه منابع",f"🌐 {i}/{len(rows)} · {src.get('name')} → کشف"))
            try:
                r=await discover_for_processing(db,src,ai,allow_scout=False,include_old=False,advance_cursor=False)
                found=int(r.get('direct_count',0) or 0)
                fresh=int(r.get('fresh_count',0) or 0)
                new_count=int(r.get('new_count',0) or 0)
                method=r.get('method') or 'مستقیم'
                if new_count:
                    marker='🟢 آماده بررسی'
                elif fresh:
                    marker='🟡 تازه هست، قبلاً دیده شده'
                elif found:
                    marker='🟠 محتوا هست، ولی تازه نیست'
                else:
                    marker='🔴 دریافت نشد'
                results.append(f"{marker} · {src.get('name')}: پیدا {found} · تازه‌۲۴ساعت {fresh} · جدید {new_count} · مسیر {method}")
            except Exception as e:
                results.append(f"❌ {src.get('name')}: {html.escape(str(e)[:180])}")
    finally: await ai.close()
    await log_automation(db,"INFO","health_test_sources_finished",f"sources={len(rows)}")
    await edit_health_progress(call.message,"🧪 <b>نتیجه تست همه منابع</b>\n\n"+"\n".join(results)+"\n\n🟢 قابل بررسی = محتوای تازه پیدا شد\n🟡 = سایت پاسخ داد ولی گزینه تازه/جدید نداریم\n🔴 = دریافت مستقیم محتوا موفق نشد", get_admin_back_kb("auto_health")); await call.answer()

async def _live_health_animation(key):
    dots=(".","..","..."); i=0
    while key in _LIVE_HEALTH_STATE:
        state=_LIVE_HEALTH_STATE.get(key)
        if not state: return
        try:
            title=state.get("title","در حال انجام")
            bar=state.get("bar","")
            history=state.get("history",[])[-5:]
            text=f"<b>Thinking{dots[i % 3]}</b> · {html.escape(title)}\n\n<code>{bar}</code>\n"+"\n".join(f"• {html.escape(x)}" for x in history)
            await state["message"].edit_text(text,parse_mode="HTML")
        except asyncio.CancelledError:
            return
        except Exception:
            pass
        i+=1; await asyncio.sleep(0.9)

async def edit_health_progress(message: Message, text: str, reply_markup=None):
    key=(message.chat.id,message.message_id)
    if reply_markup is not None:
        task=_LIVE_HEALTH_TASKS.pop(key,None); _LIVE_HEALTH_STATE.pop(key,None)
        if task:
            task.cancel()
            try: await task
            except asyncio.CancelledError: pass
        try: await message.edit_text(text,parse_mode="HTML",reply_markup=reply_markup)
        except Exception: pass
        return
    state=_LIVE_HEALTH_STATE.get(key)
    title="در حال انجام"; bar=""
    plain=strip_html_text(text or "")
    lines=[x.strip() for x in plain.splitlines() if x.strip()]
    if lines: title=lines[0]
    m=re.search(r"<code>(.*?)</code>",text or "",re.S)
    if m: bar=strip_html_text(m.group(1))
    detail=next((x for x in lines[1:] if not x.startswith(("█","░")) and "لطفاً منتظر" not in x), "")
    if not state:
        state={"message":message,"title":title,"bar":bar,"history":[],"last":""}
        _LIVE_HEALTH_STATE[key]=state
        state["title"]=title; state["bar"]=bar
        first_text=f"<b>Thinking.</b> · {html.escape(title)}\n\n<code>{bar}</code>"
        try: await message.edit_text(first_text,parse_mode="HTML")
        except Exception: pass
        _LIVE_HEALTH_TASKS[key]=asyncio.create_task(_live_health_animation(key))
    state["title"]=title; state["bar"]=bar
    if detail and detail!=state.get("last"):
        state["history"].append(detail[:500]); state["history"]=state["history"][-5:]; state["last"]=detail

def health_progress_block(stage: int, total: int, title: str, detail: str = "") -> str:
    total=max(1,total); filled=max(0,min(total,stage)); bar="█"*filled+"░"*(total-filled); pct=int((filled/total)*100)
    return f"<b>{html.escape(title)}</b>\n\n<code>{bar}</code> {pct}%\n{html.escape(detail)}"

async def choose_test_candidate(db, ai, progress=None):
    """Find a fresh test item source-by-source, with visible failover diagnostics.
    Manual tests bypass the source cursor/retry cooldown so a rejected recent article can be retested
    after the manager changes criteria. Freshness allows the last 24 hours; the first 6 hours are prioritized.
    """
    rows=await db.execute("SELECT * FROM sources WHERE enabled=1 ORDER BY priority ASC,id ASC")
    recent_tested_hashes={str(r.get('content_hash') or '') for r in await db.execute("SELECT content_hash FROM test_history ORDER BY id DESC LIMIT 200") if r.get('content_hash')}
    recent_article_rows=await db.execute("SELECT source_url,body,title FROM articles WHERE status IN ('published','ready','test') ORDER BY id DESC LIMIT 300")
    recent_article_urls={normalize_url(r.get('source_url') or '') for r in recent_article_rows if r.get('source_url')}
    recent_article_hashes={text_hash(str(r.get('title') or '')+' '+str(r.get('body') or '')) for r in recent_article_rows}
    diagnostics=[]
    total=len(rows)
    for idx,src in enumerate(rows,1):
        name=str(src.get('name') or src.get('url') or f'منبع {idx}') + (" · خاموش" if not src.get("enabled") else "")
        try:
            if progress: await progress(f"🌐 {idx}/{total} · {name} → کشف مستقیم")
            r=await discover_for_processing(db,src,ai,allow_scout=False,include_old=True)
            raw_items=list(r.get('items') or [])
            method=r.get('method') or 'مستقیم'
            if progress: await progress(f"🌐 {idx}/{total} · {name} → {len(raw_items)} گزینه ({method})")
            priority_hours=float(await get_setting(db,'news_priority_hours',str(NEWS_PRIORITY_HOURS)) or NEWS_PRIORITY_HOURS)
            def _test_sort_key(x):
                dt=parse_publication_datetime(x.get('published_at') or '')
                if not dt: return (1, 0)
                age=(datetime.now(timezone.utc)-dt).total_seconds()/3600.0
                return (0 if age <= priority_hours else 1, -dt.timestamp())
            items=sorted(raw_items,key=_test_sort_key)
            if not items and progress: await progress(f"🌐 {idx}/{total} · {name} → رد شد؛ مورد تازه‌ای پیدا نشد")
            for c in items:
                c=await enrich_candidate_content(dict(c))
                fresh_ok,fresh_reason,_=candidate_is_fresh(c)
                if not fresh_ok:
                    continue
                # Re-check paywall before test
                insufficient, reason = is_insufficient_content(c.get('title',''), c.get('body',''), c.get('description',''))
                if insufficient:
                    continue
                body=(c.get('body') or c.get('description') or '').strip(); url=normalize_url(c.get('url') or '')
                chash=text_hash((c.get('title') or '')+' '+body)
                if len(body)<20 or not url or url in recent_article_urls or chash in recent_tested_hashes or chash in recent_article_hashes:
                    continue
                c['_test_hash']=chash
                if progress: await progress(f"✅ {idx}/{total} · {name} → گزینه تازه پیدا شد")
                return src,c
            diagnostics.append(f"{name}: مورد تازه/جدیدِ قابل تست نداشت")
            if progress: await progress(f"➡️ {idx}/{total} · {name} → رد شد؛ رفتیم سراغ منبع بعدی")
        except Exception as exc:
            msg=f"{type(exc).__name__}: {str(exc)[:120]}"
            diagnostics.append(f"{name}: {msg}")
            if progress: await progress(f"⚠️ {idx}/{total} · {name} → خطا؛ منبع بعدی")
            continue
    try: await log_automation(db,'WARN','test_candidate_exhausted',' | '.join(diagnostics)[:1800])
    except Exception: pass
    return None,None


@router.callback_query(F.data == "health_dry_run")
async def health_dry_run(call:CallbackQuery,db:D1Database,bot:Bot):
    if call.from_user.id!=ADMIN_ID:return
    await call.answer("تست تولید شروع شد…")
    await edit_health_progress(call.message,health_progress_block(1,6,"تست تولید بدون انتشار شروع شد","یک Candidate واقعی از بین منابع انتخاب می‌شود؛ محتوای ثابت استفاده نمی‌شود."))
    ai=AIProviderManager(db,bot)
    try:
        src,item=await choose_test_candidate(db,ai,lambda detail: edit_health_progress(call.message,health_progress_block(2,6,'تست تولید بدون انتشار',detail)))
        if not item:
            await edit_health_progress(call.message,"❌ <b>هیچ گزینه محتوای تازه‌ای برای تست پیدا نشد.</b>\n\nهمه منابع به‌ترتیب بررسی شدند.", get_admin_back_kb("auto_health")); return
        await edit_health_progress(call.message,health_progress_block(2,6,"محتوا پیدا شد",f"منبع: {src.get('name')}\nعنوان: {item.get('title')[:180]}"))
        test_hash=item.get('_test_hash') or text_hash((item.get('title') or '')+' '+(item.get('body') or item.get('description') or ''))
        await db.execute("INSERT INTO test_history(source_url,content_hash,title,tested_at) VALUES(?,?,?,?)",[item.get('url') or '',test_hash,item.get('title') or '',datetime.now(timezone.utc).isoformat()])
        weights={k:float(await get_setting(db,'weight_'+k,'10')) for k in ['global','technology','ai','cyber','education','iran','freshness','source','novelty']}
        out=await ai_editorial_process(ai,item,src,[],weights,await get_manager_editorial_prompts(db),progress=lambda detail: edit_health_progress(call.message,health_progress_block(3,6,"در حال تولید محتوا",detail)))
        if out.get('error'):
            await edit_health_progress(call.message,"❌ <b>تست تولید شکست خورد</b>\n\n<code>"+html.escape(str(out['error'])[:1800])+"</code>", get_admin_back_kb("auto_health")); return
        min_score=float(await get_setting(db,'min_content_score',str(DEFAULT_MIN_CONTENT_SCORE)))
        if float(out.get('score',0) or 0) < min_score:
            await edit_health_progress(call.message,f"⚠️ <b>این گزینه زیر حداقل امتیاز مدیر بود.</b>\n\nامتیاز: <b>{out.get('score','-')}</b> · حد مدیر: <b>{min_score:g}</b>\nدلیل: {html.escape(str(out.get('why','-'))[:800])}", get_admin_back_kb("auto_health")); return
        await edit_health_progress(call.message,health_progress_block(4,6,"محتوا تولید شد","در حال بررسی Formatting و طول متن…"))
        ch=ensure_rich_channel_format(str(out.get('title') or item.get('title') or 'مطلب'), out.get('channel_html') or out.get('channel_text') or item.get('body') or item.get('description') or '', str(out.get('category') or src.get('category') or 'tech'))
        ar=ensure_rich_article_format(str(out.get('title') or item.get('title') or 'مطلب'), out.get('article_html') or out.get('article_text') or item.get('body') or item.get('description') or '', item.get('url') or '')
        await edit_health_progress(call.message,health_progress_block(5,6,"قالب و محتوا آماده شد","عکس منبع و Deep Link آزمایشی نیز بررسی می‌شوند."))
        ai_info=out.get('ai') or {}
        msg=("✅ <b>تست تولید واقعی موفق شد.</b>\n\n"
             f"🌐 منبع: <b>{html.escape(str(src.get('name')))}</b>\n"
             f"📰 عنوان: <b>{html.escape(str(out.get('title') or item.get('title')))}</b>\n"
             f"🤖 مدل: <code>{html.escape(str(ai_info.get('model') or '-'))}</code>\n"
             f"📊 امتیاز: <b>{out.get('score','-')}</b>\n\n"
             "<b>📝 کانال:</b>\n"+ch[:1500]+"\n\n<b>📖 مقاله:</b>\n"+ar[:4200]+"\n\n"
             "🚫 <b>انتشار انجام نشد.</b> این همان موتور تولید واقعی بود اما در حالت تست.")
        await edit_health_progress(call.message,msg, get_admin_back_kb("auto_health"))
    except Exception as e:
        logger.exception('health dry run failed')
        await edit_health_progress(call.message,"❌ <b>تست تولید شکست خورد</b>\n\n<code>"+html.escape(str(e)[:2500])+"</code>", get_admin_back_kb("auto_health"))
    finally: await ai.close()

def make_health_png(width=1280,height=720):
    row=bytearray()
    for x in range(width):
        t=x/(width-1); row.extend((int(16+24*t),int(22+36*t),int(48+78*t)))
    raw=bytearray()
    for _ in range(height): raw.append(0); raw.extend(row)
    def chunk(tag,data): return struct.pack('>I',len(data))+tag+data+struct.pack('>I',zlib.crc32(tag+data)&0xffffffff)
    return b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',width,height,8,2,0,0,0))+chunk(b'IDAT',zlib.compress(bytes(raw),9))+chunk(b'IEND',b'')

@router.callback_query(F.data == "health_run_cycle")
async def health_run_cycle(call:CallbackQuery,db:D1Database,bot:Bot):
    if call.from_user.id!=ADMIN_ID:return
    await call.answer('چرخه واقعی شروع شد؛ این بار واقعاً منابع و AI را اجرا می‌کنم…')
    await log_automation(db,"INFO","real_cycle_started","manual real pipeline test")
    ai=AIProviderManager(db,bot); rows=await db.execute("SELECT * FROM sources WHERE enabled=1 ORDER BY priority ASC,id ASC")
    await edit_health_progress(call.message,health_progress_block(0,max(1,len(rows)),'▶️ اجرای یک چرخه واقعی','این همان Pipeline اتوماتیک است؛ داده ساختگی استفاده نمی‌شود.'))
    results=[]
    try:
        total=len(rows)
        for i,src in enumerate(rows,1):
            name=str(src.get('name') or src.get('url') or f'منبع {i}')
            await edit_health_progress(call.message,health_progress_block(i-1,max(1,total),'▶️ اجرای یک چرخه واقعی',f'🌐 {i}/{total} · {name} → در حال بررسی عمیق…'))
            await log_automation(db,'INFO','source_check_started',f'{i}/{total} · {name} → شروع بررسی')
            try:
                r=await fetch_source_cycle(db,src,ai,progress=lambda _stage,detail: edit_health_progress(call.message,health_progress_block(i,max(1,total),"▶️ اجرای یک چرخه واقعی",detail)))
                results.append(r)
                await log_automation(db,'INFO','source_check_result',f'{i}/{total} · {name} → پیدا {r.get("found",0)} · تازه {r.get("candidates",0)} · AI {r.get("processed",0)} · صف {r.get("queued",0)} · رد {r.get("rejected",0)} · خطا {r.get("errors",0)}')
                await edit_health_progress(call.message,health_progress_block(i,max(1,total),'▶️ اجرای یک چرخه واقعی',f'🌐 {i}/{total} · {name} → پایان: پیدا {r.get("found",0)} | تازه {r.get("candidates",0)} | صف {r.get("queued",0)}'))
            except Exception as exc:
                r={'errors':1,'found':0,'candidates':0,'processed':0,'queued':0,'rejected':0}
                results.append(r)
                await log_automation(db,'ERROR','source_check_result',f'{i}/{total} · {name} → خطا: {type(exc).__name__}: {str(exc)[:180]}')
                await edit_health_progress(call.message,health_progress_block(i,max(1,total),'▶️ اجرای یک چرخه واقعی',f'🌐 {i}/{total} · {name} → خطا؛ منبع بعدی'))
        published=await publish_next_article(db,bot)
        total_found=sum((r.get('found',0) if isinstance(r,dict) else 0) for r in results)
        total_new=sum((r.get('candidates',0) if isinstance(r,dict) else 0) for r in results)
        total_processed=sum((r.get('processed',0) if isinstance(r,dict) else 0) for r in results)
        total_queued=sum((r.get('queued',0) if isinstance(r,dict) else 0) for r in results)
        q=await db.execute("SELECT COUNT(*) c FROM publication_queue WHERE status='queued'")
        await log_automation(db,"INFO","real_cycle_finished",json.dumps({"sources":len(rows),"processed":total_processed,"queued":total_queued,"published":bool(published)},ensure_ascii=False))
        total_rejected=sum((r.get('rejected',0) if isinstance(r,dict) else 0) for r in results)
        total_errors=sum((r.get('errors',0) if isinstance(r,dict) else 0) for r in results)
        detail = ('✅ بله' if published else '⏸ خیر')
        summary_text=(f"✅ <b>چرخه واقعی کامل شد.</b>\n\n"
                     f"🌐 منابع بررسی‌شده: <b>{len(rows)}</b>\n"
                     f"📰 مواردی که منبع برگرداند: <b>{total_found}</b>\n"
                     f"🆕 گزینه‌های تازه/جدید: <b>{total_new}</b>\n"
                     f"🤖 ارسال‌شده به AI: <b>{total_processed}</b>\n"
                     f"✅ پذیرفته‌شده: <b>{total_queued}</b>\n"
                     f"🚫 ردشده: <b>{total_rejected}</b>\n"
                     f"❌ خطا: <b>{total_errors}</b>\n"
                     f"📦 صف فعلی: <b>{q[0].get('c',0) if q else 0}</b>\n"
                     f"📢 انتشار همین چرخه: <b>{detail}</b>\n\n"
                     "ℹ️ این چرخه همان کاری را اجرا می‌کند که Worker خودکار انجام می‌دهد:\n"
                     "کشف → تازه/جدید → AI → امتیاز مدیر → تولید → صف → انتشار بر اساس برنامه.")
        await edit_health_progress(call.message,summary_text, get_admin_back_kb("auto_health"))
    except Exception as e:
        logger.exception('health run cycle failed')
        await edit_health_progress(call.message,"❌ <b>اجرای چرخه شکست خورد</b>\n\n<code>"+html.escape(str(e)[:2500])+"</code>", get_admin_back_kb("auto_health"))
    finally: await ai.close()

@router.callback_query(F.data == "health_test_publish")
async def health_test_publish(call:CallbackQuery,db:D1Database,bot:Bot):
    if call.from_user.id!=ADMIN_ID:return
    channel=await get_channel_id(db)
    if not channel:
        await call.message.edit_text("❌ <b>کانال تنظیم نشده است.</b>",parse_mode='HTML',reply_markup=get_admin_back_kb('auto_health')); return
    await call.answer('تست انتشار واقعی شروع شد…')
    await edit_health_progress(call.message,health_progress_block(1,6,'📢 تست انتشار واقعی','یک گزینه محتوای تازه از منابع واقعی گرفته و با AI تولید می‌شود؛ متن ثابت استفاده نمی‌شود.'))
    ai=AIProviderManager(db,bot)
    try:
        src,item=await choose_test_candidate(db,ai,lambda detail: edit_health_progress(call.message,health_progress_block(2,6,'📢 تست انتشار واقعی',detail)))
        if not item: raise RuntimeError('هیچ گزینه محتوای تازه‌ای برای تست انتشار پیدا نشد.')
        await edit_health_progress(call.message,health_progress_block(2,6,'Candidate واقعی پیدا شد',f"منبع: {src.get('name')}\n{item.get('title')[:180]}"))
        test_hash=item.get('_test_hash') or text_hash((item.get('title') or '')+' '+(item.get('body') or item.get('description') or ''))
        await db.execute("INSERT INTO test_history(source_url,content_hash,title,tested_at) VALUES(?,?,?,?)",[item.get('url') or '',test_hash,item.get('title') or '',datetime.now(timezone.utc).isoformat()])
        weights={k:float(await get_setting(db,'weight_'+k,'10')) for k in ['global','technology','ai','cyber','education','iran','freshness','source','novelty']}
        out=await ai_editorial_process(ai,item,src,[],weights,await get_manager_editorial_prompts(db),progress=lambda detail: edit_health_progress(call.message,health_progress_block(3,6,"در حال تولید محتوا",detail)))
        if out.get('error'): raise RuntimeError(out['error'])
        # Test publication obeys only the manager's numeric threshold.
        min_score=float(await get_setting(db,'min_content_score',str(DEFAULT_MIN_CONTENT_SCORE)))
        if not manager_accepts_score(float(out.get('score',0) or 0), min_score):
            raise RuntimeError(f"امتیاز {out.get('score','-')} با حد مدیر {min_score:g} و دامنه انعطاف {MANAGER_SCORE_TOLERANCE:g} همخوان نیست")
        ch=sanitize_telegram_html(out.get('channel_html') or out.get('channel_text') or '')
        ar=sanitize_telegram_html(out.get('article_html') or out.get('article_text') or '')
        ar=append_resource_links(ar,out.get('resource_links'),item.get('url') or '')
        ar=remove_article_metadata_blocks(ar)
        await edit_health_progress(call.message,health_progress_block(3,6,'محتوا و Formatting آماده شد','در حال ذخیره مقاله تست و ساخت Deep Link…'))
        now=datetime.now(timezone.utc).isoformat()
        ins=await db.execute("INSERT INTO articles(source_item_id,title,channel_text,body,source_url,image_url,category,score,status,created_at,source_published_at) VALUES(NULL,?,?,?,?,?,?,?,'test',?,?) RETURNING id",
            [out.get('title') or item.get('title') or 'Test',ch,ar,item.get('url') or '','', 'test',float(out.get('score') or 0),now,item.get('published_at','')[:100]])
        aid=int(ins[0]['id']) if ins else 0
        token=make_deep_token(aid); await db.execute('UPDATE articles SET deep_token=? WHERE id=?',[token,aid])
        username=await get_runtime_bot_username(bot)
        if not username: raise RuntimeError('Username ربات پیدا نشد.')
        deep=f'https://t.me/{username}?start=article_{token}'
        await edit_health_progress(call.message,health_progress_block(4,6,'Deep Link آماده شد','ارسال همان محتوای تولیدشده به کانال…'))
        channel_html=sanitize_telegram_html(ch)
        photo=item.get('image_url') or ''
        sent=None
        if photo:
            try: sent=await bot.send_photo(channel,photo=photo,caption=publication_caption(str(out.get('title') or item.get('title') or 'مطلب'),channel_html,deep),parse_mode='HTML')
            except Exception: sent=None
        if sent is None:
            final_text=sanitize_telegram_html(channel_html + f"\n\n<a href=\"{html.escape(deep,quote=True)}\">📖 بیشتر بخوانید</a>")
            sent=await bot.send_message(channel,text=final_text[:4096],parse_mode='HTML',disable_web_page_preview=True)
        await db.execute("UPDATE articles SET published_message_id=?,published_at=? WHERE id=?",[getattr(sent,'message_id',0),now,aid])
        await edit_health_progress(call.message,health_progress_block(5,6,'✅ انتشار انجام شد','در حال نهایی‌کردن نتیجه و لینک تست…'))
        result=("✅ <b>تست انتشار واقعی موفق شد.</b>\n\n"
                f"🌐 منبع: <b>{html.escape(str(src.get('name')))}</b>\n"
                f"📰 عنوان: <b>{html.escape(str(out.get('title') or item.get('title')))}</b>\n"
                f"🤖 مدل: <code>{html.escape(str((out.get('ai') or {}).get('model') or '-'))}</code>\n"
                f"📢 Message ID: <code>{getattr(sent,'message_id',0)}</code>\n"
                f"🔗 <a href=\"{html.escape(deep,quote=True)}\">📖 باز کردن ادامه مطلب تست</a>")
        await edit_health_progress(call.message,result, get_admin_back_kb("auto_health"))
    except Exception as e:
        logger.exception('real publish test failed')
        await edit_health_progress(call.message,'❌ <b>تست انتشار واقعی شکست خورد</b>\n\n<code>'+html.escape(str(e)[:2500])+'</code>', get_admin_back_kb("auto_health"))
    finally: await ai.close()

@router.callback_query(F.data == "health_deployment")
async def health_deployment(call:CallbackQuery,db:D1Database):
    if call.from_user.id!=ADMIN_ID:return
    await call.answer()
    hb=await get_setting(db,'worker_heartbeat_at',''); started=await get_setting(db,'worker_started_at',''); cycle=await get_setting(db,'last_cycle_finished_at','')
    now=datetime.now(timezone.utc); hb_age=None
    if hb:
        try: hb_age=int((now-datetime.fromisoformat(hb.replace('Z','+00:00'))).total_seconds())
        except Exception: hb_age=None
    alive=hb_age is not None and hb_age<180
    text=(f"🚦 <b>وضعیت اجرا / Deployment</b>\n\n📦 نسخه: <code>{BUILD_VERSION}</code>\n"
          f"🤖 Worker: {'🟢 زنده' if alive else '🔴 Heartbeat دریافت نمی‌شود'}\n"
          f"⚙️ اتوماسیون: {'🟢 فعال' if await get_setting(db,'automation_enabled','0')=='1' else '🔴 خاموش'}\n"
          f"💓 آخرین Heartbeat: {(str(hb_age)+' ثانیه قبل') if hb_age is not None else 'نداریم'}\n"
          f"🚀 Worker شروع شد: {started or 'نامشخص'}\n🔄 آخرین چرخه: {cycle or 'هنوز اجرا نشده'}")
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=get_admin_back_kb('auto_health')); await call.answer()

@router.callback_query(F.data == "health_logs")
async def health_logs(call:CallbackQuery,db:D1Database):
    await call.answer()
    rows=await db.execute("SELECT level,event,details,created_at FROM automation_logs ORDER BY id DESC LIMIT 20")
    names={"source_check_started":"شروع بررسی منبع","source_check_result":"نتیجه منبع","source_cycle":"چرخه منبع","source_cycle_failed":"خطای منبع","real_cycle_started":"شروع چرخه واقعی","real_cycle_finished":"پایان چرخه واقعی","publication_failed":"خطای انتشار","published":"انتشار موفق","test_candidate_exhausted":"پایان جستجوی گزینه تست","health_test_sources_started":"شروع تست منابع","health_test_sources_finished":"پایان تست منابع"}
    text='📜 <b>لاگ کوتاه و زنده اتوماسیون</b>\n\n'
    if not rows: text+='هنوز لاگی ثبت نشده است.'
    else:
        for r in rows:
            ev=str(r.get('event') or '')
            label=names.get(ev,ev)
            tm=html.escape(str(r.get('created_at') or ''))[11:19]
            detail=html.escape(str(r.get('details') or '')[:420])
            text+=f"<b>{tm} · {html.escape(label)}</b>\n{detail}\n\n"
    await call.message.edit_text(text[:4000],parse_mode='HTML',reply_markup=get_admin_back_kb('auto_health')); await call.answer()


@router.callback_query(F.data == "auto_settings")
async def auto_settings_legacy(call: CallbackQuery, db: D1Database):
    # سازگاری با callbackهای قدیمی؛ به برنامه انتشار هدایت می‌شود.
    await auto_schedule(call, db)

def current_automation_parent(call: CallbackQuery, fallback: str = "auto_channel") -> str:
    return fallback

async def prompt_for_setting(call: CallbackQuery, state: FSMContext, key: str, label: str, parent: str = "auto_schedule"):
    await state.set_state(BotStates.admin_automation_setting)
    await state.update_data(automation_setting_key=key, panel_message_id=call.message.message_id, parent_callback=parent)
    await call.message.edit_text(label, parse_mode="HTML", reply_markup=get_exit_menu())
    await call.answer()


@router.callback_query(F.data == "set_max_daily")
async def set_max_daily(call: CallbackQuery, state: FSMContext, db: D1Database):
    current=await get_setting(db,"max_daily_posts",str(DEFAULT_MAX_DAILY_POSTS))
    await prompt_for_setting(call, state, "max_daily_posts", f"🔢 <b>سقف تقریبی پست روزانه</b> را به عدد بفرست.\nفعلاً روی <b>{html.escape(current)}</b> پست است.", "auto_channel")
@router.callback_query(F.data == "set_min_score")
async def set_min_score(call: CallbackQuery, state: FSMContext):
    await prompt_for_setting(call, state, "min_content_score", "⭐ حداقل امتیاز انتشار را بین 0 تا 100 بفرست. پیشنهاد: 75", "auto_quality")

@router.callback_query(F.data == "set_min_gap")
async def set_min_gap(call: CallbackQuery, state: FSMContext, db: D1Database):
    current=await get_setting(db,"min_post_gap_minutes",str(DEFAULT_MIN_POST_GAP_MINUTES))
    await prompt_for_setting(call, state, "min_post_gap_minutes", f"⏱ <b>حداقل فاصله بین دو پست</b> را بر حسب دقیقه بفرست.\nفعلاً روی <b>{format_duration_minutes(current)}</b> است.\nمثال: <code>30</code> یعنی هر ۳۰ دقیقه و <code>120</code> یعنی هر ۲ ساعت.", "auto_channel")
@router.callback_query(F.data == "set_default_interval")
async def set_default_interval(call: CallbackQuery, state: FSMContext, db: D1Database):
    current=await get_setting(db,"default_source_interval",str(DEFAULT_SOURCE_INTERVAL_MINUTES))
    await prompt_for_setting(call, state, "default_source_interval", f"🌐 <b>فاصله بررسی پیش‌فرض منابع</b> را بر حسب دقیقه بفرست.\nفعلاً روی <b>{html.escape(current)}</b> دقیقه است.\nمثال: <code>1</code> یعنی هر دقیقه.", "auto_channel")
@router.callback_query(F.data == "set_workers")
async def set_workers(call: CallbackQuery, state: FSMContext, db: D1Database):
    current=await get_setting(db,"max_workers",str(DEFAULT_MAX_WORKERS))
    await prompt_for_setting(call, state, "max_workers", f"⚡ تعداد Workerهای همزمان را بین 1 تا 4 بفرست.\nفعلاً روی <b>{html.escape(current)}</b> است.", "auto_channel")
@router.callback_query(F.data == "set_ai_workers")
async def set_ai_workers(call: CallbackQuery, state: FSMContext, db: D1Database):
    current=await get_setting(db,"max_ai_workers",str(DEFAULT_MAX_AI_WORKERS))
    await prompt_for_setting(call, state, "max_ai_workers", f"🧠 تعداد درخواست‌های همزمان AI را بین 1 تا 4 بفرست.\nفعلاً روی <b>{html.escape(current)}</b> است.", "auto_channel")
@router.callback_query(F.data == "set_ai_verify")
async def set_ai_verify(call:CallbackQuery,state:FSMContext):
    await prompt_for_setting(call,state,"ai_verify_mode","🛡 حالت راستی‌آزمایی را بفرست:\nauto = فقط موارد حساس\nalways = همیشه\noff = خاموش","auto_quality")

async def next_publication_estimate(db:D1Database)->Dict[str,Any]:
    now=datetime.now(timezone.utc)
    last_manual=await get_setting(db,"last_manual_channel_post_at","")
    last_pub=await db.execute("SELECT published_at FROM publication_queue WHERE status='published' AND published_at IS NOT NULL ORDER BY id DESC LIMIT 1")
    candidates=[x for x in [last_manual, last_pub[0].get("published_at") if last_pub else ""] if x]
    latest=None
    for raw in candidates:
        try:
            dt=datetime.fromisoformat(str(raw).replace("Z","+00:00"))
            if latest is None or dt>latest: latest=dt
        except Exception: pass
    interval_minutes=float(await get_setting(db,"min_post_gap_minutes",str(DEFAULT_MIN_POST_GAP_MINUTES)))
    target=max(now, latest+timedelta(minutes=interval_minutes) if latest else now)
    queued=await db.execute("SELECT COUNT(*) c FROM publication_queue WHERE status='queued'")
    return {"target":target,"minutes":max(0,int((target-now).total_seconds()/60)) if target>now else 0,"latest":latest,"interval_minutes":int(interval_minutes),"queued":int(queued[0].get('c',0)) if queued else 0}

@router.callback_query(F.data == "auto_publish_now")
async def auto_publish_now(call:CallbackQuery,db:D1Database,bot:Bot):
    if call.from_user.id!=ADMIN_ID: return
    try:
        ok=await publish_next_article(db,bot,force=True)
        msg="✅ اولین محتوای صف همین حالا منتشر شد." if ok else "⚠️ محتوای آماده‌ای برای انتشار فوری پیدا نشد یا سقف روزانه تکمیل شده است."
    except Exception as e:
        msg="❌ انتشار فوری شکست خورد:\n"+html.escape(str(e)[:1200])
    await call.message.edit_text(msg,parse_mode="HTML",reply_markup=get_admin_back_kb("auto_queue")); await call.answer()

@router.callback_query(F.data == "auto_queue")
async def auto_queue(call: CallbackQuery, db: D1Database):
    await call.answer()
    est=await next_publication_estimate(db)
    rows=await db.execute("SELECT q.id,q.article_id,q.status,q.attempts,a.title,a.score,a.category,a.deep_views FROM publication_queue q JOIN articles a ON a.id=q.article_id WHERE q.status='queued' ORDER BY COALESCE(a.source_published_at,a.created_at) DESC, a.score DESC, q.created_at ASC LIMIT 20")
    last_txt=est['latest'].astimezone(pytz.timezone('Asia/Tehran')).strftime('%H:%M') if est['latest'] else 'هنوز منتشر نشده'
    if est['minutes']<=0: next_txt='آماده انتشار طبق برنامه'
    elif est['minutes']<60: next_txt=f"حدود {est['minutes']} دقیقه دیگر"
    else: next_txt=f"حدود {est['minutes']//60} ساعت و {est['minutes']%60} دقیقه دیگر"
    text=("📥 <b>صف انتشار</b>\n\n"
          f"📦 تعداد در صف: <b>{est['queued']}</b>\n"
          f"🕘 آخرین انتشار: <b>{last_txt}</b>\n"
          f"⏱ فاصله مدیریت‌شده: <b>{est['interval_minutes']} دقیقه</b>\n"
          f"🕐 نوبت بعدی: <b>{next_txt}</b>\n\n")
    if not rows: text+="صف فعلاً خالی است."
    kb_rows=[]
    for r in rows:
        text+=f"#{r['article_id']} · ⭐ {float(r['score'] or 0):.0f} · {str(r['title'])[:70]}\n"
        kb_rows.append([InlineKeyboardButton(text=f"📄 #{r['article_id']} · {str(r['title'])[:22]}",callback_data=f'auto_art_{r["article_id"]}')])
    kb_rows += [[InlineKeyboardButton(text='🚀 همین حالا منتشر کن',callback_data='auto_publish_now'),InlineKeyboardButton(text='🔄 بروزرسانی',callback_data='auto_queue')],
                [InlineKeyboardButton(text='📰 محتوای تولیدشده',callback_data='auto_articles')],
                [InlineKeyboardButton(text='🔙 محتوا و داده‌ها',callback_data='auto_content_db')]]
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=kb_rows)); await call.answer()

@router.callback_query(F.data == "auto_articles")
async def auto_articles(call: CallbackQuery, db: D1Database):
    if call.from_user.id != ADMIN_ID: return
    await call.answer()
    rows=await db.execute("SELECT id,title,score,status,category,created_at,published_at,deep_views FROM articles ORDER BY id DESC LIMIT 20")
    text="📰 <b>محتوای تولیدشده</b>\n\n"
    kb=[]
    if not rows: text+='هنوز محتوایی تولید نشده.'
    for r in rows:
        text+=f"#{r['id']} · {'✅' if r.get('status')=='published' else '📝'} · ⭐{float(r.get('score') or 0):.0f} · {str(r.get('title') or '')[:70]}\n"
        kb.append([InlineKeyboardButton(text=f"📄 مشاهده #{r['id']}",callback_data=f"auto_art_{r['id']}")])
    kb += [[InlineKeyboardButton(text='🔙 محتوا و داده‌ها',callback_data='auto_content_db')]]
    await call.message.edit_text(text[:4000],parse_mode='HTML',reply_markup=InlineKeyboardMarkup(inline_keyboard=kb)); await call.answer()

async def render_automation_article(call: CallbackQuery, db: D1Database, article_id:int):
    rows=await db.execute("SELECT a.*,q.status q_status,q.scheduled_at FROM articles a LEFT JOIN publication_queue q ON q.article_id=a.id WHERE a.id=?",[article_id])
    if not rows:
        await call.answer('محتوا پیدا نشد',show_alert=True); return
    a=rows[0]
    ch=plain_len(a.get('channel_text') or '')
    ar=plain_len(a.get('body') or '')
    text=(f"📰 <b>محتوا #{article_id}</b>\n\n"
          f"<b>{html.escape(str(a.get('title') or 'بدون عنوان'))}</b>\n\n"
          f"📌 وضعیت: <b>{html.escape(str(a.get('status') or '-'))}</b>\n"
          f"⭐ امتیاز: <b>{float(a.get('score') or 0):.1f}</b>\n"
          f"📥 وضعیت صف: <b>{html.escape(str(a.get('q_status') or 'ندارد'))}</b>\n"
          f"📏 کانال: <b>{ch}</b> کاراکتر · مقاله: <b>{ar}</b> کاراکتر\n"
          f"👁 بازشدن Deep Link: <b>{int(a.get('deep_views') or 0)}</b>\n"
          f"🌐 منبع: <code>{html.escape(str(a.get('source_url') or '-'))}</code>\n\n"
          "از اینجا می‌توانی محتوای تولیدشده را ببینی، ویرایش یا حذف کنی.")
    kb=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text='👁 مشاهده متن',callback_data=f'auto_art_view_{article_id}')],
        [InlineKeyboardButton(text='✏️ عنوان',callback_data=f'auto_art_edit_title_{article_id}'),InlineKeyboardButton(text='✏️ متن کانال',callback_data=f'auto_art_edit_channel_{article_id}')],
        [InlineKeyboardButton(text='✏️ متن کامل',callback_data=f'auto_art_edit_body_{article_id}'),InlineKeyboardButton(text='📊 آمار',callback_data=f'auto_art_stats_{article_id}')],
        [InlineKeyboardButton(text='🗑 حذف',callback_data=f'auto_art_delete_{article_id}')],
        [InlineKeyboardButton(text='🔙 '+('صف انتشار' if a.get('q_status')=='queued' else 'محتوای تولیدشده'),callback_data='auto_queue' if a.get('q_status')=='queued' else 'auto_articles')]
    ])
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=kb); await call.answer()

@router.callback_query(F.data.regexp(r'^auto_art_(\d+)$'))
async def auto_art_view_callback(call:CallbackQuery,db:D1Database):
    await render_automation_article(call,db,int(call.data.split('_')[-1]))

@router.callback_query(F.data.regexp(r'^auto_art_view_(\d+)$'))
async def auto_art_view_text(call:CallbackQuery,db:D1Database,bot:Bot):
    aid=int(call.data.split('_')[-1]); rows=await db.execute("SELECT title,channel_text,body,status FROM articles WHERE id=?",[aid])
    if not rows: await call.answer('محتوا پیدا نشد',show_alert=True); return
    a=rows[0]
    head=f"📄 <b>{html.escape(str(a.get('title') or ''))}</b>\n\n📢 <b>نسخه کانال:</b>\n{sanitize_telegram_html(a.get('channel_text') or '')}\n\n📖 <b>نسخه کامل:</b>\n"
    body=sanitize_telegram_html(a.get('body') or '')
    paragraphs=[x for x in body.split('\n\n') if x.strip()]
    chunks=[]; cur=head
    for para in paragraphs:
        candidate=cur+para+'\n\n'
        if len(candidate)>3800 and cur.strip()!=head.strip():
            chunks.append(cur.rstrip()); cur=para+'\n\n'
        else:
            cur=candidate
    if cur.strip(): chunks.append(cur.rstrip())
    if not chunks: chunks=[head+'(متن کامل خالی است.)']
    await call.message.edit_text(chunks[0][:4000],parse_mode='HTML',reply_markup=get_admin_back_kb(f'auto_art_{aid}'))
    for chunk in chunks[1:]:
        try: await bot.send_message(call.message.chat.id,chunk[:4000],parse_mode='HTML')
        except Exception: pass
    await call.answer()

@router.callback_query(F.data.regexp(r'^auto_art_stats_(\d+)$'))
async def auto_art_stats(call:CallbackQuery,db:D1Database):
    aid=int(call.data.split('_')[-1]); rows=await db.execute("SELECT a.*,q.status q_status FROM articles a LEFT JOIN publication_queue q ON q.article_id=a.id WHERE a.id=?",[aid])
    if not rows: await call.answer('محتوا پیدا نشد',show_alert=True); return
    a=rows[0]
    text=(f"📊 <b>آمار محتوا #{aid}</b>\n\nعنوان: <b>{html.escape(str(a.get('title') or ''))}</b>\n"
          f"امتیاز: <b>{float(a.get('score') or 0):.1f}</b>\nوضعیت: <b>{html.escape(str(a.get('status') or '-'))}</b>\n"
          f"صف: <b>{html.escape(str(a.get('q_status') or 'ندارد'))}</b>\nDeep Link: <b>{int(a.get('deep_views') or 0)} بار</b>\n"
          f"تولید: <b>{html.escape(str(a.get('created_at') or '-'))}</b>\nانتشار: <b>{html.escape(str(a.get('published_at') or '-'))}</b>")
    await call.message.edit_text(text,parse_mode='HTML',reply_markup=get_admin_back_kb(f'auto_art_{aid}')); await call.answer()

@router.callback_query(F.data.regexp(r'^auto_art_edit_(title|channel|body)_(\d+)$'))
async def auto_art_edit_start(call:CallbackQuery,state:FSMContext,db:D1Database):
    if call.from_user.id!=ADMIN_ID:return
    parts=call.data.split('_'); field=parts[2]; aid=int(parts[3])
    rows=await db.execute("SELECT title,channel_text,body FROM articles WHERE id=?",[aid])
    if not rows: await call.answer('محتوا پیدا نشد',show_alert=True); return
    labels={'title':'عنوان','channel':'متن کانال','body':'متن کامل'}
    await state.set_state(BotStates.automation_article_edit)
    await state.update_data(article_edit_id=aid,article_edit_field=field,parent_message_id=call.message.message_id)
    await call.message.edit_text(f"✏️ <b>ویرایش {labels[field]} #{aid}</b>\n\nمقدار جدید را بفرست.\n\nپیام قبلی پاک نمی‌شود.",parse_mode='HTML',reply_markup=get_exit_menu()); await call.answer()

@router.message(F.chat.id==ADMIN_ID,StateFilter(BotStates.automation_article_edit))
async def auto_art_edit_input(message:Message,state:FSMContext,db:D1Database,bot:Bot):
    data=await state.get_data(); aid=int(data['article_edit_id']); field=data['article_edit_field']; value=(message.text or message.caption or '').strip()
    if not value:
        await message.answer('❌ مقدار خالی است؛ دوباره بفرست.',reply_markup=get_exit_menu()); return
    col={'title':'title','channel':'channel_text','body':'body'}[field]
    if field=='title': value=strip_html_text(value)[:500]
    elif field=='channel': value=sanitize_telegram_html(value)[:5000]
    else: value=sanitize_telegram_html(value)[:18000]
    await db.execute(f"UPDATE articles SET {col}=? WHERE id=?",[value,aid])
    # اگر پست قبلاً در کانال منتشر شده، تلاش می‌کنیم همان پیام هم اصلاح شود.
    rows=await db.execute("SELECT published_message_id,status,deep_token,title,channel_text FROM articles WHERE id=?",[aid])
    if rows and rows[0].get('status')=='published' and rows[0].get('published_message_id'):
        try:
            channel_id=await get_channel_id(db); token=rows[0].get('deep_token'); username=await get_runtime_bot_username(bot)
            deep=f"https://t.me/{username}?start=auto_{token}" if token and username else ''
            if field in {'title','channel'} and deep:
                latest=await db.execute("SELECT title,channel_text FROM articles WHERE id=?",[aid])
                cap=publication_caption(latest[0].get('title') or '',latest[0].get('channel_text') or '',deep)
                try: await bot.edit_message_caption(chat_id=channel_id,message_id=int(rows[0]['published_message_id']),caption=cap,parse_mode='HTML')
                except Exception:
                    try: await bot.edit_message_text(chat_id=channel_id,message_id=int(rows[0]['published_message_id']),text=cap,parse_mode='HTML')
                    except Exception: pass
        except Exception: pass
    await state.set_state(BotStates.idle)
    # Return to article panel via a fresh bot message to avoid losing the parent navigation.
    cb=type('C',(),{})(); cb.message=type('M',(),{})(); cb.message.chat=message.chat; cb.message.message_id=data.get('parent_message_id',0)
    await message.answer(f"✅ {field} محتوای #{aid} ویرایش شد.",reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='📄 مدیریت همین محتوا',callback_data=f'auto_art_{aid}')],[InlineKeyboardButton(text='🔙 محتوا و داده‌ها',callback_data='auto_content_db')]]))

@router.callback_query(F.data.regexp(r'^auto_art_delete_(\d+)$'))
async def auto_art_delete(call:CallbackQuery):
    aid=int(call.data.split('_')[-1])
    kb=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🗑️ بله، حذف شود',callback_data=f'auto_art_delete_yes_{aid}')],[InlineKeyboardButton(text='↩️ لغو',callback_data=f'auto_art_{aid}')]])
    await call.message.edit_text(f'⚠️ <b>حذف محتوای #{aid}</b>\n\nاین عمل مقاله، صف و ارتباط آن با منبع را از چرخه دوباره‌کاری خارج می‌کند. ادامه می‌دهی؟',parse_mode='HTML',reply_markup=kb); await call.answer()

@router.callback_query(F.data.regexp(r'^auto_art_delete_yes_(\d+)$'))
async def auto_art_delete_yes(call:CallbackQuery,db:D1Database):
    aid=int(call.data.split('_')[-1])
    await db.execute("UPDATE source_items SET status='discarded',article_id=NULL WHERE article_id=?",[aid])
    await db.execute("DELETE FROM publication_queue WHERE article_id=?",[aid])
    await db.execute("DELETE FROM articles WHERE id=?",[aid])
    await call.message.edit_text('🗑️ <b>محتوا حذف شد.</b>',parse_mode='HTML',reply_markup=automation_content_db_kb()); await call.answer('حذف شد')


@router.channel_post()
async def on_channel_post(message: Message, db: D1Database):
    configured_channel = await get_channel_id(db)
    if not configured_channel or str(message.chat.id) != str(configured_channel):
        return
    rows = await db.execute("SELECT id FROM articles WHERE published_message_id=?", [message.message_id])
    if rows:
        return
    now = datetime.now(timezone.utc).isoformat()
    await set_setting(db, "last_manual_channel_post_at", now)
    await db.execute("INSERT INTO manual_channel_events(message_id, created_at) VALUES(?,?)", [message.message_id, now])


# ============================================================
# پردازش رویدادهای کلیک روی کیبوردهای شیشه‌ای (Callback Queries)
# ============================================================
@router.callback_query(F.data.startswith("alike_") | F.data.startswith("adis_"))
async def process_article_voting(call: CallbackQuery, db: D1Database):
    parts=call.data.split("_"); new_vote="like" if parts[0]=="alike" else "dislike"; article_id=int(parts[1]); uid=call.from_user.id
    try:
        existing=await db.execute("SELECT vote_type FROM user_content_votes WHERE user_id=? AND content_type='article' AND content_id=?",[uid,article_id])
        if existing and existing[0].get('vote_type')==new_vote:
            await db.execute("DELETE FROM user_content_votes WHERE user_id=? AND content_type='article' AND content_id=?",[uid,article_id]); msg="🔄 رأی حذف شد"
        elif existing:
            await db.execute("UPDATE user_content_votes SET vote_type=? WHERE user_id=? AND content_type='article' AND content_id=?",[new_vote,uid,article_id]); msg="🔄 رأی تغییر کرد"
        else:
            await db.execute("INSERT INTO user_content_votes(user_id,content_type,content_id,vote_type,created_at) VALUES(?,?,?,?,?)",[uid,'article',article_id,new_vote,datetime.now(timezone.utc).isoformat()]); msg="✅ ثبت شد"
        likes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='like'",[article_id]))[0].get('c',0)
        dislikes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='dislike'",[article_id]))[0].get('c',0)
        saved=bool(await db.execute("SELECT 1 FROM user_content_saves WHERE user_id=? AND content_type='article' AND content_id=?",[uid,article_id]))
        await call.message.edit_reply_markup(reply_markup=get_article_inline_kb(article_id,likes,dislikes,saved)); await call.answer(msg)
    except Exception as exc:
        logger.exception("article vote failed: %s",exc); await call.answer("❌ ثبت واکنش انجام نشد",show_alert=True)

@router.callback_query(F.data.startswith("asave_"))
async def process_article_save_action(call: CallbackQuery):
    article_id=int(call.data.split("_")[1]); await call.answer(); await call.message.edit_reply_markup(reply_markup=get_save_to_folder_kb("article",article_id,f"article_actions_{article_id}"))

@router.callback_query(F.data.startswith("aunsave_"))
async def process_article_unsave_action(call: CallbackQuery, db: D1Database):
    article_id=int(call.data.split("_")[1]); uid=call.from_user.id
    try:
        await db.execute("DELETE FROM user_content_saves WHERE user_id=? AND content_type='article' AND content_id=?",[uid,article_id])
        likes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='like'",[article_id]))[0].get('c',0)
        dislikes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='dislike'",[article_id]))[0].get('c',0)
        await call.message.edit_reply_markup(reply_markup=get_article_inline_kb(article_id,likes,dislikes,False)); await call.answer("🗑️ از ذخیره‌ها حذف شد")
    except Exception as exc:
        logger.exception("article unsave failed: %s",exc); await call.answer("❌ حذف نشد",show_alert=True)

@router.callback_query(F.data.startswith("usave_"))
async def process_unified_folder_save(call: CallbackQuery, db: D1Database):
    parts=call.data.split("_")
    if len(parts)!=4: return await call.answer("❌ خطا",show_alert=True)
    _,ctype,cid_str,folder=parts; cid=int(cid_str); uid=call.from_user.id
    try:
        await db.execute("INSERT OR REPLACE INTO user_content_saves(user_id,content_type,content_id,folder,created_at) VALUES(?,?,?,?,?)",[uid,ctype,cid,folder,datetime.now(timezone.utc).isoformat()])
        if ctype=='article':
            likes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='like'",[cid]))[0].get('c',0)
            dislikes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='dislike'",[cid]))[0].get('c',0)
            await call.message.edit_reply_markup(reply_markup=get_article_inline_kb(cid,likes,dislikes,True))
        else:
            rows=await db.execute("SELECT likes,dislikes FROM posts WHERE id=?",[cid]); p=rows[0] if rows else {}
            await call.message.edit_reply_markup(reply_markup=get_post_inline_kb(cid,p.get('likes',0),p.get('dislikes',0),True))
        await call.answer(f"✅ در {FOLDER_NAMES.get(folder,folder)} ذخیره شد")
    except Exception as exc:
        logger.exception("save failed: %s",exc); await call.answer("❌ ذخیره‌سازی انجام نشد",show_alert=True)

@router.callback_query(F.data.startswith("article_actions_"))
async def article_actions(call: CallbackQuery, db: D1Database):
    article_id=int(call.data.split("_")[2]); uid=call.from_user.id
    likes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='like'",[article_id]))[0].get('c',0)
    dislikes=(await db.execute("SELECT COUNT(*) c FROM user_content_votes WHERE content_type='article' AND content_id=? AND vote_type='dislike'",[article_id]))[0].get('c',0)
    saved=bool(await db.execute("SELECT 1 FROM user_content_saves WHERE user_id=? AND content_type='article' AND content_id=?",[uid,article_id]))
    await call.message.edit_reply_markup(reply_markup=get_article_inline_kb(article_id,likes,dislikes,saved)); await call.answer()

@router.callback_query(F.data.startswith("like_") | F.data.startswith("dis_"))
async def process_post_voting(call: CallbackQuery, db: D1Database):
    parts = call.data.split("_")
    new_vote = "like" if parts[0] == "like" else "dislike"
    post_id = int(parts[1])
    user_id = call.from_user.id
    
    vote_rows = await db.execute("SELECT vote_type FROM user_content_votes WHERE user_id = ? AND content_type='post' AND content_id = ?", [user_id, post_id])
    response_text = ""
    
    try:
        if not vote_rows:
            await db.execute_batch([
                {"sql": "INSERT INTO user_content_votes(user_id,content_type,content_id,vote_type,created_at) VALUES(?,?,?,?,?)", "params": [user_id, "post", post_id, new_vote, datetime.now(timezone.utc).isoformat()]},
                {"sql": f"UPDATE posts SET {new_vote}s = {new_vote}s + 1 WHERE id = ?", "params": [post_id]}
            ])
            response_text = "✅ رأی خفنت ثبت شد! 😎"
        else:
            current_vote = vote_rows[0].get("vote_type")
            if current_vote == new_vote:
                await db.execute_batch([
                    {"sql": "DELETE FROM user_content_votes WHERE user_id = ? AND content_type='post' AND content_id = ?", "params": [user_id, post_id]},
                    {"sql": f"UPDATE posts SET {new_vote}s = {new_vote}s - 1 WHERE id = ?", "params": [post_id]}
                ])
                response_text = "🔄 رأیت رو پس گرفتی! 🔙"
            else:
                await db.execute_batch([
                    {"sql": "UPDATE user_content_votes SET vote_type = ? WHERE user_id = ? AND content_type='post' AND content_id = ?", "params": [new_vote, user_id, post_id]},
                    {"sql": f"UPDATE posts SET {new_vote}s = {new_vote}s + 1, {current_vote}s = {current_vote}s - 1 WHERE id = ?", "params": [post_id]}
                ])
                response_text = "🔄 رأیت با موفقیت تغییر کرد!"
    except Exception:
        response_text = "❌ خطا در ثبت رأی"
        
    await call.answer(response_text, show_alert=True)
    
    p_rows = await db.execute("SELECT likes, dislikes FROM posts WHERE id = ?", [post_id])
    if p_rows:
        p = p_rows[0]
        s_rows = await db.execute("SELECT folder FROM user_content_saves WHERE user_id = ? AND content_type='post' AND content_id = ?", [user_id, post_id])
        kb = get_post_inline_kb(post_id, p.get("likes", 0), p.get("dislikes", 0), len(s_rows) > 0)
        try:
            await call.message.edit_reply_markup(reply_markup=kb)
        except Exception:
            pass

@router.callback_query(F.data.startswith("save_"))
async def process_save_action(call: CallbackQuery):
    post_id = int(call.data.split("_")[1])
    try:
        await call.message.edit_reply_markup(reply_markup=get_save_to_folder_kb("post",post_id,f"post_actions_{post_id}"))
    except Exception:
        pass
    await call.answer()

@router.callback_query(F.data.startswith("fsave_"))
async def process_folder_save(call: CallbackQuery, db: D1Database):
    parts=call.data.split("_")
    post_id=int(parts[1]); folder=parts[2]; user_id=call.from_user.id
    try:
        await db.execute("INSERT OR REPLACE INTO user_content_saves(user_id,content_type,content_id,folder,created_at) VALUES(?,?,?,?,?)",[user_id,"post",post_id,folder,datetime.now(timezone.utc).isoformat()])
        p_rows=await db.execute("SELECT likes,dislikes FROM posts WHERE id=?",[post_id])
        p=p_rows[0] if p_rows else {}
        await call.answer(f"✅ در {FOLDER_NAMES.get(folder,folder)} ذخیره شد",show_alert=True)
        await call.message.edit_reply_markup(reply_markup=get_post_inline_kb(post_id,p.get('likes',0),p.get('dislikes',0),True))
    except Exception:
        await call.answer("❌ خطا در ذخیره‌سازی",show_alert=True)

@router.callback_query(F.data.startswith("unsave_"))
async def process_unsave_action(call: CallbackQuery, db: D1Database):
    post_id = int(call.data.split("_")[1])
    user_id = call.from_user.id
    
    try:
        await db.execute("DELETE FROM user_content_saves WHERE user_id = ? AND content_type='post' AND content_id = ?", [user_id, post_id])
        await call.answer("🗑️ مطلب از ذخیره‌هات پاک شد!", show_alert=True)
        
        p_rows = await db.execute("SELECT likes, dislikes FROM posts WHERE id = ?", [post_id])
        if p_rows:
            p = p_rows[0]
            kb = get_post_inline_kb(post_id, p.get("likes", 0), p.get("dislikes", 0), False)
            try:
                await call.message.edit_reply_markup(reply_markup=kb)
            except Exception:
                pass
    except Exception:
        await call.answer("❌ خطا در حذف", show_alert=True)

@router.callback_query(F.data.startswith("f_view_"))
async def process_view_saved_folder(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    folder = call.data.split("_")[2]
    user_id = call.from_user.id
    state_data = await state.get_data()
    
    if state_data.get("cached_folder") == folder and state_data.get("cached_list"):
        cached_list = state_data["cached_list"]
        await call.answer()
        await state.update_data(current_folder=folder, current_index=0, current_list=cached_list)
        p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [cached_list[0]])
        if p_rows:
            kb = get_saved_folder_pagination_kb(cached_list[0], folder, 0)
            await send_post_content(bot, call.message.chat.id, p_rows[0], kb)
        return
        
    rows = await db.execute(
        """SELECT posts.id FROM user_content_saves s JOIN posts ON s.content_id = posts.id AND s.content_type='post'
           WHERE s.user_id = ? AND s.folder = ? AND posts.deleted = 0
           ORDER BY posts.id DESC LIMIT 30""",
        [user_id, folder]
    )
    folder_display = FOLDER_NAMES.get(folder, folder)
    if not rows:
        await call.answer(f"📭 {folder_display} فعلاً خالیه! برو از کانال چند تا مطلب خفن توش ذخیره کن 🕸️", show_alert=True)
    else:
        post_ids = [r["id"] for r in rows]
        await state.update_data(cached_folder=folder, cached_list=post_ids, current_folder=folder, current_index=0, current_list=post_ids)
        await call.answer()
        
        post_id = post_ids[0]
        p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [post_id])
        if p_rows:
            kb = get_saved_folder_pagination_kb(post_id, folder, 0)
            await send_post_content(bot, call.message.chat.id, p_rows[0], kb)

@router.callback_query(F.data.startswith("fpg_"))
async def process_folder_pagination(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    parts = call.data.split("_")
    direction = parts[1]
    folder = parts[2]
    current_index = int(parts[3])
    
    state_data = await state.get_data()
    lst = state_data.get("current_list", [])
    if lst and folder:
        new_index = current_index + 1 if direction == "next" else current_index - 1
        new_index = max(0, min(new_index, len(lst) - 1))
        
        if new_index == current_index:
            await call.answer("🚧 رسیدی به انتهای لیست!")
        else:
            await call.answer()
            post_id = lst[new_index]
            await state.update_data(current_index=new_index)
            
            p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [post_id])
            if p_rows:
                post = p_rows[0]
                kb = get_saved_folder_pagination_kb(post_id, folder, new_index)
                if post.get("file_id") and post.get("media_type"):
                    try:
                        await call.message.delete()
                    except Exception:
                        pass
                    await send_post_content(bot, call.message.chat.id, post, kb)
                else:
                    try:
                        await call.message.edit_text(text=post.get("text") or "", reply_markup=kb)
                    except Exception:
                        pass

@router.callback_query(F.data.startswith("f_srch_"))
async def process_f_search_button(call: CallbackQuery, state: FSMContext):
    folder = call.data.split("_")[2]
    state_data = await state.get_data()
    
    now = time.time() * 1000
    WINDOW_MS = 8 * 60 * 60 * 1000
    search_count = state_data.get("search_count", 0)
    window_start = state_data.get("search_window_start", 0)
    
    if now - window_start > WINDOW_MS:
        search_count = 0
        window_start = 0
        
    if search_count >= 5:
        await call.answer("🛑 به دلیل کمبود منابع در هر 8 ساعت قادر به تنها 5 بار جستوجو هستید", show_alert=True)
        unlock_time_ms = window_start + WINDOW_MS
        tehran_tz = pytz.timezone("Asia/Tehran")
        unlock_dt = datetime.fromtimestamp(unlock_time_ms / 1000, tehran_tz)
        time_str = unlock_dt.strftime("%H:%M")
        day_str = "امروز" if unlock_dt.date() == datetime.now(tehran_tz).date() else "فردا"
        
        await call.message.answer(f"⏱️ موتور جستجوی اختصاصی شما {day_str} ساعت {time_str} فعال میشه\n\n تا اون موقع می‌تونی دستی پوشه‌هات رو ورق بزنی ! 🕵️‍♂️")
        return
        
    await state.set_state(BotStates.user_search_folder)
    await state.update_data(folder=folder)
    folder_display = FOLDER_NAMES.get(folder, folder)
    await call.message.answer(f"🔍 کلمات یا واژه‌ای که می‌دونی تو پوشه {folder_display} ذخیره کردی رو بفرست تا برات سرچش کنم 🕵️‍♂️")
    await call.answer()

@router.callback_query(F.data.startswith("fspg_"))
async def process_folder_search_pagination(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    parts = call.data.split("_")
    direction = parts[1]
    folder = parts[2]
    current_index = int(parts[3])
    
    state_data = await state.get_data()
    search_ids = state_data.get("search_ids", [])
    if search_ids and folder:
        new_index = current_index + 1 if direction == "next" else current_index - 1
        new_index = max(0, min(new_index, len(search_ids) - 1))
        
        if new_index == current_index:
            await call.answer("🚧 رسیدی به انتهای نتایج!")
        else:
            await call.answer()
            post_id = search_ids[new_index]
            p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [post_id])
            if p_rows:
                post = p_rows[0]
                kb = get_saved_folder_search_pagination_kb(post_id, folder, new_index)
                if post.get("file_id") and post.get("media_type"):
                    try:
                        await call.message.delete()
                    except Exception:
                        pass
                    await send_post_content(bot, call.message.chat.id, post, kb)
                else:
                    try:
                        await call.message.edit_text(text=post.get("text") or "", reply_markup=kb)
                    except Exception:
                        pass

@router.callback_query(F.data.startswith("ask_del_"))
async def process_ask_deletion(call: CallbackQuery, state: FSMContext):
    parts = call.data.split("_")
    post_id = int(parts[2])
    folder = parts[3]
    
    await state.update_data(pending_delete={"post_id": post_id, "folder": folder})
    kb = get_confirm_delete_kb(post_id, folder)
    try:
        await call.message.edit_reply_markup(reply_markup=kb)
    except Exception:
        await call.message.answer("آیا مطمئنی می‌خوای این مطلب رو از پوشه‌ات پاک کنی؟ 🤔", reply_markup=kb)
    await call.answer()

@router.callback_query(F.data.startswith("cancel_delete_"))
async def process_cancel_deletion(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    folder = call.data.split("_")[2]
    await call.answer("✅ عملیات لغو شد.", show_alert=True)
    try:
        await call.message.delete()
    except Exception:
        pass
        
    state_data = await state.get_data()
    lst = state_data.get("current_list", [])
    idx = state_data.get("current_index", 0)
    
    if lst and idx < len(lst):
        post_id = lst[idx]
        p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [post_id])
        if p_rows:
            kb = get_saved_folder_pagination_kb(post_id, folder, idx)
            await send_post_content(bot, call.message.chat.id, p_rows[0], kb)
    else:
        user_id = call.from_user.id
        rows = await db.execute(
            """SELECT posts.id FROM user_content_saves s JOIN posts ON s.content_id = posts.id AND s.content_type='post'
               WHERE s.user_id = ? AND s.folder = ? AND posts.deleted = 0
               ORDER BY posts.id DESC LIMIT 30""",
            [user_id, folder]
        )
        if rows:
            post_id = rows[0]["id"]
            kb = get_saved_folder_pagination_kb(post_id, folder, 0)
            await send_post_content(bot, call.message.chat.id, rows[0], kb)
        else:
            await call.message.answer("📭 این پوشه خالی شد.")

@router.callback_query(F.data.startswith("f_del_save_"))
async def process_f_del_save(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    parts = call.data.split("_")
    post_id = int(parts[3])
    folder = parts[4]
    user_id = call.from_user.id
    
    try:
        await db.execute("DELETE FROM user_content_saves WHERE user_id = ? AND content_type='post' AND content_id = ?", [user_id, post_id])
        await call.answer("🗑️ مطلب با موفقیت حذف شد!", show_alert=True)
        try:
            await call.message.delete()
        except Exception:
            pass
            
        rows = await db.execute(
            """SELECT posts.id FROM user_content_saves s JOIN posts ON s.content_id = posts.id AND s.content_type='post'
               WHERE s.user_id = ? AND s.folder = ? AND posts.deleted = 0
               ORDER BY posts.id DESC LIMIT 30""",
            [user_id, folder]
        )
        if rows:
            post_ids = [r["id"] for r in rows]
            await state.update_data(current_list=post_ids, current_index=0)
            new_post_id = post_ids[0]
            p_rows = await db.execute("SELECT text, file_id, media_type FROM posts WHERE id = ?", [new_post_id])
            if p_rows:
                kb = get_saved_folder_pagination_kb(new_post_id, folder, 0)
                await send_post_content(bot, call.message.chat.id, p_rows[0], kb)
        else:
            folder_display = FOLDER_NAMES.get(folder, folder)
            await call.message.answer(f"📭 پوشه {folder_display} کاملاً خالی شد.")
    except Exception:
        await call.answer("❌ خطا در حذف", show_alert=True)

# ============================================================
# بخش‌های خلاصه لیست و مدیریت پست‌ها برای ادمین (Callback Queries)
# ============================================================
async def send_admin_all_posts_page(bot: Bot,chat_id:int,rows:List[Dict[str,Any]],page:int,total_pages:int,total_count:int,edit_message_id:Optional[int]=None):
    text="📋 <b>همه محتواها</b>\n\n"+f"صفحه {page+1}/{total_pages} · مجموع {total_count}\n"
    buttons=[]
    for p in rows:
        preview=html.escape(strip_html_text(p.get("text") or "")[:60].replace("\n"," "))
        text+=f"\n<b>#{p['id']}</b> {preview}"
        buttons.append([InlineKeyboardButton(text=f"✏️ #{p['id']}",callback_data=f"aedit_{p['id']}"),
                        InlineKeyboardButton(text=f"🗑 #{p['id']}",callback_data=f"adelete_{p['id']}")])
    buttons.append([InlineKeyboardButton(text="⏮",callback_data=f"adm_all_page_prev_{page}"),InlineKeyboardButton(text=f"{page+1}/{total_pages}",callback_data="noop"),InlineKeyboardButton(text="⏭",callback_data=f"adm_all_page_next_{page}")])
    buttons.append([InlineKeyboardButton(text="🔙 مدیریت محتوا",callback_data="admin_content")])
    kb=InlineKeyboardMarkup(inline_keyboard=buttons)
    if edit_message_id:
        try:
            await bot.edit_message_text(chat_id=chat_id,message_id=edit_message_id,text=text,parse_mode="HTML",reply_markup=kb); return
        except Exception: pass
    await bot.send_message(chat_id,text,parse_mode="HTML",reply_markup=kb)

@router.callback_query(F.data == "adm_view_all")
async def callback_admin_view_all(call: CallbackQuery):
    await call.message.edit_text("📋 <b>همه محتواها</b>\n\nبرای نمایش ادامه بده:",parse_mode="HTML",reply_markup=get_admin_view_all_confirm_kb())
    await call.answer()

@router.callback_query(F.data == "adm_view_all_cancel")
async def callback_admin_view_all_cancel(call: CallbackQuery):
    await call.message.edit_text("📁 <b>مدیریت محتوای هسته</b>",parse_mode="HTML",reply_markup=get_content_management_kb())
    await call.answer()

@router.callback_query(F.data == "adm_view_all_confirm")
async def callback_admin_view_all_confirm(call:CallbackQuery,state:FSMContext,db:D1Database,bot:Bot):
    per_page=10
    total=(await db.execute("SELECT COUNT(*) c FROM posts WHERE deleted=0"))[0].get("c",0)
    pages=max(1,math.ceil(total/per_page))
    rows=await db.execute("SELECT id,text,likes,dislikes,views,file_id,media_type FROM posts WHERE deleted=0 ORDER BY id DESC LIMIT ? OFFSET ?",[per_page,0])
    await state.set_state(BotStates.admin_view_all); await state.update_data(all_posts_page=0,all_per_page=per_page,all_total_pages=pages,all_total_count=total)
    if rows: await send_admin_all_posts_page(bot,call.message.chat.id,rows,0,pages,total,call.message.message_id)
    else: await call.message.edit_text("📭 محتوایی وجود ندارد.",reply_markup=get_content_management_kb())
    await call.answer()

@router.callback_query(F.data.startswith("adm_all_page_"))
async def callback_admin_all_posts_page(call:CallbackQuery,state:FSMContext,db:D1Database,bot:Bot):
    parts=call.data.split("_"); direction=parts[3]; current=int(parts[4]); data=await state.get_data()
    per=int(data.get("all_per_page",10)); total_pages=int(data.get("all_total_pages",1)); total=int(data.get("all_total_count",0))
    new=max(0,min(current+(1 if direction=="next" else -1),total_pages-1))
    rows=await db.execute("SELECT id,text,likes,dislikes,views,file_id,media_type FROM posts WHERE deleted=0 ORDER BY id DESC LIMIT ? OFFSET ?",[per,new*per])
    await state.update_data(all_posts_page=new)
    if rows: await send_admin_all_posts_page(bot,call.message.chat.id,rows,new,total_pages,total,call.message.message_id)
    await call.answer()

@router.callback_query(F.data == "adm_search_text")
async def callback_admin_search_text(call:CallbackQuery,state:FSMContext):
    await state.set_state(BotStates.admin_search_word); await state.update_data(search_ids=[],search_index=0)
    await call.message.edit_text("🔍 <b>جستجو</b>\n\nکلمه کلیدی یا شماره پست را بفرست.",parse_mode="HTML",reply_markup=get_exit_menu())
    await call.answer()

@router.message(F.chat.id==ADMIN_ID,StateFilter(BotStates.admin_search_word))
async def process_admin_search_word(message:Message,state:FSMContext,db:D1Database,bot:Bot):
    q=(message.text or "").strip()
    if not q: return
    rows=await db.execute("SELECT id FROM posts WHERE id=? AND deleted=0" if q.isdigit() else "SELECT id FROM posts WHERE text LIKE ? AND deleted=0 ORDER BY id DESC LIMIT 50",[int(q)] if q.isdigit() else [f"%{q}%"])
    ids=[r["id"] for r in rows]
    if not ids:
        await message.answer("❌ چیزی پیدا نشد.",reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔍 دوباره",callback_data="adm_search_text"),InlineKeyboardButton(text="🔙 مدیریت محتوا",callback_data="admin_content")]])); return
    await state.update_data(search_ids=ids,search_index=0); await state.set_state(BotStates.admin_search_word)
    p=await db.execute("SELECT id,text,file_id,media_type FROM posts WHERE id=?",[ids[0]])
    if p: await bot.send_message(message.chat.id,"نتیجه:",reply_markup=get_admin_search_pagination_kb(ids[0],0)); await send_post_content(bot,message.chat.id,p[0],get_admin_search_pagination_kb(ids[0],0))

@router.callback_query(F.data.startswith("asearch_"))
async def callback_admin_search_pagination(call:CallbackQuery,state:FSMContext,db:D1Database,bot:Bot):
    parts=call.data.split("_"); direction=parts[1]; current=int(parts[2]); data=await state.get_data(); ids=data.get("search_ids",[])
    if not ids: await call.answer("جستجو تمام شده است",show_alert=True); return
    new=max(0,min(current+(1 if direction=="next" else -1),len(ids)-1)); await state.update_data(search_index=new)
    p=await db.execute("SELECT id,text,file_id,media_type FROM posts WHERE id=?",[ids[new]])
    if p:
        kb=get_admin_search_pagination_kb(ids[new],new)
        if p[0].get("file_id"):
            try: await call.message.delete()
            except Exception: pass
            await send_post_content(bot,call.message.chat.id,p[0],kb)
        else:
            await call.message.edit_text(p[0].get("text") or "",reply_markup=kb)
    await call.answer()

@router.callback_query(F.data.startswith("aedit_"))
async def admin_edit_post_start(call:CallbackQuery,state:FSMContext,db:D1Database):
    pid=int(call.data.split("_")[1]); rows=await db.execute("SELECT id,text FROM posts WHERE id=? AND deleted=0",[pid])
    if not rows: await call.answer("پست پیدا نشد",show_alert=True); return
    await state.set_state(BotStates.admin_post_edit); await state.update_data(edit_post_id=pid,parent_message_id=call.message.message_id)
    await call.message.edit_text(f"✏️ <b>ویرایش #{pid}</b>\n\nمتن جدید را بفرست.",parse_mode="HTML",reply_markup=get_exit_menu()); await call.answer()

@router.message(F.chat.id==ADMIN_ID,StateFilter(BotStates.admin_post_edit))
async def admin_edit_post_input(message:Message,state:FSMContext,db:D1Database):
    data=await state.get_data(); pid=int(data["edit_post_id"]); new_text=message.text or message.caption or ""
    if not new_text: await message.answer("❌ متن خالی است."); return
    await db.execute("UPDATE posts SET text=? WHERE id=?",[new_text,pid]); await state.set_state(BotStates.idle)
    await message.answer(f"✅ پست #{pid} ویرایش شد.",reply_markup=get_content_management_kb())

@router.callback_query(F.data.startswith("astats_"))
async def callback_admin_search_post_stats(call:CallbackQuery,db:D1Database):
    pid=int(call.data.split("_")[1]); p=await db.execute("SELECT likes,dislikes,views FROM posts WHERE id=?",[pid])
    if not p: await call.answer("پست پیدا نشد",show_alert=True); return
    await call.answer(f"👁 {p[0].get('views',0)} | 👍 {p[0].get('likes',0)} | 👎 {p[0].get('dislikes',0)}",show_alert=True)

@router.callback_query(F.data.startswith("adelete_"))
async def callback_admin_delete_post(call:CallbackQuery,db:D1Database):
    pid=int(call.data.split("_")[1]); p=await db.execute("SELECT text FROM posts WHERE id=? AND deleted=0",[pid])
    if not p: await call.answer("پست پیدا نشد",show_alert=True); return
    kb=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🗑️ تأیید حذف",callback_data=f"adelete_confirm_{pid}"),InlineKeyboardButton(text="↩️ لغو",callback_data="admin_content")]])
    await call.message.edit_text(f"⚠️ <b>حذف #{pid}</b>\n\nآیا مطمئنی؟",parse_mode="HTML",reply_markup=kb); await call.answer()

@router.callback_query(F.data.startswith("adelete_confirm_"))
async def callback_admin_delete_post_confirm(call:CallbackQuery,db:D1Database):
    pid=int(call.data.split("_")[-1]); await db.execute("UPDATE posts SET deleted=1 WHERE id=?",[pid])
    await call.message.edit_text("🗑️ حذف شد.",reply_markup=get_content_management_kb()); await call.answer("حذف شد")


# ============================================================
# تایید ارسال‌های ادمین و راهنما (Callback Queries)
# ============================================================
@router.callback_query(F.data == "help_more")
async def callback_help_more(call: CallbackQuery):
    first_name = call.from_user.first_name or "دوست"
    detailed_text = f"""ببین {first_name} جان، داستان از این قراره! 🤖

ما اینجا یه پایگاه داده خفن و پویا از دنیای تکنولوژی، هوش مصنوعی و امنیت سایبری ساختیم.\n\n🚀 حتماً دیدی که تو کانال @TechNowAi بعضی وقتا فقط یه خلاصه کوچیک از خبرا یا آموزش‌ها رو می‌ذاریم؛ دلیلش اینه که تلگرام شلوغ نشه! اما وقتی روی لینک‌ها می‌زنی، دقیقاً هدایت میشی به همینجا تا متن کامل، جامع و تخصصی رو با خیال راحت مطالعه کنی. 📖🧐

حالا اینجا چه امکاناتی داری؟

۱. 💡 رأی‌گیری هوشمند: می‌تونی به هر پست رأی (👍 یا 👎) بدی. اینجوری ما می‌فهمیم سلیقه‌ات چیه و مطالب بهتری برات آماده می‌کنیم!

۲. 📂 پوشه‌بندی اختصاصی: یه مطلب خیلی برات کاربردی بود؟ با یه کلیک 💾 ذخیره‌اش کن و دقیقاً بندازش تو پوشه مخصوص خودش (مثلاً هوش مصنوعی یا امنیت) تا هر وقت بهش نیاز داشتی، تو سه‌سوت پیداش کنی!

۳. 🔍 جستجوی پیشرفته: تو پوشه‌هات دنبال یه کلمه خاص می‌گردی؟ دکمه جستجو رو بزن و کلمه‌ات رو بفرست تا ربات کل آرشیوت رو زیر و رو کنه!

۴. 🤖 هوش مصنوعی: با انتخاب دکمه هوش مصنوعی از منو، میتونی سوالاتت رو بپرسی یا فایل متنی/کد بفرستی تا پردازش بشه.

۵. 💬 ارتباط مستقیم: اگه ایده جذابی داشتی یا جایی به مشکل خوردی، مستقیم با خود مدیریت چت کن.

🔄 هر جا حس کردی ربات یه ذره گیج می‌زنه، فقط یه /start بفرست تا مثل روز اول سرحال بشه! ⚡️

📜 یادت نره که این ابزار برای پیشرفت و یادگیری راحت‌تر تو طراحی شده، پس حسابی ازش استفاده کن! 🎯

📌 راستی این ربات مخصوص کانال خودمون هست و همینجا کارایی داره خلاصه که ما تلاش میکنیم تا در کمک به علوم فناوری و هوش مصنوعی و امنیت سایبری برای فارسی‌زبانان سهیم باشیم ❤️

نسخه ربات: v1.5.0 🏷️"""
    try:
        await call.message.edit_text(text=detailed_text, reply_markup=get_help_got_it_kb())
    except Exception:
        pass
    await call.answer()

@router.callback_query(F.data == "help_got_it")
async def callback_help_got_it(call: CallbackQuery):
    try:
        await call.message.delete()
    except Exception:
        pass
    await call.answer("🚀 بزن بریم سراغ یادگیری!")

@router.callback_query(F.data == "conf_add_yes")
async def callback_confirm_add_post_yes(call: CallbackQuery, state: FSMContext, db: D1Database):
    state_data = await state.get_data()
    temp_text = state_data.get("temp_text")
    temp_file_id = state_data.get("temp_file_id")
    temp_media_type = state_data.get("temp_media_type")
    
    if temp_text or temp_file_id:
        try:
            res = await db.execute(
                "INSERT INTO posts(text, file_id, media_type) VALUES(?, ?, ?) RETURNING id",
                [temp_text, temp_file_id, temp_media_type]
            )
            post_id = None
            if res and isinstance(res, list) and len(res) > 0:
                post_id = res[0].get("id")
                
            if not post_id:
                last_id_rows = await db.execute("SELECT last_insert_rowid() as id")
                if last_id_rows:
                    post_id = last_id_rows[0].get("id")
                    
            await state.update_data(temp_text=None, temp_file_id=None, temp_media_type=None)
            await state.set_state(BotStates.idle)
            
            await call.message.answer(f"✅ آرشیو شد!\n🔗 لینک:\nhttps://t.me/{BOT_USERNAME}?start={post_id}")
            await call.answer("✅ ثبت شد!")
        except Exception as e:
            await call.answer(f"❌ خطا در ثبت: {e}", show_alert=True)
    else:
        await call.answer("❌ اطلاعات ناقص است", show_alert=True)

@router.callback_query(F.data == "conf_add_no")
async def callback_confirm_add_post_no(call: CallbackQuery, state: FSMContext):
    await state.update_data(temp_text=None, temp_file_id=None, temp_media_type=None)
    await state.set_state(BotStates.idle)
    await call.message.answer("❌ لغو شد.")
    await call.answer("لغو شد")

@router.callback_query(F.data == "conf_broad_yes")
async def callback_confirm_broadcast_yes(call: CallbackQuery, state: FSMContext, db: D1Database, bot: Bot):
    state_data = await state.get_data()
    temp_text = state_data.get("temp_text")
    temp_file_id = state_data.get("temp_file_id")
    temp_media_type = state_data.get("temp_media_type")
    
    if not temp_text and not temp_file_id:
        await call.answer("❌ اطلاعات ناقص است", show_alert=True)
        return
        
    users = await db.execute("SELECT id FROM users")
    if not users:
        await call.message.answer("⚠️ هیچ کاربری در دیتابیس وجود ندارد.")
        await call.answer()
        return
        
    await call.answer("🚀 ارسال همگانی شروع شد...")
    success_count, fail_count = 0, 0
    CHUNK_SIZE = 20
    
    async def send_to_user(bot_instance: Bot, uid: int, text: str, file: str, mtype: str):
        caption = text if len(text) <= 1024 else text[:1020] + "..."
        try:
            if mtype == "photo" and file:
                await bot_instance.send_photo(chat_id=uid, photo=file, caption=caption)
            elif mtype == "document" and file:
                await bot_instance.send_document(chat_id=uid, document=file, caption=caption)
            elif mtype == "video" and file:
                await bot_instance.send_video(chat_id=uid, video=file, caption=caption)
            elif mtype == "audio" and file:
                await bot_instance.send_audio(chat_id=uid, audio=file, caption=caption)
            else:
                safe_text = text if len(text) <= 4096 else text[:4090] + "..."
                await bot_instance.send_message(chat_id=uid, text=safe_text or "پیام همگانی")
            return True
        except Exception:
            return False

    for i in range(0, len(users), CHUNK_SIZE):
        chunk = users[i:i+CHUNK_SIZE]
        tasks = [send_to_user(bot, u["id"], temp_text, temp_file_id, temp_media_type) for u in chunk]
        results = await asyncio.gather(*tasks)
        success_count += sum(1 for r in results if r)
        fail_count += sum(1 for r in results if not r)
        await asyncio.sleep(0.1)
        
    await state.update_data(temp_text=None, temp_file_id=None, temp_media_type=None)
    await state.set_state(BotStates.idle)
    
    await call.message.answer(f"✅ ارسال همگانی انجام شد.\nموفق: {success_count} نفر\nناموفق: {fail_count} نفر")
    await call.answer("✅ ارسال همگانی کامل شد!")

@router.callback_query(F.data == "conf_broad_no")
async def callback_confirm_broadcast_no(call: CallbackQuery, state: FSMContext):
    await state.update_data(temp_text=None, temp_file_id=None, temp_media_type=None)
    await state.set_state(BotStates.idle)
    await call.message.answer("❌ ارسال همگانی لغو شد.")
    await call.answer("لغو شد")

@router.callback_query(F.data == "noop")
async def callback_noop_dummy(call: CallbackQuery):
    await call.answer()

# ============================================================
# متد اجرایی اصلی ربات (Startup & Main Polling)
# ============================================================
async def main():
    if not API_TOKEN:
        raise RuntimeError("TELEGRAM_BOT_TOKEN is not configured")
    if not (CF_ACCOUNT_ID and CF_DATABASE_ID and CF_API_TOKEN):
        raise RuntimeError("Cloudflare D1 environment variables are not fully configured")
    bot = Bot(token=API_TOKEN)
    global BOT_USERNAME
    try:
        bot_identity = await bot.get_me()
        if bot_identity.username:
            BOT_USERNAME = bot_identity.username
    except Exception:
        pass
    dp = Dispatcher(storage=MemoryStorage())
    
    db = D1Database(
        account_id=CF_ACCOUNT_ID,
        database_id=CF_DATABASE_ID,
        api_token=CF_API_TOKEN
    )
    await db.start()
    await get_http_session()
    dp["db"] = db
    
    await initialize_database(db)
    await migrate_unified_user_interactions(db)
    await initialize_automation_database(db)
    
    dp.include_router(router)
    
    automation_task = asyncio.create_task(automation_loop(db, bot))
    logger.info("Bot started successfully in Long Polling mode with content automation...")
    try:
        await dp.start_polling(bot)
    finally:
        automation_task.cancel()
        try:
            await automation_task
        except asyncio.CancelledError:
            pass
        await db.close()
        await close_http_session()
        await bot.session.close()

if __name__ == "__main__":
    asyncio.run(main())