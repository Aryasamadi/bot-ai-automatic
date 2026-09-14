# -*- coding: utf-8 -*-
""" 
NewsBot v3 — نسخه بهینه‌شده و تثبیت‌شده (Single-File)
"""
import os, re, json, html, time, random, asyncio, logging, sqlite3, hashlib, secrets, tempfile, threading, sys
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin, urlparse, parse_qsl, urlencode
import httpx, feedparser, trafilatura
from bs4 import BeautifulSoup
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, BotCommand
from telegram.constants import ParseMode, ChatType
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, ContextTypes, filters
from telegram.error import BadRequest, RetryAfter

# ============================================================
# تنظیمات محیطی
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
SUPER_ADMIN_IDS = {int(x) for x in os.getenv("SUPER_ADMIN_IDS", "0").split(",") if x.strip().isdigit()}
DB_FILE = os.getenv("DB_FILE", "newsbot.db")
DATA_TTL_HOURS = int(os.getenv("DATA_TTL_HOURS", "24"))
MAX_MEDIA_MB = int(os.getenv("MAX_MEDIA_MB", "50"))
MAX_MEDIA_BYTES = MAX_MEDIA_MB * 1024 * 1024
MAX_ARTICLE_CHARS = int(os.getenv("MAX_ARTICLE_CHARS", "28000"))
MAX_ARTICLE_PAGES = int(os.getenv("MAX_ARTICLE_PAGES", "3"))
CF_ACCOUNT_ID = os.getenv("CF_ACCOUNT_ID", "")
CF_KV_NAMESPACE_ID = os.getenv("CF_KV_NAMESPACE_ID", "")
CF_API_TOKEN = os.getenv("CF_API_TOKEN", "")
CF_ENABLED = bool(CF_ACCOUNT_ID and CF_KV_NAMESPACE_ID and CF_API_TOKEN)
DEFAULT_UTC_OFFSET = float(os.getenv("DEFAULT_UTC_OFFSET", "3.5"))   # تهران
BOT_USERNAME = ""
NOTIFY_SUPER = None
NOTIFY_USER = None
UTC = timezone.utc
HTML = ParseMode.HTML
APP: Application = None
CAPTION_LIMIT, MSG_LIMIT = 1024, 4096
SOURCE_COOLDOWN_MIN = 10
MODEL_PROBE_MIN = 10
MIN_INTERVAL = 30
MAX_LOOKBACK = 48
MAX_PPC = 5
POST_LIMIT_DEFAULT = 700
BOT_FULL_MAX = 2500
LANGS = ("fa", "en")

AI_CONCURRENCY = int(os.getenv("AI_CONCURRENCY", "3"))
FETCH_CONCURRENCY = int(os.getenv("FETCH_CONCURRENCY", "8"))
CYCLE_CONCURRENCY = int(os.getenv("CYCLE_CONCURRENCY", "2"))
MAX_CYCLES_PER_TICK = int(os.getenv("MAX_CYCLES_PER_TICK", "4"))
TICK_SECONDS = int(os.getenv("TICK_SECONDS", "120"))
TEST_COOLDOWN_SEC = int(os.getenv("TEST_COOLDOWN_SEC", "120"))
CB_RATE = float(os.getenv("CB_RATE", "0.6"))

logging.basicConfig(format="%(asctime)s | %(levelname)s | %(message)s", level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("core")

# ============================================================
# ابزار زمان
TZ_ZONES = [("tehran", 3.5), ("istanbul", 3), ("dubai", 4), ("kabul", 4.5), ("karachi", 5), ("delhi", 5.5), ("moscow", 3), ("berlin", 1), ("london", 0),
            ("beijing", 8), ("tokyo", 9), ("sydney", 10), ("newyork", -5), ("losangeles", -8), ("saopaulo", -3), ("utc", 0)]

def now_utc(): return datetime.now(UTC)
def now_iso(): return now_utc().isoformat()
def parse_dt(s):
    if not s: return None
    try:
        d = datetime.fromisoformat(str(s).replace("Z", "+00:00"))
        return d if d.tzinfo else d.replace(tzinfo=UTC)
    except Exception: return None

def tz_of(off):
    try: return timezone(timedelta(hours=float(off)))
    except Exception: return timezone(timedelta(hours=DEFAULT_UTC_OFFSET))

def off_label(off):
    try: off = float(off)
    except Exception: off = DEFAULT_UTC_OFFSET
    h = int(abs(off)); m = int(round((abs(off) - h) * 60))
    return f"UTC{'+' if off >= 0 else '-'}{h:02d}:{m:02d}"

def utc_clock(): return now_utc().strftime("%H:%M")
def local_clock(off): return datetime.now(tz_of(off)).strftime("%H:%M")
def today_str(off=DEFAULT_UTC_OFFSET): return datetime.now(tz_of(off)).strftime("%Y-%m-%d")
def fmt_date(d, off=DEFAULT_UTC_OFFSET, with_time=False):
    if not d: return "—"
    if isinstance(d, str): d = parse_dt(d)
    return d.astimezone(tz_of(off)).strftime("%Y-%m-%d %H:%M" if with_time else "%Y-%m-%d") if d else "—"

def ago_text(iso, lang="fa"):
    d = parse_dt(iso)
    if not d: return "—"
    s = int((now_utc() - d).total_seconds())
    if lang == "en": return f"{s}s" if s < 60 else f"{s//60}m" if s < 3600 else f"{s//3600}h" if s < 86400 else f"{s//86400}d"
    return f"{s} ثانیه" if s < 60 else f"{s//60} دقیقه" if s < 3600 else f"{s//3600} ساعت" if s < 86400 else f"{s//86400} روز"

def url_hash(u): return hashlib.sha1(u.strip().encode()).hexdigest()[:20]

def parse_expiry(text):
    t = str(text).strip().translate(str.maketrans("۰۱۲۳۴۵۶۷۸۹", "0123456789"))
    if t.isdigit(): return (now_utc() + timedelta(days=int(t))).isoformat()
    m = re.match(r"^(\d{4})[-/](\d{1,2})[-/](\d{1,2})$", t)
    if not m: return None
    try: return datetime(int(m[1]), int(m[2]), int(m[3]), 23, 59, tzinfo=UTC).isoformat()
    except Exception: return None

# ============================================================
# محافظت در برابر فشار: قفل‌ها، سمافورها، محدودکننده‌ی نرخ
AI_SEM = asyncio.Semaphore(AI_CONCURRENCY)
FETCH_SEM = asyncio.Semaphore(FETCH_CONCURRENCY)
CYCLE_SEM = asyncio.Semaphore(CYCLE_CONCURRENCY)
_ch_locks, _rl = {}, {}

def ch_lock(cid):
    if cid not in _ch_locks: _ch_locks[cid] = asyncio.Lock()
    return _ch_locks[cid]

def purge_ch_lock(cid):
    _ch_locks.pop(cid, None)

def purge_model_lock(mid):
    _model_locks.pop(mid, None)

def rate_ok(key, min_gap):
    t = time.time(); last = _rl.get(key, 0)
    if t - last < min_gap: return False
    _rl[key] = t
    if len(_rl) > 5000:
        now_t = time.time()
        expired = [k for k, ts in _rl.items() if now_t - ts > 3600]
        for k in expired: _rl.pop(k, None)
    return True

def rate_free(key, min_gap): return (time.time() - _rl.get(key, 0)) >= min_gap
def rate_mark(key):
    _rl[key] = time.time()
    if len(_rl) > 5000:
        now_t = time.time()
        for k in [k for k, ts in _rl.items() if now_t - ts > 3600]: _rl.pop(k, None)

def rate_clear(key): _rl.pop(key, None)
def rate_left(key, min_gap): return max(0, int(min_gap - (time.time() - _rl.get(key, 0))))

# ============================================================
# دیتابیس با پشتیبانی امن
_conn, _lock = None, threading.RLock()
SCHEMA = """
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, username TEXT, name TEXT, role TEXT DEFAULT 'user', plan_id INTEGER, plan_expires TEXT, next_plan_id INTEGER, next_plan_days INTEGER, free_used INTEGER DEFAULT 0, banned INTEGER DEFAULT 0, lang TEXT, remind_key TEXT, premium INTEGER DEFAULT 0, created_at TEXT, last_seen TEXT);
CREATE TABLE IF NOT EXISTS plans(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, name_en TEXT, days INTEGER, daily_posts INTEGER, max_sources INTEGER, max_channels INTEGER, daily_tests INTEGER, price TEXT DEFAULT '', price_en TEXT DEFAULT '', description TEXT DEFAULT '', description_en TEXT DEFAULT '', is_free INTEGER DEFAULT 0, active INTEGER DEFAULT 1, sort INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS discounts(code TEXT PRIMARY KEY, percent INTEGER, expires TEXT, max_uses INTEGER DEFAULT 0, used INTEGER DEFAULT 0, active INTEGER DEFAULT 1, created_at TEXT);
CREATE TABLE IF NOT EXISTS channels(id INTEGER PRIMARY KEY AUTOINCREMENT, admin_id INTEGER, chat_id INTEGER, title TEXT, username TEXT, lock_code TEXT, verified_by INTEGER, created_at TEXT, settings TEXT);
CREATE TABLE IF NOT EXISTS sources(id INTEGER PRIMARY KEY AUTOINCREMENT, admin_id INTEGER, channel_id INTEGER, url TEXT, feed_url TEXT, title TEXT DEFAULT '', active INTEGER DEFAULT 1, bot_active INTEGER DEFAULT 1, api_url TEXT, api_key TEXT, api_note TEXT DEFAULT '', etag TEXT, last_modified TEXT, last_fetch TEXT, fail_count INTEGER DEFAULT 0, found_total INTEGER DEFAULT 0, last_error TEXT);
CREATE TABLE IF NOT EXISTS usage(admin_id INTEGER, day TEXT, posts INTEGER DEFAULT 0, tests INTEGER DEFAULT 0, PRIMARY KEY(admin_id, day));
CREATE TABLE IF NOT EXISTS articles(id INTEGER PRIMARY KEY AUTOINCREMENT, admin_id INTEGER, channel_id INTEGER, hash TEXT, url TEXT, title TEXT, source_id INTEGER, published_at TEXT, created_at TEXT, status TEXT, reason TEXT, score REAL, category TEXT, text TEXT, post_html TEXT, full_html TEXT, media TEXT, links TEXT, model TEXT, UNIQUE(channel_id, hash));
CREATE TABLE IF NOT EXISTS posted(channel_id INTEGER, hash TEXT, posted_at TEXT, PRIMARY KEY(channel_id, hash));
CREATE TABLE IF NOT EXISTS ai_models(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, kind TEXT, base_url TEXT, api_key TEXT, model TEXT, priority INTEGER DEFAULT 10, active INTEGER DEFAULT 1, status TEXT DEFAULT 'ok', fail_count INTEGER DEFAULT 0, last_error TEXT, last_ok TEXT, last_fail TEXT, ok_count INTEGER DEFAULT 0, temperature REAL DEFAULT 0.5, max_tokens INTEGER DEFAULT 2500);
CREATE TABLE IF NOT EXISTS deeplinks(key TEXT PRIMARY KEY, admin_id INTEGER, created_at TEXT, local_json TEXT);
CREATE TABLE IF NOT EXISTS kv_cache(key TEXT PRIMARY KEY, value TEXT, cached_at TEXT);
CREATE TABLE IF NOT EXISTS logs(id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, level TEXT, admin_id INTEGER, msg TEXT);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS support(user_id INTEGER PRIMARY KEY, open INTEGER DEFAULT 0, opened_at TEXT);
CREATE TABLE IF NOT EXISTS support_map(admin_id INTEGER, message_id INTEGER, user_id INTEGER, ts TEXT, PRIMARY KEY(admin_id, message_id));
CREATE TABLE IF NOT EXISTS pay_requests(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, plan_id INTEGER, status TEXT DEFAULT 'pending', created_at TEXT, receipt_chat INTEGER, receipt_msg INTEGER, note TEXT, decided_at TEXT, discount TEXT, final_price TEXT);
CREATE INDEX IF NOT EXISTS idx_art_ch_status ON articles(channel_id, status);
CREATE INDEX IF NOT EXISTS idx_art_created ON articles(created_at);
CREATE INDEX IF NOT EXISTS idx_src_ch ON sources(channel_id);
CREATE INDEX IF NOT EXISTS idx_logs_admin ON logs(admin_id, id);
"""

MIGRATIONS = [("users", "next_plan_id", "INTEGER"), ("users", "next_plan_days", "INTEGER"), ("users", "lang", "TEXT"), ("users", "remind_key", "TEXT"), ("users", "premium", "INTEGER DEFAULT 0"),
              ("plans", "name_en", "TEXT"), ("plans", "price_en", "TEXT DEFAULT ''"), ("plans", "description_en", "TEXT DEFAULT ''"),
              ("channels", "lock_code", "TEXT"), ("channels", "verified_by", "INTEGER"), ("channels", "created_at", "TEXT"), ("channels", "settings", "TEXT"),
              ("sources", "channel_id", "INTEGER"), ("sources", "feed_url", "TEXT"), ("sources", "last_error", "TEXT"), ("articles", "channel_id", "INTEGER"),
              ("sources", "bot_active", "INTEGER DEFAULT 1"), ("sources", "api_url", "TEXT"), ("sources", "api_key", "TEXT"), ("sources", "api_note", "TEXT DEFAULT ''"),
              ("pay_requests", "discount", "TEXT"), ("pay_requests", "final_price", "TEXT")]

def db():
    global _conn
    if _conn is None:
        _conn = sqlite3.connect(DB_FILE, check_same_thread=False, timeout=20)
        _conn.row_factory = sqlite3.Row
        for pr in ("PRAGMA journal_mode=WAL", "PRAGMA synchronous=NORMAL", "PRAGMA busy_timeout=15000", "PRAGMA cache_size=-16000", "PRAGMA temp_store=MEMORY"): _conn.execute(pr)
        _conn.executescript(SCHEMA)
        for tbl, col, decl in MIGRATIONS:
            try: _conn.execute(f"ALTER TABLE {tbl} ADD COLUMN {col} {decl}")
            except sqlite3.OperationalError: pass
        _conn.commit()
    return _conn

def q(sql, params=(), one=False, commit=False):
    with _lock:
        cur = db().execute(sql, params)
        if commit: db().commit(); return cur.lastrowid
        return cur.fetchone() if one else cur.fetchall()

def gset(k, v): q("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (k, json.dumps(v, ensure_ascii=False)), commit=True)
def gget(k, default=None):
    r = q("SELECT value FROM settings WHERE key=?", (k,), one=True)
    return json.loads(r["value"]) if r else default

def log_event(level, msg, admin_id=None):
    q("INSERT INTO logs(ts,level,admin_id,msg) VALUES(?,?,?,?)", (now_iso(), level, admin_id, str(msg)[:600]), commit=True)
    (log.error if level == "ERROR" else log.warning if level == "WARN" else log.info)(f"[{admin_id}] {msg}")

def recent_logs(n=30, admin_id=None, level=None):
    sql, p = "SELECT * FROM logs WHERE 1=1", []
    if admin_id: sql += " AND admin_id=?"; p.append(admin_id)
    if level: sql += " AND level=?"; p.append(level)
    return q(sql + " ORDER BY id DESC LIMIT ?", (*p, n))

# ============================================================
# متن‌های سراسری دوزبانه
DEFAULT_TEXTS = {
    "welcome": {"fa": """👋 سلام {name}!

این ربات، ادمین تمام‌وقت کانال شماست: منابع را می‌خواند، بهترین مقالات را انتخاب می‌کند، با هوش مصنوعی بازنویسی می‌کند و با قالب زیبا در کانال‌تان منتشر می‌کند.

یک بار تنظیم کنید؛ بقیه‌اش خودکار است.""",
                "en": """👋 Hi {name}!

This bot is your channel's full-time editor: it reads your sources, picks the best articles, rewrites them with AI and publishes them beautifully formatted in your channel.

Set it up once; the rest is automatic."""},
    "help": {"fa": """📘 <b>راهنما</b>

/create — پنل مدیریت و پلن رایگان
/man — پشتیبانی
/about — درباره
/lang — زبان
/cancel — لغو عملیات""",
             "en": """📘 <b>Help</b>

/create — admin panel & free plan
/man — support
/about — about
/lang — language
/cancel — cancel action"""},
    "about": {"fa": """ℹ️ <b>درباره</b>

ربات مدیریت خودکار محتوای کانال تلگرام.""", "en": """ℹ️ <b>About</b>

Automated Telegram channel content manager."""},
    "pay": {"fa": """💳 <b>پرداخت پلن «{plan}»</b>

💰 مبلغ: <b>{price}</b>

به شماره کارت زیر واریز کنید:
<code>0000-0000-0000-0000</code>
به نام: ...

سپس <b>تصویر رسید</b> را همین‌جا بفرستید.""",
            "en": """💳 <b>Payment for “{plan}”</b>

💰 Amount: <b>{price}</b>

Transfer to:
<code>0000-0000-0000-0000</code>
Name: ...

Then send the <b>receipt image</b> right here."""},
}
def gtext(key, lang="fa", **kw):
    v = gget(f"text_{key}_{lang}") or DEFAULT_TEXTS[key].get(lang) or DEFAULT_TEXTS[key]["fa"]
    try: return v.format(**kw) if kw else v
    except Exception: return v
def gtext_set(key, lang, value): gset(f"text_{key}_{lang}", value)

# ============================================================
# کاربران، نقش‌ها و زبان
def is_super(uid): return uid in SUPER_ADMIN_IDS
def get_user(uid): return q("SELECT * FROM users WHERE id=?", (uid,), one=True)
def ensure_user(uid, username="", name="", premium=None):
    u = get_user(uid)
    if not u: q("INSERT INTO users(id,username,name,role,premium,created_at,last_seen) VALUES(?,?,?,?,?,?,?)", (uid, username or "", name or "", "super" if is_super(uid) else "user", 1 if premium else 0, now_iso(), now_iso()), commit=True)
    else:
        ls = parse_dt(u["last_seen"])
        if not ls or (now_utc() - ls).total_seconds() > 300 or (premium is not None and int(bool(premium)) != (u["premium"] or 0)) or (username and username != u["username"]):
            q("UPDATE users SET username=?,name=?,last_seen=?,premium=?,role=CASE WHEN ?=1 THEN 'super' ELSE role END WHERE id=?",
              (username or u["username"], name or u["name"], now_iso(), (1 if premium else 0) if premium is not None else (u["premium"] or 0), 1 if is_super(uid) else 0, uid), commit=True)
        else: return u
    return get_user(uid)

def user_upsert(uid, uname="", name="", premium=None): return ensure_user(uid, uname, name, premium)
def is_banned(uid):
    u = get_user(uid)
    return bool(u and u["banned"])

def set_role(uid, role): q("UPDATE users SET role=? WHERE id=?", (role, uid), commit=True)
def role_of(uid):
    if is_super(uid): return "super"
    u = get_user(uid); return u["role"] if u else "user"
def user_lang(uid):
    u = get_user(uid); return u["lang"] if u and u["lang"] in LANGS else None
def set_lang(uid, lang): q("UPDATE users SET lang=? WHERE id=?", (lang if lang in LANGS else "fa", uid), commit=True)
def list_users(role=None, limit=5000): return q("SELECT * FROM users" + (" WHERE role=?" if role else "") + " ORDER BY created_at DESC LIMIT ?", ((role, limit) if role else (limit,)))
def list_admins(): return q("SELECT * FROM users WHERE role IN ('admin','super') AND banned=0")
def count_users(): return q("SELECT role, COUNT(*) c FROM users GROUP BY role")

# ============================================================
# پلن‌ها و اشتراک
def seed_plans():
    if not q("SELECT 1 FROM plans LIMIT 1"):
        create_plan(name="رایگان", name_en="Free", days=7, daily_posts=1, max_sources=2, max_channels=1, daily_tests=1, price="رایگان", price_en="Free", description="۱ پست در روز · ۷ روز", description_en="1 post/day · 7 days", is_free=1, sort=0)
        create_plan(name="حرفه‌ای", name_en="Pro", days=30, daily_posts=20, max_sources=15, max_channels=3, daily_tests=5, price="توافقی", price_en="Contact us", description="۲۰ پست روزانه · ۱۵ منبع · ۳ کانال", description_en="20 posts/day · 15 sources · 3 channels", is_free=0, sort=1)

def list_plans(active_only=True): return q("SELECT * FROM plans" + (" WHERE active=1" if active_only else "") + " ORDER BY sort, id")
def get_plan(pid): return q("SELECT * FROM plans WHERE id=?", (pid,), one=True) if pid else None
def free_plan(): return q("SELECT * FROM plans WHERE is_free=1 AND active=1 ORDER BY id LIMIT 1", one=True)
def plan_txt(p, field, lang="fa"):
    if not p: return ""
    if lang == "en" and p[f"{field}_en"]: return p[f"{field}_en"]
    return p[field] or ""

def create_plan(**f):
    return q("INSERT INTO plans(name,name_en,days,daily_posts,max_sources,max_channels,daily_tests,price,price_en,description,description_en,is_free,sort) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
             (f.get("name", "پلن"), f.get("name_en", ""), f.get("days", 30), f.get("daily_posts", 5), f.get("max_sources", 5), f.get("max_channels", 1), f.get("daily_tests", 2), f.get("price", ""), f.get("price_en", ""), f.get("description", ""), f.get("description_en", ""), f.get("is_free", 0), f.get("sort", 0)), commit=True)
def update_plan(pid, **f):
    for k, v in f.items(): q(f"UPDATE plans SET {k}=? WHERE id=?", (v, pid), commit=True)
def delete_plan(pid): q("DELETE FROM plans WHERE id=?", (pid,), commit=True)

def assign_plan(uid, pid, days=None):
    p = get_plan(pid)
    if not p: return None, False
    u = get_user(uid); d = int(days if days is not None else p["days"]); now = now_utc()
    cur = parse_dt(u["plan_expires"]) if u else None; active = bool(cur and cur > now and u["plan_id"])
    if active and not p["is_free"] and (get_plan(u["plan_id"]) or {"is_free": 0})["is_free"]: active = False
    if active and u["plan_id"] != pid:
        same_next = u["next_plan_id"] == pid
        q("UPDATE users SET next_plan_id=?, next_plan_days=? WHERE id=?", (pid, (u["next_plan_days"] or 0) + d if same_next else d, uid), commit=True)
        return cur, True
    exp = (cur if active else now) + timedelta(days=d)
    q("UPDATE users SET plan_id=?, plan_expires=?, remind_key=NULL, role=CASE WHEN role='user' THEN 'admin' ELSE role END, free_used=CASE WHEN ?=1 THEN 1 ELSE free_used END WHERE id=?", (pid, exp.isoformat(), p["is_free"], uid), commit=True)
    return exp, False

def revoke_plan(uid): q("UPDATE users SET plan_id=NULL, plan_expires=NULL, next_plan_id=NULL, next_plan_days=NULL, remind_key=NULL WHERE id=?", (uid,), commit=True)
def activate_next_plans():
    out = []
    for u in q("SELECT * FROM users WHERE next_plan_id IS NOT NULL AND (plan_expires IS NULL OR plan_expires<=?)", (now_iso(),)):
        p = get_plan(u["next_plan_id"])
        if not p: q("UPDATE users SET next_plan_id=NULL, next_plan_days=NULL WHERE id=?", (u["id"],), commit=True); continue
        exp = now_utc() + timedelta(days=int(u["next_plan_days"] or p["days"]))
        q("UPDATE users SET plan_id=?, plan_expires=?, next_plan_id=NULL, next_plan_days=NULL, remind_key=NULL WHERE id=?", (p["id"], exp.isoformat(), u["id"]), commit=True)
        out.append((u["id"], p, exp))
    return out

def expiring_users():
    out, now = [], now_utc()
    for u in q("SELECT * FROM users WHERE plan_expires IS NOT NULL AND banned=0 AND plan_expires>?", (now_iso(),)):
        exp = parse_dt(u["plan_expires"])
        if not exp: continue
        left = (exp - now).total_seconds() / 3600
        stage = "24" if left <= 24 else "72" if left <= 72 else None
        if not stage or u["remind_key"] == stage or (stage == "72" and u["remind_key"] == "24"): continue
        q("UPDATE users SET remind_key=? WHERE id=?", (stage, u["id"]), commit=True); out.append((u, stage, left))
    return out

def admin_limits(uid):
    if is_super(uid): return dict(daily_posts=None, max_sources=None, max_channels=None, daily_tests=None, plan=None, plan_id=None, expires=None, active=True, next_plan=None)
    u = get_user(uid); p = get_plan(u["plan_id"]) if u and u["plan_id"] else None
    exp = parse_dt(u["plan_expires"]) if u else None; active = bool(p and exp and exp > now_utc() and not u["banned"])
    return dict(daily_posts=p["daily_posts"] if p else 0, max_sources=p["max_sources"] if p else 0, max_channels=p["max_channels"] if p else 0, daily_tests=p["daily_tests"] if p else 0, plan=p, plan_id=p["id"] if p else None, expires=exp, active=active, next_plan=get_plan(u["next_plan_id"]) if u and u["next_plan_id"] else None)

def admin_offset(uid):
    ch = q("SELECT settings FROM channels WHERE admin_id=? ORDER BY id LIMIT 1", (uid,), one=True)
    try: return float(json.loads(ch["settings"]).get("utc_offset", DEFAULT_UTC_OFFSET)) if ch and ch["settings"] else DEFAULT_UTC_OFFSET
    except Exception: return DEFAULT_UTC_OFFSET

def usage_today(uid):
    r = q("SELECT posts,tests FROM usage WHERE admin_id=? AND day=?", (uid, today_str(admin_offset(uid))), one=True)
    return {"posts": r["posts"], "tests": r["tests"]} if r else {"posts": 0, "tests": 0}

def usage_inc(uid, field):
    d = today_str(admin_offset(uid))
    q("INSERT INTO usage(admin_id,day,posts,tests) VALUES(?,?,0,0) ON CONFLICT(admin_id,day) DO NOTHING", (uid, d), commit=True)
    q(f"UPDATE usage SET {field}={field}+1 WHERE admin_id=? AND day=?", (uid, d), commit=True)

def usage_reset(uid, field="tests"): q(f"UPDATE usage SET {field}=0 WHERE admin_id=? AND day=?", (uid, today_str(admin_offset(uid))), commit=True)
def remaining(uid, field="posts"):
    lim = admin_limits(uid); cap = lim["daily_posts"] if field == "posts" else lim["daily_tests"]
    if cap is None: return None
    return max(0, cap - usage_today(uid)[field])

# ============================================================
# کدهای تخفیف
_FA_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
def disc_list(): return q("SELECT * FROM discounts ORDER BY created_at DESC")
def disc_get(code): return q("SELECT * FROM discounts WHERE code=?", (str(code).strip().upper(),), one=True) if code else None
def disc_create(code, percent, expires_iso, max_uses=0):
    code = re.sub(r"\s+", "", str(code)).upper()
    if not code or disc_get(code): return None
    q("INSERT INTO discounts(code,percent,expires,max_uses,used,active,created_at) VALUES(?,?,?,?,0,1,?)", (code, max(1, min(100, int(percent))), expires_iso, int(max_uses or 0), now_iso()), commit=True); return code
def disc_update(code, **f):
    for k, v in f.items(): q(f"UPDATE discounts SET {k}=? WHERE code=?", (v, code), commit=True)
def disc_delete(code): q("DELETE FROM discounts WHERE code=?", (code,), commit=True)
def disc_valid(code):
    d = disc_get(code)
    if not d: return None, "not_found"
    if not d["active"]: return None, "inactive"
    e = parse_dt(d["expires"])
    if e and e <= now_utc(): return None, "expired"
    if d["max_uses"] and d["used"] >= d["max_uses"]: return None, "exhausted"
    return d, "ok"
def disc_use(code): q("UPDATE discounts SET used=used+1 WHERE code=?", (code,), commit=True)
def discount_price(price_text, percent):
    t = str(price_text or "").translate(_FA_DIGITS); m = re.search(r"\d[\d,٬.]*", t)
    if not m: return f"{price_text} (-{percent}%)"
    try: n = float(m.group(0).replace(",", "").replace("٬", ""))
    except Exception: return f"{price_text} (-{percent}%)"
    v = n * (100 - percent) / 100; vs = f"{int(v):,}" if v == int(v) else f"{v:,.2f}"
    return t[:m.start()] + vs + t[m.end():]

# ============================================================
# کانال‌ها و تنظیمات
DEFAULT_PROMPT = {
    "fa": ("تو سردبیر حرفه‌ای یک کانال تلگرامی هستی و مثل یک انسانِ خبره و خوش‌قلم می‌نویسی؛ نه مثل ربات و نه مثل هوش مصنوعی. به زبانی می‌نویسی که در «زبان خروجی» تعیین شده است. "
           "متن را روان، دقیق، بی‌طرف و بدون اغراق بازنویسی کن؛ چیزی که در منبع نیست اضافه نکن و اعداد، تاریخ‌ها و اسامی را دقیقاً حفظ کن. "
           "تیتر جذاب در خط اول داخل <b> با یک ایموجی مرتبط؛ سپس لید یک‌جمله‌ای؛ سپس پاراگراف‌های کوتاه ۲ تا ۳ خطی با یک خط خالی بین آن‌ها. "
           "هر پاراگراف با یک ایموجی مرتبط شروع شود و در طول متن هم ایموجی‌های مناسب ادامه یابد. "
           "نکات و فهرست‌ها را با «•» بنویس، اصطلاحات و اعداد مهم را <b> کن، مهم‌ترین نقل‌قول یا آمار را داخل <blockquote> بگذار. "
           "از خط جداکننده مثل «---»، جملات کلیشه‌ای و لحن قالبی پرهیز کن. جمله‌ها کوتاه و متنوع، بدون مقدمه‌چینی، با یک جمع‌بندی یک‌خطی در پایان."),
    "en": ("You are a professional editor of a Telegram channel who writes like a skilled, eloquent human — never like a bot or an AI. You write in the language set in “Output language”. "
           "Rewrite clearly, precisely, neutrally and without exaggeration; never add facts missing from the source and keep numbers, dates and names exact. "
           "Catchy headline on the first line inside <b> with one relevant emoji; then a one-sentence lead; then short 2–3 line paragraphs separated by a blank line. "
           "Every paragraph starts with a relevant emoji and suitable emojis continue naturally through the text. "
           "List points with “•”, bold key terms and numbers with <b>, put the most important quote or figure inside <blockquote>. "
           "Never use divider lines like “---”, no clichés, no robotic tone. Short, varied sentences, no preamble, one-line takeaway at the end."),
}
_LEGACY_PROMPTS = (
    "تو سردبیر حرفه‌ای یک کانال تلگرامی فارسی هستی. متن را روان، دقیق، بی‌طرف و بدون اغراق بازنویسی کن؛ چیزی که در منبع نیست اضافه نکن و اعداد، تاریخ‌ها و اسامی را دقیقاً حفظ کن.",
    "You are a professional editor of an English Telegram channel. Rewrite clearly, precisely, neutrally and without exaggeration; never add facts missing from the source and keep numbers, dates and names exact."
)
DEFAULT_CATEGORIES = {
    "fa": [{"name": "خبری", "emoji": "📰", "style": "تیتر کوتاه بولد، لید یک‌جمله‌ای، ۲ تا ۳ پاراگراف کوتاه، یک نکته‌ی کلیدی با «•»."},
           {"name": "آموزشی", "emoji": "🎓", "style": "تیتر بولد، مقدمه‌ی یک‌خطی، ۳ تا ۶ نکته با «•»، جمع‌بندی یک‌خطی."},
           {"name": "تحلیلی", "emoji": "🧠", "style": "تیتر بولد، یک نقل‌قول کلیدی داخل blockquote، تحلیل در دو پاراگراف کوتاه."},
           {"name": "معرفی و بررسی", "emoji": "🔍", "style": "تیتر بولد، خلاصه‌ی یک‌خطی، مزایا/معایب با «•»، جمع‌بندی بی‌طرف."}],
    "en": [{"name": "News", "emoji": "📰", "style": "Short bold headline, one-sentence lead, 2–3 short paragraphs, one key point as a “•” bullet."},
           {"name": "Tutorial", "emoji": "🎓", "style": "Bold headline, one-line intro, 3–6 “•” bullets, one-line takeaway."},
           {"name": "Analysis", "emoji": "🧠", "style": "Bold headline, one key quote in blockquote, analysis in two short paragraphs."},
           {"name": "Review", "emoji": "🔍", "style": "Bold headline, one-line summary, pros/cons as “•” bullets, neutral verdict."}],
}
DEFAULT_CRITERIA = {
    "fa": [{"name": "ارزش محتوایی", "weight": 40}, {"name": "غیرتبلیغاتی بودن", "weight": 15}, {"name": "کیفیت و کامل بودن", "weight": 20}, {"name": "ارتباط با موضوع کانال", "weight": 15}, {"name": "تازگی", "weight": 10}],
    "en": [{"name": "Content value", "weight": 40}, {"name": "Non-promotional", "weight": 15}, {"name": "Quality & completeness", "weight": 20}, {"name": "Relevance to channel topic", "weight": 15}, {"name": "Freshness", "weight": 10}],
}

def default_settings(lang="fa", channel_username=""):
    lang = lang if lang in LANGS else "fa"
    return {"ui_lang": lang, "enabled": True, "mode": "auto", "prompt": DEFAULT_PROMPT[lang], "topic": "", "language": "فارسی" if lang == "fa" else "English",
            "categories": [dict(c) for c in DEFAULT_CATEGORIES[lang]], "criteria": [dict(c) for c in DEFAULT_CRITERIA[lang]], "min_score": 60,
            "lookback_hours": 24, "allow_undated": True, "quiet_start": None, "quiet_end": None, "utc_offset": DEFAULT_UTC_OFFSET,
            "include_media": True, "include_link": True, "signature": f"@{channel_username}" if channel_username else "@channel", "max_words": 150, "post_limit": POST_LIMIT_DEFAULT,
            "strict_ads": False, "interval_minutes": 60, "posts_per_cycle": 2, "hashtags": True, "premium_format": False,
            "last_run": None, "last_end": None, "last_result": "", "last_diag": None, "last_notified_diag": ""}

def get_settings(cid):
    ch = q("SELECT settings, username, admin_id FROM channels WHERE id=?", (cid,), one=True)
    stored = {}
    if ch and ch["settings"]:
        try: stored = json.loads(ch["settings"])
        except Exception: stored = {}
    base = stored.get("ui_lang") or (user_lang(ch["admin_id"]) if ch else None) or "fa"
    s = default_settings(base if base in LANGS else "fa", ch["username"] if ch else ""); s.update(stored); s["ui_lang"] = base if base in LANGS else "fa"
    s["interval_minutes"] = max(MIN_INTERVAL, int(s.get("interval_minutes") or MIN_INTERVAL)); s["lookback_hours"] = min(MAX_LOOKBACK, max(1, int(s.get("lookback_hours") or 24)))
    s["posts_per_cycle"] = min(MAX_PPC, max(1, int(s.get("posts_per_cycle") or 1))); s["post_limit"] = min(4000, max(300, int(s.get("post_limit") or POST_LIMIT_DEFAULT)))
    return s

def save_settings(cid, s): q("UPDATE channels SET settings=? WHERE id=?", (json.dumps(s, ensure_ascii=False), cid), commit=True)
def update_settings(cid, **kw): s = get_settings(cid); s.update(kw); save_settings(cid, s); return s
def toggle_setting(cid, field):
    s = get_settings(cid); val = not bool(s.get(field, False))
    update_settings(cid, **{field: val}); return val
def init_settings(cid, lang="fa"):
    ch = get_channel(cid); u = ch["username"] if ch else ""; s = default_settings(lang, u); save_settings(cid, s); return s
def in_quiet(s):
    a, b = s.get("quiet_start"), s.get("quiet_end")
    if a is None or b is None or a == b: return False
    h = datetime.now(tz_of(s.get("utc_offset"))).hour
    return (a <= h < b) if a < b else (h >= a or h < b)

def relocalize_settings(cid, new_lang):
    new_lang = new_lang if new_lang in LANGS else "fa"; s = get_settings(cid); old = s.get("ui_lang", "fa")
    if old != new_lang:
        old_d, new_d = default_settings(old, ""), default_settings(new_lang, "")
        for k in ("prompt", "language", "categories", "criteria"):
            if json.dumps(s.get(k), ensure_ascii=False, sort_keys=True) == json.dumps(old_d.get(k), ensure_ascii=False, sort_keys=True):
                s[k] = new_d[k]
    s["ui_lang"] = new_lang; s["last_diag"] = None; s["last_notified_diag"] = ""; save_settings(cid, s); return s

def relocalize_all(uid, new_lang):
    n = 0
    for ch in q("SELECT id FROM channels WHERE admin_id=?", (uid,)):
        try: relocalize_settings(ch["id"], new_lang); n += 1
        except Exception as e: log.warning(f"relocalize {ch['id']}: {e}")
    return n

def _lock_code(): return f"{random.SystemRandom().randint(0, 999999):06d}"
gen_lock_code = _lock_code
def list_channels(uid): return q("SELECT * FROM channels WHERE admin_id=? ORDER BY id", (uid,))
def get_channel(cid): return q("SELECT * FROM channels WHERE id=?", (cid,), one=True)
def channel_owned(cid, uid):
    ch = get_channel(cid); return ch if ch and (ch["admin_id"] == uid or is_super(uid)) else None
def channel_by_chat(chat_id): return q("SELECT * FROM channels WHERE chat_id=?", (chat_id,), one=True)

def add_channel(uid, chat_id, title, username, verified_by, lang="fa"):
    if channel_by_chat(chat_id): return None
    return q("INSERT INTO channels(admin_id,chat_id,title,username,lock_code,verified_by,created_at,settings) VALUES(?,?,?,?,?,?,?,?)",
             (uid, chat_id, title, username or "", _lock_code(), verified_by, now_iso(), json.dumps(default_settings(lang, username), ensure_ascii=False)), commit=True)

def transfer_channel(cid, new_uid, lang="fa"):
    ch = get_channel(cid)
    if not ch: return None
    q("DELETE FROM sources WHERE channel_id=?", (cid,), commit=True); q("DELETE FROM articles WHERE channel_id=? AND status!='published'", (cid,), commit=True)
    q("UPDATE channels SET admin_id=?, verified_by=?, lock_code=?, settings=? WHERE id=?", (new_uid, new_uid, _lock_code(), json.dumps(default_settings(lang, ch["username"]), ensure_ascii=False), cid), commit=True)
    return ch["admin_id"]

def regen_lock(cid): code = _lock_code(); q("UPDATE channels SET lock_code=? WHERE id=?", (code, cid), commit=True); return code
def reset_channel_link(cid):
    code = _lock_code(); q("UPDATE channels SET lock_code=? WHERE id=?", (code, cid), commit=True)
    n = q("SELECT COUNT(*) c FROM articles WHERE channel_id=? AND status!='published'", (cid,), one=True)["c"]
    q("DELETE FROM articles WHERE channel_id=? AND status!='published'", (cid,), commit=True)
    update_settings(cid, enabled=False, last_run=None, last_end=None, last_result="", last_diag=None, last_notified_diag="")
    return code, n

def check_lock(cid, code): ch = get_channel(cid); return bool(ch and ch["lock_code"] and str(code).strip() == ch["lock_code"])
def del_channel(cid, uid):
    q("DELETE FROM sources WHERE channel_id=? AND admin_id=?", (cid, uid), commit=True); q("DELETE FROM articles WHERE channel_id=? AND admin_id=?", (cid, uid), commit=True)
    q("DELETE FROM channels WHERE id=? AND admin_id=?", (cid, uid), commit=True)
    purge_ch_lock(cid)

def delete_channel(cid, uid=None):
    if uid is None:
        ch = get_channel(cid); uid = ch["admin_id"] if ch else None
    if uid is not None: del_channel(cid, uid)

def update_channel_meta(cid, title=None, username=None):
    if title is not None: q("UPDATE channels SET title=? WHERE id=?", (title, cid), commit=True)
    if username is not None: q("UPDATE channels SET username=? WHERE id=?", (username, cid), commit=True)

# ============================================================
# منابع
def normalize_url(u):
    u = str(u).strip()
    if not u.startswith(("http://", "https://")): u = "https://" + u
    return u.split("#")[0].rstrip("/")

def list_sources(cid, active_only=False): return q("SELECT * FROM sources WHERE channel_id=?" + (" AND active=1" if active_only else "") + " ORDER BY id", (cid,))
def count_sources(uid): return q("SELECT COUNT(*) c FROM sources WHERE admin_id=?", (uid,), one=True)["c"]
def add_source(uid, cid, url, title="", api_url="", api_key="", api_note=""):
    url = normalize_url(url)
    if q("SELECT 1 FROM sources WHERE channel_id=? AND url=?", (cid, url), one=True): return None
    return q("INSERT INTO sources(admin_id,channel_id,url,title,api_url,api_key,api_note) VALUES(?,?,?,?,?,?,?)", (uid, cid, url, title, api_url or None, api_key or None, api_note or ""), commit=True)

def get_source(sid): return q("SELECT * FROM sources WHERE id=?", (sid,), one=True)
def source_of_article(a):
    sid = a["source_id"] if a and "source_id" in a.keys() else None
    return get_source(sid) if sid else None

def del_source(sid, uid=None):
    if uid is not None: q("DELETE FROM sources WHERE id=? AND admin_id=?", (sid, uid), commit=True)
    else: q("DELETE FROM sources WHERE id=?", (sid,), commit=True)
def delete_source(sid, uid=None): del_source(sid, uid)
def set_source_active(sid, val, col="active"):
    if col not in ("active", "bot_active"): return None
    q(f"UPDATE sources SET {col}=? WHERE id=?", (1 if val else 0, sid), commit=True); return bool(val)

def toggle_source(sid, uid, col="active"):
    if col not in ("active", "bot_active"): col = "active"
    q(f"UPDATE sources SET {col}=1-COALESCE({col},1) WHERE id=? AND admin_id=?", (sid, uid), commit=True); s = get_source(sid); return bool(s and s[col])

def source_bot_ok(sid):
    if not sid: return True
    s = get_source(sid); return bool(s is None or s["bot_active"] is None or s["bot_active"])

def set_source_api(sid, api_url="", api_key="", api_note=""):
    q("UPDATE sources SET api_url=?, api_key=?, api_note=? WHERE id=?", ((api_url or "").strip() or None, (api_key or "").strip() or None, (api_note or "").strip(), sid), commit=True)
    return get_source(sid)

def source_ok(sid, feed_url=None, etag=None, last_modified=None):
    q("UPDATE sources SET last_fetch=?, fail_count=0, last_error=NULL, etag=?, last_modified=?, feed_url=COALESCE(?, feed_url) WHERE id=?", (now_iso(), etag, last_modified, feed_url, sid), commit=True)
def source_fail(sid, err): q("UPDATE sources SET last_fetch=?, fail_count=fail_count+1, last_error=? WHERE id=?", (now_iso(), str(err)[:200], sid), commit=True)

# ============================================================
# مقالات
def article_exists(cid, h): return bool(q("SELECT 1 FROM articles WHERE channel_id=? AND hash=?", (cid, h), one=True))
def article_insert(uid, cid, h, url, title, source_id, published_at, status="discovered", reason=""):
    with _lock:
        cur = db().execute("INSERT OR IGNORE INTO articles(admin_id,channel_id,hash,url,title,source_id,published_at,created_at,status,reason) VALUES(?,?,?,?,?,?,?,?,?,?)",
                           (uid, cid, h, url, title or "", source_id, published_at, now_iso(), status, reason))
        db().commit(); return cur.lastrowid if cur.rowcount else None

def article_update(aid, **f):
    if not f: return
    q("UPDATE articles SET " + ", ".join(f"{k}=?" for k in f) + " WHERE id=?", (*f.values(), aid), commit=True)
def get_article(aid): return q("SELECT * FROM articles WHERE id=?", (aid,), one=True)
def articles_by_status(cid, status, limit=50):
    st = ("rejected", "failed") if status == "rejected" else (status,)
    return q(f"SELECT id,title,score,category,created_at,url,reason,status FROM articles WHERE channel_id=? AND status IN ({','.join('?'*len(st))}) ORDER BY id DESC LIMIT ?", (cid, *st, limit))
def ready_count(cid): return q("SELECT COUNT(*) c FROM articles WHERE channel_id=? AND status='ready'", (cid,), one=True)["c"]
def delete_article(aid, uid=None):
    if uid is not None: q("DELETE FROM articles WHERE id=? AND admin_id=?", (aid, uid), commit=True)
    else: q("DELETE FROM articles WHERE id=?", (aid,), commit=True)
def article_delete(aid, uid=None): delete_article(aid, uid)
def posted_before(chat_id, h): return bool(q("SELECT 1 FROM posted WHERE channel_id=? AND hash=?", (chat_id, h), one=True))
def mark_posted(chat_id, h): q("INSERT OR IGNORE INTO posted VALUES(?,?,?)", (chat_id, h, now_iso()), commit=True)

def count_articles(uid=None, hours=24, status=None, cid=None):
    since = (now_utc() - timedelta(hours=hours)).isoformat(); sql, p = "SELECT COUNT(*) c FROM articles WHERE created_at>=?", [since]
    if cid is not None: sql += " AND channel_id=?"; p.append(cid)
    elif uid is not None: sql += " AND admin_id=?"; p.append(uid)
    if status: sql += " AND status=?"; p.append(status)
    return q(sql, tuple(p), one=True)["c"]

def cleanup():
    if (time.time() - float(gget("last_cleanup", 0))) < 3600: return
    ttl = (now_utc() - timedelta(hours=DATA_TTL_HOURS)).isoformat()
    q("DELETE FROM articles WHERE created_at<? AND status NOT IN ('ready','published')", (ttl,), commit=True)
    q("DELETE FROM articles WHERE created_at<? AND status IN ('ready','published')", ((now_utc() - timedelta(hours=72)).isoformat(),), commit=True)
    q("DELETE FROM posted WHERE posted_at<?", ((now_utc() - timedelta(days=90)).isoformat(),), commit=True)
    q("DELETE FROM kv_cache WHERE cached_at<?", (ttl,), commit=True)
    q("DELETE FROM deeplinks WHERE created_at<?", ((now_utc() - timedelta(days=30)).isoformat(),), commit=True)
    q("DELETE FROM logs WHERE id < (SELECT COALESCE(MAX(id),0) FROM logs) - 3000", commit=True)
    q("DELETE FROM usage WHERE day<?", ((now_utc() - timedelta(days=60)).strftime("%Y-%m-%d"),), commit=True)
    q("DELETE FROM support_map WHERE ts<?", ((now_utc() - timedelta(days=7)).isoformat(),), commit=True)
    q("DELETE FROM pay_requests WHERE status!='pending' AND decided_at<?", ((now_utc() - timedelta(days=90)).isoformat(),), commit=True)
    try: q("PRAGMA wal_checkpoint(TRUNCATE)")
    except Exception: pass
    gset("last_cleanup", time.time())

# ============================================================
# پشتیبانی و پرداخت با جدول امن support_map
def support_open(uid): q("INSERT OR REPLACE INTO support(user_id,open,opened_at) VALUES(?,1,?)", (uid, now_iso()), commit=True)
def support_close(uid): q("UPDATE support SET open=0 WHERE user_id=?", (uid,), commit=True)
def support_is_open(uid):
    r = q("SELECT open FROM support WHERE user_id=?", (uid,), one=True); return bool(r and r["open"])

def support_map_set(admin_id, msg_id, uid):
    q("INSERT OR REPLACE INTO support_map(admin_id,message_id,user_id,ts) VALUES(?,?,?,?)", (admin_id, msg_id, uid, now_iso()), commit=True)

def support_map_get(admin_id, msg_id):
    r = q("SELECT user_id FROM support_map WHERE admin_id=? AND message_id=?", (admin_id, msg_id), one=True)
    return r["user_id"] if r else None

def pay_pending_for(uid, pid): return q("SELECT * FROM pay_requests WHERE user_id=? AND plan_id=? AND status='pending'", (uid, pid), one=True)
def pay_create(uid, pid, receipt_chat=None, receipt_msg=None, note="", discount=None, final_price=None):
    return q("INSERT INTO pay_requests(user_id,plan_id,created_at,receipt_chat,receipt_msg,note,discount,final_price) VALUES(?,?,?,?,?,?,?,?)", (uid, pid, now_iso(), receipt_chat, receipt_msg, (note or "")[:500], discount, final_price), commit=True)
def pay_pending(): return q("SELECT r.*, u.username, u.name, p.name plan_name, p.price plan_price FROM pay_requests r JOIN users u ON u.id=r.user_id JOIN plans p ON p.id=r.plan_id WHERE r.status='pending' ORDER BY r.id")
def pay_get(rid): return q("SELECT * FROM pay_requests WHERE id=?", (rid,), one=True)
def pay_set(rid, status): q("UPDATE pay_requests SET status=?, decided_at=? WHERE id=?", (status, now_iso(), rid), commit=True)

# ============================================================
# کلاینت HTTP، کش KV و دیپ‌لینک
_http = None
UA_BROWSER = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"
UA_FEED = "Mozilla/5.0 (compatible; NewsBot/3.0; +https://t.me) FeedFetcher"

def http():
    global _http
    if _http is None:
        _http = httpx.AsyncClient(follow_redirects=True, timeout=httpx.Timeout(25, connect=10), limits=httpx.Limits(max_connections=FETCH_CONCURRENCY + 8, max_keepalive_connections=8),
                                  headers={"User-Agent": UA_BROWSER, "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8", "Accept-Language": "fa,en;q=0.8"})
    return _http

async def fetch(url, **kw):
    async with FETCH_SEM: return await http().get(url, **kw)

class FetchError(RuntimeError):
    def __init__(self, status, url=""): super().__init__(f"HTTP {status}"); self.status = int(status); self.url = url

CF_BASE = f"https://api.cloudflare.com/client/v4/accounts/{CF_ACCOUNT_ID}/storage/kv/namespaces/{CF_KV_NAMESPACE_ID}/values/"
async def kv_put(key, value):
    try:
        r = await http().put(CF_BASE + key, content=value.encode(), headers={"Authorization": f"Bearer {CF_API_TOKEN}", "Content-Type": "text/plain"}); return r.status_code == 200
    except Exception as e: log_event("ERROR", f"KV put: {e}"); return False

async def kv_get(key):
    try:
        r = await http().get(CF_BASE + key, headers={"Authorization": f"Bearer {CF_API_TOKEN}"}); return r.text if r.status_code == 200 else None
    except Exception as e: log_event("ERROR", f"KV get: {e}"); return None

async def store_deeplink(admin_id, payload):
    key = secrets.token_urlsafe(6); data = json.dumps(payload, ensure_ascii=False); saved_cf = CF_ENABLED and await kv_put(key, data)
    q("INSERT INTO deeplinks(key,admin_id,created_at,local_json) VALUES(?,?,?,?)", (key, admin_id, now_iso(), None if saved_cf else data), commit=True)
    q("INSERT OR REPLACE INTO kv_cache VALUES(?,?,?)", (key, data, now_iso()), commit=True); return key

async def load_deeplink(key):
    r = q("SELECT value FROM kv_cache WHERE key=?", (key,), one=True)
    if r: return json.loads(r["value"])
    row = q("SELECT local_json FROM deeplinks WHERE key=?", (key,), one=True); data = row["local_json"] if row and row["local_json"] else (await kv_get(key) if CF_ENABLED else None)
    if data: q("INSERT OR REPLACE INTO kv_cache VALUES(?,?,?)", (key, data, now_iso()), commit=True); return json.loads(data)
    return None

def init_core():
    db(); seed_plans()
    if gget("automation_enabled") is None: gset("automation_enabled", True)
    log.info(f"core v3 آماده | CF KV: {'فعال' if CF_ENABLED else 'محلی'} | مدیر کلان: {SUPER_ADMIN_IDS} | AI×{AI_CONCURRENCY} FETCH×{FETCH_CONCURRENCY} CYCLE×{CYCLE_CONCURRENCY}")

init_db = init_core

# ============================================================
# موتور هوش مصنوعی (چندمدله با Fallback)
def hostname(u):
    try: return urlparse(u).netloc.replace("www.", "") or u
    except Exception: return str(u)

def detect_kind(base_url):
    b = (base_url or "").lower()
    if "anthropic.com" in b: return "anthropic"
    if "generativelanguage.googleapis.com" in b: return "gemini"
    return "openai"

def list_models(active_only=False): return q("SELECT * FROM ai_models" + (" WHERE active=1" if active_only else "") + " ORDER BY priority, id")
def get_model(mid): return q("SELECT * FROM ai_models WHERE id=?", (mid,), one=True)
def add_model(base_url, api_key, model, name="", priority=10, temperature=0.5, max_tokens=2500):
    base_url = str(base_url).strip().rstrip("/"); model = str(model).strip(); kind = detect_kind(base_url)
    name = (name or f"{hostname(base_url) or kind}").strip()[:40]
    return q("INSERT INTO ai_models(name,kind,base_url,api_key,model,priority,temperature,max_tokens) VALUES(?,?,?,?,?,?,?,?)", (name, kind, base_url, api_key.strip(), model, priority, temperature, max_tokens), commit=True)

def update_model(mid, **f):
    if "base_url" in f: f["base_url"] = str(f["base_url"]).strip().rstrip("/"); f["kind"] = detect_kind(f["base_url"])
    q("UPDATE ai_models SET " + ", ".join(f"{k}=?" for k in f) + " WHERE id=?", (*f.values(), mid), commit=True)

def delete_model(mid):
    q("DELETE FROM ai_models WHERE id=?", (mid,), commit=True)
    purge_model_lock(mid)

async def notify_super(text, kb=None):
    if NOTIFY_SUPER:
        try: await NOTIFY_SUPER(text, kb)
        except Exception as e: log.warning(f"notify super: {e}")

async def notify_user(uid, text, kb=None):
    if NOTIFY_USER:
        try: await NOTIFY_USER(uid, text, kb)
        except Exception as e: log.warning(f"notify user {uid}: {e}")

def _err_text(r):
    try:
        j = r.json(); e = j.get("error"); msg = (e.get("message") if isinstance(e, dict) else e) or j.get("message") or j.get("detail") or r.text
    except Exception: msg = r.text
    return f"HTTP {r.status_code}: {re.sub(r'<[^>]+>', '', str(msg))[:160]}"

def _openai_content(j):
    ch = (j.get("choices") or [{}])[0]; msg = ch.get("message") or ch.get("delta") or {}; c = msg.get("content")
    if not c and ch.get("text"): c = ch["text"]
    if isinstance(c, list): c = "".join(p.get("text", "") for p in c if isinstance(p, dict))
    return c or ""

async def _post(url, **kw): return await http().post(url, timeout=httpx.Timeout(120, connect=15), **kw)

async def _call_model(m, system, user):
    kind = m["kind"] or detect_kind(m["base_url"]); base = (m["base_url"] or "").rstrip("/"); key = m["api_key"] or ""; model = m["model"]; temp = float(m["temperature"] or 0.5); mx = int(m["max_tokens"] or 2500)
    if kind == "anthropic":
        url = base + ("/messages" if base.endswith("/v1") else "/v1/messages")
        r = await _post(url, headers={"x-api-key": key, "anthropic-version": "2023-06-01", "content-type": "application/json"}, json={"model": model, "max_tokens": mx, "temperature": temp, "system": system, "messages": [{"role": "user", "content": user}]})
        if r.status_code >= 400: raise RuntimeError(_err_text(r))
        return "".join(b.get("text", "") for b in r.json().get("content", []) if b.get("type") == "text")
    if kind == "gemini":
        model = model.replace("models/", ""); root = base if re.search(r"/v1(beta)?$", base) else base + "/v1beta"
        r = await _post(f"{root}/models/{model}:generateContent", params={"key": key}, json={"system_instruction": {"parts": [{"text": system}]}, "contents": [{"role": "user", "parts": [{"text": user}]}], "generationConfig": {"temperature": temp, "maxOutputTokens": mx}})
        if r.status_code >= 400: raise RuntimeError(_err_text(r))
        cands = r.json().get("candidates") or []
        if not cands: raise RuntimeError("no candidates (safety block?)")
        return "".join(p.get("text", "") for p in cands[0].get("content", {}).get("parts", []))
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    if "openrouter" in base: headers.update({"HTTP-Referer": "https://t.me", "X-Title": "NewsBot"})
    body = {"model": model, "temperature": temp, "max_tokens": mx, "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]}
    url = base if base.endswith("/chat/completions") else base + "/chat/completions"
    r = await _post(url, headers=headers, json=body)
    if r.status_code == 404 and not re.search(r"/v\d", base): r = await _post(base + "/v1/chat/completions", headers=headers, json=body)
    if r.status_code >= 400: raise RuntimeError(_err_text(r))
    return _openai_content(r.json())

async def _mark_fail(m, err):
    fc = (m["fail_count"] or 0) + 1; update_model(m["id"], fail_count=fc, last_error=str(err)[:300], last_fail=now_iso())
    if fc >= 2 and m["status"] != "down":
        update_model(m["id"], status="down"); log_event("ERROR", f"مدل «{m['name']}» از کار افتاد: {err}")
        await notify_super(f"🔴 مدل <b>{html.escape(m['name'])}</b> (<code>{html.escape(m['model'])}</code>) از کار افتاد.\n<code>{html.escape(str(err)[:200])}</code>")

async def _mark_ok(m):
    update_model(m["id"], fail_count=0, status="ok", last_ok=now_iso(), ok_count=(m["ok_count"] or 0) + 1)
    if m["status"] == "down": log_event("INFO", f"مدل «{m['name']}» دوباره فعال شد."); await notify_super(f"🟢 مدل <b>{html.escape(m['name'])}</b> دوباره فعال شد.")

AI_ERR = {"ai_busy": ("سرویس هوش مصنوعی موقتاً شلوغ است", "AI service is busy right now"), "ai_auth": ("دسترسی سرویس هوش مصنوعی برقرار نشد", "AI service access failed"),
          "ai_timeout": ("سرویس هوش مصنوعی پاسخ نداد", "AI service did not respond"), "ai_empty": ("پاسخ خالی از سرویس هوش مصنوعی", "Empty response from AI service"),
          "ai_none": ("سرویس هوش مصنوعی در دسترس نیست", "AI service unavailable"), "ai_error": ("خطای موقت سرویس هوش مصنوعی", "Temporary AI service error")}

def err_code(e):
    t = str(e or "").lower()
    if "429" in t or "rate limit" in t or "quota" in t or "overload" in t or "busy" in t: return "ai_busy"
    if "401" in t or "403" in t or "api key" in t or "unauthor" in t or "permission" in t or "credential" in t: return "ai_auth"
    if "timeout" in t or "timed out" in t or "connect" in t or "network" in t or "unreachable" in t: return "ai_timeout"
    if "empty" in t or "no candidates" in t: return "ai_empty"
    if "no_models" in t or "no model" in t: return "ai_none"
    return "ai_error"

def ai_err_text(code, lang="fa"): return AI_ERR.get(code if code in AI_ERR else "ai_error")[1 if lang == "en" else 0]

_model_locks = {}
def model_lock(mid):
    if mid not in _model_locks: _model_locks[mid] = asyncio.Lock()
    return _model_locks[mid]

def model_busy(mid): return model_lock(mid).locked()
def _model_ready(m):
    if m["status"] != "down": return True
    lf = parse_dt(m["last_fail"]); return bool(not lf or (now_utc() - lf) >= timedelta(minutes=MODEL_PROBE_MIN))

async def ai_chat(system, user, on_queue=None):
    models = [m for m in list_models(active_only=True) if _model_ready(m)]
    if not models: log_event("ERROR", "هیچ مدل فعالی در دسترس نیست."); return None, None, "ai_none"
    last, tried, told = "ai_error", set(), False
    while True:
        rest = [m for m in models if m["id"] not in tried]
        if not rest: return None, None, last
        free = [m for m in rest if not model_busy(m["id"])]
        if not free and on_queue and not told:
            told = True
            try: await on_queue()
            except Exception: pass
        m = (free or rest)[0]; tried.add(m["id"])
        try:
            async with model_lock(m["id"]):
                async with AI_SEM: text = await _call_model(m, system, user)
            if not text or not text.strip(): raise RuntimeError("empty response")
            await _mark_ok(m); return text.strip(), m["name"], None
        except Exception as e: last = err_code(e); await _mark_fail(m, e)

async def test_model(mid):
    m = get_model(mid); t = time.time()
    try:
        async with model_lock(mid):
            async with AI_SEM: out = await _call_model(m, "You are a health-check. Reply with exactly one word.", "Say: READY")
        if not out or not out.strip(): raise RuntimeError("empty response")
        await _mark_ok(m); return True, out.strip()[:100], round(time.time() - t, 1)
    except Exception as e: await _mark_fail(m, e); return False, str(e)[:200], round(time.time() - t, 1)

async def probe_down_models():
    for m in q("SELECT * FROM ai_models WHERE active=1 AND status='down' ORDER BY last_fail LIMIT 1"):
        lf = parse_dt(m["last_fail"])
        if not lf or (now_utc() - lf) >= timedelta(minutes=MODEL_PROBE_MIN): await test_model(m["id"])

def any_model_available(): return any(_model_ready(m) for m in list_models(active_only=True))
def models_free_count(): return sum(1 for m in list_models(active_only=True) if _model_ready(m) and not model_busy(m["id"]))

def parse_json(text):
    if not text: return None
    t = re.sub(r"```(?:json|JSON)?", "", text).strip(); s, e = t.find("{"), t.rfind("}")
    if s < 0 or e < 0: return None
    body = t[s:e + 1]
    base = [body, re.sub(r",\s*([}\]])", r"\1", body)]
    fixed = []
    for c in base:
        out, ins, esc = [], False, False
        for ch in c:
            if ins:
                if esc: esc = False
                elif ch == "\\": esc = True
                elif ch == '"': ins = False
                elif ch == "\n": out.append("\\n"); continue
                elif ch == "\r": continue
                elif ch == "\t": out.append("\\t"); continue
                out.append(ch)
            else:
                if ch == '"': ins = True
                out.append(ch)
        fixed.append("".join(out))
    for cand in base + fixed + [re.sub(r",\s*([}\]])", r"\1", f) for f in fixed]:
        for strict in (True, False):
            try: return json.loads(cand, strict=strict)
            except Exception: continue
    return None

# ============================================================
# پالایش HTML و متن
ALLOWED = {"b", "strong", "i", "em", "u", "s", "del", "code", "pre", "a", "blockquote", "tg-spoiler", "span", "tg-emoji"}
def sanitize_html(text, premium=False):
    if not text: return ""
    text = str(text)
    text = re.sub(r"(?m)^[ \t]*[-–—_=*~•⸻]{3,}[ \t]*$", "", text)
    text = re.sub(r"```[a-zA-Z]*\n?", "", text); text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text); text = re.sub(r"__(.+?)__", r"<u>\1</u>", text); text = re.sub(r"~~(.+?)~~", r"<s>\1</s>", text)
    text = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<i>\1</i>", text); text = re.sub(r"\|\|(.+?)\|\|", r"<tg-spoiler>\1</tg-spoiler>", text)
    text = re.sub(r"^#{1,6}\s*(.+)$", r"<b>\1</b>", text, flags=re.M); text = re.sub(r"^\s*>\s?(.+)$", r"<blockquote>\1</blockquote>", text, flags=re.M); text = re.sub(r"^\s*[-*]\s+", "• ", text, flags=re.M)
    text = re.sub(r"<br\s*/?>", "\n", text, flags=re.I).replace("</p>", "\n\n").replace("<p>", ""); text = re.sub(r"</?(ul|ol|div|h[1-6]|section|article)[^>]*>", "\n", text); text = re.sub(r"<li[^>]*>", "• ", text).replace("</li>", "\n")
    out, stack = [], []
    for part in re.split(r"(<[^>]+>)", text):
        m = re.match(r"<(/?)([a-zA-Z-]+)([^>]*)>", part)
        if not m: out.append(html.escape(html.unescape(part), quote=False)); continue
        closing, tag, attrs = m.group(1), m.group(2).lower(), m.group(3); tag = {"strong": "b", "em": "i", "del": "s"}.get(tag, tag)
        if tag not in ALLOWED: continue
        if tag == "span":
            if "tg-spoiler" not in attrs: continue
            tag = "tg-spoiler"
        if tag == "tg-emoji" and not premium: continue
        if closing:
            if tag in stack:
                while stack:
                    t = stack.pop(); out.append(f"</{t}>")
                    if t == tag: break
        else:
            if tag == "a":
                h = re.search(r'href=["\']([^"\']+)["\']', attrs)
                if not h: continue
                out.append(f'<a href="{html.escape(h.group(1), quote=True)}">')
            elif tag == "tg-emoji":
                eid = re.search(r'emoji-id=["\']?(\d+)', attrs)
                if not eid: continue
                out.append(f'<tg-emoji emoji-id="{eid.group(1)}">')
            elif tag == "blockquote" and "expandable" in attrs: out.append("<blockquote expandable>")
            else: out.append(f"<{tag}>")
            stack.append(tag)
    while stack: out.append(f"</{stack.pop()}>")
    return tidy_html("".join(out))

def tidy_html(t):
    t = t.replace("\r", ""); t = re.sub(r"[ \t]+\n", "\n", t); t = re.sub(r"(?<!\n)\n?•", "\n•", t)
    t = re.sub(r"(</b>|</blockquote>)\n(?!\n)(?!•)", r"\1\n\n", t); t = re.sub(r"([.!?؟۔])\n(?!\n)(?!•)(?=\S)", r"\1\n\n", t)
    t = re.sub(r"\n{3,}", "\n\n", t); return t.strip()

def downgrade_html(t):
    t = re.sub(r"</?tg-emoji[^>]*>", "", t or ""); t = re.sub(r"</?tg-spoiler>", "", t); t = t.replace("<blockquote expandable>", "<blockquote>")
    return sanitize_html(t, premium=False)

def strip_tags(t): return html.unescape(re.sub(r"<[^>]+>", "", t or ""))

def salvage_post(raw):
    if not raw: return ""
    t = re.sub(r"```[a-zA-Z]*\n?", "", str(raw)).strip()
    if not t.startswith("{"): return t
    depth, ins, esc, end = 0, False, False, -1
    for idx, ch in enumerate(t):
        if ins:
            if esc: esc = False
            elif ch == "\\": esc = True
            elif ch == '"': ins = False
        elif ch == '"': ins = True
        elif ch == "{": depth += 1
        elif ch == "}":
            depth -= 1
            if depth <= 0: end = idx; break
    j = parse_json(t[:end + 1] if end >= 0 else t)
    if isinstance(j, dict):
        p = str(j.get("post") or "").strip()
        if p: return p
        f = str(j.get("full") or "").strip()
        if f: return f
    if end >= 0:
        rest = t[end + 1:].strip()
        if len(strip_tags(rest)) >= 40: return rest
    if end < 0:
        m = None
        for mm in re.finditer(r'":\s*"', t): m = mm
        if m:
            rest = t[m.end():].strip()
            if len(strip_tags(rest)) >= 40: return rest
    lines = [ln for ln in t.splitlines() if not re.match(r'^\s*"?[A-Za-z_][A-Za-z_0-9 ]{2,24}"?\s*:', ln) and not re.fullmatch(r'\s*[{}\[\],]*\s*', ln)]
    return "\n".join(lines).strip() or t

def _cut_pos(text, limit):
    cut = text[:limit]; nl = cut.rfind("\n")
    if nl > limit * 0.5: return nl
    pos = -1
    for m in re.finditer(r'[.!?؟…]+["»”’)\]]*(?=</[a-zA-Z]|\s|$)', cut): pos = m.end()
    if pos > limit * 0.4: return pos
    sp = cut.rfind(" ")
    return sp if sp > limit * 0.4 else len(cut)

def split_post_html(text, limit, premium=True):
    if len(text) <= limit: return text, ""
    pos = _cut_pos(text, limit); head_raw, rest_raw = text[:pos], text[pos:]
    if rest_raw[:1] not in ("<", "", "\n", " ") and ">" in rest_raw[:80]:
        gt = rest_raw.find(">")
        if "<" not in rest_raw[:gt]: rest_raw = rest_raw[gt + 1:]
    head = sanitize_html(re.sub(r"<[^>]*$", "", head_raw), premium=premium).rstrip() + " …"
    rest = sanitize_html(rest_raw, premium=premium).strip()
    return head, rest

def fit_html(text, limit, premium=True):
    if len(text) <= limit: return text, False
    return split_post_html(text, limit, premium)[0], True

def clean_ai_text(t, s=None):
    if not t: return t
    t = str(t).replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\t", " ")
    names = [str(c.get("name", "")).strip() for c in (s or {}).get("criteria", []) if c.get("name")]
    names += ["ارزش محتوایی", "غیرتبلیغاتی بودن", "کیفیت و کامل بودن", "ارتباط با موضوع کانال", "تازگی", "Content value", "Non-promotional", "Quality & completeness", "Relevance to channel topic", "Relevance", "Freshness"]
    num = r'(?:10|[0-9۰-۹])(?:[.,][0-9۰-۹])?'
    pat = re.compile(r'["“«\']?([^"”»:\n]{2,40})(?:\s*:\s*["”»\']?\s*|\s*["”»\']?\s*:\s*)' + num + r'\s*[,،.؛;]?')
    def rep(m):
        label = m.group(1).strip()
        return "" if any(label and (label in n or n in label) for n in names) else m.group(0)
    
    # ایمن‌سازی: حداکثر ۴ بار تکرار حلقه برای پیشگیری از نوسان یا قفل CPU
    loop_count = 0
    prev = None
    while prev != t and loop_count < 4:
        prev = t
        t = pat.sub(rep, t)
        loop_count += 1

    t = re.sub(r'(?m)^\s*["”»،,{}\[\].…؛:!؟]+\s*$\n?', "", t)
    t = re.sub(r'''\[([^\]\n]{1,160})\]\((https?://[^)\s"']{4,})\)''', lambda m: m.group(2) if m.group(1).strip() in m.group(2) else f'<a href="{m.group(2)}">{m.group(1).replace(chr(34), "")}</a>', t)
    t = re.sub(r"\[([^\]\n]{0,160})\]\(\s*\)", r"\1", t)
    t = re.sub(r"(?<![\w])['‘’]([\w؀-ۿ][\w؀-ۿ \-]{0,38}[\w؀-ۿ]|[\w؀-ۿ])['‘’](?![\w])", r"\1", t)
    em = re.compile(r"[\U0001F000-\U0001FAFF]")
    hits = em.findall(t)
    if hits:
        t = em.sub("", t).replace("️", ""); t = re.sub(r'<a href="[^"]*">\s*</a>', " ", t)
        t = t.rstrip() + " " + hits[-1]
    t = re.sub(r"(?m)^[ \t]+|[ \t]+$", "", t); t = re.sub(r"[ \t]{2,}", " ", t)
    t = re.sub(r"\n{3,}", "\n\n", t)
    parts = re.split(r"(<pre>.*?</pre>|<code>.*?</code>)", t, flags=re.S)
    for i in range(0, len(parts), 2): parts[i] = re.sub(r"(?<!\n)\n(?!\n)", "\n\n", parts[i])
    t = "".join(parts)
    blocks, seen, keep = t.split("\n\n"), set(), []
    for b in blocks:
        k = re.sub(r"<[^>]+>", " ", b); k = re.sub(r"[\s‌]+", " ", k).strip().lower()
        if k and k in seen: continue
        if k: seen.add(k)
        keep.append(b)
    t = "\n\n".join(keep).strip()
    return t

def strip_source_url(t, url):
    if not t or not url: return t
    host = re.sub(r"^[a-zA-Z]+://(www\.)?", "", str(url)).split("/")[0].strip().lower()
    if not host or "." not in host: return t
    h = re.escape(host)
    t = re.sub(r'<a href="[^"]*' + h + r'[^"]*"[^>]*>.*?</a>', " ", t, flags=re.I | re.S)
    t = re.sub(r"""https?://[^\s<>"']*""" + h + r"""[^\s<>"']*""", " ", t, flags=re.I)
    t = re.sub(r"(?m)^[ \t]+$", "", t)
    return t

def finish_ok(t):
    if not t: return t
    e = re.sub(r"(</[a-zA-Z]+>|\s)+$", "", t)
    if e and re.search(r"[\w؀-ۿ،,؛:]$", e): return t.rstrip() + " …"
    return t

def split_html(text, limit=MSG_LIMIT):
    if len(text) <= limit: return [text]
    chunks, cur = [], ""
    for para in text.split("\n"):
        if len(cur) + len(para) + 1 > limit: chunks.append(sanitize_html(cur, premium=True)); cur = para
        else: cur = f"{cur}\n{para}" if cur else para
    if cur: chunks.append(sanitize_html(cur, premium=True))
    return chunks

def preview_text(html_text, n=100):
    t = re.sub(r"\s+", " ", strip_tags(html_text).replace("\n", " ")).strip()
    if len(t) <= n: return html.escape(t)
    cut = t[:n]; sp = cut.rfind(" "); return html.escape(cut[:sp] if sp > n * 0.6 else cut) + " …"

def headline_of(html_text):
    first = (html_text or "").strip().split("\n", 1)[0]; return sanitize_html(first, premium=True)[:900]

# ============================================================
# کشف و استخراج مقاله
FEED_ACCEPT = "application/rss+xml, application/atom+xml, application/rdf+xml, application/xml;q=0.9, text/xml;q=0.9, */*;q=0.5"
FEED_PATHS = ("/feed", "/feed/", "/rss", "/rss/", "/rss.xml", "/feed.xml", "/atom.xml", "/index.xml", "/feeds/posts/default?alt=rss", "/?feed=rss2", "/feed/rss", "/feed/atom", "/rss/all", "/rss/news", "/news/rss", "/news/feed", "/blog/feed", "/fa/rss", "/en/rss", "/feeds")
SITEMAP_PATHS = ("/news-sitemap.xml", "/sitemap-news.xml", "/sitemap_news.xml", "/post-sitemap.xml", "/sitemap-posts.xml", "/sitemap.xml", "/sitemap_index.xml")

def clean_url(u):
    try:
        p = urlparse(str(u).strip()); qs = [(k, v) for k, v in parse_qsl(p.query, keep_blank_values=True) if not k.lower().startswith(("utm_", "fbclid", "gclid", "mc_", "ref", "igshid"))]
        return normalize_url(p._replace(query=urlencode(qs), fragment="").geturl())
    except Exception: return normalize_url(u)

def _struct_dt(st):
    try: return datetime(*st[:6], tzinfo=UTC).isoformat() if st else None
    except Exception: return None

def _entry_dt(e):
    for k in ("published_parsed", "updated_parsed", "created_parsed"):
        d = _struct_dt(e.get(k))
        if d: return d
    for k in ("published", "updated", "dc_date", "date"):
        d = parse_dt(e.get(k))
        if d: return d.isoformat()
    return None

BAD_MEDIA = re.compile(r"(logo|sprite|placeholder|avatar|profile|icon|favicon|blank|default|noimage|no-image|pixel|spacer|1x1|advert|banner|watermark)", re.I)
def _bad_media_url(u):
    if not u or not str(u).startswith("http"): return True
    p = urlparse(str(u)).path.lower()
    if p.endswith((".svg", ".ico")): return True
    return bool(BAD_MEDIA.search(p))

def _mk_media(u, kind, page=""):
    return None if _bad_media_url(u) else {"url": str(u), "kind": kind, "page": page or ""}

def _entry_media(e, page=""):
    vids = []
    for m in (e.get("media_content") or []) + (e.get("media_thumbnail") or []):
        u = m.get("url"); t = (m.get("type") or "").lower()
        if u and ("video" in t or re.search(r"\.(mp4|webm|mov|m4v)(\?|$)", u, re.I)): vids.append(u)
        if u and (m.get("medium") == "image" or "image" in t or re.search(r"\.(jpe?g|png|webp|gif)(\?|$)", u, re.I)):
            got = _mk_media(u, "animation" if u.lower().split("?")[0].endswith(".gif") else "photo", page)
            if got: return got
    for enc in e.get("enclosures") or []:
        u = enc.get("href") or enc.get("url"); t = (enc.get("type") or "").lower()
        if u and t.startswith("video/"): vids.append(u)
        if u and t.startswith("image/"):
            got = _mk_media(u, "photo", page)
            if got: return got
    h = _entry_html(e)
    for m in re.finditer(r'<img[^>]+src=["\']([^"\']+)["\']', h or ""):
        got = _mk_media(m.group(1), "photo", page)
        if got: return got
    for u in vids:
        got = _mk_media(u, "video", page)
        if got: return got
    return None

def _entry_html(e):
    c = e.get("content")
    if c and isinstance(c, list) and c[0].get("value"): return c[0]["value"]
    return e.get("summary") or e.get("description") or ""

def _feed_items(feed, base, limit):
    items, seen = [], set()
    for e in feed.entries[:limit * 2]:
        link = e.get("link") or next((l.get("href") for l in e.get("links", []) if l.get("rel") == "alternate"), None) or e.get("id") or ""
        if not link: continue
        if not str(link).startswith("http"): link = urljoin(base, link)
        link = clean_url(link)
        if link in seen or not urlparse(link).netloc: continue
        seen.add(link); items.append({"url": link, "title": re.sub(r"\s+", " ", strip_tags(e.get("title") or "")).strip(), "published": _entry_dt(e), "html": _entry_html(e), "media": _entry_media(e, link)})
        if len(items) >= limit: break
    return items

def _sitemap_items(xml, limit):
    out, since = [], (now_utc() - timedelta(days=7)).isoformat()
    for m in re.finditer(r"<url>(.*?)</url>", xml, re.S):
        blk = m.group(1); loc = re.search(r"<loc>\s*(.*?)\s*</loc>", blk, re.S)
        if not loc: continue
        d = re.search(r"<(?:news:)?publication_date>\s*(.*?)\s*<", blk) or re.search(r"<lastmod>\s*(.*?)\s*<", blk); t = re.search(r"<news:title>\s*(.*?)\s*</news:title>", blk, re.S)
        pub = parse_dt(d.group(1)) if d else None
        if pub and pub.isoformat() < since: continue
        out.append({"url": clean_url(html.unescape(loc.group(1))), "title": html.unescape(strip_tags(t.group(1))).strip() if t else "", "published": pub.isoformat() if pub else None, "html": "", "media": None})
    out.sort(key=lambda x: x["published"] or "", reverse=True); return out[:limit]

def _parse_any(content, base, limit):
    head = content[:4096].lower()
    if b"<sitemapindex" in head: return None
    if b"<urlset" in head: return _sitemap_items(content.decode("utf-8", "ignore"), limit) or None
    if b"<html" in head and not (b"<rss" in head or b"<feed" in head or b"<rdf" in head): return None
    try: f = feedparser.parse(content)
    except Exception: return None
    return _feed_items(f, base, limit) if f.entries else None

async def _get(url, cond=None, feed=False):
    h = {"Accept": FEED_ACCEPT} if feed else {}
    if cond: h.update(cond)
    r = await fetch(url, headers=h)
    if r.status_code in (403, 406, 429, 503):
        p = urlparse(url); ref = f"{p.scheme}://{p.netloc}/"
        for extra in ({"User-Agent": UA_FEED}, {"Referer": ref, "Accept-Language": "en-US,en;q=0.9,fa;q=0.8", "Sec-Fetch-Mode": "navigate"}):
            try:
                r2 = await fetch(url, headers={**h, **extra})
                if r2.status_code == 200: return r2
            except Exception: pass
    return r

def _html_links(soup, base_url, limit):
    base = hostname(base_url); scored, seen = [], set()
    for a in soup.find_all("a", href=True):
        try: href = clean_url(urljoin(base_url, a["href"]))
        except Exception: continue
        p = urlparse(href); path = p.path.strip("/")
        if hostname(href) != base or href in seen or href.rstrip("/") == base_url.rstrip("/") or len(path) < 8: continue
        if re.search(r"^(tag|tags|category|categories|author|page|login|search|feed|rss|wp-|about|contact|privacy|terms)(/|$)|/(tag|category|author|page)/|\.(jpe?g|png|gif|pdf|mp4|zip|xml)$", path, re.I): continue
        title = a.get_text(" ", strip=True)
        if not title and a.img: title = (a.img.get("alt") or a.img.get("title") or "").strip()
        title = re.sub(r"\s+", " ", title)
        if len(title) < 12: continue
        sc = 0
        if re.search(r"\d{4}/\d{1,2}", path): sc += 3
        if re.search(r"/(news|article|articles|post|posts|blog|story|stories|\d{4,})(/|$)", path): sc += 2
        if a.find_parent(["article", "h1", "h2", "h3"]) or a.find(["h1", "h2", "h3"]): sc += 3
        if len(title) >= 25: sc += 2
        if "/" in path: sc += 1
        if re.search(r"-\w+-\w+", path): sc += 1
        if a.find_parent(["nav", "header", "footer", "aside"]): sc -= 3
        if sc < 4: continue
        seen.add(href); scored.append((sc, {"url": href, "title": title[:200], "published": None, "html": "", "media": None}))
    scored.sort(key=lambda x: -x[0]); return [x[1] for x in scored[:limit]]

API_ARRAY_KEYS = ("articles", "items", "results", "data", "posts", "news", "response", "docs", "entries", "stories", "hits", "records", "list", "feed")
def _api_pick_list(j, depth=0):
    if isinstance(j, list): return j if (j and isinstance(j[0], dict)) else []
    if not isinstance(j, dict) or depth > 4: return []
    for k in API_ARRAY_KEYS:
        v = j.get(k)
        if isinstance(v, list) and v and isinstance(v[0], dict): return v
        if isinstance(v, dict):
            got = _api_pick_list(v, depth + 1)
            if got: return got
    best = []
    for v in j.values():
        if isinstance(v, list) and v and isinstance(v[0], dict) and len(v) > len(best): best = v
        elif isinstance(v, dict) and not best:
            got = _api_pick_list(v, depth + 1)
            if got: best = got
    return best

def _api_first(d, *names):
    for n in names:
        v = d.get(n)
        if isinstance(v, dict): v = v.get("rendered") or v.get("url") or v.get("href") or v.get("src") or v.get("value") or v.get("full") or v.get("large") or v.get("source_url")
        if isinstance(v, list) and v: v = v[0].get("url") or v[0].get("src") or v[0].get("href") if isinstance(v[0], dict) else v[0]
        if isinstance(v, (str, int, float)) and str(v).strip(): return str(v).strip()
    return ""

def _api_items(raw, base, limit):
    try: j = json.loads(raw) if isinstance(raw, (str, bytes, bytearray)) else raw
    except Exception: return []
    out, seen = [], set()
    for d in _api_pick_list(j)[:max(limit * 3, 30)]:
        if not isinstance(d, dict): continue
        u = _api_first(d, "url", "link", "canonical_url", "webUrl", "web_url", "permalink", "guid", "source_url", "shortlink")
        if not u.startswith("http"): u = urljoin(base, u) if u.startswith("/") else ""
        if not u.startswith("http"): continue
        u = clean_url(u)
        if u in seen: continue
        seen.add(u)
        title = strip_tags(_api_first(d, "title", "headline", "name", "heading", "subject"))
        body = _api_first(d, "content", "body", "text", "description", "summary", "excerpt", "abstract", "trailText")
        pub = _api_first(d, "publishedAt", "published_at", "published", "pubDate", "date", "date_published", "created_at", "createdAt", "updated_at", "webPublicationDate")
        pd = parse_dt(pub); img = _api_first(d, "urlToImage", "image", "image_url", "imageUrl", "thumbnail", "thumb", "enclosure", "cover", "featured_image", "picture", "media")
        vid = _api_first(d, "video", "video_url", "videoUrl", "mp4")
        media = (_mk_media(vid, "video", u) if vid else None) or (_mk_media(img, "photo", u) if img else None)
        out.append({"url": u, "title": re.sub(r"\s+", " ", title)[:300], "published": pd.isoformat() if pd else None, "html": body if "<" in body else "", "media": media})
        if len(out) >= limit: break
    out.sort(key=lambda x: x["published"] or "", reverse=True); return out

def _has_api(src):
    try: return bool(src["api_url"])
    except Exception: return False

async def _api_discover(src, limit):
    api = str(src["api_url"]); key = (src["api_key"] or "").strip()
    url = api
    for ph in ("{key}", "{apikey}", "{api_key}", "{token}", "{APIKEY}"): url = url.replace(ph, key)
    h = {"Accept": "application/json, text/json, */*;q=0.5"}
    if key and key not in url: h.update({"Authorization": f"Bearer {key}", "X-Api-Key": key, "apikey": key})
    r = await fetch(url, headers=h)
    if r.status_code != 200: raise FetchError(r.status_code, url)
    items = _api_items(r.text, url, limit)
    if not items: raise RuntimeError("API: no items")
    source_ok(src["id"]); return items, True, "api"

async def discover_source(src, limit=25, use_cache=True):
    cond = {}
    if src.get("etag"): cond["If-None-Match"] = src["etag"]
    if src.get("last_modified"): cond["If-Modified-Since"] = src["last_modified"]
    try:
        if _has_api(src): return await _api_discover(src, limit)
        if src["feed_url"] and use_cache:
            r = await _get(src["feed_url"], cond, feed=True)
            if r.status_code == 304: source_ok(src["id"], src["feed_url"], src.get("etag"), src.get("last_modified")) if src.get("id") else None; return [], False, "feed"
            if r.status_code == 200:
                items = _parse_any(r.content, src["feed_url"], limit)
                if items: source_ok(src["id"], src["feed_url"], r.headers.get("etag"), r.headers.get("last-modified")); return items, True, "sitemap" if b"<urlset" in r.content[:4096].lower() else "feed"
        r = await _get(src["url"], feed=False)
        if r.status_code != 200: raise FetchError(r.status_code, src["url"])
        items = _parse_any(r.content, src["url"], limit)
        if items: source_ok(src["id"], src["url"], r.headers.get("etag"), r.headers.get("last-modified")) if src.get("id") else None; return items, True, "feed"
        soup = BeautifulSoup(r.text, "lxml"); p = urlparse(src["url"]); origin = f"{p.scheme}://{p.netloc}"; cands = []
        for tag in soup.find_all("link", attrs={"type": re.compile(r"application/(rss|atom|rdf)\+xml|application/feed\+json", re.I)}):
            if tag.get("href"): cands.append(urljoin(src["url"], tag["href"]))
        for a in soup.find_all("a", href=True):
            h = urljoin(src["url"], a["href"])
            if re.search(r"(/|\.)(rss|feed|atom)s?(/|\.xml|\?|$)", h, re.I) and (hostname(h) == hostname(src["url"]) or "feedburner" in h or "feeds." in h): cands.append(h)
        if p.path.strip("/"): cands += [src["url"] + g for g in ("/feed", "/rss", "/feed/", "/rss.xml", "/atom.xml")]
        cands += [origin + g for g in FEED_PATHS]
        seen = set()
        for fu in [c for c in cands if not (c in seen or seen.add(c))][:14]:
            try: rr = await _get(fu, feed=True)
            except Exception: continue
            if rr.status_code == 200:
                items = _parse_any(rr.content, fu, limit)
                if items: source_ok(src["id"], fu, rr.headers.get("etag"), rr.headers.get("last-modified")); return items, True, "feed"
        smaps = list(SITEMAP_PATHS)
        try:
            rb = await fetch(origin + "/robots.txt", timeout=10)
            if rb.status_code == 200: smaps = [m.strip() for m in re.findall(r"(?im)^sitemap:\s*(\S+)", rb.text)][:3] + smaps
        except Exception: pass
        for sp in smaps[:9]:
            su = sp if sp.startswith("http") else origin + sp
            try: rr = await _get(su, feed=True)
            except Exception: continue
            if rr.status_code != 200: continue
            head = rr.content[:4096].lower()
            if b"<urlset" in head:
                items = _sitemap_items(rr.content.decode("utf-8", "ignore"), limit)
                if items: source_ok(src["id"], su) if src.get("id") else None; return items, True, "sitemap"
            elif b"<sitemapindex" in head:
                kids = re.findall(r"<sitemap>.*?<loc>\s*(.*?)\s*</loc>", rr.content.decode("utf-8", "ignore"), re.S)
                pref = [k for k in kids if re.search(r"news|post|article|blog|\d{4}", k, re.I)] or kids
                for ku in pref[-2:]:
                    try: rk = await _get(html.unescape(ku), feed=True)
                    except Exception: continue
                    if rk.status_code == 200 and b"<urlset" in rk.content[:4096].lower():
                        items = _sitemap_items(rk.content.decode("utf-8", "ignore"), limit)
                        if items: source_ok(src["id"], html.unescape(ku)) if src.get("id") else None; return items, True, "sitemap"
        items = _html_links(soup, src["url"], limit); source_ok(src["id"]) if src.get("id") else None; return items, True, "html"
    except Exception as e: source_fail(src["id"], e) if src.get("id") else None; raise

def _probe_status(e):
    st = getattr(e, "status", None)
    if isinstance(st, int): return st
    r = getattr(e, "response", None); st = getattr(r, "status_code", None)
    return int(st) if isinstance(st, int) else 0

async def probe_source(src, lang="fa", added=False):
    off = tr(lang, "src_added_off" if added else "src_now_off")
    try:
        items, _, m = await discover_source(src, use_cache=False)
    except Exception as e:
        set_source_active(src["id"], False, "active")
        return False, tr(lang, "src_403" if _probe_status(e) in (401, 403, 406, 451) else "src_dead") + off
    if not items:
        set_source_active(src["id"], False, "active")
        return False, tr(lang, "src_dead") + off
    return True, tr(lang, "src_added", n=len(items), m=m)

# ============================================================
# استخراج متن مقاله
def _ld_image(soup):
    for sc in soup.find_all("script", attrs={"type": re.compile("ld\\+json", re.I)})[:6]:
        try: data = json.loads(sc.string or sc.get_text() or "{}")
        except Exception: continue
        nodes = data if isinstance(data, list) else [data]
        if isinstance(data, dict) and isinstance(data.get("@graph"), list): nodes = data["@graph"]
        for node in nodes:
            if not isinstance(node, dict): continue
            c = node.get("image") or node.get("thumbnailUrl")
            if isinstance(c, dict): c = c.get("url")
            if isinstance(c, list) and c: c = c[0].get("url") if isinstance(c[0], dict) else c[0]
            if isinstance(c, str) and c.strip(): return c.strip()
    return ""

def _img_src(tag):
    u = tag.get("src") or tag.get("data-src") or tag.get("data-original") or tag.get("data-lazy-src") or ""
    if not u:
        ss = tag.get("srcset") or tag.get("data-srcset") or ""
        u = ss.split(",")[0].strip().split(" ")[0] if ss else ""
    return u

def _find_media(soup, base):
    def meta(*names):
        for n in names:
            t = soup.find("meta", property=n) or soup.find("meta", attrs={"name": n})
            if t and t.get("content"): return urljoin(base, t["content"].strip())
        return ""
    vt = (meta("og:video:type") or "").lower(); v = meta("og:video:secure_url", "og:video:url", "og:video", "twitter:player:stream")
    if v and (re.search(r"\.(mp4|mov|webm|m4v)(\?|$)", v, re.I) or "mp4" in vt or "video/" in vt):
        got = _mk_media(v, "video", base)
        if got: return got
    for tag in soup.find_all(["video", "source"]):
        s = tag.get("src") or tag.get("data-src") or ""
        if s and re.search(r"\.(mp4|webm|mov|m4v)(\?|$)", s, re.I):
            got = _mk_media(urljoin(base, s), "video", base)
            if got: return got
    img = meta("og:image:secure_url", "og:image", "twitter:image", "twitter:image:src")
    if not img:
        l = soup.find("link", rel="image_src"); img = urljoin(base, l["href"]) if l and l.get("href") else ""
    if not img:
        c = _ld_image(soup); img = urljoin(base, c) if c else ""
    if not img:
        for tag in soup.find_all("img")[:60]:
            u = _img_src(tag)
            if not u: continue
            u = urljoin(base, u)
            if _bad_media_url(u): continue
            try: w = int(re.sub(r"\D", "", str(tag.get("width") or "0")) or 0)
            except Exception: w = 0
            if w >= 300 or re.search(r"\.(jpe?g|png|webp)(\?|$)", u, re.I): img = u; break
    if img:
        got = _mk_media(img, "animation" if img.lower().split("?")[0].endswith(".gif") else "photo", base)
        if got: return got
    return None

def _soup_text(soup):
    for t in soup(["script", "style", "noscript", "nav", "header", "footer", "aside", "form", "iframe"]): t.decompose()
    cands = soup.find_all(["article", "main"]) + [soup.find(attrs={"role": "main"})] + soup.find_all(attrs={"itemprop": "articleBody"}) + soup.find_all("div", class_=re.compile(r"(article|post|entry|content|body|story|text|news|detail)", re.I))[:30]
    def blocks(c):
        out = []
        for x in c.find_all(["p", "li", "h2", "h3", "h4", "blockquote"]):
            t = x.get_text(" ", strip=True)
            if not t: continue
            if x.name in ("h2", "h3", "h4"):
                if 3 <= len(t) <= 160: out.append(t)
            elif x.name == "li":
                if len(t) > 25: out.append("• " + t)
            elif len(t) > 25: out.append(t)
        return out
    seen, merged = set(), []
    for c in sorted([c for c in cands if c], key=lambda c: len(c.get_text(" ", strip=True)), reverse=True)[:6]:
        for t in blocks(c):
            k = t[:90]
            if k in seen: continue
            seen.add(k); merged.append(t)
    best = "\n\n".join(merged)
    if len(best) >= 400: return best
    alt = "\n\n".join(t for t in blocks(soup) if t)
    return max(best, alt, key=len)

def _next_page_url(soup, base):
    t = soup.find("link", rel="next") or soup.find("a", rel="next")
    u = (t.get("href") if t else "") or ""
    if not u: return ""
    u = urljoin(base, u.strip())
    return u if u.startswith("http") and clean_url(u) != clean_url(base) else ""

def _traf(raw, url):
    try: data = trafilatura.extract(raw, url=url, include_comments=False, include_tables=True, include_formatting=False, output_format="json", with_metadata=True, favor_recall=True)
    except Exception: data = None
    try: return json.loads(data) if data else {}
    except Exception: return {}

def _parse_page(raw, url):
    d = _traf(raw, url); soup = BeautifulSoup(raw, "lxml")
    def meta(*names):
        for n in names:
            t = soup.find("meta", property=n) or soup.find("meta", attrs={"name": n})
            if t and t.get("content"): return t["content"].strip()
        return ""
    title = (d.get("title") or meta("og:title", "twitter:title") or (soup.h1.get_text(" ", strip=True) if soup.h1 else "") or (soup.title.string if soup.title and soup.title.string else "") or "").strip()
    pub = None
    if d.get("date"):
        try: pub = datetime.strptime(d["date"][:10], "%Y-%m-%d").replace(tzinfo=UTC).isoformat()
        except Exception: pub = None
    if not pub:
        for n in ("article:published_time", "og:published_time", "pubdate", "publishdate", "publish-date", "date", "DC.date.issued", "article:modified_time", "og:updated_time"):
            v = parse_dt(meta(n))
            if v: pub = v.isoformat(); break
    if not pub:
        t = soup.find("time", datetime=True); v = parse_dt(t["datetime"]) if t else None
        if not v:
            m = re.search(r'"datePublished"\s*:\s*"([^"]+)"', raw); v = parse_dt(m.group(1)) if m else None
        pub = v.isoformat() if v else None
    media = _find_media(soup, url); nxt = _next_page_url(soup, url); text = (d.get("text") or "").strip()
    soup_t = _soup_text(soup)
    if len(soup_t) > max(400, len(text) * 1.3): text = soup_t
    if len(text) < 250: text = max(text, soup_t, key=len)
    return {"title": re.sub(r"\s+", " ", title)[:300], "text": text, "published": pub, "media": media, "author": d.get("author"), "site": d.get("sitename"), "next": nxt}

def _html_to_text(h):
    if not h: return ""
    soup = BeautifulSoup(h, "lxml")
    for t in soup(["script", "style", "noscript"]): t.decompose()
    return re.sub(r"\n{3,}", "\n\n", soup.get_text("\n", strip=True))

def _merge_text(a, b):
    seen = {p.strip()[:90] for p in a.split("\n\n") if p.strip()}; out = [a]
    for p in b.split("\n\n"):
        k = p.strip()[:90]
        if len(k) < 20 or k in seen: continue
        seen.add(k); out.append(p.strip())
    return "\n\n".join(out)

async def extract_article(url, fallback_html=""):
    raw = None
    try:
        r = await _get(url, feed=False)
        if r.status_code == 200 and "html" in r.headers.get("content-type", "text/html").lower(): raw = r.text
    except Exception: pass
    page = await asyncio.to_thread(_parse_page, raw, url) if raw else {"title": "", "text": "", "published": None, "media": None, "author": None, "site": None, "next": ""}
    seen_pages, nxt, hops = {clean_url(url)}, page.get("next") or "", 0
    while nxt and hops < max(0, MAX_ARTICLE_PAGES - 1) and len(page["text"]) < MAX_ARTICLE_CHARS:
        hops += 1
        if clean_url(nxt) in seen_pages: break
        seen_pages.add(clean_url(nxt))
        try:
            r2 = await _get(nxt, feed=False)
            if r2.status_code != 200: break
            p2 = await asyncio.to_thread(_parse_page, r2.text, nxt)
        except Exception: break
        if not p2 or len(p2["text"]) < 120: break
        page["text"] = _merge_text(page["text"], p2["text"])
        if not page.get("media") and p2.get("media"): page["media"] = p2["media"]
        nxt = p2.get("next") or ""
    if len(page["text"]) < 250 and fallback_html:
        fb = await asyncio.to_thread(_html_to_text, fallback_html)
        if len(fb) > len(page["text"]): page["text"] = fb
    if len(page["text"]) < 250: return None
    page["url"] = url; page["pages"] = hops + 1; page["text"] = page["text"][:MAX_ARTICLE_CHARS]; return page

# ============================================================
# فیلتر هوشمند ضد تبلیغات
AD_WORDS_BY_LANG = {
    "fa": ["رپورتاژ", "رپورتاژ آگهی", "تبلیغ", "آگهی", "اسپانسر", "کد تخفیف", "تخفیف ویژه", "همین حالا خرید", "خرید آنلاین", "تماس بگیرید", "شماره تماس", "سفارش دهید", "قیمت مناسب", "ارزان‌ترین", "بهترین قیمت", "فروش ویژه", "ثبت‌نام کنید", "ثبت نام کنید", "لینک خرید", "شرط‌بندی", "شرط بندی", "سایت شرط", "درآمد میلیونی", "وام فوری", "خرید فالوور", "مشاوره رایگان", "پیش‌فروش", "کلیک کنید"],
    "en": ["sponsored", "sponsored content", "advertorial", "promoted post", "affiliate", "buy now", "limited offer", "special offer", "discount code", "coupon code", "order now", "sign up now", "click here", "shop now", "best price", "giveaway", "casino", "betting"],
}
AD_WORDS = sorted({w for ws in AD_WORDS_BY_LANG.values() for w in ws}, key=len, reverse=True)
AD_STRONG = ["رپورتاژ", "رپورتاژ آگهی", "sponsored", "sponsored content", "advertorial", "promoted post"]

def _wordset_re(words):
    lat = [re.escape(w) for w in words if re.fullmatch(r"[\x20-\x7f]+", w)]
    oth = [re.escape(w) for w in words if not re.fullmatch(r"[\x20-\x7f]+", w)]
    parts = ([r"\b(?:" + "|".join(lat) + r")\b"] if lat else []) + ([r"(?<![\w؀-ۿ])(?:" + "|".join(oth) + r")(?![\w؀-ۿ])"] if oth else [])
    return re.compile("|".join(parts), re.I) if parts else None

AD_RE = _wordset_re(AD_WORDS); AD_STRONG_RE = _wordset_re(AD_STRONG)
AD_URL = re.compile(r"/(rpt|reportage|reportaj|sponsored|sponsor|ads?|advert|advertorial|promo|partner|pr-|press-release|reklama)[/-]", re.I)

def heuristic_ad_check(art, strict=False):
    text, title, url = art["text"], art["title"] or "", art["url"]; low = (title + "\n" + text).lower(); n = max(1, len(text) / 1000); score = 0.0; reasons = []
    if AD_URL.search(url): score += 4; reasons.append("ad-url")
    strong = {m.lower() for m in (AD_STRONG_RE.findall(low) if AD_STRONG_RE else [])}
    if strong: score += min(5, 2.5 * len(strong)); reasons.append(f"ad-strong×{len(strong)}")
    hits = [m.lower() for m in (AD_RE.findall(low) if AD_RE else [])]; distinct = len(set(hits))
    if distinct >= 2: score += min(4, (distinct - 1) * 0.9 + len(hits) / n * 0.5); reasons.append(f"ad-words×{len(hits)}/{distinct}")
    if AD_STRONG_RE and AD_STRONG_RE.search(title.lower()): score += 3; reasons.append("ad-title")
    phones = len(re.findall(r"(?<!\d)(?:\+98|0)9\d{9}(?!\d)|(?<!\d)0\d{2,3}[-\s]?\d{7,8}(?!\d)|(?<!\d)\+\d{1,3}[-\s]?\d{3}[-\s]?\d{3,4}[-\s]?\d{3,4}(?!\d)", text))
    if phones: score += 2 + phones; reasons.append(f"phone×{phones}")
    money = len(re.findall(r"\d[\d,٬.]*\s*(تومان|ریال|دلار|درهم|\$|€|£|₽|₺|₹|﷼)", text))
    if money / n > 4: score += 2; reasons.append(f"prices×{money}")
    if money and re.search(r"قیمت اصلی|original price|list price|اکنون فقط|فقط \d+([.,]\d+)?\s*(دلار|تومان|ریال|یورو|€|\$)", low): return True, "price-discount", round(score + 6, 1)
    if len(re.findall(r"t\.me/|telegram\.me/|instagram\.com/|wa\.me/|whatsapp\.com/", text)) > 1: score += 2; reasons.append("social-link")
    if len(re.findall(r"https?://", text)) / n > 6: score += 2; reasons.append("many-links")
    if len(text) < 300: score += 1.5; reasons.append("short")
    threshold = 6 if strict else 9; return score >= threshold, ", ".join(reasons), round(score, 1)

# ============================================================
# پرامپت، تولید محتوا و ترکیب
def build_prompt(s, art, want_full):
    cats = "\n".join(f"- {c['emoji']} {c['name']}: {c['style']}" for c in s["categories"]) or "- General"; crit = "\n".join(f"- {c['name']} (weight {c['weight']})" for c in s["criteria"])
    premium = ("\n- Advanced formatting is ON: you MAY also use <u>, <s>, <tg-spoiler> and <blockquote expandable>. Use them tastefully." if s.get("premium_format") else "")
    system = f"""You are the editor-in-chief and content evaluator of a Telegram channel. Output language: {s['language']}. EVERY word of the output MUST be written in {s['language']}, regardless of any other instruction. Channel topic: {s['topic'] or 'general'}.
EDITOR INSTRUCTIONS (follow strictly):
{s['prompt']}
CATEGORIES (choose exactly one and apply its style):
{cats}
EVALUATION CRITERIA (score each 0–10, honestly and strictly):
{crit}
FORMATTING RULES (mandatory, not optional):
- HUMAN VOICE: write like a skilled human editor, never like a bot or an AI. Never use divider lines like "---" or "***".
- Line 1: headline inside <b>. Then a blank line, then a one-sentence lead.
- Only these HTML tags (NO Markdown): <b>, <i>, <u>, <s>, <code>, <pre>, <a href="">, <blockquote>.
- MANDATORY: both "post" and "full" MUST contain at least one <blockquote> wrapping a key quote or figure.
- MANDATORY: <b> for key terms, names and numbers.
- PURE TEXT: "post" and "full" contain only the article itself — never scores or JSON fragments in text fields.
- "post": an engaging, COMPLETE mini-story — max {s['max_words']} words and at most {max(400, int(s['post_limit']) - 120)} characters{', ending with 2–4 relevant hashtags on the last line' if s['hashtags'] else ''}.
- "full": {'the EXPANDED bot version: deeper details, background and context (300–700 words, max 2500 characters).' if want_full else 'null'}
- If the text is an advertisement / advertorial / product-for-sale / betting promotion: is_ad=true.{premium}
Return ONLY one valid JSON object with exactly this structure:
{{"is_ad": false, "ad_reason": "", "category": "category name", "title": "headline", "scores": {{"criterion name": 0-10}}, "post": "HTML", "full": "HTML or null"}}"""
    user = f"TITLE: {art['title']}\nSOURCE: {art['url']}\nDATE: {art.get('published') or 'unknown'}\n\nARTICLE TEXT:\n{art['text']}"; return system, user

def weighted_score(s, scores):
    tot, acc = 0, 0.0
    for c in s["criteria"]:
        w = float(c.get("weight", 0)); v = scores.get(c["name"])
        if v is None:
            for k, val in scores.items():
                if c["name"][:6] in k or k[:6] in c["name"]: v = val; break
        try: v = max(0.0, min(10.0, float(v)))
        except Exception: v = 5.0
        tot += w; acc += w * v / 10
    return round(acc / tot * 100, 1) if tot else 0.0

async def generate(s, art, on_queue=None):
    want_full = len(art["text"]) > 1200; system, user = build_prompt(s, art, want_full); raw, model, err = await ai_chat(system, user, on_queue=on_queue)
    if not raw: return None, None, err
    j = parse_json(raw)
    if not j or not str(j.get("post") or "").strip(): j = {"is_ad": False, "category": s["categories"][0]["name"] if s["categories"] else "", "title": art["title"], "scores": {}, "post": clean_ai_text(salvage_post(raw), s)[:3000], "full": None}
    j["score"] = weighted_score(s, j.get("scores") or {}) if j.get("scores") else 65.0; return j, model, None

def signature_of(s, ch):
    sig = (s.get("signature") or "").strip()
    if sig.lower() == "@channel": sig = f"@{ch['username']}" if ch and ch["username"] else ""
    return sanitize_html(sig, premium=s.get("premium_format", False)) if sig else ""

def make_tail(s, ch, url):
    sig = signature_of(s, ch)
    return ("\n" + sig) if sig else ""

def ensure_quote(t):
    if not t or "<blockquote" in t.lower(): return t
    parts = str(t).split("\n\n")
    if len(parts) < 2: return t
    cand = [i for i in range(1, len(parts)) if 30 <= len(strip_tags(parts[i]).strip()) <= 500 and not parts[i].lstrip().startswith(("•", "#", "🔗", "<a", "<pre", "<code"))]
    if not cand: return t
    i = cand[len(cand) // 2] if len(cand) > 1 else cand[0]; parts[i] = f"<blockquote>{parts[i].strip()}</blockquote>"
    return "\n\n".join(parts)

def compose(s, ch, art, gen):
    prem = bool(s.get("premium_format")); post = sanitize_html(ensure_quote(clean_ai_text(salvage_post(gen.get("post") or ""), s)), premium=prem)
    full = clean_ai_text(salvage_post(gen["full"]), s) if gen.get("full") and str(gen["full"]).lower() != "null" else None
    if full: full = finish_ok(fit_html(sanitize_html(ensure_quote(full), premium=prem), BOT_FULL_MAX, prem)[0])
    core = re.sub(r"#[^\s#]+", " ", re.sub(r"<[^>]+>", " ", post)); core = re.sub(r"[\s‌]+", " ", core).strip()
    if len(core) < 120 and full and len(re.sub(r"<[^>]+>", " ", full)) >= 200:
        txt = re.sub(r"</?[a-z][^>]*>", " ", full); sen = re.split(r"(?<=[.!?؟…])\s+", txt); acc = ""
        cap_len = max(300, int(s["post_limit"]) - 160)
        for x in sen:
            if acc and len(acc) + len(x) + 1 > cap_len: break
            acc += (" " if acc else "") + x
        if len(acc) >= 120: post = sanitize_html(ensure_quote(acc + " …"), premium=prem)
    return post + make_tail(s, ch, art["url"]), full

# ============================================================
# رسانه و انتشار ایمن
def _media_headers(media):
    h = {"Accept": "image/avif,image/webp,image/*,video/*,*/*;q=0.8"}
    page = (media or {}).get("page") or ""
    try:
        p = urlparse(page)
        if p.scheme and p.netloc: h["Referer"] = f"{p.scheme}://{p.netloc}/"
    except Exception: pass
    return h

def _ext_kind(u, fallback="photo"):
    e = os.path.splitext(urlparse(str(u)).path)[1].lower()
    if e in (".mp4", ".m4v", ".mov", ".webm"): return "video"
    if e == ".gif": return "animation"
    if e in (".jpg", ".jpeg", ".png", ".webp", ".bmp"): return "photo"
    return fallback

async def download_media(media):
    if not media or not media.get("url"): return None
    for hdr in (_media_headers(media), {"User-Agent": UA_FEED, "Accept": "*/*"}):
        tmp = None
        try:
            async with FETCH_SEM:
                async with http().stream("GET", media["url"], headers=hdr, timeout=httpx.Timeout(180, connect=15)) as r:
                    if r.status_code != 200: continue
                    ct = r.headers.get("content-type", "").lower()
                    if ct.startswith("text/") or "html" in ct: return None
                    try:
                        if int(r.headers.get("content-length") or 0) > MAX_MEDIA_BYTES: return None
                    except Exception: pass
                    kind = "animation" if "gif" in ct else "photo" if ct.startswith("image/") else "video" if ct.startswith("video/") else _ext_kind(media["url"], media.get("kind") or "document")
                    ext = {"photo": ".jpg", "animation": ".gif", "video": ".mp4"}.get(kind, os.path.splitext(urlparse(media["url"]).path)[1] or ".bin")
                    tmp = tempfile.NamedTemporaryFile(delete=False, suffix=ext); size = 0
                    async for chunk in r.aiter_bytes(262144):
                        size += len(chunk)
                        if size > MAX_MEDIA_BYTES:
                            tmp.close(); os.unlink(tmp.name); return None
                        tmp.write(chunk)
                    tmp.close()
                    if size < 1024:
                        os.unlink(tmp.name); return None
                    if kind == "photo" and size > 10 * 1024 * 1024: kind = "document"
                    return tmp.name, kind
        except Exception as e:
            if tmp and os.path.exists(tmp.name):
                try: os.unlink(tmp.name)
                except Exception: pass
            log.warning(f"media: {e}")
    return None

def _is_parse_err(e): s = str(e).lower(); return "parse" in s or "entit" in s or "tag" in s or "unsupported start" in s

async def _send_media(bot, chat_id, caption, pm, media):
    kind = media.get("kind", "photo"); mf = media.get("_file")
    if not mf and kind == "photo":
        try: return await bot.send_photo(chat_id, media["url"], caption=caption, parse_mode=pm)
        except BadRequest as e:
            if _is_parse_err(e): raise
        except Exception: pass
    if not mf: mf = await download_media(media); media["_file"] = mf
    if not mf: return None
    path, k = mf
    try:
        with open(path, "rb") as f:
            fn = getattr(bot, f"send_{k}"); kw = {k: f}
            if k == "video": kw["supports_streaming"] = True
            if k in ("video", "animation", "document"): kw.update(read_timeout=240, write_timeout=600, connect_timeout=30, pool_timeout=120)
            return await fn(chat_id, caption=caption, parse_mode=pm, **kw)
    except RetryAfter: raise
    except BadRequest as e:
        if _is_parse_err(e): raise
        log.warning(f"send_{k}: {e}"); return None
    except Exception as e:
        log.warning(f"send_{k}: {e}"); return None

async def send_post(bot, chat_id, text, media=None):
    variants = [(text, "HTML"), (downgrade_html(text), "HTML"), (strip_tags(text), None)]
    for i, (t, pm) in enumerate(variants):
        try:
            if media:
                cap_ok = len(t) <= CAPTION_LIMIT; cap = t if cap_ok else (headline_of(t) if pm else strip_tags(headline_of(t)))
                m = await _send_media(bot, chat_id, cap, pm, media)
                if m:
                    if cap_ok: return m
                    return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True, reply_to_message_id=m.message_id)
            return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True)
        except RetryAfter as e:
            await asyncio.sleep(min(30, float(e.retry_after) + 1)); return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True)
        except BadRequest as e:
            if _is_parse_err(e) and i < len(variants) - 1: continue
            raise
    raise RuntimeError("format")

def msg_link(ch, msg): return f"https://t.me/{ch['username']}/{msg.message_id}" if ch["username"] else f"https://t.me/c/{str(ch['chat_id'])[4:]}/{msg.message_id}"

async def bot_can_post(bot, chat_id):
    try:
        me = await bot.get_chat_member(chat_id, bot.id)
        if me.status == "creator": return True
        return me.status == "administrator" and getattr(me, "can_post_messages", True) is not False
    except Exception: return False

async def user_is_admin(bot, chat_id, uid):
    try:
        m = await bot.get_chat_member(chat_id, uid)
        return m.status in ("creator", "administrator")
    except Exception: return False

async def publish_article(bot, aid, count_usage=True):
    a = get_article(aid)
    if not a or not a["post_html"]: return False, "not_ready"
    ch = get_channel(a["channel_id"]); admin_id = a["admin_id"]
    if not ch: return False, "no_channel"
    s = get_settings(ch["id"]); lang = s["ui_lang"]; prem = bool(s.get("premium_format"))
    if not await bot_can_post(bot, ch["chat_id"]): article_update(aid, status="failed", reason="bot_not_admin"); return False, "bot_not_admin"
    if posted_before(ch["chat_id"], a["hash"]): article_update(aid, status="failed", reason="duplicate"); return False, "duplicate"
    media = json.loads(a["media"]) if a["media"] and s["include_media"] else None
    tail = make_tail(s, ch, a["url"]); post = re.sub(r'\s*🔗 <a href="[^"]+">Source</a>\s*', "\n", a["post_html"] or ""); post = clean_ai_text(strip_source_url(post, a["url"]), s); body = post[:-len(tail)] if tail and post.endswith(tail) else post; text = post; limit = int(s["post_limit"])
    if len(post) > limit:
        cut, rest = split_post_html(body, max(200, limit - len(tail) - 100 - len(BOT_USERNAME)), prem)
        htitle = f"<b>{html.escape(a['title'] or '')}</b>"
        cfull = clean_ai_text(strip_source_url(a["full_html"], a["url"]), s) if source_bot_ok(a["source_id"]) and a["full_html"] else ""
        ftxt = cfull if cfull.strip() else ((htitle + "\n\n" + rest) if rest else htitle)
        if len(ftxt) > BOT_FULL_MAX: ftxt = fit_html(ftxt, BOT_FULL_MAX, prem)[0]
        ftxt = finish_ok(ftxt)
        key = await store_deeplink(admin_id, {"short": cut, "full": ftxt, "title": a["title"], "url": a["url"], "show_source": bool(s.get("include_link", True)), "media": {k: v for k, v in media.items() if not k.startswith("_")} if media else None, "ts": now_iso()})
        more = f'\n\n<a href="https://t.me/{BOT_USERNAME}?start=r_{key}">📖 {"بیشتر" if lang == "fa" else "more..."}</a>'
        text = cut + more + tail
    try:
        try: msg = await send_post(bot, ch["chat_id"], text, media)
        except Exception as e: article_update(aid, status="failed", reason=f"send: {str(e)[:120]}"); log_event("ERROR", f"ارسال به {ch['title']}: {e}", admin_id); return False, f"send_failed:{str(e)[:120]}"
    finally:
        if media and media.get("_file"):
            try:
                if os.path.exists(media["_file"][0]): os.unlink(media["_file"][0])
            except Exception: pass
    mark_posted(ch["chat_id"], a["hash"]); link = msg_link(ch, msg)
    article_update(aid, status="published", links=json.dumps([link]), reason="")
    if count_usage: usage_inc(admin_id, "posts")
    log_event("INFO", f"منتشر شد در {ch['title']}: {(a['title'] or '')[:60]}", admin_id); return True, link

# ============================================================
# سیستم تشخیص و گزارش چرخه (Diagnostics)
DIAG = {
    "busy": ("⏳ چرخه‌ی دیگری روی این کانال در حال اجراست", "⏳ Another cycle is running on this channel"),
    "no_channel": ("❌ کانال یافت نشد", "❌ Channel not found"), "plan_inactive": ("⛔ پلن فعال نیست", "⛔ Plan inactive"), "no_sources": ("⚠️ منبعی ثبت نشده", "⚠️ No source added"),
    "quota_posts": ("⛔ سهمیه‌ی پست امروز: {used}/{cap}", "⛔ Today's posts: {used}/{cap}"), "quota_tests": ("⛔ سهمیه‌ی تست امروز: {used}/{cap}", "⛔ Today's tests: {used}/{cap}"),
    "bot_not_admin": ("❌ ربات ادمین کانال نیست یا مجوز ارسال ندارد", "❌ Bot is not admin / can't post"),
    "src_ok": ("🌐 {name} [{m}]: {n} آیتم · 🆕 {new}", "🌐 {name} [{m}]: {n} items · 🆕 {new}"), "src_notmod": ("🌐 {name}: بدون تغییر", "🌐 {name}: unchanged"),
    "src_empty": ("🟡 {name}: فید/مقاله‌ای پیدا نشد", "🟡 {name}: no feed/articles found"), "src_fail": ("🔴 {name}: {err}", "🔴 {name}: {err}"), "src_cooldown": ("⏸ {name}: به‌تازگی بررسی شده", "⏸ {name}: checked recently"),
    "old": ("🕰 {n} قدیمی‌تر از {h} ساعت", "🕰 {n} older than {h}h"), "leftover": ("♻️ {n} باقی‌مانده از چرخه‌های قبل", "♻️ {n} left over from earlier cycles"), "retry": ("🧪 {n} مورد قبلی دوباره بررسی می‌شود", "🧪 Re-checking {n} earlier items"),
    "found": ("🔎 {n} مقاله برای بررسی", "🔎 {n} articles to process"), "none_found": ("⚠️ مقاله‌ی جدیدی نیست", "⚠️ No new article"),
    "extract_fail": ("📄 {n} بدون متن قابل استخراج", "📄 {n} without extractable text"), "undated": ("📅 {n} بدون تاریخ (رد شد)", "📅 {n} undated (skipped)"), "ad": ("🛡 {n} تبلیغ (فیلتر)", "🛡 {n} ads (filter)"),
    "ai_fail": ("🤖 خطای AI: {err}", "🤖 AI error: {err}"), "ai_ad": ("🤖 {n} تبلیغ (تشخیص AI)", "🤖 {n} ads (AI)"), "low": ("⭐ {n} زیر حداقل {min} · بهترین {best}", "⭐ {n} below {min} · best {best}"),
    "from_src": ("🌐 تولید از منبع: {name}", "🌐 Generated from source: {name}"),
    "quiet": ("🌙 ساعت خاموشی؛ در صف ماند", "🌙 Quiet hours; queued"), "review": ("📝 {n} در صفحه‌ی انتشار منتظر تأیید", "📝 {n} awaiting approval in publish page"),
    "published": ("✅ {n} منتشر شد", "✅ {n} published"), "pub_fail": ("❌ انتشار: {err}", "❌ Publish: {err}"), "detail": ("   ↳ {title} — {why}", "   ↳ {title} — {why}"),
    "hint_sources": ("→ منبع دیگری اضافه کنید یا بازه را بیشتر کنید (≤۴۸h)", "→ Add another source or widen the window (≤48h)"), "hint_score": ("→ حداقل امتیاز را کمتر کنید", "→ Lower the minimum score"),
    "hint_ads": ("→ فیلتر سخت تبلیغ را خاموش کنید", "→ Turn off strict ad filter"), "hint_ai": ("→ سرویس AI پاسخ نمی‌دهد؛ چند دقیقه بعد یا /man", "→ AI service failing; retry later or /man"),
    "hint_admin": ("→ ربات را با مجوز «ارسال پیام» ادمین کنید", "→ Make the bot admin with “post messages”"), "hint_undated": ("→ «بدون تاریخ» را روشن کنید", "→ Turn on “undated articles”"),
    "hint_extract": ("→ این منبع متن استاندارد ندارد؛ منبع دیگر", "→ Source lacks readable text; try another"), "hint_review": ("→ حالت را روی «خودکار» بگذارید", "→ Switch mode to “auto”"), "hint_quota": ("→ ارتقای پلن", "→ Upgrade plan"),
    "stage": ("📍 مرحله: {stage}", "📍 Stage: {stage}"),
}
STAGES = {"start": ("شروع", "start"), "checks": ("بررسی پلن/کانال/منبع", "checks"), "discover": ("کشف مقالات", "discovery"), "extract": ("استخراج متن", "extraction"), "filter": ("فیلتر", "filtering"), "ai": ("تولید با AI", "AI generation"), "score": ("امتیازدهی", "scoring"), "publish": ("انتشار", "publishing"), "done": ("پایان", "done")}

class Diag:
    def __init__(self): self.items, self.hints, self.stage = [], [], "start"
    def add(self, key, **kw): self.items.append((key, kw))
    def hint(self, key, **kw):
        if key not in [h[0] for h in self.hints]: self.hints.append((key, kw))
    def keys(self): return sorted({k for k, _ in self.items if k not in ("src_ok", "src_notmod", "found", "detail", "leftover", "retry")})
    def render(self, lang="fa", with_stage=True):
        i = 1 if lang == "en" else 0; lines = []
        for k, kw in self.items:
            try: lines.append(DIAG[k][i].format(**kw))
            except Exception: lines.append(DIAG[k][i])
        if with_stage: lines.append(DIAG["stage"][i].format(stage=STAGES.get(self.stage, STAGES["start"])[i]))
        for k, kw in self.hints:
            try: lines.append(DIAG[k][i].format(**kw))
            except Exception: lines.append(DIAG[k][i])
        return "\n".join(lines)
    def to_json(self): return json.dumps({"items": self.items, "hints": self.hints, "stage": self.stage}, ensure_ascii=False)

def _within_lookback(pub_iso, s):
    if not pub_iso: return bool(s["allow_undated"])
    d = parse_dt(pub_iso); return bool(d and (now_utc() - d) <= timedelta(hours=int(s["lookback_hours"])))

def _pub_err(code, lang):
    if code == "bot_not_admin": return DIAG["bot_not_admin"][1 if lang == "en" else 0]
    if code == "duplicate": return "duplicate" if lang == "en" else "تکراری"
    return code.replace("send_failed:", "")

def article_src_name(aid):
    a = get_article(aid); src = source_of_article(a) if a else None
    return ((src["title"] or "").strip() or hostname(src["url"])) if src else ""

PROG = {"fa": {"start": "شروع…", "src": "بررسی {n} منبع…", "found": "{n} مقاله پیدا شد", "extract": "استخراج {i}/{n}: {t}", "ai": "تولید با AI: {t}", "queue": "⏳ همه‌ی مدل‌ها مشغول‌اند؛ در صف پردازش…", "pub": "انتشار…", "done": "پایان"},
        "en": {"start": "Starting…", "src": "Checking {n} sources…", "found": "{n} articles found", "extract": "Extracting {i}/{n}: {t}", "ai": "Generating with AI: {t}", "queue": "⏳ All models busy; queued…", "pub": "Publishing…", "done": "Done"}}

def _res(D): return {"found": 0, "processed": 0, "accepted": 0, "rejected": 0, "queued": 0, "published": 0, "errors": 0, "links": [], "src": "", "pub": [], "diag": D, "msg": ""}

async def run_channel_cycle(bot, uid, cid, test_mode=False, progress=None):
    lk = ch_lock(cid)
    if lk.locked():
        D = Diag(); D.add("busy"); r = _res(D); r["msg"] = D.render(get_settings(cid)["ui_lang"], False); return r
    async with lk:
        async with CYCLE_SEM: return await _cycle(bot, uid, cid, test_mode, progress)

async def _cycle(bot, uid, cid, test_mode, progress):
    D = Diag(); res = _res(D); s = get_settings(cid); ch = get_channel(cid); lim = admin_limits(uid); lang = s["ui_lang"]; P = PROG[lang if lang in PROG else "fa"]
    async def p(pct, txt):
        if progress:
            try: await progress(pct, txt)
            except Exception: pass
    def fin():
        res["msg"] = D.render(lang, with_stage=False); update_settings(cid, last_end=now_iso(), last_result=res["msg"][:1500], last_diag=D.to_json()); return res
    D.stage = "checks"
    if not ch: D.add("no_channel"); return fin()
    if not lim["active"]: D.add("plan_inactive"); D.hint("hint_quota"); return fin()
    sources = list_sources(cid, active_only=True)
    if not sources: D.add("no_sources"); D.hint("hint_sources"); return fin()
    field = "tests" if test_mode else "posts"; rem = remaining(uid, field)
    if rem is not None and rem <= 0: D.add("quota_tests" if test_mode else "quota_posts", used=usage_today(uid)[field], cap=lim["daily_tests" if test_mode else "daily_posts"]); D.hint("hint_quota"); return fin()
    if not await bot_can_post(bot, ch["chat_id"]): D.add("bot_not_admin"); D.hint("hint_admin"); return fin()
    target = 1 if test_mode else min(rem if rem is not None else 99, int(s["posts_per_cycle"])); update_settings(cid, last_run=now_iso()); await p(5, P["start"])
    
    D.stage = "discover"; await p(10, P["src"].format(n=len(sources)))
    async def one(src):
        name = hostname(src["url"]); lf = parse_dt(src["last_fetch"])
        if not test_mode and lf and (now_utc() - lf) < timedelta(minutes=SOURCE_COOLDOWN_MIN): return src, name, None, False, "", "cooldown"
        try: items, changed, method = await discover_source(src, use_cache=not test_mode); return src, name, items, changed, method, None
        except Exception as e: return src, name, None, False, "", str(e)[:80]
    results = await asyncio.gather(*[one(src) for src in sources])
    leftovers = q("SELECT id,url,title,published_at FROM articles WHERE channel_id=? AND status='discovered' ORDER BY id DESC LIMIT 10", (cid,))
    candidates, all_items, n_old, seen = [], [], 0, set()
    for src, name, items, changed, method, err in results:
        if err == "cooldown": D.add("src_cooldown", name=name); continue
        if err: res["errors"] += 1; D.add("src_fail", name=name, err=err); log_event("WARN", f"منبع {src['url']}: {err}", uid); continue
        if not changed: D.add("src_notmod", name=name); continue
        if not items: D.add("src_empty", name=name); continue
        new = 0
        for it in items:
            h = url_hash(it["url"]); all_items.append((it, h))
            if h in seen or article_exists(cid, h): continue
            seen.add(h)
            if it.get("published") and not _within_lookback(it["published"], s): article_insert(uid, cid, h, it["url"], it["title"], src["id"], it["published"], "skipped", "old"); n_old += 1; continue
            aid = article_insert(uid, cid, h, it["url"], it["title"], src["id"], it.get("published"))
            if aid: candidates.append({"aid": aid, "url": it["url"], "title": it["title"], "published": it.get("published"), "html": it.get("html") or "", "media": it.get("media")}); new += 1
        D.add("src_ok", name=name, m=method, n=len(items), new=new)
        if new: q("UPDATE sources SET found_total=found_total+? WHERE id=?", (new, src["id"]), commit=True)
    candidates.sort(key=lambda c: c["published"] or "", reverse=True)
    lo = [{"aid": r["id"], "url": r["url"], "title": r["title"], "published": r["published_at"], "html": "", "media": None} for r in leftovers if r["id"] not in {c["aid"] for c in candidates}]
    if lo: D.add("leftover", n=len(lo)); candidates += lo
    if n_old: D.add("old", n=n_old, h=s["lookback_hours"])
    if not candidates and test_mode and all_items:
        retry = 0
        for it, h in all_items:
            row = q("SELECT id,status FROM articles WHERE channel_id=? AND hash=?", (cid, h), one=True)
            if row and row["status"] in ("skipped", "rejected", "failed") and not posted_before(ch["chat_id"], h):
                article_update(row["id"], status="discovered", reason=""); candidates.append({"aid": row["id"], "url": it["url"], "title": it["title"], "published": it.get("published"), "html": it.get("html") or "", "media": it.get("media")}); retry += 1
                if retry >= 5: break
        if retry: D.add("retry", n=retry)
    res["found"] = len(candidates); await p(40, P["found"].format(n=len(candidates)))
    if not candidates: D.add("none_found"); D.hint("hint_sources"); return fin()
    D.add("found", n=len(candidates))

    quiet = in_quiet(s); cnt = {"extract": 0, "undated": 0, "ad": 0, "ai_ad": 0, "low": 0}; best = 0.0; details = []; ai_err = None; i = 0; stop = False
    while i < len(candidates) and not stop:
        chunk = candidates[i:i + 3]; i += len(chunk); D.stage = "extract"
        await p(40 + int(50 * i / len(candidates)), P["extract"].format(i=i, n=len(candidates), t=(chunk[0]["title"] or chunk[0]["url"])[:40]))
        arts = await asyncio.gather(*[extract_article(c["url"], c["html"]) for c in chunk], return_exceptions=True)
        for c, art in zip(chunk, arts):
            if res["accepted"] >= target: stop = True; break
            aid = c["aid"]; res["processed"] += 1
            if not art or isinstance(art, Exception): article_update(aid, status="rejected", reason="extract_failed"); res["rejected"] += 1; cnt["extract"] += 1; continue
            if not art["title"]: art["title"] = c["title"] or hostname(c["url"])
            if not art["media"] and c["media"]: art["media"] = c["media"]
            D.stage = "filter"
            if not c["published"] and not _within_lookback(art["published"], s):
                if art["published"]: article_update(aid, status="skipped", reason="old", published_at=art["published"]); continue
                article_update(aid, status="skipped", reason="undated"); cnt["undated"] += 1; continue
            bad, why, _ = heuristic_ad_check(art, s["strict_ads"])
            if bad: article_update(aid, status="rejected", reason=f"ad_filter: {why}"); res["rejected"] += 1; cnt["ad"] += 1; details.append((art["title"], "ad: " + why)); continue
            D.stage = "ai"; pct = min(94, 40 + int(50 * i / len(candidates))); await p(pct, P["ai"].format(t=art["title"][:40]))
            async def _on_queue(_pct=pct): await p(_pct, P["queue"])
            gen, model, err = await generate(s, art, on_queue=_on_queue)
            if not gen: article_update(aid, status="failed", reason=f"ai: {err}"); res["errors"] += 1; ai_err = err; stop = True; break
            D.stage = "score"
            if gen.get("is_ad"): article_update(aid, status="rejected", reason=f"ai_ad: {gen.get('ad_reason', '')}", score=gen["score"]); res["rejected"] += 1; cnt["ai_ad"] += 1; details.append((art["title"], f"AI ad: {str(gen.get('ad_reason', ''))[:40]}")); continue
            best = max(best, gen["score"])
            if gen["score"] < float(s["min_score"]): article_update(aid, status="rejected", reason=f"score {gen['score']} < {s['min_score']}", score=gen["score"]); res["rejected"] += 1; cnt["low"] += 1; details.append((art["title"], f"score {gen['score']}")); continue
            post, full = compose(s, ch, art, gen)
            article_update(aid, title=gen.get("title") or art["title"], post_html=post, full_html=full, score=gen["score"], category=gen.get("category"), model=model, media=json.dumps(art["media"]) if art["media"] else None, published_at=art["published"], status="ready", reason=""); res["accepted"] += 1
            sname = article_src_name(aid)
            if sname: res["src"] = sname; D.add("from_src", name=sname)
            if test_mode or (s["mode"] == "auto" and not quiet):
                D.stage = "publish"; await p(96, P["pub"]); ok, out = await publish_article(bot, aid, count_usage=not test_mode)
                if ok:
                    res["published"] += 1; res["links"].append(out); res["pub"].append(((gen.get("title") or art["title"] or "")[:60], sname, out))
                    if test_mode: usage_inc(uid, "tests")
                else:
                    res["errors"] += 1; D.add("pub_fail", err=_pub_err(out, lang))
                    if out == "bot_not_admin": D.hint("hint_admin"); stop = True; break
            else: res["queued"] += 1

    if cnt["extract"]: D.add("extract_fail", n=cnt["extract"])
    if cnt["undated"]: D.add("undated", n=cnt["undated"]); D.hint("hint_undated")
    if cnt["ad"]: D.add("ad", n=cnt["ad"])
    if ai_err: D.add("ai_fail", err=ai_err_text(ai_err, lang)); D.hint("hint_ai")
    if cnt["ai_ad"]: D.add("ai_ad", n=cnt["ai_ad"])
    if cnt["low"]: D.add("low", n=cnt["low"], min=s["min_score"], best=best)
    for t, w in details[:3]: D.add("detail", title=(t or "")[:40], why=w[:50])
    if res["published"]: D.add("published", n=res["published"]); D.stage = "done"
    elif res["queued"]:
        D.add("quiet" if quiet else "review", n=res["queued"]); D.stage = "done"
        if not quiet: D.hint("hint_review")
    elif not ai_err and res["accepted"] == 0:
        top = max(cnt["ad"], cnt["low"], cnt["extract"])
        if top and cnt["ad"] == top: D.hint("hint_ads")
        elif top and cnt["low"] == top: D.hint("hint_score")
        elif top and cnt["extract"] == top: D.hint("hint_extract")
    await p(100, P["done"]); return fin()

async def flush_ready(bot, uid, cid, max_n=2):
    s = get_settings(cid)
    if s["mode"] != "auto" or in_quiet(s) or not s["enabled"]: return 0
    rem = remaining(uid, "posts"); sent = 0
    for a in articles_by_status(cid, "ready", max_n):
        if rem is not None and rem <= 0: break
        ok, _ = await publish_article(bot, a["id"])
        if ok: sent += 1; rem = None if rem is None else rem - 1
    return sent

_tick_lock = asyncio.Lock()
async def _plan_notifications():
    for uid, p, exp in activate_next_plans():
        lang = user_lang(uid) or "fa"; name = html.escape(plan_txt(p, "name", lang)); d = fmt_date(exp, admin_offset(uid))
        await notify_user(uid, f"🎉 پلن بعدی «<b>{name}</b>» فعال شد · تا {d}\n/create" if lang == "fa" else f"🎉 Next plan “<b>{name}</b>” is now active · until {d}\n/create")
    for u, stage, left in expiring_users():
        if u["next_plan_id"]: continue
        lang = u["lang"] or "fa"; p = get_plan(u["plan_id"]); name = html.escape(plan_txt(p, "name", lang)) if p else "—"
        await notify_user(u["id"], (f"⏳ پلن «{name}» حدود <b>{int(left)} ساعت</b> دیگر تمام می‌شود." if lang == "fa" else f"⏳ Plan “{name}” ends in about <b>{int(left)}h</b>."), [[("🔄 تمدید / ارتقا" if lang == "fa" else "🔄 Renew / Upgrade", "u:plans")]])
    for u in q("SELECT * FROM users WHERE plan_id IS NOT NULL AND plan_expires<=? AND next_plan_id IS NULL AND (remind_key IS NULL OR remind_key!='expired') AND banned=0", (now_iso(),)):
        q("UPDATE users SET remind_key='expired' WHERE id=?", (u["id"],), commit=True); lang = u["lang"] or "fa"
        await notify_user(u["id"], ("🔴 <b>پلن شما تمام شد؛ انتشار خودکار متوقف است.</b>" if lang == "fa" else "🔴 <b>Your plan expired; automatic publishing is paused.</b>"), [[("🔄 تمدید / ارتقا" if lang == "fa" else "🔄 Renew / Upgrade", "u:plans")]])

async def _report_failed_cycle(uid, ch, s, res):
    D = res["diag"]; fp = "|".join(D.keys()); last = (s.get("last_notified_diag") or "").split("@"); last_fp, last_ts = last[0], (parse_dt(last[1]) if len(last) > 1 else None)
    if fp == last_fp and last_ts and (now_utc() - last_ts) < timedelta(hours=24): return
    update_settings(ch["id"], last_notified_diag=f"{fp}@{now_iso()}"); lang = s["ui_lang"]
    head = f"⚠️ <b>{'چرخه بدون انتشار' if lang == 'fa' else 'Cycle published nothing'}</b> · 📢 {html.escape(ch['title'])}\n\n"
    await notify_user(uid, head + html.escape(D.render(lang)), [[("🛠 پنل کانال" if lang == "fa" else "🛠 Channel panel", f"a:ch:{ch['id']}")]])

async def _report_published(uid, ch, s, res):
    lang = s["ui_lang"]; fa = lang != "en"
    head = f"✅ <b>{'منتشر شد' if fa else 'Published'}</b> · 📢 {html.escape(ch['title'])}\n"
    body = "".join(f"\n• {html.escape(t or '—')}" + (f"\n   {tr(lang, 'test_src', name=html.escape(sn))}" if sn else "") for t, sn, _ in res["pub"][:3])
    kb = []
    if res["pub"] and res["pub"][0][2]: kb.append([("🔗 " + ("مشاهده در کانال" if fa else "View in channel"), res["pub"][0][2])])
    kb.append([("🛠 " + ("پنل کانال" if fa else "Channel panel"), f"a:ch:{ch['id']}")])
    await notify_user(uid, head + body, kb)

async def _scheduled(bot, uid, ch, s):
    try:
        res = await run_channel_cycle(bot, uid, ch["id"])
        if res["published"]: await _report_published(uid, ch, s, res)
        elif not res["queued"] and s["mode"] == "auto" and "busy" not in [k for k, _ in res["diag"].items]: await _report_failed_cycle(uid, ch, s, res)
    except Exception as e: log_event("ERROR", f"چرخه {ch['title']}: {e}", uid)

async def scheduler_tick(bot):
    if _tick_lock.locked(): return
    async with _tick_lock:
        gset("heartbeat", now_iso()); cleanup()
        try: await probe_down_models()
        except Exception as e: log.warning(f"probe: {e}")
        try: await _plan_notifications()
        except Exception as e: log_event("ERROR", f"plan notifications: {e}")
        if not gget("automation_enabled", True): return
        due = []
        for u in list_admins():
            uid = u["id"]
            if not admin_limits(uid)["active"]: continue
            rem = remaining(uid, "posts")
            for ch in list_channels(uid):
                s = get_settings(ch["id"])
                if not s["enabled"]: continue
                try: await flush_ready(bot, uid, ch["id"])
                except Exception as e: log_event("ERROR", f"flush {ch['title']}: {e}", uid)
                if rem is not None and rem <= 0: continue
                if in_quiet(s) and s["mode"] == "auto": continue
                lr = parse_dt(s["last_run"])
                if not lr or (now_utc() - lr) >= timedelta(minutes=int(s["interval_minutes"])): due.append((lr.isoformat() if lr else "", uid, ch, s))
        gset("load_due", len(due))
        if not due: return
        if not any_model_available(): log_event("WARN", f"{len(due)} کانال در انتظار؛ هیچ مدل AI در دسترس نیست"); return
        due.sort(key=lambda x: x[0]); batch = due[:MAX_CYCLES_PER_TICK]
        gset("last_cycle_start", now_iso()); await asyncio.gather(*[_scheduled(bot, uid, ch, s) for _, uid, ch, s in batch]); gset("last_cycle_end", now_iso())

def report_text(uid=None, cid=None, lang="fa"):
    fa = lang != "en"; hb = gget("heartbeat"); hb_age = (now_utc() - parse_dt(hb)).total_seconds() if hb else 1e9; hb_icon = "🟢" if hb_age < TICK_SECONDS * 4 else "🔴"
    if cid is None:
        roles = {r["role"]: r["c"] for r in count_users()}; models = list_models(); ok = sum(1 for m in models if m["active"] and m["status"] == "ok"); down = sum(1 for m in models if m["active"] and m["status"] == "down")
        size = os.path.getsize(DB_FILE) / 1024 / 1024 if os.path.exists(DB_FILE) else 0; auto = gget("automation_enabled", True)
        n = lambda st=None, h=24: count_articles(None, h, st)
        if fa: return (f"📊 <b>گزارش سیستم</b>\n\n{'🟢' if auto else '🔴'} اتوماسیون · 💓 {ago_text(hb, lang)} {hb_icon} · ⚖️ صف زمان‌بند: {gget('load_due', 0)}\n👥 کاربران {sum(roles.values())} · مدیران {roles.get('admin', 0)} · کلان {roles.get('super', 0)}\n🧾 پلن‌ها {len(list_plans())} · 🛎 پرداخت معلق {len(pay_pending())} · 🎟 کد تخفیف {len(disc_list())}\n"
                       f"🤖 مدل‌ها: ✅{ok} 🔴{down} / {len(models)}\n📢 کانال‌ها {q('SELECT COUNT(*) c FROM channels', one=True)['c']} · 🌐 منابع فعال {q('SELECT COUNT(*) c FROM sources WHERE active=1', one=True)['c']}\n📰 ۲۴h: کشف {n()} · ✅ {n('published')} · ♻️ {n('rejected')} · ❌ {n('failed')} · 📝 صف {n('ready', 72)}\n"
                       f"🔗 دیپ‌لینک {q('SELECT COUNT(*) c FROM deeplinks', one=True)['c']} ({'CF KV' if CF_ENABLED else 'محلی'}) · 💾 {size:.2f} MB\n🕐 آخرین چرخه: {fmt_date(gget('last_cycle_start'), DEFAULT_UTC_OFFSET, True)} → {fmt_date(gget('last_cycle_end'), DEFAULT_UTC_OFFSET, True)}")
        return (f"📊 <b>System report</b>\n\n{'🟢' if auto else '🔴'} automation · 💓 {ago_text(hb, lang)} {hb_icon} · ⚖️ scheduler queue: {gget('load_due', 0)}\n👥 users {sum(roles.values())} · admins {roles.get('admin', 0)} · super {roles.get('super', 0)}\n🧾 plans {len(list_plans())} · 🛎 pending payments {len(pay_pending())} · 🎟 discount codes {len(disc_list())}\n"
                f"🤖 models: ✅{ok} 🔴{down} / {len(models)}\n📢 channels {q('SELECT COUNT(*) c FROM channels', one=True)['c']} · 🌐 active sources {q('SELECT COUNT(*) c FROM sources WHERE active=1', one=True)['c']}\n📰 24h: found {n()} · ✅ {n('published')} · ♻️ {n('rejected')} · ❌ {n('failed')} · 📝 queue {n('ready', 72)}\n"
                f"🔗 deep links {q('SELECT COUNT(*) c FROM deeplinks', one=True)['c']} ({'CF KV' if CF_ENABLED else 'local'}) · 💾 {size:.2f} MB\n🕐 last cycle: {fmt_date(gget('last_cycle_start'), DEFAULT_UTC_OFFSET, True)} → {fmt_date(gget('last_cycle_end'), DEFAULT_UTC_OFFSET, True)}")
    s = get_settings(cid); ch = get_channel(cid); lim = admin_limits(uid); use = usage_today(uid); off = s["utc_offset"]; cap = lambda v: "∞" if v is None else v
    quiet = f"{s['quiet_start']:02d}→{s['quiet_end']:02d}" if s["quiet_start"] is not None and s["quiet_end"] is not None else ("—")
    pname = "∞" if is_super(uid) else (plan_txt(lim["plan"], "name", lang) or ("بدون پلن" if fa else "no plan")); until = f" · {fmt_date(lim['expires'], off)}" if lim["expires"] else ""
    c = lambda st=None: count_articles(cid=cid, hours=24, status=st)
    if fa: return (f"📊 <b>گزارش</b> · 📢 {html.escape(ch['title'])}\n\n{'🟢' if s['enabled'] else '🔴'} اتوماسیون · {'⚡ خودکار' if s['mode'] == 'auto' else '📝 بازبینی'} · 🧾 {html.escape(pname)}{until}\n🌐 منابع {len(list_sources(cid, True))} · 📰 کشف ۲۴h {c()} · 📥 صف {ready_count(cid)}\n📢 پست امروز {use['posts']}/{cap(lim['daily_posts'])} · 🧪 تست {use['tests']}/{cap(lim['daily_tests'])}\n♻️ رد ۲۴h {c('rejected')} · ❌ ناموفق {c('failed')}\n"
                   f"⭐ حداقل {s['min_score']} · 🕰 {s['lookback_hours']}h · ⏱ هر {s['interval_minutes']}′ · 🌙 {quiet} · 🌍 {off_label(off)}\n💓 {ago_text(hb, lang)} {hb_icon} · 🕐 چرخه: {fmt_date(s['last_run'], off, True)} → {fmt_date(s['last_end'], off, True)}")
    return (f"📊 <b>Report</b> · 📢 {html.escape(ch['title'])}\n\n{'🟢' if s['enabled'] else '🔴'} automation · {'⚡ auto' if s['mode'] == 'auto' else '📝 review'} · 🧾 {html.escape(pname)}{until}\n🌐 sources {len(list_sources(cid, True))} · 📰 found 24h {c()} · 📥 queue {ready_count(cid)}\n📢 posts today {use['posts']}/{cap(lim['daily_posts'])} · 🧪 tests {use['tests']}/{cap(lim['daily_tests'])}\n♻️ rejected 24h {c('rejected')} · ❌ failed {c('failed')}\n"
            f"⭐ min {s['min_score']} · 🕰 {s['lookback_hours']}h · ⏱ every {s['interval_minutes']}′ · 🌙 {quiet} · 🌍 {off_label(off)}\n💓 {ago_text(hb, lang)} {hb_icon} · 🕐 cycle: {fmt_date(s['last_run'], off, True)} → {fmt_date(s['last_end'], off, True)}")

# ============================================================
# رابط کاربری تلگرام (UI & Views)
TXT = {
    "back": ("🔙 بازگشت", "🔙 Back"), "home": ("🏠 خانه", "🏠 Home"), "cancel": ("❌ انصراف", "❌ Cancel"), "cancelled": ("↩️ لغو شد", "↩️ Cancelled"),
    "saved": ("✅ ذخیره شد", "✅ Saved"), "deleted": ("🗑 حذف شد", "🗑 Deleted"), "on": ("روشن", "on"), "off": ("خاموش", "off"), "yes": ("✅ بله", "✅ Yes"), "no": ("❌ خیر", "❌ No"),
    "send_value": ("مقدار را بفرستید", "Send the value"), "step": ("🧩 <b>{i}/{n}</b>", "🧩 <b>{i}/{n}</b>"), "need_int": ("⚠️ عدد بفرستید", "⚠️ Send a number"), "empty": ("⚠️ خالی است", "⚠️ Empty"),
    "range": ("⚠️ بازه‌ی مجاز: {lo}–{hi}", "⚠️ Allowed range: {lo}–{hi}"), "notfound": ("❌ یافت نشد", "❌ Not found"), "error": ("❌ {e}", "❌ {e}"),
    "choose_lang": ("🌐 <b>زبان / Language</b>", "🌐 <b>زبان / Language</b>"), "lang_set": ("✅ فارسی", "✅ English"), "banned": ("⛔ دسترسی مسدود است", "⛔ Access blocked"),
    "lang_set_n": (" · {n} کانال هم‌زبان شد", " · {n} channel(s) relocalized"),
    "busy_click": ("⏳ کمی آهسته‌تر", "⏳ Slow down a bit"),
    "plans_btn": ("🧾 شروع", "🧾 Start"), "plans_title": ("🧾 <b>پلن‌ها</b>", "🧾 <b>Plans</b>"), "plans_current": ("🧾 فعلی: <b>{name}</b>{until}", "🧾 Current: <b>{name}</b>{until}"), "until": (" · تا {d}", " · until {d}"),
    "plans_next": ("⏭ بعدی: <b>{name}</b>", "⏭ Next: <b>{name}</b>"), "plans_pick": ("برای دیدن جزئیات و قیمت، پلن را انتخاب کنید:", "Pick a plan to see details and price:"),
    "plan_details": ("⏳ {days} روز · 📢 {posts} پست/روز · 🧪 {tests} تست/روز\n🌐 {src} منبع · 📣 {ch} کانال\n💰 <b>{price}</b>", "⏳ {days} days · 📢 {posts} posts/day · 🧪 {tests} tests/day\n🌐 {src} sources · 📣 {ch} channels\n💰 <b>{price}</b>"),
    "plan_disc_line": ("🎟 <s>{old}</s> → <b>{new}</b> ({code} −{p}%)", "🎟 <s>{old}</s> → <b>{new}</b> ({code} −{p}%)"),
    "plan_chain_note": ("ℹ️ با پلن فعال متفاوت، این پلن پس از پایان آن شروع می‌شود؛ تمدید همان پلن فقط روز اضافه می‌کند.", "ℹ️ With a different active plan, this one starts after it ends; renewing the same plan only adds days."),
    "free_word": ("رایگان", "Free"), "plan_free_btn": ("🎁 فعال‌سازی رایگان", "🎁 Activate free"), "plan_free_used": ("✔️ استفاده شده", "✔️ Used"),
    "plan_req_btn": ("💳 خرید", "💳 Buy"), "plan_renew_btn": ("🔄 تمدید", "🔄 Renew"), "plan_pending_btn": ("⏳ در انتظار بررسی", "⏳ Pending"), "disc_btn": ("🎟 کد تخفیف", "🎟 Discount code"), "disc_remove": ("🎟 حذف کد", "🎟 Remove code"),
    "disc_prompt": ("کد تخفیف را بفرستید:", "Send the discount code:"), "disc_ok": ("🎟 کد اعمال شد: −{p}%", "🎟 Code applied: −{p}%"), "disc_bad": ("❌ کد نامعتبر", "❌ Invalid code"), "disc_expired": ("❌ کد منقضی شده", "❌ Code expired"), "disc_exhausted": ("❌ ظرفیت کد تمام شده", "❌ Code fully used"),
    "plan_notfound": ("❌ پلن یافت نشد", "❌ Plan not found"), "free_once": ("⚠️ پلن رایگان فقط یک بار", "⚠️ Free plan only once"), "free_done": ("✅ «{name}» فعال شد؛ حالا کانال و منبع اضافه کنید.", "✅ “{name}” activated; now add a channel and sources."),
    "req_pending": ("⏳ درخواست قبلی هنوز در بررسی است", "⏳ Previous request still under review"), "receipt_hint": ("\n\n📎 <i>تصویر رسید را همین‌جا بفرستید.</i>", "\n\n📎 <i>Send the receipt image here.</i>"),
    "receipt_ok": ("✅ <b>رسید دریافت شد.</b>\nحداکثر تا ۱ ساعت بررسی و نتیجه همین‌جا اعلام می‌شود.", "✅ <b>Receipt received.</b>\nReviewed within 1 hour; you'll be notified here."), "wait_btn": ("🚪 خروج", "🚪 Exit"), "receipt_empty": ("⚠️ تصویر رسید یا توضیح پرداخت را بفرستید", "⚠️ Send the receipt image or a payment note"),
    "pay_approved": ("🎉 پرداخت تأیید شد؛ پلن <b>{name}</b> {when}.\n/create", "🎉 Payment approved; plan <b>{name}</b> {when}.\n/create"), "pay_when_now": ("تا {d} فعال است", "is active until {d}"), "pay_when_queued": ("پس از پلن فعلی ({d}) شروع می‌شود", "starts after the current plan ({d})"),
    "pay_rejected": ("❌ پرداخت تأیید نشد. پیگیری: /man", "❌ Payment not approved. Follow up: /man"),
    "no_admin": ("⛔ ابتدا یک پلن فعال کنید", "⛔ Activate a plan first"), "panel": ("🛠 <b>پنل مدیریت</b>", "🛠 <b>Admin panel</b>"), "no_plan": ("بدون پلن", "no plan"),
    "today_line": ("📢 {p}/{pc} پست · 🧪 {t}/{tc} تست · 📣 {c}/{cc} کانال · 🌐 {s}/{sc} منبع", "📢 {p}/{pc} posts · 🧪 {t}/{tc} tests · 📣 {c}/{cc} channels · 🌐 {s}/{sc} sources"),
    "plan_inactive": ("⚠️ <b>پلن فعال نیست</b> → تمدید/ارتقا", "⚠️ <b>Plan inactive</b> → renew/upgrade"), "pick_channel": ("کانال را انتخاب کنید (هر کانال تنظیمات مستقل دارد):", "Pick a channel (each has its own settings):"),
    "no_channels": ("هنوز کانالی ندارید. ربات را در کانال ادمین کنید و «افزودن کانال» را بزنید.", "No channel yet. Make the bot admin of your channel, then tap “Add channel”."),
    "ch_add": ("➕ افزودن کانال", "➕ Add channel"), "my_plan": ("🧾 پلن من", "🧾 My plan"), "logs": ("📜 لاگ", "📜 Logs"), "super_panel": ("👑 مدیر کلان", "👑 Super admin"),
    "ch_add_prompt": ("۱) ربات را در کانال <b>ادمین</b> کنید (مجوز ارسال پیام)\n۲) یک پیام از کانال <b>فوروارد</b> کنید یا آیدی بفرستید (<code>@mychannel</code> / <code>-100…</code>)\n\n🔐 فقط ادمین همان کانال می‌تواند ثبت کند.", "1) Make the bot channel <b>admin</b> (post permission)\n2) <b>Forward</b> a channel message or send its ID (<code>@mychannel</code> / <code>-100…</code>)\n\n🔐 Only that channel's admin can register it."),
    "ch_no_access": ("❌ دسترسی به کانال ممکن نیست: {e}", "❌ Can't access channel: {e}"), "ch_need_fwd": ("⚠️ پیام فورواردشده یا آیدی کانال بفرستید", "⚠️ Forward a channel message or send its ID"),
    "ch_bot_not_admin": ("❌ ربات ادمین این کانال نیست / مجوز ارسال ندارد", "❌ Bot is not admin of this channel / can't post"), "ch_user_not_admin": ("🔐 شما ادمین این کانال نیستید", "🔐 You are not an admin of this channel"),
    "ch_exists_mine": ("⚠️ این کانال قبلاً ثبت شده", "⚠️ Channel already registered"),
    "ch_locked": ("🔐 <b>این کانال در پنل کاربر دیگری است.</b>\nبرای انتقال، <b>کد قفل ۶ رقمی</b> را بفرستید (مالک فعلی در «کد قفل» می‌بیند). با انتقال، تنظیمات مالک قبلی جدا و به او اطلاع داده می‌شود.", "🔐 <b>This channel belongs to another user's panel.</b>\nTo transfer, send its <b>6-digit lock code</b> (owner sees it under “Lock code”). The previous owner's settings are detached and they get notified."),
    "ch_lock_bad": ("❌ کد اشتباه؛ به مالک اطلاع داده شد", "❌ Wrong code; owner notified"), "ch_lock_ok": ("✅ «{title}» به پنل شما منتقل شد", "✅ “{title}” transferred to your panel"),
    "ch_owner_alert": ("🚨 <b>هشدار امنیتی</b>\n{who} برای «{title}» کد قفل اشتباه وارد کرد.", "🚨 <b>Security alert</b>\n{who} entered a wrong lock code for “{title}”."),
    "ch_owner_moved": ("⚠️ «{title}» با کد معتبر به {who} منتقل شد. اگر شما نبودید: /man", "⚠️ “{title}” was transferred to {who} with a valid code. If this wasn't you: /man"),
    "ch_added": ("✅ «{title}» اضافه شد", "✅ “{title}” added"), "limit_channels": ("⚠️ سقف کانال پلن: {n}", "⚠️ Plan channel limit: {n}"), "limit_sources": ("⚠️ سقف منبع پلن: {n}", "⚠️ Plan source limit: {n}"),
    "limit_posts": ("⚠️ سهمیه‌ی پست امروز تمام شد ({n})", "⚠️ Today's post quota used ({n})"), "limit_tests": ("⚠️ سهمیه‌ی تست امروز تمام شد ({n})", "⚠️ Today's test quota used ({n})"),
    "ch_panel": ("📣 <b>{title}</b>", "📣 <b>{title}</b>"), "ch_status": ("{i} اتوماسیون {st} · {mode}", "{i} Automation {st} · {mode}"), "auto": ("⚡ خودکار", "⚡ auto"), "review": ("📝 بازبینی", "📝 review"),
    "ch_stats": ("🌐 {s} منبع · 📝 صف {q} · ✅ ۲۴h {p} · ♻️ رد {r} · 🕐 {a}", "🌐 {s} sources · 📝 queue {q} · ✅ 24h {p} · ♻️ rejected {r} · 🕐 {a}"),
    "report": ("📊 گزارش", "📊 Report"), "test": ("🧪 تست فوری", "🧪 Quick test"), "sources": ("🌐 منابع ({n})", "🌐 Sources ({n})"), "content": ("✍️ محتوا", "✍️ Content"), "sched": ("⏰ زمان‌بندی", "⏰ Schedule"),
    "queue": ("📝 صف انتشار ({n})", "📝 Publish queue ({n})"), "rejected": ("♻️ ردشده‌ها", "♻️ Rejected"), "automation": ("{i} اتوماسیون", "{i} Automation"), "lock": ("🔐 کد قفل", "🔐 Lock code"), "ch_del": ("🗑 حذف کانال", "🗑 Remove channel"),
    "refresh": ("🔄 بروزرسانی", "🔄 Refresh"), "ch_del_q": ("❓ «{title}» با منابع، تنظیمات و صف حذف شود؟", "❓ Remove “{title}” with its sources, settings and queue?"), "ch_deleted": ("🗑 کانال حذف شد", "🗑 Channel removed"),
    "tog_enabled": ("🟢 اتوماسیون روشن شد", "🟢 Automation on"), "tog_disabled": ("🔴 اتوماسیون خاموش شد", "🔴 Automation off"),
    "lock_text": ("🔐 <b>کد قفل «{title}»</b>\n\nاگر کسی بخواهد این کانال را در پنل خود ثبت کند باید این کد را بدهد؛ وگرنه رد می‌شود و به شما خبر می‌رسد.\n\n🔑 <code>{code}</code>\n\n⚠️ محرمانه نگه دارید؛ در صورت لو رفتن بازتولید کنید.", "🔐 <b>Lock code of “{title}”</b>\n\nAnyone trying to register this channel in their panel must enter this code; otherwise it's rejected and you're notified.\n\n🔑 <code>{code}</code>\n\n⚠️ Keep it secret; regenerate if leaked."),
    "lock_regen": ("🔁 بازتولید", "🔁 Regenerate"), "lock_regen_ok": ("✅ کد جدید صادر شد", "✅ New code issued"),
    "src_title": ("🌐 <b>منابع — {title}</b> · {n}/{cap}\n💡 بهترین نتیجه با سایت‌هایی است که <b>RSS</b> دارند؛ آدرس فید یا خود سایت را بدهید.\nستون اول = کانال · ستون دوم = ربات", "🌐 <b>Sources — {title}</b> · {n}/{cap}\n💡 Best results with sites that have <b>RSS</b>.\nFirst mark = channel · second = bot"),
    "src_line": ("\n{i}{b} {host} · 🆕 {n}{err}", "\n{i}{b} {host} · 🆕 {n}{err}"), "src_err": (" · ⚠️×{n}", " · ⚠️×{n}"), "src_add": ("➕ افزودن منبع", "➕ Add source"),
    "src_add_prompt": ("آدرس منبع را بفرستید:\n<code>https://example.com/feed</code>", "Send the source URL:\n<code>https://example.com/feed</code>"),
    "src_bad": ("⚠️ آدرس نامعتبر", "⚠️ Invalid URL"), "src_dup": ("⚠️ منبع تکراری", "⚠️ Duplicate source"), "src_checking": ("🔎 بررسی منبع…", "🔎 Checking source…"),
    "src_added": ("✅ منبع اضافه شد · {n} مقاله [{m}]", "✅ Source added · {n} articles [{m}]"),
    "src_403": ("🚫 این سایت به ربات‌ها اجازه‌ی خواندن نمی‌دهد (HTTP 403).", "🚫 This site blocks bots (HTTP 403)."),
    "src_dead": ("⚠️ تست بارگذاری موفق نبود؛ اگر فید RSS دارد، آدرس فید را مستقیم بدهید.", "⚠️ Load test failed; provide direct RSS URL."),
    "src_added_off": ("\n➕ منبع اضافه شد اما 🔴 خاموش است.", "\n➕ The source was added but is 🔴 off."), "src_now_off": ("\n🔴 منبع خاموش شد.", "\n🔴 The source was turned off."),
    "src_view": ("🌐 <b>{host}</b>\n<code>{url}</code>\n{feed}\n{st} · آخرین بررسی {last} · 🆕 {n} · ⚠️×{f}{err}", "🌐 <b>{host}</b>\n<code>{url}</code>\n{feed}\n{st} · last check {last} · 🆕 {n} · ⚠️×{f}{err}"),
    "src_feed": ("📡 <code>{u}</code>", "📡 <code>{u}</code>"), "active": ("🟢 فعال", "🟢 active"), "inactive": ("🔴 غیرفعال", "🔴 inactive"), "toggle": ("⏯ روشن/خاموش", "⏯ On/off"), "delete": ("🗑 حذف", "🗑 Delete"),
    "src_st": ("{c} کانال · {b} ربات", "{c} channel · {b} bot"), "tog_ch": ("⏯ منبع کانال", "⏯ Channel source"), "tog_bot": ("🤖 منبع ربات", "🤖 Bot source"),
    "src_ch_on": ("🟢 منبع برای کانال روشن شد", "🟢 Source on for channel"), "src_ch_off": ("🔴 منبع برای کانال خاموش شد", "🔴 Source off for channel"),
    "src_bot_on": ("🟢 منبع برای محتوای ربات روشن شد", "🟢 Source on for bot content"), "src_bot_off": ("🔴 منبع برای محتوای ربات خاموش شد", "🔴 Source off for bot content"),
    "src_api": ("🔌 API", "🔌 API"), "src_api_none": ("🔌 API: —", "🔌 API: —"), "src_api_on": ("🔌 API: <code>{u}</code>", "🔌 API: <code>{u}</code>"),
    "src_api_url": ("آدرس API منبع را بفرستید (خروجی JSON):", "Send source API URL (JSON):"),
    "src_api_key": ("کلید API را بفرستید (اگر لازم نیست بنویسید <code>-</code>):", "Send API key (or <code>-</code>):"),
    "src_api_ok": ("✅ API ثبت شد · {n} آیتم خوانده شد", "✅ API saved · {n} items read"), "src_api_bad": ("⚠️ پاسخ API قابل استفاده نبود؛ ثبت شد اما منبع 🔴 خاموش است.", "⚠️ API response wasn't usable."),
    "src_api_del": ("🗑 API حذف شد", "🗑 API removed"),
    "src_on": ("🟢 منبع روشن شد", "🟢 Source on"), "src_off": ("🔴 منبع خاموش شد", "🔴 Source off"), "src_deleted": ("🗑 منبع حذف شد", "🗑 Source deleted"), "src_recheck": ("🔎 بررسی دوباره", "🔎 Re-check"),
    "content_title": ("✍️ <b>محتوا — {title}</b>\n🎯 {topic} · 🗣 {lang}\n📝 <i>{prompt}</i>\n✒️ {sig}", "✍️ <b>Content — {title}</b>\n🎯 {topic} · 🗣 {lang}\n📝 <i>{prompt}</i>\n✒️ {sig}"),
    "general": ("عمومی", "general"), "b_topic": ("🎯 موضوع", "🎯 Topic"), "b_lang": ("🗣 زبان خروجی", "🗣 Output language"), "b_prompt": ("📝 پرامپت", "📝 Prompt"), "b_sig": ("✒️ امضا", "✒️ Signature"),
    "b_cats": ("🗂 دسته‌ها ({n})", "🗂 Categories ({n})"), "b_crits": ("📏 معیارها ({n})", "📏 Criteria ({n})"), "b_min": ("⭐ حداقل امتیاز {n}", "⭐ Min score {n}"), "b_words": ("🔢 کلمات {n}", "🔢 Words {n}"), "b_limit": ("📏 سقف کاراکتر {n}", "📏 Char limit {n}"),
    "b_hashtags": ("#️⃣ هشتگ {i}", "#️⃣ Hashtags {i}"), "b_link": ("🔗 منبع در ربات {i}", "🔗 Source in bot {i}"), "b_media": ("🖼 رسانه {i}", "🖼 Media {i}"), "b_strict": ("🛡 فیلتر سخت {i}", "🛡 Strict filter {i}"), "b_premium": ("💎 فرمت پریمیوم {i}", "💎 Premium format {i}"),
    "tog_hashtags": ("#️⃣ هشتگ", "#️⃣ Hashtags"), "tog_include_link": ("🔗 منبع در ربات", "🔗 Source in bot"), "tog_include_media": ("🖼 رسانه", "🖼 Media"), "tog_strict_ads": ("🛡 فیلتر سخت تبلیغ", "🛡 Strict ad filter"), "tog_premium_format": ("💎 فرمت پریمیوم", "💎 Premium format"), "tog_allow_undated": ("📅 بدون تاریخ", "📅 Undated"),
    "prem_need_prem": ("💎 این قالب فقط برای مدیرانِ دارای تلگرام پریمیوم فعال می‌شود.", "💎 Only admins with Telegram Premium can enable this."),
    "prem_on_ok": ("💎 فعال شد. قالب پیشرفته‌ی پریمیوم به پست‌ها اعمال می‌شود.", "💎 Enabled. Premium advanced formatting active."),
    "togd_hashtags": ("هشتگ‌های مرتبط در انتهای پست اضافه می‌شوند", "Related hashtags added"), "togd_include_link": ("منبع خبر فقط در «ادامه در ربات» نمایش داده می‌شود", "Source shown in bot"), "togd_include_media": ("تصویر یا ویدیو همراه پست ارسال می‌شود", "Media sent with post"), "togd_strict_ads": ("فیلتر سخت‌گیرانه‌تر، تبلیغ‌ها را زودتر رد می‌کند", "Stricter ad filter"), "togd_premium_format": ("قالب پیشرفته‌ی پریمیوم در پست‌ها استفاده می‌شود", "Premium formatting in posts"), "togd_allow_undated": ("مقالاتِ بدون تاریخ هم منتشر می‌شوند", "Undated articles published"),
    "cats_title": ("🗂 <b>دسته‌ها</b>\nAI برای هر مقاله یکی را انتخاب و با سبک آن می‌نویسد.", "🗂 <b>Categories</b>"), "cat_add": ("➕ دسته", "➕ Category"),
    "cat_view": ("{e} <b>{name}</b>\n📐 {style}", "{e} <b>{name}</b>\n📐 {style}"), "cat_edit": ("✏️ سبک", "✏️ Style"), "cat_style_prompt": ("سبک نگارش جدید این دسته:", "New writing style:"),
    "cat_added": ("✅ دسته اضافه شد", "✅ Category added"), "cat_updated": ("✅ سبک بروزرسانی شد", "✅ Style updated"), "cat_min": ("⚠️ حداقل یک دسته لازم است", "⚠️ At least one category required"),
    "crits_title": ("📏 <b>معیارها</b>\nامتیاز ۰–۱۰۰ · زیر {m} رد می‌شود.", "📏 <b>Criteria</b>"), "crit_add": ("➕ معیار", "➕ Criterion"),
    "crit_line": ("\n• {name} — {w} ({p}%)", "\n• {name} — {w} ({p}%)"), "crit_btn": ("{name} · {w}", "{name} · {w}"), "crit_view": ("📏 <b>{name}</b> · وزن {w}", "📏 <b>{name}</b> · weight {w}"), "crit_w": ("✏️ وزن", "✏️ Weight"),
    "crit_w_prompt": ("وزن جدید (۱–۱۰۰):", "New weight (1–100):"), "crit_added": ("✅ معیار اضافه شد", "✅ Criterion added"), "crit_updated": ("✅ وزن بروزرسانی شد", "✅ Weight updated"), "crit_min": ("⚠️ حداقل یک معیار لازم است", "⚠️ At least one criterion required"),
    "sched_title": ("⏰ <b>زمان‌بندی — {title}</b>\n⏱ هر {iv}′ · 📦 {ppc} پست/چرخه · 🕰 {lb}h اخیر · 📅 بدون تاریخ {ud}\n🌙 {quiet} · 🌍 {city} {tz} (⌚ {loc} · UTC {utc})\n🔁 {mode}", "⏰ <b>Schedule — {title}</b>"),
    "mode_auto": ("⚡ خودکار — انتشار مستقیم", "⚡ auto — publish directly"), "mode_review": ("📝 بازبینی — تأیید دستی در صف", "📝 review — manual approval in queue"), "none": ("—", "—"),
    "b_interval": ("⏱ هر {n}′", "⏱ Every {n}′"), "b_ppc": ("📦 {n} پست/چرخه", "📦 {n}/cycle"), "b_lookback": ("🕰 {n}h", "🕰 {n}h"), "b_undated": ("📅 بدون تاریخ {i}", "📅 Undated {i}"),
    "b_quiet": ("🌙 خاموشی", "🌙 Quiet hours"), "b_tz": ("🌍 منطقه زمانی", "🌍 Time zone"), "b_mode": ("🔁 {m}", "🔁 {m}"),
    "mode_set_auto": ("⚡ خودکار: انتشار مستقیم", "⚡ Auto: publish directly"), "mode_set_review": ("📝 بازبینی: منتظر تأیید در صف", "📝 Review: waits for approval"),
    "quiet_pick_start": ("🌙 <b>خاموشی</b> · ساعت <b>شروع</b>:", "🌙 <b>Quiet hours</b> · start hour:"), "quiet_pick_end": ("🌙 شروع {h}:00 · ساعت <b>پایان</b>:", "🌙 Start {h}:00 · end hour:"),
    "quiet_off": ("🚫 بدون خاموشی", "🚫 No quiet hours"), "quiet_set": ("🌙 خاموشی {a}:00 → {b}:00", "🌙 Quiet {a}:00 → {b}:00"), "quiet_cleared": ("🌙 خاموشی حذف شد", "🌙 Quiet hours cleared"),
    "tz_pick": ("🌍 <b>منطقه زمانی</b> · UTC الان <b>{utc}</b>\nنزدیک‌ترین شهر را انتخاب کنید:", "🌍 <b>Time zone</b>"), "tz_set": ("🌍 {city} {tz} · ⌚ {loc}", "🌍 {city} {tz} · ⌚ {loc}"),
    "queue_title": ("📝 <b>صف انتشار — {title}</b> · {n} آماده", "📝 <b>Publish queue — {title}</b> · {n} ready"), "rej_title": ("♻️ <b>ردشده‌های ۲۴h — {title}</b>", "♻️ <b>Rejected 24h — {title}</b>"),
    "pub_first": ("🚀 انتشار اولین", "🚀 Publish first"), "art_title": ("📝 <b>{title}</b>\n⭐ {score} · 🗂 {cat}\n📌 {st}{reason} · 🌐 {host}\n━━━━━━━━━━━━\n{body}", "📝 <b>{title}</b>"),
    "art_nobody": ("<i>(محتوایی تولید نشده)</i>", "<i>(no content generated)</i>"), "art_pub": ("🚀 انتشار", "🚀 Publish"), "art_edit": ("✏️ ویرایش", "✏️ Edit"), "art_full": ("📖 نسخه کامل", "📖 Full version"), "art_view": ("👁 مشاهده", "👁 View"),
    "art_del_arch": ("🗑 حذف از آرشیو", "🗑 Remove from archive"), "art_to_ready": ("♻️ به صف انتشار", "♻️ To publish queue"), "art_edit_prompt": ("متن جدید پست:", "New post text:"),
    "art_updated": ("✅ متن بروزرسانی شد", "✅ Text updated"), "art_moved": ("♻️ به صف منتقل شد", "♻️ Moved to queue"), "publishing": ("⏳ انتشار…", "⏳ Publishing…"), "published_ok": ("✅ منتشر شد", "✅ Published"), "pub_failed": ("❌ انتشار: {e}", "❌ Publish: {e}"), "full_head": ("📖 <b>نسخه‌ی کامل</b>\n\n", "📖 <b>Full version</b>\n\n"),
    "myplan": ("🧾 <b>پلن من: {name}</b>\n{st}{exp}{nxt}\n📢 {p}/{pc} پست · 🧪 {t}/{tc} تست\n🌐 {s}/{sc} منبع · 📣 {c}/{cc} کانال", "🧾 <b>My plan: {name}</b>"),
    "st_active": ("🟢 فعال", "🟢 active"), "st_expired": ("🔴 غیرفعال", "🔴 inactive"), "exp_at": (" · تا {d}", " · until {d}"), "upgrade_btn": ("⬆️ ارتقا / تمدید", "⬆️ Upgrade / renew"),
    "logs_title": ("📜 <b>لاگ</b>{lvl}\n\n", "📜 <b>Logs</b>{lvl}\n\n"), "logs_empty": ("— خالی —", "— empty —"), "all": ("همه", "All"), "errors": ("خطاها", "Errors"), "warns": ("هشدارها", "Warnings"),
    "logs_note": ("\n\n<i>۱۰ مورد آخر</i>", "\n\n<i>last 10 entries</i>"),
    "rj_extract": ("متن قابل استخراج نبود", "no extractable text"), "rj_ad": ("فیلتر تبلیغ", "ad filter"), "rj_ai_ad": ("تبلیغ (تشخیص AI)", "ad (AI)"), "rj_score": ("امتیاز کمتر از حداقل", "below minimum score"),
    "rj_ai": ("سرویس هوش مصنوعی پاسخ نداد", "AI service did not respond"), "rj_send": ("ارسال به کانال ناموفق", "sending to channel failed"), "rj_dup": ("تکراری", "duplicate"),
    "rj_admin": ("ربات ادمین کانال نیست", "bot is not channel admin"), "rj_old": ("قدیمی‌تر از بازه", "older than window"), "rj_undated": ("بدون تاریخ", "undated"), "rj_other": ("نامشخص", "unspecified"),
    "test_head": ("🧪 <b>تست — {title}</b>", "🧪 <b>Test — {title}</b>"), "preparing": ("آماده‌سازی…", "Preparing…"), "test_wait": ("⏳ تست بعدی تا {n} ثانیه دیگر", "⏳ Next test in {n}s"), "test_busy": ("⏳ چرخه‌ای روی این کانال در حال اجراست", "⏳ A cycle is already running"),
    "test_ok": ("✅ <b>منتشر شد</b>", "✅ <b>Published</b>"), "test_queued": ("📝 در <b>صف انتشار</b> منتظر تأیید", "📝 Waiting in <b>publish queue</b>"), "test_fail": ("⚠️ <b>چیزی منتشر نشد</b>", "⚠️ <b>Nothing published</b>"),
    "test_log": ("📋 {d}", "📋 {d}"), "back_panel": ("🔙 پنل کانال", "🔙 Channel panel"),
    "test_retry_note": ("ℹ️ سهمیه کسر نشد؛ می‌توانید دوباره تست کنید.", "ℹ️ No quota deducted; retry right away."),
    "test_src": ("🌐 تولید از منبع: <b>{name}</b>", "🌐 Generated from source: <b>{name}</b>"),
    "lock_reset_q": ("⚠️ با بازتولید کد قفل، کانال ریست امنیتی می‌شود. ادامه می‌دهید؟", "⚠️ Lock code reset. Continue?"),
    "lock_reset_ok": ("✅ کد جدید صادر شد · کانال ریست شد", "✅ New code issued · channel reset"),
}

def tr(lang, key, / , **kw):
    s = TXT[key][1 if lang == "en" else 0]
    try: return s.format(**kw) if kw else s
    except Exception: return s

STATUS = {"discovered": ("🔎 کشف‌شده", "🔎 discovered"), "skipped": ("⏭ خارج از بازه", "⏭ out of window"), "rejected": ("♻️ ردشده", "♻️ rejected"), "failed": ("❌ ناموفق", "❌ failed"), "ready": ("📝 آماده", "📝 ready"), "published": ("✅ منتشرشده", "✅ published")}

def reason_text(reason, lang):
    r = (reason or "").strip().lower()
    if not r: return ""
    if r.startswith("ai:"): return ai_err_text(r.split(":", 1)[1].strip(), lang)
    for pre, key in (("extract", "rj_extract"), ("ad_filter", "rj_ad"), ("ai_ad", "rj_ai_ad"), ("score", "rj_score"), ("send", "rj_send"), ("duplicate", "rj_dup"), ("bot_not_admin", "rj_admin"), ("old", "rj_old"), ("undated", "rj_undated")):
        if r.startswith(pre): return tr(lang, key)
    if r.startswith("ai_"): return ai_err_text(r, lang)
    return tr(lang, "rj_other")

INT_FIELDS = {"max_words": (30, 600), "min_score": (0, 100), "post_limit": (300, 4000), "interval_minutes": (MIN_INTERVAL, 1440), "posts_per_cycle": (1, MAX_PPC), "lookback_hours": (1, MAX_LOOKBACK)}
FIELD_LABEL = {"prompt": ("پرامپت نگارش", "Writing prompt"), "topic": ("موضوع کانال", "Channel topic"), "language": ("زبان خروجی", "Output language"), "signature": ("امضای پایان پست", "Post signature"),
               "max_words": ("حداکثر کلمات پست", "Max post words"), "min_score": ("حداقل امتیاز", "Min score"), "post_limit": ("سقف کاراکتر پست", "Post char limit"),
               "interval_minutes": ("فاصله‌ی چرخه (دقیقه)", "Cycle interval (min)"), "posts_per_cycle": ("پست در هر چرخه", "Posts per cycle"), "lookback_hours": ("مقالات چند ساعت اخیر", "Lookback hours")}
SCHED_FIELDS = ("interval_minutes", "posts_per_cycle", "lookback_hours")

TZ_NAMES = {"tehran": ("🇮🇷 تهران", "🇮🇷 Tehran"), "istanbul": ("🇹🇷 استانبول", "🇹🇷 Istanbul"), "dubai": ("🇦🇪 دبی", "🇦🇪 Dubai"), "kabul": ("🇦🇫 کابل", "🇦🇫 Kabul"), "karachi": ("🇵🇰 کراچی", "🇵🇰 Karachi"), "delhi": ("🇮🇳 دهلی", "🇮🇳 Delhi"),
            "moscow": ("🇷🇺 مسکو", "🇷🇺 Moscow"), "berlin": ("🇩🇪 برلین", "🇩🇪 Berlin"), "london": ("🇬🇧 لندن", "🇬🇧 London"), "beijing": ("🇨🇳 پکن", "🇨🇳 Beijing"), "tokyo": ("🇯🇵 توکیو", "🇯🇵 Tokyo"), "sydney": ("🇦🇺 سیدنی", "🇦🇺 Sydney"),
            "newyork": ("🇺🇸 نیویورک", "🇺🇸 New York"), "losangeles": ("🇺🇸 لس‌آنجلس", "🇺🇸 Los Angeles"), "saopaulo": ("🇧🇷 سائوپائولو", "🇧🇷 São Paulo"), "utc": ("🌐 گرینویچ", "🌐 UTC")}
def tz_city(off, lang):
    z = next((k for k, o in TZ_ZONES if abs(o - float(off)) < 0.01), None); return TZ_NAMES[z][1 if lang == "en" else 0] if z else ""

WIZ = {
    "cat_add": [("name", ("نام دسته", "Category name"), "str"), ("emoji", ("یک ایموجی", "One emoji"), "str"), ("style", ("سبک نگارش", "Writing style"), "str")],
    "crit_add": [("name", ("نام معیار", "Criterion name"), "str"), ("weight", ("وزن (۱–۱۰۰)", "Weight (1–100)"), "int")],
    "plan_new": [("name", ("نام (فارسی)", "Name (Persian)"), "str"), ("name_en", ("نام (انگلیسی)", "Name (English)"), "str"), ("days", ("مدت (روز)", "Days"), "int"), ("daily_posts", ("پست روزانه", "Posts/day"), "int"), ("max_sources", ("حداکثر منبع", "Max sources"), "int"), ("max_channels", ("حداکثر کانال", "Max channels"), "int"), ("daily_tests", ("تست روزانه", "Tests/day"), "int"),
                 ("price", ("قیمت (فارسی)", "Price (Persian)"), "str"), ("price_en", ("قیمت (انگلیسی)", "Price (English)"), "str"), ("description", ("توضیح کوتاه (فارسی)", "Short description (Persian)"), "str"), ("description_en", ("توضیح کوتاه (انگلیسی)", "Short description (English)"), "str")],
    "model_add": [("base_url", ("Base URL سرویس:", "Service Base URL:"), "str"), ("api_key", ("کلید API", "API key"), "str"), ("model", ("نام مدل", "Model name"), "str")],
    "disc_add": [("code", ("کد تخفیف", "Discount code"), "str"), ("percent", ("درصد تخفیف (۱–۱۰۰)", "Discount percent"), "int"), ("expires", ("انقضا: روز یا تاریخ YYYY-MM-DD", "Expiry: days or YYYY-MM-DD"), "str"), ("max_uses", ("سقف استفاده (0 = نامحدود)", "Max uses"), "int")],
}

def B(t, d): return InlineKeyboardButton(t, callback_data=d[:64])
def U(t, url): return InlineKeyboardButton(t, url=url)
def esc(x): return html.escape(str(x if x is not None else ""))
def onoff(v): return "✅" if v else "❌"
def bar(p): f = int(p // 10); return "█" * f + "░" * (10 - f)
def to_int(s): return int(float(str(s).strip().translate(_FA_DIGITS)))
def pairs(btns, n=2): return [btns[i:i + n] for i in range(0, len(btns), n)]
def uname(u): return ("@" + u["username"]) if u and u["username"] else (u["name"] if u and u["name"] else str(u["id"] if u else "?"))
def can_admin(uid): return role_of(uid) in ("admin", "super")
def L(update): return user_lang(update.effective_user.id) or "fa"
def cap(v): return "∞" if v is None else v
def kbm(kb): return InlineKeyboardMarkup([[B(t, d) if not str(d).startswith("http") else U(t, d) for t, d in row] for row in kb]) if kb else None

async def popup(update, context, text, alert=False):
    qy = update.callback_query
    if qy:
        try: await qy.answer(text[:200], show_alert=alert); context.user_data["_answered"] = True; return
        except Exception: pass
    context.user_data["notice"] = text

async def render(update, context, text, kb=None, force_new=False):
    notice = context.user_data.pop("notice", None)
    if notice: text = f"{notice}\n\n{text}"
    text = text[:4000]; markup = InlineKeyboardMarkup(kb) if kb else None; qy = update.callback_query; chat_id = update.effective_chat.id
    if qy and qy.message and not force_new:
        try: await qy.edit_message_text(text, reply_markup=markup, parse_mode=HTML, disable_web_page_preview=True); context.user_data["panel"] = qy.message.message_id; return
        except BadRequest as e:
            if "not modified" in str(e).lower(): return
    mid = context.user_data.get("panel")
    if mid and not force_new:
        try: await context.bot.edit_message_text(text, chat_id=chat_id, message_id=mid, reply_markup=markup, parse_mode=HTML, disable_web_page_preview=True); return
        except BadRequest as e:
            if "not modified" in str(e).lower(): return
    m = await context.bot.send_message(chat_id, text, reply_markup=markup, parse_mode=HTML, disable_web_page_preview=True); context.user_data["panel"] = m.message_id

async def ask(update, context, prompt, kind, back, **extra):
    lang = L(update); context.user_data["await"] = {"kind": kind, "back": back, **extra}
    await render(update, context, f"✏️ {prompt}\n\n<i>{tr(lang, 'send_value')}</i>", [[B(tr(lang, "cancel"), "c:cancel")]])

async def wiz_start(update, context, wiz, back, **data): context.user_data["await"] = {"kind": "wiz", "wiz": wiz, "step": 0, "data": data, "back": back}; await wiz_prompt(update, context)
async def wiz_prompt(update, context):
    lang = L(update); st = context.user_data["await"]; steps = WIZ[st["wiz"]]; i = st["step"]
    await render(update, context, f"{tr(lang, 'step', i=i + 1, n=len(steps))} ✏️ {steps[i][1][1 if lang == 'en' else 0]}\n\n<i>{tr(lang, 'send_value')}</i>", [[B(tr(lang, "cancel"), "c:cancel")]])

async def notify_supers(text, kb=None):
    for sid in SUPER_ADMIN_IDS:
        try: await APP.bot.send_message(sid, text, parse_mode=HTML, reply_markup=kbm(kb) if kb and isinstance(kb[0][0], tuple) else (InlineKeyboardMarkup(kb) if kb else None), disable_web_page_preview=True)
        except Exception as e: log.warning(f"notify {sid}: {e}")

async def notify_user_fn(uid, text, kb=None):
    try: await APP.bot.send_message(uid, text, parse_mode=HTML, reply_markup=kbm(kb), disable_web_page_preview=True)
    except Exception as e: log.warning(f"notify user {uid}: {e}")

async def go_home(update, context):
    uid = update.effective_user.id; context.user_data.pop("await", None)
    if not user_lang(uid): return await view_lang(update, context)
    return await (view_super_home if is_super(uid) else view_admin_home if can_admin(uid) else view_user_home)(update, context)

# ============================================================
# نماهای کاربری، کانال و محتوا
async def view_lang(update, context): await render(update, context, tr("fa", "choose_lang"), [[B("🇮🇷 فارسی", "lang:fa"), B("🇬🇧 English", "lang:en")]])

async def set_language(update, context, lang):
    uid = update.effective_user.id; set_lang(uid, lang)
    try: n = relocalize_all(uid, lang)
    except Exception as e: log.warning(f"relocalize_all {uid}: {e}"); n = 0
    await popup(update, context, tr(lang, "lang_set") + (tr(lang, "lang_set_n", n=n) if n else "")); await go_home(update, context)

async def view_user_home(update, context):
    lang = L(update); u = update.effective_user
    await render(update, context, gtext("welcome", lang, name=esc(u.first_name)), [[B(tr(lang, "plans_btn"), "u:plans")]])

async def view_plans(update, context):
    uid = update.effective_user.id; lang = L(update); lim = admin_limits(uid); text = tr(lang, "plans_title") + "\n\n"
    if lim["plan_id"]: text += tr(lang, "plans_current", name=esc(plan_txt(lim["plan"], "name", lang)), until=tr(lang, "until", d=fmt_date(lim["expires"], admin_offset(uid))) if lim["expires"] else "") + "\n"
    if lim["next_plan"]: text += tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang))) + "\n"
    text += "\n" + tr(lang, "plans_pick")
    kb = pairs([B(f"{'🎁' if p['is_free'] else '⭐'} {plan_txt(p, 'name', lang)}", f"u:plan:{p['id']}") for p in list_plans()])
    kb.append([B(tr(lang, "back"), "home")]); await render(update, context, text, kb)

def _applied_disc(context, pid):
    code = (context.user_data.get("disc") or {}).get(str(pid)); d, why = disc_valid(code) if code else (None, "")
    return d

def _price_text(p, lang, d):
    price = plan_txt(p, "price", lang) or tr(lang, "free_word")
    return (discount_price(price, d["percent"]), price) if d else (price, None)

async def view_plan(update, context, pid):
    uid = update.effective_user.id; lang = L(update); p = get_plan(pid); u = get_user(uid); lim = admin_limits(uid)
    if not p: await popup(update, context, tr(lang, "plan_notfound")); return await view_plans(update, context)
    d = _applied_disc(context, pid); new_price, old_price = _price_text(p, lang, d)
    text = f"{'🎁' if p['is_free'] else '⭐'} <b>{esc(plan_txt(p, 'name', lang))}</b>\n{esc(plan_txt(p, 'description', lang))}\n\n" + tr(lang, "plan_details", days=p["days"], posts=p["daily_posts"], src=p["max_sources"], ch=p["max_channels"], tests=p["daily_tests"], price=esc(new_price))
    if d: text += "\n" + tr(lang, "plan_disc_line", old=esc(old_price), new=esc(new_price), code=esc(d["code"]), p=d["percent"])
    kb = []
    if p["is_free"]: kb.append([B(tr(lang, "plan_free_used"), "noop") if u and u["free_used"] else B(tr(lang, "plan_free_btn"), f"u:free:{pid}")])
    else:
        text += "\n\n" + tr(lang, "plan_chain_note")
        if pay_pending_for(uid, pid): kb.append([B(tr(lang, "plan_pending_btn"), "noop")])
        else: kb.append([B(tr(lang, "plan_renew_btn" if lim["plan_id"] == pid and lim["active"] else "plan_req_btn"), f"u:req:{pid}"), B(tr(lang, "disc_remove") if d else tr(lang, "disc_btn"), f"u:disc{'x' if d else ''}:{pid}")])
    kb.append([B(tr(lang, "back"), "u:plans")]); await render(update, context, text, kb)

async def do_free(update, context, pid):
    uid = update.effective_user.id; lang = L(update); u = get_user(uid); p = get_plan(pid)
    if not p or not p["is_free"] or u["free_used"]: await popup(update, context, tr(lang, "free_once"), alert=True); return await view_plans(update, context)
    assign_plan(uid, pid); log_event("INFO", f"پلن رایگان فعال شد برای {uid}", uid); await popup(update, context, tr(lang, "free_done", name=plan_txt(p, "name", lang)), alert=True)
    await notify_supers(f"🎁 {esc(uname(u))} (<code>{uid}</code>) پلن رایگان را فعال کرد."); await view_admin_home(update, context)

async def do_request(update, context, pid):
    uid = update.effective_user.id; lang = L(update); p = get_plan(pid)
    if not p: await popup(update, context, tr(lang, "plan_notfound")); return await view_plans(update, context)
    if pay_pending_for(uid, pid): await popup(update, context, tr(lang, "req_pending"), alert=True); return await view_plan(update, context, pid)
    d = _applied_disc(context, pid); new_price, _ = _price_text(p, lang, d)
    context.user_data["await"] = {"kind": "receipt", "pid": pid, "back": f"u:plan:{pid}", "disc": d["code"] if d else None, "final": new_price}
    await render(update, context, gtext("pay", lang, plan=esc(plan_txt(p, "name", lang)), price=esc(new_price)) + tr(lang, "receipt_hint"), [[B(tr(lang, "cancel"), "c:cancel")]])

async def view_receipt_ok(update, context): lang = L(update); await render(update, context, tr(lang, "receipt_ok"), [[B(tr(lang, "wait_btn"), "home")]], force_new=True)

async def view_admin_home(update, context):
    uid = update.effective_user.id; lang = L(update); lim = admin_limits(uid); use = usage_today(uid); chs = list_channels(uid)
    pname = "∞" if is_super(uid) else (plan_txt(lim["plan"], "name", lang) or tr(lang, "no_plan"))
    text = (f"{tr(lang, 'panel')}\n🧾 <b>{esc(pname)}</b>" + (tr(lang, "until", d=fmt_date(lim["expires"], admin_offset(uid))) if lim["expires"] else "") + "\n" +
            tr(lang, "today_line", p=use["posts"], pc=cap(lim["daily_posts"]), t=use["tests"], tc=cap(lim["daily_tests"]), c=len(chs), cc=cap(lim["max_channels"]), s=count_sources(uid), sc=cap(lim["max_sources"])))
    if lim["next_plan"]: text += "\n" + tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang)))
    if not lim["active"]: text += "\n\n" + tr(lang, "plan_inactive")
    text += "\n\n" + (tr(lang, "pick_channel") if chs else tr(lang, "no_channels"))
    kb = pairs([B(f"{'🟢' if get_settings(c['id'])['enabled'] else '🔴'} {c['title'][:22]}", f"a:ch:{c['id']}") for c in chs])
    kb.append([B(tr(lang, "ch_add"), "a:chadd")]); kb.append([B(tr(lang, "my_plan"), "a:plan")])
    if is_super(uid): kb.append([B(tr(lang, "super_panel"), "s:home")])
    await render(update, context, text, kb)

async def view_channel(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: await popup(update, context, tr(lang, "notfound")); return await view_admin_home(update, context)
    s = get_settings(cid); on = s["enabled"]
    text = (tr(lang, "ch_panel", title=esc(ch["title"])) + (f" · @{ch['username']}" if ch["username"] else "") + "\n" + tr(lang, "ch_status", i="🟢" if on else "🔴", st=tr(lang, "on" if on else "off"), mode=tr(lang, "auto" if s["mode"] == "auto" else "review")) + "\n" +
            tr(lang, "ch_stats", s=len(list_sources(cid, True)), q=ready_count(cid), p=count_articles(cid=cid, hours=24, status="published"), r=count_articles(cid=cid, hours=24, status="rejected"), a=ago_text(s["last_run"], lang)))
    kb = [[B(tr(lang, "report"), f"a:rep:{cid}"), B(tr(lang, "test"), f"a:test:{cid}")], [B(tr(lang, "sources", n=len(list_sources(cid))), f"a:src:{cid}"), B(tr(lang, "content"), f"a:con:{cid}")],
          [B(tr(lang, "sched"), f"a:sch:{cid}"), B(tr(lang, "queue", n=ready_count(cid)), f"a:que:{cid}")], [B(tr(lang, "rejected"), f"a:rej:{cid}"), B(tr(lang, "lock"), f"a:lock:{cid}")],
          [B(tr(lang, "logs"), f"a:logs:{cid}"), B(tr(lang, "automation", i="🟢" if on else "🔴"), f"a:tog:{cid}:enabled")], [B(tr(lang, "ch_del"), f"a:chdel:{cid}")], [B(tr(lang, "back"), "a:home")]]
    await render(update, context, text, kb)

async def view_lock(update, context, cid):
    lang = L(update); ch = channel_owned(cid, update.effective_user.id)
    if not ch: return await view_admin_home(update, context)
    await render(update, context, tr(lang, "lock_text", title=esc(ch["title"]), code=ch["lock_code"] or regen_lock(cid)), [[B(tr(lang, "lock_regen"), f"a:lockre:{cid}")], [B(tr(lang, "back"), f"a:ch:{cid}")]])

async def view_sources(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: return await view_admin_home(update, context)
    srcs = list_sources(cid); lim = admin_limits(uid)
    text = tr(lang, "src_title", title=esc(ch["title"]), n=count_sources(uid), cap=cap(lim["max_sources"])) + "\n" + "".join(
        tr(lang, "src_line", i="🟢" if s["active"] else "🔴", b="🤖" if (s["bot_active"] is None or s["bot_active"]) else "🚫", host=esc(hostname(s["url"])) + (" 🔌" if _has_api(s) else ""), n=s["found_total"], err=tr(lang, "src_err", n=s["fail_count"]) if s["fail_count"] else "") for s in srcs)
    kb = pairs([B(f"{'🟢' if s['active'] else '🔴'} {hostname(s['url'])[:22]}", f"a:srcv:{s['id']}") for s in srcs]) + [[B(tr(lang, "src_add"), f"a:srca:{cid}")], [B(tr(lang, "back"), f"a:ch:{cid}")]]
    await render(update, context, text, kb)

async def view_source(update, context, sid):
    lang = L(update); s = get_source(sid)
    if not s or (s["admin_id"] != update.effective_user.id and not is_super(update.effective_user.id)): return await view_admin_home(update, context)
    bot_on = s["bot_active"] is None or s["bot_active"]
    st = tr(lang, "src_st", c="🟢" if s["active"] else "🔴", b="🤖" if bot_on else "🚫")
    api = tr(lang, "src_api_on", u=esc(str(s["api_url"])[:60])) if _has_api(s) else tr(lang, "src_api_none")
    text = tr(lang, "src_view", host=esc(hostname(s["url"])), url=esc(s["url"]), feed=tr(lang, "src_feed", u=esc(s["feed_url"])) if s["feed_url"] and s["feed_url"] != s["url"] else "", st=st, last=ago_text(s["last_fetch"], lang), n=s["found_total"], f=s["fail_count"], err=f"\n⚠️ <code>{esc((s['last_error'] or '')[:120])}</code>" if s["last_error"] else "") + "\n" + api
    kb = [[B(tr(lang, "src_recheck"), f"a:srcr:{sid}")], [B(("🟢 " if s["active"] else "🔴 ") + tr(lang, "tog_ch"), f"a:srct:{sid}"), B(("🟢 " if bot_on else "🔴 ") + tr(lang, "tog_bot"), f"a:srctb:{sid}")],
          [B(tr(lang, "src_api"), f"a:srcapi:{sid}")] + ([B(tr(lang, "src_api_del"), f"a:srcapix:{sid}")] if _has_api(s) else []), [B(tr(lang, "delete"), f"a:srcd:{sid}")], [B(tr(lang, "back"), f"a:src:{s['channel_id']}")]]
    await render(update, context, text, kb)

async def view_content(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: return await view_admin_home(update, context)
    s = get_settings(cid)
    text = tr(lang, "content_title", title=esc(ch["title"]), topic=esc(s["topic"] or tr(lang, "general")), lang=esc(s["language"]), prompt=esc(s["prompt"][:2500]) + ("…" if len(s["prompt"]) > 2500 else ""), sig=esc(strip_tags(s["signature"])[:60]) or "—")
    kb = [[B(tr(lang, "b_topic"), f"a:set:{cid}:topic"), B(tr(lang, "b_lang"), f"a:set:{cid}:language")], [B(tr(lang, "b_prompt"), f"a:set:{cid}:prompt"), B(tr(lang, "b_sig"), f"a:set:{cid}:signature")],
          [B(tr(lang, "b_cats", n=len(s["categories"])), f"a:cat:{cid}"), B(tr(lang, "b_crits", n=len(s["criteria"])), f"a:cri:{cid}")], [B(tr(lang, "b_min", n=s["min_score"]), f"a:set:{cid}:min_score"), B(tr(lang, "b_words", n=s["max_words"]), f"a:set:{cid}:max_words")],
          [B(tr(lang, "b_limit", n=s["post_limit"]), f"a:set:{cid}:post_limit"), B(tr(lang, "b_hashtags", i=onoff(s["hashtags"])), f"a:tog:{cid}:hashtags")], [B(tr(lang, "b_link", i=onoff(s["include_link"])), f"a:tog:{cid}:include_link"), B(tr(lang, "b_media", i=onoff(s["include_media"])), f"a:tog:{cid}:include_media")],
          [B(tr(lang, "b_strict", i=onoff(s["strict_ads"])), f"a:tog:{cid}:strict_ads"), B(tr(lang, "b_premium", i=onoff(s["premium_format"])), f"a:tog:{cid}:premium_format")], [B(tr(lang, "back"), f"a:ch:{cid}")]]
    await render(update, context, text, kb)

async def view_cats(update, context, cid):
    lang = L(update); s = get_settings(cid)
    text = tr(lang, "cats_title") + "\n" + "".join(f"\n{c['emoji']} <b>{esc(c['name'])}</b>: {esc(c['style'][:70])}" for c in s["categories"])
    kb = pairs([B(f"{c['emoji']} {c['name'][:18]}", f"a:catv:{cid}:{i}") for i, c in enumerate(s["categories"])]) + [[B(tr(lang, "cat_add"), f"a:cata:{cid}")], [B(tr(lang, "back"), f"a:con:{cid}")]]; await render(update, context, text, kb)

async def view_cat(update, context, cid, i):
    lang = L(update); s = get_settings(cid); c = s["categories"][i] if i < len(s["categories"]) else None
    if not c: return await view_cats(update, context, cid)
    await render(update, context, tr(lang, "cat_view", e=c["emoji"], name=esc(c["name"]), style=esc(c["style"])), [[B(tr(lang, "cat_edit"), f"a:cats:{cid}:{i}"), B(tr(lang, "delete"), f"a:catd:{cid}:{i}")], [B(tr(lang, "back"), f"a:cat:{cid}")]])

async def view_crits(update, context, cid):
    lang = L(update); s = get_settings(cid); tot = sum(float(c["weight"]) for c in s["criteria"]) or 1
    text = tr(lang, "crits_title", m=s["min_score"]) + "\n" + "".join(tr(lang, "crit_line", name=esc(c["name"]), w=c["weight"], p=f"{float(c['weight']) / tot * 100:.0f}") for c in s["criteria"])
    kb = pairs([B(tr(lang, "crit_btn", name=c["name"][:16], w=c["weight"]), f"a:criv:{cid}:{i}") for i, c in enumerate(s["criteria"])]) + [[B(tr(lang, "crit_add"), f"a:cria:{cid}")], [B(tr(lang, "back"), f"a:con:{cid}")]]; await render(update, context, text, kb)

async def view_crit(update, context, cid, i):
    lang = L(update); s = get_settings(cid); c = s["criteria"][i] if i < len(s["criteria"]) else None
    if not c: return await view_crits(update, context, cid)
    await render(update, context, tr(lang, "crit_view", name=esc(c["name"]), w=c["weight"]), [[B(tr(lang, "crit_w"), f"a:criw:{cid}:{i}"), B(tr(lang, "delete"), f"a:crid:{cid}:{i}")], [B(tr(lang, "back"), f"a:cri:{cid}")]])

def hour_grid(prefix): return [[B(f"{h:02d}", f"{prefix}:{h}") for h in range(r, r + 6)] for r in range(0, 24, 6)]

async def view_sched(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: return await view_admin_home(update, context)
    s = get_settings(cid); off = s["utc_offset"]; quiet = f"{s['quiet_start']:02d}→{s['quiet_end']:02d}" if s["quiet_start"] is not None and s["quiet_end"] is not None else tr(lang, "none")
    text = tr(lang, "sched_title", title=esc(ch["title"]), iv=s["interval_minutes"], ppc=s["posts_per_cycle"], lb=s["lookback_hours"], ud=onoff(s["allow_undated"]), quiet=quiet, city=tz_city(off, lang), tz=off_label(off), loc=local_clock(off), utc=utc_clock(), mode=tr(lang, "mode_auto" if s["mode"] == "auto" else "mode_review"))
    kb = [[B(tr(lang, "b_interval", n=s["interval_minutes"]), f"a:set:{cid}:interval_minutes"), B(tr(lang, "b_ppc", n=s["posts_per_cycle"]), f"a:set:{cid}:posts_per_cycle")], [B(tr(lang, "b_lookback", n=s["lookback_hours"]), f"a:set:{cid}:lookback_hours"), B(tr(lang, "b_undated", i=onoff(s["allow_undated"])), f"a:tog:{cid}:allow_undated")],
          [B(tr(lang, "b_quiet"), f"a:quiet:{cid}"), B(tr(lang, "b_tz"), f"a:tz:{cid}")], [B(tr(lang, "b_mode", m=tr(lang, "auto" if s["mode"] == "auto" else "review")), f"a:mode:{cid}")], [B(tr(lang, "back"), f"a:ch:{cid}")]]
    await render(update, context, text, kb)

async def view_quiet(update, context, cid):
    lang = L(update); s = get_settings(cid)
    await render(update, context, tr(lang, "quiet_pick_start"), hour_grid(f"a:qs:{cid}") + [[B(tr(lang, "quiet_off"), f"a:qoff:{cid}")], [B(tr(lang, "back"), f"a:sch:{cid}")]])

async def view_tz(update, context, cid):
    lang = L(update); s = get_settings(cid); cur = float(s["utc_offset"]); i = 1 if lang == "en" else 0
    rows = pairs([B(("✅ " if abs(o - cur) < 0.01 else "") + f"{TZ_NAMES[z][i]} {off_label(o)}", f"a:tzs:{cid}:{k}") for k, (z, o) in enumerate(TZ_ZONES)])
    await render(update, context, tr(lang, "tz_pick", utc=utc_clock()), rows + [[B(tr(lang, "back"), f"a:sch:{cid}")]])

async def view_queue(update, context, cid, status="ready"):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: return await view_admin_home(update, context)
    arts = articles_by_status(cid, status, 15 if status == "ready" else 5)
    if status == "ready": text = tr(lang, "queue_title", title=esc(ch["title"]), n=len(arts))
    else: text = tr(lang, "rej_title", title=esc(ch["title"])) + "\n" + "".join(f"\n• {esc((r['title'] or hostname(r['url']))[:40])} — <i>{esc(reason_text(r['reason'], lang))}</i>" for r in arts)
    kb = [[B(f"{'⭐' + str(a['score']) if a['score'] else '•'} {(a['title'] or hostname(a['url']))[:35]}", f"a:art:{a['id']}")] for a in arts]
    if status == "ready" and arts: kb.append([B(tr(lang, "pub_first"), f"a:pub:{arts[0]['id']}")])
    kb.append([B(tr(lang, "back"), f"a:ch:{cid}")]); await render(update, context, text, kb)

async def view_article(update, context, aid):
    uid = update.effective_user.id; lang = L(update); a = get_article(aid)
    if not a or (a["admin_id"] != uid and not is_super(uid)): await popup(update, context, tr(lang, "notfound")); return await view_admin_home(update, context)
    cid = a["channel_id"]; body, _ = fit_html(a["post_html"] or tr(lang, "art_nobody"), 2600); i = 1 if lang == "en" else 0
    rt = reason_text(a["reason"], lang)
    text = tr(lang, "art_title", title=esc((a["title"] or "")[:80]), score=a["score"] or "—", cat=esc(a["category"] or "—"), st=STATUS.get(a["status"], (a["status"], a["status"]))[i], reason=f" · {esc(rt)}" if rt else "", host=esc(hostname(a["url"])), body=body)
    kb = []
    if a["status"] == "ready":
        kb.append([B(tr(lang, "art_pub"), f"a:pub:{aid}"), B(tr(lang, "art_edit"), f"a:arte:{aid}")]); row = [B(tr(lang, "delete"), f"a:artd:{aid}")]
        if a["full_html"]: row.insert(0, B(tr(lang, "art_full"), f"a:artf:{aid}"))
        kb.append(row)
    elif a["status"] == "published":
        links = json.loads(a["links"] or "[]")
        if links: kb.append([U(tr(lang, "art_view"), links[0])])
        kb.append([B(tr(lang, "art_del_arch"), f"a:artd:{aid}")])
    else:
        row = [B(tr(lang, "delete"), f"a:artd:{aid}")]
        if a["post_html"]: row.insert(0, B(tr(lang, "art_to_ready"), f"a:artr:{aid}"))
        kb.append(row)
    kb.append([B(tr(lang, "back"), f"a:que:{cid}" if a["status"] in ("ready", "published") else f"a:rej:{cid}")]); await render(update, context, text, kb)

async def view_my_plan(update, context):
    uid = update.effective_user.id; lang = L(update); lim = admin_limits(uid); use = usage_today(uid)
    pname = "∞" if is_super(uid) else (plan_txt(lim["plan"], "name", lang) or tr(lang, "no_plan"))
    text = tr(lang, "myplan", name=esc(pname), st=tr(lang, "st_active" if lim["active"] else "st_expired"), exp=tr(lang, "exp_at", d=fmt_date(lim["expires"], admin_offset(uid), True)) if lim["expires"] else "", nxt=("\n" + tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang)))) if lim["next_plan"] else "",
              p=use["posts"], pc=cap(lim["daily_posts"]), t=use["tests"], tc=cap(lim["daily_tests"]), s=count_sources(uid), sc=cap(lim["max_sources"]), c=len(list_channels(uid)), cc=cap(lim["max_channels"]))
    await render(update, context, text, [[B(tr(lang, "upgrade_btn"), "u:plans")], [B(tr(lang, "back"), "a:home")]])

async def view_logs(update, context, admin_id=None, level=None, back="a:home", refresh="a:logs"):
    lang = L(update); n = 10 if admin_id else 20; rows = recent_logs(n, admin_id=admin_id, level=level)
    text = tr(lang, "logs_title", lvl=f" · {level}" if level else "") + ("\n".join(f"{'🔴' if r['level'] == 'ERROR' else '🟡' if r['level'] == 'WARN' else '🔵'} <code>{r['ts'][11:16]}</code> {esc(r['msg'][:100])}" for r in rows) or tr(lang, "logs_empty"))
    if admin_id: text += tr(lang, "logs_note")
    kb = [[B(tr(lang, "refresh"), refresh)], [B(tr(lang, "back"), back)]] if admin_id else [[B(tr(lang, "all"), "s:logs:all"), B(tr(lang, "errors"), "s:logs:ERROR"), B(tr(lang, "warns"), "s:logs:WARN")], [B(tr(lang, "back"), back)]]
    await render(update, context, text, kb)

async def run_test(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid); qy = update.callback_query
    if not ch: return await view_admin_home(update, context)
    rem = remaining(uid, "tests")
    if rem is not None and rem <= 0: await popup(update, context, tr(lang, "limit_tests", n=admin_limits(uid)["daily_tests"]), alert=True); return await view_channel(update, context, cid)
    if ch_lock(cid).locked(): await popup(update, context, tr(lang, "test_busy"), alert=True); return await view_channel(update, context, cid)
    if not is_super(uid) and not rate_free(f"test:{cid}", TEST_COOLDOWN_SEC): await popup(update, context, tr(lang, "test_wait", n=rate_left(f"test:{cid}", TEST_COOLDOWN_SEC)), alert=True); return await view_channel(update, context, cid)
    try: await qy.answer(); context.user_data["_answered"] = True
    except Exception: pass
    last = [0.0]; head = tr(lang, "test_head", title=esc(ch["title"]))
    async def progress(pct, txt):
        if time.time() - last[0] < 1.6 and pct < 100: return
        last[0] = time.time()
        try: await qy.edit_message_text(f"{head}\n\n{bar(pct)} <b>{pct}%</b>\n⏳ {esc(txt)}", parse_mode=HTML)
        except Exception: pass
    await progress(1, tr(lang, "preparing"))
    try: res = await run_channel_cycle(context.bot, uid, cid, test_mode=True, progress=progress)
    except Exception as e:
        log_event("ERROR", f"تست کانال {ch['title']}: {e}", uid); d = Diag(); d.add("ai_fail", err=ai_err_text(err_code(e), lang)); res = {"published": 0, "queued": 0, "links": [], "diag": d, "src": ""}
    ok = bool(res["published"] or res.get("queued"))
    if ok: rate_mark(f"test:{cid}")
    else: rate_clear(f"test:{cid}")
    diag = esc(res["diag"].render(lang)); kb = []
    src = (res.get("src") or "").strip(); src_line = ("\n" + tr(lang, "test_src", name=esc(src[:60]))) if src else ""
    if res["published"]: text = f"{tr(lang, 'test_ok')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}"; kb.append([U(f"{tr(lang, 'art_view')} {i + 1}", l) for i, l in enumerate(res["links"][:3])])
    elif res.get("queued"): text = f"{tr(lang, 'test_queued')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}"; kb.append([B(tr(lang, "queue", n=ready_count(cid)), f"a:que:{cid}")])
    else: text = f"{tr(lang, 'test_fail')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}\n\n{tr(lang, 'test_retry_note')}"; kb.append([B(tr(lang, "rejected"), f"a:rej:{cid}"), B(tr(lang, "sched"), f"a:sch:{cid}")])
    kb.append([B(tr(lang, "back_panel"), f"a:ch:{cid}")]); await render(update, context, text, kb)

# ============================================================
# پنل مدیریت کلان (Super Admin Views)
async def view_super_home(update, context):
    uid = update.effective_user.id
    if not is_super(uid): return await view_user_home(update, context)
    roles = {r["role"]: r["c"] for r in count_users()}; models = list_models(); ok = sum(1 for m in models if m["active"] and m["status"] == "ok")
    auto = gget("automation_enabled", True); npay = len(pay_pending())
    text = (f"👑 <b>مدیریت کلان</b>\n\n{'🟢' if auto else '🔴'} اتوماسیون · 👥 کاربران {sum(roles.values())} (مدیر {roles.get('admin', 0)})\n"
            f"📢 کانال‌ها {q('SELECT COUNT(*) c FROM channels', one=True)['c']} · 🤖 مدل‌ها {ok}/{len(models)}\n"
            f"🧾 پلن‌ها {len(list_plans())} · 🛎 پرداخت‌ها {npay} · 🎟 تخفیف‌ها {len(disc_list())}")
    kb = [[B("📊 گزارش کامل", "s:rep"), B("👥 کاربران", "s:users:0")],
          [B(f"🛎 پرداخت‌ها ({npay})", "s:pays"), B("🧾 پلن‌ها", "s:plans")],
          [B(f"🤖 مدل‌های AI ({len(models)})", "s:models"), B("🎟 کدهای تخفیف", "s:discs")],
          [B("📢 پیام همگانی", "s:bcast"), B("⚙️ متن‌ها و تنظیمات", "s:texts")],
          [B("📜 لاگ کل سیستم", "s:logs:all"), B(f"{'🔴 توقف' if auto else '🟢 شروع'} اتوماسیون", "s:togauto")],
          [B("🛠 پنل مدیریت من", "a:home")]]
    await render(update, context, text, kb)

async def view_super_users(update, context, page=0):
    page = int(page); users = list_users(limit=10, offset=page * 10); total = q("SELECT COUNT(*) c FROM users", one=True)["c"]
    text = f"👥 <b>کاربران</b> ({total} کل)\nصفحه {page + 1} از {max(1, (total + 9) // 10)}\n"
    btns = []
    for u in users:
        p = get_plan(u["plan_id"]) if u["plan_id"] else None
        pname = f" · {plan_txt(p, 'name', 'fa')}" if p else ""
        btns.append([B(f"{'🚫 ' if u['banned'] else ''}{uname(u)[:20]}{pname}", f"s:u:{u['id']}")])
    nav = []
    if page > 0: nav.append(B("⬅️ قبلی", f"s:users:{page - 1}"))
    if (page + 1) * 10 < total: nav.append(B("بعدی ➡️", f"s:users:{page + 1}"))
    if nav: btns.append(nav)
    btns.append([B("🔙 بازگشت", "s:home")]); await render(update, context, text, btns)

async def view_super_user(update, context, uid):
    u = get_user(uid)
    if not u: return await view_super_users(update, context)
    p = get_plan(u["plan_id"]) if u["plan_id"] else None; np = get_plan(u["next_plan_id"]) if u["next_plan_id"] else None
    text = (f"👤 <b>{esc(uname(u))}</b> (<code>{uid}</code>)\nنقش: <b>{u['role']}</b> · زبان: {u['lang'] or '—'}\n"
            f"پلن: <b>{esc(plan_txt(p, 'name', 'fa')) if p else 'بدون پلن'}</b>" + (f" تا {fmt_date(u['plan_expires'], DEFAULT_UTC_OFFSET)}" if u['plan_expires'] else "") + "\n" +
            (f"پلن بعدی: <b>{esc(plan_txt(np, 'name', 'fa'))}</b>\n" if np else "") +
            f"کانال‌ها: {len(list_channels(uid))} · منابع: {count_sources(uid)}\nثبت: {fmt_date(u['created_at'], DEFAULT_UTC_OFFSET)}\nوضعیت: {'🚫 مسدود' if u['banned'] else '🟢 فعال'}")
    kb = [[B("🧾 تخصیص پلن", f"s:usetp:{uid}"), B("🚫 لغو پلن", f"s:uclrp:{uid}")],
          [B("🟢 رفع انسداد" if u["banned"] else "🚫 مسدود کردن", f"s:uban:{uid}")],
          [B("👑 ارتقا به کلان" if u["role"] != "super" else "👤 تنزل از کلان", f"s:urole:{uid}")],
          [B("🔙 بازگشت", "s:users:0")]]
    await render(update, context, text, kb)

async def view_super_plans(update, context):
    plans = list_plans()
    text = "🧾 <b>مدیریت پلن‌ها</b>\nبرای مشاهده یا ویرایش، یک پلن را انتخاب کنید:"
    kb = [[B(f"{'🎁' if p['is_free'] else '⭐'} {p['name']} ({p['days']} روز)", f"s:plan:{p['id']}")] for p in plans]
    kb.append([B("➕ پلن جدید", "s:plana")]); kb.append([B("🔙 بازگشت", "s:home")]); await render(update, context, text, kb)

async def view_super_plan(update, context, pid):
    p = get_plan(pid)
    if not p: return await view_super_plans(update, context)
    text = (f"🧾 <b>{esc(p['name'])}</b> ({esc(p['name_en'] or '')})\n{esc(p['description'] or '')}\n\n"
            f"مدت: {p['days']} روز · قیمت: {esc(p['price'] or 'رایگان')}\n"
            f"پست روزانه: {p['daily_posts']} · تست روزانه: {p['daily_tests']}\n"
            f"سقف منابع: {p['max_sources']} · سقف کانال‌ها: {p['max_channels']}\nوضعیت: {'🎁 رایگان' if p['is_free'] else '💳 پولی'}")
    kb = [[B("✏️ تغییر قیمت", f"s:plpr:{pid}"), B("✏️ مدت (روز)", f"s:pldy:{pid}")],
          [B("🗑 حذف پلن", f"s:pldel:{pid}")], [B("🔙 بازگشت", "s:plans")]]
    await render(update, context, text, kb)

async def view_super_models(update, context):
    models = list_models()
    text = "🤖 <b>مدل‌های هوش مصنوعی</b>\nترتیب اولویت به صورت آبشاری (Fallback) است:\n"
    btns = []
    for i, m in enumerate(models):
        st = "🟢" if m["status"] == "ok" else "🔴"
        btns.append([B(f"{i + 1}. {st} {m['model'][:25]}", f"s:mview:{m['id']}")])
    btns.append([B("➕ افزودن مدل جدید", "s:madd")]); btns.append([B("🔙 بازگشت", "s:home")]); await render(update, context, text, btns)

async def view_super_model(update, context, mid):
    m = get_model(mid)
    if not m: return await view_super_models(update, context)
    text = (f"🤖 <b>{esc(m['model'])}</b>\n"
            f"Base URL: <code>{esc(m['base_url'])}</code>\n"
            f"وضعیت: {'🟢 فعال' if m['active'] else '⚪ خاموش'} ({m['status']})\n"
            f"خطای آخر: <code>{esc((m['last_error'] or '')[:150])}</code>\n"
            f"بررسی آخر: {ago_text(m['last_check'], 'fa')}")
    kb = [[B("🔄 تست فوری", f"s:mtest:{mid}"), B("⏯ فعال/غیرفعال", f"s:mtog:{mid}")],
          [B("⬆️ اولویت بالاتر", f"s:mup:{mid}"), B("⬇️ اولویت پایین‌تر", f"s:mdn:{mid}")],
          [B("🗑 حذف مدل", f"s:mdel:{mid}")], [B("🔙 بازگشت", "s:models")]]
    await render(update, context, text, kb)

async def view_super_discs(update, context):
    discs = disc_list()
    text = f"🎟 <b>کدهای تخفیف</b> ({len(discs)})\n\n" + "".join(
        f"• <code>{esc(d['code'])}</code>: −{d['percent']}% (مصرف {d['used_count']}/{d['max_uses'] or '∞'})\n" for d in discs[:15])
    kb = [[B("➕ کد جدید", "s:disca")], [B("🔙 بازگشت", "s:home")]]
    await render(update, context, text, kb)

async def view_super_pays(update, context):
    pays = pay_pending()
    text = f"🛎 <b>درخواست‌های پرداخت معلق</b> ({len(pays)})\n"
    btns = []
    for py in pays:
        u = get_user(py["user_id"]); p = get_plan(py["plan_id"])
        btns.append([B(f"{uname(u)[:15]} · {plan_txt(p, 'name', 'fa') if p else '—'}", f"s:payv:{py['id']}")])
    btns.append([B("🔙 بازگشت", "s:home")]); await render(update, context, text, btns)

async def view_super_pay(update, context, pid):
    py = q("SELECT * FROM payments WHERE id=?", (pid,), one=True)
    if not py: return await view_super_pays(update, context)
    u = get_user(py["user_id"]); p = get_plan(py["plan_id"])
    text = (f"🛎 <b>رسید پرداخت #{py['id']}</b>\n"
            f"کاربر: {esc(uname(u))} (<code>{py['user_id']}</code>)\n"
            f"پلن: <b>{esc(plan_txt(p, 'name', 'fa') if p else '—')}</b>\n"
            f"کد تخفیف: <code>{esc(py['discount_code'] or '—')}</code>\n"
            f"مبلغ نهایی: <b>{esc(py['final_price'] or '—')}</b>\n"
            f"زمان ارسال: {fmt_date(py['created_at'], DEFAULT_UTC_OFFSET, True)}")
    kb = [[B("✅ تأیید پرداخت", f"s:payok:{pid}"), B("❌ رد پرداخت", f"s:payno:{pid}")], [B("🔙 بازگشت", "s:pays")]]
    if py["receipt_file_id"]:
        try: await update.effective_chat.send_photo(py["receipt_file_id"], caption=text, reply_markup=kbm(kb), parse_mode=HTML); return
        except Exception as e: log.warning(f"send receipt photo: {e}")
    await render(update, context, text + f"\n\nیادداشت/متن:\n<code>{esc(py['receipt_text'] or '—')}</code>", kb)

async def view_super_texts(update, context):
    text = "⚙️ <b>تنظیمات و پیام‌های سیستمی</b>\nبرای ویرایش هر پیام، کلید مربوطه را انتخاب کنید:"
    kb = [[B("📝 متن خوش‌آمدگویی", "s:tedit:welcome"), B("💳 راهنمای کارت/پرداخت", "s:tedit:pay")],
          [B("📞 پشتیبانی /man", "s:tedit:support"), B("🔙 بازگشت", "s:home")]]
    await render(update, context, text, kb)

# ============================================================
# پردازش رویدادهای تلگرام (Handlers & Dispatchers)
async def on_callback(update, context):
    qy = update.callback_query; data = qy.data; uid = update.effective_user.id; lang = L(update)
    if is_banned(uid): return await popup(update, context, tr(lang, "banned"), alert=True)
    if not rate_free(f"cb:{uid}", 0.3): return await popup(update, context, tr(lang, "busy_click"))
    rate_mark(f"cb:{uid}")

    if data == "noop":
        try: await qy.answer()
        except Exception: pass
        return
    if data == "home": return await go_home(update, context)
    if data.startswith("lang:"): return await set_language(update, context, data.split(":")[1])

    # User flows
    if data == "u:plans": return await view_plans(update, context)
    if data.startswith("u:plan:"): return await view_plan(update, context, int(data.split(":")[2]))
    if data.startswith("u:free:"): return await do_free(update, context, int(data.split(":")[2]))
    if data.startswith("u:req:"): return await do_request(update, context, int(data.split(":")[2]))
    if data.startswith("u:disc:"):
        pid = int(data.split(":")[2]); context.user_data["disc_pid"] = pid
        return await ask(update, context, tr(lang, "disc_prompt"), "disc", f"u:plan:{pid}")
    if data.startswith("u:discx:"):
        pid = int(data.split(":")[2])
        if "disc" in context.user_data: context.user_data["disc"].pop(str(pid), None)
        return await view_plan(update, context, pid)

    # Admin home & channel flows
    if data == "a:home": return await view_admin_home(update, context)
    if data == "a:chadd":
        lim = admin_limits(uid); chs = list_channels(uid)
        if lim["max_channels"] is not None and len(chs) >= lim["max_channels"]:
            return await popup(update, context, tr(lang, "limit_channels", n=lim["max_channels"]), alert=True)
        return await ask(update, context, tr(lang, "ch_add_prompt"), "ch_add", "a:home")
    if data.startswith("a:ch:"): return await view_channel(update, context, int(data.split(":")[2]))
    if data.startswith("a:rep:"):
        cid = int(data.split(":")[2]); text = report_text(uid, cid, lang)
        return await render(update, context, text, [[B(tr(lang, "back"), f"a:ch:{cid}")]])
    if data.startswith("a:test:"): return await run_test(update, context, int(data.split(":")[2]))
    if data == "a:plan": return await view_my_plan(update, context)
    if data.startswith("a:logs:"):
        cid = int(data.split(":")[2])
        return await view_logs(update, context, admin_id=uid, back=f"a:ch:{cid}", refresh=f"a:logs:{cid}")
    if data == "a:logs": return await view_logs(update, context, admin_id=uid, back="a:home", refresh="a:logs")

    # Lock code
    if data.startswith("a:lock:"): return await view_lock(update, context, int(data.split(":")[2]))
    if data.startswith("a:lockre:"):
        cid = int(data.split(":")[2]); regen_lock(cid); await popup(update, context, tr(lang, "lock_regen_ok"))
        return await view_lock(update, context, cid)

    # Channel delete & toggles
    if data.startswith("a:chdel:"):
        cid = int(data.split(":")[2]); ch = get_channel(cid)
        if not ch or ch["admin_id"] != uid: return await view_admin_home(update, context)
        return await render(update, context, tr(lang, "ch_del_q", title=esc(ch["title"])),
                            [[B(tr(lang, "yes"), f"a:chdelok:{cid}"), B(tr(lang, "no"), f"a:ch:{cid}")]])
    if data.startswith("a:chdelok:"):
        cid = int(data.split(":")[2]); delete_channel(cid); await popup(update, context, tr(lang, "ch_deleted"))
        return await view_admin_home(update, context)
    if data.startswith("a:tog:"):
        parts = data.split(":"); cid = int(parts[2]); field = parts[3]
        val = toggle_setting(cid, field)
        await popup(update, context, tr(lang, f"tog_{field}" if f"tog_{field}" in TXT else ("on" if val else "off")))
        return await view_channel(update, context, cid) if field == "enabled" else await view_content(update, context, cid)

    # Content & subviews
    if data.startswith("a:con:"): return await view_content(update, context, int(data.split(":")[2]))
    if data.startswith("a:set:"):
        parts = data.split(":"); cid = int(parts[2]); field = parts[3]
        return await ask(update, context, FIELD_LABEL.get(field, (field, field))[1 if lang == "en" else 0],
                         "set", f"a:con:{cid}" if field not in SCHED_FIELDS else f"a:sch:{cid}", cid=cid, field=field)
    if data.startswith("a:cat:"): return await view_cats(update, context, int(data.split(":")[2]))
    if data.startswith("a:catv:"):
        parts = data.split(":"); return await view_cat(update, context, int(parts[2]), int(parts[3]))
    if data.startswith("a:cata:"):
        return await wiz_start(update, context, "cat_add", f"a:cat:{data.split(':')[2]}", cid=int(data.split(":")[2]))
    if data.startswith("a:catd:"):
        parts = data.split(":"); cid = int(parts[2]); i = int(parts[3])
        s = get_settings(cid); cats = list(s["categories"])
        if len(cats) <= 1: await popup(update, context, tr(lang, "cat_min"), alert=True); return await view_cats(update, context, cid)
        cats.pop(i); update_settings(cid, categories=cats); await popup(update, context, tr(lang, "deleted"))
        return await view_cats(update, context, cid)
    if data.startswith("a:cats:"):
        parts = data.split(":"); cid = int(parts[2]); i = int(parts[3])
        return await ask(update, context, tr(lang, "cat_style_prompt"), "cat_style", f"a:catv:{cid}:{i}", cid=cid, i=i)

    # Criteria
    if data.startswith("a:cri:"): return await view_crits(update, context, int(data.split(":")[2]))
    if data.startswith("a:criv:"):
        parts = data.split(":"); return await view_crit(update, context, int(parts[2]), int(parts[3]))
    if data.startswith("a:cria:"):
        return await wiz_start(update, context, "crit_add", f"a:cri:{data.split(':')[2]}", cid=int(data.split(":")[2]))
    if data.startswith("a:crid:"):
        parts = data.split(":"); cid = int(parts[2]); i = int(parts[3])
        s = get_settings(cid); crits = list(s["criteria"])
        if len(crits) <= 1: await popup(update, context, tr(lang, "crit_min"), alert=True); return await view_crits(update, context, cid)
        crits.pop(i); update_settings(cid, criteria=crits); await popup(update, context, tr(lang, "deleted"))
        return await view_crits(update, context, cid)
    if data.startswith("a:criw:"):
        parts = data.split(":"); cid = int(parts[2]); i = int(parts[3])
        return await ask(update, context, tr(lang, "crit_w_prompt"), "crit_weight", f"a:criv:{cid}:{i}", cid=cid, i=i)

    # Schedule & quiet & tz
    if data.startswith("a:sch:"): return await view_sched(update, context, int(data.split(":")[2]))
    if data.startswith("a:mode:"):
        cid = int(data.split(":")[2]); s = get_settings(cid); new_mode = "review" if s["mode"] == "auto" else "auto"
        update_settings(cid, mode=new_mode); await popup(update, context, tr(lang, f"mode_set_{new_mode}"))
        return await view_sched(update, context, cid)
    if data.startswith("a:quiet:"): return await view_quiet(update, context, int(data.split(":")[2]))
    if data.startswith("a:qoff:"):
        cid = int(data.split(":")[2]); update_settings(cid, quiet_start=None, quiet_end=None)
        await popup(update, context, tr(lang, "quiet_cleared")); return await view_sched(update, context, cid)
    if data.startswith("a:qs:"):
        parts = data.split(":"); cid = int(parts[2]); sh = int(parts[3])
        context.user_data["quiet_start"] = sh
        return await render(update, context, tr(lang, "quiet_pick_end", h=sh),
                            hour_grid(f"a:qe:{cid}") + [[B(tr(lang, "back"), f"a:quiet:{cid}")]])
    if data.startswith("a:qe:"):
        parts = data.split(":"); cid = int(parts[2]); eh = int(parts[3]); sh = context.user_data.get("quiet_start", 0)
        update_settings(cid, quiet_start=sh, quiet_end=eh)
        await popup(update, context, tr(lang, "quiet_set", a=sh, b=eh)); return await view_sched(update, context, cid)
    if data.startswith("a:tz:"): return await view_tz(update, context, int(data.split(":")[2]))
    if data.startswith("a:tzs:"):
        parts = data.split(":"); cid = int(parts[2]); idx = int(parts[3]); _, off = TZ_ZONES[idx]
        update_settings(cid, utc_offset=off); await popup(update, context, tr(lang, "tz_set", city=tz_city(off, lang), tz=off_label(off), loc=local_clock(off)))
        return await view_sched(update, context, cid)

    # Queue & articles
    if data.startswith("a:que:"): return await view_queue(update, context, int(data.split(":")[2]), "ready")
    if data.startswith("a:rej:"): return await view_queue(update, context, int(data.split(":")[2]), "rejected")
    if data.startswith("a:art:"): return await view_article(update, context, int(data.split(":")[2]))
    if data.startswith("a:arte:"):
        aid = int(data.split(":")[2]); return await ask(update, context, tr(lang, "art_edit_prompt"), "art_edit", f"a:art:{aid}", aid=aid)
    if data.startswith("a:artd:"):
        aid = int(data.split(":")[2]); a = get_article(aid); cid = a["channel_id"] if a else 0
        article_delete(aid); await popup(update, context, tr(lang, "deleted"))
        return await view_queue(update, context, cid, "ready")
    if data.startswith("a:artr:"):
        aid = int(data.split(":")[2]); article_update(aid, status="ready", reason=""); await popup(update, context, tr(lang, "art_moved"))
        return await view_article(update, context, aid)
    if data.startswith("a:artf:"):
        aid = int(data.split(":")[2]); a = get_article(aid)
        if not a or not a["full_html"]: return await popup(update, context, tr(lang, "empty"))
        body, _ = fit_html(a["full_html"], 3800)
        return await render(update, context, tr(lang, "full_head") + body, [[B(tr(lang, "back"), f"a:art:{aid}")]])
    if data.startswith("a:pub:"):
        aid = int(data.split(":")[2]); a = get_article(aid)
        if not a: return await view_admin_home(update, context)
        await popup(update, context, tr(lang, "publishing"))
        ok, out = await publish_article(context.bot, aid, count_usage=True)
        if ok: await popup(update, context, tr(lang, "published_ok"), alert=True); return await view_article(update, context, aid)
        await popup(update, context, tr(lang, "pub_failed", e=_pub_err(out, lang)), alert=True)
        return await view_article(update, context, aid)

    # Sources
    if data.startswith("a:src:"): return await view_sources(update, context, int(data.split(":")[2]))
    if data.startswith("a:srca:"):
        cid = int(data.split(":")[2]); lim = admin_limits(uid); cur = count_sources(uid)
        if lim["max_sources"] is not None and cur >= lim["max_sources"]:
            return await popup(update, context, tr(lang, "limit_sources", n=lim["max_sources"]), alert=True)
        return await ask(update, context, tr(lang, "src_add_prompt"), "src_add", f"a:src:{cid}", cid=cid)
    if data.startswith("a:srcv:"): return await view_source(update, context, int(data.split(":")[2]))
    if data.startswith("a:srct:"):
        sid = int(data.split(":")[2]); s = get_source(sid)
        if s:
            act = 0 if s["active"] else 1; q("UPDATE sources SET active=? WHERE id=?", (act, sid), commit=True)
            await popup(update, context, tr(lang, "src_on" if act else "src_off"))
        return await view_source(update, context, sid)
    if data.startswith("a:srctb:"):
        sid = int(data.split(":")[2]); s = get_source(sid)
        if s:
            cur = s["bot_active"] if s["bot_active"] is not None else 1; new_v = 0 if cur else 1
            q("UPDATE sources SET bot_active=? WHERE id=?", (new_v, sid), commit=True)
            await popup(update, context, tr(lang, "src_bot_on" if new_v else "src_bot_off"))
        return await view_source(update, context, sid)
    if data.startswith("a:srcapi:"):
        sid = int(data.split(":")[2]); return await ask(update, context, tr(lang, "src_api_url"), "src_api_url", f"a:srcv:{sid}", sid=sid)
    if data.startswith("a:srcapix:"):
        sid = int(data.split(":")[2]); q("UPDATE sources SET api_url=NULL, api_key=NULL WHERE id=?", (sid,), commit=True)
        await popup(update, context, tr(lang, "src_api_del")); return await view_source(update, context, sid)
    if data.startswith("a:srcd:"):
        sid = int(data.split(":")[2]); s = get_source(sid); cid = s["channel_id"] if s else 0
        delete_source(sid); await popup(update, context, tr(lang, "src_deleted"))
        return await view_sources(update, context, cid)
    if data.startswith("a:srcr:"):
        sid = int(data.split(":")[2]); s = get_source(sid)
        if s:
            try: items, _, m = await discover_source(s, use_cache=False); await popup(update, context, f"✅ {len(items)} items [{m}]", alert=True)
            except Exception as e: await popup(update, context, f"❌ {e}", alert=True)
        return await view_source(update, context, sid)

    # Super admin callbacks
    if is_super(uid):
        if data == "s:home": return await view_super_home(update, context)
        if data == "s:rep":
            text = report_text(None, None, "fa")
            return await render(update, context, text, [[B("🔙 بازگشت", "s:home")]])
        if data.startswith("s:users:"): return await view_super_users(update, context, int(data.split(":")[2]))
        if data.startswith("s:u:"): return await view_super_user(update, context, int(data.split(":")[2]))
        if data.startswith("s:uban:"):
            target = int(data.split(":")[2]); u = get_user(target)
            if u: q("UPDATE users SET banned=? WHERE id=?", (0 if u["banned"] else 1, target), commit=True)
            return await view_super_user(update, context, target)
        if data.startswith("s:urole:"):
            target = int(data.split(":")[2]); u = get_user(target)
            if u: q("UPDATE users SET role=? WHERE id=?", ("super" if u["role"] != "super" else "admin", target), commit=True)
            return await view_super_user(update, context, target)
        if data.startswith("s:uclrp:"):
            target = int(data.split(":")[2]); q("UPDATE users SET plan_id=NULL, plan_expires=NULL, next_plan_id=NULL WHERE id=?", (target,), commit=True)
            return await view_super_user(update, context, target)
        if data.startswith("s:usetp:"):
            target = int(data.split(":")[2]); plans = list_plans()
            kb = [[B(p["name"], f"s:usetpok:{target}:{p['id']}")] for p in plans] + [[B("🔙 بازگشت", f"s:u:{target}")]]
            return await render(update, context, "پلن مورد نظر را انتخاب کنید:", kb)
        if data.startswith("s:usetpok:"):
            parts = data.split(":"); target = int(parts[2]); pid = int(parts[3])
            assign_plan(target, pid); await popup(update, context, "✅ پلن اعمال شد")
            return await view_super_user(update, context, target)
        if data == "s:plans": return await view_super_plans(update, context)
        if data.startswith("s:plan:"): return await view_super_plan(update, context, int(data.split(":")[2]))
        if data == "s:plana": return await wiz_start(update, context, "plan_new", "s:plans")
        if data.startswith("s:pldel:"):
            pid = int(data.split(":")[2]); q("DELETE FROM plans WHERE id=?", (pid,), commit=True)
            await popup(update, context, "🗑 پلن حذف شد"); return await view_super_plans(update, context)
        if data.startswith("s:plpr:"):
            pid = int(data.split(":")[2]); return await ask(update, context, "قیمت جدید پلن:", "pl_price", f"s:plan:{pid}", pid=pid)
        if data.startswith("s:pldy:"):
            pid = int(data.split(":")[2]); return await ask(update, context, "تعداد روزهای پلن:", "pl_days", f"s:plan:{pid}", pid=pid)
        if data == "s:models": return await view_super_models(update, context)
        if data.startswith("s:mview:"): return await view_super_model(update, context, int(data.split(":")[2]))
        if data == "s:madd": return await wiz_start(update, context, "model_add", "s:models")
        if data.startswith("s:mtog:"):
            mid = int(data.split(":")[2]); m = get_model(mid)
            if m: q("UPDATE ai_models SET active=? WHERE id=?", (0 if m["active"] else 1, mid), commit=True)
            return await view_super_model(update, context, mid)
        if data.startswith("s:mdel:"):
            mid = int(data.split(":")[2]); q("DELETE FROM ai_models WHERE id=?", (mid,), commit=True)
            await popup(update, context, "🗑 مدل حذف شد"); return await view_super_models(update, context)
        if data.startswith("s:mtest:"):
            mid = int(data.split(":")[2]); m = get_model(mid)
            if m:
                ok, err = await test_model(m["base_url"], m["api_key"], m["model"])
                q("UPDATE ai_models SET status=?, last_error=?, last_check=? WHERE id=?", ("ok" if ok else "down", "" if ok else err, now_iso(), mid), commit=True)
                await popup(update, context, "✅ مدل با موفقیت تست شد" if ok else f"❌ خطا: {err}", alert=True)
            return await view_super_model(update, context, mid)
        if data.startswith("s:mup:"):
            mid = int(data.split(":")[2]); m = get_model(mid)
            if m and m["priority"] > 1:
                other = q("SELECT * FROM ai_models WHERE priority=?", (m["priority"] - 1,), one=True)
                if other: q("UPDATE ai_models SET priority=? WHERE id=?", (m["priority"], other["id"]), commit=True)
                q("UPDATE ai_models SET priority=? WHERE id=?", (m["priority"] - 1, mid), commit=True)
            return await view_super_models(update, context)
        if data.startswith("s:mdn:"):
            mid = int(data.split(":")[2]); m = get_model(mid)
            if m:
                other = q("SELECT * FROM ai_models WHERE priority=?", (m["priority"] + 1,), one=True)
                if other: q("UPDATE ai_models SET priority=? WHERE id=?", (m["priority"], other["id"]), commit=True)
                q("UPDATE ai_models SET priority=? WHERE id=?", (m["priority"] + 1, mid), commit=True)
            return await view_super_models(update, context)
        if data == "s:discs": return await view_super_discs(update, context)
        if data == "s:disca": return await wiz_start(update, context, "disc_add", "s:discs")
        if data == "s:pays": return await view_super_pays(update, context)
        if data.startswith("s:payv:"): return await view_super_pay(update, context, int(data.split(":")[2]))
        if data.startswith("s:payok:"):
            pid = int(data.split(":")[2]); py = q("SELECT * FROM payments WHERE id=?", (pid,), one=True)
            if py:
                q("UPDATE payments SET status='approved' WHERE id=?", (pid,), commit=True)
                exp = assign_plan(py["user_id"], py["plan_id"])
                p = get_plan(py["plan_id"]); u = get_user(py["user_id"]); lang = u["lang"] or "fa"
                d = fmt_date(exp, admin_offset(py["user_id"]))
                await notify_user_fn(py["user_id"], tr(lang, "pay_approved", name=esc(plan_txt(p, "name", lang)), when=tr(lang, "pay_when_now", d=d)))
                await popup(update, context, "✅ پرداخت تأیید و پلن فعال شد")
            return await view_super_pays(update, context)
        if data.startswith("s:payno:"):
            pid = int(data.split(":")[2]); py = q("SELECT * FROM payments WHERE id=?", (pid,), one=True)
            if py:
                q("UPDATE payments SET status='rejected' WHERE id=?", (pid,), commit=True)
                u = get_user(py["user_id"]); lang = u["lang"] or "fa"
                await notify_user_fn(py["user_id"], tr(lang, "pay_rejected"))
                await popup(update, context, "❌ پرداخت رد شد")
            return await view_super_pays(update, context)
        if data == "s:texts": return await view_super_texts(update, context)
        if data.startswith("s:tedit:"):
            key = data.split(":")[2]; return await ask(update, context, f"متن جدید برای {key}:", "text_edit", "s:texts", text_key=key)
        if data == "s:bcast": return await ask(update, context, "پیام همگانی را بفرستید:", "broadcast", "s:home")
        if data.startswith("s:logs:"):
            lvl = data.split(":")[2]; lvl = None if lvl == "all" else lvl
            return await view_logs(update, context, admin_id=None, level=lvl, back="s:home")
        if data == "s:togauto":
            cur = gget("automation_enabled", True); gset("automation_enabled", not cur)
            await popup(update, context, "🟢 اتوماسیون فعال شد" if not cur else "🔴 اتوماسیون متوقف شد")
            return await view_super_home(update, context)

    if data == "c:cancel":
        context.user_data.pop("await", None)
        await popup(update, context, tr(lang, "cancelled"))
        return await go_home(update, context)

# ============================================================
# مدیریت پیام‌های ورودی کاربر (Message & Wizard Processing)
def forwarded_channel(msg):
    origin = getattr(msg, "forward_origin", None)
    if not origin or getattr(origin, "type", None) != "channel":
        return None
    return getattr(origin, "chat", None)

# ============================================================
# مدیریت پیام‌های ورودی کاربر (Message & Wizard Processing)
async def on_message(update, context):
    if not update.message: return
    uid = update.effective_user.id; msg = update.message; text = (msg.text or "").strip(); lang = L(update)
    user_upsert(uid, uname=update.effective_user.username, name=update.effective_user.full_name)
    if is_banned(uid): return await msg.reply_text(tr(lang, "banned"))

    st = context.user_data.get("await")
    if not st:
        # Check if user forwarded a channel post without being in await mode
        if forwarded_channel(msg):
            context.user_data["await"] = {"kind": "ch_add", "back": "a:home"}
            st = context.user_data["await"]
        else:
            return

    kind = st.get("kind")

    # Wizard handling
    if kind == "wiz":
        wiz = st["wiz"]; step = st["step"]; steps = WIZ[wiz]; key, _, ktype = steps[step]
        val = text
        if ktype == "int":
            try: val = to_int(text)
            except Exception: return await msg.reply_text(tr(lang, "need_int"))
        st["data"][key] = val; st["step"] += 1
        if st["step"] < len(steps): return await wiz_prompt(update, context)

        # Wizard complete
        context.user_data.pop("await", None); d = st["data"]
        if wiz == "cat_add":
            cid = d["cid"]; s = get_settings(cid); cats = list(s["categories"])
            cats.append({"name": str(d["name"]), "emoji": str(d["emoji"]), "style": str(d["style"])})
            update_settings(cid, categories=cats); await popup(update, context, tr(lang, "cat_added"))
            return await view_cats(update, context, cid)
        elif wiz == "crit_add":
            cid = d["cid"]; s = get_settings(cid); crits = list(s["criteria"])
            crits.append({"name": str(d["name"]), "weight": int(d["weight"])})
            update_settings(cid, criteria=crits); await popup(update, context, tr(lang, "crit_added"))
            return await view_crits(update, context, cid)
        elif wiz == "plan_new":
            q("INSERT INTO plans(name,name_en,days,daily_posts,max_sources,max_channels,daily_tests,price,price_en,description,description_en,is_free) VALUES(?,?,?,?,?,?,?,?,?,?,?,0)",
              (d["name"], d["name_en"], d["days"], d["daily_posts"], d["max_sources"], d["max_channels"], d["daily_tests"], d["price"], d["price_en"], d["description"], d["description_en"]), commit=True)
            await popup(update, context, "✅ پلن جدید اضافه شد"); return await view_super_plans(update, context)
        elif wiz == "model_add":
            prio = (q("SELECT MAX(priority) m FROM ai_models", one=True)["m"] or 0) + 1
            q("INSERT INTO ai_models(base_url,api_key,model,active,priority,status) VALUES(?,?,?,1,?,'ok')", (d["base_url"], d["api_key"], d["model"], prio), commit=True)
            await popup(update, context, "✅ مدل اضافه شد"); return await view_super_models(update, context)
        elif wiz == "disc_add":
            exp_val = str(d["expires"]).strip()
            if exp_val.isdigit(): exp_date = (now_utc() + timedelta(days=int(exp_val))).isoformat()
            else: exp_date = exp_val + "T23:59:59Z"
            q("INSERT INTO discounts(code,percent,expires_at,max_uses,used_count) VALUES(?,?,?,?,0)", (d["code"].upper(), d["percent"], exp_date, d["max_uses"]), commit=True)
            await popup(update, context, "✅ کد تخفیف اضافه شد"); return await view_super_discs(update, context)

    # Receipt submission
    if kind == "receipt":
        pid = st["pid"]; file_id = msg.photo[-1].file_id if msg.photo else None
        q("INSERT INTO payments(user_id,plan_id,receipt_file_id,receipt_text,discount_code,final_price,status,created_at) VALUES(?,?,?,?,?,?, 'pending', ?)",
          (uid, pid, file_id, text, st.get("disc"), st.get("final"), now_iso()), commit=True)
        context.user_data.pop("await", None)
        await notify_supers(f"🛎 <b>رسید پرداخت جدید</b> از {uname(get_user(uid))} برای پلن #{pid}")
        return await view_receipt_ok(update, context)

    # Add source
    if kind == "src_add":
        cid = st["cid"]; url = text.strip()
        if not (url.startswith("http://") or url.startswith("https://")): return await msg.reply_text(tr(lang, "src_bad"))
        if q("SELECT id FROM sources WHERE channel_id=? AND url=?", (cid, url), one=True): return await msg.reply_text(tr(lang, "src_dup"))
        m_check = await msg.reply_text(tr(lang, "src_checking"))
        try:
            items, _, method = await discover_source({"url": url, "feed_url": None, "api_url": None, "api_key": None}, use_cache=False)
            sid = q("INSERT INTO sources(admin_id,channel_id,url,feed_url,active,bot_active,last_fetch,found_total,fail_count) VALUES(?,?,?,?,1,1,?,0,0)",
                    (uid, cid, url, url if method.startswith("rss") else None, now_iso()), commit=True)
            context.user_data.pop("await", None)
            try: await m_check.delete()
            except Exception: pass
            await popup(update, context, tr(lang, "src_added", n=len(items), m=method))
            return await view_sources(update, context, cid)
        except Exception as e:
            try: await m_check.delete()
            except Exception: pass
            err_str = str(e)
            if "403" in err_str: return await msg.reply_text(tr(lang, "src_403"))
            return await msg.reply_text(tr(lang, "src_dead"))

    # Source API
    if kind == "src_api_url":
        st["api_url"] = text.strip(); st["kind"] = "src_api_key"
        return await msg.reply_text(tr(lang, "src_api_key"), parse_mode=HTML)
    if kind == "src_api_key":
        sid = st["sid"]; a_key = None if text.strip() in ("-", "") else text.strip()
        q("UPDATE sources SET api_url=?, api_key=? WHERE id=?", (st["api_url"], a_key, sid), commit=True)
        context.user_data.pop("await", None); await popup(update, context, tr(lang, "src_api_ok", n=0))
        return await view_source(update, context, sid)

    # Channel add
    if kind == "ch_add":
        chat_id, ch_title, ch_user = None, None, None
        ch = forwarded_channel(msg)
        if ch:
            chat_id = ch.id; ch_title = ch.title; ch_user = ch.username
        elif text:
            target = text.strip()
            if not (target.startswith("@") or target.startswith("-100")): target = "@" + target
            try:
                c = await context.bot.get_chat(target)
                if c.type == "channel": chat_id = c.id; ch_title = c.title; ch_user = c.username
            except Exception as e: return await msg.reply_text(tr(lang, "ch_no_access", e=e))
        if not chat_id: return await msg.reply_text(tr(lang, "ch_need_fwd"))
        if not await bot_can_post(context.bot, chat_id): return await msg.reply_text(tr(lang, "ch_bot_not_admin"))
        if not await user_is_admin(context.bot, chat_id, uid): return await msg.reply_text(tr(lang, "ch_user_not_admin"))

        existing = q("SELECT * FROM channels WHERE chat_id=?", (chat_id,), one=True)
        if existing:
            if existing["admin_id"] == uid: return await msg.reply_text(tr(lang, "ch_exists_mine"))
            # Locked channel transfer
            st["kind"] = "ch_lock_code"; st["target_cid"] = existing["id"]; st["target_title"] = ch_title or existing["title"]
            return await msg.reply_text(tr(lang, "ch_locked"), parse_mode=HTML)

        cid = q("INSERT INTO channels(admin_id,chat_id,title,username,created_at,lock_code) VALUES(?,?,?,?,?,?)",
                (uid, chat_id, ch_title or "Channel", ch_user, now_iso(), gen_lock_code()), commit=True)
        init_settings(cid, lang)
        context.user_data.pop("await", None); await popup(update, context, tr(lang, "ch_added", title=ch_title or "Channel"))
        return await view_channel(update, context, cid)

    # Channel lock code verification for transfer
    if kind == "ch_lock_code":
        code = text.strip(); target_cid = st["target_cid"]
        ch = q("SELECT * FROM channels WHERE id=?", (target_cid,), one=True)
        if not ch or ch["lock_code"] != code:
            if ch: await notify_user_fn(ch["admin_id"], tr(user_lang(ch["admin_id"]) or "fa", "ch_owner_alert", who=uname(get_user(uid)), title=ch["title"]))
            return await msg.reply_text(tr(lang, "ch_lock_bad"))
        # Successful transfer
        old_admin = ch["admin_id"]
        q("UPDATE channels SET admin_id=?, lock_code=? WHERE id=?", (uid, gen_lock_code(), target_cid), commit=True)
        init_settings(target_cid, lang)
        await notify_user_fn(old_admin, tr(user_lang(old_admin) or "fa", "ch_owner_moved", who=uname(get_user(uid)), title=ch["title"]))
        context.user_data.pop("await", None); await popup(update, context, tr(lang, "ch_lock_ok", title=ch["title"]))
        return await view_channel(update, context, target_cid)

    # Settings field update
    if kind == "set":
        cid = st["cid"]; field = st["field"]; val = text
        if field in INT_FIELDS:
            lo, hi = INT_FIELDS[field]
            try:
                n = to_int(text)
                if not (lo <= n <= hi): return await msg.reply_text(tr(lang, "range", lo=lo, hi=hi))
                val = n
            except Exception: return await msg.reply_text(tr(lang, "need_int"))
        update_settings(cid, **{field: val})
        context.user_data.pop("await", None); await popup(update, context, tr(lang, "saved"))
        return await view_content(update, context, cid) if field not in SCHED_FIELDS else await view_sched(update, context, cid)

    # Category style update
    if kind == "cat_style":
        cid = st["cid"]; i = st["i"]; s = get_settings(cid); cats = list(s["categories"])
        if i < len(cats):
            cats[i]["style"] = text; update_settings(cid, categories=cats)
            await popup(update, context, tr(lang, "cat_updated"))
        context.user_data.pop("await", None); return await view_cat(update, context, cid, i)

    # Criteria weight update
    if kind == "crit_weight":
        cid = st["cid"]; i = st["i"]
        try: w = to_int(text)
        except Exception: return await msg.reply_text(tr(lang, "need_int"))
        s = get_settings(cid); crits = list(s["criteria"])
        if i < len(crits):
            crits[i]["weight"] = w; update_settings(cid, criteria=crits)
            await popup(update, context, tr(lang, "crit_updated"))
        context.user_data.pop("await", None); return await view_crit(update, context, cid, i)

    # Article edit
    if kind == "art_edit":
        aid = st["aid"]; article_update(aid, post_html=text)
        context.user_data.pop("await", None); await popup(update, context, tr(lang, "art_updated"))
        return await view_article(update, context, aid)

    # Discount apply
    if kind == "disc":
        code = text.strip().upper(); d, why = disc_valid(code)
        if not d: return await msg.reply_text(tr(lang, "disc_expired" if why == "expired" else "disc_exhausted" if why == "exhausted" else "disc_bad"))
        pid = context.user_data.get("disc_pid")
        if "disc" not in context.user_data: context.user_data["disc"] = {}
        context.user_data["disc"][str(pid)] = code; context.user_data.pop("await", None)
        await popup(update, context, tr(lang, "disc_ok", p=d["percent"]))
        return await view_plan(update, context, pid)

    # Super admin text edits
    if kind == "text_edit":
        key = st["text_key"]; gset(f"text_{key}_{lang}", text)
        context.user_data.pop("await", None); await msg.reply_text("✅ متن با موفقیت بروزرسانی شد.")
        return await view_super_texts(update, context)

    # Super admin broadcast
    if kind == "broadcast":
        context.user_data.pop("await", None); users = list_users(limit=1000)
        await msg.reply_text(f"📢 ارسال همگانی به {len(users)} کاربر شروع شد...")
        sent, failed = 0, 0
        for u in users:
            try:
                await context.bot.send_message(u["id"], text, parse_mode=HTML)
                sent += 1; await asyncio.sleep(0.05)
            except Exception: failed += 1
        return await msg.reply_text(f"✅ ارسال به اتمام رسید.\nارسال شد: {sent} · ناموفق: {failed}")

# ============================================================
# دستورات بات تلگرام (Bot Commands)
async def cmd_start(update, context):
    uid = update.effective_user.id; args = context.args or []
    context.user_data.pop("panel", None)
    context.user_data.pop("await", None)
    user_upsert(uid, uname=update.effective_user.username, name=update.effective_user.full_name)
    if is_banned(uid): return await update.message.reply_text(tr("fa", "banned"))
    if args and args[0].startswith("dl_"):
        key = args[0][3:]; data = await load_deeplink(key)
        if data and isinstance(data, dict) and data.get("full"):
            body, _ = fit_html(data["full"], 3800)
            return await update.message.reply_text(f"📖 <b>نسخه‌ی کامل مقاله</b>\n\n{body}", parse_mode=HTML, disable_web_page_preview=True)
        elif data and isinstance(data, str):
            body, _ = fit_html(data, 3800)
            return await update.message.reply_text(f"📖 <b>نسخه‌ی کامل مقاله</b>\n\n{body}", parse_mode=HTML, disable_web_page_preview=True)
    await go_home(update, context)

async def cmd_create(update, context):
    uid = update.effective_user.id
    if not can_admin(uid): return await update.message.reply_text(tr(L(update), "no_admin"))
    await view_admin_home(update, context)

async def cmd_help(update, context):
    lang = L(update)
    h_fa = "💡 <b>راهنمای ربات خبرنگار هوشمند</b>\n\n/start - شروع و انتخاب زبان\n/create - ورود به پنل مدیریت کانال‌ها\n/report - گزارش آماری کانال\n/logs - لاگ عملکردهای اخیر\n/man - ارتباط با پشتیبانی\n/cancel - انصراف از عملیات جاری"
    h_en = "💡 <b>News Bot Help</b>\n\n/start - Start & Language selection\n/create - Channel Management Panel\n/report - Channel stats & report\n/logs - Recent activity logs\n/man - Contact support\n/cancel - Cancel current operation"
    await update.message.reply_text(h_fa if lang == "fa" else h_en, parse_mode=HTML)

async def cmd_man(update, context):
    lang = L(update)
    sup_text = gtext("support", lang) or ("📞 جهت ارتباط با پشتیبانی، لطفاً پیام خود را برای @Admin ارسال کنید." if lang == "fa" else "📞 To contact support, please message @Admin.")
    await update.message.reply_text(sup_text, parse_mode=HTML)

async def cmd_report(update, context):
    uid = update.effective_user.id; lang = L(update)
    if is_super(uid): return await update.message.reply_text(report_text(None, None, lang), parse_mode=HTML)
    chs = list_channels(uid)
    if not chs: return await update.message.reply_text(tr(lang, "no_channels"))
    await update.message.reply_text(report_text(uid, chs[0]["id"], lang), parse_mode=HTML)

async def cmd_logs(update, context):
    uid = update.effective_user.id
    await view_logs(update, context, admin_id=uid if not is_super(uid) else None)

async def cmd_cancel(update, context):
    context.user_data.pop("await", None)
    await update.message.reply_text(tr(L(update), "cancelled"))
    await go_home(update, context)

# ============================================================
# حلقه‌ی زمان‌بندی و راه‌اندازی اصلی (Scheduler & Main Entrypoint)
async def scheduler_loop(app):
    log.info("Scheduler loop started.")
    while True:
        try: await scheduler_tick(app.bot)
        except asyncio.CancelledError: break
        except Exception as e: log.error(f"Scheduler tick unhandled error: {e}")
        await asyncio.sleep(TICK_SECONDS)

def main():
    global APP
    init_db()
    if not BOT_TOKEN:
        log.error("BOT_TOKEN is not set! Please set BOT_TOKEN in environment variables.")
        return

    APP = Application.builder().token(BOT_TOKEN).build()

    # Commands
    APP.add_handler(CommandHandler("start", cmd_start))
    APP.add_handler(CommandHandler("create", cmd_create))
    APP.add_handler(CommandHandler("help", cmd_help))
    APP.add_handler(CommandHandler("man", cmd_man))
    APP.add_handler(CommandHandler("report", cmd_report))
    APP.add_handler(CommandHandler("logs", cmd_logs))
    APP.add_handler(CommandHandler("cancel", cmd_cancel))

    # Callbacks and Messages
    APP.add_handler(CallbackQueryHandler(on_callback))
    APP.add_handler(MessageHandler(filters.ALL & ~filters.COMMAND, on_message))

    log.info("Starting Telegram Bot application...")

    async def post_init(application):
        asyncio.create_task(scheduler_loop(application))

    APP.post_init = post_init
    APP.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
