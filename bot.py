# -*- coding: utf-8 -*-
""" 
NewsBot v3 — یک‌فایل کامل: هسته‌ی داده، موتور محتوا، رابط کاربری، پنل مدیر کلان
نیازمندی‌ها: python-telegram-bot[job-queue]>=21, httpx, feedparser, trafilatura, beautifulsoup4, lxml
"""
import os, re, json, html, time, random, asyncio, logging, sqlite3, hashlib, secrets, tempfile, threading, ipaddress, socket
from datetime import datetime, timedelta, timezone
from contextvars import ContextVar
from dataclasses import dataclass, field
from types import SimpleNamespace
from urllib.parse import urljoin, urlparse
import httpx, feedparser, trafilatura
from bs4 import BeautifulSoup
#  ============================================================
# تنظیمات محیطی
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
SUPER_ADMIN_IDS = {int(x) for x in os.getenv("SUPER_ADMIN_IDS", "").split(",") if x.strip().isdigit() and int(x) > 0}
DB_FILE = os.getenv("DB_FILE", "newsbot.db")
DATA_TTL_HOURS = int(os.getenv("DATA_TTL_HOURS", "24"))
MAX_MEDIA_MB = int(os.getenv("MAX_MEDIA_MB", "50"))
MAX_MEDIA_BYTES = MAX_MEDIA_MB * 1024 * 1024
MAX_PAGE_BYTES = int(os.getenv("MAX_PAGE_MB", "8")) * 1024 * 1024   # سقف حجم صفحه/فید دانلودی (جلوگیری از پرشدن حافظه)
MAX_ARTICLE_CHARS = int(os.getenv("MAX_ARTICLE_CHARS", "28000"))
MAX_ARTICLE_PAGES = int(os.getenv("MAX_ARTICLE_PAGES", "3"))
AI_INPUT_TEXT_CHARS = int(os.getenv("AI_INPUT_TEXT_CHARS", "8000"))  # limit on article text sent to the model
CF_ACCOUNT_ID = os.getenv("CF_ACCOUNT_ID", "")
CF_KV_NAMESPACE_ID = os.getenv("CF_KV_NAMESPACE_ID", "")
CF_API_TOKEN = os.getenv("CF_API_TOKEN", "")
CF_ENABLED = bool(CF_ACCOUNT_ID and CF_KV_NAMESPACE_ID and CF_API_TOKEN)
DEFAULT_UTC_OFFSET = float(os.getenv("DEFAULT_UTC_OFFSET", "3.5"))   # تهران
BOT_USERNAME = ""
NOTIFY_SUPER = None          # async fn(text, kb=None)   — پایین‌تر در لایه‌ی پشتیبانی ست می‌شود
NOTIFY_USER = None           # async fn(uid, text, kb=None)
SCHED_NOTIF_FAILURES = False # when True, notify_user() re-raises send failures so _plan_notifications releases remind_key
UTC = timezone.utc
CAPTION_LIMIT, MSG_LIMIT = 1024, 4096
SOURCE_COOLDOWN_MIN = 10     # حداقل فاصله‌ی دو بررسی یک منبع در حالت خودکار
MODEL_PROBE_MIN = 10
MIN_INTERVAL = 30            # حداقل فاصله‌ی چرخه (دقیقه)
MAX_LOOKBACK = 48            # حداکثر بازه‌ی مقالات (ساعت)
MAX_PPC = 5                  # حداکثر پست در هر چرخه
POST_LIMIT_DEFAULT = 700     # سقف کاراکتر پست کانال (پیش‌فرض)؛ بیشتر از آن → «ادامه در ربات»
BOT_FULL_MAX = 2500          # سقف کاراکتر محتوای کامل داخل ربات («ادامه در ربات»)
LANGS = ("fa", "en")
# ---- محافظت در برابر فشار (قابل تنظیم با متغیر محیطی)
AI_CONCURRENCY = int(os.getenv("AI_CONCURRENCY", "3"))          # درخواست هم‌زمان به مدل‌ها
FETCH_CONCURRENCY = int(os.getenv("FETCH_CONCURRENCY", "8"))    # دانلود هم‌زمان صفحات/فیدها
CYCLE_CONCURRENCY = int(os.getenv("CYCLE_CONCURRENCY", "2"))    # چرخه‌ی هم‌زمان کانال‌ها
MAX_CYCLES_PER_TICK = int(os.getenv("MAX_CYCLES_PER_TICK", "4"))  # حداکثر چرخه‌ی زمان‌بندی‌شده در هر تیک
TICK_SECONDS = int(os.getenv("TICK_SECONDS", "120"))            # فاصله‌ی تیک زمان‌بند
TEST_COOLDOWN_SEC = int(os.getenv("TEST_COOLDOWN_SEC", "120"))  # فاصله‌ی دو تست فوری روی یک کانال
CB_RATE = float(os.getenv("CB_RATE", "0.6"))                    # حداقل فاصله‌ی دو کلیک یک کاربر (ثانیه)
logging.basicConfig(format="%(asctime)s | %(levelname)s | %(message)s", level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("core")
# ============================================================
# ابزار زمان (فقط بر پایه‌ی آفست UTC)
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
    """«30» → ۳۰ روز بعد · «2025-12-31» → پایان همان روز (UTC). خروجی: iso یا None"""
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
    """قفل هر کانال: هرگز دو چرخه (تست/خودکار/انتشار دستی) هم‌زمان روی یک کانال اجرا نمی‌شود."""
    if cid not in _ch_locks: _ch_locks[cid] = asyncio.Lock()
    return _ch_locks[cid]
def rate_ok(key, min_gap):
    """True اگر از آخرین رخداد این کلید حداقل min_gap ثانیه گذشته باشد (و زمان را به‌روز می‌کند)."""
    t = time.time(); last = _rl.get(key, 0)
    if t - last < min_gap: return False
    _rl[key] = t
    if len(_rl) > 20000: [_rl.pop(k) for k in list(_rl)[:10000]]
    return True
def rate_free(key, min_gap):
    """فقط بررسی می‌کند و چیزی ثبت نمی‌کند (برای مواردی که محدودیت باید فقط بعد از موفقیت اعمال شود)."""
    return (time.time() - _rl.get(key, 0)) >= min_gap
def rate_mark(key):
    _rl[key] = time.time()
    if len(_rl) > 20000: [_rl.pop(k) for k in list(_rl)[:10000]]
def rate_clear(key): _rl.pop(key, None)
def rate_left(key, min_gap): return max(0, int(min_gap - (time.time() - _rl.get(key, 0))))
# ============================================================
# دیتابیس + مهاجرت خودکار
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
CREATE TABLE IF NOT EXISTS ai_models(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, kind TEXT, base_url TEXT, api_key TEXT, model TEXT, priority INTEGER DEFAULT 10, active INTEGER DEFAULT 1, status TEXT DEFAULT 'ok', fail_count INTEGER DEFAULT 0, last_error TEXT, last_ok TEXT, last_fail TEXT, ok_count INTEGER DEFAULT 0, temperature REAL DEFAULT 0.5, max_tokens INTEGER DEFAULT 2500, owner_id INTEGER);
CREATE TABLE IF NOT EXISTS deeplinks(key TEXT PRIMARY KEY, admin_id INTEGER, created_at TEXT, local_json TEXT);
CREATE TABLE IF NOT EXISTS kv_cache(key TEXT PRIMARY KEY, value TEXT, cached_at TEXT);
CREATE TABLE IF NOT EXISTS logs(id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, level TEXT, admin_id INTEGER, msg TEXT);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS support(user_id INTEGER PRIMARY KEY, open INTEGER DEFAULT 0, opened_at TEXT);
CREATE TABLE IF NOT EXISTS support_map(msg_id INTEGER PRIMARY KEY, user_id INTEGER, ts TEXT);
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
              ("pay_requests", "discount", "TEXT"), ("pay_requests", "final_price", "TEXT"),
              ("ai_models", "temperature", "REAL DEFAULT 0.5"), ("ai_models", "max_tokens", "INTEGER DEFAULT 2500"), ("ai_models", "owner_id", "INTEGER"),
              ("plans", "daily_tests", "INTEGER DEFAULT 2"), ("plans", "price_num", "REAL DEFAULT 0"), ("sources", "found_total", "INTEGER DEFAULT 0"), ("sources", "title", "TEXT DEFAULT ''")]
def db():
    global _conn
    if _conn is None:
        _conn = sqlite3.connect(DB_FILE, check_same_thread=False, timeout=15)
        _conn.row_factory = sqlite3.Row
        for pr in ("PRAGMA journal_mode=WAL", "PRAGMA synchronous=NORMAL", "PRAGMA busy_timeout=8000", "PRAGMA cache_size=-16000", "PRAGMA temp_store=MEMORY"): _conn.execute(pr)
        _conn.executescript(SCHEMA)
        for tbl, col, decl in MIGRATIONS:
            try: _conn.execute(f"ALTER TABLE {tbl} ADD COLUMN {col} {decl}")
            except sqlite3.OperationalError: pass
        _conn.commit()
    return _conn
def q(sql, params=(), one=False, commit=False):
    """قفل موقت SQLite زیر بار (چند چرخه‌ی هم‌زمان) خطا نمی‌دهد؛ چند بار کوتاه دوباره تلاش می‌شود."""
    for attempt in range(4):
        try:
            with _lock:
                cur = db().execute(sql, params)
                if commit: db().commit(); return cur.lastrowid
                return cur.fetchone() if one else cur.fetchall()
        except sqlite3.OperationalError as e:
            msg = str(e).lower()
            try: db().rollback()   # تراکنش ناتمام باز نماند؛ وگرنه تلاش دوباره روی تغییر نیمه‌کاره سوار می‌شود
            except Exception: pass
            if attempt == 3 or ("locked" not in msg and "busy" not in msg): raise   # انتظار قفل با PRAGMA busy_timeout انجام می‌شود؛ حلقه‌ی رویداد مسدود نمی‌شود
_COLS = {}
def _safe_fields(table, f):
    """در SQL پویا فقط ستون‌های واقعیِ همان جدول پذیرفته می‌شوند (نام ستون از ورودی کاربر می‌آید)."""
    if table not in _COLS: _COLS[table] = {r["name"] for r in q(f"PRAGMA table_info({table})")}
    bad = [k for k in f if k not in _COLS[table]]
    if bad: raise ValueError(f"unknown column: {bad[0]}")
    return f
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
# متن‌های سراسری دوزبانه (قابل ویرایش توسط مدیر کلان)
DEFAULT_TEXTS = {
    "welcome": {"fa": "👋 سلام {name}!\n\nاین ربات، ادمین تمام‌وقت کانال شماست: منابع را می‌خواند، بهترین مقالات را انتخاب می‌کند، با هوش مصنوعی بازنویسی می‌کند و با قالب زیبا در کانال‌تان منتشر می‌کند.\n\nیک بار تنظیم کنید؛ بقیه‌اش خودکار است.",
                "en": "👋 Hi {name}!\n\nThis bot is your channel's full-time editor: it reads your sources, picks the best articles, rewrites them with AI and publishes them beautifully formatted in your channel.\n\nSet it up once; the rest is automatic."},
    "help": {"fa": "📘 <b>راهنما</b>\n\n/create — پنل مدیریت و پلن رایگان\n/man — پشتیبانی\n/about — درباره\n/lang — زبان\n/cancel — لغو عملیات",
             "en": "📘 <b>Help</b>\n\n/create — admin panel & free plan\n/man — support\n/about — about\n/lang — language\n/cancel — cancel action"},
    "about": {"fa": "ℹ️ <b>درباره</b>\n\nربات مدیریت خودکار محتوای کانال تلگرام.", "en": "ℹ️ <b>About</b>\n\nAutomated Telegram channel content manager."},
    "pay": {"fa": "💳 <b>پرداخت پلن «{plan}»</b>\n\n💰 مبلغ: <b>{price}</b>\n\nبه شماره کارت زیر واریز کنید:\n<code>0000-0000-0000-0000</code>\nبه نام: ...\n\nسپس <b>تصویر رسید</b> را همین‌جا بفرستید.",
            "en": "💳 <b>Payment for “{plan}”</b>\n\n💰 Amount: <b>{price}</b>\n\nTransfer to:\n<code>0000-0000-0000-0000</code>\nName: ...\n\nThen send the <b>receipt image</b> right here."},
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
        # last_seen حداکثر هر ۵ دقیقه نوشته می‌شود تا فشار نوشتن پایین بماند
        ls = parse_dt(u["last_seen"])
        if not ls or (now_utc() - ls).total_seconds() > 300 or (premium is not None and int(bool(premium)) != (u["premium"] or 0)) or (username and username != u["username"]):
            q("UPDATE users SET username=?,name=?,last_seen=?,premium=?,role=CASE WHEN ?=1 THEN 'super' ELSE role END WHERE id=?",
              (username or u["username"], name or u["name"], now_iso(), (1 if premium else 0) if premium is not None else (u["premium"] or 0), 1 if is_super(uid) else 0, uid), commit=True)
        else: return u
    return get_user(uid)
def set_role(uid, role): q("UPDATE users SET role=? WHERE id=?", (role, uid), commit=True)
def role_of(uid):
    if is_super(uid): return "super"
    u = get_user(uid); return u["role"] if u else "user"
def user_lang(uid):
    u = get_user(uid); return u["lang"] if u and u["lang"] in LANGS else None
def set_lang(uid, lang): q("UPDATE users SET lang=? WHERE id=?", (lang if lang in LANGS else "fa", uid), commit=True)
def list_users(role=None, limit=200000): return q("SELECT * FROM users" + (" WHERE role=?" if role else "") + " ORDER BY created_at DESC LIMIT ?", ((role, limit) if role else (limit,)))
def list_admins(): return q("SELECT * FROM users WHERE role IN ('admin','super') AND banned=0")
def count_users(): return q("SELECT role, COUNT(*) c FROM users GROUP BY role")
# ============================================================
# پلن‌ها (زنجیره‌ای) و اشتراک
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
    return q("INSERT INTO plans(name,name_en,days,daily_posts,max_sources,max_channels,daily_tests,price,price_en,description,description_en,is_free,sort,price_num) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
             (f.get("name", "پلن"), f.get("name_en", ""), f.get("days", 30), f.get("daily_posts", 5), f.get("max_sources", 5), f.get("max_channels", 1), f.get("daily_tests", 2), f.get("price", ""), f.get("price_en", ""), f.get("description", ""), f.get("description_en", ""), f.get("is_free", 0), f.get("sort", 0), f.get("price_num", 0) or 0), commit=True)
def update_plan(pid, **f):
    for k, v in _safe_fields("plans", f).items(): q(f"UPDATE plans SET {k}=? WHERE id=?", (v, pid), commit=True)
def delete_plan(pid): q("DELETE FROM plans WHERE id=?", (pid,), commit=True)
def assign_plan(uid, pid, days=None):
    """
    زنجیره‌ای: بدون پلن فعال → همین حالا · همان پلن فعال → روزها اضافه می‌شود · پلن متفاوت فعال → «پلن بعدی» (ارتقا از رایگان فوری است).
    خروجی: (تاریخ انقضا/شروع, queued)
    """
    p = get_plan(pid)
    if not p: return None, False
    u = get_user(uid); d = int(days if days is not None else p["days"]); now = now_utc()
    cur = parse_dt(u["plan_expires"]) if u else None; active = bool(cur and cur > now and u["plan_id"])
    if active and not p["is_free"] and (get_plan(u["plan_id"]) or {"is_free": 0})["is_free"]: active = False
    if active and u["plan_id"] != pid:
        # ارتقا فوری: روزهای باقی‌ماندهٔ واقعیِ پلن فعلی به پلن جدید منتقل می‌شود و پلن جدید هم همین حالا فعال می‌شود
        carry = upgrade_carryover_days(uid)
        d_total = d + carry
        exp = now + timedelta(days=d_total)
        q("UPDATE users SET plan_id=?, plan_expires=?, next_plan_id=NULL, next_plan_days=NULL, remind_key=NULL, role=CASE WHEN role='user' THEN 'admin' ELSE role END, free_used=free_used WHERE id=?",
          (pid, exp.isoformat(), uid), commit=True)
        return exp, False
    exp = (cur if active else now) + timedelta(days=d)
    q("UPDATE users SET plan_id=?, plan_expires=?, remind_key=NULL, role=CASE WHEN role='user' THEN 'admin' ELSE role END, free_used=CASE WHEN ?=1 THEN 1 ELSE free_used END WHERE id=?", (pid, exp.isoformat(), p["is_free"], uid), commit=True)
    return exp, False
def proration_remaining_days(uid):
    """روزهای باقی‌ماندهٔ واقعیِ پلن فعلی (اعداد کسری برای کمتر از ۲۴ ساعت)؛ اگر active نباشد ۰ است."""
    u = get_user(uid)
    if not u: return 0.0
    cur = parse_dt(u["plan_expires"]) if u["plan_expires"] else None
    now = now_utc()
    if not cur or not u["plan_id"] or cur <= now: return 0.0
    return max(0.0, (cur - now).total_seconds() / 86400.0)
def proration_remaining_value(uid, new_price_num, cur_price_num, cur_days):
    """ارزش باقی‌ماندهٔ پلن فعلی بر اساس spec: current_plan_price × (remaining_time / original_plan_duration).
    اگر قیمت عددیِ پلن فعلی ثبت نشده باشد (0)، ارزش قابل‌محاسبه نیست → ۰ (بدون اعتبار؛ مبلغ کامل جدید)."""
    rem = proration_remaining_days(uid)
    if rem <= 0 or not cur_days or cur_days <= 0 or not cur_price_num:
        return 0.0
    return round(cur_price_num * (rem / cur_days), 2)
def upgrade_amount(cur_price_num, new_price_num, cur_days, uid):
    """مبلغ نهاییِ ارتقا با proration: max(0, new − remaining_value)؛ اگر قیمت جدید عددی نباشد None (حساب نمی‌شود)."""
    if not new_price_num: return None
    rv = proration_remaining_value(uid, new_price_num, cur_price_num, cur_days)
    amt = new_price_num - rv
    return round(max(0.0, amt), 2)
def upgrade_carryover_days(uid):
    """روزهای باقی‌ماندهٔ واقعیِ پلن فعلی به‌صورت کسری (float) برای transfer به پلن جدید."""
    return proration_remaining_days(uid)
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
    """کاربران غیرممنوعی که پلنِ فعالِشان (بر اساس plan_expires واقعی، نه مدت پلن) به بازه‌های هشدار رسیده است:
    ۴۸ ساعت (کلید «48h») و ۲۴ ساعت (کلید «24h»؛ کلید قدیمی «24» هم سرکوب‌کنندهٔ آن است).
    نزدیک‌ترین بازهٔ رسیده، هر تیک یک‌بار رزرو می‌شود تا اگر ربات offline بوده، صفِ هشدارِ قدیمی ارسال نشود.
    رزرو یک‌سویه است → تیک‌های مکرر و ری‌استارت تکرار نمی‌کنند؛ ارتقا/تمدید remind_key را NULL می‌کنند و هشدارهای
    انقضای تازهٔ جدید دوباره فعال می‌شوند. خروجی: [(u, key, left_h), ...]"""
    out, now = [], now_utc()
    for u in q("SELECT * FROM users WHERE plan_expires IS NOT NULL AND banned=0", ()):
        exp = parse_dt(u["plan_expires"])
        if not exp or exp <= now: continue
        left = (exp - now).total_seconds() / 3600
        rk = u["remind_key"]
        if left <= 24:
            key = "24h"
            if rk in ("24h", "24"): continue
        elif left <= 48:
            key = "48h"
            if rk == "48h": continue
        else:
            continue
        cur_k = u["remind_key"]
        # atomic claim: only if current value is NULL or one of the two keys we're replacing
        q("UPDATE users SET remind_key=? WHERE id=? AND (remind_key IN (?, ?) OR remind_key IS NULL)",
          (key, u["id"], cur_k, key), commit=True)
        out.append((u, key, left))
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
def usage_reserve(uid, field="posts"):
    """سهمیه را پیشاپیش و اتمیک رزرو می‌کند تا چند چرخه‌ی هم‌زمان از سقف پلن عبور نکنند. خروجی: (ok, day) — day سطلِ همان رزرو است."""
    lim = admin_limits(uid); cap = lim["daily_posts"] if field == "posts" else lim["daily_tests"]
    if cap is None: return True, None
    d = today_str(admin_offset(uid))
    q("INSERT INTO usage(admin_id,day,posts,tests) VALUES(?,?,0,0) ON CONFLICT(admin_id,day) DO NOTHING", (uid, d), commit=True)
    with _lock:
        cur = db().execute(f"UPDATE usage SET {field}={field}+1 WHERE admin_id=? AND day=? AND {field}<?", (uid, d, cap))
        db().commit(); return cur.rowcount > 0, d
def usage_release(uid, field, day):
    if day is None: return
    q(f"UPDATE usage SET {field}=MAX(0,{field}-1) WHERE admin_id=? AND day=?", (uid, day), commit=True)
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
    for k, v in _safe_fields("discounts", f).items(): q(f"UPDATE discounts SET {k}=? WHERE code=?", (v, code), commit=True)
def disc_delete(code): q("DELETE FROM discounts WHERE code=?", (code,), commit=True)
def disc_valid(code):
    """خروجی: (row|None, reason) — reason: ok | notfound | inactive | expired | exhausted"""
    d = disc_get(code)
    if not d: return None, "notfound"
    if not d["active"]: return None, "inactive"
    e = parse_dt(d["expires"])
    if e and e <= now_utc(): return None, "expired"
    if d["max_uses"] and d["used"] >= d["max_uses"]: return None, "exhausted"
    return d, "ok"
def disc_use(code): q("UPDATE discounts SET used=used+1 WHERE code=?", (code,), commit=True)
def discount_price(price_text, percent):
    """اگر قیمت عدد داشته باشد، مبلغ پس از تخفیف را با همان واحد برمی‌گرداند؛ در غیر این‌صورت «قیمت + (٪ تخفیف)»."""
    t = str(price_text or "").translate(_FA_DIGITS); m = re.search(r"\d[\d,٬.]*", t)
    if not m: return f"{price_text} (-{percent}%)"
    try: n = float(m.group(0).replace(",", "").replace("٬", ""))
    except Exception: return f"{price_text} (-{percent}%)"
    v = n * (100 - percent) / 100; vs = f"{int(v):,}" if v == int(v) else f"{v:,.2f}"
    return t[:m.start()] + vs + t[m.end():]
# ============================================================
# تنظیمات مستقل هر کانال
DEFAULT_PROMPT = {
    "fa": ("تو سردبیر حرفه‌ای یک کانال تلگرامی هستی و مثل یک انسانِ خبره و خوش‌قلم می‌نویسی؛ نه مثل ربات و نه مثل هوش مصنوعی. به زبانی می‌نویسی که در «زبان خروجی» تعیین شده است. "
           "متن را روان، دقیق، بی‌طرف و بدون اغراق بازنویسی کن؛ چیزی که در منبع نیست اضافه نکن و اعداد، تاریخ‌ها و اسامی را دقیقاً حفظ کن. "
           "تیتر جذاب در خط اول داخل <b> با یک ایموجی مرتبط؛ سپس لید یک‌جمله‌ای؛ سپس پاراگراف‌های کوتاه ۲ تا ۳ خطی با یک خط خالی بین آن‌ها. "
           "هر پاراگراف با یک ایموجی مرتبط شروع شود و در طول متن هم ایموجی‌های مناسب ادامه یابد (متنِ حدود ۲۰۰۰ کاراکتری حدود ۸ تا ۱۲ ایموجی می‌خواهد). "
           "نکات و فهرست‌ها را با «•» بنویس، اصطلاحات و اعداد مهم را <b> کن، مهم‌ترین نقل‌قول یا آمار را داخل <blockquote> بگذار. "
           "از خط جداکننده مثل «---»، جملات کلیشه‌ای و لحن قالبی پرهیز کن. جمله‌ها کوتاه و متنوع، بدون مقدمه‌چینی، با یک جمع‌بندی یک‌خطی در پایان."),
    "en": ("You are a professional editor of a Telegram channel who writes like a skilled, eloquent human — never like a bot or an AI. You write in the language set in “Output language”. "
           "Rewrite clearly, precisely, neutrally and without exaggeration; never add facts missing from the source and keep numbers, dates and names exact. "
           "Catchy headline on the first line inside <b> with one relevant emoji; then a one-sentence lead; then short 2–3 line paragraphs separated by a blank line. "
           "Every paragraph starts with a relevant emoji and suitable emojis continue naturally through the text (a ~2000-character post wants about 8–12 emojis). "
           "List points with “•”, bold key terms and numbers with <b>, put the most important quote or figure inside <blockquote>. "
           "Never use divider lines like “---”, no clichés, no robotic tone. Short, varied sentences, no preamble, one-line takeaway at the end."),
}
# پرامپت‌های پیش‌فرضِ نسخه‌های قبل — اگر کانال هنوز همان‌ها را دارد، خودکار با پیش‌فرض جدید جایگزین می‌شوند
_LEGACY_PROMPTS = (
    "تو سردبیر حرفه‌ای یک کانال تلگرامی فارسی هستی. متن را روان، دقیق، بی‌طرف و بدون اغراق بازنویسی کن؛ چیزی که در منبع نیست اضافه نکن و اعداد، تاریخ‌ها و اسامی را دقیقاً حفظ کن. "
    "تیتر جذاب در خط اول داخل <b> با یک ایموجی مرتبط؛ سپس لید یک‌جمله‌ای؛ سپس پاراگراف‌های کوتاه ۲ تا ۳ خطی با یک خط خالی بین آن‌ها. "
    "نکات کلیدی را با «•» فهرست کن، اصطلاحات مهم را <b> کن، نقل‌قول مهم را داخل <blockquote> بگذار. در هر پاراگراف حداکثر یک ایموجی مرتبط. جمله‌ها کوتاه، بدون مقدمه‌چینی، با یک جمع‌بندی یک‌خطی در پایان.",
    "You are a professional editor of an English Telegram channel. Rewrite clearly, precisely, neutrally and without exaggeration; never add facts missing from the source and keep numbers, dates and names exact. "
    "Catchy headline on the first line inside <b> with one relevant emoji; then a one-sentence lead; then short 2–3 line paragraphs separated by a blank line. "
    "List key points with “•”, bold key terms with <b>, put a key quote inside <blockquote>. At most one relevant emoji per paragraph. Short sentences, no preamble, one-line takeaway at the end.",
)
DEFAULT_CATEGORIES = {
    "fa": [{"name": "خبری", "emoji": "📰", "style": "تیتر کوتاه بولد، لید یک‌جمله‌ای، ۲ تا ۳ پاراگراف کوتاه، یک نکته‌ی کلیدی با «•»."},
           {"name": "آموزشی", "emoji": "🎓", "style": "تیتر بولد، مقدمه‌ی یک‌خطی، ۳ تا ۶ نکته با «•»، جمع‌بندی یک‌خطی."},
           {"name": "تحلیلی", "emoji": "🧠", "style": "تیتر بولد، یک نقل‌قول کلیدی داخل blockquote، تحلیل در دو پاراگراف کوتاه."},
           {"name": "معرفی و بررسی", "emoji": "🔍", "style": "تیتر بولد، خلاصه‌ی یک‌خطی، مزایا/معایب با «•»، جمع‌بندی بی‌طرف."},
           {"name": "علمی و پژوهشی", "emoji": "🔬", "style": "تیتر بولد، یافته‌ی اصلی در یک جمله، روش و اعداد مهم با «•»، محدودیت‌ها در یک خط."},
           {"name": "اقتصادی و بازار", "emoji": "📈", "style": "تیتر بولد، عدد/روند کلیدی در blockquote، دلیل و پیامد در دو پاراگراف کوتاه، بدون توصیه‌ی مالی."},
           {"name": "سلامت و سبک زندگی", "emoji": "🫁", "style": "تیتر بولد، توضیح ساده، توصیه‌های عملی با «•»، یک خط یادآوری که جایگزین پزشک نیست."},
           {"name": "ورزشی", "emoji": "🏆", "style": "تیتر بولد، نتیجه/رخداد در خط اول، آمار مهم با «•»، یک جمله درباره‌ی ادامه‌ی ماجرا."},
           {"name": "فرهنگ و هنر", "emoji": "🎭", "style": "تیتر بولد، معرفی کوتاه اثر/رخداد، یک نقل‌قول در blockquote، لحن روایی و بی‌قضاوت."},
           {"name": "شغلی و مهارت", "emoji": "💼", "style": "تیتر بولد، فرصت/مهارت در یک جمله، مراحل عملی با «•»، یک خط جمع‌بندی."}],
    "en": [{"name": "News", "emoji": "📰", "style": "Short bold headline, one-sentence lead, 2–3 short paragraphs, one key point as a “•” bullet."},
           {"name": "Tutorial", "emoji": "🎓", "style": "Bold headline, one-line intro, 3–6 “•” bullets, one-line takeaway."},
           {"name": "Analysis", "emoji": "🧠", "style": "Bold headline, one key quote in blockquote, analysis in two short paragraphs."},
           {"name": "Review", "emoji": "🔍", "style": "Bold headline, one-line summary, pros/cons as “•” bullets, neutral verdict."},
           {"name": "Science & research", "emoji": "🔬", "style": "Bold headline, the main finding in one sentence, method and key numbers as “•” bullets, limitations in one line."},
           {"name": "Business & markets", "emoji": "📈", "style": "Bold headline, the key figure or trend in a blockquote, cause and effect in two short paragraphs, no financial advice."},
           {"name": "Health & lifestyle", "emoji": "🫁", "style": "Bold headline, plain explanation, practical tips as “•” bullets, one line noting it is not medical advice."},
           {"name": "Sports", "emoji": "🏆", "style": "Bold headline, result or event on the first line, key stats as “•” bullets, one sentence on what comes next."},
           {"name": "Culture & arts", "emoji": "🎭", "style": "Bold headline, short introduction of the work or event, one quote in blockquote, narrative and non-judgmental tone."},
           {"name": "Career & skills", "emoji": "💼", "style": "Bold headline, the opportunity or skill in one sentence, actionable steps as “•” bullets, one-line takeaway."}],
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
            "strict_ads": False, "interval_minutes": 60, "posts_per_cycle": 2, "hashtags": True,
            "last_run": None, "last_end": None, "last_result": "", "last_diag": None, "last_notified_diag": ""}
def get_settings(cid):
    ch = q("SELECT settings, username, admin_id FROM channels WHERE id=?", (cid,), one=True)
    stored = {}
    if ch and ch["settings"]:
        try: stored = json.loads(ch["settings"])
        except Exception: stored = {}
    base = stored.get("ui_lang") or (user_lang(ch["admin_id"]) if ch else None) or "fa"
    s = default_settings(base if base in LANGS else "fa", ch["username"] if ch else ""); s.update(stored); s["ui_lang"] = base if base in LANGS else "fa"
    if s.get("prompt") in _LEGACY_PROMPTS: s["prompt"] = DEFAULT_PROMPT[s["ui_lang"]]  # پرامپتِ پیش‌فرضِ قدیمی → خودکار به نسخه‌ی جدید (خنثی از زبان)
    s["interval_minutes"] = max(MIN_INTERVAL, int(s.get("interval_minutes") or MIN_INTERVAL)); s["lookback_hours"] = min(MAX_LOOKBACK, max(1, int(s.get("lookback_hours") or 24)))
    s["posts_per_cycle"] = min(MAX_PPC, max(1, int(s.get("posts_per_cycle") or 1))); s["post_limit"] = min(4000, max(300, int(s.get("post_limit") or POST_LIMIT_DEFAULT)))
    return s
LOCALIZED_KEYS = ("prompt", "language", "categories", "criteria")
def _same(a, b):
    try: return json.dumps(a, ensure_ascii=False, sort_keys=True) == json.dumps(b, ensure_ascii=False, sort_keys=True)
    except Exception: return a == b
def relocalize_settings(cid, new_lang):
    """زبان مدیر عوض شد → صفر تا صدِ تنظیمات کانال هم عوض می‌شود: هر مقداری که همان «پیش‌فرض زبان قبلی» بوده (پرامپت، زبان محتوا، دسته‌ها، معیارها) به زبان جدید بازنویسی می‌شود؛ مقادیر دست‌ساز مدیر دست‌نخورده می‌مانند."""
    new_lang = new_lang if new_lang in LANGS else "fa"; s = get_settings(cid); old = s.get("ui_lang", "fa")
    if old != new_lang:
        old_d, new_d = default_settings(old, ""), default_settings(new_lang, "")
        for k in LOCALIZED_KEYS:
            if _same(s.get(k), old_d.get(k)): s[k] = new_d[k]
    s["ui_lang"] = new_lang; s["last_diag"] = None; s["last_notified_diag"] = ""; save_settings(cid, s); return s
def relocalize_all(uid, new_lang):
    n = 0
    for ch in q("SELECT id FROM channels WHERE admin_id=?", (uid,)):
        try: relocalize_settings(ch["id"], new_lang); n += 1
        except Exception as e: log.warning(f"relocalize {ch['id']}: {e}")
    return n
def save_settings(cid, s): q("UPDATE channels SET settings=? WHERE id=?", (json.dumps(s, ensure_ascii=False), cid), commit=True)
def update_settings(cid, **kw): s = get_settings(cid); s.update(kw); save_settings(cid, s); return s
def in_quiet(s):
    a, b = s.get("quiet_start"), s.get("quiet_end")
    if a is None or b is None or a == b: return False
    h = datetime.now(tz_of(s.get("utc_offset"))).hour
    return (a <= h < b) if a < b else (h >= a or h < b)
# ============================================================
# کانال‌ها + لایه‌ی امنیتی (کد قفل)
def _lock_code(): return f"{random.SystemRandom().randint(0, 999999):06d}"
def list_channels(uid): return q("SELECT * FROM channels WHERE admin_id=? ORDER BY id", (uid,))
def get_channel(cid): return q("SELECT * FROM channels WHERE id=?", (cid,), one=True)
def channel_owned(cid, uid):
    ch = get_channel(cid); return ch if ch and (ch["admin_id"] == uid or is_super(uid)) else None
def channel_by_chat(chat_id): return q("SELECT * FROM channels WHERE chat_id=?", (chat_id,), one=True)
def add_channel(uid, chat_id, title, username, verified_by, lang="fa"):
    if channel_by_chat(chat_id): return None
    return q("INSERT INTO channels(admin_id,chat_id,title,username,lock_code,verified_by,created_at,settings) VALUES(?,?,?,?,?,?,?,?)",
             (uid, chat_id, title, username or "", _lock_code(), verified_by, now_iso(), json.dumps(default_settings(lang, username), ensure_ascii=False)), commit=True)
def publication_pending(cid):
    if ch_lock(cid).locked(): return True
    rows = q("SELECT s.value FROM articles a JOIN settings s ON s.key='pubj:'||a.id WHERE a.channel_id=? AND s.value!='null'", (cid,))
    return any((json.loads(r["value"]) or {}).get("phase") in ("in_flight", "partial", "ack") for r in rows)

def transfer_channel(cid, new_uid, lang="fa"):
    if publication_pending(cid): raise RuntimeError("channel_busy")
    ch = get_channel(cid)
    if not ch: return None
    q("DELETE FROM sources WHERE channel_id=?", (cid,), commit=True); q("DELETE FROM articles WHERE channel_id=? AND status!='published'", (cid,), commit=True)
    q("UPDATE channels SET admin_id=?, verified_by=?, lock_code=?, settings=? WHERE id=?", (new_uid, new_uid, _lock_code(), json.dumps(default_settings(lang, ch["username"]), ensure_ascii=False), cid), commit=True)
    return ch["admin_id"]
def regen_lock(cid): code = _lock_code(); q("UPDATE channels SET lock_code=? WHERE id=?", (code, cid), commit=True); return code
def reset_channel_link(cid):
    """بازتولید کد قفل ⇒ پیوند کانال از نظر امنیتی باطل می‌شود: کد تازه صادر می‌شود، صف انتشار (تأیید‌نشده‌ها) پاک می‌شود، اتوماسیون خاموش و وضعیت چرخه صفر می‌شود. منابع و آرشیو منتشر‌شده دست‌نخورده می‌مانند."""
    code = _lock_code()
    if publication_pending(cid): raise RuntimeError("channel_busy")
    q("UPDATE channels SET lock_code=? WHERE id=?", (code, cid), commit=True)
    n = q("SELECT COUNT(*) c FROM articles WHERE channel_id=? AND status!='published'", (cid,), one=True)["c"]
    q("DELETE FROM articles WHERE channel_id=? AND status!='published'", (cid,), commit=True)
    update_settings(cid, enabled=False, last_run=None, last_end=None, last_result="", last_diag=None, last_notified_diag="")
    return code, n
def check_lock(cid, code): ch = get_channel(cid); return bool(ch and ch["lock_code"] and str(code).strip() == ch["lock_code"])
def del_channel(cid, uid):
    if publication_pending(cid): raise RuntimeError("channel_busy")
    q("DELETE FROM sources WHERE channel_id=? AND admin_id=?", (cid, uid), commit=True); q("DELETE FROM articles WHERE channel_id=? AND admin_id=?", (cid, uid), commit=True)
    q("DELETE FROM channels WHERE id=? AND admin_id=?", (cid, uid), commit=True)
def update_channel_meta(cid, title=None, username=None):
    if title is not None: q("UPDATE channels SET title=? WHERE id=?", (title, cid), commit=True)
    if username is not None: q("UPDATE channels SET username=? WHERE id=?", (username, cid), commit=True)
# ============================================================
# منابع (مستقل برای هر کانال)
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
def del_source(sid, uid): q("DELETE FROM sources WHERE id=? AND admin_id=?", (sid, uid), commit=True)
def set_source_active(sid, val, col="active"):
    if col not in ("active", "bot_active"): return None
    q(f"UPDATE sources SET {col}=? WHERE id=?", (1 if val else 0, sid), commit=True); return bool(val)
def toggle_source(sid, uid, col="active"):
    """col='active' ⇒ منبعِ محتوای کانال · col='bot_active' ⇒ منبعِ محتوای ربات (نسخه‌ی کامل داخل ربات)"""
    if col not in ("active", "bot_active"): col = "active"
    q(f"UPDATE sources SET {col}=1-COALESCE({col},1) WHERE id=? AND admin_id=?", (sid, uid), commit=True); s = get_source(sid); return bool(s and s[col])
def source_bot_ok(sid):
    if not sid: return True
    s = get_source(sid); return bool(s is None or s["bot_active"] is None or s["bot_active"])
def set_source_api(sid, api_url="", api_key="", api_note=""):
    """ثبت/حذف API یک منبع. خالی‌بودن api_url ⇒ حذف API و برگشت به مسیر عادی RSS/HTML."""
    q("UPDATE sources SET api_url=?, api_key=?, api_note=? WHERE id=?", ((api_url or "").strip() or None, (api_key or "").strip() or None, (api_note or "").strip(), sid), commit=True)
    return get_source(sid)
def source_ok(sid, feed_url=None, etag=None, last_modified=None):
    q("UPDATE sources SET last_fetch=?, fail_count=0, last_error=NULL, etag=?, last_modified=?, feed_url=COALESCE(?, feed_url) WHERE id=?", (now_iso(), etag, last_modified, feed_url, sid), commit=True)
def source_fail(sid, err): q("UPDATE sources SET last_fetch=?, fail_count=fail_count+1, last_error=? WHERE id=?", (now_iso(), str(err)[:200], sid), commit=True)
# ============================================================
# مقالات (مستقل برای هر کانال)
def article_exists(cid, h): return bool(q("SELECT 1 FROM articles WHERE channel_id=? AND hash=?", (cid, h), one=True))
def article_insert(uid, cid, h, url, title, source_id, published_at, status="discovered", reason=""):
    """اگر رکورد از قبل موجود باشد، INSERT OR IGNORE چیزی درج نمی‌کند و lastrowid بی‌اعتبار می‌شود؛ در آن حالت None برمی‌گردانیم تا محتوای تولیدشده هرگز به مقاله‌ی اشتباه نچسبد."""
    with _lock:
        cur = db().execute("INSERT OR IGNORE INTO articles(admin_id,channel_id,hash,url,title,source_id,published_at,created_at,status,reason) VALUES(?,?,?,?,?,?,?,?,?,?)",
                           (uid, cid, h, url, title or "", source_id, published_at, now_iso(), status, reason))
        db().commit(); return cur.lastrowid if cur.rowcount else None
def article_update(aid, **f):
    if not f: return
    _safe_fields("articles", f)
    q("UPDATE articles SET " + ", ".join(f"{k}=?" for k in f) + " WHERE id=?", (*f.values(), aid), commit=True)
def get_article(aid): return q("SELECT * FROM articles WHERE id=?", (aid,), one=True)
def get_pub_journal(aid): return gget(f"pubj:{aid}") or None
def set_pub_journal(aid, entry): gset(f"pubj:{aid}", entry)
def release_publication(aid, journal, reason):
    with _lock:
        conn = db()
        try:
            conn.execute("BEGIN IMMEDIATE")
            day = journal.get("reserved_day")
            if day is not None and journal.get("phase") != "in_flight":
                conn.execute("UPDATE usage SET posts=MAX(0,posts-1) WHERE admin_id=? AND day=?", (journal["admin_id"], day))
            journal = dict(journal, reserved_day=day if journal.get("phase") == "in_flight" else None)
            conn.execute("UPDATE articles SET reason=? WHERE id=?", (reason, aid))
            if journal.get("phase") == "prepared":
                conn.execute("DELETE FROM settings WHERE key=?", (f"pubj:{aid}",))
            else:
                conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (f"pubj:{aid}", json.dumps(journal)))
            conn.commit()
        except BaseException:
            conn.rollback(); raise
    return journal

class PublicationTransport:
    def __init__(self, bot, aid, journal, parent):
        self.bot, self.aid, self.journal, self.parent = bot, aid, journal, parent
        self.caption_complete = False
    def __getattr__(self, name):
        method = getattr(self.bot, name)
        if not name.startswith("send_"): return method
        async def send(*args, **kwargs):
            operation_checkpoint()
            if self.parent.cancelling(): raise asyncio.CancelledError
            previous = self.journal["phase"]
            self.journal["phase"] = "in_flight"
            set_pub_journal(self.aid, self.journal)
            try: message = await method(*args, **kwargs)
            except (BadRequest, RetryAfter, Forbidden):
                self.journal["phase"] = previous
                set_pub_journal(self.aid, self.journal)
                raise
            except NetworkError:
                raise
            except Exception:
                raise
            if name != "send_message" and not self.caption_complete:
                self.journal.update(phase="partial", media_id=message.message_id)
            else:
                self.journal.update(phase="ack", message_id=message.message_id)
            set_pub_journal(self.aid, self.journal)
            return message
        return send

def reserve_publication(aid, admin_id, count_usage, test_user, previous):
    day = today_str(admin_offset(admin_id))
    cap = admin_limits(admin_id)["daily_posts"] if count_usage else None
    journal = dict(previous or {}, phase="partial" if previous and previous.get("media_id") else "prepared",
                   admin_id=admin_id, test_user=test_user, day=day, reserved_day=day if count_usage and cap is not None else None)
    with _lock:
        conn = db()
        try:
            conn.execute("BEGIN IMMEDIATE")
            if journal["reserved_day"] is not None:
                conn.execute("INSERT OR IGNORE INTO usage(admin_id,day,posts,tests) VALUES(?,?,0,0)", (admin_id, day))
                cur = conn.execute("UPDATE usage SET posts=posts+1 WHERE admin_id=? AND day=? AND posts<?", (admin_id, day, cap))
                if not cur.rowcount: conn.rollback(); return None
            conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (f"pubj:{aid}", json.dumps(journal)))
            conn.commit()
        except BaseException:
            conn.rollback(); raise
    return journal

def settle_publication(aid, ch, journal):
    link = journal.get("link") or msg_link(ch, SimpleNamespace(message_id=journal["message_id"]))
    with _lock:
        conn = db()
        try:
            conn.execute("BEGIN IMMEDIATE")
            a = conn.execute("SELECT * FROM articles WHERE id=?", (aid,)).fetchone()
            if not a: raise RuntimeError("article_missing")
            if a["status"] != "published":
                conn.execute("INSERT OR IGNORE INTO posted VALUES(?,?,?)", (ch["chat_id"], a["hash"], now_iso()))
                conn.execute("UPDATE articles SET status='published',links=?,reason='' WHERE id=?", (json.dumps([link]), aid))
                uid = journal.get("test_user")
                if uid is not None:
                    day = journal["day"]
                    conn.execute("INSERT INTO usage(admin_id,day,posts,tests) VALUES(?,?,0,1) ON CONFLICT(admin_id,day) DO UPDATE SET tests=tests+1", (uid, day))
            conn.execute("DELETE FROM settings WHERE key=?", (f"pubj:{aid}",))
            conn.commit()
        except BaseException:
            conn.rollback(); raise
    if journal.get("test_user") is not None: rate_mark(f"test:{ch['id']}")
def recover_publications():
    for row in q("SELECT a.id,a.channel_id,a.reason FROM articles a JOIN settings s ON s.key='pubj:'||a.id WHERE s.value!='null'"):
        if ch_lock(row["channel_id"]).locked(): continue
        journal = get_pub_journal(row["id"])
        if not journal: continue
        try:
            if journal.get("phase") == "ack":
                ch = get_channel(row["channel_id"])
                if ch: settle_publication(row["id"], ch, journal)
            else:
                release_publication(row["id"], journal, "delivery_unknown" if journal.get("phase") == "in_flight" else row["reason"] or "")
        except Exception: log.exception("publication recovery failed article=%s", row["id"])

def articles_by_status(cid, status, limit=50, automatic=False):
    st = ("rejected", "failed") if status == "rejected" else (status,)
    order = "ASC" if status == "ready" else "DESC"
    eligible = " AND COALESCE(reason,'')!='cancelled'" if automatic else ""
    return q(f"SELECT id,title,score,category,created_at,url,reason,status FROM articles WHERE channel_id=? AND status IN ({','.join('?'*len(st))}){eligible} ORDER BY id {order} LIMIT ?", (cid, *st, limit))
def ready_count(cid): return q("SELECT COUNT(*) c FROM articles WHERE channel_id=? AND status='ready'", (cid,), one=True)["c"]
def delete_article(aid, uid):
    a = get_article(aid)
    if a and publication_pending(a["channel_id"]): raise RuntimeError("channel_busy")
    q("DELETE FROM articles WHERE id=? AND admin_id=?", (aid, uid), commit=True)
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
    q("DELETE FROM articles WHERE created_at<? AND status='published'", ((now_utc() - timedelta(hours=72)).isoformat(),), commit=True)
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
# پشتیبانی و درخواست‌های پرداخت
def support_open(uid): q("INSERT OR REPLACE INTO support(user_id,open,opened_at) VALUES(?,1,?)", (uid, now_iso()), commit=True)
def support_close(uid): q("UPDATE support SET open=0 WHERE user_id=?", (uid,), commit=True)
def support_is_open(uid):
    r = q("SELECT open FROM support WHERE user_id=?", (uid,), one=True); return bool(r and r["open"])
def support_map_set(msg_key, uid): q("INSERT OR REPLACE INTO support_map VALUES(?,?,?)", (msg_key, uid, now_iso()), commit=True)
def support_map_get(msg_key):
    r = q("SELECT user_id FROM support_map WHERE msg_id=?", (msg_key,), one=True); return r["user_id"] if r else None
def pay_pending_for(uid, pid): return q("SELECT * FROM pay_requests WHERE user_id=? AND plan_id=? AND status='pending'", (uid, pid), one=True)
def pay_create(uid, pid, receipt_chat=None, receipt_msg=None, note="", discount=None, final_price=None):
    return q("INSERT INTO pay_requests(user_id,plan_id,created_at,receipt_chat,receipt_msg,note,discount,final_price) VALUES(?,?,?,?,?,?,?,?)", (uid, pid, now_iso(), receipt_chat, receipt_msg, (note or "")[:500], discount, final_price), commit=True)
def pay_pending(): return q("SELECT r.*, u.username, u.name, p.name plan_name, p.price plan_price FROM pay_requests r JOIN users u ON u.id=r.user_id JOIN plans p ON p.id=r.plan_id WHERE r.status='pending' ORDER BY r.id")
def pay_get(rid): return q("SELECT * FROM pay_requests WHERE id=?", (rid,), one=True)
def pay_set(rid, status): q("UPDATE pay_requests SET status=?, decided_at=? WHERE id=?", (status, now_iso(), rid), commit=True)
def pay_claim(rid):
    """CAS: only the first decider of a pending payment wins (prevents double-approve double-assignment)."""
    with _lock:
        db().execute("UPDATE pay_requests SET status='processing' WHERE id=? AND status='pending'", (rid,))
        return db().execute("SELECT status FROM pay_requests WHERE id=?", (rid,)).fetchone()[0] == "processing"
# ============================================================
# HTTP مشترک، Cloudflare KV، دیپ‌لینک
_http = None
UA_BROWSER = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"
UA_FEED = "Mozilla/5.0 (compatible; NewsBot/3.0; +https://t.me) FeedFetcher"
def http():
    global _http
    if _http is None:
        _http = httpx.AsyncClient(follow_redirects=True, timeout=httpx.Timeout(25, connect=10), limits=httpx.Limits(max_connections=FETCH_CONCURRENCY + 8, max_keepalive_connections=8),
                                  headers={"User-Agent": UA_BROWSER, "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8", "Accept-Language": "fa,en;q=0.8"})
    return _http
_PRIVATE_HOSTS = ("localhost", "metadata.google.internal")
_host_ok = {}
def public_url(u):
    """آدرس، بیرونی و امن است؟ منبعِ کاربر نباید به شبکه‌ی داخلی سرور اشاره کند (SSRF)."""
    try: p = urlparse(str(u))
    except Exception: return False
    if p.scheme not in ("http", "https") or not p.hostname: return False
    host = p.hostname.lower()
    if host in _host_ok: return _host_ok[host]
    ok = not (host in _PRIVATE_HOSTS or host.endswith((".local", ".internal", ".localhost")))
    if ok:
        try: addrs = [i[4][0] for i in socket.getaddrinfo(host, None)]
        except Exception: addrs = []      # resolve نشد؛ خودِ درخواست خطای معمول می‌دهد
        for a in addrs:
            try: ip = ipaddress.ip_address(a)
            except Exception: ok = False; break
            if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast: ok = False; break
    if len(_host_ok) > 5000: _host_ok.clear()
    _host_ok[host] = ok; return ok
async def fetch(url, **kw):
    """دانلود با سمافور سراسری (جلوگیری از فشار هم‌زمان). خروجی: Response یا Exception."""
    if not await asyncio.to_thread(public_url, url): raise FetchError(403, str(url))
    async with FETCH_SEM: r = await http().get(url, **kw)
    try:
        if int(r.headers.get("content-length") or 0) > MAX_PAGE_BYTES: raise FetchError(413, str(url))
    except (TypeError, ValueError): pass
    return r
class FetchError(RuntimeError):
    """خطای HTTP با کد وضعیت؛ برای پیام اختصاصی ۴۰۳ هنگام افزودن منبع."""
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
    """payload: {short, full, title, url, show_source, media:{url,kind}|None, ts}"""
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
    db(); seed_plans(); recover_publications()
    if gget("automation_enabled") is None: gset("automation_enabled", True)
    log.info(f"core v3 آماده | CF KV: {'فعال' if CF_ENABLED else 'محلی'} | مدیر کلان: {SUPER_ADMIN_IDS} | AI×{AI_CONCURRENCY} FETCH×{FETCH_CONCURRENCY} CYCLE×{CYCLE_CONCURRENCY}")
# ---------- پایان لایه‌ی هسته‌ی داده ----------
# ============================================================
# موتور: مدل‌های AI سازگار با همه، فرمت‌بندی، کشف/استخراج قدرتمند، انتشار، چرخه، زمان‌بند
# ============================================================
from urllib.parse import parse_qsl, urlencode
from telegram.error import BadRequest, RetryAfter, NetworkError, Forbidden
def hostname(u):
    try: return urlparse(u).netloc.replace("www.", "") or u
    except Exception: return str(u)
# ============================================================
# مدل‌های هوش مصنوعی — هر سرویسی با Base URL + کلید + نام مدل (نوع خودکار تشخیص داده می‌شود)
def detect_kind(base_url):
    b = (base_url or "").lower()
    if "anthropic.com" in b: return "anthropic"
    if "generativelanguage.googleapis.com" in b: return "gemini"
    return "openai"     # OpenAI-compatible: OpenAI, OpenRouter, Groq, DeepSeek, Together, Mistral, xAI, Ollama, LM Studio, …
def list_models(active_only=False, owner_id=None):
    """owner_id=None ⇒ مدل‌های عمومیِ مدیر کلان · owner_id=<uid> ⇒ مدل‌های شخصیِ همان مدیر"""
    sql = "SELECT * FROM ai_models WHERE " + ("owner_id=?" if owner_id else "owner_id IS NULL")
    if active_only: sql += " AND active=1"
    return q(sql + " ORDER BY priority, id", (owner_id,) if owner_id else ())
def get_model(mid): return q("SELECT * FROM ai_models WHERE id=?", (mid,), one=True)
def add_model(base_url, api_key, model, name="", priority=10, temperature=0.5, max_tokens=2500, owner_id=None):
    base_url = str(base_url).strip().rstrip("/"); model = str(model).strip(); kind = detect_kind(base_url)
    name = (name or f"{hostname(base_url) or kind}").strip()[:40]
    return q("INSERT INTO ai_models(name,kind,base_url,api_key,model,priority,temperature,max_tokens,owner_id) VALUES(?,?,?,?,?,?,?,?,?)", (name, kind, base_url, api_key.strip(), model, priority, temperature, max_tokens, owner_id), commit=True)
def update_model(mid, **f):
    if "base_url" in f: f["base_url"] = str(f["base_url"]).strip().rstrip("/"); f["kind"] = detect_kind(f["base_url"])
    _safe_fields("ai_models", f)
    q("UPDATE ai_models SET " + ", ".join(f"{k}=?" for k in f) + " WHERE id=?", (*f.values(), mid), commit=True)
def delete_model(mid): q("DELETE FROM ai_models WHERE id=?", (mid,), commit=True)
async def notify_super(text, kb=None):
    if NOTIFY_SUPER:
        try: await NOTIFY_SUPER(text, kb)
        except Exception as e: log.warning(f"notify super: {e}")
async def notify_user(uid, text, kb=None):
    if NOTIFY_USER:
        try: await NOTIFY_USER(uid, text, kb)
        except Exception as e:
            log.warning(f"notify user {uid}: {e}")
            if SCHED_NOTIF_FAILURES:
                raise  # scheduled-warning failures must reach _plan_notifications' release branch
def _err_text(r):
    try:
        j = r.json(); e = j.get("error"); msg = (e.get("message") if isinstance(e, dict) else e) or j.get("message") or j.get("detail") or r.text
    except Exception: msg = r.text
    return f"HTTP {r.status_code}: {re.sub(r'<[^>]+>', '', str(msg))[:160]}"
class AIResponseError(RuntimeError):
    pass


def _provider_json(r):
    if r.status_code >= 400: raise AIResponseError(_err_text(r))
    try: j = r.json()
    except ValueError as e: raise AIResponseError("malformed provider JSON") from e
    if not isinstance(j, dict): raise AIResponseError("malformed provider envelope")
    if j.get("error"): raise AIResponseError("provider error response")
    return j


def _ai_text(value):
    if not isinstance(value, str): raise AIResponseError("invalid response text")
    value = value.strip()
    if not value: raise AIResponseError("empty response")
    return value


def _openai_content(j):
    choices = j.get("choices")
    if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
        raise AIResponseError("malformed provider choices")
    ch = choices[0]; msg = ch.get("message") or ch.get("delta") or {}
    if not isinstance(msg, dict): raise AIResponseError("malformed provider message")
    if msg.get("refusal"): raise AIResponseError("provider refused response")
    c = msg.get("content") or ch.get("text")
    if isinstance(c, list):
        if any(not isinstance(p, dict) or not isinstance(p.get("text"), str) for p in c):
            raise AIResponseError("malformed provider content")
        c = "".join(p["text"] for p in c)
    return _ai_text(c)
async def _post(url, **kw): return await http().post(url, timeout=httpx.Timeout(120, connect=15), **kw)
async def _call_model(m, system, user):
    kind = m["kind"] or detect_kind(m["base_url"]); base = (m["base_url"] or "").rstrip("/"); key = m["api_key"] or ""; model = m["model"]; temp = 0.5 if m["temperature"] is None else float(m["temperature"]); mx = int(m["max_tokens"] or 2500)
    if kind == "anthropic":
        url = base + ("/messages" if base.endswith("/v1") else "/v1/messages")
        r = await _post(url, headers={"x-api-key": key, "anthropic-version": "2023-06-01", "content-type": "application/json"}, json={"model": model, "max_tokens": mx, "temperature": temp, "system": system, "messages": [{"role": "user", "content": user}]})
        j = _provider_json(r); blocks = j.get("content")
        if not isinstance(blocks, list) or any(not isinstance(b, dict) for b in blocks): raise AIResponseError("malformed provider content")
        parts = [b.get("text") for b in blocks if b.get("type") == "text"]
        if any(not isinstance(p, str) for p in parts): raise AIResponseError("invalid response text")
        return _ai_text("".join(parts))
    if kind == "gemini":
        model = model.replace("models/", ""); root = base if re.search(r"/v1(beta)?$", base) else base + "/v1beta"
        r = await _post(f"{root}/models/{model}:generateContent", params={"key": key}, json={"system_instruction": {"parts": [{"text": system}]}, "contents": [{"role": "user", "parts": [{"text": user}]}], "generationConfig": {"temperature": temp, "maxOutputTokens": mx}})
        j = _provider_json(r); cands = j.get("candidates")
        if not isinstance(cands, list) or not cands or not isinstance(cands[0], dict): raise AIResponseError("malformed provider candidates")
        content = cands[0].get("content")
        if not isinstance(content, dict): raise AIResponseError("provider blocked response")
        parts = content.get("parts")
        if not isinstance(parts, list) or any(not isinstance(p, dict) or not isinstance(p.get("text"), str) for p in parts): raise AIResponseError("malformed provider parts")
        return _ai_text("".join(p["text"] for p in parts))
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    if "openrouter" in base: headers.update({"HTTP-Referer": "https://t.me", "X-Title": "NewsBot"})
    body = {"model": model, "temperature": temp, "max_tokens": mx, "messages": [{"role": "system", "content": system}, {"role": "user", "content": user}]}
    url = base if base.endswith("/chat/completions") else base + "/chat/completions"
    r = await _post(url, headers=headers, json=body)
    if r.status_code == 404 and not re.search(r"/v\d", base): r = await _post(base + "/v1/chat/completions", headers=headers, json=body)
    return _openai_content(_provider_json(r))
async def _mark_fail(m, err):
    cur = get_model(m["id"]) or m   # اسنپ‌شاتِ ورودی ممکن است کهنه باشد؛ شمارنده از سطر فعلی خوانده می‌شود
    fc = (cur["fail_count"] or 0) + 1; update_model(m["id"], fail_count=fc, last_error=str(err)[:300], last_fail=now_iso())
    if fc >= 2 and cur["status"] != "down":
        update_model(m["id"], status="down"); log_event("ERROR", f"مدل «{m['name']}» از کار افتاد: {err}")
        await notify_super(f"🔴 مدل <b>{html.escape(m['name'])}</b> (<code>{html.escape(m['model'])}</code>) از کار افتاد.\n<code>{html.escape(str(err)[:200])}</code>")
async def _mark_ok(m):
    cur = get_model(m["id"]) or m   # ok_count/fail_count از سطر فعلی، نه از اسنپ‌شات احتمالاً کهنه
    update_model(m["id"], fail_count=0, status="ok", last_ok=now_iso(), ok_count=(cur["ok_count"] or 0) + 1)
    if cur["status"] == "down": log_event("INFO", f"مدل «{m['name']}» دوباره فعال شد."); await notify_super(f"🟢 مدل <b>{html.escape(m['name'])}</b> دوباره فعال شد.")
# --- حریم خصوصی مدل‌ها: هیچ نام مدل/آدرس/کلیدی به مدیر میانی نمی‌رسد؛ فقط یک کد کوتاه و بی‌خطر
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
    """مدلِ سالم، یا مدلِ افتاده‌ای که وقت آزمایش دوباره‌اش رسیده است."""
    if m["status"] != "down": return True
    lf = parse_dt(m["last_fail"]); return bool(not lf or (now_utc() - lf) >= timedelta(minutes=MODEL_PROBE_MIN))
_ai_events = ContextVar("ai_events", default=None)


def _model_label(m, owner_id=None):
    if owner_id and m["owner_id"] != owner_id: return "مدل عمومی/پیش‌فرض" if user_lang(owner_id) != "en" else "Public/default model"
    return m["name"] or m["model"]


async def _ai_event(event, label="", code=None):
    callback = _ai_events.get()
    if callback: await callback(event, label, code)


def _validate_output(text):
    text = _ai_text(text)
    if text.startswith(("{", "[")):
        try: j = json.loads(text)
        except ValueError as e: raise AIResponseError("malformed AI output") from e
        if not isinstance(j, dict) or j.get("error"): raise AIResponseError("invalid AI output")
    return text


def _validate_ready(text):
    if _ai_text(text).upper() != "READY": raise AIResponseError("invalid health-check output")


def _validate_generation(text):
    _validate_output(text)
    j = parse_json(text)
    if isinstance(j, dict):
        if j.get("is_ad") is True: return
        post = j.get("post")
        if not isinstance(post, str) or not strip_tags(post).strip(): raise AIResponseError("invalid empty post")
    elif not strip_tags(salvage_post(text)).strip(): raise AIResponseError("empty AI output")


async def _try_models(groups, system, user, owner_id=None, on_queue=None, validate=None, explicit_id=None):
    tried = set(); last = "ai_none"
    for stage, models in groups:
        if stage == "test" and not models: await _ai_event("no_test")
        rest = list(models)
        while rest:
            free = [m for m in rest if not model_busy(m["id"])]
            m = (rest if explicit_id == rest[0]["id"] else (free or rest))[0]
            rest.remove(m)
            if m["id"] in tried: continue
            tried.add(m["id"])
            label = _model_label(m, owner_id)
            if model_busy(m["id"]) or AI_SEM.locked():
                await _ai_event("busy", label)
                if on_queue: await on_queue()
            try:
                async with model_lock(m["id"]):
                    current = get_model(m["id"])
                    if not current or current["owner_id"] != m["owner_id"] or (m["id"] != explicit_id and (not current["active"] or not _model_ready(current))):
                        await _ai_event("unavailable", label); continue
                    async with AI_SEM:
                        await _ai_event("start", label, stage)
                        text = _validate_output(await _call_model(current, system, user))
                        if validate: validate(text)
                    await _mark_ok(current)
                await _ai_event("success", label)
                return text, label, None
            except (httpx.HTTPError, asyncio.TimeoutError, AIResponseError) as e:
                last = "ai_timeout" if isinstance(e, (httpx.TimeoutException, asyncio.TimeoutError)) else err_code(e)
                await _mark_fail(m, e)
                await _ai_event("failure", label, last)
    await _ai_event("failed", code=last)
    return None, None, last


async def ai_chat(system, user, on_queue=None, owner_id=None, selected_id=None, validate=None):
    personal = [m for m in list_models(active_only=True, owner_id=owner_id) if _model_ready(m)] if owner_id else []
    if selected_id is not None:
        selected = get_model(selected_id)
        if not selected or selected["owner_id"] != owner_id or owner_id is None:
            return None, None, "ai_none"
        personal = [selected] + [m for m in personal if m["id"] != selected_id]
    shared = [m for m in list_models(active_only=True) if _model_ready(m)]
    test_id = gget("test_model_id")
    test = [m for m in shared if m["id"] == test_id]
    shared = [m for m in shared if m["id"] != test_id]
    return await _try_models([("personal", personal), ("test", test), ("public", shared)], system, user,
                             owner_id, on_queue, validate, selected_id)


async def test_model(mid):
    m = get_model(mid); t = time.monotonic()
    if not m: return False, "no model", 0.0
    out, label, err = await _try_models([("direct", [m])], "You are a health-check. Reply with exactly one word.",
                                      "Say: READY", validate=_validate_ready, explicit_id=mid)
    return out is not None, out[:100] if out else err, round(time.monotonic() - t, 1)
async def probe_down_models():
    for m in q("SELECT * FROM ai_models WHERE active=1 AND status='down' ORDER BY last_fail LIMIT 1"):
        lf = parse_dt(m["last_fail"])
        if not lf or (now_utc() - lf) >= timedelta(minutes=MODEL_PROBE_MIN): await test_model(m["id"])
def any_model_available(owner_id=None): return any(_model_ready(m) for m in list_models(active_only=True, owner_id=owner_id)) or (bool(owner_id) and any(_model_ready(m) for m in list_models(active_only=True)))
def models_free_count(): return sum(1 for m in list_models(active_only=True) if _model_ready(m) and not model_busy(m["id"]))
def parse_json(text):
    if not text: return None
    t = re.sub(r"```(?:json|JSON)?", "", text).strip(); s, e = t.find("{"), t.rfind("}")
    if s < 0 or e < 0: return None
    body = t[s:e + 1]
    base = [body, re.sub(r",\s*([}\]])", r"\1", body)]
    fixed = []
    for c in base:   # تعمیر خط/تبِ خام داخل رشته‌ها — خطای رایج مدل‌ها در JSON چندخطی
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
# HTML امن تلگرام + فرمت‌بندی
ALLOWED = {"b", "strong", "i", "em", "u", "s", "del", "code", "pre", "a", "blockquote", "tg-spoiler", "span", "tg-emoji"}
def sanitize_html(text):
    """Markdown/HTML آزاد → HTML مجاز تلگرام."""
    if not text: return ""
    text = str(text)
    text = re.sub(r"(?m)^[ \t]*[-–—_=*~•⸻]{3,}[ \t]*$", "", text)  # جداکننده‌های رباتیک (--- و امثال آن) حذف می‌شوند
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
        if tag == "tg-emoji": continue
        if closing:
            if tag in stack:
                while stack:
                    t = stack.pop(); out.append(f"</{t}>")
                    if t == tag: break
        else:
            if tag == "a":
                h = re.search(r'href=["\']([^"\']+)["\']', attrs)
                if not h or not h.group(1).strip().lower().startswith(("http://", "https://", "tg://")): continue
                out.append(f'<a href="{html.escape(html.unescape(h.group(1).strip()), quote=True)}">')
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
    """حذف قابلیت‌های خاص با حفظ متن و فرمت‌های معمولی (برای تلاش دوباره پس از خطای پارس تلگرام)."""
    t = re.sub(r"</?tg-emoji[^>]*>", "", t or ""); t = re.sub(r"</?tg-spoiler>", "", t); t = t.replace("<blockquote expandable>", "<blockquote>")
    return sanitize_html(t)
def strip_tags(t): return html.unescape(re.sub(r"<[^>]+>", "", t or ""))
def salvage_post(raw):
    """نگهبان نشت JSON — اگر پاسخ مدل قابل تجزیه نباشد، پاکت JSON حذف و فقط متن واقعی پست بازیابی می‌شود؛ هرگز JSON خام منتشر نمی‌شود."""
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
    if end < 0:   # شیء ناکامل (پاسخ قطع‌شده): متنِ بازِ آخرین کلید بازیابی می‌شود
        m = None
        for mm in re.finditer(r'":\s*"', t): m = mm
        if m:
            rest = t[m.end():].strip()
            if len(strip_tags(rest)) >= 40: return rest
    lines = [ln for ln in t.splitlines() if not re.match(r'^\s*"?[A-Za-z_][A-Za-z_0-9 ]{2,24}"?\s*:', ln) and not re.fullmatch(r'\s*[{}\[\],]*\s*', ln)]
    return "\n".join(lines).strip() or t
def _cut_pos(text, limit):
    """نقطه‌ی برش امن: پایان پاراگراف، بعد پایان جمله، بعد پایان کلمه — هرگز وسط جمله رها نمی‌شود."""
    cut = text[:limit]; nl = cut.rfind("\n")
    if nl > limit * 0.5: return nl
    pos = -1
    for m in re.finditer(r'[.!?؟…]+["»”’)\]]*(?=</[a-zA-Z]|\s|$)', cut): pos = m.end()
    if pos > limit * 0.4: return pos
    sp = cut.rfind(" ")
    return sp if sp > limit * 0.4 else len(cut)
def split_post_html(text, limit):
    """پست را در مرز امن به دو بخش «کانال + ادامه» می‌شکند؛ بخش دوم برای «ادامه در ربات» است و متنِ بخش اول را تکرار نمی‌کند."""
    if len(text) <= limit: return text, ""
    pos = _cut_pos(text, limit); head_raw, rest_raw = text[:pos], text[pos:]
    if rest_raw[:1] not in ("<", "", "\n", " ") and ">" in rest_raw[:80]:
        gt = rest_raw.find(">")
        if "<" not in rest_raw[:gt]: rest_raw = rest_raw[gt + 1:]  # تکه‌ی نیمه‌تمامِ یک تگ از ابتدای ادامه حذف می‌شود
    head = sanitize_html(re.sub(r"<[^>]*$", "", head_raw)).rstrip() + " …"
    # اگر برشِ فعلی (اگر توی وسطِ Quote واقع شده باشد، sanitize تگِ ناقص را حذف می‌کند) Quote را از بخشِ «کانال» برداشته
    # باشد و Quote در ادامهٔ «ادامه در ربات» مانده باشد، مرزِ برش را به پایانِ نخستین Quote می‌رانیم تا Quote با کانال بماند؛
    # Quote‌های بعدی و متنِ اضافی به بخشِ ربات می‌روند.
    if "<blockquote" not in head.lower() and "<blockquote" in text.lower():
        bq = text.lower().find("</blockquote>")
        if 0 <= bq and _cut_pos(text, limit) < bq:
            pos = bq + len("</blockquote>")
            head_raw, rest_raw = text[:pos], text[pos:]
            head = sanitize_html(re.sub(r"<[^>]*$", "", head_raw)).rstrip() + " …"
    rest = sanitize_html(rest_raw).strip()
    return head, rest
def fit_html(text, limit):
    if len(text) <= limit: return text, False
    return split_post_html(text, limit)[0], True
def clean_ai_text(t, s=None):
    """زباله‌های مدل حذف می‌شود: دیکشنری امتیازها («معیار»: ۹، ...) و تکه‌های JSON چسبیده به متن پست — هرگز به کانال یا ربات نمی‌رسد."""
    if not t: return t
    t = str(t).replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\t", " ")
    names = [str(c.get("name", "")).strip() for c in (s or {}).get("criteria", []) if c.get("name")]
    names += ["ارزش محتوایی", "غیرتبلیغاتی بودن", "کیفیت و کامل بودن", "ارتباط با موضوع کانال", "تازگی", "Content value", "Non-promotional", "Quality & completeness", "Relevance to channel topic", "Relevance", "Freshness"]
    num = r'(?:10|[0-9۰-۹])(?:[.,][0-9۰-۹])?'
    pat = re.compile(r'["“«\']?([^"”»:\n]{2,40})(?:\s*:\s*["”»\']?\s*|\s*["”»\']?\s*:\s*)' + num + r'\s*[,،.؛;]?')
    def rep(m):
        label = m.group(1).strip()
        return "" if any(label and (label in n or n in label) for n in names) else m.group(0)
    prev = None
    while prev != t: prev = t; t = pat.sub(rep, t)
    t = re.sub(r'(?m)^\s*["”»،,{}\[\].…؛:!؟]+\s*$\n?', "", t)   # خط‌های زباله‌ی JSON (مثل «",» یا «10.» تنها)
    t = re.sub(r"\[([^\]\n]{1,160})\]\((https?://[^)\s\"']{4,})\)", lambda m: m.group(2) if m.group(1).strip() in m.group(2) else f'<a href="{m.group(2)}">{m.group(1).replace(chr(34), "")}</a>', t)   # لینک مارک‌داونی → لینک واقعی
    t = re.sub(r"\[([^\]\n]{0,160})\]\(\s*\)", r"\1", t)
    t = re.sub(r"(?<![\w])['‘’]([\w؀-ۿ][\w؀-ۿ \-]{0,38}[\w؀-ۿ]|[\w؀-ۿ])['‘’](?![\w])", r"\1", t)   # کوتیشن دور واژه‌ها حذف می‌شود
    em = re.compile(r"[\U0001F000-\U0001FAFF]")
    hits = em.findall(t)
    if hits:
        t = em.sub("", t).replace("️", ""); t = re.sub(r'<a href="[^"]*">\s*</a>', " ", t)
        t = t.rstrip() + " " + hits[-1]   # فقط یک ایموجی، در همان انتها
    t = re.sub(r"(?m)^[ \t]+|[ \t]+$", "", t); t = re.sub(r"[ \t]{2,}", " ", t)
    t = re.sub(r"\n{3,}", "\n\n", t)
    parts = re.split(r"(<pre>.*?</pre>|<code>.*?</code>)", t, flags=re.S)
    for i in range(0, len(parts), 2): parts[i] = re.sub(r"(?<!\n)\n(?!\n)", "\n\n", parts[i])   # پاراگراف‌ها همیشه با خط خالی از هم جدا می‌شوند
    t = "".join(parts)
    blocks, seen, keep = t.split("\n\n"), set(), []
    for b in blocks:
        k = re.sub(r"<[^>]+>", " ", b); k = re.sub(r"[\s‌]+", " ", k).strip().lower()
        if k and k in seen: continue   # پاراگراف تکراری (متن یکسان) حذف می‌شود
        if k: seen.add(k)
        keep.append(b)
    t = "\n\n".join(keep).strip()
    t = re.sub(r'[\s"\'\\,\[\]{}]+$', '', t)
    return t
def strip_source_url(t, url):
    """قانون ثابت: لینک منبع هرگز نباید داخل متن پست دیده شود — هر اشاره‌ای به دامنه‌ی منبع (لینک خام یا <a>) حذف می‌شود؛ بقیه‌ی لینک‌ها دست‌نخورده می‌مانند."""
    if not t or not url: return t
    host = re.sub(r"^[a-zA-Z]+://(www\.)?", "", str(url)).split("/")[0].strip().lower()
    if not host or "." not in host: return t
    h = re.escape(host)
    t = re.sub(r'<a href="[^"]*' + h + r'[^"]*"[^>]*>.*?</a>', " ", t, flags=re.I | re.S)
    t = re.sub(r"https?://[^\s<>\"']*" + h + r"[^\s<>\"']*", " ", t, flags=re.I)
    t = re.sub(r"(?m)^[ \t]+$", "", t)
    return t
def finish_ok(t):
    """اگر متن ناگهان وسط جمله قطع شده باشد، نشانه‌ی ادامه (« …») می‌گذارد — جمله‌ی تمام‌شده دست نمی‌خورد."""
    if not t: return t
    e = re.sub(r"(</[a-zA-Z]+>|\s)+$", "", t)
    if e and re.search(r"[\w؀-ۿ،,؛:]$", e): return t.rstrip() + " …"
    return t
def split_html(text, limit=MSG_LIMIT):
    if len(text) <= limit: return [text]
    chunks, cur = [], ""
    for para in text.split("\n"):
        if len(cur) + len(para) + 1 > limit: chunks.append(sanitize_html(cur)); cur = para
        else: cur = f"{cur}\n{para}" if cur else para
    if cur: chunks.append(sanitize_html(cur))
    return chunks
def preview_text(html_text, n=100):
    t = re.sub(r"\s+", " ", strip_tags(html_text).replace("\n", " ")).strip()
    if len(t) <= n: return html.escape(t)
    cut = t[:n]; sp = cut.rfind(" "); return html.escape(cut[:sp] if sp > n * 0.6 else cut) + " …"
def headline_of(html_text):
    first = (html_text or "").strip().split("\n", 1)[0]; return sanitize_html(first)[:900]
# ============================================================
# کشف مقاله — فید (RSS/Atom/RDF) → سایت‌مپ → لینک‌های HTML ؛ آدرس فید پیدا‌شده کش می‌شود
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
    """رسانه‌ی نامرتبط (لوگو، آواتار، بنر، پیکسل شفاف…) نباید به‌عنوان تصویر مقاله فرستاده شود."""
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
    """بایت‌های پاسخ → آیتم‌ها (فید یا سایت‌مپ) یا None"""
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
# --- منابع API (برای سایت‌هایی که مدیر خودش API می‌دهد) — نقشه‌بردار عمومی: هر ساختار JSON را می‌فهمد
API_ARRAY_KEYS = ("articles", "items", "results", "data", "posts", "news", "response", "docs", "entries", "stories", "hits", "records", "list", "feed")
def _api_pick_list(j, depth=0):
    """آرایه‌ی مقالات را در هر ساختار JSON پیدا می‌کند (NewsAPI، GNews، WordPress، Strapi، سرویس‌های سفارشی…)."""
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
        out.append({"url": u, "title": re.sub(r"\s+", " ", title)[:300], "published": pd.isoformat() if pd else None, "html": body if "<" in body else html.escape(body), "media": media})
        if len(out) >= limit: break
    out.sort(key=lambda x: x["published"] or "", reverse=True); return out
def _has_api(src):
    try: return bool(src["api_url"])
    except Exception: return False
async def _api_discover(src, limit):
    """کلید API هم داخل آدرس ({key}) و هم در هدرهای رایج فرستاده می‌شود تا با اکثر سرویس‌ها بی‌تنظیمِ اضافه کار کند."""
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
    """خروجی: (items, changed, method) — method: api | feed | sitemap | html ؛ changed=False یعنی 304 (بدون تغییر)"""
    cond = {}
    if src["etag"]: cond["If-None-Match"] = src["etag"]
    if src["last_modified"]: cond["If-Modified-Since"] = src["last_modified"]
    try:
        if _has_api(src): return await _api_discover(src, limit)
        if src["feed_url"] and use_cache:
            r = await _get(src["feed_url"], cond, feed=True)
            if r.status_code == 304: source_ok(src["id"], src["feed_url"], src["etag"], src["last_modified"]); return [], False, "feed"
            if r.status_code == 200:
                items = _parse_any(r.content, src["feed_url"], limit)
                if items: source_ok(src["id"], src["feed_url"], r.headers.get("etag"), r.headers.get("last-modified")); return items, True, "sitemap" if b"<urlset" in r.content[:4096].lower() else "feed"
        r = await _get(src["url"], feed=False)
        if r.status_code != 200: raise FetchError(r.status_code, src["url"])
        items = _parse_any(r.content, src["url"], limit)
        if items: source_ok(src["id"], src["url"], r.headers.get("etag"), r.headers.get("last-modified")); return items, True, "feed"
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
                if items: source_ok(src["id"], su); return items, True, "sitemap"
            elif b"<sitemapindex" in head:
                kids = re.findall(r"<sitemap>.*?<loc>\s*(.*?)\s*</loc>", rr.content.decode("utf-8", "ignore"), re.S)
                pref = [k for k in kids if re.search(r"news|post|article|blog|\d{4}", k, re.I)] or kids
                for ku in pref[-2:]:
                    try: rk = await _get(html.unescape(ku), feed=True)
                    except Exception: continue
                    if rk.status_code == 200 and b"<urlset" in rk.content[:4096].lower():
                        items = _sitemap_items(rk.content.decode("utf-8", "ignore"), limit)
                        if items: source_ok(src["id"], html.unescape(ku)); return items, True, "sitemap"
        items = _html_links(soup, src["url"], limit); source_ok(src["id"]); return items, True, "html"
    except Exception as e: source_fail(src["id"], e); raise
def _probe_status(e):
    """کد وضعیت HTTP را از هر خطایی که بالا آمده بیرون می‌کشد (۰ اگر HTTP نبود)."""
    st = getattr(e, "status", None)
    if isinstance(st, int): return st
    r = getattr(e, "response", None); st = getattr(r, "status_code", None)
    return int(st) if isinstance(st, int) else 0
async def probe_source(src, lang="fa", added=False):
    """تستِ بارگذاریِ منبع؛ خروجی: (ok, متنِ پاپ‌آپ). هر شکستی ⇒ منبع 🔴 خاموش می‌شود و دلیلِ کوتاه اعلام می‌گردد."""
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
# استخراج متن مقاله — trafilatura → بلوک‌های HTML → محتوای فید (در ترد جدا تا حلقه‌ی رویداد مسدود نشود)
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
    """ویدیو (og:video / <video>) → تصویر (og:image / twitter / link / JSON-LD / بزرگ‌ترین تصویر متن). لوگو و آواتار و پیکسل رد می‌شوند."""
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
    """کل متن صفحه، نه فقط ابتدای آن: همه‌ی بلوک‌های محتوایی با هم ادغام می‌شوند (پاراگراف، بولت، زیرتیتر) و تکراری‌ها حذف می‌شوند."""
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
    """صفحه‌ی بعدی مقالات چندصفحه‌ای (فقط rel=next که استاندارد و بی‌خطر است)."""
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
    """چسباندن متن صفحه‌ی بعدی بدون تکرار پاراگراف‌ها."""
    seen = {p.strip()[:90] for p in a.split("\n\n") if p.strip()}; out = [a]
    for p in b.split("\n\n"):
        k = p.strip()[:90]
        if len(k) < 20 or k in seen: continue
        seen.add(k); out.append(p.strip())
    return "\n\n".join(out)
async def extract_article(url, fallback_html=""):
    """کل متن خبر خوانده می‌شود: اگر مقاله چندصفحه‌ای باشد (rel=next) تا MAX_ARTICLE_PAGES صفحه دنبال و به هم دوخته می‌شود."""
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
# فیلتر تبلیغ — چندزبانه، منطبق با پرشمارترین زبان‌های کاربران تلگرام
AD_WORDS_BY_LANG = {
    "fa": ["رپورتاژ", "رپورتاژ آگهی", "تبلیغ", "آگهی", "اسپانسر", "کد تخفیف", "تخفیف ویژه", "همین حالا خرید", "خرید آنلاین", "تماس بگیرید", "شماره تماس", "سفارش دهید", "قیمت مناسب", "ارزان‌ترین", "بهترین قیمت", "فروش ویژه", "ثبت‌نام کنید", "ثبت نام کنید", "لینک خرید", "شرط‌بندی", "شرط بندی", "سایت شرط", "درآمد میلیونی", "وام فوری", "خرید فالوور", "مشاوره رایگان", "پیش‌فروش", "کلیک کنید"],
    "en": ["sponsored", "sponsored content", "advertorial", "promoted post", "affiliate", "buy now", "limited offer", "special offer", "discount code", "coupon code", "order now", "sign up now", "click here", "shop now", "best price", "giveaway", "casino", "betting"],
    "ru": ["реклама", "рекламный", "спонсор", "спонсируемый", "на правах рекламы", "скидка", "промокод", "купон", "казино", "ставки на спорт", "купить сейчас", "заказать сейчас", "акция"],
    "hi": ["विज्ञापन", "प्रायोजित", "छूट", "कूपन", "अभी खरीदें", "विशेष ऑफर"],
    "id": ["iklan", "bersponsor", "disponsori", "promo", "diskon", "kupon", "beli sekarang", "judi", "taruhan"],
    "pt": ["publicidade", "patrocinado", "patrocinada", "publieditorial", "desconto", "cupom", "compre agora", "oferta especial", "aposta", "cassino"],
    "es": ["publicidad", "patrocinado", "patrocinada", "publirreportaje", "descuento", "cupón", "compra ahora", "oferta especial", "apuestas", "casino"],
    "ar": ["إعلان", "ممول", "برعاية", "إعلان ممول", "خصم", "كوبون", "اشتر الآن", "عرض خاص", "كازينو", "مراهنات"],
    "tr": ["reklam", "sponsorlu", "sponsor", "indirim", "kupon", "hemen satın al", "kampanya", "bahis", "kumar"],
    "uk": ["реклама", "спонсор", "знижка", "промокод", "купон", "купити зараз", "ставки", "казино"],
    "uz": ["reklama", "homiy", "chegirma", "kupon", "hozir xarid qiling", "tikish"],
    "ms": ["iklan", "tajaan", "ditaja", "diskaun", "kupon", "beli sekarang", "pertaruhan"],
    "vi": ["quảng cáo", "tài trợ", "được tài trợ", "giảm giá", "mã giảm giá", "mua ngay", "cá cược"],
    "zh": ["广告", "赞助", "赞助内容", "推广", "优惠券", "折扣", "立即购买", "博彩", "赌场"],
    "de": ["werbung", "gesponsert", "anzeige", "rabatt", "gutschein", "jetzt kaufen", "wetten"],
    "fr": ["publicité", "sponsorisé", "parrainé", "réduction", "code promo", "achetez maintenant", "paris sportifs", "casino"],
    "it": ["pubblicità", "sponsorizzato", "sconto", "codice sconto", "acquista ora", "scommesse"],
    "bn": ["বিজ্ঞাপন", "প্রচারিত", "ছাড়", "কুপন", "এখনই কিনুন"],
    "th": ["โฆษณา", "ผู้สนับสนุน", "ส่วนลด", "คูปอง", "ซื้อเลย", "พนัน"],
}
AD_WORDS = sorted({w for ws in AD_WORDS_BY_LANG.values() for w in ws}, key=len, reverse=True)
AD_STRONG = ["رپورتاژ", "رپورتاژ آگهی", "sponsored", "sponsored content", "advertorial", "promoted post", "реклама", "на правах рекламы", "спонсируемый", "patrocinado", "patrocinada", "publirreportaje", "publieditorial", "bersponsor", "disponsori", "إعلان ممول", "برعاية", "sponsorlu", "gesponsert", "sponsorisé", "sponsorizzato", "प्रायोजित", "প্রচারিত", "ผู้สนับสนุน", "tajaan", "ditaja", "homiy", "赞助内容", "được tài trợ"]
def _wordset_re(words):
    """کلمات لاتین با مرز واژه (تا «ads» داخل کلمه‌ی دیگر شمرده نشود) و کلمات غیرلاتین به‌صورت زیررشته."""
    lat = [re.escape(w) for w in words if re.fullmatch(r"[\x20-\x7f]+", w)]; oth = [re.escape(w) for w in words if not re.fullmatch(r"[\x20-\x7f]+", w)]
    parts = ([r"\b(?:" + "|".join(lat) + r")\b"] if lat else []) + (["(?:" + "|".join(oth) + ")"] if oth else [])
    return re.compile("|".join(parts), re.I) if parts else None
AD_RE = _wordset_re(AD_WORDS); AD_STRONG_RE = _wordset_re(AD_STRONG)
AD_URL = re.compile(r"/(rpt|reportage|reportaj|sponsored|sponsor|ads?|advert|advertorial|promo|partner|pr-|press-release|reklama)[/-]", re.I)
def heuristic_ad_check(art, strict=False):
    """فیلتر نرم‌شده: یک کلمه‌ی معمولی به‌تنهایی خبر را رد نمی‌کند؛ فقط نشانه‌های قطعی (کلمات صریح تبلیغاتی، تلفن، انبوه لینک و قیمت) وزن جدی دارند."""
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
# پرامپت، تولید و ترکیب نهایی
def build_prompt(s, art, want_full):
    cats = "\n".join(f"- {c['emoji']} {c['name']}: {c['style']}" for c in s["categories"]) or "- General"; crit = "\n".join(f"- {c['name']} (weight {c['weight']})" for c in s["criteria"])
    system = f"""You are the editor-in-chief and content evaluator of a Telegram channel. Output language: {s['language']}. EVERY word of the output MUST be written in {s['language']}, regardless of any other instruction. Channel topic: {s['topic'] or 'general'}.
CHANNEL STYLE (editor's tone guide — apply it, but the FORMATTING RULES below ALWAYS win over it when they conflict):
{sanitize_html(s['prompt'])}
CATEGORIES (choose exactly one and apply its style):
{cats}
EVALUATION CRITERIA (score each 0–10, honestly and strictly):
{crit}
FORMATTING RULES (mandatory, not optional — these override any conflicting style guidance above):
- HUMAN VOICE: write like a skilled human editor, never like a bot or an AI. Vary sentence length, no meta commentary, no clichéd openings like "In today's world", and NEVER use divider lines like "---" or "***" or "⸻".
- EMOJI: at most ONE relevant emoji in the whole post, placed on the last line next to the hashtags; no emojis inside paragraphs or bullets.
- Line 1: headline inside <b>. Then a blank line, then a one-sentence lead.
- SYMBOLS: wherever a list, step, comparison or highlight helps, start the line with a symbol from this palette (pick 1–2 kinds per post and stay consistent): • ◦ ◆ ◇ ▸ ▹ ➤ ➜ ➥ ➢ → ➝ ⇢ ⟶ ⤷ — each such line is its own paragraph.
- Only these HTML tags (NO Markdown): <b>, <i>, <u>, <s>, <code>, <pre>, <a href="">, <blockquote>.
- MANDATORY: "post" MUST contain at least one <blockquote> wrapping the single most important sentence, quote or number of the news, placed naturally in the middle or near the end — never on line 1, never empty, and never around the whole text.
- MANDATORY: <b> for key terms, names and numbers (4–8 times per post). <i> only once or twice, for a short nuance or aside. <code> at most once and only for an exact figure/version/ticker/code — never for ordinary words. Never wrap a whole paragraph in <i>, <code> or <pre>.
- RTL: if the output language reads right-to-left (Persian, Arabic, …), open every paragraph and sentence with a word of that language, then place any English term after it; keep English runs short — long English runs scramble right-to-left text. A quoted English phrase in a blockquote may start with English.
- SITES: only when the story itself recommends a tool, service or website, state its name and its full URL in plain text; NEVER the article's own source or any news site — the source link is added by the system itself, not by you.
- PURE TEXT: "post" and "full" contain only the article itself — never scores, ratings, field names or JSON fragments; those live only in their own JSON fields.
- FORMAT CONTRACT: paragraphs are separated by ONE blank line; never end mid-sentence — finish the sentence or compress the story; plain words only (no 'quoted' terms, no [markdown](links)); a sale price, discount or original-price comparison in the story means is_ad=true.
- VARY THE SUBJECT: name the main person/thing once at first mention, then use pronouns or natural substitutes — never open every paragraph with the same name.
- UNKNOWN NAMES: a little-known person, company or term gets a one-clause introduction at first mention.
- NEUTRAL & SOURCE-ONLY: strictly neutral — no judgment, opinion, praise or personal analysis; never add or invent anything beyond the source; never pad to reach the cap — shorter is fine.
- "post": an engaging, COMPLETE mini-story — max {s['max_words']} words and at most {max(400, int(s['post_limit']) - 120)} characters; never leave the story half-told: if space is tight, compress the whole story instead of dropping its second half.{', ending with 2–4 relevant hashtags on the last line' if s['hashtags'] else ''}.
- "full": {'the EXPANDED bot version: everything the post says PLUS the deeper details, background, numbers and context — it must NOT merely repeat the post; start fresh and go deeper. Same format: <b> sub-headings, bullets, at least two <blockquote> highlights (300–700 words, max 2500 characters).' if want_full else 'null'}
- If the text is an advertisement / advertorial / product-for-sale / betting promotion: is_ad=true.
- No preamble, never talk about yourself.
REMINDER: the entire output — title, post, full, hashtags — must be in {s['language']} only.
Return ONLY one valid JSON object (no code fences) with exactly this structure:
{{"is_ad": false, "ad_reason": "", "category": "category name", "title": "headline", "scores": {{"criterion name": 0-10}}, "post": "HTML", "full": "HTML or null"}}"""
    text = art['text'][:AI_INPUT_TEXT_CHARS]; user = f"TITLE: {art['title']}\nSOURCE: {art['url']}\nDATE: {art.get('published') or 'unknown'}\n\nARTICLE TEXT:\n{text}"; return system, user
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
async def generate(s, art, on_queue=None, owner_id=None):
    """خروجی: (json, model_name, error_code) — error_code کلید امن است (هرگز متن خطای مدل یا base url)."""
    want_full = len(art["text"]) > 1200; system, user = build_prompt(s, art, want_full); raw, model, err = await ai_chat(system, user, on_queue=on_queue, owner_id=owner_id, validate=_validate_generation)
    if not raw: return None, None, err
    j = parse_json(raw)
    if not isinstance(j, dict):
        # پاکت JSON قابل تجزیه نبود → بازیابی متن واقعی از پاسخ خام (رفتار salvage قبلی حفظ می‌شود)
        j = {"is_ad": False, "category": s["categories"][0]["name"] if s["categories"] else "", "title": art["title"], "scores": {}, "post": clean_ai_text(salvage_post(raw), s)[:3000], "full": None}
    elif not str(j.get("post") or "").strip() and not j.get("is_ad"):
        j = {"is_ad": False, "category": s["categories"][0]["name"] if s["categories"] else "", "title": art["title"], "scores": {}, "post": clean_ai_text(salvage_post(raw), s)[:3000], "full": None}
    # تبلیغِ صریحِ مدل (حتی بدون post) هرگز با محتوای ساختگی بازنویسی نمی‌شود
    scores = j.get("scores")
    if not isinstance(scores, dict) or not scores:
        scores = None; j.pop("scores", None)
    j["score"] = weighted_score(s, scores) if scores else 65.0; return j, model, None
def signature_of(s, ch):
    sig = (s.get("signature") or "").strip()
    if sig.lower() == "@channel": sig = f"@{ch['username']}" if ch and ch["username"] else ""
    return sanitize_html(sig) if sig else ""
def make_tail(s, ch, url):
    """پایان‌بند پست کانال: فقط امضا — منبع هرگز در کانال نمایش داده نمی‌شود (فقط در «ادامه در ربات»، با اجازه‌ی مدیر)."""
    sig = signature_of(s, ch)
    return ("\n" + sig) if sig else ""
def ensure_quote(t):
    """اجبارِ quote: اگر مدل بلاک‌کوت نگذاشته باشد، یک پاراگراف مهمِ میانی خودکار داخل <blockquote> گذاشته می‌شود."""
    if not t or "<blockquote" in t.lower(): return t
    parts = str(t).split("\n\n")
    if len(parts) < 2: return t
    cand = [i for i in range(1, len(parts)) if 30 <= len(strip_tags(parts[i]).strip()) <= 500 and not parts[i].lstrip().startswith(("•", "#", "🔗", "<a", "<pre", "<code"))]
    if not cand: return t
    i = cand[len(cand) // 2] if len(cand) > 1 else cand[0]; parts[i] = f"<blockquote>{parts[i].strip()}</blockquote>"
    return "\n\n".join(parts)
def compose(s, ch, art, gen):
    post = sanitize_html(ensure_quote(clean_ai_text(salvage_post(gen.get("post") or ""), s)))
    full = clean_ai_text(salvage_post(gen["full"]), s) if gen.get("full") and str(gen["full"]).lower() != "null" else None
    if full: full = finish_ok(fit_html(sanitize_html(ensure_quote(full)), BOT_FULL_MAX)[0])
    core = re.sub(r"#[^\s#]+", " ", re.sub(r"<[^>]+>", " ", post)); core = re.sub(r"[\s‌]+", " ", core).strip()
    if len(core) < 120 and full and len(re.sub(r"<[^>]+>", " ", full)) >= 200:
        # پست تهی/یک‌خطی (فقط ایموجی و امضا): آغاز نسخه‌ی کامل به‌عنوان پست کانال ساخته می‌شود تا کانال هرگز خالی نماند
        txt = re.sub(r"</?[a-z][^>]*>", " ", full); sen = re.split(r"(?<=[.!?؟…])\s+", txt); acc = ""
        cap = max(300, int(s["post_limit"]) - 160)
        for x in sen:
            if acc and len(acc) + len(x) + 1 > cap: break
            acc += (" " if acc else "") + x
        if len(acc) >= 120: post = sanitize_html(ensure_quote(acc + " …"))
    return post + make_tail(s, ch, art["url"]), full
# ============================================================
# رسانه و انتشار
def _media_headers(media):
    """Referer دامنه‌ی خبر: بسیاری از سایت‌ها بدون آن به تصویر و ویدیو پاسخ ۴۰۳ می‌دهند (علت اصلی «عکس برداشت نمی‌شود»)."""
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
    """دانلود جریانی تا سقف MAX_MEDIA_MB (پیش‌فرض ۵۰ مگابایت = سقف آپلود ربات‌های تلگرام). اگر نوبت اول رد شد، یک‌بار با هدر دیگری دوباره تلاش می‌شود."""
    if not media or not media.get("url"): return None
    if not await asyncio.to_thread(public_url, media["url"]): return None
    for hdr in (_media_headers(media), {"User-Agent": UA_FEED, "Accept": "*/*"}):
        tmp = None; path = None
        try:
            async with FETCH_SEM:
                async with http().stream("GET", media["url"], headers=hdr, timeout=httpx.Timeout(180, connect=15)) as r:
                    if r.status_code != 200: continue
                    ct = r.headers.get("content-type", "").lower()
                    if ct.startswith("text/") or "html" in ct: return None
                    try:
                        if int(r.headers.get("content-length") or 0) > MAX_MEDIA_BYTES: log.info(f"media skipped (> {MAX_MEDIA_MB}MB)"); return None
                    except Exception: pass
                    kind = "animation" if "gif" in ct else "photo" if ct.startswith("image/") else "video" if ct.startswith("video/") else _ext_kind(media["url"], media.get("kind") or "document")
                    ext = {"photo": ".jpg", "animation": ".gif", "video": ".mp4"}.get(kind, os.path.splitext(urlparse(media["url"]).path)[1] or ".bin")
                    tmp = tempfile.NamedTemporaryFile(delete=False, suffix=ext); size = 0
                    try:      # فایل موقت در هیچ مسیری (خطا، سقف حجم، فایل ناقص) روی دیسک جا نمی‌ماند
                        async for chunk in r.aiter_bytes(262144):
                            size += len(chunk)
                            if size > MAX_MEDIA_BYTES: log.info(f"media skipped (> {MAX_MEDIA_MB}MB)"); return None
                            tmp.write(chunk)
                    finally:
                        tmp.close()
                    if size < 1024: return None
                    if kind == "photo" and size > 10 * 1024 * 1024: kind = "document"
                    path = tmp.name
        except Exception as e:
            log.warning(f"media: {e}"); path = None
        except BaseException:
            path = None
            raise
        finally:
            if tmp is not None and path is None:   # مالکیت فایل فقط پس از خروج سالم از استریم منتقل می‌شود
                try: os.unlink(tmp.name)
                except OSError: pass
        if path: return path, kind
    return None
def _is_parse_err(e): s = str(e).lower(); return "parse" in s or "entit" in s or "tag" in s or "unsupported start" in s
async def _send_media(bot, chat_id, caption, pm, media):
    """رسانه با کپشن؛ ابتدا با URL، سپس دانلود و آپلود. None ⇒ رسانه قابل ارسال نیست (متن تنها فرستاده می‌شود)."""
    kind = media.get("kind", "photo"); mf = media.get("_file")
    if not mf and kind == "photo":
        try: return await bot.send_photo(chat_id, media["url"], caption=caption, parse_mode=pm)
        except BadRequest as e:
            if _is_parse_err(e): raise
        except (NetworkError, RetryAfter, Forbidden): raise
        except Exception: raise
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
    except (NetworkError, Forbidden): raise
    except Exception:
        raise
async def send_post(bot, chat_id, text, media=None):
    """کپشن ≤۱۰۲۴ → رسانه+کپشن · متن بلندتر → رسانه با تیتر و سپس متن · خطای پارس → تنزل تدریجی فرمت (معمولی → ساده)."""
    variants = [(text, "HTML"), (downgrade_html(text), "HTML"), (strip_tags(text), None)]
    sent_media = SimpleNamespace(message_id=media["_sent_id"]) if media and media.get("_sent_id") else None
    for i, (t, pm) in enumerate(variants):
        try:
            if media:
                cap_ok = len(t) <= CAPTION_LIMIT; cap = t if cap_ok else (headline_of(t) if pm else strip_tags(headline_of(t)))
                if isinstance(bot, PublicationTransport): bot.caption_complete = cap_ok
                m = sent_media or await _send_media(bot, chat_id, cap, pm, media)
                if m:
                    if not sent_media:
                        sent_media = m
                        if cap_ok: return m
                    return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True, reply_to_message_id=m.message_id)
            return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True)
        except RetryAfter as e:
            await asyncio.sleep(min(30, float(e.retry_after) + 1)); return await bot.send_message(chat_id, t, parse_mode=pm, disable_web_page_preview=True, **({"reply_to_message_id": sent_media.message_id} if sent_media else {}))
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
async def publish_article(bot, aid, count_usage=True, test_user=None):
    a = get_article(aid)
    if not a: return False, "not_ready"
    async with ch_lock(a["channel_id"]):
        return await _publish_article_locked(bot, aid, count_usage, test_user)

async def _publish_article_locked(bot, aid, count_usage=True, test_user=None):
    a = get_article(aid)
    if not a or a["status"] != "ready" or not a["post_html"]: return False, "not_ready"
    ch = get_channel(a["channel_id"]); admin_id = a["admin_id"]
    if not ch: return False, "no_channel"
    operation_checkpoint()
    journal = get_pub_journal(aid)
    if journal and (journal.get("link") or journal.get("phase") == "ack"):
        link = journal.get("link") or msg_link(ch, SimpleNamespace(message_id=journal["message_id"]))
        settle_publication(aid, ch, journal)
        return True, link
    if journal:
        journal = release_publication(aid, journal, "delivery_unknown" if journal.get("phase") == "in_flight" else (a["reason"] or ""))
        if journal.get("phase") == "in_flight": return False, "delivery_unknown"
    if ch["admin_id"] != admin_id: return False, "no_channel"
    if posted_before(ch["chat_id"], a["hash"]): return False, "duplicate"
    journal = reserve_publication(aid, admin_id, count_usage, test_user, journal)
    if journal is None: return False, "quota"
    media = None; published = False
    try:
        s = get_settings(ch["id"]); lang = s["ui_lang"]
        if not await bot_can_post(bot, ch["chat_id"]):
            article_update(aid, reason="bot_not_admin"); return False, "bot_not_admin"
        operation_checkpoint()
        if posted_before(ch["chat_id"], a["hash"]):
            article_update(aid, reason="duplicate"); return False, "duplicate"
        media = json.loads(a["media"]) if a["media"] and s["include_media"] else None
        tail = make_tail(s, ch, a["url"]); post = re.sub(r'\s*🔗 <a href="[^"]+">Source</a>\s*', "\n", a["post_html"] or ""); post = clean_ai_text(strip_source_url(post, a["url"]), s); body = post[:-len(tail)] if tail and post.endswith(tail) else post; text = post; limit = int(s["post_limit"])
        if len(post) > limit:
            cut, rest = split_post_html(body, max(200, limit - len(tail) - 100 - len(BOT_USERNAME)))
            htitle = f"<b>{html.escape(a['title'] or '')}</b>"
            cfull = clean_ai_text(strip_source_url(a["full_html"], a["url"]), s) if source_bot_ok(a["source_id"]) and a["full_html"] else ""
            ftxt = cfull if cfull.strip() else ((htitle + "\n\n" + rest) if rest else htitle)
            if len(ftxt) > BOT_FULL_MAX: ftxt = fit_html(ftxt, BOT_FULL_MAX)[0]
            ftxt = finish_ok(ftxt)
            key = await store_deeplink(admin_id, {"short": cut, "full": ftxt, "title": a["title"], "url": a["url"], "show_source": bool(s.get("include_link", True)), "media": {k: v for k, v in media.items() if not k.startswith("_")} if media else None, "ts": now_iso()})
            more = f'\n\n<a href="https://t.me/{BOT_USERNAME}?start=r_{key}">📖 {"بیشتر" if lang == "fa" else "more..."}</a>'
            text = cut + more + tail
        if journal.get("media_id"):
            text = journal["text"]
            media = {"_sent_id": journal["media_id"]}
        elif media and media.get("kind") != "photo": media["_file"] = await download_media(media)
        journal["text"] = text
        set_pub_journal(aid, journal)
        operation_checkpoint()
        parent = asyncio.current_task()
        async def commit_send():
            nonlocal published
            operation_checkpoint()
            if parent.cancelling(): raise asyncio.CancelledError
            try: msg = await send_post(PublicationTransport(bot, aid, journal, parent), ch["chat_id"], text, media)
            except Exception as e:
                if journal.get("phase") == "ack":
                    published = True
                    raise
                article_update(aid, reason="delivery_unknown" if journal.get("phase") == "in_flight" else f"send: {str(e)[:120]}")
                log.exception("publication failed article=%s channel=%s", aid, ch["id"])
                return False, f"send_failed:{str(e)[:120]}"
            published = True
            op = _current_operation.get()
            if op: op.published_count += 1
            link = msg_link(ch, msg)
            journal.update(phase="ack", link=link)
            set_pub_journal(aid, journal)
            settle_publication(aid, ch, journal)
            log_event("INFO", f"منتشر شد در {ch['title']}: {(a['title'] or '')[:60]}", admin_id)
            return True, link
        sending = asyncio.create_task(commit_send(), name=f"publication:{aid}")
        try: return await asyncio.shield(sending)
        except asyncio.CancelledError:
            # Keep the channel locked until an in-flight delivery has settled, even on repeated cancellation.
            while not sending.done():
                try: await asyncio.shield(sending)
                except asyncio.CancelledError: continue
                except Exception: break
            if not sending.cancelled():
                try: sending.result()
                except Exception: log.exception("publication settlement failed article=%s", aid)
            raise
    except asyncio.CancelledError:
        if not published: article_update(aid, reason="delivery_unknown" if journal.get("phase") == "in_flight" else "cancelled")
        raise
    finally:
        try:
            if not published and journal.get("phase") != "ack":
                current = get_article(aid)
                release_publication(aid, journal, current["reason"] if current else "")
        finally:
            if media and media.get("_file"):
                try: os.unlink(media["_file"][0])
                except OSError: log.debug("media cleanup failed", exc_info=True)
# ============================================================
# تشخیص مرحله‌ای (Diagnostics) — کوتاه، نمادین، دوزبانه
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
    """نام منبعِ تولیدکننده‌ی یک مقاله (برای نمایش به مدیر در تست فوری و چرخه‌ی خودکار)."""
    a = get_article(aid); src = source_of_article(a) if a else None
    return ((src["title"] or "").strip() or hostname(src["url"])) if src else ""
# ============================================================
# چرخه‌ی یک کانال (قفل هر کانال + سقف چرخه‌های هم‌زمان)
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
    # --- کشف (منابع به‌صورت هم‌زمان، محدود با FETCH_SEM)
    D.stage = "discover"; await p(10, P["src"].format(n=len(sources)))
    async def one(src):
        name = hostname(src["url"]); lf = parse_dt(src["last_fetch"])
        if not test_mode and lf and (now_utc() - lf) < timedelta(minutes=SOURCE_COOLDOWN_MIN): return src, name, None, False, "", "cooldown"
        try: items, changed, method = await discover_source(src, use_cache=not test_mode); return src, name, items, changed, method, None
        except Exception as e: return src, name, None, False, "", str(e)[:80]
    results = await asyncio.gather(*[one(src) for src in sources])
    leftovers = q("SELECT id,url,title,published_at FROM articles WHERE channel_id=? AND status='discovered' AND source_id IN (SELECT id FROM sources WHERE active=1 AND channel_id=articles.channel_id) ORDER BY id DESC LIMIT 10", (cid,))
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
    # --- پردازش (استخراج ۳تایی هم‌زمان، تولید ترتیبی تا رسیدن به هدف)
    quiet = in_quiet(s); cnt = {"extract": 0, "undated": 0, "ad": 0, "ai_ad": 0, "low": 0}; best = 0.0; details = []; ai_err = None; i = 0; stop = False
    # مانده‌ی صف ready از چرخه‌های قبلی اول منتشر می‌شود تا FIFO حفظ شود؛ داخل سقف همان چرخه (posts_per_cycle) و فقط در حالت خودکار خارج از خاموشی
    drained = 0
    if not test_mode and s["mode"] == "auto" and not quiet:
        backlog = [r["id"] for r in articles_by_status(cid, "ready", 50, automatic=True)]
        rem_now = remaining(uid, "posts")
        if backlog and (rem_now is None or rem_now > 0):
            D.add("leftover", n=len(backlog)); D.stage = "publish"
            for aid_b in backlog:
                if (rem_now is not None and rem_now <= 0) or res["published"] >= target: break
                try:
                    ok, out = await _publish_article_locked(bot, aid_b, count_usage=True)
                except asyncio.CancelledError:
                    a_b = get_article(aid_b)
                    if a_b and a_b["status"] == "ready": article_update(aid_b, reason="cancelled")
                    raise
                if ok:
                    res["published"] += 1; res["links"].append(out); res["pub"].append(((get_article(aid_b)["title"] or "")[:60], article_src_name(aid_b), out))
                    rem_now = None if rem_now is None else rem_now - 1; drained += 1
                elif out != "duplicate":
                    break
    target -= drained
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
            # هر نامزد (کشف‌شده، مانده‌ی صف یا تلاش مجدد) بلافاصله پیش از تولید دوباره با پنجره‌ی زمانی سنجیده می‌شود
            pub_when = art.get("published") or c.get("published")
            if not _within_lookback(pub_when, s):
                article_update(aid, status="skipped", reason="old" if pub_when else "undated", **({"published_at": pub_when} if pub_when else {}))
                if not pub_when: cnt["undated"] += 1
                continue
            bad, why, _ = heuristic_ad_check(art, s["strict_ads"])
            if bad: article_update(aid, status="rejected", reason=f"ad_filter: {why}"); res["rejected"] += 1; cnt["ad"] += 1; details.append((art["title"], "ad: " + why)); continue
            D.stage = "ai"; pct = min(94, 40 + int(50 * i / len(candidates))); await p(pct, P["ai"].format(t=art["title"][:40]))
            async def _on_queue(_pct=pct): await p(_pct, P["queue"])
            gen, model, err = await generate(s, art, on_queue=_on_queue, owner_id=uid)
            if not gen: article_update(aid, status="failed", reason=f"ai: {err}"); res["errors"] += 1; ai_err = err; continue
            D.stage = "score"
            if gen.get("is_ad"): article_update(aid, status="rejected", reason=f"ai_ad: {gen.get('ad_reason', '')}", score=gen["score"]); res["rejected"] += 1; cnt["ai_ad"] += 1; details.append((art["title"], f"AI ad: {str(gen.get('ad_reason', ''))[:40]}")); continue
            best = max(best, gen["score"])
            if gen["score"] < float(s["min_score"]): article_update(aid, status="rejected", reason=f"score {gen['score']} < {s['min_score']}", score=gen["score"]); res["rejected"] += 1; cnt["low"] += 1; details.append((art["title"], f"score {gen['score']}")); continue
            post, full = compose(s, ch, art, gen)
            article_update(aid, title=gen.get("title") or art["title"], post_html=post, full_html=full, score=gen["score"], category=gen.get("category"), model=model, media=json.dumps(art["media"]) if art["media"] else None, published_at=art["published"], status="ready", reason=""); res["accepted"] += 1
            sname = article_src_name(aid)
            if sname: res["src"] = sname; D.add("from_src", name=sname)
            if test_mode or (s["mode"] == "auto" and not quiet):
                D.stage = "publish"
                try:
                    await p(96, P["pub"])
                    ok, out = await _publish_article_locked(bot, aid, count_usage=not test_mode, test_user=uid if test_mode else None)
                except asyncio.CancelledError:
                    a = get_article(aid)
                    if a and a["status"] == "ready": article_update(aid, reason="cancelled")
                    raise
                if ok:
                    res["published"] += 1; res["links"].append(out); res["pub"].append(((gen.get("title") or art["title"] or "")[:60], sname, out))
                else:
                    res["errors"] += 1; D.add("pub_fail", err=_pub_err(out, lang))
                    if out == "bot_not_admin": D.hint("hint_admin"); stop = True; break
            else: res["queued"] += 1
    # --- جمع‌بندی
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
async def run_admin_cycle(bot, uid, test_mode=False, progress=None):
    out = {}
    for ch in list_channels(uid):
        try: out[ch["id"]] = await run_channel_cycle(bot, uid, ch["id"], test_mode, progress)
        except Exception as e: log_event("ERROR", f"چرخه کانال {ch['title']}: {e}", uid)
    return out
async def flush_ready(bot, uid, cid, max_n=2):
    lk = ch_lock(cid)
    if lk.locked(): return 0
    async with lk:
        s = get_settings(cid); ch = get_channel(cid)
        if not ch or ch["admin_id"] != uid or not admin_limits(uid)["active"]: return 0
        if s["mode"] != "auto" or in_quiet(s) or not s["enabled"]: return 0
        rem = remaining(uid, "posts"); sent = 0
        for a in articles_by_status(cid, "ready", max_n, automatic=True):
            if rem is not None and rem <= 0: break
            operation_checkpoint()
            ok, out = await _publish_article_locked(bot, a["id"])
            if ok: sent += 1; rem = None if rem is None else rem - 1
            elif out != "duplicate": break
        return sent
# ============================================================
# زمان‌بند هوشمند: عادلانه (قدیمی‌ترین اجرا اول)، سقف چرخه در هر تیک، توقف وقتی هیچ مدلی در دسترس نیست
_tick_lock = asyncio.Lock()
async def _plan_notifications():
    global SCHED_NOTIF_FAILURES
    for uid, p, exp in activate_next_plans():
        lang = user_lang(uid) or "fa"; name = html.escape(plan_txt(p, "name", lang)); d = fmt_date(exp, admin_offset(uid))
        await notify_user(uid, f"🎉 پلن بعدی «<b>{name}</b>» فعال شد · تا {d}\n/create" if lang == "fa" else f"🎉 Next plan “<b>{name}</b>” is now active · until {d}\n/create")
    SCHED_NOTIF_FAILURES = True
    try:
        for u, key, left in expiring_users():
            if u["next_plan_id"]: continue
            lang = u["lang"] or "fa"; p = get_plan(u["plan_id"]); name = html.escape(plan_txt(p, "name", lang)) if p else "—"
            # کلید در DB رزرو شده؛ اگر ارسال واقعاً ناموفق باشد، claim آزاد می‌شود تا تیک بعدی دوباره تلاش کند
            try:
                await notify_user(u["id"], (f"⏳ پلن «{name}» حدود <b>{int(left)} ساعت</b> دیگر تمام می‌شود." if lang == "fa" else f"⏳ Plan “{name}” ends in about <b>{int(left)}h</b>."), [[("🔄 تمدید / ارتقا" if lang == "fa" else "🔄 Renew / Upgrade", "u:plans")]])
            except Exception:
                q("UPDATE users SET remind_key=NULL WHERE id=? AND remind_key=?", (u["id"], key), commit=True)
    finally:
        SCHED_NOTIF_FAILURES = False
    for u in q("SELECT * FROM users WHERE plan_id IS NOT NULL AND plan_expires<=? AND next_plan_id IS NULL AND (remind_key IS NULL OR remind_key!='expired') AND banned=0", (now_iso(),)):
        q("UPDATE users SET remind_key='expired' WHERE id=?", (u["id"],), commit=True); lang = u["lang"] or "fa"
        await notify_user(u["id"], ("🔴 <b>پلن شما تمام شد؛ انتشار خودکار متوقف است.</b>" if lang == "fa" else "🔴 <b>Your plan expired; automatic publishing is paused.</b>"), [[("🔄 تمدید / ارتقا" if lang == "fa" else "🔄 Renew / Upgrade", "u:plans")]])
async def _report_failed_cycle(uid, ch, s, res):
    """چرخه‌ی زمان‌بندی‌شده چیزی منتشر نکرد → یک بار (تا ۲۴ ساعت برای همان الگو) به مدیر اطلاع بده."""
    D = res["diag"]; fp = "|".join(D.keys()); last = (s.get("last_notified_diag") or "").split("@"); last_fp, last_ts = last[0], (parse_dt(last[1]) if len(last) > 1 else None)
    if fp == last_fp and last_ts and (now_utc() - last_ts) < timedelta(hours=24): return
    update_settings(ch["id"], last_notified_diag=f"{fp}@{now_iso()}"); lang = s["ui_lang"]
    head = f"⚠️ <b>{'چرخه بدون انتشار' if lang == 'fa' else 'Cycle published nothing'}</b> · 📢 {html.escape(ch['title'])}\n\n"
    await notify_user(uid, head + html.escape(D.render(lang)), [[("🛠 پنل کانال" if lang == "fa" else "🛠 Channel panel", f"a:ch:{ch['id']}")]])
async def _report_published(uid, ch, s, res):
    """چرخه‌ی خودکار منتشر کرد → یک پیام کوتاه با نام منبعِ هر پست (یک پیام برای کل چرخه، نه برای هر پست)."""
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
        if not any(any_model_available(uid) for _, uid, _, _ in due): log_event("WARN", f"{len(due)} کانال در انتظار؛ هیچ مدل AI در دسترس نیست"); return
        due.sort(key=lambda x: x[0]); batch = due[:MAX_CYCLES_PER_TICK]
        gset("last_cycle_start", now_iso()); await asyncio.gather(*[_scheduled(bot, uid, ch, s) for _, uid, ch, s in batch]); gset("last_cycle_end", now_iso())
# ============================================================
# گزارش (دوزبانه، فشرده)
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
# ---------- پایان لایه‌ی موتور (چرخه، زمان‌بند، گزارش) ----------
# ============================================================
# رابط کاربری تلگرام (دوزبانه، فشرده)
# ============================================================
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, BotCommand
from telegram.constants import ParseMode, ChatType
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, ContextTypes, filters
HTML = ParseMode.HTML
APP: Application = None
# ============================================================
# دیکشنری دوزبانه‌ی رابط کاربری  (fa, en)
TXT = {
    "back": ("🔙 بازگشت", "🔙 Back"), "home": ("🏠 خانه", "🏠 Home"), "cancel": ("❌ انصراف", "❌ Cancel"), "cancelled": ("↩️ لغو شد", "↩️ Cancelled"),
    "saved": ("✅ ذخیره شد", "✅ Saved"), "deleted": ("🗑 حذف شد", "🗑 Deleted"), "on": ("روشن", "on"), "off": ("خاموش", "off"), "yes": ("✅ بله", "✅ Yes"), "no": ("❌ خیر", "❌ No"),
    "send_value": ("مقدار را بفرستید", "Send the value"), "step": ("🧩 <b>{i}/{n}</b>", "🧩 <b>{i}/{n}</b>"), "need_int": ("⚠️ عدد بفرستید", "⚠️ Send a number"), "empty": ("⚠️ خالی است", "⚠️ Empty"),
    "range": ("⚠️ بازه‌ی مجاز: {lo}–{hi}", "⚠️ Allowed range: {lo}–{hi}"), "notfound": ("❌ یافت نشد", "❌ Not found"), "error": ("❌ {e}", "❌ {e}"),
    "choose_lang": ("🌐 <b>زبان / Language</b>", "🌐 <b>زبان / Language</b>"), "lang_set": ("✅ فارسی", "✅ English"), "banned": ("⛔ دسترسی مسدود است", "⛔ Access blocked"),
    "lang_set_n": (" · {n} کانال هم‌زبان شد", " · {n} channel(s) relocalized"),
    "busy_click": ("⏳ کمی آهسته‌تر", "⏳ Slow down a bit"),
    # ---- کاربر / پلن
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
    # ---- پنل مدیر
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
    # ---- پنل کانال
    "ch_panel": ("📣 <b>{title}</b>", "📣 <b>{title}</b>"), "ch_status": ("{i} اتوماسیون {st} · {mode}", "{i} Automation {st} · {mode}"), "auto": ("⚡ خودکار", "⚡ auto"), "review": ("📝 بازبینی", "📝 review"),
    "ch_stats": ("🌐 {s} منبع · 📝 صف {q} · ✅ ۲۴h {p} · ♻️ رد {r} · 🕐 {a}", "🌐 {s} sources · 📝 queue {q} · ✅ 24h {p} · ♻️ rejected {r} · 🕐 {a}"),
    "report": ("📊 گزارش", "📊 Report"), "test": ("🧪 تست فوری", "🧪 Quick test"), "sources": ("🌐 منابع ({n})", "🌐 Sources ({n})"), "content": ("✍️ محتوا", "✍️ Content"), "sched": ("⏰ زمان‌بندی", "⏰ Schedule"),
    "queue": ("📝 صف انتشار ({n})", "📝 Publish queue ({n})"), "rejected": ("♻️ ردشده‌ها", "♻️ Rejected"), "automation": ("{i} اتوماسیون", "{i} Automation"), "lock": ("🔐 کد قفل", "🔐 Lock code"), "ch_del": ("🗑 حذف کانال", "🗑 Remove channel"),
    "refresh": ("🔄 بروزرسانی", "🔄 Refresh"), "ch_del_q": ("❓ «{title}» با منابع، تنظیمات و صف حذف شود؟", "❓ Remove “{title}” with its sources, settings and queue?"), "ch_deleted": ("🗑 کانال حذف شد", "🗑 Channel removed"),
    "tog_enabled": ("🟢 اتوماسیون روشن شد", "🟢 Automation on"), "tog_disabled": ("🔴 اتوماسیون خاموش شد", "🔴 Automation off"),
    "lock_text": ("🔐 <b>کد قفل «{title}»</b>\n\nاگر کسی بخواهد این کانال را در پنل خود ثبت کند باید این کد را بدهد؛ وگرنه رد می‌شود و به شما خبر می‌رسد.\n\n🔑 <code>{code}</code>\n\n⚠️ محرمانه نگه دارید؛ در صورت لو رفتن بازتولید کنید.", "🔐 <b>Lock code of “{title}”</b>\n\nAnyone trying to register this channel in their panel must enter this code; otherwise it's rejected and you're notified.\n\n🔑 <code>{code}</code>\n\n⚠️ Keep it secret; regenerate if leaked."),
    "lock_regen": ("🔁 بازتولید", "🔁 Regenerate"), "lock_regen_ok": ("✅ کد جدید صادر شد", "✅ New code issued"),
    # ---- منابع
    "src_title": ("🌐 <b>منابع — {title}</b> · {n}/{cap}\n💡 بهترین نتیجه با سایت‌هایی است که <b>RSS</b> دارند؛ آدرس فید یا خود سایت را بدهید (ربات فید/سایت‌مپ را خودش پیدا می‌کند).\nستون اول = محتوای کانال · ستون دوم = محتوای ربات", "🌐 <b>Sources — {title}</b> · {n}/{cap}\n💡 Best results with sites that have <b>RSS</b>; give the feed or the site URL (the bot finds feed/sitemap itself).\nFirst mark = channel content · second = bot content"),
    "src_line": ("\n{i}{b} {host} · 🆕 {n}{err}", "\n{i}{b} {host} · 🆕 {n}{err}"), "src_err": (" · ⚠️×{n}", " · ⚠️×{n}"), "src_add": ("➕ افزودن منبع", "➕ Add source"),
    "src_add_prompt": ("آدرس منبع را بفرستید:\n<code>https://example.com/feed</code>\n\n💡 ترجیحاً سایتی بدهید که <b>RSS</b> دارد (آدرس‌هایی مثل <code>/feed</code> ، <code>/rss</code> ، <code>/atom.xml</code>)؛ اگر آدرس صفحه‌ی اصلی را بدهید ربات خودش فید و سایت‌مپ را می‌جوید.\nℹ️ اگر <code>https://</code> را ننویسید خودکار به ابتدای آدرس اضافه می‌شود.", "Send the source URL:\n<code>https://example.com/feed</code>\n\n💡 Prefer a site that has <b>RSS</b> (paths like <code>/feed</code>, <code>/rss</code>, <code>/atom.xml</code>); if you give the homepage, the bot will look for a feed/sitemap itself.\nℹ️ If you omit <code>https://</code> it is added automatically."),
    "src_bad": ("⚠️ آدرس نامعتبر", "⚠️ Invalid URL"), "src_dup": ("⚠️ منبع تکراری", "⚠️ Duplicate source"), "src_checking": ("🔎 بررسی منبع…", "🔎 Checking source…"),
    "src_added": ("✅ منبع اضافه شد · {n} مقاله [{m}]", "✅ Source added · {n} articles [{m}]"), "src_added_empty": ("\n⚠️ چیزی پیدا نشد؛ آدرس فید را مستقیم بدهید.", "\n⚠️ Nothing found; give the feed URL directly."),
    "src_403": ("🚫 این سایت به ربات‌ها اجازه‌ی خواندن نمی‌دهد (HTTP 403)؛ از این سایت (یا سایت‌های مشابه) نمی‌توان محتوایی دریافت کرد.", "🚫 This site blocks bots (HTTP 403); content can't be fetched from this site (or similar sites)."),
    "src_dead": ("⚠️ تست بارگذاری موفق نبود؛ نمی‌توان از این سایت محتوا تولید کرد. اگر فید RSS دارد، آدرس فید را مستقیم بدهید.", "⚠️ Load test failed; content can't be produced from this site. If it has an RSS feed, give the feed URL directly."),
    "src_added_off": ("\n➕ منبع اضافه شد اما 🔴 خاموش است.", "\n➕ The source was added but is 🔴 off."), "src_now_off": ("\n🔴 منبع خاموش شد.", "\n🔴 The source was turned off."),
    "src_view": ("🌐 <b>{host}</b>\n<code>{url}</code>\n{feed}\n{st} · آخرین بررسی {last} · 🆕 {n} · ⚠️×{f}{err}", "🌐 <b>{host}</b>\n<code>{url}</code>\n{feed}\n{st} · last check {last} · 🆕 {n} · ⚠️×{f}{err}"),
    "src_feed": ("📡 <code>{u}</code>", "📡 <code>{u}</code>"), "active": ("🟢 فعال", "🟢 active"), "inactive": ("🔴 غیرفعال", "🔴 inactive"), "toggle": ("⏯ روشن/خاموش", "⏯ On/off"), "delete": ("🗑 حذف", "🗑 Delete"),
    "src_st": ("{c} کانال · {b} ربات", "{c} channel · {b} bot"), "tog_ch": ("⏯ منبع کانال", "⏯ Channel source"), "tog_bot": ("🤖 منبع ربات", "🤖 Bot source"),
    "src_ch_on": ("🟢 منبع برای کانال روشن شد", "🟢 Source on for channel"), "src_ch_off": ("🔴 منبع برای کانال خاموش شد", "🔴 Source off for channel"),
    "src_bot_on": ("🟢 منبع برای محتوای ربات روشن شد", "🟢 Source on for bot content"), "src_bot_off": ("🔴 منبع برای محتوای ربات خاموش شد", "🔴 Source off for bot content"),
    "src_api": ("🔌 API", "🔌 API"), "src_api_none": ("🔌 API: —", "🔌 API: —"), "src_api_on": ("🔌 API: <code>{u}</code>", "🔌 API: <code>{u}</code>"),
    "src_api_url": ("آدرس API منبع را بفرستید (خروجی JSON):\n<code>https://site.com/wp-json/wp/v2/posts?per_page=20</code>\n\nℹ️ اگر کلید API داخل آدرس می‌آید، جای کلید بنویسید <code>{key}</code> تا ربات آن را جای‌گذاری کند.\nبرای حذف API بنویسید <code>-</code>", "Send the source API URL (JSON output):\n<code>https://site.com/wp-json/wp/v2/posts?per_page=20</code>\n\nℹ️ If the key goes inside the URL, write <code>{key}</code> where the key belongs and the bot will substitute it.\nSend <code>-</code> to remove the API."),
    "src_api_key": ("کلید API را بفرستید (اگر لازم نیست بنویسید <code>-</code>):", "Send the API key (send <code>-</code> if not needed):"),
    "src_api_ok": ("✅ API ثبت شد · {n} آیتم خوانده شد", "✅ API saved · {n} items read"), "src_api_bad": ("⚠️ پاسخ API قابل استفاده نبود؛ ثبت شد اما منبع 🔴 خاموش است.", "⚠️ API response wasn't usable; saved but the source is 🔴 off."),
    "src_api_del": ("🗑 API حذف شد", "🗑 API removed"),
    "src_on": ("🟢 منبع روشن شد", "🟢 Source on"), "src_off": ("🔴 منبع خاموش شد", "🔴 Source off"), "src_deleted": ("🗑 منبع حذف شد", "🗑 Source deleted"), "src_recheck": ("🔎 بررسی دوباره", "🔎 Re-check"),
    # ---- محتوا
    "content_title": ("✍️ <b>محتوا — {title}</b>\n🎯 {topic} · 🗣 {lang}\n📝 <i>{prompt}</i>\n✒️ {sig}", "✍️ <b>Content — {title}</b>\n🎯 {topic} · 🗣 {lang}\n📝 <i>{prompt}</i>\n✒️ {sig}"),
    "general": ("عمومی", "general"), "b_topic": ("🎯 موضوع", "🎯 Topic"), "b_lang": ("🗣 زبان خروجی", "🗣 Output language"), "b_prompt": ("📝 پرامپت", "📝 Prompt"), "b_sig": ("✒️ امضا", "✒️ Signature"),
    "b_cats": ("🗂 دسته‌ها ({n})", "🗂 Categories ({n})"), "b_crits": ("📏 معیارها ({n})", "📏 Criteria ({n})"), "b_min": ("⭐ حداقل امتیاز {n}", "⭐ Min score {n}"), "b_words": ("🔢 کلمات {n}", "🔢 Words {n}"), "b_limit": ("📏 سقف کاراکتر {n}", "📏 Char limit {n}"),
    "b_hashtags": ("#️⃣ هشتگ {i}", "#️⃣ Hashtags {i}"), "b_link": ("🔗 منبع در ربات {i}", "🔗 Source in bot {i}"), "b_media": ("🖼 رسانه {i}", "🖼 Media {i}"), "b_strict": ("🛡 فیلتر سخت {i}", "🛡 Strict filter {i}"),
    "tog_hashtags": ("#️⃣ هشتگ", "#️⃣ Hashtags"), "tog_include_link": ("🔗 منبع در ربات", "🔗 Source in bot"), "tog_include_media": ("🖼 رسانه", "🖼 Media"), "tog_strict_ads": ("🛡 فیلتر سخت تبلیغ", "🛡 Strict ad filter"), "tog_allow_undated": ("📅 بدون تاریخ", "📅 Undated"),
    "togd_hashtags": ("هشتگ‌های مرتبط در انتهای پست اضافه می‌شوند", "Related hashtags are added at the end of the post"), "togd_include_link": ("منبع خبر فقط در «ادامه در ربات» نمایش داده می‌شود", "The news source is shown only in “continue in bot”"), "togd_include_media": ("تصویر یا ویدیوی خبر همراه پست ارسال می‌شود", "The news photo or video is sent with the post"), "togd_strict_ads": ("فیلتر سخت‌گیرانه‌تر، تبلیغ‌ها را زودتر رد می‌کند", "The stricter filter rejects ad-like articles earlier"), "togd_allow_undated": ("مقالاتِ بدون تاریخ هم منتشر می‌شوند", "Articles without a publish date are published too"),
    "cats_title": ("🗂 <b>دسته‌ها</b>\nAI برای هر مقاله یکی را انتخاب و با سبک آن می‌نویسد.", "🗂 <b>Categories</b>\nAI picks one per article and writes in its style."), "cat_add": ("➕ دسته", "➕ Category"),
    "cat_view": ("{e} <b>{name}</b>\n📐 {style}", "{e} <b>{name}</b>\n📐 {style}"), "cat_edit": ("✏️ سبک", "✏️ Style"), "cat_style_prompt": ("سبک نگارش جدید این دسته:", "New writing style for this category:"),
    "cat_added": ("✅ دسته اضافه شد", "✅ Category added"), "cat_updated": ("✅ سبک بروزرسانی شد", "✅ Style updated"), "cat_min": ("⚠️ حداقل یک دسته لازم است", "⚠️ At least one category required"),
    "crits_title": ("📏 <b>معیارها</b>\nامتیاز ۰–۱۰۰ · زیر {m} رد می‌شود.", "📏 <b>Criteria</b>\nScore 0–100 · below {m} is rejected."), "crit_add": ("➕ معیار", "➕ Criterion"),
    "crit_line": ("\n• {name} — {w} ({p}%)", "\n• {name} — {w} ({p}%)"), "crit_btn": ("{name} · {w}", "{name} · {w}"), "crit_view": ("📏 <b>{name}</b> · وزن {w}", "📏 <b>{name}</b> · weight {w}"), "crit_w": ("✏️ وزن", "✏️ Weight"),
    "crit_w_prompt": ("وزن جدید (۱–۱۰۰):", "New weight (1–100):"), "crit_added": ("✅ معیار اضافه شد", "✅ Criterion added"), "crit_updated": ("✅ وزن بروزرسانی شد", "✅ Weight updated"), "crit_min": ("⚠️ حداقل یک معیار لازم است", "⚠️ At least one criterion required"),
    # ---- هوش مصنوعی شخصیِ مدیر
    "my_ai": ("🤖 هوش مصنوعی من", "🤖 My AI"),
    "my_ai_title": ("🤖 <b>هوش مصنوعی من</b>\nمدل‌های شخصی شما اول استفاده می‌شوند؛ اگر خطا دادند، مدل‌های عمومی ربات جایگزین می‌شوند.", "🤖 <b>My AI</b>\nYour own models are used first; if they fail, the bot's shared models take over."),
    "my_ai_none": ("\n\n⚠️ <b>هنوز مدل شخصی ندارید.</b> مدل‌های عمومی ممکن است هر لحطه شلوغ یا خاموش شوند؛ حتماً یک مدل شخصی اضافه کنید.", "\n\n⚠️ <b>You have no personal model yet.</b> The shared models can get busy or go down at any time; adding your own is strongly recommended."),
    "my_ai_line": ("\n{i} <b>{name}</b> · <code>{model}</code> · ✅{ok}", "\n{i} <b>{name}</b> · <code>{model}</code> · ✅{ok}"),
    "my_ai_add": ("➕ افزودن مدل", "➕ Add model"), "my_ai_added": ("✅ مدل «{name}» اضافه شد · {res}", "✅ Model “{name}” added · {res}"),
    "my_ai_view": ("🤖 <b>{name}</b> · {kind}\n<code>{model}</code>\n🔗 <code>{base}</code>\n{st} · ✅ {ok} · ⚠️×{fc}\n🕐 موفق {lo} · خطا {lf}", "🤖 <b>{name}</b> · {kind}\n<code>{model}</code>\n🔗 <code>{base}</code>\n{st} · ✅ {ok} · ⚠️×{fc}\n🕐 ok {lo} · error {lf}"),
    # ---- زمان‌بندی
    "sched_title": ("⏰ <b>زمان‌بندی — {title}</b>\n⏱ هر {iv}′ · 📦 {ppc} پست/چرخه · 🕰 {lb}h اخیر · 📅 بدون تاریخ {ud}\n🌙 {quiet} · 🌍 {city} {tz} (⌚ {loc} · UTC {utc})\n🔁 {mode}", "⏰ <b>Schedule — {title}</b>\n⏱ every {iv}′ · 📦 {ppc} posts/cycle · 🕰 last {lb}h · 📅 undated {ud}\n🌙 {quiet} · 🌍 {city} {tz} (⌚ {loc} · UTC {utc})\n🔁 {mode}"),
    "mode_auto": ("⚡ خودکار — انتشار مستقیم", "⚡ auto — publish directly"), "mode_review": ("📝 بازبینی — تأیید دستی در صف", "📝 review — manual approval in queue"), "none": ("—", "—"),
    "b_interval": ("⏱ هر {n}′", "⏱ Every {n}′"), "b_ppc": ("📦 {n} پست/چرخه", "📦 {n}/cycle"), "b_lookback": ("🕰 {n}h", "🕰 {n}h"), "b_undated": ("📅 بدون تاریخ {i}", "📅 Undated {i}"),
    "b_quiet": ("🌙 خاموشی", "🌙 Quiet hours"), "b_tz": ("🌍 منطقه زمانی", "🌍 Time zone"), "b_mode": ("🔁 {m}", "🔁 {m}"),
    "mode_set_auto": ("⚡ خودکار: انتشار مستقیم", "⚡ Auto: publish directly"), "mode_set_review": ("📝 بازبینی: منتظر تأیید در صف", "📝 Review: waits for approval"),
    "quiet_pick_start": ("🌙 <b>خاموشی</b> · ساعت <b>شروع</b> ({tz} · الان {loc}):", "🌙 <b>Quiet hours</b> · <b>start</b> hour ({tz} · now {loc}):"), "quiet_pick_end": ("🌙 شروع {h}:00 · ساعت <b>پایان</b>:", "🌙 Start {h}:00 · <b>end</b> hour:"),
    "quiet_off": ("🚫 بدون خاموشی", "🚫 No quiet hours"), "quiet_set": ("🌙 خاموشی {a}:00 → {b}:00", "🌙 Quiet {a}:00 → {b}:00"), "quiet_cleared": ("🌙 خاموشی حذف شد", "🌙 Quiet hours cleared"),
    "tz_pick": ("🌍 <b>منطقه زمانی</b> · UTC الان <b>{utc}</b>\nنزدیک‌ترین شهر را انتخاب کنید:", "🌍 <b>Time zone</b> · UTC now <b>{utc}</b>\nPick the nearest city:"), "tz_set": ("🌍 {city} {tz} · ⌚ {loc}", "🌍 {city} {tz} · ⌚ {loc}"),
    # ---- صف / مقاله
    "queue_title": ("📝 <b>صف انتشار — {title}</b> · {n} آماده", "📝 <b>Publish queue — {title}</b> · {n} ready"), "rej_title": ("♻️ <b>ردشده‌های ۲۴h — {title}</b>", "♻️ <b>Rejected 24h — {title}</b>"),
    "pub_first": ("🚀 انتشار اولین", "🚀 Publish first"), "art_title": ("📝 <b>{title}</b>\n⭐ {score} · 🗂 {cat}\n📌 {st}{reason} · 🌐 {host}\n━━━━━━━━━━━━\n{body}", "📝 <b>{title}</b>\n⭐ {score} · 🗂 {cat}\n📌 {st}{reason} · 🌐 {host}\n━━━━━━━━━━━━\n{body}"),
    "art_nobody": ("<i>(محتوایی تولید نشده)</i>", "<i>(no content generated)</i>"), "art_pub": ("🚀 انتشار", "🚀 Publish"), "art_edit": ("✏️ ویرایش", "✏️ Edit"), "art_full": ("📖 نسخه کامل", "📖 Full version"), "art_view": ("👁 مشاهده", "👁 View"),
    "art_del_arch": ("🗑 حذف از آرشیو", "🗑 Remove from archive"), "art_to_ready": ("♻️ به صف انتشار", "♻️ To publish queue"), "art_edit_prompt": ("متن جدید پست (فرمت تلگرام حفظ می‌شود):", "New post text (Telegram formatting kept):"),
    "art_updated": ("✅ متن بروزرسانی شد", "✅ Text updated"), "art_moved": ("♻️ به صف منتقل شد", "♻️ Moved to queue"), "publishing": ("⏳ انتشار…", "⏳ Publishing…"), "published_ok": ("✅ منتشر شد", "✅ Published"), "pub_failed": ("❌ انتشار: {e}", "❌ Publish: {e}"), "full_head": ("📖 <b>نسخه‌ی کامل</b>\n\n", "📖 <b>Full version</b>\n\n"),
    # ---- پلن من / لاگ
    "myplan": ("🧾 <b>پلن من: {name}</b>\n{st}{exp}{nxt}\n📢 {p}/{pc} پست · 🧪 {t}/{tc} تست (امروز)\n🌐 {s}/{sc} منبع · 📣 {c}/{cc} کانال", "🧾 <b>My plan: {name}</b>\n{st}{exp}{nxt}\n📢 {p}/{pc} posts · 🧪 {t}/{tc} tests (today)\n🌐 {s}/{sc} sources · 📣 {c}/{cc} channels"),
    "st_active": ("🟢 فعال", "🟢 active"), "st_expired": ("🔴 غیرفعال", "🔴 inactive"), "exp_at": (" · تا {d}", " · until {d}"), "upgrade_btn": ("⬆️ ارتقا / تمدید", "⬆️ Upgrade / renew"),
    "logs_title": ("📜 <b>لاگ</b>{lvl}\n\n", "📜 <b>Logs</b>{lvl}\n\n"), "logs_empty": ("— خالی —", "— empty —"), "all": ("همه", "All"), "errors": ("خطاها", "Errors"), "warns": ("هشدارها", "Warnings"),
    "logs_note": ("\n\n<i>۱۰ مورد آخر</i>", "\n\n<i>last 10 entries</i>"),
    # ---- دلیل کوتاه ردشده‌ها (بدون جزئیات فنی)
    "rj_extract": ("متن قابل استخراج نبود", "no extractable text"), "rj_ad": ("فیلتر تبلیغ", "ad filter"), "rj_ai_ad": ("تبلیغ (تشخیص AI)", "ad (AI)"), "rj_score": ("امتیاز کمتر از حداقل", "below minimum score"),
    "rj_ai": ("سرویس هوش مصنوعی پاسخ نداد", "AI service did not respond"), "rj_send": ("ارسال به کانال ناموفق", "sending to channel failed"), "rj_dup": ("تکراری", "duplicate"),
    "rj_admin": ("ربات ادمین کانال نیست", "bot is not channel admin"), "rj_old": ("قدیمی‌تر از بازه", "older than window"), "rj_undated": ("بدون تاریخ", "undated"), "rj_other": ("نامشخص", "unspecified"),
    # ---- تست
    "test_head": ("🧪 <b>تست — {title}</b>", "🧪 <b>Test — {title}</b>"), "preparing": ("آماده‌سازی…", "Preparing…"), "test_wait": ("⏳ تست بعدی تا {n} ثانیه دیگر", "⏳ Next test in {n}s"), "test_busy": ("⏳ چرخه‌ای روی این کانال در حال اجراست", "⏳ A cycle is already running on this channel"),
    "test_ok": ("✅ <b>منتشر شد</b>", "✅ <b>Published</b>"), "test_queued": ("📝 در <b>صف انتشار</b> منتظر تأیید (حالت بازبینی)", "📝 Waiting in <b>publish queue</b> (review mode)"), "test_fail": ("⚠️ <b>چیزی منتشر نشد</b>", "⚠️ <b>Nothing published</b>"),
    "test_log": ("📋 {d}", "📋 {d}"), "test_quota_note": ("ℹ️ سهمیه‌ی تست فقط با انتشار موفق کسر می‌شود", "ℹ️ Test quota is deducted only on success"), "back_panel": ("🔙 پنل کانال", "🔙 Channel panel"),
    "test_retry_note": ("ℹ️ سهمیه و محدودیت زمانی اعمال نشد؛ می‌توانید همین حالا دوباره تست کنید.", "ℹ️ No quota or cooldown was applied; you can retry right away."),
    "test_src": ("🌐 تولید از منبع: <b>{name}</b>", "🌐 Generated from source: <b>{name}</b>"),
    "lock_reset_q": ("⚠️ با بازتولید کد قفل، این کانال از نظر امنیتی <b>ریست</b> می‌شود:\n• کد قفل تازه صادر می‌شود\n• صفِ انتشارِ تأییدنشده پاک می‌شود\n• اتوماسیون خاموش می‌شود\n\nمنابع و پست‌های منتشرشده دست‌نخورده می‌مانند. ادامه می‌دهید؟", "⚠️ Regenerating the lock code <b>resets</b> this channel for security:\n• a new lock code is issued\n• the unapproved publish queue is cleared\n• automation is turned off\n\nSources and already-published posts stay untouched. Continue?"),
    "lock_reset_ok": ("✅ کد جدید صادر شد · کانال ریست شد ({n} مورد از صف پاک شد) · 🔴 اتوماسیون خاموش شد", "✅ New code issued · channel reset ({n} queued items cleared) · 🔴 automation turned off"),
}
def tr(lang, key, / , **kw):
    s = TXT[key][1 if lang == "en" else 0]
    try: return s.format(**kw) if kw else s
    except Exception: return s
STATUS = {"discovered": ("🔎 کشف‌شده", "🔎 discovered"), "skipped": ("⏭ خارج از بازه", "⏭ out of window"), "rejected": ("♻️ ردشده", "♻️ rejected"), "failed": ("❌ ناموفق", "❌ failed"), "ready": ("📝 آماده", "📝 ready"), "published": ("✅ منتشرشده", "✅ published")}
def reason_text(reason, lang):
    """دلیل کوتاه و امن برای مدیر: هیچ نام مدل، Base URL یا متن خطای فنی نشان داده نمی‌شود."""
    r = (reason or "").strip().lower()
    if not r: return ""
    if r.startswith("ai:"): return ai_err_text(r.split(":", 1)[1].strip(), lang)
    for pre, key in (("extract", "rj_extract"), ("ad_filter", "rj_ad"), ("ai_ad", "rj_ai_ad"), ("score", "rj_score"), ("send", "rj_send"), ("duplicate", "rj_dup"), ("bot_not_admin", "rj_admin"), ("old", "rj_old"), ("undated", "rj_undated")):
        if r.startswith(pre): return tr(lang, key)
    if r.startswith("ai_"): return ai_err_text(r, lang)
    return tr(lang, "rj_other")
INT_FIELDS = {"max_words": (30, 600), "min_score": (0, 100), "post_limit": (300, 4000), "interval_minutes": (MIN_INTERVAL, 1440), "posts_per_cycle": (1, MAX_PPC), "lookback_hours": (1, MAX_LOOKBACK)}
FIELD_LABEL = {"prompt": ("پرامپت نگارش", "Writing prompt"), "topic": ("موضوع کانال", "Channel topic"), "language": ("زبان خروجی (نام زبان را بنویس: Italian، Chinese، فارسی، …)", "Output language (type the language name: Italian, Chinese, English, …)"), "signature": ("امضای پایان پست (@channel = یوزرنیم کانال)", "Post signature (@channel = channel username)"),
               "max_words": ("حداکثر کلمات پست", "Max post words"), "min_score": ("حداقل امتیاز (۰–۱۰۰)", "Min score (0–100)"), "post_limit": ("سقف کاراکتر پست کانال (پیش‌فرض ۷۰۰)؛ محتوای کامل‌تر → «ادامه در ربات» (۳۰۰–۴۰۰۰)", "Channel post char limit (default 700); longer content → “continue in bot” (300–4000)"),
               "interval_minutes": (f"فاصله‌ی چرخه (دقیقه، ≥{MIN_INTERVAL})", f"Cycle interval (min, ≥{MIN_INTERVAL})"), "posts_per_cycle": (f"پست در هر چرخه (≤{MAX_PPC})", f"Posts per cycle (≤{MAX_PPC})"), "lookback_hours": (f"مقالات چند ساعت اخیر (≤{MAX_LOOKBACK})", f"Articles from last N hours (≤{MAX_LOOKBACK})")}
SCHED_FIELDS = ("interval_minutes", "posts_per_cycle", "lookback_hours")
TZ_NAMES = {"tehran": ("🇮🇷 تهران", "🇮🇷 Tehran"), "istanbul": ("🇹🇷 استانبول", "🇹🇷 Istanbul"), "dubai": ("🇦🇪 دبی", "🇦🇪 Dubai"), "kabul": ("🇦🇫 کابل", "🇦🇫 Kabul"), "karachi": ("🇵🇰 کراچی", "🇵🇰 Karachi"), "delhi": ("🇮🇳 دهلی", "🇮🇳 Delhi"),
            "moscow": ("🇷🇺 مسکو", "🇷🇺 Moscow"), "berlin": ("🇩🇪 برلین", "🇩🇪 Berlin"), "london": ("🇬🇧 لندن", "🇬🇧 London"), "beijing": ("🇨🇳 پکن", "🇨🇳 Beijing"), "tokyo": ("🇯🇵 توکیو", "🇯🇵 Tokyo"), "sydney": ("🇦🇺 سیدنی", "🇦🇺 Sydney"),
            "newyork": ("🇺🇸 نیویورک", "🇺🇸 New York"), "losangeles": ("🇺🇸 لس‌آنجلس", "🇺🇸 Los Angeles"), "saopaulo": ("🇧🇷 سائوپائولو", "🇧🇷 São Paulo"), "utc": ("🌐 گرینویچ", "🌐 UTC")}
def tz_city(off, lang):
    z = next((k for k, o in TZ_ZONES if abs(o - float(off)) < 0.01), None); return TZ_NAMES[z][1 if lang == "en" else 0] if z else ""
WIZ = {
    "cat_add": [("name", ("نام دسته (مثلاً خبری)", "Category name (e.g. News)"), "str"), ("emoji", ("یک ایموجی", "One emoji"), "str"), ("style", ("سبک نگارش (مثلاً: تیتر بولد، سه جمله، دو بولت)", "Writing style (e.g. bold headline, three sentences, two bullets)"), "str")],
    "crit_add": [("name", ("نام معیار", "Criterion name"), "str"), ("weight", ("وزن (۱–۱۰۰)", "Weight (1–100)"), "int")],
    "plan_new": [("name", ("نام (فارسی)", "Name (Persian)"), "str"), ("name_en", ("نام (انگلیسی)", "Name (English)"), "str"), ("days", ("مدت (روز)", "Days"), "int"), ("daily_posts", ("پست روزانه", "Posts/day"), "int"), ("max_sources", ("حداکثر منبع", "Max sources"), "int"), ("max_channels", ("حداکثر کانال", "Max channels"), "int"), ("daily_tests", ("تست روزانه", "Tests/day"), "int"),
                 ("price", ("قیمت (فارسی، مثلاً ۲۰۰,۰۰۰ تومان)", "Price (Persian)"), "str"), ("price_en", ("قیمت (انگلیسی، مثلاً 5 USDT)", "Price (English)"), "str"),
                 ("price_num", ("قیمت عددی برای proration (مثلاً ۵ = $5؛ خالی = بدون proration)", "Numeric price for proration (e.g. 5 = $5; blank = no proration)"), "float"),
                 ("description", ("توضیح کوتاه (فارسی)", "Short description (Persian)"), "str"), ("description_en", ("توضیح کوتاه (انگلیسی)", "Short description (English)"), "str")],
    "model_add": [("base_url", ("Base URL سرویس را بفرستید (همان آدرسی که سرویس‌دهنده‌ی شما اعلام کرده است):", "Send the service Base URL (exactly as your provider documents it):"), "str"),
                  ("api_key", ("کلید API (توکن)", "API key (token)"), "str"), ("model", ("نام مدل", "Model name"), "str")],
    "my_ai_add": [("base_url", ("Base URL سرویس هوش مصنوعی خودتان را بفرستید (همان آدرسی که سرویس‌دهنده اعلام کرده):", "Send the Base URL of your own AI service (exactly as your provider documents it):"), "str"),
                  ("api_key", ("کلید API (توکن)", "API key (token)"), "str"), ("model", ("نام مدل", "Model name"), "str")],
    "disc_add": [("code", ("کد تخفیف (مثلاً SPRING30)", "Discount code (e.g. SPRING30)"), "str"), ("percent", ("درصد تخفیف (۱–۱۰۰)", "Discount percent (1–100)"), "int"), ("expires", ("انقضا: تعداد روز (مثلاً 30) یا تاریخ (2025-12-31)", "Expiry: days (e.g. 30) or date (2025-12-31)"), "str"), ("max_uses", ("حداکثر دفعات استفاده (0 = نامحدود)", "Max uses (0 = unlimited)"), "int")],
}
# ============================================================
# ابزار UI
def B(t, d): return InlineKeyboardButton(t, callback_data=d[:64])
def U(t, url): return InlineKeyboardButton(t, url=url)
def esc(x): return html.escape(str(x if x is not None else ""))
def onoff(v): return "✅" if v else "❌"
def bar(p): f = int(p // 10); return "█" * f + "░" * (10 - f)
def to_int(s):
    text = str(s).strip().translate(_FA_DIGITS)
    if not re.fullmatch(r"[+-]?[0-9]+", text): raise ValueError("Expected an integer")
    return int(text)
def pairs(btns, n=2): return [btns[i:i + n] for i in range(0, len(btns), n)]
def uname(u): return ("@" + u["username"]) if u and u["username"] else (u["name"] if u and u["name"] else str(u["id"] if u else "?"))
def can_admin(uid): return role_of(uid) in ("admin", "super")
def L(update): return user_lang(update.effective_user.id) or "fa"
def cap(v): return "∞" if v is None else v
def kbm(kb):
    """[[(label, data)]] → InlineKeyboardMarkup (برای notify از هسته)"""
    return InlineKeyboardMarkup([[B(t, d) if not str(d).startswith("http") else U(t, d) for t, d in row] for row in kb]) if kb else None
_current_operation = ContextVar("current_operation", default=None)
_operations, _user_controls = {}, {}
_temp_messages, _temp_tasks = set(), set()

@dataclass
class Operation:
    user: int
    channel: int | None
    operation_type: str
    chat_id: int
    started_at: str = field(default_factory=now_iso)
    task: asyncio.Task | None = None
    cancelled: bool = False
    started: bool = False
    replaced_status: bool = False
    published_count: int = 0
    failed: bool = False
    status_message_id: int | None = None
    status_text: str = ""
    final_status: bool = False
    ai_popup: bool = False
    status_lock: asyncio.Lock = field(default_factory=asyncio.Lock)


def operation_checkpoint():
    op = _current_operation.get()
    if op and op.cancelled: raise asyncio.CancelledError


def clear_interaction(context, keep=()):
    for key in ("await", "notice", "disc", "bc_src", "qs", "qs_channel"):
        if key not in keep: context.user_data.pop(key, None)


def user_control(uid):
    if uid not in _user_controls: _user_controls[uid] = asyncio.Lock()
    return _user_controls[uid]


def operation_text(lang, key):
    texts = {
        "running": ("⚙️ در حال پردازش…", "⚙️ Processing…"),
        "completed": ("✅ عملیات انجام شد", "✅ Operation completed"),
        "cancelled": ("⛔ عملیات لغو شد", "⛔ Operation cancelled"),
        "cancelled_after_publish": ("ادامهٔ عملیات لغو شد؛ {n} مطلب پیش از توقف منتشر شده و حذف نشده است.", "Further work cancelled; {n} post(s) were published before stopping and have not been removed."),
        "failed": ("⚠️ عملیات انجام نشد؛ دوباره تلاش کنید.", "⚠️ Operation failed; please try again."),
        "busy": ("عملیات قبلی در حال اجراست؛ برای توقف /cancel را بفرستید.", "An operation is running; use /cancel to stop it."),
        "fallback": ("⚠️ مدل پاسخ قابل‌استفاده نداد؛ در حال بررسی مدل بعدی…", "⚠️ Model unavailable; trying the next model…"),
    }
    return texts[key][1 if lang == "en" else 0]


async def delete_temp(bot, chat_id, mid, seconds=8):
    key = (chat_id, mid)
    try:
        if seconds: await asyncio.sleep(seconds)
        if key in _temp_messages: await bot.delete_message(chat_id, mid)
    except Exception:
        log.debug("temporary message deletion failed", exc_info=True)
    finally: _temp_messages.discard(key)


def expire_temp(bot, chat_id, mid, seconds=8):
    task = asyncio.create_task(delete_temp(bot, chat_id, mid, seconds))
    _temp_tasks.add(task); task.add_done_callback(_temp_tasks.discard)


async def create_temp(bot, chat_id, text, temporary=True):
    task = asyncio.create_task(bot.send_message(chat_id, text[:4000], parse_mode=HTML, disable_web_page_preview=True))
    try: msg = await asyncio.shield(task)
    except asyncio.CancelledError:
        try:
            msg = await task
            if temporary:
                _temp_messages.add((chat_id, msg.message_id))
                expire_temp(bot, chat_id, msg.message_id, 0)
            else:
                op = _current_operation.get()
                if op: op.status_message_id = msg.message_id
        except Exception: log.debug("cancelled status delivery failed", exc_info=True)
        raise
    if temporary: _temp_messages.add((chat_id, msg.message_id))
    return msg.message_id


async def operation_status(context, text, failed=False, terminal=False):
    op = _current_operation.get()
    if not op: return False
    if not terminal: operation_checkpoint()
    op.failed = op.failed or failed
    async with op.status_lock:
        text = text[:4000]
        if text == op.status_text: return True
        try:
            if op.status_message_id is None:
                op.status_message_id = context.user_data.get("status_message_id")
            if op.status_message_id is None:
                op.status_message_id = await create_temp(context.bot, op.chat_id, text, temporary=False)
                context.user_data["status_message_id"] = op.status_message_id
            else:
                await context.bot.edit_message_text(text, chat_id=op.chat_id, message_id=op.status_message_id, parse_mode=HTML, disable_web_page_preview=True)
            op.status_text = text
        except BadRequest as e:
            if "not modified" in str(e).lower(): op.status_text = text
            else: log.debug("operation status rejected", exc_info=True)
        except Exception: log.debug("operation status unavailable", exc_info=True)
    return True


async def run_user_operation(update, context, kind, channel, work, show_status=False, replace=False, keep=()):
    uid = update.effective_user.id; lang = L(update)
    async with user_control(uid):
        replaced_status = False
        if replace:
            replaced_status = await cancel_user_operation(uid)
            clear_interaction(context, keep=keep)
        if uid in _operations:
            await popup(update, context, operation_text(lang, "busy"), alert=True)
            return
        op = Operation(uid, channel, kind, update.effective_chat.id, replaced_status=replaced_status)
        async def run():
            token = _current_operation.set(op)
            outcome = "completed"
            try:
                op.started = True
                log_event("INFO", f"operation start type={kind} channel={channel}", uid)
                operation_checkpoint()
                if show_status: await operation_status(context, operation_text(lang, "running"))
                result = await work()
                operation_checkpoint()
                if op.failed: outcome = "failed"
                return result
            except asyncio.CancelledError:
                op.cancelled = True; outcome = "cancelled"
                raise
            except Exception:
                op.failed = True; outcome = "failed"
                op.final_status = False
                log.exception("operation failed user=%s type=%s channel=%s", uid, kind, channel)
                clear_interaction(context)
            finally:
                try:
                    if outcome == "cancelled":
                        clear_interaction(context)
                        key = "cancelled_after_publish" if op.published_count else "cancelled"
                        await operation_status(context, operation_text(lang, key).format(n=op.published_count), terminal=True)
                    elif outcome == "failed" and not op.final_status:
                        await operation_status(context, operation_text(lang, outcome), failed=True, terminal=True)
                    elif op.status_message_id is not None and not op.final_status:
                        await operation_status(context, operation_text(lang, "completed"), terminal=True)
                    log_event("ERROR" if outcome == "failed" else "INFO", f"operation {outcome} type={kind} channel={channel}", uid)
                finally:
                    if op.status_message_id is not None: context.user_data["status_message_id"] = op.status_message_id
                    if _operations.get(uid) is op: _operations.pop(uid, None)
                    _current_operation.reset(token)
        op.task = asyncio.create_task(run(), name=f"user:{uid}:{kind}")
        _operations[uid] = op
    try: return await asyncio.shield(op.task)
    except asyncio.CancelledError:
        if not op.cancelled:
            op.cancelled = True
            if op.started: op.task.cancel()
        if op.started:
            try: await asyncio.shield(op.task)
            except asyncio.CancelledError: pass
    finally:
        if op.task.done() and _operations.get(uid) is op: _operations.pop(uid, None)


async def cancel_user_operation(uid):
    op = _operations.get(uid)
    if not op: return False
    if not op.cancelled and not op.task.done():
        op.cancelled = True
        if op.started: op.task.cancel()
    try: await asyncio.shield(op.task)
    except asyncio.CancelledError:
        if not op.task.done(): raise
    if _operations.get(uid) is op: _operations.pop(uid, None)
    return op.status_message_id is not None


def _ai_status_reporter(context, lang):
    async def report(event, label, code):
        name = esc(label); en = lang == "en"
        texts = {
            "busy": f"Model busy; waiting: {name}" if en else f"مدل مشغول است؛ در انتظار: {name}",
            "start": f"Testing/using model: {name}" if en else f"در حال فراخوانی مدل: {name}",
            "failure": (f"{name}: {ai_err_text(code, lang)}; checking the next model…" if en else f"{name}: {ai_err_text(code, lang)}؛ بررسی مدل بعدی…"),
            "unavailable": f"Model unavailable: {name}; checking the next model…" if en else f"مدل قابل استفاده نیست: {name}؛ بررسی مدل بعدی…",
            "no_test": "Selected Test Model is unset or unavailable; checking public models." if en else "Test Model منتخب تعیین نشده یا قابل استفاده نیست؛ بررسی مدل‌های عمومی.",
            "success": f"AI response received — model: {name}" if en else f"پاسخ معتبر دریافت شد — مدل: {name}",
            "failed": ai_err_text(code, lang),
        }
        await operation_status(context, texts[event])
    return report


async def run_model_test(update, context, mid, personal=False):
    uid = update.effective_user.id; lang = L(update); m = get_model(mid)
    op = _current_operation.get()
    if op: op.ai_popup = True
    if not m or (personal and m["owner_id"] != uid):
        return await popup(update, context, tr(lang, "notfound"), alert=True)
    started = time.monotonic(); label = _model_label(m, uid if personal else None)
    token = _ai_events.set(_ai_status_reporter(context, lang))
    try:
        if personal:
            out, label, error = await ai_chat("You are a health-check. Reply with exactly one word.", "Say: READY",
                                             owner_id=uid, selected_id=mid, validate=_validate_ready)
            ok = out is not None
        else:
            ok, out, elapsed = await test_model(mid)
            error = None if ok else out
        elapsed = round(time.monotonic() - started, 1)
        if ok:
            result = f"Test successful — model: {esc(label)} ({elapsed}s)" if lang == "en" else f"تست موفق — مدل: {esc(label)} ({elapsed}s)"
        else:
            result = ("Test failed — " if lang == "en" else "تست ناموفق — ") + ai_err_text(error, lang)
        await operation_status(context, result, failed=not ok, terminal=True)
        if op: op.final_status = True
        await popup(update, context, result, alert=True)
        return ok
    finally:
        _ai_events.reset(token)


async def popup(update, context, text, alert=False):
    op = _current_operation.get()
    if op and op.status_message_id is not None and not op.ai_popup:
        op.final_status = True
        await operation_status(context, text)
        return
    qy = update.callback_query
    if qy:
        try: await qy.answer(strip_tags(text)[:200], show_alert=alert); context._callback_answered = True; return
        except Exception: pass
    await send_temp(context, update.effective_chat.id, text)
async def render(update, context, text, kb=None, force_new=False):
    operation_checkpoint()
    notice = context.user_data.pop("notice", None)
    if notice: await popup(update, context, notice)
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
    lang = L(update); st = context.user_data.get("await")
    if not isinstance(st, dict) or st.get("kind") != "wiz": return
    steps = WIZ.get(st.get("wiz"), ()); i = st.get("step")
    if type(i) is not int or not 0 <= i < len(steps):
        if context.user_data.get("await") is st: context.user_data.pop("await", None)
        return
    await render(update, context, f"{tr(lang, 'step', i=i + 1, n=len(steps))} ✏️ {steps[i][1][1 if lang == 'en' else 0]}\n\n<i>{tr(lang, 'send_value')}</i>", [[B(tr(lang, "cancel"), "c:cancel")]])
async def notify_supers(text, kb=None):
    for sid in SUPER_ADMIN_IDS:
        try: await APP.bot.send_message(sid, text, parse_mode=HTML, reply_markup=kbm(kb) if kb and isinstance(kb[0][0], tuple) else (InlineKeyboardMarkup(kb) if kb else None), disable_web_page_preview=True)
        except Exception as e: log.warning(f"notify {sid}: {e}")
async def notify_user_fn(uid, text, kb=None):
    try: await APP.bot.send_message(uid, text, parse_mode=HTML, reply_markup=kbm(kb), disable_web_page_preview=True)
    except Exception as e:
        log.warning(f"notify user {uid}: {e}")
        if SCHED_NOTIF_FAILURES:
            raise  # scheduled-warning mode: propagate so _plan_notifications releases remind_key
async def go_home(update, context):
    uid = update.effective_user.id; context.user_data.pop("await", None)
    if not user_lang(uid): return await view_lang(update, context)
    return await (view_super_home if is_super(uid) else view_admin_home if can_admin(uid) else view_user_home)(update, context)
# ============================================================
# انتخاب زبان · منوی کاربر · پلن‌ها (دودویی، قیمت پس از کلیک، کد تخفیف)
async def view_lang(update, context): await render(update, context, tr("fa", "choose_lang"), [[B("🇮🇷 فارسی", "lang:fa"), B("🇬🇧 English", "lang:en")]])
async def set_language(update, context, lang):
    """تغییر زبان صفر تا صد: زبانِ رابط، و در همه‌ی کانال‌ها پرامپت پیش‌فرض و متن‌های پیش‌فرضِ محتوا/گزارش هم به زبان تازه بازنویسی می‌شوند (فقط آن‌هایی که مدیر دستی عوض نکرده)."""
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
        if _price_num(p) and lim["active"] and lim["plan_id"] not in (None, 0) and lim["plan_id"] != pid:
            text += "\n" + ("⚠️ ارتقا با کسر روزهای باقی‌ماندهٔ پلن فعلی محاسبه می‌شود؛ مبلغ دقیق در صفحهٔ پرداخت نمایش داده می‌شود."
                           if lang == "fa" else "⚠️ Upgrade will be pro-rated against your remaining current plan time; the exact amount is shown on the payment page.")
        elif lim["active"] and lim["plan_id"] not in (None, 0) and lim["plan_id"] != pid:
            # no numeric price on either side → proration impossible; show full price explicitly
            text += "\n" + ("⚠️ قیمت عددیِ پلن‌ها تنظیم نشده است؛ این خرید کاملِ پلن جدید محاسبه می‌شود (بدون کسر روزهای باقی‌مانده)."
                            if lang == "fa" else "⚠️ No numeric price is set on the plans; this purchase is billed at the full new-plan price (no day credit).")
        if pay_pending_for(uid, pid): kb.append([B(tr(lang, "plan_pending_btn"), "noop")])
        else: kb.append([B(tr(lang, "plan_renew_btn" if lim["plan_id"] == pid and lim["active"] else "plan_req_btn"), f"u:req:{pid}"), B(tr(lang, "disc_remove") if d else tr(lang, "disc_btn"), f"u:disc{'x' if d else ''}:{pid}")])
    kb.append([B(tr(lang, "back"), "u:plans")]); await render(update, context, text, kb)
async def do_free(update, context, pid):
    uid = update.effective_user.id; lang = L(update); u = get_user(uid); p = get_plan(pid)
    if not p or not p["is_free"] or u["free_used"]: await popup(update, context, tr(lang, "free_once"), alert=True); return await view_plans(update, context)
    assign_plan(uid, pid); log_event("INFO", f"پلن رایگان فعال شد برای {uid}", uid); await popup(update, context, tr(lang, "free_done", name=plan_txt(p, "name", lang)), alert=True)
    await notify_supers(f"🎁 {esc(uname(u))} (<code>{uid}</code>) پلن رایگان را فعال کرد."); await view_admin_home(update, context)
def _fmt_price(v):
    s = f"{v:g}"
    return s + "$"
def _price_num(p):
    """قیمت عددیِ پلن (برای proration)؛ اگر ستون price_num وجود نداشته باشد یا خالی باشد ۰ (proration انجام نمی‌شود)."""
    try:
        return float(p["price_num"] or 0)
    except (KeyError, IndexError, TypeError, ValueError):
        return 0.0
def _upgrade_price(uid, p, cur, disc_percent):
    """مبلغ ارتقا با proration: max(0, price_num - remaining_value)؛ تخفیف روی همان مبلغ اعمال می‌شود."""
    new_num = _price_num(p)
    if not new_num or not cur or not _price_num(cur): return None, None
    cur_num, cur_days = _price_num(cur), cur["days"] or 0
    rv = proration_remaining_value(uid, new_num, cur_num, cur_days)
    amt = round(max(0.0, new_num - rv), 2)
    if disc_percent: amt = round(amt * (100 - disc_percent) / 100, 2)
    return amt, rv
async def do_request(update, context, pid):
    uid = update.effective_user.id; lang = L(update); p = get_plan(pid)
    if not p: await popup(update, context, tr(lang, "plan_notfound")); return await view_plans(update, context)
    if pay_pending_for(uid, pid): await popup(update, context, tr(lang, "req_pending"), alert=True); return await view_plan(update, context, pid)
    lim = admin_limits(uid); cur = get_plan(lim["plan_id"]) if lim["plan_id"] else None
    d = _applied_disc(context, pid); new_price, _ = _price_text(p, lang, d)
    amt, rv = _upgrade_price(uid, p, cur, d["percent"] if d else None)
    # single source of truth: amount (number) and display (text) computed exactly once here;
    # the same amount persists to pay_requests.final_price at receipt time (no later overwrite)
    if amt is not None:
        final_amount = str(amt)
        display = f"{_fmt_price(amt)}  (بقایای {plan_txt(cur, 'name', lang)}: −{_fmt_price(rv)})"
    else:
        final_amount = new_price
        display = new_price
    context.user_data["await"] = {"kind": "receipt", "pid": pid, "back": f"u:plan:{pid}", "disc": d["code"] if d else None,
                                   "final": final_amount, "display": display, "upgrade_amt": amt}
    await render(update, context, gtext("pay", lang, plan=esc(plan_txt(p, "name", lang)), price=esc(display)) + tr(lang, "receipt_hint"), [[B(tr(lang, "cancel"), "c:cancel")]])
async def view_receipt_ok(update, context): lang = L(update); await render(update, context, tr(lang, "receipt_ok"), [[B(tr(lang, "wait_btn"), "home")]], force_new=True)
# ============================================================
# پنل مدیر میانی — صفحه‌ی اصلی و پنل کانال
async def view_admin_home(update, context):
    uid = update.effective_user.id; lang = L(update); lim = admin_limits(uid); use = usage_today(uid); chs = list_channels(uid)
    pname = "∞" if is_super(uid) else (plan_txt(lim["plan"], "name", lang) or tr(lang, "no_plan"))
    text = (f"{tr(lang, 'panel')}\n🧾 <b>{esc(pname)}</b>" + (tr(lang, "until", d=fmt_date(lim["expires"], admin_offset(uid))) if lim["expires"] else "") + "\n" +
            tr(lang, "today_line", p=use["posts"], pc=cap(lim["daily_posts"]), t=use["tests"], tc=cap(lim["daily_tests"]), c=len(chs), cc=cap(lim["max_channels"]), s=count_sources(uid), sc=cap(lim["max_sources"])))
    if lim["next_plan"]: text += "\n" + tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang)))
    if not lim["active"]: text += "\n\n" + tr(lang, "plan_inactive")
    text += "\n\n" + (tr(lang, "pick_channel") if chs else tr(lang, "no_channels"))
    kb = pairs([B(f"{'🟢' if get_settings(c['id'])['enabled'] else '🔴'} {c['title'][:22]}", f"a:ch:{c['id']}") for c in chs])
    kb.append([B(tr(lang, "ch_add"), "a:chadd")]); kb.append([B(tr(lang, "my_plan"), "a:plan"), B(tr(lang, "my_ai"), "a:myai")])
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
# ============================================================
# منابع
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
# ============================================================
# محتوا، دسته‌ها، معیارها
async def view_content(update, context, cid):
    uid = update.effective_user.id; lang = L(update); ch = channel_owned(cid, uid)
    if not ch: return await view_admin_home(update, context)
    s = get_settings(cid)
    text = tr(lang, "content_title", title=esc(ch["title"]), topic=esc(s["topic"] or tr(lang, "general")), lang=esc(s["language"]), prompt=esc(s["prompt"][:2500]) + ("…" if len(s["prompt"]) > 2500 else ""), sig=esc(strip_tags(s["signature"])[:60]) or "—")
    kb = [[B(tr(lang, "b_topic"), f"a:set:{cid}:topic"), B(tr(lang, "b_lang"), f"a:set:{cid}:language")], [B(tr(lang, "b_prompt"), f"a:set:{cid}:prompt"), B(tr(lang, "b_sig"), f"a:set:{cid}:signature")],
          [B(tr(lang, "b_cats", n=len(s["categories"])), f"a:cat:{cid}"), B(tr(lang, "b_crits", n=len(s["criteria"])), f"a:cri:{cid}")], [B(tr(lang, "b_min", n=s["min_score"]), f"a:set:{cid}:min_score"), B(tr(lang, "b_words", n=s["max_words"]), f"a:set:{cid}:max_words")],
          [B(tr(lang, "b_limit", n=s["post_limit"]), f"a:set:{cid}:post_limit"), B(tr(lang, "b_hashtags", i=onoff(s["hashtags"])), f"a:tog:{cid}:hashtags")], [B(tr(lang, "b_link", i=onoff(s["include_link"])), f"a:tog:{cid}:include_link"), B(tr(lang, "b_media", i=onoff(s["include_media"])), f"a:tog:{cid}:include_media")],
          [B(tr(lang, "b_strict", i=onoff(s["strict_ads"])), f"a:tog:{cid}:strict_ads")], [B(tr(lang, "back"), f"a:ch:{cid}")]]
    await render(update, context, text, kb)
async def view_cats(update, context, cid):
    lang = L(update); s = get_settings(cid)
    text = tr(lang, "cats_title") + "\n" + "".join(f"\n{c['emoji']} <b>{esc(c['name'])}</b>: {esc(c['style'][:70])}" for c in s["categories"])
    kb = pairs([B(f"{c['emoji']} {c['name'][:18]}", f"a:catv:{cid}:{i}") for i, c in enumerate(s["categories"])]) + [[B(tr(lang, "cat_add"), f"a:cata:{cid}")], [B(tr(lang, "back"), f"a:con:{cid}")]]; await render(update, context, text, kb)
async def view_cat(update, context, cid, i):
    lang = L(update); s = get_settings(cid); c = s["categories"][i] if 0 <= i < len(s["categories"]) else None
    if not c: return await view_cats(update, context, cid)
    await render(update, context, tr(lang, "cat_view", e=c["emoji"], name=esc(c["name"]), style=esc(c["style"])), [[B(tr(lang, "cat_edit"), f"a:cats:{cid}:{i}"), B(tr(lang, "delete"), f"a:catd:{cid}:{i}")], [B(tr(lang, "back"), f"a:cat:{cid}")]])
async def view_crits(update, context, cid):
    lang = L(update); s = get_settings(cid); tot = sum(float(c["weight"]) for c in s["criteria"]) or 1
    text = tr(lang, "crits_title", m=s["min_score"]) + "\n" + "".join(tr(lang, "crit_line", name=esc(c["name"]), w=c["weight"], p=f"{float(c['weight']) / tot * 100:.0f}") for c in s["criteria"])
    kb = pairs([B(tr(lang, "crit_btn", name=c["name"][:16], w=c["weight"]), f"a:criv:{cid}:{i}") for i, c in enumerate(s["criteria"])]) + [[B(tr(lang, "crit_add"), f"a:cria:{cid}")], [B(tr(lang, "back"), f"a:con:{cid}")]]; await render(update, context, text, kb)
async def view_crit(update, context, cid, i):
    lang = L(update); s = get_settings(cid); c = s["criteria"][i] if 0 <= i < len(s["criteria"]) else None
    if not c: return await view_crits(update, context, cid)
    await render(update, context, tr(lang, "crit_view", name=esc(c["name"]), w=c["weight"]), [[B(tr(lang, "crit_w"), f"a:criw:{cid}:{i}"), B(tr(lang, "delete"), f"a:crid:{cid}:{i}")], [B(tr(lang, "back"), f"a:cri:{cid}")]])
# ============================================================
# زمان‌بندی، خاموشی، منطقه‌ی زمانی شهری
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
    await render(update, context, tr(lang, "quiet_pick_start", tz=off_label(s["utc_offset"]), loc=local_clock(s["utc_offset"])), hour_grid(f"a:qs:{cid}") + [[B(tr(lang, "quiet_off"), f"a:qoff:{cid}")], [B(tr(lang, "back"), f"a:sch:{cid}")]])
async def view_tz(update, context, cid):
    lang = L(update); s = get_settings(cid); cur = float(s["utc_offset"]); i = 1 if lang == "en" else 0
    rows = pairs([B(("✅ " if abs(o - cur) < 0.01 else "") + f"{TZ_NAMES[z][i]} {off_label(o)}", f"a:tzs:{cid}:{k}") for k, (z, o) in enumerate(TZ_ZONES)])
    await render(update, context, tr(lang, "tz_pick", utc=utc_clock()), rows + [[B(tr(lang, "back"), f"a:sch:{cid}")]])
# ============================================================
# صف انتشار و مقالات
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
# ============================================================
# پلن من، لاگ، تست فوری (با محدودیت نرخ)
async def view_my_ai(update, context):
    """مدل‌های شخصیِ همین مدیر (جدا از مدل‌های عمومی مدیر کلان)."""
    uid = update.effective_user.id; lang = L(update); ms = list_models(owner_id=uid)
    text = tr(lang, "my_ai_title") + ("".join(tr(lang, "my_ai_line", i=_mic(m), name=esc(_mname(m)), model=esc(m["model"]), ok=m["ok_count"]) for m in ms) if ms else tr(lang, "my_ai_none"))
    kb = pairs([B(f"{_mic(m)} {_mname(m)[:20]}", f"a:myai_v:{m['id']}") for m in ms]) + [[B(tr(lang, "my_ai_add"), "a:myai_add")], [B(tr(lang, "back"), "a:home")]]
    await render(update, context, text, kb)
async def view_my_ai_model(update, context, mid):
    uid = update.effective_user.id; lang = L(update); m = get_model(mid)
    if not m or m["owner_id"] != uid: await popup(update, context, tr(lang, "notfound")); return await view_my_ai(update, context)
    text = tr(lang, "my_ai_view", name=esc(m["name"]), kind=m["kind"], model=esc(m["model"]), base=esc(m["base_url"]), st=tr(lang, "s_m_off" if not m["active"] else "s_m_ok" if m["status"] == "ok" else "s_m_down"), ok=m["ok_count"], fc=m["fail_count"], lo=ago_text(m["last_ok"], lang), lf=ago_text(m["last_fail"], lang))
    kb = [[B(tr(lang, "s_model_test"), f"a:myai_t:{mid}"), B(tr(lang, "toggle"), f"a:myai_o:{mid}")]] + pairs([B(f"✏️ {f[2] if lang == 'en' else f[1]}", f"a:myai_e:{mid}:{f[0]}") for f in MODEL_FIELDS]) + [[B(tr(lang, "delete"), f"a:myai_d:{mid}")], [B(tr(lang, "back"), "a:myai")]]
    await render(update, context, text, kb)
async def view_my_plan(update, context):
    uid = update.effective_user.id; lang = L(update); lim = admin_limits(uid); use = usage_today(uid)
    pname = "∞" if is_super(uid) else (plan_txt(lim["plan"], "name", lang) or tr(lang, "no_plan"))
    text = tr(lang, "myplan", name=esc(pname), st=tr(lang, "st_active" if lim["active"] else "st_expired"), exp=tr(lang, "exp_at", d=fmt_date(lim["expires"], admin_offset(uid), True)) if lim["expires"] else "", nxt=("\n" + tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang)))) if lim["next_plan"] else "",
              p=use["posts"], pc=cap(lim["daily_posts"]), t=use["tests"], tc=cap(lim["daily_tests"]), s=count_sources(uid), sc=cap(lim["max_sources"]), c=len(list_channels(uid)), cc=cap(lim["max_channels"]))
    await render(update, context, text, [[B(tr(lang, "upgrade_btn"), "u:plans")], [B(tr(lang, "back"), "a:home")]])
async def view_logs(update, context, admin_id=None, level=None, back="a:home", refresh="a:logs"):
    """مدیران فقط ۱۰ مورد آخر را می‌بینند (پیام‌ها پیش از ثبت از نام مدل و Base URL پاک شده‌اند)؛ سوپرادمین ۲۰ مورد."""
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
    try: await qy.answer(); context._callback_answered = True
    except Exception: pass
    last = [0.0]; head = tr(lang, "test_head", title=esc(ch["title"]))
    async def progress(pct, txt):
        if time.time() - last[0] < 1.6 and pct < 100: return
        last[0] = time.time()
        await operation_status(context, f"{head}\n\n{bar(pct)} <b>{pct}%</b>\n{esc(txt)}")
    await progress(1, tr(lang, "preparing"))
    model_labels = []; report_ai = _ai_status_reporter(context, lang)
    async def ai_progress(event, label, code):
        if event == "success" and label not in model_labels: model_labels.append(label)
        await report_ai(event, label, code)
    ai_token = _ai_events.set(ai_progress)
    try: res = await run_channel_cycle(context.bot, uid, cid, test_mode=True, progress=progress)
    except Exception as e:
        log_event("ERROR", f"تست کانال {ch['title']}: {e}", uid); d = Diag(); d.add("ai_fail", err=ai_err_text(err_code(e), lang)); res = {"published": 0, "queued": 0, "links": [], "diag": d, "src": ""}
    except asyncio.CancelledError:
        raise
    finally:
        _ai_events.reset(ai_token)
    ok = bool(res["published"] or res.get("queued"))
    if ok and not res.get("published"): rate_mark(f"test:{cid}")  # تستِ موفقِ صف‌شده
    elif not ok: rate_clear(f"test:{cid}")
    diag = esc(res["diag"].render(lang)); kb = []
    src = (res.get("src") or "").strip(); src_line = ("\n" + tr(lang, "test_src", name=esc(src[:60]))) if src else ""
    if res["published"]: text = f"{tr(lang, 'test_ok')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}"; kb.append([U(f"{tr(lang, 'art_view')} {i + 1}", l) for i, l in enumerate(res["links"][:3])])
    elif res.get("queued"): text = f"{tr(lang, 'test_queued')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}"; kb.append([B(tr(lang, "queue", n=ready_count(cid)), f"a:que:{cid}")])
    else: text = f"{tr(lang, 'test_fail')}{src_line}\n\n{tr(lang, 'test_log', d=diag)}\n\n{tr(lang, 'test_retry_note')}"; kb.append([B(tr(lang, "rejected"), f"a:rej:{cid}"), B(tr(lang, "sched"), f"a:sch:{cid}")])
    op = _current_operation.get()
    model_line = ("Model: " if lang == "en" else "مدل: ") + esc(", ".join(model_labels)) if model_labels else ""
    if model_line: text += "\n" + model_line
    final = ("Test successful" if ok else "Test failed") if lang == "en" else ("تست موفق" if ok else "تست ناموفق")
    await operation_status(context, final + (" — " + model_line if model_line else ""), failed=not ok, terminal=True)
    if op: op.failed = not ok; op.final_status = True
    kb.append([B(tr(lang, "back_panel"), f"a:ch:{cid}")]); await render(update, context, text, kb)
# ---------- پایان پنل مدیر میانی ----------
# ============================================================
# پنل مدیر کلان، dispatch (با محدودکننده‌ی نرخ)، ورودی‌ها، پشتیبانی، دیپ‌لینک، main
# ============================================================
TXT.update({
    "s_title": ("👑 <b>مدیر کلان</b>\n🤖 مدل‌ها {m} ({ms}) · 👥 مدیران {a} / کاربران {u}\n🛎 پرداخت معلق {p} · 🎟 کد تخفیف {dc} · ⚖️ صف {due}\n💓 {hb}", "👑 <b>Super admin</b>\n🤖 models {m} ({ms}) · 👥 admins {a} / users {u}\n🛎 pending payments {p} · 🎟 discount codes {dc} · ⚖️ queue {due}\n💓 {hb}"),
    "s_all_ok": ("سالم", "healthy"), "s_down": ("{n} خراب 🔴", "{n} down 🔴"), "s_report": ("📊 گزارش", "📊 Report"), "s_logs": ("📜 لاگ", "📜 Logs"), "s_plans": ("🧾 پلن‌ها", "🧾 Plans"), "s_users": ("👥 کاربران", "👥 Users"),
    "s_models": ("🤖 مدل‌ها", "🤖 Models"), "s_pays": ("🛎 پرداخت‌ها ({n})", "🛎 Payments ({n})"), "s_discs": ("🎟 کدهای تخفیف", "🎟 Discount codes"), "s_bc": ("📣 همگانی", "📣 Broadcast"), "s_texts": ("📝 متن‌ها", "📝 Texts"),
    "s_admins": ("🧑‍💼 مدیران", "🧑‍💼 Admins"), "s_auto": ("{i} اتوماسیون کل", "{i} Global automation"), "s_me": ("👤 پنل من", "👤 My panel"), "s_auto_on": ("🟢 اتوماسیون کل روشن شد", "🟢 Global automation on"), "s_auto_off": ("🔴 اتوماسیون کل خاموش شد", "🔴 Global automation off"),
    "s_plans_title": ("🧾 <b>پلن‌ها</b>", "🧾 <b>Plans</b>"), "s_plan_new": ("➕ پلن", "➕ Plan"), "s_plan_created": ("✅ «{name}» ساخته شد", "✅ “{name}” created"), "s_plan_deleted": ("🗑 پلن حذف شد", "🗑 Plan deleted"),
    "s_plan_view": ("🧾 <b>{name}</b> / {name_en} {free} {st}\n{desc}\n{desc_en}\n⏳ {days}d · 📢 {posts}/d · 🧪 {tests}/d · 🌐 {src} · 📣 {ch}\n💰 {price} / {price_en} · 🔢 {price_num}\n👥 {n} کاربر", "🧾 <b>{name}</b> / {name_en} {free} {st}\n{desc}\n{desc_en}\n⏳ {days}d · 📢 {posts}/d · 🧪 {tests}/d · 🌐 {src} · 📣 {ch}\n💰 {price} / {price_en} · 🔢 {price_num}\n👥 {n} users"),
    "s_plan_free_set": ("🎁 رایگان شود", "🎁 Make free"), "s_plan_free_done": ("🎁 پلن رایگان تنظیم شد", "🎁 Free plan set"), "s_plan_del": ("🗑 حذف پلن", "🗑 Delete plan"), "s_field_prompt": ("مقدار جدید «{f}»:", "New value for “{f}”:"),
    "s_discs_title": ("🎟 <b>کدهای تخفیف</b>", "🎟 <b>Discount codes</b>"), "s_disc_new": ("➕ کد", "➕ Code"), "s_disc_line": ("\n{i} <code>{code}</code> −{p}% · تا {exp} · {used}/{max}", "\n{i} <code>{code}</code> −{p}% · until {exp} · {used}/{max}"),
    "s_disc_view": ("🎟 <code>{code}</code> {st}\n−{p}% · انقضا {exp} · استفاده {used}/{max}", "🎟 <code>{code}</code> {st}\n−{p}% · expires {exp} · used {used}/{max}"), "s_disc_created": ("✅ کد {code} ساخته شد", "✅ Code {code} created"), "s_disc_dup": ("⚠️ کد تکراری یا نامعتبر", "⚠️ Duplicate or invalid code"),
    "s_disc_exp_bad": ("⚠️ انقضا: عدد روز یا تاریخ YYYY-MM-DD", "⚠️ Expiry: days number or YYYY-MM-DD"), "s_disc_p": ("✏️ درصد", "✏️ Percent"), "s_disc_e": ("✏️ انقضا", "✏️ Expiry"), "s_disc_m": ("✏️ سقف استفاده", "✏️ Max uses"), "s_disc_del": ("🗑 حذف کد", "🗑 Delete code"), "unlimited": ("∞", "∞"),
    "s_users_title": ("👥 <b>{what}</b> ({n}) · {p}/{pp}", "👥 <b>{what}</b> ({n}) · {p}/{pp}"), "s_users_w": ("کاربران", "Users"), "s_admins_w": ("مدیران", "Admins"), "s_prev": ("⬅️", "⬅️"), "s_next": ("➡️", "➡️"),
    "s_user_view": ("👤 <b>{name}</b> · <code>{id}</code> · {role} · {ban} · {lang} {prem}\n🧾 {plan} {act}{exp}{nxt}\n📢 امروز {p} پست · {t} تست · 📣 {c} کانال · 🌐 {s} منبع\n📰 ۲۴h: {d} کشف · {pub} منتشر · 🎁 رایگان {free}\n🕐 عضویت {join} · آخرین {seen}", "👤 <b>{name}</b> · <code>{id}</code> · {role} · {ban} · {lang} {prem}\n🧾 {plan} {act}{exp}{nxt}\n📢 today {p} posts · {t} tests · 📣 {c} channels · 🌐 {s} sources\n📰 24h: {d} found · {pub} published · 🎁 free {free}\n🕐 joined {join} · seen {seen}"),
    "s_ban_y": ("⛔ مسدود", "⛔ banned"), "s_ban_n": ("✅ آزاد", "✅ active"), "s_uplan": ("🧾 تعیین پلن", "🧾 Assign plan"), "s_urevoke": ("❌ لغو پلن", "❌ Revoke plan"), "s_uban": ("⛔ مسدود/آزاد", "⛔ Ban/unban"), "s_umsg": ("✉️ پیام", "✉️ Message"),
    "s_ureport": ("📊 کانال‌ها", "📊 Channels"), "s_ufree": ("🔁 ریست رایگان", "🔁 Reset free"), "s_utests": ("🧪 ریست تست", "🧪 Reset tests"), "s_uposts": ("📢 ریست پست", "📢 Reset posts"),
    "s_plan_pick": ("🧾 پلن این کاربر:", "🧾 Plan for this user:"), "s_assigned": ("✅ پلن تا {d} فعال شد", "✅ Plan active until {d}"), "s_assigned_q": ("⏭ پلن بعدی (پس از {d})", "⏭ Queued as next (after {d})"),
    "s_revoked": ("❌ پلن لغو شد", "❌ Plan revoked"), "s_banned": ("⛔ مسدود شد", "⛔ Banned"), "s_unbanned": ("✅ آزاد شد", "✅ Unbanned"), "s_free_reset": ("🔁 سهمیه‌ی رایگان ریست شد", "🔁 Free quota reset"), "s_tests_reset": ("🧪 تست امروز ریست شد", "🧪 Tests reset"), "s_posts_reset": ("📢 پست امروز ریست شد", "📢 Posts reset"),
    "s_no_channels": ("کانالی ندارد", "No channels"), "s_pick_channel": ("📢 کانال:", "📢 Channel:"),
    "s_models_title": ("🤖 <b>مدل‌ها</b>\nبه ترتیب اولویت؛ با خرابی یکی، بعدی استفاده می‌شود. هر سرویس سازگار با OpenAI / Anthropic / Gemini پشتیبانی می‌شود.", "🤖 <b>Models</b>\nUsed in priority order; on failure the next is used. Any OpenAI-compatible / Anthropic / Gemini service is supported."), "s_model_add": ("➕ مدل", "➕ Model"), "s_models_test": ("🧪 تست همه", "🧪 Test all"),
    "s_model_view": ("🤖 <b>{name}</b> · {kind}\n<code>{model}</code>\n🔗 <code>{base}</code>\n🔑 <code>{key}</code>\n⚙️ اولویت {pr} · دما {temp} · توکن {mx}\n{st} · ✅ {ok} · ⚠️×{fc}\n🕐 موفق {lo} · خطا {lf}{err}", "🤖 <b>{name}</b> · {kind}\n<code>{model}</code>\n🔗 <code>{base}</code>\n🔑 <code>{key}</code>\n⚙️ priority {pr} · temp {temp} · tokens {mx}\n{st} · ✅ {ok} · ⚠️×{fc}\n🕐 ok {lo} · error {lf}{err}"),
    "s_m_off": ("⏸ خاموش", "⏸ off"), "s_m_ok": ("🟢 سالم", "🟢 healthy"), "s_m_down": ("🔴 خراب", "🔴 down"), "s_model_test": ("🧪 تست", "🧪 Test"), "s_model_del": ("🗑 حذف مدل", "🗑 Delete model"),
    "s_model_testing": ("🧪 در حال تست…", "🧪 Testing…"), "s_model_res": ("{i} {t}s: {out}", "{i} {t}s: {out}"), "s_model_added": ("✅ مدل «{name}» اضافه شد · {res}", "✅ Model “{name}” added · {res}"), "s_model_need": ("⚠️ Base URL و نام مدل الزامی است", "⚠️ Base URL and model name are required"), "s_model_on": ("🟢 مدل روشن شد", "🟢 Model on"), "s_model_off": ("⏸ مدل خاموش شد", "⏸ Model off"),
    "s_pays_title": ("🛎 <b>پرداخت‌های معلق</b>", "🛎 <b>Pending payments</b>"), "s_pay_none": ("— خالی —", "— none —"), "s_pay_line": ("\n• #{id} {who} → <b>{plan}</b> · {price} · {t}", "\n• #{id} {who} → <b>{plan}</b> · {price} · {t}"), "s_pay_rc": ("📎 #{id}", "📎 #{id}"),
    "s_pay_ok": ("✅ تأیید", "✅ Approve"), "s_pay_no": ("❌ رد", "❌ Reject"), "s_pay_done_ok": ("✅ تأیید شد؛ پلن فعال/رزرو شد", "✅ Approved; plan activated/queued"), "s_pay_done_no": ("❌ رد شد", "❌ Rejected"), "s_pay_seen": ("⚠️ قبلاً بررسی شده", "⚠️ Already handled"),
    "s_pay_new": ("🛎 <b>پرداخت #{id}</b>\n👤 {who} (<code>{uid}</code>)\n🧾 <b>{plan}</b> · 💰 {price}{disc}{note}", "🛎 <b>Payment #{id}</b>\n👤 {who} (<code>{uid}</code>)\n🧾 <b>{plan}</b> · 💰 {price}{disc}{note}"),
    "s_bc_prompt": ("پیام همگانی (متن/عکس/ویدیو؛ فرمت حفظ می‌شود):", "Broadcast message (text/photo/video; formatting kept):"), "s_bc_confirm": ("📣 ارسال به <b>{n}</b> کاربر؟", "📣 Send to <b>{n}</b> users?"), "s_bc_go": ("✅ ارسال", "✅ Send"), "s_bc_sending": ("📣 ارسال به {n} کاربر…", "📣 Sending to {n} users…"), "s_bc_done": ("📣 موفق {ok} · ناموفق {fail}", "📣 ok {ok} · failed {fail}"),
    "s_texts_title": ("📝 <b>متن‌ها</b> (فارسی/انگلیسی) · جای‌گذارها: welcome {{name}} · pay {{plan}} {{price}}", "📝 <b>Texts</b> (fa/en) · placeholders: welcome {{name}} · pay {{plan}} {{price}}"), "s_text_prompt": ("متن جدید «{k}» ({lg}):", "New “{k}” text ({lg}):"), "s_text_saved": ("✅ متن ذخیره شد", "✅ Text saved"), "s_text_reset_done": ("↩️ پیش‌فرض شد", "↩️ Reset to default"),
    "s_umsg_prompt": ("پیام برای این کاربر:", "Message to this user:"), "s_umsg_sent": ("✅ ارسال شد", "✅ Sent"), "s_umsg_head": ("📩 <b>پیام مدیریت:</b>\n\n", "📩 <b>Admin message:</b>\n\n"),
    "sup_open": ("💬 <b>پشتیبانی</b>\nهر پیامی بفرستید مستقیم به مدیر می‌رسد و پاسخ همین‌جا می‌آید.", "💬 <b>Support</b>\nAny message goes straight to the admin; replies arrive here."), "sup_close": ("❌ پایان گفتگو", "❌ End chat"), "sup_closed": ("✅ گفتگو پایان یافت", "✅ Chat ended"),
    "sup_reply_head": ("💬 <b>پاسخ پشتیبانی:</b>\n", "💬 <b>Support reply:</b>\n"), "sup_sent": ("✅ ارسال شد", "✅ Sent"), "sup_fail": ("❌ ارسال نشد: {e}", "❌ Not sent: {e}"), "sup_received": ("✅", "✅"),
    "dl_notfound": ("⚠️ محتوا یافت نشد یا منقضی شده", "⚠️ Content not found or expired"), "dl_source": ("🔗 Source", "🔗 Source"),
})
PLAN_FIELDS = [("name", "نام (فا)", "Name (fa)"), ("name_en", "نام (en)", "Name (en)"), ("days", "مدت (روز)", "Days"), ("daily_posts", "پست/روز", "Posts/day"), ("max_sources", "منابع", "Sources"), ("max_channels", "کانال‌ها", "Channels"), ("daily_tests", "تست/روز", "Tests/day"), ("price", "قیمت (فا)", "Price (fa)"), ("price_en", "قیمت (en)", "Price (en)"), ("price_num", "قیمت عددی (برای proration)", "Numeric price (proration)"), ("description", "توضیح (فا)", "Description (fa)"), ("description_en", "توضیح (en)", "Description (en)")]
MODEL_FIELDS = [("model", "نام مدل", "Model"), ("base_url", "Base URL", "Base URL"), ("api_key", "کلید API", "API key"), ("name", "نام نمایشی", "Display name"), ("priority", "اولویت", "Priority"), ("temperature", "دما (0–2)", "Temperature (0–2)"), ("max_tokens", "حداکثر توکن", "Max tokens")]
TEXT_KEYS = ["welcome", "help", "about", "pay"]
def fl(fields, key, lang): return next((f[2] if lang == "en" else f[1] for f in fields if f[0] == key), key)
# ============================================================
# پنل مدیر کلان
async def view_super_home(update, context):
    lang = L(update); models = list_models(); down = sum(1 for m in models if m["active"] and m["status"] == "down"); auto = gget("automation_enabled", True); n_pay = len(pay_pending())
    text = tr(lang, "s_title", m=len(models), ms=tr(lang, "s_all_ok") if not down else tr(lang, "s_down", n=down), a=len(list_users("admin")), u=len(list_users()), p=n_pay, dc=len(disc_list()), due=gget("load_due", 0), hb=ago_text(gget("heartbeat"), lang))
    kb = [[B(tr(lang, "s_report"), "s:report"), B(tr(lang, "s_logs"), "s:logs:all")], [B(tr(lang, "s_plans"), "s:plans"), B(tr(lang, "s_discs"), "s:discs")], [B(tr(lang, "s_users"), "s:users:0"), B(tr(lang, "s_admins"), "s:admins:0")],
          [B(tr(lang, "s_models"), "s:models"), B(tr(lang, "s_pays", n=n_pay), "s:pays")], [B(tr(lang, "s_bc"), "s:bc"), B(tr(lang, "s_texts"), "s:texts")], [B(tr(lang, "s_auto", i="🟢" if auto else "🔴"), "s:auto"), B(tr(lang, "s_me"), "a:home")]]
    await render(update, context, text, kb)
async def view_s_plans(update, context):
    lang = L(update); plans = list_plans(active_only=False)
    text = tr(lang, "s_plans_title") + "\n" + "".join(f"\n{'🟢' if p['active'] else '🔴'}{'🎁' if p['is_free'] else ''} <b>{esc(plan_txt(p, 'name', lang))}</b> · {p['days']}d · {p['daily_posts']}p · {p['max_sources']}s · {p['max_channels']}c · {esc(plan_txt(p, 'price', lang))}" for p in plans)
    kb = pairs([B(f"{'🟢' if p['active'] else '🔴'} {plan_txt(p, 'name', lang)[:20]}", f"s:plan:{p['id']}") for p in plans]) + [[B(tr(lang, "s_plan_new"), "s:plan_new")], [B(tr(lang, "back"), "s:home")]]; await render(update, context, text, kb)
async def view_s_plan(update, context, pid):
    lang = L(update); p = get_plan(pid)
    if not p: return await view_s_plans(update, context)
    n = q("SELECT COUNT(*) c FROM users WHERE plan_id=?", (pid,), one=True)["c"]
    text = tr(lang, "s_plan_view", name=esc(p["name"]), name_en=esc(p["name_en"] or "—"), free="🎁" if p["is_free"] else "", st="🟢" if p["active"] else "🔴", desc=esc(p["description"]), desc_en=esc(p["description_en"] or ""), days=p["days"], posts=p["daily_posts"], tests=p["daily_tests"], src=p["max_sources"], ch=p["max_channels"], price=esc(p["price"]), price_en=esc(p["price_en"] or "—"), price_num=f"${p['price_num']}" if p.get("price_num") else "—", n=n)
    kb = pairs([B(f"✏️ {f[2] if lang == 'en' else f[1]}", f"s:plan_e:{pid}:{f[0]}") for f in PLAN_FIELDS]) + [[B(tr(lang, "toggle"), f"s:plan_t:{pid}"), B(tr(lang, "s_plan_free_set"), f"s:plan_free:{pid}")], [B(tr(lang, "s_plan_del"), f"s:plan_d:{pid}")], [B(tr(lang, "back"), "s:plans")]]
    await render(update, context, text, kb)
def _disc_st(d, lang):
    _, why = disc_valid(d["code"]); return {"ok": "🟢", "inactive": "⏸", "expired": "⌛", "exhausted": "🔚"}.get(why, "🔴")
async def view_s_discs(update, context):
    lang = L(update); ds = disc_list()
    text = tr(lang, "s_discs_title") + "".join(tr(lang, "s_disc_line", i=_disc_st(d, lang), code=esc(d["code"]), p=d["percent"], exp=fmt_date(d["expires"]) if d["expires"] else "∞", used=d["used"], max=d["max_uses"] or "∞") for d in ds)
    kb = pairs([B(f"{_disc_st(d, lang)} {d['code'][:18]} −{d['percent']}%", f"s:disc:{d['code']}") for d in ds]) + [[B(tr(lang, "s_disc_new"), "s:disc_new")], [B(tr(lang, "back"), "s:home")]]; await render(update, context, text, kb)
async def view_s_disc(update, context, code):
    lang = L(update); d = disc_get(code)
    if not d: return await view_s_discs(update, context)
    text = tr(lang, "s_disc_view", code=esc(d["code"]), st=_disc_st(d, lang), p=d["percent"], exp=fmt_date(d["expires"], DEFAULT_UTC_OFFSET, True) if d["expires"] else "∞", used=d["used"], max=d["max_uses"] or "∞")
    kb = [[B(tr(lang, "s_disc_p"), f"s:disc_e:{code}:percent"), B(tr(lang, "s_disc_e"), f"s:disc_e:{code}:expires")], [B(tr(lang, "s_disc_m"), f"s:disc_e:{code}:max_uses"), B(tr(lang, "toggle"), f"s:disc_t:{code}")], [B(tr(lang, "s_disc_del"), f"s:disc_d:{code}")], [B(tr(lang, "back"), "s:discs")]]
    await render(update, context, text, kb)
async def view_s_users(update, context, page=0, role=None):
    lang = L(update); users = list_users(role); per = 10; pages = max(1, (len(users) + per - 1) // per); page = max(0, min(page, pages - 1)); chunk = users[page * per:(page + 1) * per]; pre = "admins" if role else "users"
    def ic(u): return "⛔" if u["banned"] else {"user": "👤", "admin": "🧑‍💼"}.get(u["role"], "👑")
    text = tr(lang, "s_users_title", what=tr(lang, "s_admins_w" if role else "s_users_w"), n=len(users), p=page + 1, pp=pages) + "\n" + "".join(f"\n{ic(u)} {esc(uname(u))} · {esc(plan_txt(admin_limits(u['id'])['plan'], 'name', lang) or tr(lang, 'no_plan'))}{' 🟢' if admin_limits(u['id'])['active'] else ''}" for u in chunk)
    kb = pairs([B(f"{ic(u)} {uname(u)[:22]}", f"s:user:{u['id']}") for u in chunk]); nav = []
    if page > 0: nav.append(B(tr(lang, "s_prev"), f"s:{pre}:{page - 1}"))
    if page + 1 < pages: nav.append(B(tr(lang, "s_next"), f"s:{pre}:{page + 1}"))
    if nav: kb.append(nav)
    kb.append([B(tr(lang, "back"), "s:home")]); await render(update, context, text, kb)
async def view_s_user(update, context, tid):
    lang = L(update); u = get_user(tid)
    if not u: return await view_s_users(update, context)
    lim = admin_limits(tid); use = usage_today(tid); off = admin_offset(tid)
    text = tr(lang, "s_user_view", name=esc(uname(u)), id=tid, role=u["role"], ban=tr(lang, "s_ban_y" if u["banned"] else "s_ban_n"), lang=u["lang"] or "—", prem="💎" if u["premium"] else "", plan=esc(plan_txt(lim["plan"], "name", lang) or tr(lang, "no_plan")), act="🟢" if lim["active"] else "🔴", exp=tr(lang, "until", d=fmt_date(lim["expires"], off)) if lim["expires"] else "",
              nxt=("\n" + tr(lang, "plans_next", name=esc(plan_txt(lim["next_plan"], "name", lang)))) if lim["next_plan"] else "", p=use["posts"], t=use["tests"], c=len(list_channels(tid)), s=count_sources(tid), d=count_articles(tid, 24), pub=count_articles(tid, 24, "published"), free=onoff(u["free_used"]), join=(u["created_at"] or "")[:10], seen=ago_text(u["last_seen"], lang))
    kb = [[B(tr(lang, "s_uplan"), f"s:uplan:{tid}"), B(tr(lang, "s_urevoke"), f"s:urevoke:{tid}")], [B(tr(lang, "s_uban"), f"s:uban:{tid}"), B(tr(lang, "s_umsg"), f"s:umsg:{tid}")], [B(tr(lang, "s_ureport"), f"s:ureport:{tid}"), B(tr(lang, "s_ufree"), f"s:ufree:{tid}")], [B(tr(lang, "s_utests"), f"s:utests:{tid}"), B(tr(lang, "s_uposts"), f"s:uposts:{tid}")], [B(tr(lang, "back"), "s:users:0")]]
    await render(update, context, text, kb)
def _mic(m): return "⏸" if not m["active"] else "🟢" if m["status"] == "ok" else "🔴"
def _mname(m): return str(m["name"] or m["model"] or f"#{m['id']}")
async def view_s_models(update, context):
    lang = L(update); ms = list_models()
    text = tr(lang, "s_models_title") + "\n" + "".join(f"\n{_mic(m)} <b>{esc(_mname(m))}</b> · <code>{esc(m['model'])}</code> · p{m['priority']} · ✅{m['ok_count']}" for m in ms)
    kb = pairs([B(f"{_mic(m)} {_mname(m)[:20]} (p{m['priority']})", f"s:model:{m['id']}") for m in ms]) + [[B(tr(lang, "s_model_add"), "s:model_add"), B(tr(lang, "s_models_test"), "s:models_test")], [B(tr(lang, "back"), "s:home")]]; await render(update, context, text, kb)
async def view_s_model(update, context, mid):
    lang = L(update); m = get_model(mid)
    if not m: return await view_s_models(update, context)
    key = m["api_key"] or ""; masked = (key[:5] + "…" + key[-4:]) if len(key) > 12 else "—"
    text = tr(lang, "s_model_view", name=esc(m["name"]), kind=m["kind"], model=esc(m["model"]), base=esc(m["base_url"]), key=esc(masked), pr=m["priority"], temp=m["temperature"], mx=m["max_tokens"], st=tr(lang, "s_m_off" if not m["active"] else "s_m_ok" if m["status"] == "ok" else "s_m_down"), ok=m["ok_count"], fc=m["fail_count"], lo=ago_text(m["last_ok"], lang), lf=ago_text(m["last_fail"], lang), err=f"\n<code>{esc((m['last_error'] or '')[:150])}</code>" if m["last_error"] else "")
    kb = [[B(tr(lang, "s_model_test"), f"s:model_test:{mid}"), B(tr(lang, "toggle"), f"s:model_t:{mid}")]] + pairs([B(f"✏️ {f[2] if lang == 'en' else f[1]}", f"s:model_e:{mid}:{f[0]}") for f in MODEL_FIELDS]) + [[B(tr(lang, "s_model_del"), f"s:model_d:{mid}")], [B(tr(lang, "back"), "s:models")]]
    if m["owner_id"] is None:
        selected = gget("test_model_id") == mid
        label = ("Unset Test Model" if selected else "Use as Test Model") if lang == "en" else ("برداشتن انتخاب Test Model" if selected else "استفاده به‌عنوان Test Model")
        text += "\nTest Model: " + (("Selected" if selected else "Not selected") if lang == "en" else ("منتخب" if selected else "انتخاب نشده"))
        kb.insert(1, [B(label, f"s:model_test_pick:{mid}")])
    await render(update, context, text, kb)
async def view_s_pays(update, context):
    lang = L(update); ps = pay_pending()
    text = tr(lang, "s_pays_title") + ("".join(tr(lang, "s_pay_line", id=r["id"], who=esc(("@" + r["username"]) if r["username"] else (r["name"] or r["user_id"])), plan=esc(r["plan_name"]), price=esc(r["final_price"] or r["plan_price"]), t=r["created_at"][5:16]) for r in ps) or "\n" + tr(lang, "s_pay_none"))
    kb = [[B(tr(lang, "s_pay_rc", id=r["id"]), f"s:pay_rc:{r['id']}"), B(tr(lang, "s_pay_ok"), f"s:pay_ok:{r['id']}:l"), B(tr(lang, "s_pay_no"), f"s:pay_no:{r['id']}:l")] for r in ps] + [[B(tr(lang, "back"), "s:home")]]; await render(update, context, text, kb)
async def view_s_texts(update, context):
    lang = L(update); text = tr(lang, "s_texts_title") + "\n"
    for k in TEXT_KEYS: text += f"\n<b>{k}</b>\n🇮🇷 <i>{esc(strip_tags(gtext(k, 'fa'))[:60])}…</i>\n🇬🇧 <i>{esc(strip_tags(gtext(k, 'en'))[:60])}…</i>"
    kb = [[B(f"✏️ {k} 🇮🇷", f"s:txt:{k}:fa"), B(f"✏️ {k} 🇬🇧", f"s:txt:{k}:en"), B("↩️🇮🇷", f"s:txtr:{k}:fa"), B("↩️🇬🇧", f"s:txtr:{k}:en")] for k in TEXT_KEYS] + [[B(tr(lang, "back"), "s:home")]]; await render(update, context, text, kb)
async def decide_pay(update, context, rid, approve, from_list):
    lang = L(update); r = pay_get(rid)
    if not r or r["status"] != "pending": await popup(update, context, tr(lang, "s_pay_seen")); return await view_s_pays(update, context) if from_list else None
    ul = user_lang(r["user_id"]) or "fa"; p = get_plan(r["plan_id"])
    # claim the payment first (CAS) so a double-approve callback assigns the plan exactly once
    if not pay_claim(rid):
        await popup(update, context, tr(lang, "s_pay_seen")); return await view_s_pays(update, context) if from_list else None
    if approve:
        if not p:
            pay_set(rid, "pending"); await popup(update, context, tr(lang, "notfound"), alert=True); return await view_s_pays(update, context) if from_list else None
        exp, queued = assign_plan(r["user_id"], r["plan_id"])
        if exp is None:
            pay_set(rid, "pending"); await popup(update, context, tr(lang, "notfound"), alert=True); return await view_s_pays(update, context) if from_list else None
        pay_set(rid, "approved")
        if r["discount"]: disc_use(r["discount"])
        await notify_user_fn(r["user_id"], tr(ul, "pay_approved", name=esc(plan_txt(p, "name", ul)), when=tr(ul, "pay_when_queued" if queued else "pay_when_now", d=fmt_date(exp, admin_offset(r["user_id"]))))); await popup(update, context, tr(lang, "s_pay_done_ok"))
    else: pay_set(rid, "rejected"); await notify_user_fn(r["user_id"], tr(ul, "pay_rejected")); await popup(update, context, tr(lang, "s_pay_done_no"))
    log_event("INFO", f"پرداخت #{rid} {'تأیید' if approve else 'رد'} شد", update.effective_user.id)
    if from_list: return await view_s_pays(update, context)
    try: await update.callback_query.edit_message_reply_markup(None)
    except Exception: pass
# ============================================================
# dispatch
async def dispatch(update, context, data):
    uid = update.effective_user.id; lang = L(update); p = data.split(":"); a = p[0]; b = p[1] if len(p) > 1 else ""; c = p[2] if len(p) > 2 else ""; d = p[3] if len(p) > 3 else ""; ud = context.user_data
    if data == "noop": return
    if a == "lang": return await set_language(update, context, b)
    if not user_lang(uid): return await view_lang(update, context)
    if data == "home": return await go_home(update, context)
    if data == "c:cancel": st = ud.pop("await", None); await popup(update, context, tr(lang, "cancelled")); return await dispatch(update, context, (st or {}).get("back", "home"))
    # ---------------- کاربر
    if a == "u":
        if b == "plans": return await view_plans(update, context)
        if b == "plan": return await view_plan(update, context, int(c))
        if b == "free": return await do_free(update, context, int(c))
        if b == "req": return await do_request(update, context, int(c))
        if b == "disc": return await ask(update, context, tr(lang, "disc_prompt"), "disc", f"u:plan:{c}", pid=int(c))
        if b == "discx": ud.setdefault("disc", {}).pop(c, None); return await view_plan(update, context, int(c))
        if b == "man_close": support_close(uid); return await render(update, context, tr(lang, "sup_closed"), [[B(tr(lang, "home"), "home")]])
        return await go_home(update, context)
    # ---------------- مدیر میانی
    if a == "a":
        if not can_admin(uid): await popup(update, context, tr(lang, "no_admin"), alert=True); return await view_plans(update, context)
        lim = admin_limits(uid)
        # عملیاتی که محتوا تولید/منتشر می‌کنند فقط با پلن فعال (مشاهده و تنطیمات آزاد می‌ماند)
        if b in ("test", "pub", "srca", "chadd") and not lim["active"]: await popup(update, context, tr(lang, "plan_inactive"), alert=True); return await view_my_plan(update, context)
        if b == "home": return await view_admin_home(update, context)
        if b == "plan": return await view_my_plan(update, context)
        if b == "myai": return await view_my_ai(update, context)
        if b == "myai_add": return await wiz_start(update, context, "my_ai_add", "a:myai")
        if b in ("myai_v", "myai_t", "myai_o", "myai_d", "myai_e"):
            mid = int(c); m = get_model(mid)
            if not m or m["owner_id"] != uid: await popup(update, context, tr(lang, "notfound")); return await view_my_ai(update, context)
            if b == "myai_v": return await view_my_ai_model(update, context, mid)
            if b == "myai_o": update_model(mid, active=0 if m["active"] else 1, status="ok", fail_count=0); await popup(update, context, tr(lang, "s_model_off" if m["active"] else "s_model_on")); return await view_my_ai_model(update, context, mid)
            if b == "myai_d": delete_model(mid); await popup(update, context, tr(lang, "deleted")); return await view_my_ai(update, context)
            if b == "myai_e": return await ask(update, context, tr(lang, "s_field_prompt", f=fl(MODEL_FIELDS, d, lang)), "model_field", f"a:myai_v:{mid}", mid=mid, field=d, own=1)
            await run_model_test(update, context, mid, personal=True)
            return await view_my_ai_model(update, context, mid)
        if b == "logs":
            if c.lstrip("-").isdigit() and channel_owned(int(c), uid): return await view_logs(update, context, admin_id=uid, back=f"a:ch:{c}", refresh=f"a:logs:{c}")
            return await view_logs(update, context, admin_id=uid)
        if b == "chadd":
            if lim["max_channels"] is not None and len(list_channels(uid)) >= lim["max_channels"]: await popup(update, context, tr(lang, "limit_channels", n=lim["max_channels"]), alert=True); return await view_admin_home(update, context)
            return await ask(update, context, tr(lang, "ch_add_prompt"), "ch_add", "a:home")
        if b in ("srcv", "srct", "srctb", "srcd", "srcr", "srcapi", "srcapix"):
            sid = int(c); s = get_source(sid)
            if not s or (s["admin_id"] != uid and not is_super(uid)): await popup(update, context, tr(lang, "notfound")); return await view_admin_home(update, context)
            if b == "srcv": return await view_source(update, context, sid)
            if b == "srct": on = toggle_source(sid, s["admin_id"], "active"); await popup(update, context, tr(lang, "src_ch_on" if on else "src_ch_off")); return await view_source(update, context, sid)
            if b == "srctb": on = toggle_source(sid, s["admin_id"], "bot_active"); await popup(update, context, tr(lang, "src_bot_on" if on else "src_bot_off")); return await view_source(update, context, sid)
            if b == "srcapi": return await ask(update, context, tr(lang, "src_api_url"), "src_api_url", f"a:srcv:{sid}", sid=sid)
            if b == "srcapix": set_source_api(sid, "", "", ""); await popup(update, context, tr(lang, "src_api_del")); return await view_source(update, context, sid)
            if b == "srcr":
                if not is_super(uid) and not rate_free(f"srcr:{sid}", 60): await popup(update, context, tr(lang, "test_wait", n=rate_left(f"srcr:{sid}", 60)), alert=True); return await view_source(update, context, sid)
                await render(update, context, tr(lang, "src_checking"))
                ok, msg = await probe_source(s, lang)
                if ok: rate_mark(f"srcr:{sid}")
                else: rate_clear(f"srcr:{sid}")
                await popup(update, context, msg, alert=True); return await view_source(update, context, sid)
            del_source(sid, s["admin_id"]); await popup(update, context, tr(lang, "src_deleted")); return await view_sources(update, context, s["channel_id"])
        if b in ("art", "arte", "artd", "artr", "artf", "pub"):
            aid = int(c); art = get_article(aid)
            if not art or (art["admin_id"] != uid and not is_super(uid)): await popup(update, context, tr(lang, "notfound")); return await view_admin_home(update, context)
            cid = art["channel_id"]
            if b in ("arte", "artd", "artr") and publication_pending(cid):
                return await popup(update, context, tr(lang, "test_busy"), alert=True)
            if b == "artr" and art["status"] not in ("rejected", "failed", "skipped"):
                return await popup(update, context, tr(lang, "notfound"), alert=True)
            if b == "art": return await view_article(update, context, aid)
            if b == "arte": return await ask(update, context, tr(lang, "art_edit_prompt"), "art_edit", f"a:art:{aid}", aid=aid)
            if b == "artd": delete_article(aid, art["admin_id"]); await popup(update, context, tr(lang, "deleted")); return await view_queue(update, context, cid, "ready" if art["status"] in ("ready", "published") else "rejected")
            if b == "artr": article_update(aid, status="ready", reason=""); await popup(update, context, tr(lang, "art_moved")); return await view_article(update, context, aid)
            if b == "artf":
                if art["full_html"]:
                    fv = art["full_html"]
                    if len(fv) > BOT_FULL_MAX: fv, _ = fit_html(fv, BOT_FULL_MAX)
                    for chunk in split_html(tr(lang, "full_head") + fv): await context.bot.send_message(uid, chunk, parse_mode=HTML, disable_web_page_preview=True)
                return await view_article(update, context, aid)
            if b == "pub":
                rem = remaining(uid, "posts")
                if rem is not None and rem <= 0: await popup(update, context, tr(lang, "limit_posts", n=lim["daily_posts"]), alert=True); return await view_queue(update, context, cid)
                if ch_lock(cid).locked(): await popup(update, context, tr(lang, "test_busy"), alert=True); return await view_queue(update, context, cid)
                await render(update, context, tr(lang, "publishing"))
                try:
                    ok, out = await publish_article(context.bot, aid)
                except Exception as e:
                    log.exception("manual publish failed article=%s channel=%s", aid, cid)
                    ok, out = False, f"send_failed:{str(e)[:120]}"
                await popup(update, context, tr(lang, "published_ok") if ok else tr(lang, "pub_failed", e=_pub_err(out, lang)), alert=not ok); return await view_queue(update, context, cid)
        cid = int(c) if c.lstrip("-").isdigit() else 0; ch = channel_owned(cid, uid)
        if not ch: await popup(update, context, tr(lang, "notfound")); return await view_admin_home(update, context)
        s = get_settings(cid)
        if b == "ch": return await view_channel(update, context, cid)
        if b == "rep": return await render(update, context, report_text(uid, cid, lang), [[B(tr(lang, "refresh"), f"a:rep:{cid}")], [B(tr(lang, "back"), f"a:ch:{cid}")]])
        if b == "test": return await run_test(update, context, cid)
        if b == "lock": return await view_lock(update, context, cid)
        if b == "lockre": return await render(update, context, tr(lang, "lock_reset_q"), [[B(tr(lang, "yes"), f"a:lockre2:{cid}"), B(tr(lang, "no"), f"a:lock:{cid}")]])
        if b in ("lockre2", "chdel2") and publication_pending(cid):
            return await popup(update, context, tr(lang, "test_busy"), alert=True)
        if b == "lockre2":
            code, n = reset_channel_link(cid); log_event("WARN", f"ریست امنیتی کانال {ch['title']}", uid)
            await popup(update, context, tr(lang, "lock_reset_ok", n=n), alert=True); return await view_lock(update, context, cid)
        if b == "chdel": return await render(update, context, tr(lang, "ch_del_q", title=esc(ch["title"])), [[B(tr(lang, "yes"), f"a:chdel2:{cid}"), B(tr(lang, "no"), f"a:ch:{cid}")]])
        if b == "chdel2": del_channel(cid, ch["admin_id"]); await popup(update, context, tr(lang, "ch_deleted")); return await view_admin_home(update, context)
        if b == "tog":
            new = not s.get(d); update_settings(cid, **{d: new})
            if d == "enabled": await popup(update, context, tr(lang, "tog_enabled" if new else "tog_disabled")); return await view_channel(update, context, cid)
            else: await popup(update, context, f"{tr(lang, 'tog_' + d)}: {'✅' if new else '⛔'}\n{tr(lang, 'togd_' + d)}")
            return await (view_sched if d == "allow_undated" else view_content)(update, context, cid)
        if b == "set": return await ask(update, context, f"{FIELD_LABEL[d][1 if lang == 'en' else 0]}\n<code>{esc(strip_tags(str(s.get(d)))[:3500])}</code>", "field", f"a:sch:{cid}" if d in SCHED_FIELDS else f"a:con:{cid}", cid=cid, field=d)
        if b == "mode": new = "review" if s["mode"] == "auto" else "auto"; update_settings(cid, mode=new); await popup(update, context, tr(lang, "mode_set_auto" if new == "auto" else "mode_set_review")); return await view_sched(update, context, cid)
        if b == "sch": return await view_sched(update, context, cid)
        if b == "quiet": return await view_quiet(update, context, cid)
        if b == "qs": ud["qs"] = int(d); return await render(update, context, tr(lang, "quiet_pick_end", h=f"{int(d):02d}"), hour_grid(f"a:qe:{cid}") + [[B(tr(lang, "back"), f"a:quiet:{cid}")]])
        if b == "qe": a0 = ud.pop("qs", 0); update_settings(cid, quiet_start=a0, quiet_end=int(d)); await popup(update, context, tr(lang, "quiet_set", a=f"{a0:02d}", b=f"{int(d):02d}")); return await view_sched(update, context, cid)
        if b == "qoff": update_settings(cid, quiet_start=None, quiet_end=None); await popup(update, context, tr(lang, "quiet_cleared")); return await view_sched(update, context, cid)
        if b == "tz": return await view_tz(update, context, cid)
        if b == "tzs": z, off = TZ_ZONES[int(d)]; update_settings(cid, utc_offset=off); await popup(update, context, tr(lang, "tz_set", city=tz_city(off, lang), tz=off_label(off), loc=local_clock(off))); return await view_sched(update, context, cid)
        if b == "con": return await view_content(update, context, cid)
        if b == "cat": return await view_cats(update, context, cid)
        if b == "cata": return await wiz_start(update, context, "cat_add", f"a:cat:{cid}", cid=cid)
        if b == "catv": return await view_cat(update, context, cid, int(d))
        if b == "cats": return await ask(update, context, tr(lang, "cat_style_prompt"), "cat_style", f"a:cat:{cid}", cid=cid, idx=int(d))
        if b == "catd":
            cats = s["categories"]; i = int(d)
            if 0 <= i < len(cats) and len(cats) > 1: cats.pop(i); update_settings(cid, categories=cats); await popup(update, context, tr(lang, "deleted"))
            else: await popup(update, context, tr(lang, "cat_min"), alert=True)
            return await view_cats(update, context, cid)
        if b == "cri": return await view_crits(update, context, cid)
        if b == "cria": return await wiz_start(update, context, "crit_add", f"a:cri:{cid}", cid=cid)
        if b == "criv": return await view_crit(update, context, cid, int(d))
        if b == "criw": return await ask(update, context, tr(lang, "crit_w_prompt"), "crit_weight", f"a:cri:{cid}", cid=cid, idx=int(d))
        if b == "crid":
            cr = s["criteria"]; i = int(d)
            if 0 <= i < len(cr) and len(cr) > 1: cr.pop(i); update_settings(cid, criteria=cr); await popup(update, context, tr(lang, "deleted"))
            else: await popup(update, context, tr(lang, "crit_min"), alert=True)
            return await view_crits(update, context, cid)
        if b == "src": return await view_sources(update, context, cid)
        if b == "srca":
            if lim["max_sources"] is not None and count_sources(uid) >= lim["max_sources"]: await popup(update, context, tr(lang, "limit_sources", n=lim["max_sources"]), alert=True); return await view_sources(update, context, cid)
            return await ask(update, context, tr(lang, "src_add_prompt"), "src_add", f"a:src:{cid}", cid=cid)
        if b == "que": return await view_queue(update, context, cid, "ready")
        if b == "rej": return await view_queue(update, context, cid, "rejected")
        return await view_channel(update, context, cid)
    # ---------------- مدیر کلان
    if a == "s":
        if not is_super(uid): return
        if b == "home": return await view_super_home(update, context)
        if b == "report": return await render(update, context, report_text(None, None, lang), [[B(tr(lang, "refresh"), "s:report")], [B(tr(lang, "back"), "s:home")]])
        if b == "logs": return await view_logs(update, context, level=None if c == "all" else c, back="s:home")
        if b == "auto": new = not gget("automation_enabled", True); gset("automation_enabled", new); await popup(update, context, tr(lang, "s_auto_on" if new else "s_auto_off")); return await view_super_home(update, context)
        if b == "texts": return await view_s_texts(update, context)
        if b == "txt": return await ask(update, context, tr(lang, "s_text_prompt", k=c, lg=d), "gtext", "s:texts", key=c, lg=d)
        if b == "txtr": gtext_set(c, d, ""); await popup(update, context, tr(lang, "s_text_reset_done")); return await view_s_texts(update, context)
        if b == "bc": return await ask(update, context, tr(lang, "s_bc_prompt"), "bc", "s:home")
        if b == "bc_go":
            src = ud.pop("bc_src", None)
            if not src: return await view_super_home(update, context)
            users = list_users(); ok = fail = 0; await render(update, context, tr(lang, "s_bc_sending", n=len(users)))
            for u in users:
                try: await context.bot.copy_message(u["id"], src[0], src[1]); ok += 1
                except RetryAfter as e: await asyncio.sleep(float(e.retry_after) + 1); fail += 1
                except Exception: fail += 1
                await asyncio.sleep(.06)
            await popup(update, context, tr(lang, "s_bc_done", ok=ok, fail=fail)); return await view_super_home(update, context)
        if b == "plans": return await view_s_plans(update, context)
        if b == "plan": return await view_s_plan(update, context, int(c))
        if b == "plan_new": return await wiz_start(update, context, "plan_new", "s:plans")
        if b == "plan_e": return await ask(update, context, tr(lang, "s_field_prompt", f=fl(PLAN_FIELDS, d, lang)), "plan_field", f"s:plan:{c}", pid=int(c), field=d)
        if b == "plan_t":
            pl = get_plan(int(c))
            if not pl: await popup(update, context, tr(lang, "notfound"), alert=True); return await view_s_plans(update, context)
            update_plan(int(c), active=0 if pl["active"] else 1); await popup(update, context, tr(lang, "saved")); return await view_s_plan(update, context, int(c))
        if b == "plan_free": q("UPDATE plans SET is_free=0", commit=True); update_plan(int(c), is_free=1); await popup(update, context, tr(lang, "s_plan_free_done")); return await view_s_plan(update, context, int(c))
        if b == "plan_d": delete_plan(int(c)); await popup(update, context, tr(lang, "s_plan_deleted")); return await view_s_plans(update, context)
        if b == "discs": return await view_s_discs(update, context)
        if b == "disc_new": return await wiz_start(update, context, "disc_add", "s:discs")
        if b == "disc": return await view_s_disc(update, context, c)
        if b == "disc_e": return await ask(update, context, tr(lang, "s_field_prompt", f=d), "disc_field", f"s:disc:{c}", code=c, field=d)
        if b == "disc_t": dd = disc_get(c); disc_update(c, active=0 if dd and dd["active"] else 1); await popup(update, context, tr(lang, "saved")); return await view_s_disc(update, context, c)
        if b == "disc_d": disc_delete(c); await popup(update, context, tr(lang, "deleted")); return await view_s_discs(update, context)
        if b == "users": return await view_s_users(update, context, int(c or 0))
        if b == "admins": return await view_s_users(update, context, int(c or 0), role="admin")
        if b == "user": return await view_s_user(update, context, int(c))
        tid = int(c) if c.lstrip("-").isdigit() else 0
        if b == "uplan": return await render(update, context, tr(lang, "s_plan_pick"), pairs([B(f"{plan_txt(pl, 'name', lang)} ({pl['days']}d)", f"s:uassign:{tid}:{pl['id']}") for pl in list_plans(False)]) + [[B(tr(lang, "back"), f"s:user:{tid}")]])
        if b == "uassign":
            exp, queued = assign_plan(tid, int(d)); pl = get_plan(int(d)); ul = user_lang(tid) or "fa"; ds = fmt_date(exp, admin_offset(tid))
            await notify_user_fn(tid, tr(ul, "pay_approved", name=esc(plan_txt(pl, "name", ul)), when=tr(ul, "pay_when_queued" if queued else "pay_when_now", d=ds)))
            await popup(update, context, tr(lang, "s_assigned_q" if queued else "s_assigned", d=ds)); return await view_s_user(update, context, tid)
        if b == "urevoke": revoke_plan(tid); await popup(update, context, tr(lang, "s_revoked")); return await view_s_user(update, context, tid)
        if b == "uban": q("UPDATE users SET banned=1-banned WHERE id=?", (tid,), commit=True); await popup(update, context, tr(lang, "s_banned" if get_user(tid)["banned"] else "s_unbanned")); return await view_s_user(update, context, tid)
        if b == "ufree": q("UPDATE users SET free_used=0 WHERE id=?", (tid,), commit=True); await popup(update, context, tr(lang, "s_free_reset")); return await view_s_user(update, context, tid)
        if b == "utests": usage_reset(tid, "tests"); await popup(update, context, tr(lang, "s_tests_reset")); return await view_s_user(update, context, tid)
        if b == "uposts": usage_reset(tid, "posts"); await popup(update, context, tr(lang, "s_posts_reset")); return await view_s_user(update, context, tid)
        if b == "umsg": return await ask(update, context, tr(lang, "s_umsg_prompt"), "umsg", f"s:user:{tid}", target=tid)
        if b == "ureport":
            chs = list_channels(tid)
            if not chs: await popup(update, context, tr(lang, "s_no_channels")); return await view_s_user(update, context, tid)
            return await render(update, context, tr(lang, "s_pick_channel"), pairs([B(f"📣 {x['title'][:22]}", f"s:urep:{tid}:{x['id']}") for x in chs]) + [[B(tr(lang, "back"), f"s:user:{tid}")]])
        if b == "urep": return await render(update, context, report_text(tid, int(d), lang), [[B(tr(lang, "back"), f"s:ureport:{tid}")]])
        if b == "models": return await view_s_models(update, context)
        if b == "model": return await view_s_model(update, context, int(c))
        if b == "model_add": return await wiz_start(update, context, "model_add", "s:models")
        if b == "model_t":
            m = get_model(int(c))
            if not m: await popup(update, context, tr(lang, "notfound"), alert=True); return await view_s_models(update, context)
            turning_off = m["active"]
            update_model(int(c), active=0 if m["active"] else 1, status="ok", fail_count=0)
            if turning_off and gget("test_model_id") == m["id"]: gset("test_model_id", None)
            await popup(update, context, tr(lang, "s_model_off" if m["active"] else "s_model_on")); return await view_s_model(update, context, int(c))
        if b == "model_d":
            mid = int(c)
            if gget("test_model_id") == mid: gset("test_model_id", None)
            delete_model(mid); await popup(update, context, tr(lang, "deleted")); return await view_s_models(update, context)
        if b == "model_e": return await ask(update, context, tr(lang, "s_field_prompt", f=fl(MODEL_FIELDS, d, lang)), "model_field", f"s:model:{c}", mid=int(c), field=d)
        if b == "model_test":
            await run_model_test(update, context, int(c))
            return await view_s_model(update, context, int(c))
        if b == "model_test_pick":
            m = get_model(int(c))
            if not m or m["owner_id"] is not None or not m["active"]:
                return await popup(update, context, tr(lang, "notfound"), alert=True)
            selected = gget("test_model_id") == m["id"]
            gset("test_model_id", None if selected else m["id"])
            await popup(update, context, ("Test Model cleared" if selected else "Test Model selected") if lang == "en" else ("انتخاب Test Model برداشته شد" if selected else "Test Model انتخاب شد"))
            return await view_s_model(update, context, m["id"])
        if b == "models_test":
            await operation_status(context, tr(lang, "s_model_testing")); res = []
            for m in list_models(): ok, out, t = await test_model(m["id"]); res.append(f"{'✅' if ok else '❌'} {esc(m['name'])} ({t}s)" + ("" if ok else f": {esc(out[:60])}"))
            ud["notice"] = "\n".join(res) or "—"; return await view_s_models(update, context)
        if b == "pays": return await view_s_pays(update, context)
        if b == "pay_rc":
            r = pay_get(int(c))
            if r and r["receipt_msg"]:
                try: await context.bot.copy_message(uid, r["receipt_chat"], r["receipt_msg"])
                except Exception as e: await popup(update, context, str(e)[:100])
            return await view_s_pays(update, context)
        if b in ("pay_ok", "pay_no"): return await decide_pay(update, context, int(c), b == "pay_ok", d == "l")
        return await view_super_home(update, context)
    return await go_home(update, context)
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    qy = update.callback_query; u = update.effective_user; context._callback_answered = False
    if qy.data != "c:cancel" and not rate_ok(f"cb:{u.id}", CB_RATE):
        try: await qy.answer(tr(user_lang(u.id) or "fa", "busy_click"))
        except Exception: pass
        return
    ensure_user(u.id, u.username, u.full_name, premium=getattr(u, "is_premium", None))
    if get_user(u.id)["banned"] and not is_super(u.id): return await qy.answer(tr(L(update), "banned"), show_alert=True)
    data = qy.data or "noop"
    parts = data.split(":"); action = parts[1] if len(parts) > 1 else ""
    navigation = data in ("home", "c:cancel") or action in (
        "home", "plans", "plan", "myai", "myai_v", "srcv", "src", "art", "ch",
        "sch", "con", "quiet", "tz", "cat", "catv", "cri", "criv", "que", "rej",
        "models", "model", "users", "admins", "user", "texts", "discs", "disc",
        "pays", "report", "rep", "logs", "lock", "man_close")
    back = (context.user_data.get("await") or {}).get("back", "home")
    channel = int(parts[2]) if len(parts) > 2 and parts[0] == "a" and action == "test" and parts[2].isdigit() else None
    keep = ("disc",) if parts[0] == "u" and action in ("plan", "req", "disc", "discx") else ("bc_src",) if action == "bc_go" else ("qs", "qs_channel") if action == "qe" else ()
    async def work():
        if data == "noop": return
        if data == "c:cancel":
            if not _current_operation.get().replaced_status:
                await send_temp(context, update.effective_chat.id, operation_text(L(update), "cancelled"))
            return await dispatch(update, context, back)
        clear_interaction(context, keep=keep)
        return await dispatch(update, context, data)
    await run_user_operation(update, context, f"callback:{data}", channel, work, replace=navigation, keep=keep)
    if not getattr(context, "_callback_answered", False):
        try: await qy.answer()
        except Exception: pass
# ============================================================
# ورودی‌های متنی (ویزاردها، فیلدها، منبع، افزودن کانال + کد قفل، کد تخفیف، رسید …)
def _input_url(text, explicit_scheme=False):
    """Validate syntax only; local model providers are deliberately supported."""
    if not text or any(c.isspace() or ord(c) < 32 or 127 <= ord(c) <= 159 for c in text): raise ValueError
    if any(c in text for c in "\\<>\"#") or re.search(r"%(?![0-9a-fA-F]{2})", text): raise ValueError
    if not re.match(r"(?i)^https?://", text):
        if explicit_scheme or "://" in text or text.startswith("//"): raise ValueError
        text = "https://" + text
    parsed = urlparse(text)
    if parsed.scheme.lower() not in ("http", "https") or not parsed.netloc or parsed.username is not None or parsed.password is not None: raise ValueError
    host = parsed.hostname
    if not host or any(c in parsed.netloc for c in "{}%") or parsed.netloc.endswith(":"): raise ValueError
    if parsed.netloc.startswith("["):
        if not re.fullmatch(r"\[[0-9a-fA-F:.]+\](?::[0-9]+)?", parsed.netloc): raise ValueError
    elif parsed.netloc.count(":") > 1: raise ValueError
    if parsed.port is not None and not 1 <= parsed.port <= 65535: raise ValueError
    try: ipaddress.ip_address(host)
    except ValueError:
        host = host.rstrip(".").encode("idna").decode("ascii")
        if host.lower() != "localhost" and "." not in host: raise ValueError
        if len(host) > 253 or re.fullmatch(r"[0-9.]+", host): raise ValueError
        if any(not re.fullmatch(r"[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?", label) for label in host.split(".")): raise ValueError
    return parsed._replace(scheme=parsed.scheme.lower()).geturl()

def _input_value(field, raw, lang, name_limit=100):
    """Validate before advancing pending input; errors are ready for a popup."""
    def invalid(fa, en): raise ValueError(en if lang == "en" else fa)
    text = raw.strip()
    if field == "base_url" or field in ("source_url", "api_url"):
        try: return _input_url(raw, explicit_scheme=field == "base_url")
        except (ValueError, TypeError, UnicodeError):
            invalid("نشانی معتبر HTTP(S) بدون فاصله، نام کاربری، رمز یا # وارد کنید." + (" برای مدل http:// یا https:// الزامی است." if field == "base_url" else ""), "Enter a valid HTTP(S) URL without spaces, credentials or #." + (" Model URLs require http:// or https://." if field == "base_url" else ""))
    if field in ("api_key", "model", "code"):
        limit = 256 if field == "model" else 24 if field == "code" else None
        if not raw or any(c.isspace() or ord(c) < 32 or 127 <= ord(c) <= 159 for c in raw) or (limit and len(raw) > limit):
            if field == "api_key": invalid("کلید نباید خالی یا دارای فاصله باشد؛ برای سرویس بدون کلید، - بفرستید.", "Enter a nonempty key without whitespace, or - for an unauthenticated service.")
            if field == "model": invalid("شناسه مدل باید ۱ تا ۲۵۶ نویسه و بدون فاصله باشد.", "Model ID must contain 1–256 characters without whitespace.")
            invalid("کد تخفیف باید ۱ تا ۲۴ نویسه و بدون فاصله باشد.", "Discount code must contain 1–24 characters without whitespace.")
        # callback_data تلگرام سقف ۶۴ بایت دارد؛ بلندترین قالب s:disc_e:<code>:max_uses است
        if field == "code":
            if ":" in raw: invalid("کد تخفیف نمی‌تواند شامل «:» باشد.", "Discount code cannot contain ':'.")
            if len(raw.upper().encode("utf-8")) > 46: invalid("کد برای دکمه‌های مدیریت بیش از حد بلند است.", "Code is too long for the admin buttons; use a shorter one.")
        return "" if field == "api_key" and raw == "-" else raw
    if field in ("name", "name_en"):
        if not text or len(text) > name_limit or any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in text): invalid(f"نام باید ۱ تا {name_limit} نویسه و بدون نویسه کنترلی باشد.", f"Name must contain 1–{name_limit} characters without control characters.")
        return text
    if field == "expires":
        value = text.translate(_FA_DIGITS); now = now_utc()
        try:
            if re.fullmatch(r"[+]?[0-9]+", value):
                days = int(value)
                if days <= 0: raise ValueError
                exp = now + timedelta(days=days)
            else:
                match = re.fullmatch(r"([0-9]{4})[-/]([0-9]{1,2})[-/]([0-9]{1,2})", value)
                if not match: raise ValueError
                exp = datetime(*(int(x) for x in match.groups()), 23, 59, tzinfo=UTC)
            if exp <= now: raise ValueError
        except (ValueError, TypeError, OverflowError): invalid("انقضا باید تعداد روز مثبت یا تاریخ معتبر آینده به صورت YYYY-MM-DD باشد.", "Expiry must be positive days or a valid future date in YYYY-MM-DD format.")
        return exp.isoformat()
    if field == "channel":
        value = text.translate(_FA_DIGITS)
        if re.fullmatch(r"@[A-Za-z][A-Za-z0-9_]{4,31}", value): return value
        if re.fullmatch(r"-[0-9]+", value):
            number = int(value)
            if -(2 ** 63) <= number < 0: return number
        invalid("یوزرنیم معتبر کانال با @ یا شناسه عددی منفی کانال را بفرستید.", "Send a valid @channel_username or a negative integer channel ID.")
    if field == "temperature":
        try: value = float(text.translate(_FA_DIGITS))
        except (ValueError, TypeError): invalid("دما باید عددی بین ۰ و ۲ باشد.", "Temperature must be a finite number between 0 and 2.")
        if not 0 <= value <= 2: invalid("دما باید عددی بین ۰ و ۲ باشد.", "Temperature must be a finite number between 0 and 2.")
        return value
    if field in INT_FIELDS or field in ("days", "daily_posts", "max_sources", "max_channels", "daily_tests", "max_tokens", "max_uses", "priority", "weight", "percent", "price_num"):
        try: value = to_int(text) if field != "price_num" else float(text.translate(_FA_DIGITS).replace(",", ""))
        except (ValueError, TypeError): invalid("عدد صحیح وارد کنید؛ اعشار مجاز نیست.", "Enter an integer; decimals are not allowed.")
        lo, hi = INT_FIELDS.get(field, (1 if field in ("days", "max_tokens", "weight", "percent") else -(2 ** 63) if field == "priority" else 0, 100 if field in ("weight", "percent") else 2 ** 63 - 1))
        if field == "days": hi = (datetime.max.replace(tzinfo=UTC) - now_utc()).days
        if field == "price_num":
            if text == "": return 0.0
            try: value = float(text.translate(_FA_DIGITS).replace(",", ""))
            except (ValueError, TypeError): invalid("قیمت عددی باید یک عدد باشد (مثلا‌ 5 یا 0.5).", "Numeric price must be a number (e.g. 5 or 0.5).")
            if value < 0: invalid("قیمت عددی نمی‌تواند منفی باشد.", "Numeric price cannot be negative.")
            return value
        if not lo <= value <= hi: invalid(f"عدد صحیح بین {lo} و {hi} وارد کنید.", f"Enter an integer between {lo} and {hi}.")
        return value
    if not text: invalid("مقدار نمی‌تواند خالی باشد.", "The value cannot be empty.")
    return text

def _input_access(st, uid, lang):
    kind = st.get("kind"); wiz = st.get("wiz") if kind == "wiz" else None
    user = get_user(uid)
    if user and user["banned"] and not is_super(uid): return tr(lang, "banned")
    if kind in ("plan_field", "disc_field", "gtext", "umsg", "bc") or wiz in ("plan_new", "model_add", "disc_add") or (kind == "model_field" and not st.get("own")):
        if not is_super(uid): return tr(lang, "no_admin")
    if kind in ("field", "cat_style", "crit_weight", "src_add", "src_api_url", "src_api_key", "ch_add", "lockcode", "art_edit") or wiz in ("cat_add", "crit_add", "my_ai_add") or (kind == "model_field" and st.get("own")):
        if not can_admin(uid): return tr(lang, "no_admin")
    cid = st.get("data", {}).get("cid") if wiz in ("cat_add", "crit_add") else st.get("cid") if kind in ("field", "cat_style", "crit_weight", "src_add") else None
    if cid is not None and not channel_owned(cid, uid): return tr(lang, "notfound")
    if kind in ("src_api_url", "src_api_key", "art_edit"):
        item = get_article(st["aid"]) if kind == "art_edit" else get_source(st["sid"])
        if not item or (item["admin_id"] != uid and not is_super(uid)) or not channel_owned(item["channel_id"], uid): return tr(lang, "notfound")
    if kind == "model_field":
        model = get_model(st["mid"])
        if not model or (st.get("own") and model["owner_id"] != uid): return tr(lang, "notfound")
    if kind in ("src_add", "ch_add", "lockcode"):
        lim = admin_limits(uid)
        if not lim["active"]: return tr(lang, "plan_inactive")
        if kind == "src_add" and lim["max_sources"] is not None and count_sources(uid) >= lim["max_sources"]: return tr(lang, "limit_sources", n=lim["max_sources"])
    return None

async def handle_input(update, context, st):
    ud = context.user_data
    if not isinstance(st, dict) or ud.get("await") is not st: return
    msg = update.message; uid = update.effective_user.id; lang = L(update); kind = st["kind"]; back = st["back"]
    raw_text = msg.text or msg.caption or ""; text = raw_text.strip(); text_html = (msg.text_html or msg.caption_html or "").strip()
    if kind not in ("bc", "receipt"):
        try: await msg.delete()
        except Exception: pass
    if ud.get("await") is not st: return
    def done(notice=None):
        current = ud.get("await")
        if current is st: ud.pop("await", None)
        if notice and (current is st or current is None): ud["notice"] = notice
    denied = _input_access(st, uid, lang)
    if denied: return await popup(update, context, denied, alert=True)
    # ---- ویزاردها
    if kind == "wiz":
        steps = WIZ.get(st.get("wiz"), ()); step = st.get("step")
        if type(step) is not int or not 0 <= step < len(steps): done(); return
        key, _, typ = steps[step]
        try: val = _input_value(key, raw_text, lang, name_limit=40 if st["wiz"] in ("cat_add", "crit_add") else 100)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        st["data"][key] = val; st["step"] += 1
        if st["step"] < len(steps): return await wiz_prompt(update, context)
        # Consume the terminal state before the first finalization await.
        done(); dta = st["data"]
        if st["wiz"] == "cat_add": s = get_settings(dta["cid"]); s["categories"].append({"name": dta["name"], "emoji": dta["emoji"][:4], "style": dta["style"][:400]}); save_settings(dta["cid"], s); done(tr(lang, "cat_added"))
        elif st["wiz"] == "crit_add": s = get_settings(dta["cid"]); s["criteria"].append({"name": dta["name"], "weight": dta["weight"]}); save_settings(dta["cid"], s); done(tr(lang, "crit_added"))
        elif st["wiz"] == "plan_new": create_plan(**dta); done(tr(lang, "s_plan_created", name=esc(dta["name"])))
        elif st["wiz"] in ("model_add", "my_ai_add"):
            own = st["wiz"] == "my_ai_add"
            mid = add_model(dta["base_url"], dta["api_key"], dta["model"], owner_id=uid if own else None)
            model = get_model(mid); name = model["name"] if model else dta["model"]
            await operation_status(context, tr(lang, "s_model_testing"))
            if not get_model(mid):
                await popup(update, context, tr(lang, "notfound"), alert=True)
                return await dispatch(update, context, back)
            ok, out, t = await test_model(mid)
            model = get_model(mid)
            if not model:
                await popup(update, context, tr(lang, "notfound"), alert=True)
                return await dispatch(update, context, back)
            result = tr(lang, "my_ai_added" if own else "s_model_added", name=esc(name), res=(tr(lang, "saved") if ok else ai_err_text(err_code(out), lang)) + f" ({t}s)")
            await operation_status(context, result, failed=not ok)
            await popup(update, context, result, alert=not ok)
            return await dispatch(update, context, f"a:myai_v:{mid}" if own else back)
        elif st["wiz"] == "disc_add":
            exp = parse_dt(dta["expires"])
            if not exp or exp <= now_utc():
                st["step"] = next(i for i, item in enumerate(steps) if item[0] == "expires")
                ud["await"] = st
                return await popup(update, context, "انقضا گذشته است؛ تاریخ آینده وارد کنید." if lang != "en" else "Expiry has passed; enter a future date.", alert=True)
            code = disc_create(dta["code"], dta["percent"], dta["expires"], dta["max_uses"]); done(tr(lang, "s_disc_created", code=code) if code else tr(lang, "s_disc_dup"))
        return await dispatch(update, context, back)
    # ---- فیلد تنظیمات کانال
    if kind == "field":
        f = st["field"]; cid = st["cid"]
        if f not in FIELD_LABEL: return await popup(update, context, tr(lang, "notfound"), alert=True)
        label = FIELD_LABEL[f][1 if lang == "en" else 0]
        try: v = _input_value(f, raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        if f == "signature": v = sanitize_html(text_html)[:200]
        elif f not in INT_FIELDS: v = v[:3000]
        update_settings(cid, **{f: v}); done(f"{tr(lang, 'saved')} · {label}: {esc(strip_tags(str(v))[:40])}"); return await dispatch(update, context, back)
    if kind == "cat_style":
        s = get_settings(st["cid"]); i = st["idx"]
        if not text: return await popup(update, context, tr(lang, "empty"), alert=True)
        if not 0 <= i < len(s["categories"]): return await popup(update, context, tr(lang, "notfound"), alert=True)
        s["categories"][i]["style"] = text[:400]; save_settings(st["cid"], s); done(tr(lang, "cat_updated"))
        return await dispatch(update, context, back)
    if kind == "crit_weight":
        s = get_settings(st["cid"]); i = st["idx"]
        if not 0 <= i < len(s["criteria"]): return await popup(update, context, tr(lang, "notfound"), alert=True)
        try: weight = _input_value("weight", raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        s["criteria"][i]["weight"] = weight; save_settings(st["cid"], s); done(tr(lang, "crit_updated"))
        return await dispatch(update, context, back)
    # ---- منبع
    if kind == "src_add":
        cid = st["cid"]
        try: url = _input_value("source_url", raw_text, lang).rstrip("/")
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        sid = add_source(uid, cid, url)
        if not sid: return await popup(update, context, tr(lang, "src_dup"), alert=True)
        done()
        await operation_status(context, tr(lang, "src_checking"))
        source = get_source(sid)
        if not source or not channel_owned(cid, uid): return await popup(update, context, tr(lang, "notfound"), alert=True)
        ok, note = await probe_source(source, lang, added=True)
        source = get_source(sid)
        if not source or not channel_owned(cid, uid): return await popup(update, context, tr(lang, "notfound"), alert=True)
        if ok: q("UPDATE sources SET title=? WHERE id=?", (hostname(url), sid), commit=True)
        else: log_event("WARN", f"منبع جدید {hostname(url)}: تست بارگذاری ناموفق", uid)
        await operation_status(context, note, failed=not ok)
        await popup(update, context, note, alert=not ok)
        return await dispatch(update, context, f"a:srcv:{sid}")
    if kind == "src_api_url":
        sid = st["sid"]
        if text in ("-", "—", "‑"): set_source_api(sid, "", "", ""); done(tr(lang, "src_api_del")); return await dispatch(update, context, back)
        try: api = _input_value("api_url", raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        ud["await"] = {"kind": "src_api_key", "sid": sid, "api": api, "back": back}
        return await render(update, context, f"✏️ {tr(lang, 'src_api_key')}\n\n<i>{tr(lang, 'send_value')}</i>", [[B(tr(lang, "cancel"), "c:cancel")]])
    if kind == "src_api_key":
        sid = st["sid"]
        try:
            key = _input_value("api_key", raw_text, lang)
            api = _input_value("api_url", st["api"], lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        set_source_api(sid, api, key, ""); done()
        await operation_status(context, tr(lang, "src_checking"))
        source = get_source(sid)
        if not source or (source["admin_id"] != uid and not is_super(uid)) or not channel_owned(source["channel_id"], uid): return await popup(update, context, tr(lang, "notfound"), alert=True)
        try: items, _, _ = await _api_discover(source, 10); n = len(items)
        except (httpx.HTTPError, FetchError, RuntimeError, ValueError, TypeError, KeyError) as e: n = 0; log_event("WARN", f"API منبع {hostname(api)}: {err_code(e)}", uid)
        source = get_source(sid)
        if not source or (source["admin_id"] != uid and not is_super(uid)) or not channel_owned(source["channel_id"], uid): return await popup(update, context, tr(lang, "notfound"), alert=True)
        if not n: set_source_active(sid, False, "active")
        note = tr(lang, "src_api_ok", n=n) if n else tr(lang, "src_api_bad")
        await operation_status(context, note, failed=not n)
        await popup(update, context, note, alert=not n)
        return await dispatch(update, context, f"a:srcv:{sid}")
    # ---- افزودن کانال + لایه‌ی امنیتی
    if kind == "ch_add":
        chat = None; fo = getattr(msg, "forward_origin", None)
        if fo and getattr(fo, "chat", None) and fo.chat.type == ChatType.CHANNEL: chat = fo.chat
        else:
            try: identifier = _input_value("channel", raw_text, lang)
            except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
            try: chat = await context.bot.get_chat(identifier)
            except Exception:
                log.warning("channel lookup failed for %s", uid, exc_info=True)
                return await popup(update, context, "به کانال دسترسی ندارم؛ شناسه و دسترسی ربات را بررسی کنید." if lang != "en" else "Cannot access this channel; check its ID and the bot's access.", alert=True)
        if ud.get("await") is not st: return
        if not chat or chat.type != ChatType.CHANNEL: return await popup(update, context, tr(lang, "ch_need_fwd"), alert=True)
        if not await bot_can_post(context.bot, chat.id): return await popup(update, context, tr(lang, "ch_bot_not_admin"), alert=True)
        if ud.get("await") is not st: return
        user_is_admin = False
        try: user_is_admin = any(m.user.id == uid for m in await context.bot.get_chat_administrators(chat.id))
        except Exception:
            try: mem = await context.bot.get_chat_member(chat.id, uid); user_is_admin = mem.status in ("administrator", "creator")
            except Exception: user_is_admin = False
        if ud.get("await") is not st: return
        if not user_is_admin:
            log_event("WARN", f"ثبت کانال «{chat.title}» ({chat.id}) بدون ادمین‌بودن", uid)
            await notify_supers(f"<b>هشدار امنیتی</b>\n<code>{uid}</code> تلاش کرد «{esc(chat.title)}» را بدون ادمین‌بودن ثبت کند.")
            return await popup(update, context, tr(lang, "ch_user_not_admin"), alert=True)
        denied = _input_access(st, uid, lang)
        if denied: return await popup(update, context, denied, alert=True)
        existing = channel_by_chat(chat.id)
        if existing:
            if existing["admin_id"] == uid: update_channel_meta(existing["id"], chat.title, chat.username or ""); done(tr(lang, "ch_exists_mine")); return await dispatch(update, context, f"a:ch:{existing['id']}")
            ud["await"] = {"kind": "lockcode", "cid": existing["id"], "back": back, "tries": 0, "title": chat.title}
            return await render(update, context, tr(lang, "ch_locked"), [[B(tr(lang, "cancel"), "c:cancel")]])
        lim = admin_limits(uid)
        if lim["max_channels"] is not None and len(list_channels(uid)) >= lim["max_channels"]: return await popup(update, context, tr(lang, "limit_channels", n=lim["max_channels"]), alert=True)
        cid = add_channel(uid, chat.id, chat.title or str(chat.id), chat.username or "", uid, lang); log_event("INFO", f"کانال ثبت شد: {chat.title} ({chat.id})", uid)
        done(tr(lang, "ch_added", title=esc(chat.title))); return await dispatch(update, context, f"a:ch:{cid}")
    if kind == "lockcode":
        cid = st["cid"]; ch = get_channel(cid); me = get_user(uid); who = f"{esc(uname(me))} (<code>{uid}</code>)"
        if not ch: return await popup(update, context, tr(lang, "notfound"), alert=True)
        if check_lock(cid, text):
            if not await bot_can_post(context.bot, ch["chat_id"]): return await popup(update, context, tr(lang, "ch_bot_not_admin"), alert=True)
            try: mem = await context.bot.get_chat_member(ch["chat_id"], uid); user_is_admin = mem.status in ("administrator", "creator")
            except Exception: user_is_admin = False
            if ud.get("await") is not st: return
            if not user_is_admin: return await popup(update, context, tr(lang, "ch_user_not_admin"), alert=True)
            denied = _input_access(st, uid, lang)
            if denied: return await popup(update, context, denied, alert=True)
            ch = get_channel(cid)
            if not ch or not check_lock(cid, text): return await popup(update, context, tr(lang, "ch_lock_bad"), alert=True)
            lim = admin_limits(uid)
            if lim["max_channels"] is not None and len(list_channels(uid)) >= lim["max_channels"]: return await popup(update, context, tr(lang, "limit_channels", n=lim["max_channels"]), alert=True)
            if publication_pending(cid): return await popup(update, context, tr(lang, "test_busy"), alert=True)
            old_uid = ch["admin_id"]; ol = user_lang(old_uid) or "fa"
            transfer_channel(cid, uid, lang); done(); log_event("WARN", f"کانال {ch['title']} از {old_uid} به {uid} منتقل شد", uid)
            await notify_user_fn(old_uid, tr(ol, "ch_owner_moved", title=esc(ch["title"]), who=who)); await notify_supers(f"«{esc(ch['title'])}» transferred {old_uid} → {uid}")
            done(tr(lang, "ch_lock_ok", title=esc(ch["title"]))); return await dispatch(update, context, f"a:ch:{cid}")
        old_uid = ch["admin_id"]; ol = user_lang(old_uid) or "fa"
        st["tries"] += 1
        if st["tries"] >= 3: done()
        await notify_user_fn(old_uid, tr(ol, "ch_owner_alert", title=esc(ch["title"]), who=who)); log_event("WARN", f"کد قفل اشتباه برای {ch['title']} توسط {uid}", uid)
        await popup(update, context, tr(lang, "ch_lock_bad"), alert=True)
        if st["tries"] >= 3: return await dispatch(update, context, back)
        if ud.get("await") is st: return await render(update, context, tr(lang, "ch_locked"), [[B(tr(lang, "cancel"), "c:cancel")]])
    # ---- مقاله
    if kind == "art_edit":
        art = get_article(st["aid"])
        if not art or (art["admin_id"] != uid and not is_super(uid)) or art["status"] == "published":
            return await popup(update, context, tr(lang, "notfound"), alert=True)
        if publication_pending(art["channel_id"]): return await popup(update, context, tr(lang, "test_busy"), alert=True)
        if not text_html: return await popup(update, context, tr(lang, "empty"), alert=True)
        article_update(st["aid"], post_html=sanitize_html(text_html)); done(tr(lang, "art_updated"))
        return await dispatch(update, context, back)
    # ---- کد تخفیف
    if kind == "disc":
        d, why = disc_valid(text); pid = str(st["pid"])
        if not d: return await popup(update, context, tr(lang, {"expired": "disc_expired", "exhausted": "disc_exhausted"}.get(why, "disc_bad")), alert=True)
        ud.setdefault("disc", {})[pid] = d["code"]; done(tr(lang, "disc_ok", p=d["percent"]))
        return await dispatch(update, context, back)
    # ---- رسید پرداخت
    if kind == "receipt":
        pid = st["pid"]; p = get_plan(pid); u = get_user(uid)
        if not p or not p["active"]: return await popup(update, context, tr(lang, "notfound"), alert=True)
        if not (msg.photo or msg.document or text): await popup(update, context, tr(lang, "receipt_empty")); return
        if pay_pending_for(uid, pid): done(tr(lang, "req_pending")); return await dispatch(update, context, back)
        # st["final"] is the single source of truth (prorated amount for upgrades, full price text otherwise)
        rid = pay_create(uid, pid, msg.chat_id, msg.message_id, text, st.get("disc"), st.get("final"))
        done(); ud.get("disc", {}).pop(str(pid), None)
        disc = f"\n🎟 {esc(st['disc'])}" if st.get("disc") else ""; note = f"\n📝 {esc(text[:400])}" if text else ""
        header = tr("fa", "s_pay_new", id=rid, who=esc(uname(u)), uid=uid, plan=esc(p["name"]), price=esc(st.get("display") or st.get("final") or p["price"]), disc=disc, note=note); kb = InlineKeyboardMarkup([[B("✅ تأیید / Approve", f"s:pay_ok:{rid}"), B("❌ رد / Reject", f"s:pay_no:{rid}")]])
        for sid in SUPER_ADMIN_IDS:
            try:
                if msg.photo or msg.document: await context.bot.copy_message(sid, msg.chat_id, msg.message_id, caption=header[:1000], parse_mode=HTML, reply_markup=kb)
                else: await context.bot.send_message(sid, header, parse_mode=HTML, reply_markup=kb)
            except Exception as e: log.warning(f"pay notify {sid}: {e}")
        log_event("INFO", f"درخواست پرداخت #{rid} برای پلن {p['name']}", uid); return await view_receipt_ok(update, context)
    # ---- مدیر کلان
    if kind == "plan_field":
        f = st["field"]
        if f not in {item[0] for item in PLAN_FIELDS} or not get_plan(st["pid"]): return await popup(update, context, tr(lang, "notfound"), alert=True)
        try: v = _input_value(f, raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        update_plan(st["pid"], **{f: v}); done(tr(lang, "saved")); return await dispatch(update, context, back)
    if kind == "disc_field":
        f = st["field"]; code = st["code"]
        if f not in ("percent", "max_uses", "expires") or not disc_get(code): return await popup(update, context, tr(lang, "notfound"), alert=True)
        try: v = _input_value(f, raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        disc_update(code, **{f: v}); done(tr(lang, "saved"))
        return await dispatch(update, context, back)
    if kind == "model_field":
        f = st["field"]
        if f not in {item[0] for item in MODEL_FIELDS}: return await popup(update, context, tr(lang, "notfound"), alert=True)
        try: v = _input_value(f, raw_text, lang)
        except (ValueError, TypeError) as e: return await popup(update, context, str(e), alert=True)
        update_model(st["mid"], **{f: v}); done(tr(lang, "saved")); return await dispatch(update, context, back)
    if kind == "gtext":
        if st["key"] not in TEXT_KEYS or st["lg"] not in LANGS: return await popup(update, context, tr(lang, "notfound"), alert=True)
        gtext_set(st["key"], st["lg"], sanitize_html(text_html)); done(tr(lang, "s_text_saved")); return await dispatch(update, context, back)
    if kind == "umsg":
        if not text_html: return await popup(update, context, tr(lang, "empty"), alert=True)
        tl = user_lang(st["target"]) or "fa"
        try: await context.bot.send_message(st["target"], tr(tl, "s_umsg_head") + sanitize_html(text_html), parse_mode=HTML)
        except Exception:
            log.warning("admin message send failed for %s", uid, exc_info=True)
            return await popup(update, context, "پیام ارسال نشد؛ دوباره تلاش کنید." if lang != "en" else "Message could not be sent; please try again.", alert=True)
        done(tr(lang, "s_umsg_sent")); return await dispatch(update, context, back)
    if kind == "bc": done(); ud["bc_src"] = (msg.chat_id, msg.message_id); return await render(update, context, tr(lang, "s_bc_confirm", n=len(list_users())), [[B(tr(lang, "s_bc_go"), "s:bc_go"), B(tr(lang, "cancel"), "s:home")]], force_new=True)
    done(); return await dispatch(update, context, back)
# ============================================================
# پشتیبانی تک‌پیامی
def _sup_header(u):
    who = f"@{u['username']}" if u["username"] else f"<code>{u['id']}</code>"
    return f"📨 <b>{esc(u['name'] or '')}</b> · {who}"
async def support_forward(context, user, msg):
    header = _sup_header(user); sent = 0
    for sid in SUPER_ADMIN_IDS:
        try:
            if msg.text: m = await context.bot.send_message(sid, f"{header}\n{msg.text_html}", parse_mode=HTML, disable_web_page_preview=True)
            else:
                try: m = await context.bot.copy_message(sid, msg.chat_id, msg.message_id, caption=(f"{header}\n{msg.caption_html or ''}")[:1000], parse_mode=HTML)
                except Exception: m = await context.bot.copy_message(sid, msg.chat_id, msg.message_id)
            support_map_set(sid * 10 ** 8 + m.message_id, user["id"]); sent += 1
        except Exception as e: log.warning(f"support fwd {sid}: {e}")
    return sent
async def support_reply(context, sid, msg, target):
    tl = user_lang(target) or "fa"; head = tr(tl, "sup_reply_head")
    if msg.text: await context.bot.send_message(target, head + msg.text_html, parse_mode=HTML, disable_web_page_preview=True)
    else:
        try: await context.bot.copy_message(target, msg.chat_id, msg.message_id, caption=(head + (msg.caption_html or ""))[:1000], parse_mode=HTML)
        except Exception: await context.bot.send_message(target, head, parse_mode=HTML); await context.bot.copy_message(target, msg.chat_id, msg.message_id)
async def _ack(msg, fallback_text, kb=None):
    try: await msg.set_reaction("👌")
    except Exception:
        try: await msg.reply_text(fallback_text, reply_markup=kb)
        except Exception: pass
async def send_temp(context, chat_id, text, seconds=10):
    try: mid = await create_temp(context.bot, chat_id, text)
    except Exception:
        log.debug("temporary message send failed", exc_info=True)
        return
    expire_temp(context.bot, chat_id, mid, seconds)
async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.message; u = update.effective_user; uid = u.id
    if not msg or msg.chat.type != ChatType.PRIVATE: return
    user = ensure_user(uid, u.username, u.full_name, premium=getattr(u, "is_premium", None))
    if user["banned"] and not is_super(uid): return
    lang = L(update); st = context.user_data.get("await")
    if st:
        return await run_user_operation(update, context, f"input:{st.get('kind')}", st.get("cid") or st.get("data", {}).get("cid"), lambda: handle_input(update, context, st))
    if uid in _operations:
        return await popup(update, context, operation_text(lang, "busy"), alert=True)
    if is_super(uid) and msg.reply_to_message:
        target = support_map_get(uid * 10 ** 8 + msg.reply_to_message.message_id)
        if target:
            try: await support_reply(context, uid, msg, target); await _ack(msg, tr(lang, "sup_sent"))
            except Exception as e: await msg.reply_text(tr(lang, "sup_fail", e=str(e)[:100]))
            return
    if support_is_open(uid) and not is_super(uid):
        if not rate_ok(f"sup:{uid}", 2): return
        sent = await support_forward(context, user, msg); await _ack(msg, tr(lang, "sup_received") if sent else tr(lang, "sup_fail", e="—"), InlineKeyboardMarkup([[B(tr(lang, "sup_close"), "u:man_close")]])); return
    if not user_lang(uid): return await view_lang(update, context)
    context.user_data["panel"] = None; await go_home(update, context)
# ============================================================
# دستورات و دیپ‌لینک
def managed_command(handler):
    async def command(update, context):
        return await run_user_operation(update, context, f"command:{handler.__name__}", None, lambda: handler(update, context), replace=True)
    return command


async def _prep(update, context):
    u = update.effective_user; ensure_user(u.id, u.username, u.full_name, premium=getattr(u, "is_premium", None)); context.user_data.pop("await", None); context.user_data["panel"] = None
    return user_lang(u.id)
async def send_deeplink(update, context, key):
    data = await load_deeplink(key); chat_id = update.effective_chat.id; lang = user_lang(update.effective_user.id) or "fa"
    if not data: return await update.message.reply_text(tr(lang, "dl_notfound"))
    short = data.get("short") or ""; full = data.get("full"); media = data.get("media") or {}
    body = full if full and str(full).lower() != "null" else short
    if len(body) > BOT_FULL_MAX: body, _ = fit_html(body, BOT_FULL_MAX)
    if data.get("url") and data.get("show_source", True): body += f'\n\n<a href="{html.escape(data["url"], quote=True)}">{tr(lang, "dl_source")}</a>'
    if media.get("kind") in ("photo", "video", "animation"):
        try: await getattr(context.bot, f"send_{media['kind']}")(chat_id, media["url"], caption=preview_text(short, 100), parse_mode=HTML)
        except Exception as e: log.warning(f"deeplink media: {e}")
    for chunk in split_html(body):
        try: await context.bot.send_message(chat_id, chunk, parse_mode=HTML, disable_web_page_preview=True)
        except BadRequest: await context.bot.send_message(chat_id, downgrade_html(chunk), parse_mode=HTML, disable_web_page_preview=True)
        await asyncio.sleep(.3)
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if context.args and context.args[0].startswith("r_"): return await send_deeplink(update, context, context.args[0][2:])
    if not lang: return await view_lang(update, context)
    await go_home(update, context)
async def cmd_create(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if not lang: return await view_lang(update, context)
    await (view_admin_home if can_admin(update.effective_user.id) else view_plans)(update, context)
async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if not is_super(update.effective_user.id): return await go_home(update, context)
    if not lang: return await view_lang(update, context)
    await view_super_home(update, context)
async def cmd_man(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context); uid = update.effective_user.id
    if not lang: return await view_lang(update, context)
    support_open(uid)   # آغاز/پایان نشست پشتیبانی به مدیر کلان اعلام نمی‌شود؛ فقط پیام‌های واقعی کاربر فرستاده می‌شوند
    await render(update, context, tr(lang, "sup_open"), [[B(tr(lang, "sup_close"), "u:man_close")]], force_new=True)
async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if not lang: return await view_lang(update, context)
    await render(update, context, gtext("help", lang), [[B(tr(lang, "home"), "home")]])
async def cmd_about(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if not lang: return await view_lang(update, context)
    await render(update, context, gtext("about", lang), [[B(tr(lang, "home"), "home")]])
async def cmd_lang(update: Update, context: ContextTypes.DEFAULT_TYPE): await _prep(update, context); await view_lang(update, context)
async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    op = _current_operation.get()
    if not op or not op.replaced_status:
        await send_temp(context, update.effective_chat.id, operation_text(lang or "fa", "cancelled"))
    if not lang: return await view_lang(update, context)
    await go_home(update, context)
async def cmd_unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = await _prep(update, context)
    if not lang: return await view_lang(update, context)
    await go_home(update, context)
# ============================================================
# راه‌اندازی
async def job_tick(context: ContextTypes.DEFAULT_TYPE):
    try: await scheduler_tick(context.bot)
    except Exception as e: log_event("ERROR", f"scheduler: {e}")
async def post_init(app: Application):
    global BOT_USERNAME, NOTIFY_SUPER, NOTIFY_USER
    me = await app.bot.get_me(); BOT_USERNAME = me.username; NOTIFY_SUPER = notify_supers; NOTIFY_USER = notify_user_fn
    await app.bot.set_my_commands([BotCommand("start", "منوی اصلی"), BotCommand("create", "پنل مدیریت / پلن"), BotCommand("man", "پشتیبانی"), BotCommand("about", "درباره"), BotCommand("lang", "زبان"), BotCommand("help", "راهنما"), BotCommand("cancel", "لغو عملیات")], language_code="fa")
    await app.bot.set_my_commands([BotCommand("start", "Main menu"), BotCommand("create", "Admin panel / plan"), BotCommand("man", "Support"), BotCommand("about", "About"), BotCommand("lang", "Language"), BotCommand("help", "Help"), BotCommand("cancel", "Cancel action")])
    app.job_queue.run_repeating(job_tick, interval=TICK_SECONDS, first=15, name="tick"); log_event("INFO", f"ربات @{me.username} راه‌اندازی شد")
    await notify_supers(f"🚀 @{me.username} راه‌اندازی شد · 🤖 مدل‌های فعال {len(list_models(True))} · CF KV {'✅' if CF_ENABLED else '❌'} · تیک هر {TICK_SECONDS}s · AI×{AI_CONCURRENCY} CYCLE×{CYCLE_CONCURRENCY}")
async def post_shutdown(app: Application):
    global _http
    if _http:
        try: await _http.aclose()
        except Exception: pass
async def on_error(update, context):
    log.exception("خطا: %s", context.error)
    try: log_event("ERROR", f"unhandled: {context.error}")
    except Exception: pass
def main():
    global APP
    if not BOT_TOKEN: raise SystemExit("BOT_TOKEN تنظیم نشده است.")
    if not SUPER_ADMIN_IDS: raise SystemExit("SUPER_ADMIN_IDS تنظیم نشده است.")
    init_core(); APP = Application.builder().token(BOT_TOKEN).post_init(post_init).post_shutdown(post_shutdown).concurrent_updates(True).build()
    for cmd, fn in (("start", cmd_start), ("create", cmd_create), ("admin", cmd_admin), ("man", cmd_man), ("help", cmd_help), ("about", cmd_about), ("lang", cmd_lang), ("cancel", cmd_cancel)): APP.add_handler(CommandHandler(cmd, managed_command(fn)))
    APP.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.COMMAND, managed_command(cmd_unknown)))
    APP.add_handler(CallbackQueryHandler(on_callback)); APP.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND, on_message)); APP.add_error_handler(on_error)
    log.info("در حال اجرا…"); APP.run_polling(drop_pending_updates=True, allowed_updates=["message", "callback_query"])
if __name__ == "__main__": main()
# ---------- پایان فایل newsbot.py ----------

