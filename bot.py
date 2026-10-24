"""Rapira Faceit: Telegram-бот + сайт (топ, профили, подбор в команду) в одном процессе.

Переменные окружения:
  BOT_TOKEN     - токен от @BotFather (обязательно)
  ADMIN_IDS     - ваши Telegram ID через запятую (кто может менять таблицу топа)
  PUBLIC_URL    - https-адрес сайта, например https://myapp.onrender.com
  PORT          - порт (хостинг обычно задаёт сам)
  DATABASE_URL  - строка подключения к Postgres (Neon). Если задана, ВСЕ данные (топ, пользователи,
                  матчи, скриншоты, аватарки) хранятся в базе и не пропадают при деплое
  DATA_FILE     - файл с топом игроков (по умолчанию data.json), нужен только без DATABASE_URL
  APP_FILE      - файл с пользователями, командами, заявками (по умолчанию app.json)
  BOT_USERNAME  - необязательно, @username бота (иначе берётся через getMe)
  SHOTS_DIR / AVATARS_DIR - папки для картинок, только без DATABASE_URL

Важно: без DATABASE_URL файлы должны лежать на постоянном диске хостинга.
"""
import asyncio
import copy
import hashlib
import hmac
import json
import logging
import os
import re
import secrets
import tempfile
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

from aiogram import Bot, Dispatcher, F, Router
from aiogram.filters import Command, CommandObject
from aiogram.types import (CallbackQuery, InlineKeyboardButton,
                           InlineKeyboardMarkup, Message, WebAppInfo, BufferedInputFile)
from aiohttp import web

BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
PUBLIC_URL = os.getenv("PUBLIC_URL", "").rstrip("/")
PORT = int(os.getenv("PORT", "8080"))
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
DATA_FILE = Path(os.getenv("DATA_FILE", "data.json"))
APP_FILE = Path(os.getenv("APP_FILE", "app.json"))
BOT_USERNAME = os.getenv("BOT_USERNAME", "").lstrip("@")
BASE = Path(__file__).parent
TOP_N = 100
SHOTS_DIR = Path(os.getenv("SHOTS_DIR", str(APP_FILE.parent / "shots")))
MAX_SHOT = 5 * 1024 * 1024
AVATARS_DIR = Path(os.getenv("AVATARS_DIR", str(APP_FILE.parent / "avatars")))
MAX_AVATAR = 2 * 1024 * 1024
MAPS = [("miramash", "Miramash"), ("palace", "Palace"), ("almero", "Almero"),
        ("mirage_fps", "Mirage FPS"), ("dust2", "Dust II")]
MAP_NAME = dict(MAPS)
SIDE_NAME = {"CT": "Counter-Terrorist", "T": "Terrorist"}
BAN_TURN = 45            # секунд на бан карты, потом бан случайный
VOTE_TIME = 60           # секунд на голосование за карту
CHAT_MAX = 200           # сообщений чата матча в памяти
FRESH = 60              # заявка участвует в подборе, только если игрок был на сайте за последнюю минуту
STALE_DROP = 300         # заявка без игрока дольше 5 минут удаляется
LEAVE_CD = 3600           # запрет на поиск за выход из матча до конца игры (секунд)
QUEUE_TTL = 3600           # поиск без матча сбрасывается через час
MATCH_TTL = 6 * 3600       # активный матч без результата отменяется через 6 часов
KEEP_DAYS = 3              # сколько хранить скриншоты завершённых матчей
HISTORY_DAYS = 90          # сколько хранить историю матчей (кто играл, результат)

# ELO за матч зависит от уровня игрока (по его ELO перед матчем): (до какого уровня включительно, победа, поражение).
# Чем выше уровень, тем меньше дают за победу и больше снимают за поражение. Таблица ниже - для 3x3.
ELO_TIERS = ((3, 35, 15), (6, 30, 20), (9, 25, 25), (10, 20, 30))
# В 4x4 и 5x5 растянуто: к победе прибавляется, а к поражению добавляется столько же (поражение становится больнее).
ELO_STRETCH = {3: 0, 4: 10, 5: 20}
REF_WEEK_LIMIT = 5  # не больше стольких засчитанных приглашений за 7 дней (скользящее окно)
REF_WEEK = 7 * 86400
REF_ELO = 30       # награда пригласившему за нового друга
START_ELO = 1000  # с чего начинает игрок, которого ещё нет в таблице
SIZES = (3, 4, 5)  # пати 3x3, 4x4, 5x5
SESSION_TTL = 30 * 24 * 3600
CODE_TTL = 5 * 60

lock = asyncio.Lock()
router = Router()
bot = Bot(BOT_TOKEN)
NOSTORE = {"Cache-Control": "no-store"}


# ---------- хранилище: Postgres (DATABASE_URL) или файлы ----------
CTYPES = {"png": "image/png", "jpg": "image/jpeg", "webp": "image/webp"}
_pg = None            # пул соединений asyncpg
_cache: dict = {}     # "app" - все данные сайта, "top" - таблица топа
_dirty: set = set()   # ключи, которые нужно записать
_gone: set = set()    # картинки, которые нужно удалить
_wake = None


def _pg_args(url: str):
    """asyncpg не знает sslmode/channel_binding из строки Neon: убираем их и включаем SSL отдельно."""
    u = urlsplit(url)
    q = dict(parse_qsl(u.query))
    mode = q.pop("sslmode", "require")
    q.pop("channel_binding", None)
    return urlunsplit(u._replace(query=urlencode(q))), (False if mode == "disable" else "require")


async def _q(op: str, sql: str, *args):
    """Запрос с повтором: Neon на бесплатном плане засыпает и просыпается не мгновенно."""
    for i in range(3):
        try:
            return await getattr(_pg, op)(sql, *args)
        except Exception:
            if i == 2:
                raise
            logging.warning("Postgres: повторяю запрос (%s)", i + 1)
            await asyncio.sleep(1 + i)


def _blob_path(key: str) -> Path:
    kind, name = key.split("/", 1)
    return (SHOTS_DIR if kind == "shot" else AVATARS_DIR) / name


async def _persist(key: str) -> None:
    obj = _cache.get(key)
    if _pg:
        await _q("execute", "INSERT INTO kv (key, value, updated) VALUES ($1, $2::jsonb, now()) "
                 "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value, updated = now()",
                 key, json.dumps(obj, ensure_ascii=False))
    else:
        _atomic_write(APP_FILE if key == "app" else DATA_FILE, obj)


async def _blob_delete(keys: list) -> None:
    if _pg:
        await _q("execute", "DELETE FROM blobs WHERE key = ANY($1::text[])", keys)
    else:
        for k in keys:
            _blob_path(k).unlink(missing_ok=True)


async def _writer() -> None:
    """Пишет изменения в базу в фоне; несколько быстрых сохранений склеиваются в одну запись."""
    while True:
        await _wake.wait()
        _wake.clear()
        while _dirty or _gone:
            try:
                while _dirty:
                    k = _dirty.pop()
                    try:
                        await _persist(k)
                    except Exception:
                        _dirty.add(k)
                        raise
                if _gone:
                    ks = list(_gone)
                    _gone.difference_update(ks)
                    try:
                        await _blob_delete(ks)
                    except Exception:
                        _gone.update(ks)
                        raise
            except Exception:
                logging.exception("Не удалось записать данные, повтор через 5 секунд")
                await asyncio.sleep(5)


async def store_init() -> None:
    global _pg, _wake
    _wake = asyncio.Event()
    if DATABASE_URL:
        import asyncpg
        dsn, ssl = _pg_args(DATABASE_URL)
        for i in range(5):
            try:
                _pg = await asyncpg.create_pool(dsn, ssl=ssl, min_size=1, max_size=4, timeout=30,
                                                command_timeout=30, statement_cache_size=0,  # пул Neon = pgbouncer
                                                max_inactive_connection_lifetime=120)
                break
            except Exception:
                if i == 4:
                    raise
                logging.warning("Postgres недоступен, повтор через 3 секунды")
                await asyncio.sleep(3)
        await _q("execute", "CREATE TABLE IF NOT EXISTS kv (key text PRIMARY KEY, value jsonb NOT NULL, "
                 "updated timestamptz NOT NULL DEFAULT now())")
        await _q("execute", "CREATE TABLE IF NOT EXISTS blobs (key text PRIMARY KEY, data bytea NOT NULL, "
                 "created timestamptz NOT NULL DEFAULT now())")
        for r in await _q("fetch", "SELECT key, value FROM kv"):
            _cache[r["key"]] = json.loads(r["value"])
        logging.info("Хранилище: Postgres, ключей в базе: %s", len(_cache))
    else:
        logging.warning("DATABASE_URL не задан: данные в файлах и пропадут при деплое на бесплатном хостинге")
    for key, path in (("app", APP_FILE), ("top", DATA_FILE)):  # перенос старых файлов, если в базе пусто
        if key not in _cache and path.exists():
            try:
                _cache[key] = json.loads(path.read_text(encoding="utf-8"))
                if _pg:
                    _dirty.add(key)
                    logging.info("Данные %s перенесены из файла %s в Postgres", key, path)
            except (json.JSONDecodeError, OSError):
                pass
    asyncio.create_task(_writer())
    if _dirty:
        _wake.set()


async def store_flush() -> None:
    for _ in range(40):
        if not (_dirty or _gone):
            return
        _wake.set()
        await asyncio.sleep(0.25)


def _mark(key: str) -> None:
    _dirty.add(key)
    if _wake:
        _wake.set()


async def blob_put(key: str, data: bytes) -> None:
    _gone.discard(key)
    if _pg:
        await _q("execute", "INSERT INTO blobs (key, data) VALUES ($1, $2) "
                 "ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, created = now()", key, data)
    else:
        p = _blob_path(key)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)


async def blob_get(key: str):
    if _pg:
        row = await _q("fetchrow", "SELECT data FROM blobs WHERE key = $1", key)
        return bytes(row["data"]) if row else None
    p = _blob_path(key)
    return p.read_bytes() if p.is_file() else None


def blob_del(key: str) -> None:
    _gone.add(key)
    if _wake:
        _wake.set()


# ---------- топ (как раньше) ----------
def load() -> list:
    return copy.deepcopy(_cache.get("top") or [])


def _atomic_write(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False)
    os.replace(tmp, path)  # атомарная запись


def save(data: list) -> None:
    _cache["top"] = data
    _mark("top")


LEVELS = [800, 950, 1100, 1250, 1400, 1550, 1700, 1850, 2000]


def level_of(elo: int) -> int:
    for i, limit in enumerate(LEVELS, start=1):
        if elo <= limit:
            return i
    return 10


STAT_KEYS = ("kills", "deaths", "wins", "losses")


def ranked(data: list, limit=TOP_N) -> list:
    """Таблица по ELO. В топ-100 попадают сильнейшие: если у 101-го ELO станет выше, чем у 100-го, они меняются местами сами.
    limit=None - вся таблица (игроки за пределами топа тоже хранят статистику и видят её в профиле)."""
    rows = sorted(data, key=lambda p: p["elo"], reverse=True)
    if limit:
        rows = rows[:limit]
    out = []
    for i, p in enumerate(rows, start=1):
        r = {k: v for k, v in p.items() if k not in ("kd", "win")}  # старые поля K/D и % побед больше не используются
        for k in STAT_KEYS:
            r[k] = int(p.get(k) or 0)
        r.update(rank=i, level=level_of(p["elo"]))
        out.append(r)
    return out


def is_admin(m: Message) -> bool:
    return m.from_user is not None and m.from_user.id in ADMIN_IDS


# ---------- база: пользователи, друзья, пати ----------
class ApiError(Exception):
    def __init__(self, status: int, msg: str):
        self.status, self.msg = status, msg


def db_load() -> dict:
    d = copy.deepcopy(_cache.get("app") or {})  # копия: если запрос упадёт, кэш не испортится
    for k in ("users", "sessions", "codes", "friends", "freqs", "parties", "pinvites", "queue", "matches", "settings"):
        d.setdefault(k, {})
    return d


def db_save(db: dict) -> None:
    _cache["app"] = db
    _mark("app")


def cleanup(db: dict) -> bool:
    t = time.time()
    changed = False
    for k in [k for k, v in db["codes"].items() if v["exp"] < t]:
        del db["codes"][k]
    for k in [k for k, v in db["sessions"].items() if v["exp"] < t]:
        del db["sessions"][k]
    for k in [k for k, v in db["queue"].items()
              if v["joined"] < t - QUEUE_TTL or v.get("seen", v["joined"]) < t - STALE_DROP]:
        del db["queue"][k]
    for bu in db["users"].values():
        if bu.get("banned") and bu.get("ban_until") and bu["ban_until"] <= t:
            bu["banned"], bu["ban_reason"], bu["ban_until"] = False, "", 0
            changed = True
    for mid, m in list(db["matches"].items()):
        if m["status"] == "active" and m["created"] < t - MATCH_TTL:
            m["status"], m["ended"] = "cancelled", int(t)
            changed = True
        elif m["status"] == "active" and veto_tick(m, t):
            changed = True
        elif m["status"] in ("finished", "cancelled"):
            ended = m.get("ended", 0)
            if m["shots"] and ended < t - KEEP_DAYS * 86400:  # скриншоты удаляем раньше самого матча
                for sh in m["shots"]:
                    blob_del(f"shot/{mid}_{sh['id']}")
                m["shots"] = []
            if ended < t - HISTORY_DAYS * 86400:
                del db["matches"][mid]
    return changed


def ensure_user(db: dict, tg_id: int, username, first_name) -> dict:
    uid = str(tg_id)
    u = db["users"].get(uid)
    if u is None:
        nick = (username or first_name or "Player").strip()[:32] or "Player"
        u = {"pid": secrets.token_hex(4), "tg_id": tg_id, "nick": nick,
             "faceit": "", "about": "", "created": int(time.time())}
        db["users"][uid] = u
    u["tg_username"] = username or ""
    return u


def new_session(db: dict, uid: str) -> str:
    token = secrets.token_urlsafe(32)
    db["sessions"][token] = {"uid": uid, "exp": time.time() + SESSION_TTL}
    return token


def session_user(db: dict, request: web.Request):
    h = request.headers.get("Authorization", "")
    s = db["sessions"].get(h[7:]) if h.startswith("Bearer ") else None
    if not s or s["exp"] < time.time():
        return None
    return db["users"].get(s["uid"])


def uid_of(u: dict) -> str:
    return str(u["tg_id"])


def user_by_pid(db: dict, pid: str):
    return next((u for u in db["users"].values() if u["pid"] == pid), None)


def pub(u: dict) -> dict:
    return {"pid": u["pid"], "nick": u["nick"], "game_id": u.get("game_id", ""),
            "about": u.get("about", ""), "av": u.get("avatar", 0)}


def top_stats(pid: str):
    """Место, ELO, Kill, Death, Win и Lose игрока, если он есть в топе (привязан к профилю)."""
    r = next((x for x in ranked(load(), None) if x.get("pid") == pid), None)
    if not r:
        return None
    return {"rank": r["rank"], "in_top": r["rank"] <= TOP_N, "elo": r["elo"], "kills": r["kills"], "deaths": r["deaths"],
            "wins": r["wins"], "losses": r["losses"], "level": r["level"]}


def match_history(db, uid: str, limit: int = 20) -> list:
    """Последние завершённые матчи игрока: формат, результат, изменение ELO, с кем играл."""
    rows = []
    for m in db["matches"].values():
        if m["status"] != "finished" or m.get("winner") is None:
            continue
        for i, t in enumerate(m["teams"]):
            if uid in t["members"]:
                rows.append({"id": m["id"], "size": m["size"], "ended": m.get("ended", 0), "win": m["winner"] == i,
                             "elo": (m.get("elo_awards") or {}).get(uid),
                             "with": [db["users"][x]["nick"] for x in t["members"] if x != uid and x in db["users"]]})
    rows.sort(key=lambda r: r["ended"], reverse=True)
    return rows[:limit]


def match_record(db, uid: str) -> dict:
    """Сколько завершённых матчей сыграл игрок и сколько выиграл (история хранится HISTORY_DAYS дней)."""
    games = wins = 0
    for m in db["matches"].values():
        if m["status"] != "finished" or m.get("winner") is None:
            continue
        for i, t in enumerate(m["teams"]):
            if uid in t["members"]:
                games += 1
                wins += 1 if m["winner"] == i else 0
    return {"games": games, "wins": wins}


def id_state(u: dict) -> str:
    """'ok' - ID подтверждён админом, 'pending' - на проверке, 'rejected' - отклонён, '' - не указан/не проверен."""
    return u.get("id_status") or ""


def find_user(db, key: str):
    """Игрок по ID в игре; если такого нет, по точному нику или Telegram-нику."""
    k = key.strip().lstrip("@")
    u = next((x for x in db["users"].values() if x.get("game_id") and x["game_id"] == k), None)
    if u:
        return u
    hits = [x for x in db["users"].values()
            if x["nick"].lower() == k.lower() or (x.get("tg_username") or "").lower() == k.lower()]
    return hits[0] if len(hits) == 1 else None


ONLINE_SEC = 120  # «в сети» = сайт делал запрос за последние 2 минуты
LAST_SEEN = {}    # uid -> время последнего запроса с сайта (только в памяти: запись в базу на каждый опрос не даёт Neon уснуть)


def seen_ts(u) -> float:
    return max(LAST_SEEN.get(uid_of(u), 0), u.get("seen_at", 0) or 0)


def is_online(u) -> bool:
    return time.time() - seen_ts(u) < ONLINE_SEC


def presence(u) -> dict:
    ts = seen_ts(u)
    return {"online": time.time() - ts < ONLINE_SEC, "seen": int(ts)}


def real_party_of(db, uid):
    """Пати, где есть хотя бы двое. Лобби из одного владельца занятостью не считается."""
    p = party_of(db, uid)
    return p if p and len(p["members"]) > 1 else None


def pinvite_msg(owner, p) -> str:
    return f"{owner['nick']} зовёт вас в пати {p['size']}x{p['size']} ({len(p['members'])}/{p['size']})"


def are_friends(db, a, b) -> bool:
    return b in db["friends"].get(a, [])


def make_friends(db, a, b) -> None:
    for x, y in ((a, b), (b, a)):
        lst = db["friends"].setdefault(x, [])
        if y not in lst:
            lst.append(y)


def party_of(db, uid):
    return next((p for p in db["parties"].values() if uid in p["members"]), None)


def pending_invites(db, party_id) -> list:
    return [i for i in db["pinvites"].values() if i["party"] == party_id]


def drop_party(db, p) -> None:
    for k in [k for k, v in db["pinvites"].items() if v["party"] == p["id"]]:
        del db["pinvites"][k]
    db["parties"].pop(p["id"], None)


def relation(db, me, other):
    if me == other:
        return "self", None
    if are_friends(db, me, other):
        return "friend", None
    for r in db["freqs"].values():
        if r["from"] == me and r["to"] == other:
            return "outgoing", r["id"]
        if r["from"] == other and r["to"] == me:
            return "incoming", r["id"]
    return "none", None


def clean_str(v, mx: int, name: str, mn: int = 0) -> str:
    v = " ".join(str(v or "").split())
    if len(v) < mn:
        raise ApiError(400, f"{name}: минимум {mn} символа")
    if len(v) > mx:
        raise ApiError(400, f"{name}: максимум {mx} символов")
    return v


def tg_tag(u: dict) -> str:
    return f"@{u['tg_username']}" if u.get("tg_username") else "без username"


def accept_kb(prefix: str, rid: str):
    return [("✅ Принять", f"{prefix}:acc:{rid}"), ("❌ Отклонить", f"{prefix}:dec:{rid}")]


# ---------- поиск игры, матчи, скриншоты ----------
def team_idx(m, uid):
    for i, t in enumerate(m["teams"]):
        if uid in t["members"]:
            return i
    return None


def queue_of(db, uid):
    return next((t for t in db["queue"].values() if uid in t["members"]), None)


def party_in_queue(db, p) -> bool:
    return bool(p) and any(t.get("party") == p["id"] for t in db["queue"].values())


def match_of(db, uid):
    # активный матч игрока
    return next((m for m in db["matches"].values()
                 if m["status"] == "active" and team_idx(m, uid) is not None), None)


def find_split(tickets, n):
    # ищем две непересекающиеся группы заявок, каждая ровно на n игроков;
    # пати не разбиваются, самые старые заявки берутся первыми
    sizes = [len(t["members"]) for t in tickets[:40]]
    seen = set()

    def dfs(i, a, b, ga, gb):
        if a == n and b == n:
            return ga, gb
        if i == len(sizes) or (i, a, b) in seen:
            return None
        seen.add((i, a, b))
        sz = sizes[i]
        if a + sz <= n:
            r = dfs(i + 1, a + sz, b, ga + [i], gb)
            if r:
                return r
        if b + sz <= n:
            r = dfs(i + 1, a, b + sz, ga, gb + [i])
            if r:
                return r
        return dfs(i + 1, a, b, ga, gb)

    return dfs(0, 0, 0, [], [])


def room_kb():
    if PUBLIC_URL.startswith("https://"):
        return [("Открыть комнату", "url:" + PUBLIC_URL + "/#find")]
    return None


def new_veto():
    first = secrets.randbelow(2)  # какая команда банит первой - случайно
    return {"phase": "ban", "order": [first, 1 - first, first], "bans": [], "started": int(time.time()),
            "votes": {}, "picked": None, "left": []}


def veto_ban(v, mp):
    v["bans"].append({"map": mp, "team": v["order"][len(v["bans"])]})
    v["started"] = int(time.time())
    if len(v["bans"]) >= 3:  # три бана, остаются две карты
        banned = {b["map"] for b in v["bans"]}
        v["left"] = [k for k, _ in MAPS if k not in banned]
        v["phase"] = "vote"


def veto_pick(m, force=False):
    v, total = m["veto"], 2 * m["size"]
    cnt = {k: 0 for k in v["left"]}
    for k in v["votes"].values():
        if k in cnt:
            cnt[k] += 1
    top = max(cnt.values())
    if not force and top * 2 <= total and len(v["votes"]) < total:
        return  # большинства ещё нет и не все проголосовали
    v["picked"] = secrets.choice([k for k, c in cnt.items() if c == top])  # при равенстве - случайно
    v["phase"] = "done"


def veto_tick(m, now) -> bool:
    v = m.get("veto")
    if not v:
        return False
    if v["phase"] == "ban" and now - v["started"] > BAN_TURN:
        taken = {b["map"] for b in v["bans"]}
        veto_ban(v, secrets.choice([k for k, _ in MAPS if k not in taken]))
        return True
    if v["phase"] == "vote" and now - v["started"] > VOTE_TIME:
        veto_pick(m, force=True)
        return True
    return False


def is_fresh(t) -> bool:
    return t.get("seen", t["joined"]) > time.time() - FRESH


def try_match(db, n, outbox):
    while True:
        tickets = sorted((t for t in db["queue"].values() if t["size"] == n and is_fresh(t)),
                         key=lambda t: t["joined"])
        res = find_split(tickets, n)
        if not res:
            return
        teams = []
        for g in res:
            members = [u for i in g for u in tickets[i]["members"]]
            teams.append({"members": members, "captain": secrets.choice(members)})  # капитан случайный
        for i in res[0] + res[1]:
            db["queue"].pop(tickets[i]["id"], None)
        mid = secrets.token_hex(4)
        sides = secrets.choice([["CT", "T"], ["T", "CT"]])  # стороны выдаются случайно
        db["matches"][mid] = {"id": mid, "size": n, "status": "active", "created": int(time.time()),
                              "teams": teams, "shots": [], "report": None, "cancel_votes": [],
                              "sides": sides, "veto": new_veto(), "chat": [], "chat_seq": 0}
        for ti, t in enumerate(teams, start=1):
            cap = db["users"][t["captain"]]
            for uid in t["members"]:
                u = db["users"].get(uid)
                if not u:
                    continue
                if uid == t["captain"]:
                    role = ("Вы капитан команды: забаньте карты в комнате матча, а после игры "
                            "прикрепите скриншот результата.")
                else:
                    role = f"Капитан вашей команды: {cap['nick']} ({tg_tag(cap)})."
                outbox.append((u["tg_id"], f"Матч {n}x{n} найден! Вы в команде {ti}, сторона: {SIDE_NAME[sides[ti - 1]]}.\n{role}", room_kb()))


def drop_games(db, u, outbox, why: str) -> list:
    """Снимает игрока с поиска и отменяет его активный матч (даже если он в сети). Возвращает заметки для админа."""
    notes, uid = [], uid_of(u)
    t = queue_of(db, uid)
    if t:
        del db["queue"][t["id"]]
        notes.append("поиск игры отменён")
        for mem in t["members"]:
            mu = db["users"].get(mem)
            if mu and mem != uid:
                outbox.append((mu["tg_id"], f"Поиск игры отменён: {why}. Запустите поиск заново.", None))
    mt = match_of(db, uid)
    if mt:
        end_match(db, mt, "cancelled", outbox, f"Матч отменён: {why}.")
        notes.append("матч отменён")
    return notes


def award_ref(inv: dict) -> int:
    """+REF_ELO пригласившему (строка в таблице создаётся, если её ещё нет). Возвращает его новое ELO."""
    data = load()
    r = next((x for x in data if x.get("pid") == inv["pid"]), None)
    if r is None:
        r = {"nick": inv["nick"], "elo": START_ELO, "pid": inv["pid"]}
        for k in STAT_KEYS:
            r[k] = 0
        data.append(r)
    r["elo"] = int(r["elo"]) + REF_ELO
    save(data)
    return r["elo"]


def ref_recent(db, inv_uid: str) -> list:
    """Время засчитанных приглашений игрока за последние 7 дней (старые первыми)."""
    t = time.time() - REF_WEEK
    return sorted(x["ref_paid_at"] for x in db["users"].values()
                  if x.get("ref_by") == inv_uid and x.get("ref_paid") and x.get("ref_paid_at", 0) > t)


def pay_ref(db, u, outbox) -> None:
    """Когда ID приглашённого подтверждён - платим пригласившему +REF_ELO (один раз за друга)."""
    inv = db["users"].get(u.get("ref_by", ""))
    if not inv or u.get("ref_paid") or inv.get("banned"):
        return
    gid = u.get("game_id")
    if gid and any(x is not u and x.get("ref_paid") and x.get("game_id") == gid for x in db["users"].values()):
        return  # этот игровой ID уже приносил награду (защита от лишних аккаунтов)
    if len(ref_recent(db, u["ref_by"])) >= REF_WEEK_LIMIT:
        u["ref_skipped"] = True  # лимит недели: за этого друга награды не будет
        outbox.append((inv["tg_id"], f"Ваш друг {u['nick']} подтвердил ID, но лимит наград за приглашения "
                       f"({REF_WEEK_LIMIT} в неделю) исчерпан, ELO за него не начислено.", None))
        return
    u["ref_paid"], u["ref_paid_at"] = True, int(time.time())
    inv["ref_count"] = inv.get("ref_count", 0) + 1
    new_elo = award_ref(inv)
    outbox.append((inv["tg_id"], f"Ваш друг {u['nick']} подтвердил ID в игре: +{REF_ELO} ELO (теперь {new_elo}).", None))


def cd_left(u) -> int:
    """Секунд до конца запрета на поиск (за выход из матча)."""
    return max(0, int(u.get("cd_until", 0) - time.time()))


def settle_elo(db, m, outbox):
    """Начисляет ELO по итогу матча. Если результат поменяли (/winner) или матч отменили (/cancelmatch),
    сначала возвращает то, что было начислено раньше."""
    old = m.get("elo_awards") or {}
    win = m.get("winner") if m["status"] == "finished" else None
    if not old and win is None:
        return
    data = load()
    by_pid = {r.get("pid"): r for r in data if r.get("pid")}
    by_uid = {uid_of(u): u for u in db["users"].values()}
    for uid, d in old.items():  # откат прежнего начисления
        u = by_uid.get(uid)
        r = by_pid.get(u["pid"]) if u else None
        if r:
            r["elo"] = max(0, int(r["elo"]) - d)
    new = {}
    if win is not None:
        for ti, t in enumerate(m["teams"]):
            for uid in t["members"]:
                u = by_uid.get(uid)
                if not u:
                    continue
                r = by_pid.get(u["pid"])
                if r is None:
                    r = {"nick": u["nick"], "elo": START_ELO, "pid": u["pid"]}
                    for k in STAT_KEYS:
                        r[k] = 0
                    data.append(r)
                    by_pid[u["pid"]] = r
                before = int(r["elo"])
                _, w, l = next(x for x in ELO_TIERS if level_of(before) <= x[0])
                ext = ELO_STRETCH.get(m["size"], 0)
                delta = w + ext if ti == win else -(l + ext)
                r["elo"] = max(0, before + delta)
                new[uid] = r["elo"] - before
                outbox.append((u["tg_id"], f"ELO за матч: {new[uid]:+d}, теперь у вас {r['elo']}.", None))
    if new:
        m["elo_awards"] = new
    else:
        m.pop("elo_awards", None)
    save(data)


def end_match(db, m, status, outbox, text, winner=None):
    m["status"], m["ended"] = status, int(time.time())
    if winner is not None:
        m["winner"] = winner
    settle_elo(db, m, outbox)
    for t in m["teams"]:
        for uid in t["members"]:
            u = db["users"].get(uid)
            if u:
                outbox.append((u["tg_id"], text, None))


def notify_admins_dispute(db, m, outbox):
    lines = [f"{'Матч на проверку' if m.get('review') else 'Спорный матч'} {m['id']} ({m['size']}x{m['size']})"]
    for i, t in enumerate(m["teams"], start=1):
        names = ", ".join(db["users"][u]["nick"] + (" (кап.)" if u == t["captain"] else "")
                          for u in t["members"] if u in db["users"])
        lines.append(f"Команда {i}: {names}")
    r = m.get("report") or {}
    who = f" капитаном команды {r['team'] + 1}" if "team" in r else ""
    lines.append(f"Заявлено{who}: победила команда {r.get('winner', 0) + 1}, счёт {r.get('score') or '-'}")
    lines.append(f"Решение: /winner {m['id']} CT или /winner {m['id']} T - какая сторона победила на ФИНАЛЬНОМ скрине "
                 f"(стороны там уже поменяны)\nОтмена: /cancelmatch {m['id']}")
    for a in ADMIN_IDS:
        outbox.append((a, "\n".join(lines), None))
        for sh in m["shots"][:6]:
            outbox.append((a, f"Скриншот: команда {sh['team'] + 1}", None, f"shot/{m['id']}_{sh['id']}"))


def other_side(sd: str) -> str:
    return "T" if sd == "CT" else "CT"


def match_view(db, m, me):
    ti = team_idx(m, me)
    teams = []
    for t in m["teams"]:
        mem = []
        for uid in t["members"]:
            u = db["users"].get(uid)
            if not u:
                continue
            d = {**pub(u), "captain": uid == t["captain"], "me": uid == me}
            if uid == t["captain"] and u.get("tg_username"):
                d["tg"] = u["tg_username"]  # Telegram виден только у капитанов, чтобы договориться о лобби
            mem.append(d)
        teams.append({"members": mem})
    rep = m.get("report")
    v, vv = m.get("veto"), None
    if v:
        cnt = {k: 0 for k in v["left"]}
        for k in v["votes"].values():
            if k in cnt:
                cnt[k] += 1
        limit = BAN_TURN if v["phase"] == "ban" else VOTE_TIME
        vv = {"phase": v["phase"], "pool": [k for k, _ in MAPS], "bans": v["bans"],
              "turn": v["order"][len(v["bans"])] if v["phase"] == "ban" else None,
              "left": v["left"], "votes": cnt, "my_vote": v["votes"].get(me), "picked": v["picked"],
              "timer": max(0, int(limit - (time.time() - v["started"]))) if v["phase"] in ("ban", "vote") else 0}
    return {"id": m["id"], "size": m["size"], "team": ti, "captain": m["teams"][ti]["captain"] == me,
            "sides": m.get("sides"), "veto": vv,
            "teams": teams, "shots": [{"id": x["id"], "team": x["team"]} for x in m["shots"]],
            "report": {"team": rep["team"], "winner": rep["winner"], "score": rep["score"]} if rep else None,
            "cancel_votes": m["cancel_votes"]}


# ---------- заявки в друзья и приглашения в пати (общая логика для сайта и бота) ----------
def resolve_freq(db, rid, actor, accept, outbox) -> str:
    if actor is None:
        raise ApiError(401, "Сначала войдите на сайте через Telegram")
    r = db["freqs"].get(rid)
    if not r:
        raise ApiError(404, "Заявка уже обработана")
    if uid_of(actor) != r["to"]:
        raise ApiError(403, "Это заявка не для вас")
    del db["freqs"][rid]
    sender = db["users"].get(r["from"])
    if not sender:
        return "Игрок не найден"
    if not accept:
        return "Заявка отклонена"
    make_friends(db, r["to"], r["from"])
    outbox.append((sender["tg_id"], f"{actor['nick']} принял вашу заявку в друзья.", None))
    return f"{sender['nick']} теперь в друзьях"


def resolve_pinvite(db, iid, actor, accept, outbox) -> str:
    if actor is None:
        raise ApiError(401, "Сначала войдите на сайте через Telegram")
    inv = db["pinvites"].get(iid)
    p = db["parties"].get(inv["party"]) if inv else None
    if not inv or not p:
        db["pinvites"].pop(iid, None)
        raise ApiError(404, "Приглашение уже недействительно")
    me = uid_of(actor)
    if me != inv["to"]:
        raise ApiError(403, "Это приглашение не для вас")
    owner = db["users"].get(p["owner"])
    if not accept:
        del db["pinvites"][iid]
        if owner:
            outbox.append((owner["tg_id"], f"{actor['nick']} отклонил приглашение в пати.", None))
        return "Приглашение отклонено"
    mp = party_of(db, me)
    if mp and len(mp["members"]) > 1:
        raise ApiError(400, "Вы уже в пати - сначала выйдите из неё")
    if queue_of(db, me):
        raise ApiError(400, "Сначала отмените поиск игры")
    if mp:  # своё лобби без других игроков закрываем, чтобы принять приглашение
        drop_party(db, mp)
    if party_in_queue(db, p):
        raise ApiError(400, "Эта пати уже ищет игру")
    if len(p["members"]) >= p["size"]:
        raise ApiError(400, "В пати нет свободных мест")
    p["members"].append(me)
    for k in [k for k, v in db["pinvites"].items() if v["to"] == me]:
        del db["pinvites"][k]
    for m in p["members"]:
        if m != me and m in db["users"]:
            outbox.append((db["users"][m]["tg_id"],
                           f"{actor['nick']} в вашей пати ({len(p['members'])}/{p['size']}).", None))
    return f"Вы в пати {owner['nick'] if owner else ''}".strip()


async def flush(outbox: list) -> None:
    for item in outbox:
        tg_id, text, kb = item[:3]
        photo = item[3] if len(item) > 3 else None
        try:
            markup = None
            if kb:
                markup = InlineKeyboardMarkup(inline_keyboard=[[
                    InlineKeyboardButton(text=t, url=d[4:]) if d.startswith("url:")
                    else InlineKeyboardButton(text=t, callback_data=d) for t, d in kb]])
            data = await blob_get(photo) if photo else None
            if data:
                await bot.send_photo(tg_id, BufferedInputFile(data, filename="screenshot.jpg"), caption=text, reply_markup=markup)
            else:
                await bot.send_message(tg_id, text, reply_markup=markup)
        except Exception:
            logging.warning("Не удалось отправить сообщение %s", tg_id)


# ---------- команды бота ----------
@router.message(Command("start"))
async def cmd_start(m: Message, command: CommandObject):
    arg = (command.args or "").strip()
    if arg.startswith("auth_"):
        code = arg[5:]
        async with lock:
            entry = db_load()["codes"].get(code)
            ok = bool(entry and entry["exp"] >= time.time() and not entry.get("uid"))
        if not ok:
            return await m.answer("Ссылка для входа устарела. Вернитесь на сайт и нажмите «Войти» ещё раз.")
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="✅ Подтвердить вход", callback_data=f"auth:ok:{code}"),
            InlineKeyboardButton(text="Отмена", callback_data=f"auth:no:{code}")]])
        return await m.answer("Вход на сайт Rapira Faceit.\nЕсли вы сами нажали «Войти через Telegram» "
                              "- подтвердите. Если нет - нажмите «Отмена».", reply_markup=kb)
    if arg.startswith("ref_"):
        outbox = []
        async with lock:
            db = db_load()
            inv_uid, me_uid = arg[4:], str(m.from_user.id)
            inv = db["users"].get(inv_uid)
            # работает только для тех, у кого бота ещё нет (нет аккаунта), и только пока админ включил рефералку
            if (db["settings"].get("referral") and inv and not inv.get("banned")
                    and inv_uid != me_uid and me_uid not in db["users"]):
                u = ensure_user(db, m.from_user.id, m.from_user.username, m.from_user.first_name)
                u["ref_by"] = inv_uid
                db_save(db)
                outbox.append((inv["tg_id"], f"Ваш друг {u['nick']} впервые открыл бота по вашей ссылке. "
                               f"+{REF_ELO} ELO придёт, когда его ID в игре будет подтверждён.", None))
        await flush(outbox)
    text = ("Топ игроков FACEIT.\n/top - топ-10\n/profile - ваш профиль и пати\n"
            f"Ваш Telegram ID: {m.from_user.id}")
    if is_admin(m):
        text += ("\n\nКоманды админа:\n"
                 "/untop ID_или_@ник - убрать игрока из топа\n"
                 "/resetid ID_или_ник - сбросить ID игрока (снимает с поиска и отменяет его матч, даже если он в сети)\n"
                 "/leaver ID_или_ник [30м|1ч] - вышел из матча раньше времени: матч отменяется, поиск закрыт (по умолчанию 1ч), /unleaver - снять\n"                 "/referral on|off - включить или убрать вкладку «Пригласить друга» на сайте (+30 ELO, когда ID нового игрока подтвердят; не больше 5 в неделю на человека)\n"

                 "/ban ID_или_@ник [срок] [причина] - блокировка (срок: 30м, 1ч, 1д; без срока навсегда), /unban, /banlist\n"
                 "/users - зарегистрировались, но ещё не в топе\n"
                 "/userstop - игроки, которые уже в топе\n"
                 "/stat ID ELO [Kill] [Death] [Win] [Lose] - начислить статистику (со знаком + или - прибавляет)\n"
                 "/season [ELO] [все] - новый сезон: ELO у всех в топе станет 300 (или число, которое укажете)\n"
                 "/matches - последние матчи, /match ID - подробности и скриншоты\n"
                 "/winner ID CT|T - какая сторона победила на ФИНАЛЬНОМ скрине (стороны там уже поменяны)\n"
                 "/cancelmatch ID - отменить матч, даже уже засчитанный\n"
                 "/ids - ID игроков на проверке, /verify ID - подтвердить ID вручную\n"
                 "/broadcast Текст - рассылка всем игрокам (с предпросмотром)")
    kb = None
    if PUBLIC_URL.startswith("https://"):
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Открыть сайт", web_app=WebAppInfo(url=PUBLIC_URL))]])
    await m.answer(text, reply_markup=kb)


@router.callback_query(F.data.startswith("auth:"))
async def cb_auth(c: CallbackQuery):
    _, act, code = c.data.split(":", 2)
    async with lock:
        db = db_load()
        entry = db["codes"].get(code)
        if not entry or entry["exp"] < time.time():
            text = "Ссылка устарела. Нажмите «Войти» на сайте ещё раз."
        elif act == "ok":
            u = ensure_user(db, c.from_user.id, c.from_user.username, c.from_user.first_name)
            entry["uid"] = uid_of(u)
            db_save(db)
            text = "Готово! Вернитесь на сайт - вход выполнен."
        else:
            del db["codes"][code]
            db_save(db)
            text = "Вход отменён."
    try:
        await c.message.edit_text(text)
    except Exception:
        pass
    await c.answer()


@router.callback_query(F.data.startswith("fr:") | F.data.startswith("pi:"))
async def cb_decide(c: CallbackQuery):
    kind, act, rid = c.data.split(":", 2)
    outbox = []
    async with lock:
        db = db_load()
        actor = db["users"].get(str(c.from_user.id))
        try:
            fn = resolve_freq if kind == "fr" else resolve_pinvite
            msg = fn(db, rid, actor, act == "acc", outbox)
            db_save(db)
        except ApiError as e:
            msg = e.msg
    try:
        await c.message.edit_text(msg)
    except Exception:
        pass
    await c.answer()
    await flush(outbox)


@router.message(Command("profile"))
async def cmd_profile(m: Message):
    async with lock:
        db = db_load()
        u = db["users"].get(str(m.from_user.id))
        p = party_of(db, str(m.from_user.id)) if u else None
        n = len(db["friends"].get(str(m.from_user.id), []))
    if not u:
        return await m.answer("Профиля ещё нет. Откройте сайт и войдите через Telegram."
                              + (f"\n{PUBLIC_URL}" if PUBLIC_URL else ""))
    lines = [u["nick"],
             f"ID в игре: {u['game_id']}" if u.get("game_id") else "ID в игре не указан (добавьте в профиле на сайте)",
             f"Друзей: {n}",
             f"Пати {p['size']}x{p['size']}: {len(p['members'])}/{p['size']}" if p else "Вы не в пати"]
    if PUBLIC_URL:
        lines.append(PUBLIC_URL + "/#party")
    await m.answer("\n".join(lines))


@router.message(Command("top"))
async def cmd_top(m: Message):
    async with lock:
        rows = ranked(load())[:10]
    if not rows:
        await m.answer("Таблица пока пуста.")
        return
    await m.answer("\n".join(f"{p['rank']}. {p['nick']} - {p['elo']}" for p in rows))


MSK = timezone(timedelta(hours=3))
STATUS_RU = {"active": "идёт", "disputed": "спорный", "finished": "завершён", "cancelled": "отменён"}


def _dt(ts) -> str:
    return datetime.fromtimestamp(ts, MSK).strftime("%d.%m %H:%M") if ts else "-"


async def _send_long(m: Message, lines: list) -> None:
    chunk = ""
    for line in lines:
        if len(chunk) + len(line) + 1 > 3800:
            await m.answer(chunk)
            chunk = ""
        chunk += line + "\n"
    if chunk:
        await m.answer(chunk)


@router.message(Command("admin"))
async def cmd_admin(m: Message):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    await m.answer(
        "Команды администратора:\n"
        "/users - зарегистрировались, но не в топе (/users 2 - страница, /users ник - поиск)\n"
        "/userstop - игроки в топе (/userstop 2 - страница, /userstop ник - поиск)\n"
        "/untop ID_или_@ник - убрать игрока из топа\n"
        "/stat ID ELO [Kill] [Death] [Win] [Lose] - начислить статистику игроку, он попадёт в топ с профилем (+25 прибавляет)\n"
        "/season [ELO] [все] - новый сезон: ELO у всех в топе станет 300, можно указать своё число (перед сбросом присылает текущий топ)\n"
        "/matches - последние матчи (/matches спор - только спорные)\n"
        "/match ID - подробности матча и скриншоты\n"
        "/winner ID CT|T - засчитать победу: CT или T = какая сторона победила на ФИНАЛЬНОМ скрине (стороны там уже поменяны), работает и для засчитанных\n"
        "/cancelmatch ID - отменить матч, даже уже засчитанный\n"
        "/resetid ID_или_ник - сбросить ID игрока (снимает с поиска и отменяет его матч, даже если он в сети)\n"        "/elo - таблица начисления ELO за матчи (победа и поражение по форматам)\n"

        "/leaver ID_или_ник [30м|1ч] - вышел из матча раньше времени: матч отменяется, поиск закрыт (по умолчанию 1ч), /unleaver - снять\n"

        "/broadcast Текст - рассылка всем игрокам (с предпросмотром)")


def _page_arg(arg: str):
    arg = (arg or "").strip()
    if arg.isdigit() and int(arg) <= 99:
        return int(arg), ""
    return 1, arg.lower().lstrip("@")


def _top_sets(top):
    return {p["nick"].lower() for p in top if not p.get("pid")}, {p["pid"] for p in top if p.get("pid")}


@router.message(Command("users", "user"))
async def cmd_users(m: Message, command: CommandObject):
    # только те, кто зарегистрировался, но ещё не в топе (чтобы не мешали уже добавленные)
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    page, q = _page_arg(command.args)
    async with lock:
        db, top = db_load(), load()
    nicks, pids = _top_sets(top)
    users = sorted(db["users"].values(), key=lambda u: u.get("created", 0), reverse=True)  # новые сверху
    users = [u for u in users if u["pid"] not in pids and u["nick"].lower() not in nicks]
    if q:
        users = [u for u in users if q in u["nick"].lower() or q in (u.get("tg_username") or "").lower()
                 or q in (u.get("game_id") or "")]
    if not users:
        return await m.answer("Никого не нашёл среди тех, кто не в топе." if q else
                              "Все зарегистрированные уже в топе (или никто не регистрировался). Топ: /userstop")
    per = 40
    pages = (len(users) + per - 1) // per
    page = min(page, pages)
    lines = [f"Зарегистрировались, но не в топе: {len(users)}" + (f" (страница {page}/{pages}, дальше: /users {page + 1})" if pages > 1 else "")]
    for i, u in enumerate(users[(page - 1) * per:page * per], start=(page - 1) * per + 1):
        lines.append(f"{i}. {u['nick']} | ID {u.get('game_id') or '-'} | {tg_tag(u)}")
    lines.append("Добавить в топ: /stat ID_в_игре ELO. Кто уже в топе: /userstop")
    await _send_long(m, lines)


@router.message(Command("userstop"))
async def cmd_userstop(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    page, q = _page_arg(command.args)
    async with lock:
        db, top = db_load(), load()
    by_pid = {u["pid"]: u for u in db["users"].values()}
    rows = []
    for r in ranked(top, None):
        u = by_pid.get(r.get("pid"))
        rows.append((r, u))
    if q:
        rows = [(r, u) for r, u in rows if q in r["nick"].lower() or (u and (q in (u.get("tg_username") or "").lower()
                                                                          or q in (u.get("game_id") or "")))]
    if not rows:
        return await m.answer("В топе никого не нашёл." if q else "В топе пока никого. Добавить: /stat ID_в_игре ELO")
    per = 40
    pages = (len(rows) + per - 1) // per
    page = min(page, pages)
    lines = [f"В топе: {len(rows)}" + (f" (страница {page}/{pages}, дальше: /userstop {page + 1})" if pages > 1 else "")]
    for r, u in rows[(page - 1) * per:page * per]:
        who = f"ID {u.get('game_id') or '-'} | {tg_tag(u)}" if u else "без профиля на сайте"
        lines.append(f"{r['rank']}. {r['nick']} | ELO {r['elo']} | {who}" + (" | вне топ-100" if r["rank"] > TOP_N else ""))
    lines.append("Убрать из топа: /untop ID_в_игре или @ник (для строк «без профиля» ник из списка)")
    await _send_long(m, lines)


@router.message(Command("untop"))
async def cmd_untop(m: Message, command: CommandObject):
    # убирает из топа именно игрока (по ID в игре или @нику), а не просто строку с ником
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    key = (command.args or "").strip()
    if not key:
        return await m.answer("Формат: /untop ID_в_игре или @ник\nСписок тех, кто в топе: /userstop")
    async with lock:
        db, data = db_load(), load()
        u = find_user(db, key)
        if u:
            keep = [p for p in data if p.get("pid") != u["pid"]]
            if len(keep) == len(data):  # нет строки с профилем: возможно, осталась старая строка с тем же ником без привязки
                keep = [p for p in data if p.get("pid") or p["nick"].lower() != u["nick"].lower()]
            name = u["nick"]
        else:  # старая строка без профиля: убираем по точному нику
            k = key.lstrip("@").lower()
            keep = [p for p in data if p.get("pid") or p["nick"].lower() != k]
            name = key.lstrip("@")
        if len(keep) == len(data):
            return await m.answer("Такого игрока нет в топе. Список: /userstop")
        save(keep)
    await m.answer(f"{name} убран из топа. Профиль и аккаунт на сайте остались.")


def _apply_num(cur: int, token: str) -> int:
    # "+10" или "-3" - прибавить или отнять, "10" - поставить значение
    v = int(token)
    return max(0, min(1_000_000, cur + v if token[0] in "+-" else v))


@router.message(Command("stat"))
async def cmd_stat(m: Message, command: CommandObject):
    # начисление после матча: игрок попадает в топ, и к его строке привязывается профиль
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    usage = ("Формат: /stat ID_в_игре ELO [Kill] [Death] [Win] [Lose]\n"
             "Поставить значения: /stat 12345678 1500 120 95 14 9\n"
             "Прибавить после матча: /stat 12345678 +25 +10 +8 +1 +0\n"
             "Знак + или - прибавляет или отнимает, число без знака ставит значение. "
             "Показатель, который не нужно менять, просто не пишите (с конца).")
    parts = (command.args or "").split()
    if len(parts) < 2 or len(parts) > 6:
        return await m.answer(usage)
    try:
        for t in parts[1:]:
            int(t)
    except ValueError:
        return await m.answer(usage)
    async with lock:
        db, data = db_load(), load()
        u = find_user(db, parts[0])
        if not u:
            return await m.answer("Игрок не найден. Список зарегистрированных: /users")
        before = {x.get("pid") or x["nick"].lower(): x["nick"] for x in ranked(data)}
        row = next((x for x in data if x.get("pid") == u["pid"]), None)
        if row is None:
            same = next((x for x in data if x["nick"].lower() == u["nick"].lower()), None)
            if same and not same.get("pid"):
                row = same  # ник уже был в топе без привязки: привязываем
            elif same:
                return await m.answer(f"В топе уже есть другой игрок с ником {same['nick']}. Сначала уберите его командой /untop ID_в_игре")
        if row is None:
            if parts[1][0] in "+-":
                return await m.answer("Игрока ещё нет в топе, укажите ELO числом без знака: /stat ID 1000")
            row = {"nick": u["nick"], "elo": 0}
            data.append(row)
        row.pop("kd", None)
        row.pop("win", None)
        row["elo"] = _apply_num(row.get("elo", 0), parts[1])
        for k, token in zip(STAT_KEYS, parts[2:]):
            row[k] = _apply_num(int(row.get(k) or 0), token)
        for k in STAT_KEYS:
            row[k] = int(row.get(k) or 0)
        row["pid"] = u["pid"]
        save(data)
        full = ranked(data, None)
        place = next(r["rank"] for r in full if r.get("pid") == u["pid"])
        after = {x.get("pid") or x["nick"].lower() for x in full[:TOP_N]}
        dropped = [(k, n) for k, n in before.items() if k not in after and k not in (u["pid"], u["nick"].lower())]
        notes = []
        if place > TOP_N:
            notes.append(f"Место №{place}: вне топ-{TOP_N}, статистика сохранена и видна в профиле игрока.")
        else:
            notes.append(f"Место в топе: №{place}.")
        outbox = []
        for k, n in dropped:
            notes.append(f"Из топа-{TOP_N} вылетел: {n} (ELO ниже, чем у {u['nick']}).")
            du = next((x for x in db["users"].values() if x["pid"] == k), None)
            if du:
                outbox.append((du["tg_id"], f"Вы вылетели из топа-{TOP_N}: вас обошёл {u['nick']}. Статистика в профиле сохранена.", None))
        res = f"ELO {row['elo']}, Kill {row['kills']}, Death {row['deaths']}, Win {row['wins']}, Lose {row['losses']}"
        outbox.append((u["tg_id"], f"Вам начислена статистика: {res}. " + notes[0] + f" Ваш профиль: {PUBLIC_URL or 'на сайте'}", None))
    await m.answer(f"Готово: {u['nick']} (ID {u.get('game_id') or '-'}) - {res}.\n" + "\n".join(notes))
    await flush(outbox)


# ---------- новый сезон: сброс ELO у всех в топе ----------
PENDING_SEASON: dict = {}


SEASON_ELO = 300  # куда сбрасывается ELO, если число не указано


@router.message(Command("season"))
async def cmd_season(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").lower().split()
    wipe = any(p in ("все", "всё", "all") for p in parts)
    nums = [p for p in parts if p.lstrip("+-").isdigit()]
    if len(parts) != len(nums) + (1 if wipe else 0) or len(nums) > 1 or (nums and nums[0][0] in "+-"):
        return await m.answer("Формат: /season [ELO] [все]\nНапример: /season - ELO у всех в топе станет "
                              f"{SEASON_ELO} (Kill, Death, Win, Lose остаются).\n/season 500 - до 500.\n"
                              f"/season все - до {SEASON_ELO} и обнулить ещё Kill, Death, Win, Lose.")
    elo = int(nums[0]) if nums else SEASON_ELO
    async with lock:
        n = len(load())
    if not n:
        return await m.answer("В топе пока никого нет.")
    PENDING_SEASON[m.from_user.id] = (elo, wipe)
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"Сбросить ({n})", callback_data="ss:go"),
        InlineKeyboardButton(text="Отмена", callback_data="ss:no")]])
    await m.answer(f"Новый сезон: ELO у всех {n} игроков в топе станет {elo}"
                   + (", а Kill, Death, Win и Lose обнулятся" if wipe else " (Kill, Death, Win и Lose останутся)")
                   + ".\nПеред сбросом пришлю текущий топ, чтобы он сохранился у вас в чате. Сбросить?", reply_markup=kb)


@router.callback_query(F.data.startswith("ss:"))
async def cb_season(c: CallbackQuery):
    if c.from_user.id not in ADMIN_IDS:
        return await c.answer("Только для администратора", show_alert=True)
    pend = PENDING_SEASON.pop(c.from_user.id, None)
    try:
        await c.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    if c.data != "ss:go" or not pend:
        return await c.answer("Сброс отменён" if c.data != "ss:go" else "Запрос устарел, повторите /season", show_alert=True)
    elo, wipe = pend
    await c.answer("Сбрасываю…")
    async with lock:
        data = load()
        old = ranked(data, None)
        for row in data:
            row["elo"] = elo
            if wipe:
                for k in STAT_KEYS:
                    row[k] = 0
        save(data)
    lines = [f"Топ до сброса ({datetime.now(MSK).strftime('%d.%m.%Y')}), игроков: {len(old)}"]
    lines += [f"{r['rank']}. {r['nick']} | ELO {r['elo']} | Kill {r['kills']} Death {r['deaths']} | Win {r['wins']} Lose {r['losses']}"
              for r in old]
    await _send_long(c.message, lines)
    await c.message.answer(f"Готово: ELO у {len(old)} игроков теперь {elo}" + (", статистика обнулена." if wipe else ".")
                           + " Сообщить игрокам о новом сезоне можно через /broadcast.")


@router.message(Command("matches"))
async def cmd_matches(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    a = (command.args or "").strip().lower()
    want = next((k for k, v in STATUS_RU.items() if a and (k.startswith(a) or v.startswith(a))), None)
    async with lock:
        db = db_load()
    rows = [x for x in db["matches"].values() if not want or x["status"] == want]
    rows.sort(key=lambda x: x.get("created", 0), reverse=True)
    if not rows:
        return await m.answer("Матчей нет." if not want else f"Матчей со статусом «{STATUS_RU[want]}» нет.")
    lines = [f"Матчей: {len(rows)} (показаны последние {min(len(rows), 25)}). Подробности: /match ID"]
    for x in rows[:25]:
        res = ""
        if x["status"] == "finished" and x.get("winner") is not None:
            sc = (x.get("report") or {}).get("score")
            res = f" | победила команда {x['winner'] + 1}" + (f", счёт {sc}" if sc else "")
        lines.append(f"{x['id']} | {x['size']}x{x['size']} | {STATUS_RU.get(x['status'], x['status'])}{res} | {_dt(x.get('created'))}")
    await _send_long(m, lines)


@router.message(Command("match"))
async def cmd_match(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    mid = (command.args or "").strip()
    if not mid:
        return await m.answer("Формат: /match ID (ID виден в списке /matches)")
    async with lock:
        db = db_load()
        mt = db["matches"].get(mid)
    if not mt:
        return await m.answer(f"Матч не найден. История хранится {HISTORY_DAYS} дней.")
    head = f"Матч {mt['id']} ({mt['size']}x{mt['size']}) - {STATUS_RU.get(mt['status'], mt['status'])}\nНачался: {_dt(mt.get('created'))}"
    if mt.get("ended"):
        head += f", закончился: {_dt(mt['ended'])}"
    lines = [head]
    for i, t in enumerate(mt["teams"]):
        names = ", ".join(
            f"{db['users'][u]['nick']}{' (кап.)' if u == t['captain'] else ''} [ID {db['users'][u].get('game_id') or '-'}]"
            for u in t["members"] if u in db["users"])
        won = " - победила" if mt["status"] == "finished" and mt.get("winner") == i else ""
        lines.append(f"Команда {i + 1}{won}: {names}")
    r = mt.get("report")
    if r:
        lines.append(f"Заявка капитана: победила команда {r.get('winner', 0) + 1}, счёт {r.get('score') or '-'}")
    lines.append(f"Скриншотов: {len(mt['shots'])}" + ("" if mt["shots"] else f" (удаляются через {KEEP_DAYS} дн. после матча)"))
    if mt.get("sides"):
        lines.append("Стартовые стороны: " + ", ".join(f"команда {i + 1} - {sd}" for i, sd in enumerate(mt["sides"]))
                     + " (на финальном скрине наоборот)")
    lines.append(f"Результат: /winner {mt['id']} CT|T, отменить: /cancelmatch {mt['id']}")
    lines.append("Начислить статистику игроку: /stat ID_в_игре ELO Kill Death Win Lose")
    await _send_long(m, lines)
    await flush([(m.from_user.id, f"Скриншот: команда {sh['team'] + 1}", None, f"shot/{mt['id']}_{sh['id']}")
                 for sh in mt["shots"][:6]])


def _side_team(mt, token: str):
    """CT/T - сторона, победившая на ФИНАЛЬНОМ скриншоте (там стороны уже поменяны), или 1/2 - номер команды."""
    t = token.upper()
    if t in ("CT", "T") and mt.get("sides") and other_side(t) in mt["sides"]:
        return mt["sides"].index(other_side(t))  # победила команда, которая стартовала за противоположную сторону
    if t in ("1", "2"):
        return int(t) - 1
    return None


def _team_label(mt, i: int) -> str:
    sd = (mt.get("sides") or [None, None])[i]
    return f"команда {i + 1}" + (f" (стартовала за {sd})" if sd else "")


@router.message(Command("winner"))
async def cmd_winner(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").split()
    if len(parts) < 2:
        return await m.answer("Формат: /winner ID_матча CT или T\n"
                              "CT или T - какая сторона ПОБЕДИЛА НА ФИНАЛЬНОМ СКРИНШОТЕ. На скрине стороны уже поменяны "
                              "(после 8-го раунда), поэтому победа CT на скрине = победа команды, стартовавшей за T. "
                              "Бот сам определяет команду.\nМожно и по номеру команды: /winner ID 1 или 2.")
    outbox = []
    async with lock:
        db = db_load()
        mt = db["matches"].get(parts[0])
        if not mt:
            return await m.answer("Матч не найден. ID смотрите в /matches.")
        w = _side_team(mt, parts[1])
        if w is None:
            return await m.answer("Победителя укажите так: CT, T (сторона в матче) или 1, 2 (номер команды).")
        old = mt["status"], mt.get("winner")
        end_match(db, mt, "finished", outbox, f"Администратор определил результат: победила {_team_label(mt, w)}.", winner=w)
        db_save(db)
    note = ""
    if old[0] == "finished" and old[1] is not None and old[1] != w:
        note = f" Раньше было засчитано: {_team_label(mt, old[1])}. ELO пересчитано."
    elif old[0] == "cancelled":
        note = " Матч был отменён, теперь засчитан."
    await m.answer(f"Матч {mt['id']}: победила {_team_label(mt, w)}.{note}")
    await flush(outbox)


@router.message(Command("cancelmatch"))
async def cmd_cancelmatch(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    mid = (command.args or "").strip()
    if not mid:
        return await m.answer("Формат: /cancelmatch ID_матча (работает и для уже засчитанного матча)")
    outbox = []
    async with lock:
        db = db_load()
        mt = db["matches"].get(mid)
        if not mt:
            return await m.answer("Матч не найден. ID смотрите в /matches.")
        if mt["status"] == "cancelled":
            return await m.answer("Этот матч уже отменён.")
        was = mt["status"]
        mt.pop("winner", None)
        end_match(db, mt, "cancelled", outbox,
                  "Матч отменён администратором, результат не засчитан." if was == "finished" else "Матч отменён администратором.")
        db_save(db)
    await m.answer(f"Матч {mt['id']} отменён." + (" Результат аннулирован: победа и игра убраны из профилей игроков. "
                   "ELO, начисленное за этот матч, возвращено." if was == "finished" else ""))
    await flush(outbox)


@router.message(Command("resetid"))
async def cmd_resetid(m: Message, command: CommandObject):
    # сброс ID в игре (если игрок ошибся): /resetid ID_в_игре. Работает и когда игрок в сети, в поиске или в матче
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    key = (command.args or "").strip()
    if not key:
        return await m.answer("Формат: /resetid ID_в_игре (можно ник или @username)")
    outbox, notes = [], []
    async with lock:
        db = db_load()
        u = find_user(db, key)
        if not u:
            return await m.answer("Игрок не найден. Укажите ID в игре, ник или @username.")
        notes = drop_games(db, u, outbox, f"администратор сбросил ID у игрока {u['nick']}")
        if not (u.get("game_id") or u.get("id_status")) and not notes:
            return await m.answer(f"У {u['nick']} ID и так не указан.")
        u["game_id"], u["id_status"], u["id_note"] = "", "", ""
        db_save(db)
    outbox.append((u["tg_id"], "Администратор сбросил ваш ID в игре. Укажите правильный ID в профиле и отправьте скриншот на проверку.", None))
    await m.answer(f"ID сброшен у {u['nick']}" + (f" ({', '.join(notes)})" if notes else "") + ".")
    await flush(outbox)


@router.message(Command("referral"))
async def cmd_referral(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    arg = (command.args or "").strip().lower()
    async with lock:
        db = db_load()
        cur = bool(db["settings"].get("referral"))
        if arg in ("on", "add", "вкл", "добавить", "1"):
            db["settings"]["referral"] = True
        elif arg in ("off", "remove", "выкл", "убрать", "0"):
            db["settings"]["referral"] = False
        elif arg:
            return await m.answer("Формат: /referral on - добавить вкладку, /referral off - убрать")
        else:
            return await m.answer(f"Реферальная вкладка сейчас: {'включена' if cur else 'выключена'}.\n"
                                  "/referral on - добавить, /referral off - убрать.")
        db_save(db)
        total = sum(u.get("ref_count", 0) for u in db["users"].values())
    on = db["settings"]["referral"]
    await m.answer(("Вкладка «Пригласить друга» добавлена на сайт. " if on else "Вкладка «Пригласить друга» убрана, ссылки не работают. ")
                   + f"Всего приглашено по ссылкам: {total}.")


@router.message(Command("elo"))
async def cmd_elo(m: Message):
    lines = ["Система ELO зависит от вашего уровня и формата матча:"]
    for n, ext in ELO_STRETCH.items():
        lines.append(f"\n{n}x{n}:")
        lo = 1
        for hi, w, l in ELO_TIERS:
            lv = f"{lo}-{hi}" if hi > lo else f"{lo}"
            lines.append(f"Уровень {lv}{'+' if hi == ELO_TIERS[-1][0] else ''}: победа +{w + ext}, поражение -{l + ext}")
            lo = hi + 1
    lines.append(f"\nНовый игрок начинает с {START_ELO}. Ниже 0 ELO не опускается.")
    await m.answer("\n".join(lines))


@router.message(Command("leaver"))
async def cmd_leaver(m: Message, command: CommandObject):
    # вышел из игры до конца матча: матч отменяется, игроку запрещён поиск (по умолчанию 1 час)
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    args = (command.args or "").strip().split(None, 1)
    if not args:
        return await m.answer("Формат: /leaver ID_или_@ник [30м|1ч] - отменяет матч и запрещает вышедшему поиск (по умолчанию 1ч)")
    sec, _ = parse_duration(args[1]) if len(args) > 1 else (0, "")
    sec = sec or LEAVE_CD
    outbox = []
    async with lock:
        db = db_load()
        u = find_user(db, args[0])
        if not u:
            return await m.answer("Игрок не найден. Укажите ID в игре, ник или @username.")
        drop_games(db, u, outbox, f"игрок {u['nick']} вышел из игры до конца матча")
        u["cd_until"], u["cd_reason"] = time.time() + sec, "Выход из матча до конца игры"
        db_save(db)
    outbox.append((u["tg_id"], f"Вы вышли из матча до его конца. Поиск игр закрыт на {fmt_dur(sec)}, "
                   "таймер виден на сайте рядом с кнопкой поиска.", None))
    await m.answer(f"{u['nick']}: поиск закрыт на {fmt_dur(sec)}, активный матч отменён.")
    await flush(outbox)


@router.message(Command("unleaver"))
async def cmd_unleaver(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    key = (command.args or "").strip()
    if not key:
        return await m.answer("Формат: /unleaver ID_или_@ник - снять запрет на поиск")
    outbox = []
    async with lock:
        db = db_load()
        u = find_user(db, key)
        if not u:
            return await m.answer("Игрок не найден.")
        u["cd_until"], u["cd_reason"] = 0, ""
        db_save(db)
    outbox.append((u["tg_id"], "Запрет на поиск игр снят.", None))
    await m.answer(f"Запрет на поиск снят: {u['nick']}.")
    await flush(outbox)


@router.message(Command("queue"))
async def cmd_queue(m: Message):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    async with lock:
        db = db_load()
        rows = sorted(db["queue"].values(), key=lambda t: t["joined"])
    if not rows:
        return await m.answer("В поиске никого нет.")
    now = time.time()
    lines = []
    for t in rows[:40]:
        names = ", ".join(db["users"][u]["nick"] for u in t["members"] if u in db["users"])
        state = "на сайте" if is_fresh(t) else f"не на сайте {int(now - t.get('seen', t['joined']))} с"
        lines.append(f"{t['size']}x{t['size']}: {names} ({int(now - t['joined'])} с, {state})")
    await m.answer("\n".join(lines))


async def _ban_cmd(m: Message, command: CommandObject, ban: bool):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").split(maxsplit=1)
    if not parts:
        return await m.answer("Формат: /ban ID_в_игре или @username [срок] [причина]\nСрок: 30м, 1ч, 2ч, 1д. Без срока бан навсегда, пока не снимете /unban.\n"
                              "Например: /ban Ник 1ч вышел из матча" if ban
                              else "Формат: /unban ID_в_игре или @username")
    outbox = []
    async with lock:
        db = db_load()
        u = find_user(db, parts[0])
        if not u:
            return await m.answer("Игрок не найден.")
        if u["tg_id"] in ADMIN_IDS:
            return await m.answer("Администратора заблокировать нельзя.")
        sec, reason = parse_duration(parts[1]) if ban and len(parts) > 1 else (0, "")
        apply_ban(db, u, ban, reason.strip(), outbox, until=time.time() + sec if sec else 0)
        db_save(db)
    await m.answer(f"{'Заблокирован' + (' на ' + fmt_dur(sec) if sec else ' без срока') if ban else 'Разблокирован'}: {u['nick']}")
    await flush(outbox)


@router.message(Command("ban"))
async def cmd_ban(m: Message, command: CommandObject):
    await _ban_cmd(m, command, True)


@router.message(Command("unban"))
async def cmd_unban(m: Message, command: CommandObject):
    await _ban_cmd(m, command, False)


@router.message(Command("banlist"))
async def cmd_banlist(m: Message):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    async with lock:
        rows = [u for u in db_load()["users"].values() if u.get("banned")]
    await m.answer("\n".join(f"{u['nick']} (ID {u.get('game_id') or '-'}){': ' + u['ban_reason'] if u.get('ban_reason') else ''}{ban_left(u)}"
                             for u in rows[:50]) or "Заблокированных нет.")


PENDING_BC: dict = {}


@router.message(Command("broadcast"))
async def cmd_broadcast(m: Message, command: CommandObject):
    # рассылка всем зарегистрированным: сначала предпросмотр, отправка только после нажатия кнопки
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    text = (command.args or "").strip()
    if not text:
        return await m.answer("Формат: /broadcast Текст сообщения\nПример: /broadcast Бот снова работает, можно искать игру!")
    if len(text) > 3500:
        return await m.answer("Слишком длинный текст, сократите до 3500 символов.")
    async with lock:
        n = sum(1 for u in db_load()["users"].values() if not u.get("banned"))
    PENDING_BC[m.from_user.id] = text
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"Отправить ({n})", callback_data="bc:go"),
        InlineKeyboardButton(text="Отмена", callback_data="bc:no")]])
    await m.answer("Предпросмотр рассылки:\n\n" + text, reply_markup=kb)


@router.callback_query(F.data.startswith("bc:"))
async def cb_broadcast(c: CallbackQuery):
    if c.from_user.id not in ADMIN_IDS:
        return await c.answer("Только для администратора", show_alert=True)
    text = PENDING_BC.pop(c.from_user.id, None)
    try:
        await c.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    if c.data != "bc:go" or not text:
        return await c.answer("Рассылка отменена" if c.data != "bc:go" else "Текст устарел, повторите /broadcast", show_alert=True)
    await c.answer("Отправляю…")
    async with lock:
        ids = [u["tg_id"] for u in db_load()["users"].values() if not u.get("banned")]
    ok = fail = 0
    for tid in ids:
        try:
            await bot.send_message(tid, text)
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.05)  # укладываемся в лимиты Telegram
    await c.message.answer(f"Рассылка завершена: доставлено {ok}, не доставлено {fail} "
                           "(человек не запускал бота или заблокировал его).")


# ---------- API сайта ----------
def api(auth: bool = True):
    """Обёртка: блокировка, загрузка базы, авторизация, сохранение, уведомления в бота."""
    def deco(fn):
        async def handler(request: web.Request):
            body = {}
            if (request.content_length or 0) > 64 * 1024:  # JSON-запросы маленькие; большие тела только у загрузки картинок
                return web.json_response({"error": "Слишком большой запрос"}, status=413, headers=NOSTORE)
            if request.method == "POST":
                try:
                    body = await request.json()
                except Exception:
                    body = {}
                if not isinstance(body, dict):
                    body = {}
            outbox = []
            try:
                async with lock:
                    db = db_load()
                    changed = cleanup(db)
                    user = session_user(db, request)
                    if user is not None:
                        LAST_SEEN[uid_of(user)] = time.time()
                    if auth and user is None:
                        raise ApiError(401, "Нужен вход через Telegram")
                    ctx = {"dirty": request.method == "POST" or bool(changed)}
                    res = fn(request, db, user, body, outbox, ctx)
                    if ctx["dirty"]:
                        if user is not None:
                            user["seen_at"] = int(time.time())
                        db_save(db)
            except ApiError as e:
                return web.json_response({"error": e.msg}, status=e.status, headers=NOSTORE)
            await flush(outbox)
            return web.json_response(res, headers=NOSTORE)
        return handler
    return deco


@api(auth=False)
def api_auth_start(request, db, user, body, outbox, ctx):
    if not BOT_USERNAME:
        raise ApiError(503, "Бот ещё запускается, попробуйте через пару секунд")
    if len(db["codes"]) > 500:
        raise ApiError(429, "Слишком много попыток входа, подождите пару минут")
    code = secrets.token_urlsafe(12)
    db["codes"][code] = {"exp": time.time() + CODE_TTL, "uid": None}
    return {"code": code, "link": f"https://t.me/{BOT_USERNAME}?start=auth_{code}"}


@api(auth=False)
def api_auth_check(request, db, user, body, outbox, ctx):
    code = request.query.get("code", "")
    entry = db["codes"].get(code)
    if not entry:
        return {"status": "expired"}
    if not entry.get("uid"):
        return {"status": "pending"}
    token = new_session(db, entry["uid"])
    del db["codes"][code]
    ctx["dirty"] = True
    return {"status": "ok", "token": token}


@api(auth=False)
def api_auth_webapp(request, db, user, body, outbox, ctx):
    """Автовход, когда сайт открыт как Telegram Mini App (проверка подписи initData)."""
    pairs = dict(parse_qsl(str(body.get("initData") or ""), keep_blank_values=True))
    got = pairs.pop("hash", "")
    check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
    if not got or not hmac.compare_digest(calc, got):
        raise ApiError(401, "Неверная подпись Telegram")
    try:
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            raise ApiError(401, "Данные Telegram устарели")
        tg = json.loads(pairs["user"])
        u = ensure_user(db, int(tg["id"]), tg.get("username"), tg.get("first_name"))
    except (KeyError, ValueError, TypeError):
        raise ApiError(401, "Неверные данные Telegram")
    return {"token": new_session(db, uid_of(u))}


@api()
def api_logout(request, db, user, body, outbox, ctx):
    db["sessions"].pop(request.headers["Authorization"][7:], None)
    return {"ok": True}


@api(auth=False)
def api_me(request, db, user, body, outbox, ctx):
    cfg = {"bot": BOT_USERNAME, "referral": bool(db["settings"].get("referral")), "ref_elo": REF_ELO, "ref_limit": REF_WEEK_LIMIT}
    if user is None:
        return {"user": None, "cfg": cfg}
    uid = uid_of(user)
    return {"user": {**pub(user), "tg": user.get("tg_username", ""), "admin": user["tg_id"] in ADMIN_IDS,
                     "banned": bool(user.get("banned")), "id_status": id_state(user),
                     "ban_left": max(0, int(user.get("ban_until", 0) - time.time())) if user.get("banned") else 0,
                     "cd_left": cd_left(user), "cd_reason": user.get("cd_reason", "") if cd_left(user) else "",
                     "id_note": user.get("id_note", ""), "ref_count": user.get("ref_count", 0),
                     "ref_wait": sum(1 for x in db["users"].values()
                                     if x.get("ref_by") == uid and not x.get("ref_paid") and not x.get("ref_skipped")),
                     "ref_left": max(0, REF_WEEK_LIMIT - len(ref_recent(db, uid))),
                     "ref_reset": (int(ref_recent(db, uid)[0] + REF_WEEK - time.time())
                                   if len(ref_recent(db, uid)) >= REF_WEEK_LIMIT else 0),
                     "ref_link": f"https://t.me/{BOT_USERNAME}?start=ref_{uid}" if BOT_USERNAME else ""}, "cfg": cfg,
            "badges": {"friends": sum(1 for r in db["freqs"].values() if r["to"] == uid),
                       "party": sum(1 for i in db["pinvites"].values() if i["to"] == uid)}}


@api()
def api_profile(request, db, user, body, outbox, ctx):
    user["nick"] = clean_str(body.get("nick"), 32, "Ник", 2)
    user["about"] = clean_str(body.get("about"), 300, "О себе")
    # ID в игре меняется только через проверку по скриншоту (/api/shots/idcheck)
    return {"ok": True}


# --- друзья ---
@api()
def api_users(request, db, user, body, outbox, ctx):
    q = request.query.get("q", "").strip().lower().lstrip("#")
    if len(q) < 2:
        return []
    me, rows = uid_of(user), []
    for uid, u in db["users"].items():
        if uid == me:
            continue
        if q in u["nick"].lower() or q == (u.get("game_id") or "").lower() or q in (u.get("tg_username") or "").lower():
            rel, rid = relation(db, me, uid)
            rows.append({**pub(u), **presence(u), "relation": rel, "req_id": rid})
    return rows[:15]


@api()
def api_user(request, db, user, body, outbox, ctx):
    u = user_by_pid(db, request.match_info["pid"])
    if not u:
        raise ApiError(404, "Игрок не найден")
    rel, rid = relation(db, uid_of(user), uid_of(u))
    d = {**pub(u), **presence(u), "relation": rel, "req_id": rid,
         "friends_count": len(db["friends"].get(uid_of(u), []))}
    if rel in ("friend", "self") and u.get("tg_username"):
        d["tg"] = u["tg_username"]  # Telegram виден только друзьям
    st = top_stats(u["pid"])
    if st:
        d["stats"] = st
    d["record"] = match_record(db, uid_of(u))
    d["history"] = match_history(db, uid_of(u))
    if user["tg_id"] in ADMIN_IDS:
        d["banned"] = bool(u.get("banned"))
        d["ban_reason"] = u.get("ban_reason", "")
    return d


@api()
def api_friends(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    mp = party_of(db, me)
    invited = {i["to"] for i in pending_invites(db, mp["id"])} if mp else set()
    friends = []
    for f in db["friends"].get(me, []):
        fu = db["users"].get(f)
        if fu:
            friends.append({**pub(fu), **presence(fu), "in_party": real_party_of(db, f) is not None, "invited": f in invited})
    friends.sort(key=lambda x: (not x["online"], x["nick"].lower()))
    inc = [{"id": r["id"], "user": pub(db["users"][r["from"]])}
           for r in db["freqs"].values() if r["to"] == me and r["from"] in db["users"]]
    out = [{"id": r["id"], "user": pub(db["users"][r["to"]])}
           for r in db["freqs"].values() if r["from"] == me and r["to"] in db["users"]]
    return {"friends": friends, "incoming": inc, "outgoing": out}


@api()
def api_friend_add(request, db, user, body, outbox, ctx):
    target = user_by_pid(db, str(body.get("pid") or ""))
    me = uid_of(user)
    if not target or uid_of(target) == me:
        raise ApiError(400, "Нельзя добавить этого игрока")
    tid = uid_of(target)
    rel, rid = relation(db, me, tid)
    if rel == "friend":
        raise ApiError(400, "Вы уже друзья")
    if rel == "outgoing":
        raise ApiError(400, "Заявка уже отправлена")
    if rel == "incoming":  # встречная заявка - сразу дружим
        return {"message": resolve_freq(db, rid, user, True, outbox)}
    if sum(1 for r in db["freqs"].values() if r["from"] == me) >= 20:
        raise ApiError(400, "Слишком много неотвеченных заявок")
    rid = secrets.token_hex(4)
    db["freqs"][rid] = {"id": rid, "from": me, "to": tid, "created": int(time.time())}
    outbox.append((target["tg_id"], f"Заявка в друзья от {user['nick']} ({tg_tag(user)})", accept_kb("fr", rid)))
    return {"message": "Заявка отправлена"}


@api()
def api_freq_resolve(request, db, user, body, outbox, ctx):
    rid, act = request.match_info["id"], request.match_info["act"]
    if act == "cancel":
        r = db["freqs"].get(rid)
        if not r or r["from"] != uid_of(user):
            raise ApiError(404, "Заявка не найдена")
        del db["freqs"][rid]
        return {"message": "Заявка отозвана"}
    return {"message": resolve_freq(db, rid, user, act == "accept", outbox)}


@api()
def api_friend_remove(request, db, user, body, outbox, ctx):
    target = user_by_pid(db, str(body.get("pid") or ""))
    if not target:
        raise ApiError(404, "Игрок не найден")
    a, b = uid_of(user), uid_of(target)
    for x, y in ((a, b), (b, a)):
        if y in db["friends"].get(x, []):
            db["friends"][x].remove(y)
    return {"ok": True}


# --- пати ---
def party_view(db, p, me):
    return {"id": p["id"], "size": p["size"], "leader": p["owner"] == me,
            "in_queue": party_in_queue(db, p),
            "members": [{**pub(db["users"][m]), "leader": m == p["owner"]}
                        for m in p["members"] if m in db["users"]],
            "invited": [{"id": i["id"], "user": pub(db["users"][i["to"]])}
                        for i in pending_invites(db, p["id"]) if i["to"] in db["users"]]}


@api()
def api_party(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    p = party_of(db, me)
    invites = []
    for i in db["pinvites"].values():
        ip = db["parties"].get(i["party"])
        if i["to"] == me and ip and ip["owner"] in db["users"]:
            invites.append({"id": i["id"], "size": ip["size"], "count": len(ip["members"]),
                            "from": pub(db["users"][ip["owner"]])})
    t = queue_of(db, me)
    if t:  # «я на сайте»: обновляем метку и сразу пробуем собрать матч (вдруг вернулся игрок, который выходил)
        t["seen"] = time.time()
        ctx["dirty"] = True
        try_match(db, t["size"], outbox)
        t = queue_of(db, me)
    queue = None
    if t:
        queue = {"size": t["size"], "need": 2 * t["size"], "elapsed": int(time.time() - t["joined"]),
                 "waiting": sum(len(x["members"]) for x in db["queue"].values() if x["size"] == t["size"] and is_fresh(x)),
                 "can_cancel": t["owner"] == me}
    m = match_of(db, me)
    last = None
    for mm in sorted(db["matches"].values(), key=lambda x: x.get("ended", 0), reverse=True):
        ti = team_idx(mm, me)
        if mm["status"] != "active" and ti is not None and mm.get("ended", 0) > time.time() - 3600:
            res = None
            if mm["status"] == "finished":
                res = "win" if mm.get("winner") == ti else "lose"
            last = {"status": mm["status"], "result": res, "review": bool(mm.get("review")),
                    "elo": (mm.get("elo_awards") or {}).get(me)}
            break
    modes = {n: sum(len(x["members"]) for x in db["queue"].values() if x["size"] == n and is_fresh(x)) for n in SIZES}
    return {"party": party_view(db, p, me) if p else None, "invites": invites, "modes": modes,
            "queue": queue, "match": match_view(db, m, me) if m else None, "last": last}


def nudge_invites(db, outbox) -> bool:
    changed = False
    for i in db["pinvites"].values():
        if i.get("tg", True) or time.time() - i.get("created", 0) < 45:
            continue
        t, p = db["users"].get(i["to"]), db["parties"].get(i["party"])
        if not t or not p or is_online(t):
            continue
        owner = db["users"].get(p["owner"])
        if owner:
            outbox.append((t["tg_id"], pinvite_msg(owner, p), accept_kb("pi", i["id"])))
        i["tg"], changed = True, True
    return changed


async def invite_nudger():
    while True:
        await asyncio.sleep(30)
        outbox = []
        try:
            async with lock:
                db = db_load()
                if nudge_invites(db, outbox):
                    db_save(db)
            await flush(outbox)
        except asyncio.CancelledError:
            raise
        except Exception:
            logging.exception("invite_nudger")


def _size(v):
    try:
        n = int(v)
    except (TypeError, ValueError):
        raise ApiError(400, "Режим: 3, 4 или 5")
    if n not in SIZES:
        raise ApiError(400, "Режим: 3, 4 или 5")
    return n


@api()
def api_party_invite(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    target = user_by_pid(db, str(body.get("pid") or ""))
    if not target or not are_friends(db, me, uid_of(target)):
        raise ApiError(400, "Приглашать можно только друзей")
    tid = uid_of(target)
    p = party_of(db, me)
    if party_in_queue(db, p) or (not p and queue_of(db, me)):
        raise ApiError(400, "Сначала отмените поиск игры")
    if p and p["owner"] != me:
        raise ApiError(403, "Приглашает только лидер пати")
    if real_party_of(db, tid):
        raise ApiError(400, "Этот игрок уже в пати")
    if p and any(i["to"] == tid for i in pending_invites(db, p["id"])):
        raise ApiError(400, "Приглашение уже отправлено")
    size = p["size"] if p else _size(body.get("size", 5))
    taken = len(p["members"]) + len(pending_invites(db, p["id"])) if p else 1
    if taken >= size:
        raise ApiError(400, "Все места заняты или ждут ответа")
    if not p:
        pid = secrets.token_hex(4)
        p = db["parties"][pid] = {"id": pid, "owner": me, "size": size, "members": [me]}
    iid = secrets.token_hex(4)
    online = is_online(target)  # в сети: увидит на сайте; не в сети: сообщение в Telegram
    db["pinvites"][iid] = {"id": iid, "party": p["id"], "to": tid, "created": time.time(), "tg": not online}
    if not online:
        outbox.append((target["tg_id"], pinvite_msg(user, p), accept_kb("pi", iid)))
    return {"message": "Приглашение отправлено на сайт" if online else "Приглашение отправлено в Telegram"}


@api()
def api_party_size(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    p = party_of(db, me)
    if not p or p["owner"] != me:
        raise ApiError(403, "Режим меняет лидер пати")
    if party_in_queue(db, p):
        raise ApiError(400, "Сначала отмените поиск игры")
    n = _size(body.get("size"))
    if n < len(p["members"]) + len(pending_invites(db, p["id"])):
        raise ApiError(400, "Сначала исключите игроков или отмените приглашения")
    p["size"] = n
    return {"ok": True}


@api()
def api_party_leave(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    p = party_of(db, me)
    if not p:
        raise ApiError(400, "Вы не в пати")
    if party_in_queue(db, p):
        raise ApiError(400, "Сначала отмените поиск игры")
    p["members"].remove(me)
    if not p["members"]:
        drop_party(db, p)
    else:
        if p["owner"] == me:
            p["owner"] = p["members"][0]
        for m in p["members"]:
            outbox.append((db["users"][m]["tg_id"], f"{user['nick']} вышел из пати.", None))
    return {"ok": True}


@api()
def api_party_kick(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    p = party_of(db, me)
    target = user_by_pid(db, str(body.get("pid") or ""))
    if not p or p["owner"] != me or not target or uid_of(target) not in p["members"] or uid_of(target) == me:
        raise ApiError(400, "Нельзя исключить этого игрока")
    if party_in_queue(db, p):
        raise ApiError(400, "Сначала отмените поиск игры")
    p["members"].remove(uid_of(target))
    outbox.append((target["tg_id"], "Вас исключили из пати.", None))
    return {"ok": True}


@api()
def api_pinvite_resolve(request, db, user, body, outbox, ctx):
    iid, act = request.match_info["id"], request.match_info["act"]
    if act == "cancel":
        i = db["pinvites"].get(iid)
        p = db["parties"].get(i["party"]) if i else None
        if not p or p["owner"] != uid_of(user):
            raise ApiError(404, "Приглашение не найдено")
        del db["pinvites"][iid]
        return {"message": "Приглашение отменено"}
    return {"message": resolve_pinvite(db, iid, user, act == "accept", outbox)}


# --- поиск игры и матч ---
@api()
def api_queue_start(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    if match_of(db, me):
        raise ApiError(400, "Вы уже в матче")
    if queue_of(db, me):
        raise ApiError(400, "Поиск уже идёт")
    p = party_of(db, me)
    if p:
        if p["owner"] != me:
            raise ApiError(403, "Поиск запускает лидер пати")
        members, size, pid = list(p["members"]), p["size"], p["id"]
        for k in [k for k, v in db["pinvites"].items() if v["party"] == pid]:
            del db["pinvites"][k]  # неотвеченные приглашения снимаем
    else:
        members, size, pid = [me], _size(body.get("size", 5)), None
    for m in members:
        if match_of(db, m) or queue_of(db, m):
            raise ApiError(400, "Кто-то из пати уже в матче или поиске")
    for m in members:
        bu = db["users"].get(m, {})
        if bu.get("banned"):
            raise ApiError(403, ("Вы заблокированы администратором" if m == me else f"Игрок {bu.get('nick')} заблокирован")
                           + (f": {bu['ban_reason']}" if bu.get("ban_reason") else "") + ban_left(bu))
    for m in members:
        cu = db["users"].get(m, {})
        if cd_left(cu):
            who = "Вам" if m == me else f"Игроку {cu.get('nick')}"
            raise ApiError(403, f"{who} нельзя искать игру ещё {fmt_dur(((cd_left(cu) + 59) // 60) * 60)}: выход из матча до конца игры")
    for m in members:
        mu = db["users"].get(m, {})
        if id_state(mu) != "ok":
            who = "Вам" if m == me else f"Игроку {mu.get('nick')}"
            raise ApiError(400, {"pending": f"{who}: ID на проверке у администратора, подождите подтверждения",
                                 }.get(id_state(mu), f"{who} нужно указать ID в профиле и отправить скриншот на проверку"))
    tid = secrets.token_hex(4)
    db["queue"][tid] = {"id": tid, "owner": me, "party": pid, "members": members,
                        "size": size, "joined": time.time(), "seen": time.time()}
    try_match(db, size, outbox)
    return {"message": "Матч найден!" if match_of(db, me) else "Ищем игру…"}


@api()
def api_queue_cancel(request, db, user, body, outbox, ctx):
    me = uid_of(user)
    t = queue_of(db, me)
    if not t:
        raise ApiError(400, "Вы не в поиске")
    if t["owner"] != me:
        raise ApiError(403, "Поиск отменяет лидер пати")
    del db["queue"][t["id"]]
    for m in t["members"]:
        if m != me and m in db["users"]:
            outbox.append((db["users"][m]["tg_id"], "Лидер отменил поиск игры.", None))
    return {"message": "Поиск отменён"}


def _my_match(db, user):
    me = uid_of(user)
    m = match_of(db, me)
    if not m:
        raise ApiError(404, "Активного матча нет")
    return me, m, team_idx(m, me)


@api()
def api_match_ban(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    v = m.get("veto")
    if not v or v["phase"] != "ban":
        raise ApiError(400, "Сейчас бан карт недоступен")
    if m["teams"][ti]["captain"] != me:
        raise ApiError(403, "Карты банят капитаны команд")
    if v["order"][len(v["bans"])] != ti:
        raise ApiError(400, "Сейчас ход капитана другой команды")
    mp = body.get("map")
    if mp not in MAP_NAME or any(b["map"] == mp for b in v["bans"]):
        raise ApiError(400, "Эта карта недоступна")
    veto_ban(v, mp)
    return {"message": f"Карта {MAP_NAME[mp]} забанена"}


@api()
def api_match_vote(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    v = m.get("veto")
    if not v or v["phase"] != "vote":
        raise ApiError(400, "Голосование за карту сейчас не идёт")
    mp = body.get("map")
    if mp not in v["left"]:
        raise ApiError(400, "Выберите одну из двух оставшихся карт")
    v["votes"][me] = mp
    veto_pick(m)
    return {"message": "Голос принят"}


def chat_msg(db, m, x):
    u = db["users"].get(x["uid"], {})
    return {"id": x["id"], "pid": u.get("pid", ""), "nick": u.get("nick", "?"), "av": u.get("avatar", 0),
            "text": x["text"], "ts": int(x["ts"]), "team": team_idx(m, x["uid"])}


@api()
def api_match_chat_get(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    try:
        since = int(request.query.get("since", 0))
    except (TypeError, ValueError):
        since = 0
    return {"msgs": [chat_msg(db, m, x) for x in m.get("chat", []) if x["id"] > since]}


@api()
def api_match_chat_send(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    if user.get("banned"):
        raise ApiError(403, "Вы заблокированы и не можете писать в чат")
    text = " ".join(str(body.get("text", "")).split())[:300]
    if not text:
        raise ApiError(400, "Пустое сообщение")
    chat, now = m.setdefault("chat", []), time.time()
    if any(x["uid"] == me and now - x["ts"] < 1 for x in chat[-6:]):
        raise ApiError(429, "Не так быстро")
    m["chat_seq"] = m.get("chat_seq", 0) + 1
    chat.append({"id": m["chat_seq"], "uid": me, "text": text, "ts": now})
    del chat[:-CHAT_MAX]
    return {"ok": True}


def fmt_dur(sec: int) -> str:
    if sec % 86400 == 0:
        return f"{sec // 86400} д"
    if sec % 3600 == 0:
        return f"{sec // 3600} ч"
    return f"{max(1, sec // 60)} мин"


def ban_left(u) -> str:
    left = int(u.get("ban_until", 0) - time.time())
    return f" (осталось {fmt_dur(((left + 59) // 60) * 60)})" if u.get("banned") and left > 0 else ""


_DUR = re.compile(r"(\d{1,3})\s*(мин|м|min|m|часа|час|ч|h|дней|дня|день|дн|д|d)(?![a-zа-я])\s*", re.I)


def parse_duration(text: str):
    """'1ч вышел из матча' -> (3600, 'вышел из матча'); без срока -> (0, text), то есть бан без срока."""
    mt = _DUR.match(text)
    if not mt:
        return 0, text
    unit = mt.group(2).lower()
    mult = 60 if unit in ("мин", "м", "min", "m") else 3600 if unit in ("часа", "час", "ч", "h") else 86400
    sec = min(int(mt.group(1)) * mult, 30 * 86400)
    return (sec, text[mt.end():]) if sec > 0 else (0, text)


def apply_ban(db, u, banned: bool, reason: str, outbox, until: float = 0) -> None:
    u["banned"], u["ban_reason"], u["ban_until"] = banned, (reason[:200] if banned else ""), (until if banned else 0)
    if banned:
        uid = uid_of(u)
        t = queue_of(db, uid)
        if t:
            del db["queue"][t["id"]]
        mt = match_of(db, uid)
        if mt:  # игрок в матче: матч отменяется, все участники получат сообщение
            end_match(db, mt, "cancelled", outbox, f"Матч отменён: игрок {u['nick']} заблокирован администратором.")
        pt = party_of(db, uid)
        if pt:
            pt["members"].remove(uid)
            if not pt["members"]:
                drop_party(db, pt)
            elif pt["owner"] == uid:
                pt["owner"] = pt["members"][0]
        for k in [k for k, v in db["pinvites"].items() if v["to"] == uid]:
            del db["pinvites"][k]
    dur = int(round((until - time.time()) / 60)) * 60 if banned and until else 0
    outbox.append((u["tg_id"], ("Вы заблокированы администратором" + (f" на {fmt_dur(dur)}" if dur > 0 else "")
                                + (f": {reason}" if reason else "") + ".")
                   if banned else "Администратор снял блокировку.", None))


@api()
def api_admin_ban(request, db, user, body, outbox, ctx):
    if user["tg_id"] not in ADMIN_IDS:
        raise ApiError(403, "Только для администратора")
    u = user_by_pid(db, str(body.get("pid", "")))
    if not u or uid_of(u) == uid_of(user):
        raise ApiError(400, "Игрок не найден")
    apply_ban(db, u, bool(body.get("ban")), clean_str(body.get("reason"), 200, "Причина"), outbox)
    return {"message": "Игрок заблокирован" if body.get("ban") else "Блокировка снята"}


@api()
def api_match_cancel(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    if user["tg_id"] in ADMIN_IDS:
        end_match(db, m, "cancelled", outbox, "Матч отменён администратором.")
        return {"message": "Матч отменён"}
    if m["teams"][ti]["captain"] != me:
        raise ApiError(403, "Матч отменяют капитаны команд")
    if ti not in m["cancel_votes"]:
        m["cancel_votes"].append(ti)
    if len(m["cancel_votes"]) >= 2:
        end_match(db, m, "cancelled", outbox, "Матч отменён: капитаны обеих команд согласились.")
        return {"message": "Матч отменён"}
    other = db["users"].get(m["teams"][1 - ti]["captain"])
    if other:
        outbox.append((other["tg_id"], "Капитан соперников предлагает отменить матч. "
                       "Откройте комнату и нажмите «Отменить матч», если согласны.", room_kb()))
    return {"message": "Отмена запрошена, ждём капитана соперников"}


@api()
def api_match_report(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    if m["teams"][ti]["captain"] != me:
        raise ApiError(403, "Результат отправляет капитан команды")
    if not any(x["team"] == ti for x in m["shots"]):
        raise ApiError(400, "Сначала прикрепите скриншот результата")
    w = body.get("winner")
    if w not in ("me", "enemy"):
        raise ApiError(400, "Укажите, кто победил")
    score = clean_str(body.get("score"), 10, "Счёт")
    win = ti if w == "me" else 1 - ti
    m["report"] = {"team": ti, "winner": win, "score": score, "ts": int(time.time())}
    m["review"] = True  # на проверке у админов; капитан соперников подтверждать ничего не должен
    end_match(db, m, "disputed", outbox, f"Капитан команды {ti + 1} отправил результат: победила команда {win + 1}"
              + (f", счёт {score}" if score else "") + ". Администратор проверит скриншот и засчитает матч.")
    notify_admins_dispute(db, m, outbox)
    return {"message": "Результат отправлен администратору на проверку"}


@api()
def api_match_confirm(request, db, user, body, outbox, ctx):
    me, m, ti = _my_match(db, user)
    if m["teams"][ti]["captain"] != me:
        raise ApiError(403, "Подтверждает капитан команды")
    rep = m.get("report")
    if not rep or rep["team"] == ti:
        raise ApiError(400, "Нет результата от соперников для подтверждения")
    if body.get("accept"):
        end_match(db, m, "finished", outbox,
                  f"Матч завершён: победила команда {rep['winner'] + 1}"
                  + (f", счёт {rep['score']}" if rep["score"] else "") + ".", winner=rep["winner"])
        return {"message": "Результат подтверждён"}
    end_match(db, m, "disputed", outbox, "Результат оспорен. Скриншоты передали администратору, он примет решение.")
    notify_admins_dispute(db, m, outbox)
    return {"message": "Результат оспорен, решит администратор"}


async def api_shot_upload(request):
    data = await request.read()
    if not data or len(data) > MAX_SHOT:
        return web.json_response({"error": "Файл пустой или больше 5 МБ"}, status=400, headers=NOSTORE)
    ext = ("png" if data[:8] == b"\x89PNG\r\n\x1a\n" else "jpg" if data[:3] == b"\xff\xd8\xff"
           else "webp" if data[:4] == b"RIFF" and data[8:12] == b"WEBP" else None)
    if not ext:
        return web.json_response({"error": "Нужна картинка PNG, JPG или WEBP"}, status=400, headers=NOSTORE)
    async with lock:
        db = db_load()
        user = session_user(db, request)
        if user is None:
            return web.json_response({"error": "Нужен вход через Telegram"}, status=401, headers=NOSTORE)
        me = uid_of(user)
        m = match_of(db, me)
        if not m or m["id"] != request.match_info["mid"]:
            return web.json_response({"error": "Активного матча нет"}, status=404, headers=NOSTORE)
        ti = team_idx(m, me)
        if m["teams"][ti]["captain"] != me:
            return web.json_response({"error": "Скриншоты прикрепляет капитан"}, status=403, headers=NOSTORE)
        if sum(1 for x in m["shots"] if x["team"] == ti) >= 5:
            return web.json_response({"error": "Можно прикрепить не больше 5 скриншотов"}, status=400, headers=NOSTORE)
        sid = secrets.token_hex(6)
        await blob_put(f"shot/{m['id']}_{sid}", data)
        m["shots"].append({"id": sid, "team": ti, "ext": ext, "ts": int(time.time())})
        db_save(db)
    return web.json_response({"ok": True}, headers=NOSTORE)


async def api_shot_get(request):
    async with lock:
        db = db_load()
        user = session_user(db, request)
        m = db["matches"].get(request.match_info["mid"])
    if user is None or not m:
        return web.Response(status=404)
    if team_idx(m, uid_of(user)) is None and user["tg_id"] not in ADMIN_IDS:
        return web.Response(status=403)
    sh = next((x for x in m["shots"] if x["id"] == request.match_info["sid"]), None)
    data = await blob_get(f"shot/{m['id']}_{sh['id']}") if sh else None
    if not data:
        return web.Response(status=404)
    return web.Response(body=data, content_type=CTYPES.get(sh["ext"], "application/octet-stream"),
                        headers={**NOSTORE, "X-Content-Type-Options": "nosniff"})


def sniff_ext(b: bytes):
    if b[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if b[:3] == b"\xff\xd8\xff":
        return "jpg"
    if b[:4] == b"RIFF" and b[8:12] == b"WEBP":
        return "webp"
    return None


def _drop_avatar_files(pid: str) -> None:
    blob_del(f"avatar/{pid}")


async def api_idcheck_upload(request):
    # игрок указывает ID и прикладывает скриншот игрового профиля; админы сверяют их вручную
    data = await request.read()
    ext = sniff_ext(data) if data and len(data) <= MAX_SHOT else None
    if not ext:
        return web.json_response({"error": "Нужна картинка PNG, JPG или WEBP до 5 МБ"}, status=400, headers=NOSTORE)
    gid = request.query.get("id", "").strip()
    if not re.fullmatch(r"[0-9]{3,20}", gid):
        return web.json_response({"error": "ID в игре: только цифры, от 3 до 20"}, status=400, headers=NOSTORE)
    outbox = []
    async with lock:
        db = db_load()
        user = session_user(db, request)
        if user is None:
            return web.json_response({"error": "Нужен вход через Telegram"}, status=401, headers=NOSTORE)
        st, cur, me = id_state(user), user.get("game_id", ""), uid_of(user)
        err = ("ID уже подтверждён" if st == "ok" else "ID уже на проверке, дождитесь ответа администратора" if st == "pending"
               else f"ID нельзя изменить: у вас указан {cur}" if cur and gid != cur
               else "Этот ID уже занят другим игроком" if any(k != me and (v.get("game_id") or "") == gid
                                                              for k, v in db["users"].items()) else "")
        if err:
            return web.json_response({"error": err}, status=400, headers=NOSTORE)
        await blob_put(f"shot/idv_{user['pid']}", data)
        user["game_id"], user["id_status"], user["id_note"], user["id_ext"] = gid, "pending", "", ext
        db_save(db)
        outbox.extend(idv_notify(user))
    await flush(outbox)
    return web.json_response({"ok": True}, headers=NOSTORE)


def idv_notify(u) -> list:
    kb = [("✅ ID совпадает", f"idv:ok:{u['pid']}"), ("❌ Не совпадает", f"idv:no:{u['pid']}")]
    tg = f" (@{u['tg_username']})" if u.get("tg_username") else ""
    text = (f"Проверка ID. Игрок {u['nick']}{tg} указал ID: {u['game_id']}\n"
            "Сверьте ID на скриншоте с указанным и нажмите кнопку.")
    return [(a, text, kb, f"shot/idv_{u['pid']}") for a in ADMIN_IDS]


@router.callback_query(F.data.startswith("idv:"))
async def cb_idv(c: CallbackQuery):
    if c.from_user.id not in ADMIN_IDS:
        return await c.answer("Только для администратора", show_alert=True)
    _, act, pid = c.data.split(":", 2)
    outbox, done = [], ""
    async with lock:
        db = db_load()
        u = user_by_pid(db, pid)
        if not u or id_state(u) != "pending":
            await c.answer("Эта заявка уже обработана", show_alert=True)
            done = "обработано"
        elif act == "ok":
            u["id_status"], u["id_note"] = "ok", ""
            outbox.append((u["tg_id"], "ID в игре подтверждён ✅ Теперь можно искать игру.", None))
            pay_ref(db, u, outbox)
            done = f"✅ Подтверждён: {u['nick']} (ID {u['game_id']})"
            db_save(db)
        else:
            outbox.append((u["tg_id"], "Администратор отклонил ID: он не совпал со скриншотом. "
                           "Укажите ID заново в профиле и приложите скриншот игрового профиля, где виден ID.", None))
            drop_games(db, u, outbox, f"ID игрока {u['nick']} отклонён администратором")
            u["game_id"], u["id_status"], u["id_note"] = "", "rejected", "ID не совпал со скриншотом"
            done = f"❌ Отклонён: {u['nick']}"
            db_save(db)
    if done and done != "обработано":
        try:
            await c.message.edit_caption(caption=(c.message.caption or "") + "\n\n" + done, reply_markup=None)
        except Exception:
            pass
        await c.answer("Готово")
    await flush(outbox)


@router.message(Command("ids"))
async def cmd_ids(m: Message):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    async with lock:
        pend = [u for u in db_load()["users"].values() if id_state(u) == "pending"]
    if not pend:
        return await m.answer("Заявок на проверку ID нет.")
    await m.answer(f"На проверке: {len(pend)}. Присылаю скриншоты с кнопками.")
    out = []
    for u in pend[:10]:
        out.extend((m.from_user.id, t, k, ph) for _, t, k, ph in idv_notify(u))
    await flush(out)


@router.message(Command("verify"))
async def cmd_verify(m: Message, command: CommandObject):
    # подтвердить ID без скриншота (например, тем, кто указал ID до появления проверки)
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    key = (command.args or "").strip()
    if not key:
        return await m.answer("Формат: /verify ID_в_игре или @ник")
    outbox = []
    async with lock:
        db = db_load()
        u = find_user(db, key)
        if not u or not u.get("game_id"):
            return await m.answer("Игрок с указанным ID не найден.")
        u["id_status"], u["id_note"] = "ok", ""
        outbox.append((u["tg_id"], "ID в игре подтверждён ✅ Теперь можно искать игру.", None))
        pay_ref(db, u, outbox)
        db_save(db)
    await m.answer(f"ID подтверждён: {u['nick']} ({u['game_id']}).")
    await flush(outbox)


async def api_avatar_upload(request):
    data = await request.read()
    ext = sniff_ext(data) if data and len(data) <= MAX_AVATAR else None
    if not ext:
        return web.json_response({"error": "Нужна картинка PNG, JPG или WEBP до 2 МБ"}, status=400, headers=NOSTORE)
    async with lock:
        db = db_load()
        user = session_user(db, request)
        if user is None:
            return web.json_response({"error": "Нужен вход через Telegram"}, status=401, headers=NOSTORE)
        await blob_put(f"avatar/{user['pid']}", data)
        user["avatar"], user["avatar_ext"] = int(time.time()), ext
        db_save(db)
    return web.json_response({"ok": True, "av": user["avatar"]}, headers=NOSTORE)


async def api_avatar_get(request):
    pid = request.match_info["pid"]
    async with lock:
        u = user_by_pid(db_load(), pid)
    if not u or not u.get("avatar"):
        return web.Response(status=404)
    data = await blob_get(f"avatar/{pid}")
    if not data:
        return web.Response(status=404)
    return web.Response(body=data, content_type=CTYPES.get(u.get("avatar_ext", "jpg"), "image/jpeg"),
                        headers={"Cache-Control": "public, max-age=86400", "X-Content-Type-Options": "nosniff"})


@api()
def api_avatar_delete(request, db, user, body, outbox, ctx):
    _drop_avatar_files(user["pid"])
    user.pop("avatar", None)
    user.pop("avatar_ext", None)
    return {"ok": True}


# ---------- сайт ----------
def _index_path():
    # сначала index.html рядом с bot.py, затем static/index.html
    for path in (BASE / "index.html", BASE / "static" / "index.html"):
        if path.is_file():
            return path
    return None


async def index(_):
    path = _index_path()
    if path is None:
        logging.error("index.html не найден ни в %s, ни в %s", BASE / "static", BASE)
        return web.Response(status=500, text="index.html не найден: положите его рядом с bot.py или в папку static")
    return web.Response(body=path.read_bytes(), content_type="text/html", charset="utf-8", headers=NOSTORE)


async def debug(_):
    """Диагностика: какой файл отдаётся сайтом (можно удалить после настройки)."""
    path = _index_path()
    info = {"base": str(BASE), "files": sorted(x.name for x in BASE.iterdir())[:40],
            "static_dir": (BASE / "static").is_dir(), "index_path": str(path) if path else None,
            "storage": "postgres" if _pg else "files (данные пропадут при деплое!)",
            "users": len((_cache.get("app") or {}).get("users", {})), "top_rows": len(_cache.get("top") or [])}
    if path:
        raw = path.read_bytes()
        txt = raw.decode("utf-8", "replace")
        i = txt.find("<title>")
        info.update(size=len(raw), sha1=hashlib.sha1(raw).hexdigest()[:10],
                    title=txt[i + 7:txt.find("</title>")] if i >= 0 else None,
                    new_version=('id="boot"' in txt and 'id="fatal"' in txt),
                    new_background=('id="bgfx"' in txt), referral_tab=('id="t-invite"' in txt))
    return web.json_response(info, headers=NOSTORE)


async def api_top(_):
    async with lock:
        rows = ranked(load())
        db = db_load()
    by_pid = {u["pid"]: u for u in db["users"].values()}
    for r in rows:  # игроки, добавленные через /stat, показываются с актуальным ником и аватаркой
        u = by_pid.get(r.get("pid"))
        r["pid"] = u["pid"] if u else ""
        r["av"] = u.get("avatar", 0) if u else 0
        if u:
            r["nick"] = u["nick"]
    return web.json_response(rows, headers=NOSTORE)


async def api_public_profile(request):
    """Профиль игрока из топа для тех, кто не вошёл: виден только если игрок есть в топе."""
    pid = request.match_info["pid"]
    async with lock:
        db = db_load()
        u = user_by_pid(db, pid)
        st = top_stats(pid) if u else None
    if not u or not st:
        return web.json_response({"error": "Игрок не найден"}, status=404, headers=NOSTORE)
    return web.json_response({**pub(u), "stats": st, "record": match_record(db, uid_of(u)),
                              "history": match_history(db, uid_of(u))}, headers=NOSTORE)


async def health(_):
    return web.Response(text="ok")


async def main():
    global BOT_USERNAME
    logging.basicConfig(level=logging.INFO)
    await store_init()
    if not ADMIN_IDS:
        logging.warning("ADMIN_IDS пуст: менять таблицу никто не сможет")
    if not BOT_USERNAME:
        BOT_USERNAME = (await bot.get_me()).username
    app = web.Application(client_max_size=MAX_SHOT + 64 * 1024)  # лимит корневого приложения действует и на загрузки
    app.add_routes([
        web.get("/", index), web.get("/api/top", api_top), web.get("/health", health), web.get("/debug", debug),
        web.post("/api/auth/start", api_auth_start),
        web.get("/api/auth/check", api_auth_check),
        web.post("/api/auth/webapp", api_auth_webapp),
        web.post("/api/logout", api_logout),
        web.get("/api/me", api_me),
        web.post("/api/profile", api_profile),
        web.get("/api/users", api_users),
        web.get("/api/users/{pid}", api_user),
        web.get("/api/friends", api_friends),
        web.post("/api/friends/add", api_friend_add),
        web.post("/api/friends/remove", api_friend_remove),
        web.post("/api/freqs/{id}/{act:accept|decline|cancel}", api_freq_resolve),
        web.get("/api/party", api_party),
        web.post("/api/party/invite", api_party_invite),
        web.post("/api/party/size", api_party_size),
        web.post("/api/party/leave", api_party_leave),
        web.post("/api/party/kick", api_party_kick),
        web.post("/api/pinvites/{id}/{act:accept|decline|cancel}", api_pinvite_resolve),
        web.post("/api/queue/start", api_queue_start),
        web.post("/api/queue/cancel", api_queue_cancel),
        web.post("/api/match/cancel", api_match_cancel),
        web.post("/api/match/report", api_match_report),
        web.post("/api/match/confirm", api_match_confirm),
        web.post("/api/match/ban", api_match_ban),
        web.post("/api/match/vote", api_match_vote),
        web.get("/api/match/chat", api_match_chat_get),
        web.post("/api/match/chat", api_match_chat_send),
        web.post("/api/admin/ban", api_admin_ban),
        web.get("/api/shot/{mid:[0-9a-f]+}/{sid:[0-9a-f]+}", api_shot_get),
        web.get("/api/avatar/{pid:[0-9a-f]+}", api_avatar_get),
        web.get("/api/public/{pid:[0-9a-f]+}", api_public_profile),
        web.post("/api/avatar/delete", api_avatar_delete),
    ])
    up = web.Application(client_max_size=MAX_SHOT + 4096)  # загрузка скриншотов, лимит только здесь
    up.add_routes([web.post("/avatar", api_avatar_upload), web.post("/idcheck", api_idcheck_upload), web.post("/{mid:[0-9a-f]+}", api_shot_upload)])
    app.add_subapp("/api/shots", up)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()

    dp = Dispatcher()
    dp.include_router(router)
    nudger = asyncio.create_task(invite_nudger())
    try:
        await dp.start_polling(bot)
    finally:
        nudger.cancel()
        await store_flush()  # дописать последние изменения в базу


if __name__ == "__main__":
    asyncio.run(main())
