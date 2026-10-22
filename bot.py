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
QUEUE_TTL = 3600           # поиск без матча сбрасывается через час
MATCH_TTL = 6 * 3600       # активный матч без результата отменяется через 6 часов
KEEP_DAYS = 3              # сколько хранить скриншоты завершённых матчей
HISTORY_DAYS = 90          # сколько хранить историю матчей (кто играл, результат)

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


def ranked(data: list) -> list:
    rows = sorted(data, key=lambda p: p["elo"], reverse=True)[:TOP_N]
    return [{**p, "rank": i, "level": level_of(p["elo"])}
            for i, p in enumerate(rows, start=1)]


def upsert(data: list, nick: str, elo: int, kd=None, win=None) -> None:
    for p in data:
        if p["nick"].lower() == nick.lower():
            p["nick"], p["elo"] = nick, elo
            if kd is not None:
                p["kd"] = kd
            if win is not None:
                p["win"] = win
            return
    data.append({"nick": nick, "elo": elo,
                 "kd": kd if kd is not None else 1.0,
                 "win": win if win is not None else 50})


def parse_parts(parts: list):
    """ник ELO [K/D] [победы%] -> (nick, elo, kd, win)"""
    nick, elo = parts[0][:32], int(parts[1])
    kd = float(parts[2].replace(",", ".")) if len(parts) > 2 else None
    win = int(parts[3]) if len(parts) > 3 else None
    return nick, elo, kd, win


def is_admin(m: Message) -> bool:
    return m.from_user is not None and m.from_user.id in ADMIN_IDS


# ---------- база: пользователи, друзья, пати ----------
class ApiError(Exception):
    def __init__(self, status: int, msg: str):
        self.status, self.msg = status, msg


def db_load() -> dict:
    d = copy.deepcopy(_cache.get("app") or {})  # копия: если запрос упадёт, кэш не испортится
    for k in ("users", "sessions", "codes", "friends", "freqs", "parties", "pinvites", "queue", "matches"):
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
    """Место, ELO, K/D и победы игрока, если он есть в топе (привязан к профилю)."""
    r = next((x for x in ranked(load()) if x.get("pid") == pid), None)
    if not r:
        return None
    return {"rank": r["rank"], "elo": r["elo"], "kd": r.get("kd", 0), "win": r.get("win", 0), "level": r["level"]}


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


def find_user(db, key: str):
    """Игрок по ID в игре; если такого нет, по точному нику или Telegram-нику."""
    k = key.strip().lstrip("@")
    u = next((x for x in db["users"].values() if x.get("game_id") and x["game_id"] == k), None)
    if u:
        return u
    hits = [x for x in db["users"].values()
            if x["nick"].lower() == k.lower() or (x.get("tg_username") or "").lower() == k.lower()]
    return hits[0] if len(hits) == 1 else None


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


def end_match(db, m, status, outbox, text, winner=None):
    m["status"], m["ended"] = status, int(time.time())
    if winner is not None:
        m["winner"] = winner
    for t in m["teams"]:
        for uid in t["members"]:
            u = db["users"].get(uid)
            if u:
                outbox.append((u["tg_id"], text, None))


def notify_admins_dispute(db, m, outbox):
    lines = [f"Спорный матч {m['id']} ({m['size']}x{m['size']})"]
    for i, t in enumerate(m["teams"], start=1):
        names = ", ".join(db["users"][u]["nick"] + (" (кап.)" if u == t["captain"] else "")
                          for u in t["members"] if u in db["users"])
        lines.append(f"Команда {i}: {names}")
    r = m.get("report") or {}
    lines.append(f"Заявлено: победила команда {r.get('winner', 0) + 1}, счёт {r.get('score') or '-'}")
    lines.append(f"Решение: /winner {m['id']} 1  или  /winner {m['id']} 2\nОтмена: /cancelmatch {m['id']}")
    for a in ADMIN_IDS:
        outbox.append((a, "\n".join(lines), None))
        for sh in m["shots"][:6]:
            outbox.append((a, f"Скриншот: команда {sh['team'] + 1}", None, f"shot/{m['id']}_{sh['id']}"))


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
    if party_of(db, me):
        raise ApiError(400, "Вы уже в пати - сначала выйдите из неё")
    if queue_of(db, me):
        raise ApiError(400, "Сначала отмените поиск игры")
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
                await bot.send_photo(tg_id, BufferedInputFile(data, filename="screenshot.jpg"), caption=text)
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
    text = ("Топ игроков FACEIT.\n/top - топ-10\n/profile - ваш профиль и пати\n"
            f"Ваш Telegram ID: {m.from_user.id}")
    if is_admin(m):
        text += ("\n\nКоманды админа:\n"
                 "/elo Ник 4210 [K/D] [победы] - добавить или изменить\n"
                 "/del Ник - удалить\n"
                 "/import - заменить весь список (строки: ник ELO K/D победы)\n"
                 "/stat ID_или_@ник ELO [K/D] [победы] - добавить игрока в топ вместе с профилем и аватаркой\n"
                 "/resetid ID_в_игре - сбросить ID игрока (если ошибся)\n"
                 "/ban ID_или_@ник [причина], /unban, /banlist - блокировки\n"
                 "/users - кто зарегистрирован (чтобы добавить в топ)\n"
                 "/stat ID_в_игре ELO [K/D] [победы] - начислить статистику (/stat ID +25 - прибавить ELO)\n"
                 "/matches - последние матчи, /match ID - подробности и скриншоты\n"
                 "/winner ID 1|2 - назначить победителя\n"
                 "/cancelmatch ID - отменить матч")
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


@router.message(Command("elo"))
async def cmd_elo(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    try:
        nick, elo, kd, win = parse_parts((command.args or "").split())
    except (ValueError, IndexError):
        return await m.answer("Формат: /elo Ник 4210 [K/D] [победы]")
    async with lock:
        data = load()
        upsert(data, nick, elo, kd, win)
        save(data)
    await m.answer(f"Готово: {nick} - {elo}")


@router.message(Command("del"))
async def cmd_del(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    nick = (command.args or "").strip()
    if not nick:
        return await m.answer("Формат: /del Ник")
    async with lock:
        data = load()
        new = [p for p in data if p["nick"].lower() != nick.lower()]
        if len(new) == len(data):
            return await m.answer("Такого игрока нет.")
        save(new)
    await m.answer(f"Удалён: {nick}")


@router.message(Command("import"))
async def cmd_import(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    lines = [l for l in (command.args or "").splitlines() if l.strip()]
    if not lines:
        return await m.answer("Пришлите так:\n/import\nRapira 4210 1.45 63\nPlayer2 4100 1.40 61")
    data, bad = [], []
    for l in lines:
        try:
            nick, elo, kd, win = parse_parts(l.replace(",", " ").split())
            upsert(data, nick, elo, kd, win)
        except (ValueError, IndexError):
            bad.append(l)
    if not data:
        return await m.answer("Не удалось разобрать ни одной строки.")
    async with lock:
        old = {p["nick"].lower(): p["pid"] for p in load() if p.get("pid")}  # сохраняем привязки аватарок
        for p in data:
            if p["nick"].lower() in old:
                p["pid"] = old[p["nick"].lower()]
        save(data)
    msg = f"Список заменён, игроков: {len(data)}"
    if bad:
        msg += f"\nПропущено строк: {len(bad)}"
    await m.answer(msg)


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
        "/users - кто зарегистрирован (/users 2 - вторая страница, /users ник - поиск)\n"
        "/stat ID_в_игре ELO [K/D] [победы] - начислить статистику игроку, он попадёт в топ с профилем\n"
        "/elo Ник ELO [K/D] [победы%] - добавить или обновить игрока в топе\n"
        "/del Ник - убрать из топа\n"
        "/import - заменить весь топ списком\n"
        "/matches - последние матчи (/matches спор - только спорные)\n"
        "/match ID - подробности матча и скриншоты\n"
        "/winner ID 1|2 - решить спорный матч\n"
        "/cancelmatch ID - отменить матч\n"
        "/stat ID_или_@ник ELO [K/D] [победы] - добавить зарегистрированного игрока в топ с профилем\n"
        "/resetid ID_в_игре - сбросить ID игрока")


@router.message(Command("users"))
async def cmd_users(m: Message, command: CommandObject):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    arg = (command.args or "").strip()
    page, q = 1, ""
    if arg.isdigit() and int(arg) <= 99:
        page = int(arg)
    else:
        q = arg.lower().lstrip("@")
    async with lock:
        db, top = db_load(), load()
    users = sorted(db["users"].values(), key=lambda u: u.get("created", 0), reverse=True)  # новые сверху
    if q:
        users = [u for u in users if q in u["nick"].lower() or q in (u.get("tg_username") or "").lower()
                 or q in (u.get("game_id") or "")]
    if not users:
        return await m.answer("Никого не нашёл." if q else "Пока никто не зарегистрировался.")
    per = 40
    pages = (len(users) + per - 1) // per
    page = min(page, pages)
    nicks = {p["nick"].lower() for p in top}
    pids = {p["pid"] for p in top if p.get("pid")}
    lines = [f"Зарегистрировано: {len(users)}" + (f" (страница {page}/{pages}, дальше: /users {page + 1})" if pages > 1 else "")]
    for i, u in enumerate(users[(page - 1) * per:page * per], start=(page - 1) * per + 1):
        in_top = u["nick"].lower() in nicks or u["pid"] in pids
        lines.append(f"{i}. {u['nick']} | ID {u.get('game_id') or '-'} | {tg_tag(u)} | {'в топе' if in_top else 'не в топе'}")
    lines.append("Добавить игрока в топ с профилем и аватаркой: /stat ID_в_игре ELO [K/D] [победы%]. Метка «в топе» ставится, если игрок есть в таблице.")
    await _send_long(m, lines)


@router.message(Command("stat"))
async def cmd_stat(m: Message, command: CommandObject):
    # начисление после матча: игрок попадает в топ, и к его строке привязывается профиль
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    usage = ("Формат: /stat ID_в_игре ELO [K/D] [победы]\nПример: /stat 12345678 1500 1.35 56\n"
             "Прибавить или отнять ELO: /stat 12345678 +25  или  /stat 12345678 -20")
    parts = (command.args or "").split()
    try:
        delta = parts[1][0] in "+-"
        val = int(parts[1])
        kd = float(parts[2].replace(",", ".")) if len(parts) > 2 else None
        win = int(parts[3]) if len(parts) > 3 else None
    except (ValueError, IndexError):
        return await m.answer(usage)
    if (kd is not None and not 0 <= kd <= 20) or (win is not None and not 0 <= win <= 100):
        return await m.answer("K/D должен быть от 0 до 20, победы от 0 до 100.")
    outbox = []
    async with lock:
        db, data = db_load(), load()
        u = find_user(db, parts[0])
        if not u:
            return await m.answer("Игрок не найден. Список зарегистрированных: /users")
        row = next((x for x in data if x.get("pid") == u["pid"]), None)
        if row is None:
            same = next((x for x in data if x["nick"].lower() == u["nick"].lower()), None)
            if same and not same.get("pid"):
                row = same  # ник уже был в топе без привязки: привязываем
            elif same:
                return await m.answer(f"В топе уже есть другой игрок с ником {same['nick']}. Сначала /del {same['nick']}")
        if row is None:
            if delta:
                return await m.answer("Игрока ещё нет в топе, укажите ELO числом без знака: /stat ID 1000")
            row = {"nick": u["nick"], "elo": val, "kd": 1.0, "win": 50}
            data.append(row)
        elif delta:
            row["elo"] = max(0, row["elo"] + val)
        else:
            row["elo"] = max(0, val)
        if kd is not None:
            row["kd"] = kd
        if win is not None:
            row["win"] = win
        row["pid"] = u["pid"]
        save(data)
        res = f"ELO {row['elo']}, K/D {float(row['kd']):.2f}, победы {row['win']}%"
        outbox.append((u["tg_id"], f"Вам начислена статистика: {res}. Ваш профиль в топе: {PUBLIC_URL or 'на сайте'}", None))
    await m.answer(f"Готово: {u['nick']} (ID {u.get('game_id') or '-'}) - {res}. Профиль привязан к топу.")
    await flush(outbox)


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
    lines.append("Начислить статистику игроку: /stat ID_в_игре ELO K/D победы")
    await _send_long(m, lines)
    await flush([(m.from_user.id, f"Скриншот: команда {sh['team'] + 1}", None, f"shot/{mt['id']}_{sh['id']}")
                 for sh in mt["shots"][:6]])


async def _admin_finish(m: Message, command: CommandObject, cancel: bool):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").split()
    if not parts or (not cancel and (len(parts) < 2 or parts[1] not in ("1", "2"))):
        return await m.answer("Формат: /cancelmatch ID  или  /winner ID 1|2")
    outbox = []
    async with lock:
        db = db_load()
        mt = db["matches"].get(parts[0])
        if not mt or mt["status"] not in ("active", "disputed"):
            return await m.answer("Такого матча нет или он уже закрыт.")
        if cancel:
            end_match(db, mt, "cancelled", outbox, "Матч отменён администратором.")
        else:
            w = int(parts[1]) - 1
            end_match(db, mt, "finished", outbox, f"Администратор определил результат: победила команда {w + 1}.", winner=w)
        db_save(db)
    await m.answer("Готово.")
    await flush(outbox)


@router.message(Command("winner"))
async def cmd_winner(m: Message, command: CommandObject):
    await _admin_finish(m, command, False)


@router.message(Command("cancelmatch"))
async def cmd_cancelmatch(m: Message, command: CommandObject):
    await _admin_finish(m, command, True)


@router.message(Command("stat"))
async def cmd_stat(m: Message, command: CommandObject):
    # импорт профиля в топ: берём зарегистрированного игрока и ставим его в таблицу вместе с аватаркой и профилем
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").split()
    try:
        if len(parts) < 2:
            raise ValueError
        elo = int(parts[1])
        kd = float(parts[2].replace(",", ".")) if len(parts) > 2 else None
        win = int(parts[3]) if len(parts) > 3 else None
    except ValueError:
        return await m.answer("Формат: /stat ID_в_игре_или_@ник ELO [K/D] [победы]\n"
                              "Пример: /stat 127566 4210 1.45 63\nСписок игроков: /users")
    async with lock:
        db, data = db_load(), load()
        u = find_user(db, parts[0])
        if not u:
            return await m.answer("Игрок не найден среди зарегистрированных. Список: /users")
        p = (next((x for x in data if x.get("pid") == u["pid"]), None)
             or next((x for x in data if x["nick"].lower() == u["nick"].lower()), None))
        if p is None:
            p = {"nick": u["nick"], "elo": elo, "kd": 1.0, "win": 50}
            data.append(p)
        p["pid"], p["nick"], p["elo"] = u["pid"], u["nick"], elo
        if kd is not None:
            p["kd"] = kd
        if win is not None:
            p["win"] = win
        save(data)
        row = next((r for r in ranked(data) if r.get("pid") == u["pid"]), None)
    await m.answer(f"{u['nick']} в топе: " + (f"место №{row['rank']}, " if row else "") +
                   f"ELO {elo}, K/D {p['kd']}, победы {p['win']}%.\n"
                   "Профиль, аватарка и статистика привязаны и видны на сайте.")


@router.message(Command("resetid"))
async def cmd_resetid(m: Message, command: CommandObject):
    # сброс ID в игре (если игрок ошибся): /resetid ID_в_игре
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    gid = (command.args or "").strip()
    if not gid:
        return await m.answer("Формат: /resetid ID_в_игре")
    async with lock:
        db = db_load()
        u = next((x for x in db["users"].values() if (x.get("game_id") or "") == gid), None)
        if not u:
            return await m.answer("Игрок с таким ID не найден.")
        if queue_of(db, uid_of(u)) or match_of(db, uid_of(u)):
            return await m.answer("Игрок сейчас в поиске или матче, попробуйте позже.")
        u["game_id"] = ""
        db_save(db)
    await m.answer(f"ID сброшен у {u['nick']}.")
    await flush([(u["tg_id"], "Администратор сбросил ваш ID в игре. Укажите правильный ID на сайте, он вводится один раз.", None)])


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
        return await m.answer("Формат: /ban ID_в_игре или @username [причина]" if ban
                              else "Формат: /unban ID_в_игре или @username")
    outbox = []
    async with lock:
        db = db_load()
        u = find_user(db, parts[0])
        if not u:
            return await m.answer("Игрок не найден.")
        if u["tg_id"] in ADMIN_IDS:
            return await m.answer("Администратора заблокировать нельзя.")
        apply_ban(db, u, ban, parts[1] if len(parts) > 1 else "", outbox)
        db_save(db)
    await m.answer(f"{'Заблокирован' if ban else 'Разблокирован'}: {u['nick']}")
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
    await m.answer("\n".join(f"{u['nick']} (ID {u.get('game_id') or '-'}){': ' + u['ban_reason'] if u.get('ban_reason') else ''}"
                             for u in rows[:50]) or "Заблокированных нет.")


# ---------- API сайта ----------
def api(auth: bool = True):
    """Обёртка: блокировка, загрузка базы, авторизация, сохранение, уведомления в бота."""
    def deco(fn):
        async def handler(request: web.Request):
            body = {}
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
                    if auth and user is None:
                        raise ApiError(401, "Нужен вход через Telegram")
                    ctx = {"dirty": request.method == "POST" or bool(changed)}
                    res = fn(request, db, user, body, outbox, ctx)
                    if ctx["dirty"]:
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
    cfg = {"bot": BOT_USERNAME}
    if user is None:
        return {"user": None, "cfg": cfg}
    uid = uid_of(user)
    return {"user": {**pub(user), "tg": user.get("tg_username", ""), "admin": user["tg_id"] in ADMIN_IDS,
                     "banned": bool(user.get("banned"))}, "cfg": cfg,
            "badges": {"friends": sum(1 for r in db["freqs"].values() if r["to"] == uid),
                       "party": sum(1 for i in db["pinvites"].values() if i["to"] == uid)}}


@api()
def api_profile(request, db, user, body, outbox, ctx):
    user["nick"] = clean_str(body.get("nick"), 32, "Ник", 2)
    user["about"] = clean_str(body.get("about"), 300, "О себе")
    gid = clean_str(body.get("game_id"), 20, "ID в игре")
    cur = user.get("game_id", "")
    if cur and gid in ("", cur):
        gid = cur
    elif cur:
        raise ApiError(400, "ID в игре нельзя изменить. Если ошиблись, напишите администратору")
    if gid:
        if not re.fullmatch(r"[0-9]{3,20}", gid):
            raise ApiError(400, "ID в игре: только цифры, от 3 до 20")
        me = uid_of(user)
        if any(k != me and (v.get("game_id") or "").lower() == gid.lower() for k, v in db["users"].items()):
            raise ApiError(400, "Этот ID уже занят другим игроком")
    user["game_id"] = gid
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
            rows.append({**pub(u), "relation": rel, "req_id": rid})
    return rows[:15]


@api()
def api_user(request, db, user, body, outbox, ctx):
    u = user_by_pid(db, request.match_info["pid"])
    if not u:
        raise ApiError(404, "Игрок не найден")
    rel, rid = relation(db, uid_of(user), uid_of(u))
    d = {**pub(u), "relation": rel, "req_id": rid,
         "friends_count": len(db["friends"].get(uid_of(u), []))}
    if rel in ("friend", "self") and u.get("tg_username"):
        d["tg"] = u["tg_username"]  # Telegram виден только друзьям
    st = top_stats(u["pid"])
    if st:
        d["stats"] = st
    d["record"] = match_record(db, uid_of(u))
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
            friends.append({**pub(fu), "in_party": party_of(db, f) is not None, "invited": f in invited})
    friends.sort(key=lambda x: x["nick"].lower())
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
            last = {"status": mm["status"], "result": res}
            break
    modes = {n: sum(len(x["members"]) for x in db["queue"].values() if x["size"] == n and is_fresh(x)) for n in SIZES}
    return {"party": party_view(db, p, me) if p else None, "invites": invites, "modes": modes,
            "queue": queue, "match": match_view(db, m, me) if m else None, "last": last}


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
    if party_of(db, tid):
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
    db["pinvites"][iid] = {"id": iid, "party": p["id"], "to": tid}
    outbox.append((target["tg_id"], f"{user['nick']} зовёт вас в пати {p['size']}x{p['size']} "
                                    f"({len(p['members'])}/{p['size']})", accept_kb("pi", iid)))
    return {"message": "Приглашение отправлено"}


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


# --- ID в игре: вводится один раз и навсегда ---
@api()
def api_game_id(request, db, user, body, outbox, ctx):
    if user.get("game_id"):
        raise ApiError(400, "ID уже указан и не меняется")
    gid = clean_str(body.get("game_id"), 20, "ID в игре", 3)
    if not re.fullmatch(r"[0-9]{3,20}", gid):
        raise ApiError(400, "ID в игре: только цифры, от 3 до 20")
    me = uid_of(user)
    if any(k != me and (v.get("game_id") or "") == gid for k, v in db["users"].items()):
        raise ApiError(400, "Этот ID уже занят другим игроком")
    user["game_id"] = gid
    return {"message": "ID сохранён"}


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
                           + (f": {bu['ban_reason']}" if bu.get("ban_reason") else ""))
    for m in members:
        if not db["users"].get(m, {}).get("game_id"):
            raise ApiError(400, "Сначала укажите ID в игре" if m == me
                           else f"У игрока {db['users'][m]['nick']} не указан ID в игре")
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


def find_user(db, key: str):
    key = key.strip().lstrip("@")
    if not key:
        return None
    return next((u for u in db["users"].values()
                 if key == (u.get("game_id") or "") or key.lower() == (u.get("tg_username") or "").lower()
                 or key == u["pid"]), None)


def apply_ban(db, u, banned: bool, reason: str, outbox) -> None:
    u["banned"], u["ban_reason"] = banned, (reason[:200] if banned else "")
    if banned:
        t = queue_of(db, uid_of(u))
        if t:
            del db["queue"][t["id"]]
    outbox.append((u["tg_id"], ("Вы заблокированы администратором" + (f": {reason}" if reason else "") + ".")
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
    rep = m.get("report")
    if rep and rep["team"] != ti:
        raise ApiError(400, "Соперники уже отправили результат: подтвердите или оспорьте его")
    w = body.get("winner")
    if w not in ("me", "enemy"):
        raise ApiError(400, "Укажите, кто победил")
    m["report"] = {"team": ti, "winner": ti if w == "me" else 1 - ti,
                   "score": clean_str(body.get("score"), 10, "Счёт"), "ts": int(time.time())}
    other = db["users"].get(m["teams"][1 - ti]["captain"])
    if other:
        outbox.append((other["tg_id"], "Капитан соперников отправил результат матча. "
                       "Откройте комнату, проверьте скриншот и подтвердите или оспорьте.", room_kb()))
    return {"message": "Результат отправлен капитану соперников"}


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
                    new_version=('id="boot"' in txt and 'id="fatal"' in txt))
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
    return web.json_response({**pub(u), "stats": st, "record": match_record(db, uid_of(u))}, headers=NOSTORE)


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
    app = web.Application(client_max_size=64 * 1024)
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
        web.post("/api/game_id", api_game_id),
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
    up.add_routes([web.post("/avatar", api_avatar_upload), web.post("/{mid:[0-9a-f]+}", api_shot_upload)])
    app.add_subapp("/api/shots", up)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()

    dp = Dispatcher()
    dp.include_router(router)
    try:
        await dp.start_polling(bot)
    finally:
        await store_flush()  # дописать последние изменения в базу


if __name__ == "__main__":
    asyncio.run(main())
