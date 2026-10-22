"""Rapira Faceit: Telegram-бот + сайт (топ, профили, подбор в команду) в одном процессе.

Переменные окружения:
  BOT_TOKEN     - токен от @BotFather (обязательно)
  ADMIN_IDS     - ваши Telegram ID через запятую (кто может менять таблицу топа)
  PUBLIC_URL    - https-адрес сайта, например https://myapp.onrender.com
  PORT          - порт (хостинг обычно задаёт сам)
  DATA_FILE     - файл с топом игроков (по умолчанию data.json)
  APP_FILE      - файл с пользователями, командами, заявками (по умолчанию app.json)
  BOT_USERNAME  - необязательно, @username бота (иначе берётся через getMe)
  SHOTS_DIR     - папка для скриншотов матчей (по умолчанию shots рядом с APP_FILE)
  AVATARS_DIR   - папка для аватарок (по умолчанию avatars рядом с APP_FILE)

Важно: DATA_FILE и APP_FILE должны лежать на постоянном диске хостинга.
"""
import asyncio
import hashlib
import hmac
import json
import logging
import os
import re
import secrets
import tempfile
import time
from pathlib import Path
from urllib.parse import parse_qsl

from aiogram import Bot, Dispatcher, F, Router
from aiogram.filters import Command, CommandObject
from aiogram.types import (CallbackQuery, InlineKeyboardButton,
                           InlineKeyboardMarkup, Message, WebAppInfo, FSInputFile)
from aiohttp import web

BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
PUBLIC_URL = os.getenv("PUBLIC_URL", "").rstrip("/")
PORT = int(os.getenv("PORT", "8080"))
DATA_FILE = Path(os.getenv("DATA_FILE", "data.json"))
APP_FILE = Path(os.getenv("APP_FILE", "app.json"))
BOT_USERNAME = os.getenv("BOT_USERNAME", "").lstrip("@")
BASE = Path(__file__).parent
TOP_N = 100
SHOTS_DIR = Path(os.getenv("SHOTS_DIR", str(APP_FILE.parent / "shots")))
MAX_SHOT = 5 * 1024 * 1024
AVATARS_DIR = Path(os.getenv("AVATARS_DIR", str(APP_FILE.parent / "avatars")))
MAX_AVATAR = 2 * 1024 * 1024
QUEUE_TTL = 3600           # поиск без матча сбрасывается через час
MATCH_TTL = 6 * 3600       # активный матч без результата отменяется через 6 часов
KEEP_DAYS = 3              # сколько хранить завершённые матчи и скриншоты

SIZES = (3, 4, 5)  # пати 3x3, 4x4, 5x5
SESSION_TTL = 30 * 24 * 3600
CODE_TTL = 5 * 60

lock = asyncio.Lock()
router = Router()
bot = Bot(BOT_TOKEN)
NOSTORE = {"Cache-Control": "no-store"}


# ---------- топ (как раньше) ----------
def load() -> list:
    if not DATA_FILE.exists():
        return []
    try:
        return json.loads(DATA_FILE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return []


def _atomic_write(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False)
    os.replace(tmp, path)  # атомарная запись


def save(data: list) -> None:
    _atomic_write(DATA_FILE, data)


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
    d = {}
    if APP_FILE.exists():
        try:
            d = json.loads(APP_FILE.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            d = {}
    for k in ("users", "sessions", "codes", "friends", "freqs", "parties", "pinvites", "queue", "matches"):
        d.setdefault(k, {})
    return d


def db_save(db: dict) -> None:
    _atomic_write(APP_FILE, db)


def cleanup(db: dict) -> None:
    t = time.time()
    for k in [k for k, v in db["codes"].items() if v["exp"] < t]:
        del db["codes"][k]
    for k in [k for k, v in db["sessions"].items() if v["exp"] < t]:
        del db["sessions"][k]
    for k in [k for k, v in db["queue"].items() if v["joined"] < t - QUEUE_TTL]:
        del db["queue"][k]
    for mid, m in list(db["matches"].items()):
        if m["status"] == "active" and m["created"] < t - MATCH_TTL:
            m["status"], m["ended"] = "cancelled", int(t)
        elif m["status"] in ("finished", "cancelled") and m.get("ended", 0) < t - KEEP_DAYS * 86400:
            for f in SHOTS_DIR.glob(f"{mid}_*"):
                try:
                    f.unlink()
                except OSError:
                    pass
            del db["matches"][mid]


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


def try_match(db, n, outbox):
    while True:
        tickets = sorted((t for t in db["queue"].values() if t["size"] == n), key=lambda t: t["joined"])
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
        db["matches"][mid] = {"id": mid, "size": n, "status": "active", "created": int(time.time()),
                              "teams": teams, "shots": [], "report": None, "cancel_votes": []}
        for ti, t in enumerate(teams, start=1):
            cap = db["users"][t["captain"]]
            for uid in t["members"]:
                u = db["users"].get(uid)
                if not u:
                    continue
                if uid == t["captain"]:
                    role = ("Вы капитан команды: после игры сделайте скриншот результата "
                            "и прикрепите его в комнате матча.")
                else:
                    role = f"Капитан вашей команды: {cap['nick']} ({tg_tag(cap)})."
                outbox.append((u["tg_id"], f"Матч {n}x{n} найден! Вы в команде {ti}.\n{role}", room_kb()))


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
            path = SHOTS_DIR / f"{m['id']}_{sh['id']}.{sh['ext']}"
            if path.is_file():
                outbox.append((a, f"Скриншот: команда {sh['team'] + 1}", None, str(path)))


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
    return {"id": m["id"], "size": m["size"], "team": ti, "captain": m["teams"][ti]["captain"] == me,
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
            if photo:
                await bot.send_photo(tg_id, FSInputFile(photo), caption=text)
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
                 "/link Ник ID_в_игре - привязать аватарку игрока к нику в топе\n"
                 "/matches - спорные и активные матчи\n"
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


@router.message(Command("matches"))
async def cmd_matches(m: Message):
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    async with lock:
        db = db_load()
        rows = [x for x in db["matches"].values() if x["status"] in ("disputed", "active")]
    if not rows:
        return await m.answer("Спорных и активных матчей нет.")
    await m.answer("\n".join(f"{x['id']} - {x['status']} ({x['size']}x{x['size']})" for x in rows[:30]))


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


@router.message(Command("link"))
async def cmd_link(m: Message, command: CommandObject):
    # привязка ника из топа к зарегистрированному игроку, чтобы в топе показывалась его аватарка
    if not is_admin(m):
        return await m.answer("Нет доступа.")
    parts = (command.args or "").split()
    if len(parts) != 2:
        return await m.answer("Формат: /link Ник ID_в_игре  (отвязать: /link Ник off)")
    async with lock:
        data, db = load(), db_load()
        p = next((x for x in data if x["nick"].lower() == parts[0].lower()), None)
        if not p:
            return await m.answer("Такого ника нет в топе.")
        if parts[1].lower() == "off":
            p.pop("pid", None)
        else:
            u = next((x for x in db["users"].values() if (x.get("game_id") or "") == parts[1]), None)
            if not u:
                return await m.answer("Игрок с таким ID в игре не зарегистрирован на сайте.")
            p["pid"] = u["pid"]
        save(data)
    await m.answer("Готово.")


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
                    cleanup(db)
                    user = session_user(db, request)
                    if auth and user is None:
                        raise ApiError(401, "Нужен вход через Telegram")
                    ctx = {"dirty": request.method == "POST"}
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
    return {"user": {**pub(user), "tg": user.get("tg_username", "")}, "cfg": cfg,
            "badges": {"friends": sum(1 for r in db["freqs"].values() if r["to"] == uid),
                       "party": sum(1 for i in db["pinvites"].values() if i["to"] == uid)}}


@api()
def api_profile(request, db, user, body, outbox, ctx):
    user["nick"] = clean_str(body.get("nick"), 32, "Ник", 2)
    user["about"] = clean_str(body.get("about"), 300, "О себе")
    gid = clean_str(body.get("game_id"), 20, "ID в игре")
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
    queue = None
    if t:
        queue = {"size": t["size"], "need": 2 * t["size"], "elapsed": int(time.time() - t["joined"]),
                 "waiting": sum(len(x["members"]) for x in db["queue"].values() if x["size"] == t["size"]),
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
    return {"party": party_view(db, p, me) if p else None, "invites": invites,
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
    tid = secrets.token_hex(4)
    db["queue"][tid] = {"id": tid, "owner": me, "party": pid, "members": members,
                        "size": size, "joined": time.time()}
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
        SHOTS_DIR.mkdir(parents=True, exist_ok=True)
        (SHOTS_DIR / f"{m['id']}_{sid}.{ext}").write_bytes(data)
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
    path = SHOTS_DIR / f"{m['id']}_{sh['id']}.{sh['ext']}" if sh else None
    if not path or not path.is_file():
        return web.Response(status=404)
    return web.FileResponse(path, headers={**NOSTORE, "X-Content-Type-Options": "nosniff"})


def sniff_ext(b: bytes):
    if b[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if b[:3] == b"\xff\xd8\xff":
        return "jpg"
    if b[:4] == b"RIFF" and b[8:12] == b"WEBP":
        return "webp"
    return None


def _drop_avatar_files(pid: str) -> None:
    for f in AVATARS_DIR.glob(pid + ".*"):
        try:
            f.unlink()
        except OSError:
            pass


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
        AVATARS_DIR.mkdir(parents=True, exist_ok=True)
        _drop_avatar_files(user["pid"])
        (AVATARS_DIR / f"{user['pid']}.{ext}").write_bytes(data)
        user["avatar"], user["avatar_ext"] = int(time.time()), ext
        db_save(db)
    return web.json_response({"ok": True, "av": user["avatar"]}, headers=NOSTORE)


async def api_avatar_get(request):
    pid = request.match_info["pid"]
    async with lock:
        u = user_by_pid(db_load(), pid)
    if not u or not u.get("avatar"):
        return web.Response(status=404)
    path = AVATARS_DIR / f"{pid}.{u.get('avatar_ext', 'jpg')}"
    if not path.is_file():
        return web.Response(status=404)
    return web.FileResponse(path, headers={"Cache-Control": "public, max-age=86400",
                                           "X-Content-Type-Options": "nosniff"})


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
            "static_dir": (BASE / "static").is_dir(), "index_path": str(path) if path else None}
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
    for r in rows:  # аватарка в топе: только если админ привязал ник командой /link
        u = by_pid.get(r.get("pid"))
        r["pid"] = u["pid"] if u else ""
        r["av"] = u.get("avatar", 0) if u else 0
    return web.json_response(rows, headers=NOSTORE)


async def health(_):
    return web.Response(text="ok")


async def main():
    global BOT_USERNAME
    logging.basicConfig(level=logging.INFO)
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
        web.post("/api/queue/start", api_queue_start),
        web.post("/api/queue/cancel", api_queue_cancel),
        web.post("/api/match/cancel", api_match_cancel),
        web.post("/api/match/report", api_match_report),
        web.post("/api/match/confirm", api_match_confirm),
        web.get("/api/shot/{mid:[0-9a-f]+}/{sid:[0-9a-f]+}", api_shot_get),
        web.get("/api/avatar/{pid:[0-9a-f]+}", api_avatar_get),
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
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
