"""Rapira Faceit: Telegram-бот + сайт с топом в одном процессе.

Переменные окружения:
  BOT_TOKEN  - токен от @BotFather (обязательно)
  ADMIN_IDS  - ваши Telegram ID через запятую (кто может менять таблицу)
  PUBLIC_URL - https-адрес вашего сайта, например https://myapp.onrender.com
  PORT       - порт (хостинг обычно задаёт сам)
  DATA_FILE  - путь к файлу данных (по умолчанию data.json)
"""
import asyncio
import json
import logging
import os
import tempfile
from pathlib import Path

from aiogram import Bot, Dispatcher, Router
from aiogram.filters import Command, CommandObject
from aiogram.types import (InlineKeyboardButton, InlineKeyboardMarkup,
                           Message, WebAppInfo)
from aiohttp import web

BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
PUBLIC_URL = os.getenv("PUBLIC_URL", "").rstrip("/")
PORT = int(os.getenv("PORT", "8080"))
DATA_FILE = Path(os.getenv("DATA_FILE", "data.json"))
BASE = Path(__file__).parent
TOP_N = 100

lock = asyncio.Lock()
router = Router()


# ---------- данные ----------
def load() -> list:
    if not DATA_FILE.exists():
        return []
    try:
        return json.loads(DATA_FILE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return []


def save(data: list) -> None:
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(DATA_FILE.parent), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    os.replace(tmp, DATA_FILE)  # атомарная запись


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


# ---------- команды бота ----------
@router.message(Command("start"))
async def cmd_start(m: Message):
    text = ("Топ игроков FACEIT.\n/top - топ-10\n"
            f"Ваш Telegram ID: {m.from_user.id}")
    if is_admin(m):
        text += ("\n\nКоманды админа:\n"
                 "/elo Ник 4210 [K/D] [победы] - добавить или изменить\n"
                 "/del Ник - удалить\n"
                 "/import - заменить весь список (строки: ник ELO K/D победы)")
    kb = None
    if PUBLIC_URL.startswith("https://"):
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Открыть таблицу",
                                 web_app=WebAppInfo(url=PUBLIC_URL))]])
    await m.answer(text, reply_markup=kb)


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
        save(data)
    msg = f"Список заменён, игроков: {len(data)}"
    if bad:
        msg += f"\nПропущено строк: {len(bad)}"
    await m.answer(msg)


# ---------- сайт ----------
async def index(_):
    return web.FileResponse(BASE / "static" / "index.html")


async def api_top(_):
    async with lock:
        rows = ranked(load())
    return web.json_response(rows, headers={"Cache-Control": "no-store"})


async def health(_):
    return web.Response(text="ok")


async def main():
    logging.basicConfig(level=logging.INFO)
    if not ADMIN_IDS:
        logging.warning("ADMIN_IDS пуст: менять таблицу никто не сможет")
    app = web.Application()
    app.add_routes([web.get("/", index), web.get("/api/top", api_top),
                    web.get("/health", health)])
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()

    bot = Bot(BOT_TOKEN)
    dp = Dispatcher()
    dp.include_router(router)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
