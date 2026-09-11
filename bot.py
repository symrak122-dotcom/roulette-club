"""


ВАЖНО:
- Это ИГРОВАЯ механика с виртуальными очками, НЕ имеющими денежной стоимости
  и не привязанными к реальным платежам или подаркам Telegram.
- Никакого приёма реальных денег/подарков здесь нет и не должно быть.
- Каждая игра — честный random(), с реальным шансом как выиграть, так и
  проиграть ставку. Никаких "гарантированных" исходов.

Игры:
- 🎰 Рулетка       /roulette [ставка]
- 🎲 Кости         /dice [ставка] [1-6]  — родная Telegram-анимация кубика
- 🎯 Слоты         /slots [ставка]
- 🪙 Монетка       /coinflip [ставка] [орёл|решка]
- 🔴⚫ Чёрное/красное /blackred [ставка] [красное|чёрное]
- 🚀 Краш           /crash [ставка] затем /cashout — общий раунд с мини-приложением
- 💣 Мины           /mines [ставка] [3|5|8] — сетка 5×5, забирай выигрыш вовремя

Прочее:
- /start   — создание профиля (уникальный ID) + анимация загрузки
- /profile — просмотр своего профиля (ID, баланс, кол-во игр)
- /games   — меню всех игр
- /help    — список команд

Хранилище: SQLite (файл bot_database.db), создаётся автоматически.

Мини-приложение (index.html) синхронизировано с ботом: бот поднимает
собственный HTTP-API (см. секцию "HTTP-API для мини-приложения" ниже)
на порту из переменной окружения API_PORT (по умолчанию 8080), и
index.html обращается туда за балансом и результатами игр — так что
баланс в приложении и в боте всегда одно и то же число из одной базы.
Этот API нужно опубликовать по HTTPS-адресу (Render/Railway/свой сервер
с nginx) и указать этот адрес в константе API_BASE_URL внутри index.html.

Установка зависимостей:
    pip install -r requirements.txt

Запуск (Windows / PowerShell):
    $env:BOT_TOKEN="твой_токен_от_BotFather"
    python bot.py

Запуск (Linux / macOS):
    export BOT_TOKEN="твой_токен_от_BotFather"
    python bot.py
"""

import asyncio
import hashlib
import hmac
import json
import logging
import math
import os
import random
import re
import sqlite3
import threading
import time
import urllib.parse
from contextlib import closing
from datetime import datetime, timezone

from aiohttp import web
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, WebAppInfo
from telegram.error import BadRequest
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

# ---------------------------------------------------------------------------
# Настройки
# ---------------------------------------------------------------------------

TOKEN = os.getenv("BOT_TOKEN", "ВАШ_ТОКЕН_ЗДЕСЬ")
DB_PATH = "bot_database.db"

# Если api.telegram.org недоступен напрямую, укажи прокси, например:
#   PROXY_URL = "http://127.0.0.1:8080"
# Можно также задать через переменную окружения BOT_PROXY_URL.
PROXY_URL = os.getenv("BOT_PROXY_URL") or None

# Адрес веб-страницы мини-приложения (Telegram Mini App).
# ОБЯЗАТЕЛЬНО должен быть https:// — Telegram не открывает http:// и localhost.
# Как получить бесплатный HTTPS-адрес — см. инструкцию в конце этого файла.
# Пока не задан — кнопки мини-приложения просто не показываются, бот работает
# как раньше через обычные команды.
WEBAPP_URL = os.getenv("BOT_WEBAPP_URL") or None
# Например: WEBAPP_URL = "https://твой-юзернейм.github.io/roulette-club/"

# Порт, на котором бот поднимает свой HTTP-API для мини-приложения.
# Мини-приложение (index.html на GitHub Pages) обращается сюда, чтобы
# баланс в приложении и в самом боте всегда были одним и тем же числом
# из базы данных, а не двумя независимыми копиями.
# Этот сервер нужно сделать доступным по HTTPS-адресу (например, через
# Render/Railway/свой VPS с nginx) и указать этот адрес в index.html —
# см. константу API_BASE_URL в конце файла index.html.
# Render (и некоторые другие PaaS) сами назначают порт через переменную
# PORT и требуют, чтобы сервис слушал именно её — иначе деплой считается
# неудачным. Поэтому PORT имеет приоритет, а API_PORT — запасной вариант
# для хостингов, где порт не навязывается.
API_PORT = int(os.getenv("PORT") or os.getenv("API_PORT", "8080"))

# ID администраторов, которым разрешено создавать промокоды.
# Узнать свой Telegram ID можно у бота @userinfobot — впиши число сюда.
# Можно перечислить несколько через запятую в переменной окружения BOT_ADMIN_IDS,
# например: BOT_ADMIN_IDS="123456789,987654321"
ADMIN_IDS = {
    int(x) for x in os.getenv("BOT_ADMIN_IDS", "7222149724").split(",") if x.strip().isdigit()
}
# Либо впиши ID прямо сюда, например: ADMIN_IDS = {123456789}

STARTING_BALANCE = 100
DEFAULT_BET = 10

# --- Рулетка: (название, множитель, вес шанса) ---
ROULETTE_SECTORS = [
    ("💥 Мимо",        0.0, 55),
    ("🍒 x1.5",         1.5, 20),
    ("🍋 x2",           2.0, 12),
    ("⭐ x3",           3.0, 7),
    ("💎 x5",           5.0, 4),
    ("👑 JACKPOT x10", 10.0, 2),
]

# --- Кости: выигрыш при угадывании грани 1-6, множитель настраивается ---
DICE_WIN_MULTIPLIER = 5.0  # шанс угадать 1/6

# --- Слоты: символы барабанов и их вес (одинаковый для каждого барабана) ---
SLOT_SYMBOLS = [
    ("🍋", 24),
    ("🍒", 22),
    ("🔔", 20),
    ("⭐", 16),
    ("💎", 12),
    ("7️⃣", 6),
]
SLOT_TRIPLE_MULTIPLIER = {
    "🍋": 3, "🍒": 4, "🔔": 6, "⭐": 10, "💎": 20, "7️⃣": 50,
}
SLOT_PAIR_MULTIPLIER = 1.2

# --- Монетка: 50/50 ---
COINFLIP_WIN_MULTIPLIER = 2.0

# --- Чёрное/красное: классическая рулеточная раскладка (европейская, зеро одно) ---
# 18 красных + 18 чёрных + 1 зелёное зеро = 37 секторов.
BLACKRED_RED_COUNT = 18
BLACKRED_BLACK_COUNT = 18
BLACKRED_GREEN_COUNT = 1
BLACKRED_WIN_MULTIPLIER = 2.0

# --- Краш: множитель растёт со временем, игрок должен успеть "забрать"
# выигрыш до того, как раунд оборвётся на случайной точке. Точка обрыва
# выбирается по "корзинам" — как и в рулетке/слотах, так проще держать
# под контролем реальную частоту исходов, а не подбирать формулу вслепую.
# В большинстве случаев обрыв происходит до x2, и совсем редко долетает
# до потолка x100.
CRASH_BUCKETS = [
    # (мин.множитель, макс.множитель, вес)
    (1.00, 1.20, 35),
    (1.20, 1.50, 25),
    (1.50, 2.00, 20),
    (2.00, 3.00, 10),
    (3.00, 5.00, 5),
    (5.00, 10.00, 3),
    (10.00, 30.00, 1.5),
    (30.00, 100.00, 0.5),
]
CRASH_GROWTH_K = 0.14          # скорость роста множителя (см. current_crash_multiplier)
CRASH_WAIT_SECONDS = 5         # окно для ставок перед стартом раунда
CRASH_RESULT_PAUSE = 3         # пауза после краша перед следующим раундом
CRASH_HISTORY_LIMIT = 20
CRASH_MAX_MULTIPLIER = 100.0


def generate_crash_point() -> float:
    bucket = random.choices(CRASH_BUCKETS, weights=[b[2] for b in CRASH_BUCKETS], k=1)[0]
    lo, hi, _ = bucket
    return round(random.uniform(lo, hi), 2)


def current_crash_multiplier(elapsed: float, crash_point: float) -> float:
    """Множитель в текущий момент раунда: растёт экспоненциально с
    начала раунда и никогда не превышает точку обрыва этого раунда."""
    value = math.exp(CRASH_GROWTH_K * max(elapsed, 0))
    return round(min(value, crash_point), 2)


def seconds_to_reach(crash_point: float) -> float:
    """Через сколько секунд после старта раунда множитель дорастёт ровно
    до crash_point (момент обрыва)."""
    if crash_point <= 1.0:
        return 0.0
    return math.log(crash_point) / CRASH_GROWTH_K


# Общее состояние раунда "Краш" — единое и для Telegram-команд, и для
# API мини-приложения, чтобы оба интерфейса играли один и тот же раунд
# с одним и тем же результатом. Доступ защищён локом, т.к. бот и API
# работают в разных потоках/циклах событий.
crash_lock = threading.Lock()
crash_state = {
    "round_id": 0,
    "phase": "waiting",  # waiting | running | crashed
    "phase_started_at": time.time(),
    "crash_point": 1.0,
    "bets": {},          # telegram_id -> {"bet": int, "name": str, "cashed_out_at": float|None}
    "history": [],       # последние точки обрыва, самая новая — первая
}


def finalize_round_payout(telegram_id: int, winnings: int):
    """Начисляет выигрыш (0, если проиграл — ставка уже списана в момент
    входа в раунд) и обновляет статистику игр/рекорд, как settle()."""
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.execute(
            "UPDATE users SET balance = balance + ?, games_played = games_played + 1, "
            "best_win = CASE WHEN ? > best_win THEN ? ELSE best_win END WHERE telegram_id = ?",
            (winnings, winnings, winnings, telegram_id),
        )
        conn.commit()
        row = conn.execute(
            "SELECT balance, best_win FROM users WHERE telegram_id = ?", (telegram_id,)
        ).fetchone()
        return row[0], row[1]


def crash_snapshot():
    """Безопасный (под локом) снимок текущего состояния раунда для показа
    пользователю: фаза, текущий множитель, история, есть ли активная
    ставка. Не читает и не пишет ничего внешнего."""
    with crash_lock:
        phase = crash_state["phase"]
        elapsed = time.time() - crash_state["phase_started_at"]
        crash_point = crash_state["crash_point"]
        if phase == "running":
            mult = current_crash_multiplier(elapsed, crash_point)
        elif phase == "crashed":
            mult = crash_point
        else:
            mult = 1.0
        return {
            "phase": phase,
            "round_id": crash_state["round_id"],
            "multiplier": mult,
            "wait_remaining": max(0.0, CRASH_WAIT_SECONDS - elapsed) if phase == "waiting" else 0.0,
            "crash_point": crash_point if phase == "crashed" else None,
            "history": list(crash_state["history"]),
            "bets_snapshot": dict(crash_state["bets"]),
        }


def crash_place_bet(telegram_id: int, name: str, bet: int):
    with crash_lock:
        if crash_state["phase"] != "waiting":
            return False, "Ставки принимаются только перед стартом раунда, дождись следующего."
        if telegram_id in crash_state["bets"]:
            return False, "Ты уже поставил в этом раунде."
        crash_state["bets"][telegram_id] = {"bet": bet, "name": name, "cashed_out_at": None}
    update_balance(telegram_id, -bet)
    return True, "Ставка принята."


def crash_cash_out(telegram_id: int):
    with crash_lock:
        if crash_state["phase"] != "running":
            return False, "Раунд сейчас не идёт.", None, None
        entry = crash_state["bets"].get(telegram_id)
        if not entry:
            return False, "У тебя нет активной ставки в этом раунде.", None, None
        if entry["cashed_out_at"] is not None:
            return False, "Ты уже вывел ставку в этом раунде.", None, None
        elapsed = time.time() - crash_state["phase_started_at"]
        mult = current_crash_multiplier(elapsed, crash_state["crash_point"])
        entry["cashed_out_at"] = mult
        bet = entry["bet"]
    winnings = int(bet * mult)
    new_balance, best_win = finalize_round_payout(telegram_id, winnings)
    return True, "Выведено.", winnings, {"multiplier": mult, "balance": new_balance, "best_win": best_win, "bet": bet}


def _crash_settle_round_losses():
    """Вызывается планировщиком сразу после обрыва: те, кто не успел
    вывести ставку, её теряют (она уже списана при входе в раунд, здесь
    просто фиксируем игру в статистике)."""
    with crash_lock:
        bets = dict(crash_state["bets"])
    for telegram_id, entry in bets.items():
        if entry["cashed_out_at"] is None:
            finalize_round_payout(telegram_id, 0)


def crash_scheduler() -> None:
    """Бесконечный цикл раундов краша в отдельном потоке: ожидание ставок
    → рост множителя → обрыв → пауза → снова ожидание. Работает всегда,
    независимо от того, играет ли кто-то сейчас — так и бот, и мини-
    приложение всегда видят один и тот же текущий раунд."""
    while True:
        try:
            with crash_lock:
                crash_state["phase"] = "waiting"
                crash_state["phase_started_at"] = time.time()
                crash_state["bets"] = {}
                crash_state["round_id"] += 1
            time.sleep(CRASH_WAIT_SECONDS)

            crash_point = generate_crash_point()
            with crash_lock:
                crash_state["phase"] = "running"
                crash_state["phase_started_at"] = time.time()
                crash_state["crash_point"] = crash_point
            time.sleep(max(seconds_to_reach(crash_point), 0.0))

            with crash_lock:
                crash_state["phase"] = "crashed"
                crash_state["phase_started_at"] = time.time()
            _crash_settle_round_losses()
            with crash_lock:
                crash_state["history"].insert(0, crash_point)
                crash_state["history"] = crash_state["history"][:CRASH_HISTORY_LIMIT]
            time.sleep(CRASH_RESULT_PAUSE)
        except Exception:
            logger.exception("Ошибка в планировщике краша, продолжаем через секунду")
            time.sleep(1)


# ---------------------------------------------------------------------------
# 💣 Мины: сетка 5×5, часть клеток заминирована. За каждую безопасную
# клетку множитель растёт (честный расчёт по гипергеометрическому
# распределению — как обычно считают такие игры), в любой момент можно
# забрать выигрыш. Попал на мину — теряешь ставку. Игра ведётся в памяти
# по каждому пользователю отдельно (в отличие от краша, здесь нет общего
# раунда — своя игра у каждого).
# ---------------------------------------------------------------------------

MINES_GRID_SIZE = 25
MINES_HOUSE_EDGE = 0.97  # небольшой перевес казино, как в других играх
MINES_OPTIONS = [3, 5, 8]  # доступное количество мин на выбор игрока

mines_lock = threading.Lock()
mines_sessions = {}  # telegram_id -> {"bet","mines_count","mine_positions","revealed","active"}


def mines_multiplier(total: int, mines: int, reveals: int) -> float:
    """Честный (без перевеса) множитель для reveals открытых безопасных
    клеток — произведение гипергеометрических шансов — умноженный на
    небольшой домашний edge, как в остальных играх."""
    safe = total - mines
    mult = 1.0
    for i in range(reveals):
        mult *= (total - i) / (safe - i)
    return round(mult * MINES_HOUSE_EDGE, 2)


def mines_start(telegram_id: int, bet: int, mines_count: int):
    if mines_count not in MINES_OPTIONS:
        mines_count = MINES_OPTIONS[0]
    with mines_lock:
        existing = mines_sessions.get(telegram_id)
        if existing and existing["active"]:
            return False, "У тебя уже есть активная игра в Мины — заверши её, прежде чем начать новую."
        mine_positions = set(random.sample(range(MINES_GRID_SIZE), mines_count))
        mines_sessions[telegram_id] = {
            "bet": bet,
            "mines_count": mines_count,
            "mine_positions": mine_positions,
            "revealed": set(),
            "active": True,
        }
    update_balance(telegram_id, -bet)
    return True, "Игра началась."


def mines_reveal(telegram_id: int, index: int):
    with mines_lock:
        session = mines_sessions.get(telegram_id)
        if not session or not session["active"]:
            return False, "Нет активной игры в Мины.", None
        if not (0 <= index < MINES_GRID_SIZE):
            return False, "Некорректная клетка.", None
        if index in session["revealed"]:
            return False, "Эта клетка уже открыта.", None

        session["revealed"].add(index)
        hit_mine = index in session["mine_positions"]
        bet = session["bet"]
        mines_count = session["mines_count"]
        mine_positions = sorted(session["mine_positions"]) if hit_mine else None
        auto_clear = False
        mult = None

        if hit_mine:
            session["active"] = False
        else:
            safe_total = MINES_GRID_SIZE - mines_count
            revealed_count = len(session["revealed"])
            mult = mines_multiplier(MINES_GRID_SIZE, mines_count, revealed_count)
            if revealed_count >= safe_total:
                auto_clear = True
                session["active"] = False

    if hit_mine:
        _, best_win = finalize_round_payout(telegram_id, 0)
        updated = get_user(telegram_id)
        return True, "hit", {
            "hit": True,
            "minePositions": mine_positions,
            "balance": updated["balance"],
            "games_played": updated["games_played"],
            "best_win": updated["best_win"],
        }

    if auto_clear:
        winnings = int(bet * mult)
        new_balance, best_win = finalize_round_payout(telegram_id, winnings)
        return True, "cleared", {
            "hit": False,
            "cleared": True,
            "multiplier": mult,
            "winnings": winnings,
            "balance": new_balance,
            "best_win": best_win,
        }

    return True, "safe", {"hit": False, "cleared": False, "multiplier": mult}


def mines_cash_out(telegram_id: int):
    with mines_lock:
        session = mines_sessions.get(telegram_id)
        if not session or not session["active"]:
            return False, "Нет активной игры в Мины.", None
        if not session["revealed"]:
            return False, "Сначала открой хотя бы одну клетку.", None
        bet = session["bet"]
        mult = mines_multiplier(MINES_GRID_SIZE, session["mines_count"], len(session["revealed"]))
        mine_positions = sorted(session["mine_positions"])
        session["active"] = False

    winnings = int(bet * mult)
    new_balance, best_win = finalize_round_payout(telegram_id, winnings)
    return True, "Выведено.", {
        "multiplier": mult,
        "winnings": winnings,
        "minePositions": mine_positions,
        "balance": new_balance,
        "best_win": best_win,
    }


def mines_get_state(telegram_id: int):
    with mines_lock:
        session = mines_sessions.get(telegram_id)
        if not session:
            return None
        revealed_count = len(session["revealed"])
        mult = mines_multiplier(MINES_GRID_SIZE, session["mines_count"], revealed_count) if revealed_count else 1.0
        return {
            "active": session["active"],
            "bet": session["bet"],
            "minesCount": session["mines_count"],
            "revealed": sorted(session["revealed"]),
            "multiplier": mult,
        }


logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Безопасное редактирование сообщений
# ---------------------------------------------------------------------------

async def safe_edit(msg, text: str, parse_mode: str = None) -> None:
    """Редактирует сообщение, тихо игнорируя ошибку 'message is not modified'
    и любые другие временные сбои сети — чтобы анимация никогда не роняла
    обработчик."""
    try:
        await msg.edit_text(text, parse_mode=parse_mode)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            logger.warning("edit_text BadRequest: %s", e)
    except Exception as e:
        logger.warning("edit_text failed: %s", e)


# ---------------------------------------------------------------------------
# База данных
# ---------------------------------------------------------------------------

def init_db() -> None:
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS users (
                internal_id   INTEGER PRIMARY KEY AUTOINCREMENT,
                telegram_id   INTEGER UNIQUE NOT NULL,
                username      TEXT,
                first_name    TEXT,
                balance       INTEGER NOT NULL DEFAULT 0,
                games_played  INTEGER NOT NULL DEFAULT 0,
                created_at    TEXT NOT NULL
            )
            """
        )
        # Миграция для баз, созданных до появления бана/варнов
        existing_cols = {row[1] for row in conn.execute("PRAGMA table_info(users)")}
        if "banned" not in existing_cols:
            conn.execute("ALTER TABLE users ADD COLUMN banned INTEGER NOT NULL DEFAULT 0")
        if "ban_reason" not in existing_cols:
            conn.execute("ALTER TABLE users ADD COLUMN ban_reason TEXT")
        if "warnings" not in existing_cols:
            conn.execute("ALTER TABLE users ADD COLUMN warnings INTEGER NOT NULL DEFAULT 0")
        if "best_win" not in existing_cols:
            conn.execute("ALTER TABLE users ADD COLUMN best_win INTEGER NOT NULL DEFAULT 0")

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS promo_codes (
                code          TEXT PRIMARY KEY,
                amount        INTEGER NOT NULL,
                max_uses      INTEGER NOT NULL,
                used_count    INTEGER NOT NULL DEFAULT 0,
                created_by    INTEGER NOT NULL,
                created_at    TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS promo_redemptions (
                code          TEXT NOT NULL,
                telegram_id   INTEGER NOT NULL,
                redeemed_at   TEXT NOT NULL,
                PRIMARY KEY (code, telegram_id)
            )
            """
        )
        conn.commit()


def get_or_create_user(telegram_id: int, username: str, first_name: str) -> sqlite3.Row:
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row
        cur = conn.execute("SELECT * FROM users WHERE telegram_id = ?", (telegram_id,))
        row = cur.fetchone()
        if row:
            conn.execute(
                "UPDATE users SET username = ?, first_name = ? WHERE telegram_id = ?",
                (username, first_name, telegram_id),
            )
            conn.commit()
            return row

        conn.execute(
            """
            INSERT INTO users (telegram_id, username, first_name, balance, games_played, created_at)
            VALUES (?, ?, ?, ?, 0, ?)
            """,
            (telegram_id, username, first_name, STARTING_BALANCE, datetime.now(timezone.utc).isoformat()),
        )
        conn.commit()
        cur = conn.execute("SELECT * FROM users WHERE telegram_id = ?", (telegram_id,))
        return cur.fetchone()


def update_balance(telegram_id: int, delta: int) -> int:
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.execute(
            "UPDATE users SET balance = balance + ?, games_played = games_played + 1 WHERE telegram_id = ?",
            (delta, telegram_id),
        )
        conn.commit()
        cur = conn.execute("SELECT balance FROM users WHERE telegram_id = ?", (telegram_id,))
        return cur.fetchone()[0]


def get_user(telegram_id: int) -> sqlite3.Row:
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row
        cur = conn.execute("SELECT * FROM users WHERE telegram_id = ?", (telegram_id,))
        return cur.fetchone()


def find_user(identifier: str):
    """Ищет пользователя по telegram_id, внутреннему ID или @username."""
    identifier = identifier.strip().lstrip("@")
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row
        if identifier.isdigit():
            num = int(identifier)
            row = conn.execute("SELECT * FROM users WHERE telegram_id = ?", (num,)).fetchone()
            if row:
                return row
            row = conn.execute("SELECT * FROM users WHERE internal_id = ?", (num,)).fetchone()
            if row:
                return row
        row = conn.execute(
            "SELECT * FROM users WHERE username = ? COLLATE NOCASE", (identifier,)
        ).fetchone()
        return row


def list_all_users(limit: int = 20, offset: int = 0):
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row
        rows = conn.execute(
            "SELECT * FROM users ORDER BY internal_id ASC LIMIT ? OFFSET ?",
            (limit, offset),
        ).fetchall()
        total = conn.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        return rows, total


def get_all_user_ids() -> list:
    """Все telegram_id из базы — используется для рассылки объявлений."""
    with closing(sqlite3.connect(DB_PATH)) as conn:
        rows = conn.execute("SELECT telegram_id FROM users").fetchall()
        return [r[0] for r in rows]


def set_ban(telegram_id: int, banned: bool, reason: str = None) -> None:
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.execute(
            "UPDATE users SET banned = ?, ban_reason = ? WHERE telegram_id = ?",
            (1 if banned else 0, reason if banned else None, telegram_id),
        )
        conn.commit()


def add_warning(telegram_id: int) -> int:
    """Увеличивает счётчик предупреждений и возвращает новое значение."""
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.execute(
            "UPDATE users SET warnings = warnings + 1 WHERE telegram_id = ?",
            (telegram_id,),
        )
        conn.commit()
        cur = conn.execute("SELECT warnings FROM users WHERE telegram_id = ?", (telegram_id,))
        return cur.fetchone()[0]


def is_user_banned(telegram_id: int) -> bool:
    user = get_user(telegram_id)
    return bool(user and user["banned"])


# Автобан после этого числа предупреждений (0 — отключить автобан)
AUTO_BAN_AFTER_WARNINGS = 3


# ---------------------------------------------------------------------------
# Промокоды
# ---------------------------------------------------------------------------

def create_promo_code(code: str, amount: int, max_uses: int, created_by: int) -> bool:
    """Создаёт промокод. Возвращает False, если такой код уже существует."""
    code = code.strip().upper()
    with closing(sqlite3.connect(DB_PATH)) as conn:
        try:
            conn.execute(
                """
                INSERT INTO promo_codes (code, amount, max_uses, used_count, created_by, created_at)
                VALUES (?, ?, ?, 0, ?, ?)
                """,
                (code, amount, max_uses, created_by, datetime.now(timezone.utc).isoformat()),
            )
            conn.commit()
            return True
        except sqlite3.IntegrityError:
            return False


def get_promo_code(code: str):
    code = code.strip().upper()
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row
        cur = conn.execute("SELECT * FROM promo_codes WHERE code = ?", (code,))
        return cur.fetchone()


def redeem_promo_code(code: str, telegram_id: int):
    """
    Пытается активировать промокод для пользователя.
    Возвращает (успех: bool, сообщение: str, сумма: int).
    """
    code = code.strip().upper()
    with closing(sqlite3.connect(DB_PATH)) as conn:
        conn.row_factory = sqlite3.Row

        promo = conn.execute("SELECT * FROM promo_codes WHERE code = ?", (code,)).fetchone()
        if not promo:
            return False, "Такого промокода не существует.", 0

        if promo["used_count"] >= promo["max_uses"]:
            return False, "У этого промокода закончились активации.", 0

        already = conn.execute(
            "SELECT 1 FROM promo_redemptions WHERE code = ? AND telegram_id = ?",
            (code, telegram_id),
        ).fetchone()
        if already:
            return False, "Ты уже активировал этот промокод раньше.", 0

        # Атомарно фиксируем активацию и начисляем баланс
        conn.execute(
            "INSERT INTO promo_redemptions (code, telegram_id, redeemed_at) VALUES (?, ?, ?)",
            (code, telegram_id, datetime.now(timezone.utc).isoformat()),
        )
        conn.execute(
            "UPDATE promo_codes SET used_count = used_count + 1 WHERE code = ?",
            (code,),
        )
        conn.execute(
            "UPDATE users SET balance = balance + ? WHERE telegram_id = ?",
            (promo["amount"], telegram_id),
        )
        conn.commit()
        return True, "Промокод активирован!", promo["amount"]


# ---------------------------------------------------------------------------
# Общие утилиты для игр
# ---------------------------------------------------------------------------

def parse_bet(context: ContextTypes.DEFAULT_TYPE) -> int:
    if context.args:
        try:
            return int(context.args[0])
        except ValueError:
            return DEFAULT_BET
    return DEFAULT_BET


async def check_bet(update: Update, user: sqlite3.Row, bet: int) -> bool:
    if bet <= 0:
        await update.message.reply_text("Ставка должна быть положительным числом.")
        return False
    if user["balance"] < bet:
        await update.message.reply_text(
            f"Недостаточно очков для ставки {bet}. Твой баланс: {user['balance']}."
        )
        return False
    return True


async def check_not_banned(update: Update, telegram_id: int) -> bool:
    """Возвращает True, если можно продолжать. Если пользователь забанен —
    сообщает причину и возвращает False."""
    if is_user_banned(telegram_id):
        user = get_user(telegram_id)
        reason = user["ban_reason"] or "без указания причины"
        await update.message.reply_text(
            f"⛔ Ты заблокирован в этом боте.\nПричина: {reason}"
        )
        return False
    return True


def settle(telegram_id: int, bet: int, winnings: int):
    delta = winnings - bet
    new_balance = update_balance(telegram_id, delta)
    if winnings > 0:
        with closing(sqlite3.connect(DB_PATH)) as conn:
            conn.execute(
                "UPDATE users SET best_win = ? WHERE telegram_id = ? AND best_win < ?",
                (winnings, telegram_id, winnings),
            )
            conn.commit()
    return new_balance, delta


# ---------------------------------------------------------------------------
# /start — создание профиля + анимация загрузки
# ---------------------------------------------------------------------------

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")

    frames = [
        "⏳ Загрузка········ 10%",
        "⏳ Загрузка▓········ 25%",
        "⏳ Загрузка▓▓▓······· 45%",
        "⏳ Загрузка▓▓▓▓▓····· 65%",
        "⏳ Загрузка▓▓▓▓▓▓▓··· 85%",
        "✅ Загрузка▓▓▓▓▓▓▓▓▓▓ 100%",
    ]
    msg = await update.message.reply_text(frames[0])
    for frame in frames[1:]:
        await asyncio.sleep(0.35)
        await safe_edit(msg, frame)

    await asyncio.sleep(0.3)
    await safe_edit(
        msg,
        f"Добро пожаловать, {tg_user.first_name}!\n\n"
        f"🆔 Твой ID в системе: <b>{user['internal_id']}</b>\n"
        f"💰 Баланс: <b>{user['balance']}</b> очков\n\n"
        "Набери /games, чтобы увидеть все игры, или /help для списка команд.",
        parse_mode="HTML",
    )
    await update.message.reply_text("Меню игр:", reply_markup=games_keyboard())


def games_keyboard() -> InlineKeyboardMarkup:
    keyboard = []

    if WEBAPP_URL:
        keyboard.append([
            InlineKeyboardButton("📱 Открыть мини-приложение", web_app=WebAppInfo(url=WEBAPP_URL))
        ])

    keyboard += [
        [InlineKeyboardButton("👤 Профиль", callback_data="profile")],
        [
            InlineKeyboardButton("🎰 Рулетка", callback_data="how_roulette"),
            InlineKeyboardButton("🎲 Кости", callback_data="how_dice"),
        ],
        [
            InlineKeyboardButton("🎯 Слоты", callback_data="how_slots"),
            InlineKeyboardButton("🪙 Монетка", callback_data="how_coinflip"),
        ],
        [
            InlineKeyboardButton("🔴⚫ Чёрное/красное", callback_data="how_blackred"),
        ],
    ]
    return InlineKeyboardMarkup(keyboard)


async def games_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        "🎮 <b>Игры казино</b>\n\nВыбери игру:",
        parse_mode="HTML",
        reply_markup=games_keyboard(),
    )


# ---------------------------------------------------------------------------
# /profile
# ---------------------------------------------------------------------------

async def profile(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")

    text = (
        f"👤 <b>Профиль</b>\n\n"
        f"🆔 ID: <b>{user['internal_id']}</b>\n"
        f"Имя: {user['first_name']}\n"
        f"💰 Баланс: <b>{user['balance']}</b> очков\n"
        f"🎮 Игр сыграно: {user['games_played']}\n"
        f"📅 Регистрация: {user['created_at'][:10]}"
    )

    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.message.reply_text(text, parse_mode="HTML")
    else:
        await update.message.reply_text(text, parse_mode="HTML")


# ---------------------------------------------------------------------------
# /help
# ---------------------------------------------------------------------------

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    text = (
        "Доступные команды:\n"
        "/start — создать профиль / открыть меню\n"
        "/profile — посмотреть свой профиль\n"
        "/games — меню всех игр\n"
        "/app — открыть мини-приложение (веб-интерфейс)\n\n"
        f"🎰 /roulette [ставка] — рулетка (по умолч. {DEFAULT_BET})\n"
        f"🎲 /dice [ставка] [1-6] — родная Telegram-анимация кубика, выигрыш x{DICE_WIN_MULTIPLIER}\n"
        f"🎯 /slots [ставка] — три барабана, совпадения дают выигрыш\n"
        f"🪙 /coinflip [ставка] [орёл|решка] — выигрыш x{COINFLIP_WIN_MULTIPLIER}\n"
        f"🔴⚫ /blackred [ставка] [красное|чёрное] — выигрыш x{BLACKRED_WIN_MULTIPLIER}\n"
        f"🚀 /crash [ставка], затем /cashout — множитель растёт, успей вывести до обрыва (макс. x{CRASH_MAX_MULTIPLIER:.0f})\n"
        f"💣 /mines [ставка] [3|5|8] — сетка 5×5, открывай клетки и забирай выигрыш вовремя\n\n"
        "🎟️ /promo КОД — активировать промокод\n"
        "📩 /support текст — написать в поддержку (ответят прямо тут)\n\n"
        "ℹ️ Валюта в боте виртуальная, не имеет денежной ценности.\n"
        "В каждой игре есть реальный шанс проиграть ставку."
    )
    if tg_user.id in ADMIN_IDS:
        text += (
            "\n\n🛡️ <b>Админ-команды:</b>\n"
            "/users [страница] — список всех пользователей\n"
            "/userinfo ID_или_@username — подробная информация\n"
            "/ban ID_или_@username [причина] — заблокировать\n"
            "/unban ID_или_@username — снять блокировку\n"
            "/warn ID_или_@username [причина] — выдать предупреждение\n"
            "/createpromo КОД СУММА [макс_активаций] — создать промокод\n"
            "/reply ID текст — ответить в поддержку (или просто Reply на пересланное сообщение)\n"
            "/broadcast текст — объявление всем пользователям бота"
        )
    await update.message.reply_text(text, parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🎰 Рулетка (символьная, с анимацией через редактирование сообщения)
# ---------------------------------------------------------------------------

def spin_roulette():
    weights = [s[2] for s in ROULETTE_SECTORS]
    return random.choices(ROULETTE_SECTORS, weights=weights, k=1)[0]


def three_reel_symbols(win_symbol: str, pool: list):
    """Возвращает (список из 3 символов для барабана, индекс настоящего
    результата — теперь всегда 1, т.е. по центру). По бокам — случайные,
    но разные между собой символы из того же набора (для наглядности
    вроде «алмаз, вишня, мимо» вместо трёх одинаковых). Настоящий
    результат всегда в середине, как в классической рулетке/слоте, где
    смотрят именно на центральную линию."""
    others_pool = [s for s in pool if s != win_symbol]
    random.shuffle(others_pool)
    left = others_pool[0] if len(others_pool) > 0 else win_symbol
    right = others_pool[1] if len(others_pool) > 1 else win_symbol
    return [left, win_symbol, right], 1


async def roulette(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return
    bet = parse_bet(context)
    if not await check_bet(update, user, bet):
        return

    result_name, multiplier, _ = spin_roulette()
    reel_symbols = [s[0].split()[0] for s in ROULETTE_SECTORS]
    msg = await update.message.reply_text(f"🎰 Ставка: {bet}\n\n[ 🎲 крутим... ]")

    spins = 12
    for i in range(spins):
        delay = 0.08 + (i / spins) * 0.25
        a, b, c = random.sample(reel_symbols, k=min(3, len(reel_symbols)))
        await asyncio.sleep(delay)
        await safe_edit(msg, f"🎰 Ставка: {bet}\n\n[ {a} {b} {c} ]")

    win_symbol = result_name.split()[0]
    final_symbols, _ = three_reel_symbols(win_symbol, reel_symbols)
    final_a, final_b, final_c = final_symbols
    await asyncio.sleep(0.4)
    await safe_edit(msg, f"🎰 Ставка: {bet}\n\n[ {final_a} {final_b} {final_c} ]")

    winnings = int(bet * multiplier)
    new_balance, delta = settle(tg_user.id, bet, winnings)

    if multiplier == 0:
        outcome_text = f"😔 <b>{result_name}</b>\nТы проиграл {bet} очков."
    else:
        outcome_text = (
            f"🎉 <b>{result_name}</b>\n"
            f"Выигрыш: +{winnings} очков (ставка ×{multiplier})\n"
            f"Чистая прибыль: {'+' if delta >= 0 else ''}{delta}"
        )

    await asyncio.sleep(0.3)
    await safe_edit(msg, f"{outcome_text}\n\n💰 Новый баланс: <b>{new_balance}</b>", parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🎲 Кости — РОДНАЯ Telegram-анимация через send_dice
# ---------------------------------------------------------------------------
# Telegram сам присылает анимированный кубик (🎲) и сразу знает исход —
# пользователь видит настоящую анимацию броска, как в обычном чате, а не
# текстовую имитацию. Значение (1-6) приходит в message.dice.value.

async def dice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    bet = DEFAULT_BET
    guess = None
    if context.args:
        try:
            bet = int(context.args[0])
        except ValueError:
            bet = DEFAULT_BET
        if len(context.args) > 1:
            try:
                g = int(context.args[1])
                if 1 <= g <= 6:
                    guess = g
            except ValueError:
                guess = None

    if not await check_bet(update, user, bet):
        return

    if guess is None:
        guess = random.randint(1, 6)
        await update.message.reply_text(
            f"Ты не указал число — за тебя загадано: {guess}\n"
            f"(в следующий раз: /dice {bet} <1-6>)"
        )

    await update.message.reply_text(f"🎲 Ставка: {bet} | Твоё число: {guess}\nБросаем кубик...")

    # Отправляем настоящий анимированный кубик Telegram
    dice_msg = await context.bot.send_dice(chat_id=update.effective_chat.id, emoji="🎲")
    result = dice_msg.dice.value  # 1..6, определяется сервером Telegram

    # Ждём, пока анимация в клиенте пользователя полностью доиграет (~4 сек)
    await asyncio.sleep(4.0)

    win = result == guess
    winnings = int(bet * DICE_WIN_MULTIPLIER) if win else 0
    new_balance, delta = settle(tg_user.id, bet, winnings)

    if win:
        outcome = f"🎉 Угадал! Выпало {result}.\nВыигрыш: +{winnings} (x{DICE_WIN_MULTIPLIER})"
    else:
        outcome = f"😔 Не угадал. Выпало {result}, ты ставил на {guess}.\nПроигрыш: -{bet}"

    await update.message.reply_text(f"{outcome}\n\n💰 Новый баланс: <b>{new_balance}</b>", parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🎯 Слоты — три барабана (баг с 400 Bad Request исправлен через safe_edit)
# ---------------------------------------------------------------------------

def spin_slot_reel():
    symbols = [s[0] for s in SLOT_SYMBOLS]
    weights = [s[1] for s in SLOT_SYMBOLS]
    return random.choices(symbols, weights=weights, k=1)[0]


async def slots(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return
    bet = parse_bet(context)
    if not await check_bet(update, user, bet):
        return

    msg = await update.message.reply_text(f"🎯 Ставка: {bet}\n\n[ 🎰 | 🎰 | 🎰 ]")

    all_symbols = [s[0] for s in SLOT_SYMBOLS]
    spins = 14
    for i in range(spins):
        delay = 0.06 + (i / spins) * 0.2
        row = [random.choice(all_symbols) for _ in range(3)]
        await asyncio.sleep(delay)
        await safe_edit(msg, f"🎯 Ставка: {bet}\n\n[ {row[0]} | {row[1]} | {row[2]} ]")

    final = [spin_slot_reel() for _ in range(3)]
    await asyncio.sleep(0.4)
    await safe_edit(msg, f"🎯 Ставка: {bet}\n\n[ {final[0]} | {final[1]} | {final[2]} ]")

    if final[0] == final[1] == final[2]:
        mult = SLOT_TRIPLE_MULTIPLIER.get(final[0], 3)
        winnings = int(bet * mult)
        outcome = f"👑 ТРИ ОДИНАКОВЫХ {final[0]}!\nВыигрыш: +{winnings} (x{mult})"
    elif final[0] == final[1] or final[1] == final[2] or final[0] == final[2]:
        winnings = int(bet * SLOT_PAIR_MULTIPLIER)
        outcome = f"🙂 Пара совпала.\nВыигрыш: +{winnings} (x{SLOT_PAIR_MULTIPLIER})"
    else:
        winnings = 0
        outcome = f"😔 Ничего не совпало.\nПроигрыш: -{bet}"

    new_balance, delta = settle(tg_user.id, bet, winnings)
    await asyncio.sleep(0.3)
    await safe_edit(msg, f"{outcome}\n\n💰 Новый баланс: <b>{new_balance}</b>", parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🪙 Монетка
# ---------------------------------------------------------------------------

async def coinflip(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    bet = DEFAULT_BET
    choice = None
    if context.args:
        try:
            bet = int(context.args[0])
        except ValueError:
            bet = DEFAULT_BET
        if len(context.args) > 1:
            arg = context.args[1].lower()
            if arg in ("орёл", "орел", "heads", "о"):
                choice = "орёл"
            elif arg in ("решка", "tails", "р"):
                choice = "решка"

    if not await check_bet(update, user, bet):
        return

    if choice is None:
        choice = random.choice(["орёл", "решка"])
        await update.message.reply_text(
            f"Не указал сторону — за тебя выбрано: {choice}\n"
            f"(в следующий раз: /coinflip {bet} орёл|решка)"
        )

    msg = await update.message.reply_text(f"🪙 Ставка: {bet} | Твой выбор: {choice}\n\n[ 🪙 подбрасываем... ]")

    frames = ["🪙", "◐", "🪙", "◐", "🪙"]
    for f in frames:
        await asyncio.sleep(0.18)
        await safe_edit(msg, f"🪙 Ставка: {bet} | Твой выбор: {choice}\n\n[ {f} ]")

    result = random.choice(["орёл", "решка"])
    win = result == choice
    winnings = int(bet * COINFLIP_WIN_MULTIPLIER) if win else 0
    new_balance, delta = settle(tg_user.id, bet, winnings)

    symbol = "🦅" if result == "орёл" else "🔵"
    await asyncio.sleep(0.3)
    if win:
        outcome = f"{symbol} Выпало: {result}!\n🎉 Угадал! Выигрыш: +{winnings} (x{COINFLIP_WIN_MULTIPLIER})"
    else:
        outcome = f"{symbol} Выпало: {result}.\n😔 Не угадал. Проигрыш: -{bet}"

    await safe_edit(msg, f"{outcome}\n\n💰 Новый баланс: <b>{new_balance}</b>", parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🔴⚫ Чёрное/красное — классическая раскладка рулетки (18/18/1 зеро)
# ---------------------------------------------------------------------------

def spin_blackred():
    """Возвращает 'red', 'black' или 'green' с весами как в настоящей рулетке."""
    pool = (
        ["red"] * BLACKRED_RED_COUNT
        + ["black"] * BLACKRED_BLACK_COUNT
        + ["green"] * BLACKRED_GREEN_COUNT
    )
    return random.choice(pool)


async def blackred(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    bet = DEFAULT_BET
    choice = None
    if context.args:
        try:
            bet = int(context.args[0])
        except ValueError:
            bet = DEFAULT_BET
        if len(context.args) > 1:
            arg = context.args[1].lower()
            if arg in ("красное", "красный", "red", "к"):
                choice = "red"
            elif arg in ("чёрное", "черное", "чёрный", "черный", "black", "ч"):
                choice = "black"

    if not await check_bet(update, user, bet):
        return

    if choice is None:
        choice = random.choice(["red", "black"])
        human = "красное" if choice == "red" else "чёрное"
        await update.message.reply_text(
            f"Не указал цвет — за тебя выбрано: {human}\n"
            f"(в следующий раз: /blackred {bet} красное|чёрное)"
        )

    choice_label = "🔴 Красное" if choice == "red" else "⚫ Чёрное"
    msg = await update.message.reply_text(f"{choice_label} | Ставка: {bet}\n\n[ 🎡 крутим... ]")

    colors_cycle = ["🔴", "⚫", "🔴", "⚫", "🟢", "🔴", "⚫"]
    spins = 14
    for i in range(spins):
        delay = 0.07 + (i / spins) * 0.22
        current = random.choice(colors_cycle)
        await asyncio.sleep(delay)
        await safe_edit(msg, f"{choice_label} | Ставка: {bet}\n\n[ {current} ]")

    result = spin_blackred()
    result_symbol = {"red": "🔴", "black": "⚫", "green": "🟢"}[result]
    result_label = {"red": "Красное", "black": "Чёрное", "green": "Зеро"}[result]

    await asyncio.sleep(0.4)
    await safe_edit(msg, f"{choice_label} | Ставка: {bet}\n\n[ {result_symbol} {result_label} ]")

    win = result == choice
    winnings = int(bet * BLACKRED_WIN_MULTIPLIER) if win else 0
    new_balance, delta = settle(tg_user.id, bet, winnings)

    if win:
        outcome = f"🎉 Выпало {result_symbol} {result_label}!\nВыигрыш: +{winnings} (x{BLACKRED_WIN_MULTIPLIER})"
    elif result == "green":
        outcome = f"🟢 Выпало зеро — банк забирает казино.\nПроигрыш: -{bet}"
    else:
        outcome = f"😔 Выпало {result_symbol} {result_label}, ты ставил на {choice_label.split()[1]}.\nПроигрыш: -{bet}"

    await asyncio.sleep(0.2)
    await safe_edit(msg, f"{outcome}\n\n💰 Новый баланс: <b>{new_balance}</b>", parse_mode="HTML")


# ---------------------------------------------------------------------------
# 🚀 Краш — общий раунд для бота и мини-приложения (см. crash_scheduler)
# ---------------------------------------------------------------------------

async def crash_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/crash СТАВКА — поставить в текущем раунде краша. Раунд общий с
    мини-приложением: поставить можно тут, а вывести — хоть в приложении,
    и наоборот. Дальше используй /cashout, чтобы забрать выигрыш до того,
    как раунд оборвётся."""
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    bet = parse_bet(context)
    if not await check_bet(update, user, bet):
        return

    ok, message = crash_place_bet(tg_user.id, tg_user.first_name or "Игрок", bet)
    if not ok:
        await update.message.reply_text(f"⛔ {message}")
        return

    await update.message.reply_text(
        f"🚀 Ставка {bet} принята в текущем раунде краша.\n"
        f"Как только раунд начнётся, множитель будет расти — используй /cashout, "
        f"чтобы забрать выигрыш до обрыва. Не успеешь — ставка сгорает."
    )


async def cashout_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/cashout — забрать выигрыш по текущему множителю в игре Краш."""
    tg_user = update.effective_user
    if not await check_not_banned(update, tg_user.id):
        return

    ok, message, winnings, extra = crash_cash_out(tg_user.id)
    if not ok:
        await update.message.reply_text(f"⛔ {message}")
        return

    await update.message.reply_text(
        f"💸 Выведено на x{extra['multiplier']}!\n"
        f"Выигрыш: +{winnings} (ставка {extra['bet']})\n"
        f"💰 Новый баланс: {extra['balance']}"
    )


# ---------------------------------------------------------------------------
# 💣 Мины — игровое поле через inline-кнопки прямо в чате
# ---------------------------------------------------------------------------

def build_mines_keyboard(revealed, mines=None, hit_index=None, disabled=False):
    mines_set = set(mines or [])
    revealed_set = set(revealed or [])
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx == hit_index:
                label = "💥"
            elif disabled and idx in mines_set:
                label = "💣"
            elif idx in revealed_set:
                label = "✅"
            else:
                label = "⬜"
            cb = "mnoop" if (disabled or idx in revealed_set) else f"mn:{idx}"
            row.append(InlineKeyboardButton(label, callback_data=cb))
        rows.append(row)
    if not disabled:
        rows.append([InlineKeyboardButton("💰 Забрать", callback_data="mncashout")])
    return InlineKeyboardMarkup(rows)


async def mines_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/mines СТАВКА [мин: 3|5|8] — начать игру в Мины прямо в чате."""
    tg_user = update.effective_user
    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    bet = parse_bet(context)
    if not await check_bet(update, user, bet):
        return

    mines_count = MINES_OPTIONS[0]
    if len(context.args) > 1:
        try:
            requested = int(context.args[1])
            if requested in MINES_OPTIONS:
                mines_count = requested
        except ValueError:
            pass

    ok, message = mines_start(tg_user.id, bet, mines_count)
    if not ok:
        await update.message.reply_text(f"⛔ {message}")
        return

    await update.message.reply_text(
        f"💣 Мины — ставка {bet}, мин на поле: {mines_count} из {MINES_GRID_SIZE}\n"
        f"Открывай безопасные клетки — множитель растёт с каждой. "
        f"В любой момент жми «💰 Забрать», чтобы не рисковать дальше.",
        reply_markup=build_mines_keyboard(revealed=[]),
    )


# ---------------------------------------------------------------------------
# 🌐 HTTP-API для мини-приложения (index.html)
# ---------------------------------------------------------------------------
# Мини-приложение больше не считает результаты игр само в браузере — оно
# спрашивает у этого API, а API использует ТУ ЖЕ базу данных и ТЕ ЖЕ
# функции (spin_roulette, spin_slot_reel, settle и т.д.), что и команды
# бота. Поэтому баланс в приложении и в боте — гарантированно одно и то
# же число, а не два независимых счётчика.
#
# Подлинность запроса проверяется через initData, которую Telegram
# WebApp кладёт в window.Telegram.WebApp.initData — это подписанная
# HMAC-подписью строка, поддельную сфабриковать нельзя, не зная токен
# бота. Так что баланс нельзя "накрутить" из консоли браузера.

def validate_init_data(init_data: str, bot_token: str, max_age_seconds: int = 86400):
    """Проверяет подпись initData, присланной Telegram WebApp.
    Возвращает словарь полей, если подпись верна и данные не устарели,
    иначе None. См. https://core.telegram.org/bots/webapps#validating-data-received-via-the-web-app
    """
    if not init_data:
        return None
    try:
        pairs = urllib.parse.parse_qsl(init_data, strict_parsing=True)
    except ValueError:
        return None
    data = dict(pairs)
    received_hash = data.pop("hash", None)
    if not received_hash:
        return None

    check_string = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
    secret_key = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
    computed_hash = hmac.new(secret_key, check_string.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(computed_hash, received_hash):
        return None

    auth_date = data.get("auth_date")
    if auth_date:
        try:
            if datetime.now(timezone.utc).timestamp() - int(auth_date) > max_age_seconds:
                return None
        except ValueError:
            pass
    return data


def _cors_headers():
    return {
        "Access-Control-Allow-Origin": "*",
        "Access-Control-Allow-Headers": "Content-Type",
        "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
    }


async def _handle_options(request):
    return web.Response(headers=_cors_headers())


def _auth_telegram_user(body: dict):
    """Проверяет initData из тела запроса и возвращает объект user Telegram
    (dict с id/username/first_name), либо None, если подпись неверна."""
    init_data = body.get("initData") or ""
    parsed = validate_init_data(init_data, TOKEN)
    if not parsed:
        return None
    user_raw = parsed.get("user")
    if not user_raw:
        return None
    try:
        return json.loads(user_raw)
    except (ValueError, TypeError):
        return None


async def api_state(request):
    """POST /api/state — текущее состояние профиля (баланс, игры, рекорд)."""
    try:
        body = await request.json()
    except Exception:
        body = {}

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    user = get_or_create_user(tg_user["id"], tg_user.get("username") or "", tg_user.get("first_name") or "")
    if user["banned"]:
        return web.json_response(
            {"error": "banned", "reason": user["ban_reason"] or "без указания причины"},
            status=403,
            headers=_cors_headers(),
        )

    return web.json_response(
        {
            "internal_id": user["internal_id"],
            "name": tg_user.get("first_name") or user["first_name"] or "Игрок",
            "balance": user["balance"],
            "games_played": user["games_played"],
            "best_win": user["best_win"],
        },
        headers=_cors_headers(),
    )


async def api_play(request):
    """POST /api/play — сыграть раунд одной из игр. Тело запроса:
    { initData, game: "roulette"|"dice"|"slots"|"coinflip"|"blackred",
      bet: число, guess?: 1-6, choice?: "орёл"|"решка"|"red"|"black" }
    Вся логика — те же функции, что использует бот (spin_roulette и т.д.),
    так что шансы совпадают 1-в-1 с командами /roulette, /dice и т.д."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    telegram_id = tg_user["id"]
    user = get_or_create_user(telegram_id, tg_user.get("username") or "", tg_user.get("first_name") or "")
    if user["banned"]:
        return web.json_response(
            {"error": "banned", "reason": user["ban_reason"] or "без указания причины"},
            status=403,
            headers=_cors_headers(),
        )

    game = body.get("game")
    try:
        bet = int(body.get("bet"))
    except (TypeError, ValueError):
        return web.json_response({"error": "invalid_bet"}, status=400, headers=_cors_headers())

    if bet <= 0:
        return web.json_response({"error": "invalid_bet"}, status=400, headers=_cors_headers())
    if bet > user["balance"]:
        return web.json_response({"error": "insufficient_balance"}, status=400, headers=_cors_headers())

    if game == "roulette":
        result_name, multiplier, _ = spin_roulette()
        winnings = int(bet * multiplier)
        win_symbol = result_name.split()[0]
        reel_pool = [s[0].split()[0] for s in ROULETTE_SECTORS]
        reels, result_index = three_reel_symbols(win_symbol, reel_pool)
        payload = {"resultName": result_name, "multiplier": multiplier, "reels": reels, "resultIndex": result_index}

    elif game == "dice":
        try:
            guess = int(body.get("guess"))
            if not (1 <= guess <= 6):
                raise ValueError
        except (TypeError, ValueError):
            guess = random.randint(1, 6)
        roll = random.randint(1, 6)
        win = roll == guess
        winnings = int(bet * DICE_WIN_MULTIPLIER) if win else 0
        payload = {"roll": roll, "guess": guess, "win": win}

    elif game == "slots":
        final = [spin_slot_reel() for _ in range(3)]
        if final[0] == final[1] == final[2]:
            mult = SLOT_TRIPLE_MULTIPLIER.get(final[0], 3)
            winnings = int(bet * mult)
        elif final[0] == final[1] or final[1] == final[2] or final[0] == final[2]:
            winnings = int(bet * SLOT_PAIR_MULTIPLIER)
        else:
            winnings = 0
        payload = {"reels": final}

    elif game == "coinflip":
        choice = body.get("choice")
        if choice not in ("орёл", "решка"):
            choice = random.choice(["орёл", "решка"])
        result = random.choice(["орёл", "решка"])
        win = result == choice
        winnings = int(bet * COINFLIP_WIN_MULTIPLIER) if win else 0
        payload = {"result": result, "choice": choice, "win": win}

    elif game == "blackred":
        choice = body.get("choice")
        if choice not in ("red", "black"):
            choice = random.choice(["red", "black"])
        result = spin_blackred()
        win = result == choice
        winnings = int(bet * BLACKRED_WIN_MULTIPLIER) if win else 0
        payload = {"result": result, "choice": choice, "win": win}

    else:
        return web.json_response({"error": "unknown_game"}, status=400, headers=_cors_headers())

    new_balance, delta = settle(telegram_id, bet, winnings)
    updated = get_user(telegram_id)
    payload.update(
        {
            "bet": bet,
            "winnings": winnings,
            "delta": delta,
            "balance": new_balance,
            "games_played": updated["games_played"],
            "best_win": updated["best_win"],
        }
    )
    return web.json_response(payload, headers=_cors_headers())


async def api_promo(request):
    """POST /api/promo — активировать промокод из мини-приложения.
    Тело: { initData, code }. Использует ТУ ЖЕ логику (redeem_promo_code),
    что и команда /promo в самом боте, так что код нельзя активировать
    дважды, даже если один раз это сделали в чате, а второй — в приложении."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    telegram_id = tg_user["id"]
    user = get_or_create_user(telegram_id, tg_user.get("username") or "", tg_user.get("first_name") or "")
    if user["banned"]:
        return web.json_response(
            {"error": "banned", "reason": user["ban_reason"] or "без указания причины"},
            status=403,
            headers=_cors_headers(),
        )

    code = (body.get("code") or "").strip()
    if not code:
        return web.json_response({"error": "empty_code"}, status=400, headers=_cors_headers())

    success, message, amount = redeem_promo_code(code, telegram_id)
    updated = get_user(telegram_id)
    return web.json_response(
        {
            "success": success,
            "message": message,
            "amount": amount,
            "balance": updated["balance"],
            "games_played": updated["games_played"],
            "best_win": updated["best_win"],
        },
        headers=_cors_headers(),
    )


async def api_crash_state(request):
    """POST /api/crash/state — текущее состояние раунда краша: фаза,
    множитель, история прошлых обрывов, и есть ли у пользователя ставка
    в этом раунде. Не требует авторизации для самого раунда (он общий
    для всех), но чтобы узнать личную ставку — нужен initData."""
    try:
        body = await request.json()
    except Exception:
        body = {}

    snap = crash_snapshot()
    my_bet = None
    tg_user = _auth_telegram_user(body)
    if tg_user:
        entry = snap["bets_snapshot"].get(tg_user["id"])
        if entry:
            my_bet = {"bet": entry["bet"], "cashedOutAt": entry["cashed_out_at"]}

    return web.json_response(
        {
            "phase": snap["phase"],
            "roundId": snap["round_id"],
            "multiplier": snap["multiplier"],
            "waitRemaining": snap["wait_remaining"],
            "crashPoint": snap["crash_point"],
            "history": snap["history"],
            "myBet": my_bet,
        },
        headers=_cors_headers(),
    )


async def api_crash_bet(request):
    """POST /api/crash/bet — поставить в текущем (ожидающем) раунде краша."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    telegram_id = tg_user["id"]
    user = get_or_create_user(telegram_id, tg_user.get("username") or "", tg_user.get("first_name") or "")
    if user["banned"]:
        return web.json_response(
            {"error": "banned", "reason": user["ban_reason"] or "без указания причины"},
            status=403,
            headers=_cors_headers(),
        )

    try:
        bet = int(body.get("bet"))
    except (TypeError, ValueError):
        return web.json_response({"error": "invalid_bet"}, status=400, headers=_cors_headers())
    if bet <= 0:
        return web.json_response({"error": "invalid_bet"}, status=400, headers=_cors_headers())
    if bet > user["balance"]:
        return web.json_response({"error": "insufficient_balance"}, status=400, headers=_cors_headers())

    name = tg_user.get("first_name") or user["first_name"] or "Игрок"
    ok, message = crash_place_bet(telegram_id, name, bet)
    if not ok:
        return web.json_response({"error": "bet_rejected", "message": message}, status=400, headers=_cors_headers())

    updated = get_user(telegram_id)
    return web.json_response(
        {"success": True, "balance": updated["balance"], "games_played": updated["games_played"], "best_win": updated["best_win"]},
        headers=_cors_headers(),
    )


async def api_crash_cashout(request):
    """POST /api/crash/cashout — забрать выигрыш по текущему множителю,
    пока раунд ещё не оборвался."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    ok, message, winnings, extra = crash_cash_out(tg_user["id"])
    if not ok:
        return web.json_response({"error": "cashout_rejected", "message": message}, status=400, headers=_cors_headers())

    updated = get_user(tg_user["id"])
    return web.json_response(
        {
            "success": True,
            "winnings": winnings,
            "multiplier": extra["multiplier"],
            "balance": extra["balance"],
            "best_win": extra["best_win"],
            "games_played": updated["games_played"],
        },
        headers=_cors_headers(),
    )


async def api_mines_state(request):
    """POST /api/mines/state — текущая активная игра в Мины (если есть)."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    snap = mines_get_state(tg_user["id"])
    return web.json_response({"session": snap}, headers=_cors_headers())


async def api_mines_start(request):
    """POST /api/mines/start — начать новую игру в Мины."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    telegram_id = tg_user["id"]
    user = get_or_create_user(telegram_id, tg_user.get("username") or "", tg_user.get("first_name") or "")
    if user["banned"]:
        return web.json_response(
            {"error": "banned", "reason": user["ban_reason"] or "без указания причины"},
            status=403, headers=_cors_headers(),
        )

    try:
        bet = int(body.get("bet"))
        mines_count = int(body.get("minesCount"))
    except (TypeError, ValueError):
        return web.json_response({"error": "invalid_input"}, status=400, headers=_cors_headers())
    if bet <= 0:
        return web.json_response({"error": "invalid_bet"}, status=400, headers=_cors_headers())
    if bet > user["balance"]:
        return web.json_response({"error": "insufficient_balance"}, status=400, headers=_cors_headers())

    ok, message = mines_start(telegram_id, bet, mines_count)
    if not ok:
        return web.json_response({"error": "start_rejected", "message": message}, status=400, headers=_cors_headers())

    updated = get_user(telegram_id)
    return web.json_response(
        {"success": True, "balance": updated["balance"], "games_played": updated["games_played"], "best_win": updated["best_win"]},
        headers=_cors_headers(),
    )


async def api_mines_reveal(request):
    """POST /api/mines/reveal — открыть клетку {initData, index}."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    try:
        index = int(body.get("index"))
    except (TypeError, ValueError):
        return web.json_response({"error": "invalid_index"}, status=400, headers=_cors_headers())

    ok, kind, data = mines_reveal(tg_user["id"], index)
    if not ok:
        return web.json_response({"error": "reveal_rejected", "message": kind}, status=400, headers=_cors_headers())

    data["kind"] = kind
    return web.json_response(data, headers=_cors_headers())


async def api_mines_cashout(request):
    """POST /api/mines/cashout — забрать текущий выигрыш в Минах."""
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad_request"}, status=400, headers=_cors_headers())

    tg_user = _auth_telegram_user(body)
    if not tg_user:
        return web.json_response({"error": "unauthorized"}, status=401, headers=_cors_headers())

    ok, message, data = mines_cash_out(tg_user["id"])
    if not ok:
        return web.json_response({"error": "cashout_rejected", "message": message}, status=400, headers=_cors_headers())

    data["success"] = True
    return web.json_response(data, headers=_cors_headers())


def build_api_app() -> web.Application:
    app = web.Application()
    app.router.add_post("/api/state", api_state)
    app.router.add_post("/api/play", api_play)
    app.router.add_post("/api/promo", api_promo)
    app.router.add_post("/api/crash/state", api_crash_state)
    app.router.add_post("/api/crash/bet", api_crash_bet)
    app.router.add_post("/api/crash/cashout", api_crash_cashout)
    app.router.add_post("/api/mines/state", api_mines_state)
    app.router.add_post("/api/mines/start", api_mines_start)
    app.router.add_post("/api/mines/reveal", api_mines_reveal)
    app.router.add_post("/api/mines/cashout", api_mines_cashout)
    app.router.add_route("OPTIONS", "/api/state", _handle_options)
    app.router.add_route("OPTIONS", "/api/play", _handle_options)
    app.router.add_route("OPTIONS", "/api/promo", _handle_options)
    app.router.add_route("OPTIONS", "/api/crash/state", _handle_options)
    app.router.add_route("OPTIONS", "/api/crash/bet", _handle_options)
    app.router.add_route("OPTIONS", "/api/crash/cashout", _handle_options)
    app.router.add_route("OPTIONS", "/api/mines/state", _handle_options)
    app.router.add_route("OPTIONS", "/api/mines/start", _handle_options)
    app.router.add_route("OPTIONS", "/api/mines/reveal", _handle_options)
    app.router.add_route("OPTIONS", "/api/mines/cashout", _handle_options)
    return app


def run_api_server() -> None:
    """Запускает aiohttp-сервер в собственном event loop'е отдельного
    потока, параллельно с polling-циклом бота в главном потоке."""
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        app = build_api_app()
        logger.info("API мини-приложения слушает на 0.0.0.0:%s", API_PORT)
        # handle_signals=False обязателен: aiohttp по умолчанию пытается
        # перехватить системные сигналы (Ctrl+C и т.п.), а это разрешено
        # только в главном потоке программы. Без этого флага сервер падал
        # сразу после старта, никак не логируя ошибку, и Railway отвечал 502.
        web.run_app(app, host="0.0.0.0", port=API_PORT, print=None, handle_signals=False)
    except Exception:
        logger.exception("API мини-приложения аварийно остановилось")


# ---------------------------------------------------------------------------
# 💬 Поддержка: пользователь пишет — админ отвечает
# ---------------------------------------------------------------------------
# Скрытая метка вида "🆔ID:123456789" вшивается в пересланное админу
# сообщение и невидимо помогает боту понять, кому именно адресован ответ,
# когда админ использует обычный Reply в Telegram на это сообщение.
SUPPORT_ID_MARKER = "🆔ID:{}"
SUPPORT_ID_RE = re.compile(r"🆔ID:(\d+)")


async def support_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/support ТЕКСТ — написать в поддержку. Сообщение уходит всем
    админам; ответить можно либо через Reply на пересланное сообщение,
    либо командой /reply <ID> <текст>."""
    tg_user = update.effective_user
    if not await check_not_banned(update, tg_user.id):
        return

    text = " ".join(context.args) if context.args else ""
    if not text.strip():
        await update.message.reply_text("Напиши сообщение так: /support текст твоего вопроса")
        return
    if not ADMIN_IDS:
        await update.message.reply_text("Поддержка временно недоступна, попробуй позже.")
        return

    user = get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    header = (
        f"📩 Сообщение в поддержку\n"
        f"{SUPPORT_ID_MARKER.format(tg_user.id)}\n"
        f"От: {tg_user.first_name or 'без имени'} (@{tg_user.username or 'нет username'}), ID профиля {user['internal_id']}\n\n"
        f"{text}\n\n"
        f"↩️ Ответь на это сообщение (Reply) или командой /reply {tg_user.id} текст"
    )
    delivered = 0
    for admin_id in ADMIN_IDS:
        try:
            await context.bot.send_message(chat_id=admin_id, text=header)
            delivered += 1
        except Exception:
            logger.exception("Не удалось переслать сообщение в поддержку админу %s", admin_id)

    if delivered:
        await update.message.reply_text("✅ Сообщение отправлено в поддержку, жди ответа здесь же.")
    else:
        await update.message.reply_text("⚠️ Не удалось доставить сообщение, попробуй позже.")


async def reply_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/reply <ID пользователя> текст — явный ответ пользователю (админ)."""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return
    if len(context.args) < 2:
        await update.message.reply_text("Использование: /reply <ID пользователя> текст ответа")
        return

    try:
        target_id = int(context.args[0])
    except ValueError:
        await update.message.reply_text("ID пользователя должен быть числом.")
        return

    text = " ".join(context.args[1:])
    try:
        await context.bot.send_message(chat_id=target_id, text=f"💬 Ответ поддержки:\n\n{text}")
        await update.message.reply_text("✅ Ответ отправлен.")
    except Exception:
        await update.message.reply_text("⚠️ Не удалось отправить — возможно, пользователь заблокировал бота.")


async def admin_reply_via_native_reply(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Позволяет админу ответить пользователю просто через обычный Reply
    на пересланное сообщение поддержки, без набора команды /reply."""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        return
    original = update.message.reply_to_message
    if not original or not original.text:
        return
    match = SUPPORT_ID_RE.search(original.text)
    if not match:
        return

    target_id = int(match.group(1))
    text = update.message.text or ""
    if not text.strip():
        return
    try:
        await context.bot.send_message(chat_id=target_id, text=f"💬 Ответ поддержки:\n\n{text}")
        await update.message.reply_text("✅ Ответ отправлен.")
    except Exception:
        await update.message.reply_text("⚠️ Не удалось отправить — возможно, пользователь заблокировал бота.")


async def broadcast_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/broadcast ТЕКСТ — объявление всем пользователям бота (админ)."""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    text = " ".join(context.args) if context.args else ""
    if not text.strip():
        await update.message.reply_text("Использование: /broadcast текст объявления")
        return

    user_ids = get_all_user_ids()
    if not user_ids:
        await update.message.reply_text("Пока нет ни одного пользователя для рассылки.")
        return

    status = await update.message.reply_text(f"📢 Рассылаю объявление {len(user_ids)} пользователям...")
    sent, failed = 0, 0
    message_text = f"📢 Объявление\n\n{text}"
    for uid in user_ids:
        try:
            await context.bot.send_message(chat_id=uid, text=message_text)
            sent += 1
        except Exception:
            failed += 1
        await asyncio.sleep(0.05)  # бережём лимиты Telegram на частоту сообщений

    await safe_edit(status, f"📢 Готово: доставлено {sent}, не удалось {failed} (заблокировали бота или удалили аккаунт).")


# ---------------------------------------------------------------------------
# 🛡️ Админ-панель: список пользователей, баны, предупреждения
# ---------------------------------------------------------------------------

USERS_PAGE_SIZE = 15


def format_user_line(u: sqlite3.Row) -> str:
    status = "⛔" if u["banned"] else "✅"
    warn = f" ⚠️{u['warnings']}" if u["warnings"] else ""
    uname = f"@{u['username']}" if u["username"] else "—"
    return (
        f"{status} #{u['internal_id']} | {u['first_name']} ({uname})\n"
        f"    id:{u['telegram_id']} | 💰{u['balance']} | 🎮{u['games_played']}{warn}"
    )


async def list_users(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /users [страница]"""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    page = 1
    if context.args:
        try:
            page = max(1, int(context.args[0]))
        except ValueError:
            page = 1

    offset = (page - 1) * USERS_PAGE_SIZE
    rows, total = list_all_users(limit=USERS_PAGE_SIZE, offset=offset)

    if not rows:
        await update.message.reply_text("Пользователей на этой странице нет.")
        return

    total_pages = (total + USERS_PAGE_SIZE - 1) // USERS_PAGE_SIZE
    lines = [format_user_line(u) for u in rows]
    text = (
        f"👥 <b>Пользователи</b> (стр. {page}/{total_pages}, всего {total})\n\n"
        + "\n\n".join(lines)
        + f"\n\nЕщё страницы: /users {page + 1}"
    )
    await update.message.reply_text(text, parse_mode="HTML")


async def user_info(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /userinfo ID_или_@username"""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    if not context.args:
        await update.message.reply_text("Использование: /userinfo ID_или_@username")
        return

    u = find_user(context.args[0])
    if not u:
        await update.message.reply_text("Пользователь не найден.")
        return

    status = "⛔ Забанен" if u["banned"] else "✅ Активен"
    text = (
        f"👤 <b>{u['first_name']}</b> (@{u['username'] or '—'})\n\n"
        f"🆔 Внутренний ID: {u['internal_id']}\n"
        f"📱 Telegram ID: <code>{u['telegram_id']}</code>\n"
        f"💰 Баланс: {u['balance']}\n"
        f"🎮 Игр сыграно: {u['games_played']}\n"
        f"⚠️ Предупреждений: {u['warnings']}\n"
        f"Статус: {status}"
    )
    if u["banned"] and u["ban_reason"]:
        text += f"\nПричина бана: {u['ban_reason']}"

    await update.message.reply_text(text, parse_mode="HTML")


async def ban_user_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /ban ID_или_@username [причина]"""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    if not context.args:
        await update.message.reply_text("Использование: /ban ID_или_@username [причина]")
        return

    u = find_user(context.args[0])
    if not u:
        await update.message.reply_text("Пользователь не найден.")
        return

    if u["telegram_id"] == tg_user.id:
        await update.message.reply_text("⛔ Нельзя забанить самого себя.")
        return

    reason = " ".join(context.args[1:]) if len(context.args) > 1 else "не указана"
    set_ban(u["telegram_id"], True, reason)

    await update.message.reply_text(
        f"⛔ Пользователь {u['first_name']} (id:{u['telegram_id']}) забанен.\nПричина: {reason}"
    )
    try:
        await context.bot.send_message(
            chat_id=u["telegram_id"],
            text=f"⛔ Ты заблокирован в этом боте.\nПричина: {reason}",
        )
    except Exception:
        pass  # пользователь мог заблокировать бота — это не критично


async def unban_user_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /unban ID_или_@username"""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    if not context.args:
        await update.message.reply_text("Использование: /unban ID_или_@username")
        return

    u = find_user(context.args[0])
    if not u:
        await update.message.reply_text("Пользователь не найден.")
        return

    set_ban(u["telegram_id"], False)
    await update.message.reply_text(f"✅ Пользователь {u['first_name']} (id:{u['telegram_id']}) разбанен.")
    try:
        await context.bot.send_message(
            chat_id=u["telegram_id"],
            text="✅ Блокировка снята, можешь снова пользоваться ботом.",
        )
    except Exception:
        pass


async def warn_user_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /warn ID_или_@username [причина]"""
    tg_user = update.effective_user
    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    if not context.args:
        await update.message.reply_text("Использование: /warn ID_или_@username [причина]")
        return

    u = find_user(context.args[0])
    if not u:
        await update.message.reply_text("Пользователь не найден.")
        return

    if u["telegram_id"] == tg_user.id:
        await update.message.reply_text("⛔ Нельзя выдать предупреждение самому себе.")
        return

    reason = " ".join(context.args[1:]) if len(context.args) > 1 else "не указана"
    new_count = add_warning(u["telegram_id"])

    await update.message.reply_text(
        f"⚠️ Пользователю {u['first_name']} (id:{u['telegram_id']}) выдано предупреждение "
        f"({new_count} всего).\nПричина: {reason}"
    )

    warning_text = f"⚠️ Тебе выдано предупреждение.\nПричина: {reason}\nВсего предупреждений: {new_count}"

    auto_banned = False
    if AUTO_BAN_AFTER_WARNINGS and new_count >= AUTO_BAN_AFTER_WARNINGS:
        auto_reason = f"автобан после {new_count} предупреждений"
        set_ban(u["telegram_id"], True, auto_reason)
        warning_text += f"\n\n⛔ Достигнут лимит предупреждений — доступ заблокирован."
        auto_banned = True

    try:
        await context.bot.send_message(chat_id=u["telegram_id"], text=warning_text)
    except Exception:
        pass

    if auto_banned:
        await update.message.reply_text(
            f"⛔ Пользователь автоматически забанен (лимит {AUTO_BAN_AFTER_WARNINGS} предупреждений)."
        )


# ---------------------------------------------------------------------------
# 🎟️ Промокоды
# ---------------------------------------------------------------------------

async def create_promo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Админ-команда: /createpromo КОД СУММА [макс_активаций]"""
    tg_user = update.effective_user

    if tg_user.id not in ADMIN_IDS:
        await update.message.reply_text("⛔ Эта команда доступна только администратору.")
        return

    if len(context.args) < 2:
        await update.message.reply_text(
            "Использование:\n"
            "/createpromo КОД СУММА [макс_активаций]\n\n"
            "Примеры:\n"
            "/createpromo WELCOME100 100 — код на 100 очков, 1 активация на человека\n"
            "/createpromo VIP500 500 50 — код на 500 очков, максимум 50 активаций всего"
        )
        return

    code = context.args[0]
    try:
        amount = int(context.args[1])
    except ValueError:
        await update.message.reply_text("Сумма должна быть целым числом.")
        return

    if amount <= 0:
        await update.message.reply_text("Сумма должна быть положительной.")
        return

    max_uses = 1
    if len(context.args) >= 3:
        try:
            max_uses = int(context.args[2])
            if max_uses <= 0:
                max_uses = 1
        except ValueError:
            max_uses = 1

    created = create_promo_code(code, amount, max_uses, tg_user.id)
    if not created:
        await update.message.reply_text(
            f"Промокод «{code.upper()}» уже существует. Выбери другой код."
        )
        return

    await update.message.reply_text(
        f"✅ Промокод создан!\n\n"
        f"🎟️ Код: <code>{code.upper()}</code>\n"
        f"💰 Сумма: {amount} очков\n"
        f"🔢 Макс. активаций: {max_uses}\n\n"
        f"Отправь пользователям команду:\n<code>/promo {code.upper()}</code>",
        parse_mode="HTML",
    )


async def promo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Пользовательская команда: /promo КОД"""
    tg_user = update.effective_user
    get_or_create_user(tg_user.id, tg_user.username or "", tg_user.first_name or "")
    if not await check_not_banned(update, tg_user.id):
        return

    if not context.args:
        await update.message.reply_text("Использование: /promo КОД")
        return

    code = context.args[0]
    success, message, amount = redeem_promo_code(code, tg_user.id)

    if success:
        new_balance = get_user(tg_user.id)["balance"]
        await update.message.reply_text(
            f"🎉 {message}\n"
            f"💰 Начислено: +{amount} очков\n"
            f"Новый баланс: <b>{new_balance}</b>",
            parse_mode="HTML",
        )
    else:
        await update.message.reply_text(f"❌ {message}")


async def open_app(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/app — прямая кнопка для открытия мини-приложения."""
    if not WEBAPP_URL:
        await update.message.reply_text(
            "Мини-приложение пока не подключено.\n"
            "Администратору: задай WEBAPP_URL в bot.py (см. инструкцию в конце файла)."
        )
        return

    keyboard = InlineKeyboardMarkup(
        [[InlineKeyboardButton("📱 Открыть", web_app=WebAppInfo(url=WEBAPP_URL))]]
    )
    await update.message.reply_text("Жми, чтобы открыть мини-приложение:", reply_markup=keyboard)


# ---------------------------------------------------------------------------
# Обработчик инлайн-кнопок
# ---------------------------------------------------------------------------

async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()

    if query.data == "profile":
        await profile(update, context)
    elif query.data == "how_roulette":
        await query.message.reply_text(f"🎰 /roulette {DEFAULT_BET} — крути рулетку на указанную ставку.")
    elif query.data == "how_dice":
        await query.message.reply_text(f"🎲 /dice {DEFAULT_BET} 4 — ставка {DEFAULT_BET}, загадываешь число 4 (1–6).")
    elif query.data == "how_slots":
        await query.message.reply_text(f"🎯 /slots {DEFAULT_BET} — крути слоты на указанную ставку.")
    elif query.data == "how_coinflip":
        await query.message.reply_text(f"🪙 /coinflip {DEFAULT_BET} орёл — ставка {DEFAULT_BET} на орла.")
    elif query.data == "how_blackred":
        await query.message.reply_text(f"🔴⚫ /blackred {DEFAULT_BET} красное — ставка {DEFAULT_BET} на красное.")
    elif query.data == "mnoop":
        await query.answer()
    elif query.data.startswith("mn:"):
        idx = int(query.data.split(":", 1)[1])
        ok, kind, data = mines_reveal(query.from_user.id, idx)
        if not ok:
            await query.answer(kind, show_alert=True)
            return
        snap = mines_get_state(query.from_user.id)
        revealed = snap["revealed"] if snap else [idx]

        if kind == "hit":
            kb = build_mines_keyboard(revealed=revealed, mines=data["minePositions"], hit_index=idx, disabled=True)
            await query.edit_message_text(
                f"💥 Бум! Тут была мина — ставка сгорела.\n💰 Баланс: {data['balance']}",
                reply_markup=kb,
            )
        elif kind == "cleared":
            kb = build_mines_keyboard(revealed=revealed, mines=data["minePositions"], disabled=True)
            await query.edit_message_text(
                f"🏆 Все безопасные клетки открыты!\n"
                f"Множитель ×{data['multiplier']}, выигрыш +{data['winnings']}\n"
                f"💰 Баланс: {data['balance']}",
                reply_markup=kb,
            )
        else:
            kb = build_mines_keyboard(revealed=revealed)
            await query.edit_message_text(
                f"💣 Мины — множитель ×{data['multiplier']}\n"
                f"Открыто клеток: {len(revealed)}. Жми ещё или забирай выигрыш.",
                reply_markup=kb,
            )
    elif query.data == "mncashout":
        ok, message, data = mines_cash_out(query.from_user.id)
        if not ok:
            await query.answer(message, show_alert=True)
            return
        snap = mines_get_state(query.from_user.id)
        revealed = snap["revealed"] if snap else []
        kb = build_mines_keyboard(revealed=revealed, mines=data["minePositions"], disabled=True)
        await query.edit_message_text(
            f"💸 Забрано на ×{data['multiplier']}!\n"
            f"Выигрыш: +{data['winnings']}\n"
            f"💰 Баланс: {data['balance']}",
            reply_markup=kb,
        )


# ---------------------------------------------------------------------------
# Обработчик ошибок
# ---------------------------------------------------------------------------

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.error("Ошибка при обработке обновления %s: %s", update, context.error)


# ---------------------------------------------------------------------------
# Точка входа
# ---------------------------------------------------------------------------

async def post_init(application) -> None:
    """Выполняется один раз при старте: ставит системную Menu Button
    (кнопка рядом со скрепкой ввода), открывающую мини-приложение."""
    if not WEBAPP_URL:
        return
    try:
        from telegram import MenuButtonWebApp
        await application.bot.set_chat_menu_button(
            menu_button=MenuButtonWebApp(text="🎰 Казино", web_app=WebAppInfo(url=WEBAPP_URL))
        )
        logger.info("Menu Button с мини-приложением установлена.")
    except Exception as e:
        logger.warning("Не удалось установить Menu Button: %s", e)


def main() -> None:
    if TOKEN == "ВАШ_ТОКЕН_ЗДЕСЬ":
        raise SystemExit(
            "Укажи токен бота через переменную окружения BOT_TOKEN.\n"
            "PowerShell: $env:BOT_TOKEN=\"123456:ABC-DEF...\"\n"
            "Linux/macOS: export BOT_TOKEN=\"123456:ABC-DEF...\""
        )

    init_db()

    api_thread = threading.Thread(target=run_api_server, daemon=True)
    api_thread.start()

    crash_thread = threading.Thread(target=crash_scheduler, daemon=True)
    crash_thread.start()

    builder = ApplicationBuilder().token(TOKEN).post_init(post_init)
    if PROXY_URL:
        builder = builder.proxy(PROXY_URL).get_updates_proxy(PROXY_URL)
        logger.info("Использую прокси: %s", PROXY_URL)
    application = builder.build()

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("profile", profile))
    application.add_handler(CommandHandler("games", games_menu))
    application.add_handler(CommandHandler("app", open_app))
    application.add_handler(CommandHandler("roulette", roulette))
    application.add_handler(CommandHandler("dice", dice))
    application.add_handler(CommandHandler("slots", slots))
    application.add_handler(CommandHandler("coinflip", coinflip))
    application.add_handler(CommandHandler("blackred", blackred))
    application.add_handler(CommandHandler("crash", crash_cmd))
    application.add_handler(CommandHandler("cashout", cashout_cmd))
    application.add_handler(CommandHandler("mines", mines_cmd))
    application.add_handler(CommandHandler("createpromo", create_promo))
    application.add_handler(CommandHandler("promo", promo))
    application.add_handler(CommandHandler("users", list_users))
    application.add_handler(CommandHandler("userinfo", user_info))
    application.add_handler(CommandHandler("ban", ban_user_cmd))
    application.add_handler(CommandHandler("unban", unban_user_cmd))
    application.add_handler(CommandHandler("warn", warn_user_cmd))
    application.add_handler(CommandHandler("support", support_cmd))
    application.add_handler(CommandHandler("reply", reply_cmd))
    application.add_handler(CommandHandler("broadcast", broadcast_cmd))
    if ADMIN_IDS:
        application.add_handler(
            MessageHandler(filters.REPLY & filters.User(list(ADMIN_IDS)) & filters.TEXT, admin_reply_via_native_reply)
        )
    application.add_handler(CommandHandler("help", help_command))
    application.add_handler(CallbackQueryHandler(button_callback))

    application.add_error_handler(error_handler)

    logger.info("Бот запущен. Нажми Ctrl+C для остановки.")
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
