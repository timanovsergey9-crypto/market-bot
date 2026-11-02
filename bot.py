"""
Telegram-бот сигналов по фьючерсам BingX (USDT-M Perpetual).
Ищет перегретые и перепроданные монеты, учитывает объём, funding, OI и контекст BTC.

УСТАНОВКА (Python 3.10+):
    python -m venv venv
    source venv/bin/activate          # Windows: venv\\Scripts\\activate
    pip install -r requirements.txt

НАСТРОЙКА:
    cp .env.example .env              # Windows: copy .env.example .env
    1) Создайте бота у @BotFather и вставьте токен в BOT_TOKEN.
    2) Запустите бота с пустым CHAT_ID, напишите ему /start —
       он ответит вашим chat_id. Впишите его в CHAT_ID и перезапустите.

ЗАПУСК:
    python bot.py

    Для постоянной работы на сервере: systemd, pm2, tmux или Docker.
    Логи пишутся в консоль и в bot.log. Остановка — Ctrl+C.

ПУБЛИКАЦИЯ В ВК (необязательно):
    В .env задайте VK_TOKEN (ключ доступа сообщества или токен администратора)
    и VK_GROUP (короткое имя или числовой id группы). Бот сам публикует
    утренний обзор рынка и вечерние итоги. Проверка: в Telegram /vkpreview и /vkpost.

После запуска дайте боту поработать 1–2 часа: история OI и funding копится в SQLite,
и нормализация по ним становится точнее. Не торгуйте вслепую: сначала смотрите /stats.
"""
from __future__ import annotations

import asyncio
import bisect
import functools
import html
import json
import logging
import logging.handlers
import math
import os
import random
import re
import sqlite3
import statistics
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone

import aiohttp
from aiohttp import web
from dotenv import load_dotenv
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest, NetworkError, RetryAfter, TimedOut
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes

try:  # PostgreSQL нужен только если задан DATABASE_URL
    import psycopg
except ImportError:  # pragma: no cover
    psycopg = None


# ======================================================================
# КОНФИГУРАЦИЯ (.env)
# ======================================================================
load_dotenv()


def _env(name: str, default, cast=str):
    """Читает переменную окружения и приводит к нужному типу."""
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    raw = raw.strip()
    try:
        if cast is bool:
            return raw.lower() in ("1", "true", "yes", "on")
        if cast is int:
            return int(float(raw))
        return cast(raw)
    except ValueError:
        raise SystemExit(f"Некорректное значение в .env: {name}={raw!r}")


# Сколько свечей приходится на час для разных интервалов
BARS_PER_HOUR = {"1m": 60, "3m": 20, "5m": 12, "15m": 4, "30m": 2, "1h": 1}

# Параметры, которые можно менять на лету командой /set:
# имя -> (тип, минимум, максимум, описание)
SETTABLE = {
    "score_threshold": (float, 0.5, 6.0, "порог итогового скора для сигнала"),
    "min_volume_usdt": (float, 0, 1e12, "мин. 24ч объём (USDT)"),
    "top_n": (int, 5, 200, "сколько топ-монет по объёму сканировать"),
    "scan_interval_sec": (int, 30, 900, "период сканирования (сек)"),
    "cooldown_min": (int, 0, 10080, "пауза между сигналами по одной монете (мин)"),
    "vol_z_high": (float, -3, 6, "z-объёма, выше которого объём 'высокий'"),
    "vol_z_low": (float, -6, 3, "z-объёма, ниже которого объём 'низкий'"),
    "min_listing_days": (int, 0, 3650, "мин. возраст листинга (дни)"),
    "regime_penalty": (float, 0.3, 1.0, "множитель скора против режима рынка"),
    "rs_weight": (float, 0, 2, "вес силы монеты относительно BTC"),
    "max_spread_pct": (float, 0.01, 10, "макс. спред bid/ask (%)"),
    "max_signals_per_scan": (int, 1, 20, "макс. сигналов за один скан"),
}


class Config:
    def __init__(self) -> None:
        # --- Telegram ---
        self.bot_token: str = _env("BOT_TOKEN", "")
        self.chat_id: int = _env("CHAT_ID", 0, int)  # 0 = ещё не задан
        if not self.bot_token:
            raise SystemExit("Не задан BOT_TOKEN в .env (получите у @BotFather).")

        # --- Общее ---
        self.db_path: str = _env("DB_PATH", "signals.db")
        # PostgreSQL (Render Postgres, Neon и т.п.). Если задан — история хранится там и
        # не стирается при деплоях; иначе используется файл SQLite (db_path).
        self.database_url: str = _env("DATABASE_URL", "")
        self.fee_pct: float = _env("FEE_PCT", 0.1, float)  # круговая комиссия+проскальзывание, % (для статистики)
        self.log_level: str = _env("LOG_LEVEL", "INFO").upper()

        # --- Сканер ---
        self.top_n: int = _env("TOP_N", 60, int)
        self.scan_interval_sec: int = _env("SCAN_INTERVAL_SEC", 120, int)
        self.kline_interval: str = _env("KLINE_INTERVAL", "15m")
        self.kline_limit: int = _env("KLINE_LIMIT", 300, int)
        self.min_bars: int = _env("MIN_BARS", 120, int)
        self.concurrency: int = _env("CONCURRENCY", 5, int)
        self.request_rate: float = _env("REQUEST_RATE", 5.0, float)  # запросов/сек
        self.snapshot_keep_hours: int = _env("SNAPSHOT_KEEP_HOURS", 24, int)

        if self.kline_interval not in BARS_PER_HOUR:
            raise SystemExit(f"KLINE_INTERVAL должен быть одним из {list(BARS_PER_HOUR)}")
        bph = BARS_PER_HOUR[self.kline_interval]
        self.bars_per_hour: int = bph
        self.ret_bars: int = bph          # окно доходности = 1 час
        self.sma_bars: int = 12 * bph     # SMA за 12 часов
        self.atr_bars: int = max(2 * bph, 4)  # окно волатильности ~2 часа

        # --- Фильтры качества ---
        self.min_volume_usdt: float = _env("MIN_VOLUME_USDT", 5_000_000.0, float)
        self.min_listing_days: int = _env("MIN_LISTING_DAYS", 14, int)
        self.max_spread_pct: float = _env("MAX_SPREAD_PCT", 0.3, float)
        stables = _env(
            "STABLE_BASES",
            "USDC,TUSD,FDUSD,DAI,USDE,BUSD,USDD,PYUSD,USDP,USDS,EURT,EUR,GUSD,LUSD,FRAX,USD1,XUSD",
        )
        self.stable_bases: set[str] = {s.strip().upper() for s in stables.split(",") if s.strip()}
        # Мусор: токенизированные акции/сырьё BingX (NC...2USD) и леверидж-токены (…3L/3S)
        self.junk_re = re.compile(_env("JUNK_REGEX", r"^NC.*2USD$|\d+[LS]$"))

        # --- Скоринг ---
        self.w_ret: float = _env("W_RET", 1.0, float)
        self.w_dev: float = _env("W_DEV", 1.0, float)
        self.w_funding: float = _env("W_FUNDING", 0.7, float)
        self.w_oi: float = _env("W_OI", 0.7, float)
        self.w_volume: float = _env("W_VOLUME", 0.5, float)
        self.w_volatility: float = _env("W_VOLATILITY", 0.4, float)
        self.z_clip: float = _env("Z_CLIP", 4.0, float)
        self.funding_ref: float = _env("FUNDING_REF", 0.0005, float)  # 0.05% = 1 единица
        self.oi_ref_pct: float = _env("OI_REF_PCT", 3.0, float)       # 3% за час = 1 единица
        self.min_hist_points: int = _env("MIN_HIST_POINTS", 30, int)

        # --- Сигналы и контекст рынка ---
        self.score_threshold: float = _env("SCORE_THRESHOLD", 1.8, float)
        self.vol_z_high: float = _env("VOL_Z_HIGH", 1.0, float)
        self.vol_z_low: float = _env("VOL_Z_LOW", -0.3, float)
        self.cooldown_min: int = _env("COOLDOWN_MIN", 240, int)
        self.regime_thr_pct: float = _env("REGIME_THR_PCT", 0.8, float)
        self.regime_penalty: float = _env("REGIME_PENALTY", 0.85, float)
        self.rs_weight: float = _env("RS_WEIGHT", 0.3, float)
        self.rs_ref_pct: float = _env("RS_REF_PCT", 2.0, float)
        self.max_signals_per_scan: int = _env("MAX_SIGNALS_PER_SCAN", 5, int)
        self.mute_default_hours: int = _env("MUTE_DEFAULT_HOURS", 6, int)

        # --- Публикация в ВК ---
        self.vk_token: str = _env("VK_TOKEN", "")
        self.vk_group: str = _env("VK_GROUP", "")  # короткое имя (elevationoff) или числовой id
        self.vk_enabled: bool = bool(self.vk_token and self.vk_group)
        self.vk_api_version: str = _env("VK_API_VERSION", "5.199")
        self.vk_morning_hour: int = _env("VK_MORNING_HOUR", 9, int)   # -1 = выключить
        self.vk_evening_hour: int = _env("VK_EVENING_HOUR", 21, int)  # -1 = выключить
        self.vk_tz_offset: int = _env("VK_TZ_OFFSET", 3, int)         # 3 = Москва
        self.vk_hashtags: str = _env("VK_HASHTAGS", "#крипта #криптовалюта #биткоин #трейдинг #обзоррынка #bingx")
        self.vk_cta: str = _env("VK_CTA", "🔔 Подписывайтесь на группу — обзоры рынка выходят каждый день!")
        self.vk_disclaimer: str = _env("VK_DISCLAIMER", "⚠️ Не является финансовой рекомендацией.")


def set_param(cfg: Config, key: str, raw: str):
    """Меняет параметр из SETTABLE с проверкой типа и диапазона. Бросает ValueError."""
    if key not in SETTABLE:
        raise ValueError(f"неизвестный параметр: {key}")
    typ, lo, hi, _ = SETTABLE[key]
    try:
        val = typ(float(raw.replace(",", ".")))
    except ValueError:
        raise ValueError(f"нужно число, получено {raw!r}")
    if not (lo <= val <= hi):
        raise ValueError(f"допустимый диапазон: {lo} … {hi}")
    setattr(cfg, key, val)
    return val


# ======================================================================
# КЛИЕНТ BINGX (публичный API)
# ======================================================================
log = logging.getLogger("bot")

BASE_URL = "https://open-api.bingx.com"
RATE_LIMIT_CODES = {100410}  # код BingX "rate limit exceeded"


class BingXError(Exception):
    def __init__(self, code: int, msg: str):
        super().__init__(f"BingX code={code}: {msg}")
        self.code = code


@dataclass
class Contract:
    symbol: str
    online: bool
    launch_ts: float  # unix-секунды, 0 если биржа не отдала дату


@dataclass
class Ticker:
    symbol: str
    last: float
    quote_volume: float  # 24ч объём в USDT
    change_pct: float
    bid: float
    ask: float


@dataclass
class Candle:
    ts: int  # время открытия, мс
    open: float
    high: float
    low: float
    close: float
    volume: float  # в базовой монете


def _f(x, default: float = 0.0) -> float:
    """Безопасное приведение к float (BingX отдаёт числа строками)."""
    try:
        if x is None:
            return default
        if isinstance(x, str):
            x = x.replace("%", "").strip()
        return float(x)
    except (TypeError, ValueError):
        return default


def normalize_symbol(text: str) -> str:
    """'btc', 'BTCUSDT', 'btc/usdt' -> 'BTC-USDT'."""
    s = text.strip().upper().replace("/", "-").replace("_", "-")
    if "-" not in s:
        s = s[:-4] + "-USDT" if s.endswith("USDT") and len(s) > 4 else s + "-USDT"
    return s


class BingXClient:
    def __init__(self, rate_per_sec: float = 8.0, timeout: float = 15.0, max_retries: int = 4):
        self._interval = 1.0 / max(rate_per_sec, 0.5)
        self._timeout = timeout
        self._max_retries = max_retries
        self._session: aiohttp.ClientSession | None = None
        self._lock = asyncio.Lock()
        self._next_slot = 0.0

    async def start(self) -> None:
        self._session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=self._timeout),
            headers={"User-Agent": "bingx-signal-bot/1.0"},
        )

    async def close(self) -> None:
        if self._session:
            await self._session.close()
            self._session = None

    # ---------- низкоуровневое ----------
    async def _throttle(self) -> None:
        """Ограничитель частоты: не чаще rate_per_sec запросов в секунду."""
        async with self._lock:
            now = time.monotonic()
            start = max(now, self._next_slot)
            self._next_slot = start + self._interval
        delay = start - now
        if delay > 0:
            await asyncio.sleep(delay)

    @staticmethod
    def _backoff(attempt: int) -> float:
        return min(2 ** attempt, 20) + random.random()

    async def _get(self, path: str, params: dict | None = None):
        if self._session is None:
            raise RuntimeError("Клиент не запущен: вызовите start()")
        last_err = ""
        for attempt in range(1, self._max_retries + 1):
            await self._throttle()
            q = dict(params or {})
            q["timestamp"] = int(time.time() * 1000)
            try:
                async with self._session.get(BASE_URL + path, params=q) as resp:
                    if resp.status == 429 or resp.status >= 500:
                        last_err = f"HTTP {resp.status}"
                        wait = max(_f(resp.headers.get("Retry-After")), self._backoff(attempt))
                        log.warning("%s -> %s, пауза %.1fс", path, last_err, wait)
                        await asyncio.sleep(wait)
                        continue
                    data = await resp.json(content_type=None)
            except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                last_err = repr(e)
                await asyncio.sleep(self._backoff(attempt))
                continue

            if not isinstance(data, dict):
                last_err = "неожиданный формат ответа"
                await asyncio.sleep(self._backoff(attempt))
                continue
            code = data.get("code", 0)
            if code == 0:
                return data.get("data")
            if code in RATE_LIMIT_CODES:
                last_err = "rate limit"
                log.warning("%s: превышен лимит BingX, замедляюсь", path)
                await asyncio.sleep(self._backoff(attempt) * 2)
                continue
            raise BingXError(code, str(data.get("msg")))  # непереторяемая ошибка
        raise BingXError(-1, f"{path}: исчерпаны попытки ({last_err})")

    # ---------- публичные методы ----------
    async def get_contracts(self) -> list[Contract]:
        data = await self._get("/openApi/swap/v2/quote/contracts")
        out = []
        for c in data or []:
            sym = c.get("symbol")
            if not sym:
                continue
            launch = _f(c.get("launchTime") or c.get("onboardTime"))
            if launch > 1e11:  # миллисекунды -> секунды
                launch /= 1000.0
            online = str(c.get("status", 1)) == "1"
            out.append(Contract(sym, online, launch))
        return out

    async def get_tickers(self) -> dict[str, Ticker]:
        data = await self._get("/openApi/swap/v2/quote/ticker")
        out = {}
        for t in data or []:
            sym = t.get("symbol")
            last = _f(t.get("lastPrice"))
            if not sym or last <= 0:
                continue
            qv = _f(t.get("quoteVolume")) or _f(t.get("volume")) * last
            op = _f(t.get("openPrice"))
            chg = (last / op - 1) * 100 if op > 0 else _f(t.get("priceChangePercent"))
            out[sym] = Ticker(
                symbol=sym, last=last, quote_volume=qv,
                change_pct=chg,
                bid=_f(t.get("bidPrice")), ask=_f(t.get("askPrice")),
            )
        return out

    async def get_klines(self, symbol: str, interval: str, limit: int) -> list[Candle]:
        params = {"symbol": symbol, "interval": interval, "limit": limit}
        try:
            data = await self._get("/openApi/swap/v3/quote/klines", params)
        except BingXError as e:
            if e.code == -1:
                raise
            data = await self._get("/openApi/swap/v2/quote/klines", params)  # запасной эндпоинт
        by_ts: dict[int, Candle] = {}
        for k in data or []:
            if isinstance(k, dict):
                c = Candle(int(_f(k.get("time"))), _f(k.get("open")), _f(k.get("high")),
                           _f(k.get("low")), _f(k.get("close")), _f(k.get("volume")))
            elif isinstance(k, (list, tuple)) and len(k) >= 6:
                c = Candle(int(_f(k[0])), _f(k[1]), _f(k[2]), _f(k[3]), _f(k[4]), _f(k[5]))
            else:
                continue
            if c.close > 0 and c.high >= c.low > 0:
                by_ts[c.ts] = c
        return [by_ts[t] for t in sorted(by_ts)]  # по возрастанию времени

    async def get_funding(self, symbol: str | None = None) -> dict[str, tuple[float, float]]:
        """Funding rate: symbol -> (ставка, mark price). Без symbol — по всем (если API позволяет)."""
        data = await self._get("/openApi/swap/v2/quote/premiumIndex", {"symbol": symbol} if symbol else None)
        items = data if isinstance(data, list) else ([data] if isinstance(data, dict) else [])
        return {
            it["symbol"]: (_f(it.get("lastFundingRate")), _f(it.get("markPrice")))
            for it in items if it.get("symbol")
        }

    async def get_funding_all(self) -> dict[str, tuple[float, float]]:
        return await self.get_funding(None)

    async def get_open_interest(self, symbol: str) -> float | None:
        data = await self._get("/openApi/swap/v2/quote/openInterest", {"symbol": symbol})
        if isinstance(data, dict):
            v = _f(data.get("openInterest"))
            return v if v > 0 else None
        return None


# ======================================================================
# СКОРИНГ
# ======================================================================
def robust_z(value: float, history: list[float], floor: float, clip: float) -> float:
    """Робастный z-score. floor — минимальный масштаб, чтобы не делить на ~0."""
    if len(history) < 10:
        return 0.0
    med = statistics.median(history)
    mad = statistics.median([abs(x - med) for x in history])
    scale = max(1.4826 * mad, floor)
    return max(-clip, min(clip, (value - med) / scale))


def pct_rank(value: float, history: list[float]) -> float:
    """Перцентиль значения в истории (0..100)."""
    if not history:
        return 50.0
    return 100.0 * sum(1 for x in history if x <= value) / len(history)


def derive_norm(value: float, history: list[float], ref: float, cfg) -> float:
    """Нормализация funding / OI.

    Истории хватает -> z-score по ней (с нижней границей масштаба 0.25*ref).
    Истории мало (бот только запущен) -> просто value/ref, где ref — «одна единица».
    """
    if len(history) >= cfg.min_hist_points:
        med = statistics.median(history)
        mad = statistics.median([abs(x - med) for x in history])
        z = (value - med) / max(1.4826 * mad, 0.25 * ref)
    else:
        z = value / ref
    return max(-cfg.z_clip, min(cfg.z_clip, z))


def compute_price_features(candles, cfg) -> dict | None:
    """Признаки по свечам: доходность, отклонение от SMA, волатильность, объём."""
    n = len(candles)
    if n < cfg.min_bars:
        return None
    clip = cfg.z_clip
    closes = [c.close for c in candles]

    # 1) Доходность за окно (по умолчанию 1ч) против собственной истории таких же окон
    k = cfg.ret_bars
    rets = [closes[i] / closes[i - k] - 1 for i in range(k, n)]
    ret_now = rets[-1]
    ret_z = robust_z(ret_now, rets[:-1], 0.003, clip)

    # 2) Отклонение цены от SMA (по умолчанию 12ч)
    m = cfg.sma_bars
    pref = [0.0]
    for c in closes:
        pref.append(pref[-1] + c)
    devs = [closes[i] / ((pref[i + 1] - pref[i + 1 - m]) / m) - 1 for i in range(m - 1, n)]
    dev_now = devs[-1]
    dev_z = robust_z(dev_now, devs[:-1], 0.003, clip)

    # Для волатильности и объёма берём только закрытые свечи (последняя ещё формируется)
    closed = candles[:-1]

    # 3) Волатильность: средний диапазон (high-low)/close за atr_bars, в логарифмах
    ranges = [(c.high - c.low) / c.close for c in closed]
    a = cfg.atr_bars
    atr_series = [sum(ranges[i - a + 1:i + 1]) / a for i in range(a - 1, len(ranges))]
    log_atr = [math.log(max(x, 1e-6)) for x in atr_series]
    atr_z = robust_z(log_atr[-1], log_atr[:-1], 0.1, clip)

    # 4) Объём: сумма объёма в USDT за окно k свечей, в логарифмах
    pq = [0.0]
    for c in closed:
        pq.append(pq[-1] + c.volume * c.close)
    vsum = [pq[i + 1] - pq[i + 1 - k] for i in range(k - 1, len(closed))]
    log_v = [math.log1p(max(x, 0.0)) for x in vsum]
    vol_z = robust_z(log_v[-1], log_v[:-1], 0.1, clip)
    vol_pct = pct_rank(log_v[-1], log_v[:-1])

    h4 = 4 * cfg.bars_per_hour
    ret4h = (closes[-1] / closes[-1 - h4] - 1) * 100 if n > h4 else 0.0

    return {
        "price": closes[-1],
        "ret_pct": ret_now * 100, "ret_z": ret_z, "ret4h_pct": ret4h,
        "dev_pct": dev_now * 100, "dev_z": dev_z,
        "atr_pct": atr_series[-1] * 100, "atr_z": atr_z,
        "vol_z": vol_z, "vol_pctile": vol_pct,
    }


def oi_change_features(series: list[tuple[float, float]], lookback_sec: float, cfg):
    """series: [(ts, oi)] по возрастанию, последняя точка — текущая.

    Возвращает (изменение OI за lookback в %, нормализованное значение).
    BingX отдаёт только текущий OI, поэтому историю копим сами в SQLite.
    """
    if len(series) < 2:
        return None, 0.0
    ts = [t for t, _ in series]

    def change_at(i: int):
        j = bisect.bisect_right(ts, ts[i] - lookback_sec) - 1
        if j < 0 or series[j][1] <= 0:
            return None
        return (series[i][1] / series[j][1] - 1) * 100

    cur = change_at(len(series) - 1)
    if cur is None:  # истории меньше lookback — сравниваем с самой ранней точкой
        if ts[-1] - ts[0] < 300 or series[0][1] <= 0:
            return None, 0.0
        cur = (series[-1][1] / series[0][1] - 1) * 100
    hist = []
    for i in range(len(series) - 1):
        c = change_at(i)
        if c is not None:
            hist.append(c)
    return cur, derive_norm(cur, hist, cfg.oi_ref_pct, cfg)


def composite_score(f: dict, cfg) -> tuple[float, dict]:
    """Взвешенный скор. > 0 — перегрев вверх, < 0 — перепроданность.

    Направленные признаки (доходность, отклонение, funding) идут со своим знаком.
    Признаки «активности» (OI, объём, волатильность) не имеют направления сами по себе,
    поэтому усиливают движение в ту сторону, куда идёт цена.
    """
    s = 1.0 if f["ret_z"] >= 0 else -1.0
    terms = {
        "ret": f["ret_z"],
        "dev": f["dev_z"],
        "funding": f["funding_z"],
        "oi": s * abs(f["oi_z"]),
        "volume": s * max(f["vol_z"], 0.0),
        "volatility": s * max(f["atr_z"], 0.0),
    }
    weights = {
        "ret": cfg.w_ret, "dev": cfg.w_dev, "funding": cfg.w_funding,
        "oi": cfg.w_oi, "volume": cfg.w_volume, "volatility": cfg.w_volatility,
    }
    total_w = sum(weights.values()) or 1.0
    score = sum(weights[k] * terms[k] for k in terms) / total_w
    return score, terms


OI_CTX_RU = {
    "new_longs": "рост на новых позициях (OI растёт) — толпа входит в лонг",
    "short_cover": "рост за счёт закрытия шортов (OI падает)",
    "new_shorts": "падение на новых позициях (OI растёт) — толпа входит в шорт",
    "long_cover": "падение за счёт закрытия лонгов (OI падает)",
    "flat": "OI почти не менялся",
}


def oi_context(ret_pct: float, oi_change_pct: float | None, min_oi_pct: float = 0.3) -> str | None:
    """Сочетание направления цены и изменения Open Interest за тот же час.

    Скор не меняет: знак OI сохраняется отдельно, чтобы по накопленной статистике
    проверить, какой из четырёх контекстов реально работает лучше.
    """
    if oi_change_pct is None:
        return None
    if abs(oi_change_pct) < min_oi_pct:
        return "flat"
    price_up, oi_up = ret_pct >= 0, oi_change_pct > 0
    return {(True, True): "new_longs", (True, False): "short_cover",
            (False, True): "new_shorts", (False, False): "long_cover"}[(price_up, oi_up)]


def classify_volume(vol_z: float, cfg) -> str:
    """HIGH — объём подтверждает движение, LOW — движение на тонком объёме."""
    if vol_z >= cfg.vol_z_high:
        return "HIGH"
    if vol_z <= cfg.vol_z_low:
        return "LOW"
    return "NORMAL"


def detect_regime(btc_ret4h: float, breadth: float, cfg) -> str:
    """Режим рынка по BTC за 4ч и доле растущих монет: up / down / flat."""
    if btc_ret4h >= cfg.regime_thr_pct and breadth >= 0.55:
        return "up"
    if btc_ret4h <= -cfg.regime_thr_pct and breadth <= 0.45:
        return "down"
    return "flat"


# ======================================================================
# БАЗА ДАННЫХ (PostgreSQL по DATABASE_URL, иначе SQLite-файл)
# ======================================================================
log = logging.getLogger("bot")

SCHEMA_SQLITE = """
CREATE TABLE IF NOT EXISTS signals (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ts REAL NOT NULL, symbol TEXT NOT NULL, side TEXT NOT NULL, category TEXT NOT NULL,
    score REAL, raw_score REAL, price REAL NOT NULL, vol_tag TEXT, regime TEXT, features TEXT,
    price_1h REAL, price_4h REAL, price_24h REAL, max_fav REAL, max_adv REAL
);
CREATE INDEX IF NOT EXISTS idx_signals_symbol_ts ON signals(symbol, ts);
CREATE TABLE IF NOT EXISTS snapshots (
    symbol TEXT NOT NULL, ts REAL NOT NULL, oi REAL, funding REAL,
    PRIMARY KEY (symbol, ts)
);
CREATE TABLE IF NOT EXISTS mutes (symbol TEXT PRIMARY KEY, until REAL NOT NULL);
CREATE TABLE IF NOT EXISTS blacklist (symbol TEXT PRIMARY KEY, added REAL NOT NULL);
CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL);
"""

SCHEMA_PG = """
CREATE TABLE IF NOT EXISTS signals (
    id BIGSERIAL PRIMARY KEY,
    ts DOUBLE PRECISION NOT NULL, symbol TEXT NOT NULL, side TEXT NOT NULL, category TEXT NOT NULL,
    score DOUBLE PRECISION, raw_score DOUBLE PRECISION, price DOUBLE PRECISION NOT NULL,
    vol_tag TEXT, regime TEXT, features TEXT,
    price_1h DOUBLE PRECISION, price_4h DOUBLE PRECISION, price_24h DOUBLE PRECISION,
    max_fav DOUBLE PRECISION, max_adv DOUBLE PRECISION
);
CREATE INDEX IF NOT EXISTS idx_signals_symbol_ts ON signals(symbol, ts);
CREATE TABLE IF NOT EXISTS snapshots (
    symbol TEXT NOT NULL, ts DOUBLE PRECISION NOT NULL, oi DOUBLE PRECISION, funding DOUBLE PRECISION,
    PRIMARY KEY (symbol, ts)
);
CREATE TABLE IF NOT EXISTS mutes (symbol TEXT PRIMARY KEY, until DOUBLE PRECISION NOT NULL);
CREATE TABLE IF NOT EXISTS blacklist (symbol TEXT PRIMARY KEY, added DOUBLE PRECISION NOT NULL);
CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL);
ALTER TABLE signals ADD COLUMN IF NOT EXISTS max_fav DOUBLE PRECISION;
ALTER TABLE signals ADD COLUMN IF NOT EXISTS max_adv DOUBLE PRECISION;
"""

# Колонка с ценой исхода и горизонт в секундах
HORIZONS = (("price_1h", 3600, "1h"), ("price_4h", 14400, "4h"), ("price_24h", 86400, "24h"))


class _PgRow:
    """Строка результата: доступ и по имени колонки, и по индексу (как sqlite3.Row)."""
    __slots__ = ("_v", "_i")

    def __init__(self, values, index):
        self._v = tuple(values)
        self._i = index

    def __getitem__(self, k):
        return self._v[self._i[k] if isinstance(k, str) else k]

    def __iter__(self):
        return iter(self._v)

    def __len__(self):
        return len(self._v)


def _pg_row_factory(cursor):
    cols = [c.name for c in cursor.description] if cursor.description else []
    index = {n: i for i, n in enumerate(cols)}
    return lambda values: _PgRow(values, index)


class _PgConn:
    """Тонкая обёртка над psycopg с интерфейсом, похожим на sqlite3.Connection.

    autocommit включён, поэтому commit() — пустая операция. При обрыве соединения
    (Render/Neon могут его закрывать) один раз переподключается и повторяет запрос.
    """

    def __init__(self, url: str):
        self._url = url
        self._conn = None
        self._connect()

    def _connect(self) -> None:
        self._conn = psycopg.connect(self._url, autocommit=True, connect_timeout=15,
                                     row_factory=_pg_row_factory)

    def _run(self, fn):
        try:
            return fn()
        except (psycopg.OperationalError, psycopg.InterfaceError):
            log.warning("Соединение с PostgreSQL потеряно, переподключаюсь")
            try:
                self._conn.close()
            except Exception:
                pass
            self._connect()
            return fn()

    def execute(self, sql: str, params=()):
        sql = sql.replace("?", "%s")

        def go():
            cur = self._conn.cursor()
            cur.execute(sql, params if params else None)
            return cur
        return self._run(go)

    def executemany(self, sql: str, rows) -> None:
        sql = sql.replace("?", "%s")

        def go():
            cur = self._conn.cursor()
            cur.executemany(sql, rows)
            return cur
        self._run(go)

    def executescript(self, script: str) -> None:
        for stmt in script.split(";"):
            if stmt.strip():
                self.execute(stmt)

    def commit(self) -> None:
        pass

    def close(self) -> None:
        self._conn.close()


class Database:
    def __init__(self, path: str, url: str = ""):
        self.fee_pct = 0.0  # круговая комиссия в % (задаётся из конфига), учитывается в статистике
        self._lock = threading.RLock()
        self.pg = bool(url)
        if self.pg:
            if psycopg is None:
                raise SystemExit("DATABASE_URL задан, но не установлен psycopg (см. requirements.txt).")
            self._conn = _PgConn(url)
            with self._lock:
                self._conn.executescript(SCHEMA_PG)
            log.info("База данных: PostgreSQL (данные сохраняются между деплоями)")
        else:
            self._conn = sqlite3.connect(path, check_same_thread=False, timeout=30)
            self._conn.row_factory = sqlite3.Row
            with self._lock:
                self._conn.execute("PRAGMA journal_mode=WAL")
                self._conn.executescript(SCHEMA_SQLITE)
                have = {r["name"] for r in self._conn.execute("PRAGMA table_info(signals)").fetchall()}
                for col in ("max_fav", "max_adv"):
                    if col not in have:
                        self._conn.execute(f"ALTER TABLE signals ADD COLUMN {col} REAL")
                self._conn.commit()
            if os.getenv("RENDER"):
                log.warning("База — SQLite-файл: на Render он стирается при каждом деплое. "
                            "Задайте DATABASE_URL (PostgreSQL), чтобы история сохранялась.")
            else:
                log.info("База данных: SQLite (%s)", path)

    def close(self) -> None:
        with self._lock:
            self._conn.close()

    def _upsert(self, table: str, cols: tuple, pk: tuple) -> str:
        """INSERT с заменой по первичному ключу — для SQLite и PostgreSQL."""
        ph = ",".join("?" * len(cols))
        names = ",".join(cols)
        if not self.pg:
            return f"INSERT OR REPLACE INTO {table} ({names}) VALUES ({ph})"
        upd = ",".join(f"{c}=EXCLUDED.{c}" for c in cols if c not in pk)
        return (f"INSERT INTO {table} ({names}) VALUES ({ph}) "
                f"ON CONFLICT ({','.join(pk)}) DO UPDATE SET {upd}")

    # ---------- сигналы ----------
    def add_signal(self, s) -> int:
        sql = ("INSERT INTO signals (ts, symbol, side, category, score, raw_score, price,"
               " vol_tag, regime, features) VALUES (?,?,?,?,?,?,?,?,?,?)")
        params = (s.ts, s.symbol, s.side, s.category, s.score, s.raw_score, s.price,
                  s.vol_tag, s.regime, json.dumps(s.features, default=str))
        with self._lock:
            if self.pg:
                row = self._conn.execute(sql + " RETURNING id", params).fetchone()
                return int(row[0])
            cur = self._conn.execute(sql, params)
            self._conn.commit()
            return cur.lastrowid

    def last_signal_times(self) -> dict[str, float]:
        with self._lock:
            rows = self._conn.execute("SELECT symbol, MAX(ts) AS t FROM signals GROUP BY symbol").fetchall()
        return {r["symbol"]: r["t"] for r in rows}

    def signals_since(self, since_ts: float):
        with self._lock:
            return self._conn.execute(
                "SELECT symbol, side, price, price_1h, price_4h FROM signals WHERE ts >= ? ORDER BY ts",
                (since_ts,),
            ).fetchall()

    def count_signals(self) -> int:
        with self._lock:
            return self._conn.execute("SELECT COUNT(*) FROM signals").fetchone()[0]

    def fill_outcomes(self, now: float, prices: dict[str, float], tolerance: float = 300.0) -> int:
        """Проставляет цену через 1ч/4ч/24ч после сигнала.

        Цена берётся только если момент горизонта пройден не более чем на tolerance секунд
        (по умолчанию 5 минут), иначе исход точным не считается и пишется 0.0
        («пропущено», в статистике игнорируется) — так статистика не искажается
        поздними замерами, например после простоя бота.
        """
        n = 0
        with self._lock:
            for col, sec, _ in HORIZONS:
                due = self._conn.execute(
                    f"SELECT id, symbol, ts FROM signals WHERE {col} IS NULL AND ts <= ?",
                    (now - sec,),
                ).fetchall()
                for r in due:
                    if now - r["ts"] - sec > tolerance:
                        val = 0.0
                    else:
                        val = prices.get(r["symbol"])
                        if not val:
                            continue
                    self._conn.execute(f"UPDATE signals SET {col}=? WHERE id=?", (val, r["id"]))
                    n += 1
            self._conn.commit()
        return n

    def update_excursions(self, now: float, prices: dict[str, float]) -> None:
        """Отслеживает за 24 часа после сигнала максимальный ход в пользу (MFE) и против (MAE), в %."""
        with self._lock:
            rows = self._conn.execute(
                "SELECT id, symbol, side, price, max_fav, max_adv FROM signals WHERE ts >= ?",
                (now - 86400 - 600,),
            ).fetchall()
            for r in rows:
                p = prices.get(r["symbol"])
                if not p or not r["price"]:
                    continue
                mv = (p / r["price"] - 1) * 100
                if r["side"] == "SHORT":
                    mv = -mv
                fav = max(r["max_fav"] or 0.0, mv)
                adv = min(r["max_adv"] or 0.0, mv)
                if fav != r["max_fav"] or adv != r["max_adv"]:
                    self._conn.execute("UPDATE signals SET max_fav=?, max_adv=? WHERE id=?",
                                       (fav, adv, r["id"]))
            self._conn.commit()

    def compute_stats(self):
        """Статистика: (counts, stats).

        counts[side] — число сигналов; stats[(side, tag, horizon)] = (n, winrate%, avg%, median%).
        Ход считается с учётом круговой комиссии fee_pct: SHORT — цена упала, LONG — выросла.
        """
        with self._lock:
            rows = self._conn.execute(
                "SELECT side, vol_tag, price, price_1h, price_4h, price_24h FROM signals"
            ).fetchall()
        counts = {"SHORT": 0, "LONG": 0}
        for r in rows:
            counts[r["side"]] = counts.get(r["side"], 0) + 1
        stats = {}
        for side in ("SHORT", "LONG"):
            for tag in ("ALL", "HIGH", "NORMAL", "LOW"):
                for col, _, hz in HORIZONS:
                    moves = []
                    for r in rows:
                        if r["side"] != side or (tag != "ALL" and r["vol_tag"] != tag):
                            continue
                        p1 = r[col]
                        if not p1 or p1 <= 0 or not r["price"]:
                            continue
                        mv = (p1 / r["price"] - 1) * 100
                        moves.append((-mv if side == "SHORT" else mv) - self.fee_pct)
                    if moves:
                        wins = sum(1 for m in moves if m > 0)
                        stats[(side, tag, hz)] = (
                            len(moves), 100.0 * wins / len(moves),
                            sum(moves) / len(moves), statistics.median(moves),
                        )
        return counts, stats

    def compute_excursion_stats(self) -> dict[str, tuple[int, float, float]]:
        """{side: (n, средний MFE %, средний MAE %)} по сигналам, у которых есть замеры."""
        with self._lock:
            rows = self._conn.execute(
                "SELECT side, max_fav, max_adv FROM signals WHERE max_fav IS NOT NULL"
            ).fetchall()
        acc: dict[str, list] = {}
        for r in rows:
            acc.setdefault(r["side"], []).append((r["max_fav"], r["max_adv"] or 0.0))
        return {side: (len(v), sum(a for a, _ in v) / len(v), sum(b for _, b in v) / len(v))
                for side, v in acc.items()}

    def compute_ctx_stats(self, col: str = "price_4h", hz: str = "4h"):
        """Результат по контексту OI: {(side, ctx): (n, winrate%, avg%)} с учётом комиссии."""
        with self._lock:
            rows = self._conn.execute(
                f"SELECT side, price, {col} AS p1, features FROM signals WHERE {col} > 0"
            ).fetchall()
        acc: dict[tuple, list] = {}
        for r in rows:
            try:
                ctx = json.loads(r["features"] or "{}").get("oi_ctx")
            except ValueError:
                ctx = None
            if not ctx or not r["price"]:
                continue
            mv = (r["p1"] / r["price"] - 1) * 100
            acc.setdefault((r["side"], ctx), []).append((-mv if r["side"] == "SHORT" else mv) - self.fee_pct)
        return {k: (len(v), 100.0 * sum(1 for m in v if m > 0) / len(v), sum(v) / len(v))
                for k, v in acc.items()}

    # ---------- снимки OI / funding ----------
    def save_snapshots(self, rows: list[tuple]) -> None:
        """rows: [(symbol, ts, oi, funding)]"""
        if not rows:
            return
        with self._lock:
            self._conn.executemany(self._upsert("snapshots", ("symbol", "ts", "oi", "funding"),
                                                ("symbol", "ts")), rows)
            self._conn.commit()

    def get_snapshots(self, since_ts: float) -> dict[str, list[tuple[float, float, float | None]]]:
        with self._lock:
            rows = self._conn.execute(
                "SELECT symbol, ts, oi, funding FROM snapshots WHERE ts >= ? ORDER BY symbol, ts",
                (since_ts,),
            ).fetchall()
        out: dict[str, list] = {}
        for r in rows:
            out.setdefault(r["symbol"], []).append((r["ts"], r["oi"], r["funding"]))
        return out

    def prune_snapshots(self, before_ts: float) -> None:
        with self._lock:
            self._conn.execute("DELETE FROM snapshots WHERE ts < ?", (before_ts,))
            self._conn.commit()

    # ---------- mute / чёрный список ----------
    def set_mute(self, symbol: str, until_ts: float) -> None:
        with self._lock:
            self._conn.execute(self._upsert("mutes", ("symbol", "until"), ("symbol",)), (symbol, until_ts))
            self._conn.commit()

    def remove_mute(self, symbol: str) -> None:
        with self._lock:
            self._conn.execute("DELETE FROM mutes WHERE symbol=?", (symbol,))
            self._conn.commit()

    def get_active_mutes(self, now: float) -> dict[str, float]:
        with self._lock:
            self._conn.execute("DELETE FROM mutes WHERE until <= ?", (now,))
            self._conn.commit()
            rows = self._conn.execute("SELECT symbol, until FROM mutes").fetchall()
        return {r["symbol"]: r["until"] for r in rows}

    def add_blacklist(self, symbol: str, now: float) -> None:
        with self._lock:
            self._conn.execute(self._upsert("blacklist", ("symbol", "added"), ("symbol",)), (symbol, now))
            self._conn.commit()

    def remove_blacklist(self, symbol: str) -> bool:
        with self._lock:
            cur = self._conn.execute("DELETE FROM blacklist WHERE symbol=?", (symbol,))
            self._conn.commit()
            return cur.rowcount > 0

    def get_blacklist(self) -> set[str]:
        with self._lock:
            rows = self._conn.execute("SELECT symbol FROM blacklist").fetchall()
        return {r["symbol"] for r in rows}

    # ---------- настройки (/set) ----------
    def save_setting(self, key: str, value) -> None:
        with self._lock:
            self._conn.execute(self._upsert("settings", ("key", "value"), ("key",)), (key, str(value)))
            self._conn.commit()

    def load_settings(self) -> dict[str, str]:
        with self._lock:
            rows = self._conn.execute("SELECT key, value FROM settings").fetchall()
        return {r["key"]: r["value"] for r in rows}


# ======================================================================
# СКАНЕР И СИГНАЛЫ
# ======================================================================

log = logging.getLogger("bot")

BTC = "BTC-USDT"


@dataclass
class Signal:
    symbol: str
    side: str            # SHORT | LONG
    category: str        # OVERHEAT | OVERSOLD
    score: float         # итоговый скор после поправок на рынок
    raw_score: float     # взвешенный скор по признакам монеты
    price: float
    vol_tag: str         # HIGH | NORMAL | LOW
    regime: str          # up | down | flat
    rs_pct: float        # сила относительно BTC за 4ч, п.п.
    against_regime: bool
    features: dict
    ts: float = field(default_factory=time.time)
    id: int | None = None


@dataclass
class ScannerState:
    """Состояние сканера для команды /status."""
    last_scan_ts: float = 0.0
    last_scan_sec: float = 0.0
    regime: str = "flat"
    btc_ret4h: float = 0.0
    breadth: float = 0.5
    n_candidates: int = 0
    fail_count: int = 0
    last_error: str = ""


def is_junk(symbol: str, cfg) -> bool:
    """Стейблкоины, токенизированные акции/сырьё, леверидж-токены."""
    base = symbol.rsplit("-", 1)[0]
    return base in cfg.stable_bases or bool(cfg.junk_re.search(base))


class Scanner:
    def __init__(self, cfg, client: BingXClient, db, notifier, state: ScannerState):
        self.cfg = cfg
        self.client = client
        self.db = db
        self.notifier = notifier  # объект с async send_signal(sig) и send_text(text)
        self.state = state
        self._contracts: dict = {}
        self._contracts_ts = 0.0
        self._last_prune = 0.0

    # ---------- главный цикл ----------
    async def run(self) -> None:
        while True:
            t0 = time.monotonic()
            try:
                await self.scan_once()
                self.state.fail_count = 0
            except asyncio.CancelledError:
                raise
            except Exception as e:  # сканер не должен падать из-за одной ошибки
                self.state.fail_count += 1
                self.state.last_error = f"{type(e).__name__}: {e}"
                log.exception("Ошибка скана (подряд: %s)", self.state.fail_count)
                if self.state.fail_count == 5:
                    await self._safe_text(f"⚠️ Сканер 5 раз подряд не может получить данные BingX.\n"
                                          f"Последняя ошибка: {self.state.last_error}")
            elapsed = time.monotonic() - t0
            await asyncio.sleep(max(5.0, self.cfg.scan_interval_sec - elapsed))

    async def _safe_text(self, text: str) -> None:
        try:
            await self.notifier.send_text(text)
        except Exception:
            log.exception("Не удалось отправить сообщение")

    # ---------- один проход ----------
    async def scan_once(self) -> None:
        cfg = self.cfg
        t0 = time.monotonic()
        now = time.time()

        await self._refresh_contracts(now)
        tickers = await self.client.get_tickers()
        candidates = self._select_candidates(tickers, now)
        if not candidates:
            log.warning("Нет кандидатов: проверьте MIN_VOLUME_USDT и фильтры")
            return
        symbols = [t.symbol for t in candidates]
        fetch_list = list(dict.fromkeys([BTC] + symbols))  # BTC нужен для контекста

        try:
            funding_all = await self.client.get_funding_all()
        except BingXError as e:
            log.warning("Funding по всем монетам недоступен: %s", e)
            funding_all = {}

        history = self.db.get_snapshots(now - cfg.snapshot_keep_hours * 3600)
        sem = asyncio.Semaphore(cfg.concurrency)

        async def fetch(sym: str):
            async with sem:
                res = await asyncio.gather(
                    self.client.get_klines(sym, cfg.kline_interval, cfg.kline_limit),
                    self.client.get_open_interest(sym),
                    return_exceptions=True,
                )
                candles = None if isinstance(res[0], BaseException) else res[0]
                oi = None if isinstance(res[1], BaseException) else res[1]
                if isinstance(res[0], BaseException):
                    log.debug("%s: свечи не получены: %s", sym, res[0])
                fr = funding_all.get(sym)
                if fr is None:  # запасной вариант: funding по одной монете
                    try:
                        fr = (await self.client.get_funding(sym)).get(sym)
                    except Exception:
                        fr = None
                return sym, candles, oi, fr

        results = await asyncio.gather(*(fetch(s) for s in fetch_list))

        # --- признаки по каждой монете ---
        feats: dict[str, dict] = {}
        snap_rows = []
        for sym, candles, oi, fr in results:
            rate = fr[0] if fr else None
            if oi or rate is not None:
                snap_rows.append((sym, now, oi, rate))  # копим историю OI/funding
            if not candles:
                continue
            f = compute_price_features(candles, cfg)
            if f is None:
                continue
            series = history.get(sym, [])
            oi_series = [(t, o) for t, o, _ in series if o]
            if oi:
                oi_series.append((now, oi))
            f["oi_change_pct"], f["oi_z"] = oi_change_features(oi_series, 3600, cfg)
            fund_hist = [r for _, _, r in series if r is not None]
            f["funding"] = rate
            f["funding_z"] = derive_norm(rate, fund_hist, cfg.funding_ref, cfg) if rate is not None else 0.0
            # Явно помечаем отсутствующие данные: нулевой признак не должен выглядеть как подтверждение
            missing = []
            if not oi:
                missing.append("OI")
            elif f["oi_change_pct"] is None:
                missing.append("история OI (копится)")
            if rate is None:
                missing.append("funding")
            f["missing"] = missing
            f["oi_ctx"] = oi_context(f["ret_pct"], f["oi_change_pct"])
            feats[sym] = f
        self.db.save_snapshots(snap_rows)

        # --- контекст рынка: BTC и «ширина» рынка ---
        btc = feats.get(BTC)
        btc_ret4h = btc["ret4h_pct"] if btc else 0.0
        scanned = [feats[s] for s in symbols if s in feats]
        breadth = (sum(1 for f in scanned if f["ret4h_pct"] > 0) / len(scanned)) if scanned else 0.5
        regime = detect_regime(btc_ret4h, breadth, cfg)

        # --- оценка и отбор сигналов ---
        mutes = self.db.get_active_mutes(now)
        last_sig = self.db.last_signal_times()
        found: list[Signal] = []
        for sym in symbols:
            f = feats.get(sym)
            if not f or sym in mutes:
                continue
            if now - last_sig.get(sym, 0.0) < cfg.cooldown_min * 60:
                continue
            sig = self._evaluate(sym, f, regime, btc_ret4h, now)
            if sig:
                found.append(sig)
        found.sort(key=lambda s: abs(s.score), reverse=True)

        for sig in found[:cfg.max_signals_per_scan]:
            sig.id = self.db.add_signal(sig)
            log.info("СИГНАЛ %s %s score=%.2f vol=%s", sig.symbol, sig.side, sig.score, sig.vol_tag)
            try:
                await self.notifier.send_signal(sig)
            except Exception:
                log.exception("Не удалось отправить сигнал %s", sig.symbol)

        # --- исходы прошлых сигналов (цена через 1ч / 4ч / 24ч) ---
        prices = {s: t.last for s, t in tickers.items()}
        self.db.fill_outcomes(now, prices, tolerance=max(300.0, cfg.scan_interval_sec * 2.5))
        self.db.update_excursions(now, prices)  # MFE / MAE за первые 24 часа

        if now - self._last_prune > 3600:
            self.db.prune_snapshots(now - cfg.snapshot_keep_hours * 3600)
            self._last_prune = now

        st = self.state
        st.last_scan_ts, st.last_scan_sec = now, time.monotonic() - t0
        st.regime, st.btc_ret4h, st.breadth, st.n_candidates = regime, btc_ret4h, breadth, len(symbols)
        log.info("Скан: %d монет, режим=%s (BTC 4ч %+.2f%%, ширина %.0f%%), сигналов=%d, %.1fс",
                 len(symbols), regime, btc_ret4h, breadth * 100, len(found), st.last_scan_sec)

    # ---------- оценка одной монеты ----------
    def _evaluate(self, sym: str, f: dict, regime: str, btc_ret4h: float, now: float) -> Signal | None:
        cfg = self.cfg
        raw, terms = composite_score(f, cfg)

        # Сила относительно BTC: монета сильно обгоняет BTC -> перегрев «собственный», а не рыночный
        rs_pct = f["ret4h_pct"] - btc_ret4h
        score = raw + cfg.rs_weight * max(-3.0, min(3.0, rs_pct / cfg.rs_ref_pct))

        # Сигнал против режима рынка (short в росте / long в падении) — штраф
        against = (regime == "up" and score > 0) or (regime == "down" and score < 0)
        if against:
            score *= cfg.regime_penalty

        if abs(score) < cfg.score_threshold:
            return None
        sgn = 1.0 if score > 0 else -1.0
        # Защита: цена и отклонение от SMA должны реально быть в сторону сигнала
        if f["ret_z"] * sgn <= 0.5 or f["dev_z"] * sgn <= 0.5:
            return None

        f = dict(f, terms=terms)
        return Signal(
            symbol=sym,
            side="SHORT" if sgn > 0 else "LONG",
            category="OVERHEAT" if sgn > 0 else "OVERSOLD",
            score=score, raw_score=raw, price=f["price"],
            vol_tag=classify_volume(f["vol_z"], cfg),
            regime=regime, rs_pct=rs_pct, against_regime=against,
            features=f, ts=now,
        )

    # ---------- фильтры качества ----------
    async def _refresh_contracts(self, now: float) -> None:
        if self._contracts and now - self._contracts_ts < 3600:
            return
        try:
            self._contracts = {c.symbol: c for c in await self.client.get_contracts()}
            self._contracts_ts = now
        except BingXError as e:
            log.warning("Список контрактов недоступен: %s", e)
            self._contracts_ts = now - 3000  # повторить через ~10 минут

    def _select_candidates(self, tickers: dict[str, Ticker], now: float) -> list[Ticker]:
        cfg = self.cfg
        blacklist = self.db.get_blacklist()
        out = []
        for sym, t in tickers.items():
            if not sym.endswith("-USDT") or sym in blacklist or is_junk(sym, cfg):
                continue
            c = self._contracts.get(sym)
            if self._contracts:
                if c is None or not c.online:
                    continue
                # возраст листинга (если биржа отдала дату запуска)
                if cfg.min_listing_days > 0 and c.launch_ts > 0 \
                        and now - c.launch_ts < cfg.min_listing_days * 86400:
                    continue
            if t.quote_volume < cfg.min_volume_usdt:
                continue
            if t.bid > 0 and t.ask > 0 and (t.ask - t.bid) / t.last * 100 > cfg.max_spread_pct:
                continue  # слишком широкий спред — мусорный рынок
            out.append(t)
        out.sort(key=lambda t: t.quote_volume, reverse=True)
        return out[:cfg.top_n]


# ======================================================================
# TELEGRAM-БОТ
# ======================================================================
log = logging.getLogger("bot")

REGIME_RU = {"up": "рост ↑", "down": "падение ↓", "flat": "флэт →"}
VOL_RU = {"HIGH": "🟢 высокий", "NORMAL": "⚪ обычный", "LOW": "🔴 низкий"}

# Подсказка по сочетанию «категория + объём»
HINTS = {
    ("OVERHEAT", "HIGH"): "импульс подтверждён объёмом — против него рано, ждать признаков разворота",
    ("OVERHEAT", "LOW"): "рост на тонком объёме — откат вероятнее (кандидат в short)",
    ("OVERSOLD", "HIGH"): "падение на большом объёме — возможна капитуляция или продолжение, ждать стабилизации",
    ("OVERSOLD", "LOW"): "падение без объёма — отскок вероятнее (кандидат в long)",
}


def fmt_price(p: float) -> str:
    if p >= 1000:
        return f"{p:,.2f}"
    if p >= 1:
        return f"{p:.4f}"
    if p >= 0.01:
        return f"{p:.5f}"
    return f"{p:.8f}"


def format_signal(s: Signal) -> str:
    f = s.features
    if s.category == "OVERHEAT":
        head = "🔥 <b>ПЕРЕГРЕВ</b> · потенциальный SHORT"
    else:
        head = "🧊 <b>ПЕРЕПРОДАННОСТЬ</b> · потенциальный LONG"
    lines = [
        head,
        f"<b>{html.escape(s.symbol)}</b> · {fmt_price(s.price)}",
        f"Скор: <b>{s.score:+.2f}</b> (по монете {s.raw_score:+.2f})",
        "",
        f"📦 Объём: {VOL_RU[s.vol_tag]} (z {f['vol_z']:+.1f}, перцентиль {f['vol_pctile']:.0f})",
    ]
    hint = HINTS.get((s.category, s.vol_tag))
    if hint:
        lines.append(f"   → {hint}")
    lines += [
        f"📈 Цена: 1ч {f['ret_pct']:+.2f}% (z {f['ret_z']:+.1f}) · 4ч {f['ret4h_pct']:+.2f}%",
        f"📐 От SMA 12ч: {f['dev_pct']:+.2f}% (z {f['dev_z']:+.1f}) · ATR {f['atr_pct']:.2f}% (z {f['atr_z']:+.1f})",
    ]
    if f.get("funding") is not None:
        lines.append(f"💸 Funding: {f['funding'] * 100:+.4f}% (z {f['funding_z']:+.1f})")
    if f.get("oi_change_pct") is not None:
        lines.append(f"📊 ΔOI 1ч: {f['oi_change_pct']:+.2f}% (z {f['oi_z']:+.1f})")
        if f.get("oi_ctx"):
            lines.append(f"   → {OI_CTX_RU[f['oi_ctx']]}")
    if f.get("missing"):
        lines.append("ℹ️ Нет данных: " + ", ".join(f["missing"]) + " — эти признаки не учтены")
    lines.append(f"🌍 К BTC за 4ч: {s.rs_pct:+.2f} п.п. · рынок: {REGIME_RU[s.regime]}")
    if s.against_regime:
        lines.append("⚠️ Сигнал против режима рынка — риск выше")
    return "\n".join(lines)


def format_stats(db) -> str:
    total = db.count_signals()
    if total == 0:
        return "Пока нет сигналов — статистика появится после первых."
    counts, stats = db.compute_stats()
    lines = [f"📊 <b>Статистика сигналов</b> (всего: {total})",
             f"Win = цена пошла в сторону сигнала с учётом комиссии {db.fee_pct:.2f}% (круг).",
             "Формат: винрейт / средний ход (n)", ""]
    titles = {"SHORT": "🔥 Перегрев → SHORT", "LONG": "🧊 Перепроданность → LONG"}
    tags = (("ALL", "все"), ("HIGH", "🟢 объём выс."), ("NORMAL", "⚪ объём обыч."), ("LOW", "🔴 объём низк."))
    for side in ("SHORT", "LONG"):
        lines.append(f"<b>{titles[side]}</b> — сигналов: {counts.get(side, 0)}")
        for tag, label in tags:
            parts = []
            for hz in ("1h", "4h", "24h"):
                v = stats.get((side, tag, hz))
                if v:
                    n, win, avg, _ = v
                    parts.append(f"{hz}: {win:.0f}% / {avg:+.2f}% ({n})")
            if parts:
                lines.append(f"  {label}: " + " · ".join(parts))
        lines.append("")

    exc = db.compute_excursion_stats()
    if exc:
        lines.append("<b>Ход за 24ч после сигнала</b> (в % от цены сигнала)")
        for side in ("SHORT", "LONG"):
            if side in exc:
                n, mfe, mae = exc[side]
                lines.append(f"  {side}: в пользу в среднем {mfe:+.2f}% · против {mae:+.2f}% ({n})")
        lines.append("")

    ctx = db.compute_ctx_stats()
    if ctx:
        lines.append("<b>По контексту OI</b> (через 4ч: винрейт / средний ход, n)")
        names = {"new_longs": "цена↑ OI↑", "short_cover": "цена↑ OI↓",
                 "new_shorts": "цена↓ OI↑", "long_cover": "цена↓ OI↓", "flat": "OI ≈ 0"}
        for (side, c), (n, win, avg) in sorted(ctx.items()):
            lines.append(f"  {side} · {names.get(c, c)}: {win:.0f}% / {avg:+.2f}% ({n})")
    return "\n".join(lines).strip()


def owner_only(fn):
    """Команды доступны только владельцу (chat_id из .env); чужие сообщения игнорируются."""
    @functools.wraps(fn)
    async def wrapper(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        chat = update.effective_chat
        if chat is None or chat.id != self.cfg.chat_id:
            log.warning("Отклонён доступ: chat_id=%s", chat.id if chat else None)
            return
        return await fn(self, update, context)
    return wrapper


class TelegramBot:
    def __init__(self, cfg, db, state: ScannerState):
        self.cfg, self.db, self.state = cfg, db, state
        self.vk = None  # VKPoster, подставляется в run()
        self.app = Application.builder().token(cfg.bot_token).build()
        for name, handler in (
            ("start", self.cmd_start), ("stats", self.cmd_stats), ("status", self.cmd_status),
            ("mute", self.cmd_mute), ("unmute", self.cmd_unmute), ("set", self.cmd_set),
            ("blacklist", self.cmd_blacklist), ("unban", self.cmd_unban),
            ("vkpreview", self.cmd_vkpreview), ("vkpost", self.cmd_vkpost),
        ):
            self.app.add_handler(CommandHandler(name, handler))
        self.app.add_handler(CallbackQueryHandler(self.on_button))
        self.app.add_error_handler(self.on_error)

    # ---------- жизненный цикл ----------
    async def start(self) -> None:
        await self.app.initialize()
        await self.app.start()
        await self.app.updater.start_polling(drop_pending_updates=True)
        await self.app.bot.set_my_commands([
            BotCommand("stats", "статистика сигналов"),
            BotCommand("status", "состояние сканера"),
            BotCommand("mute", "mute монеты: /mute SYMBOL [часы]"),
            BotCommand("unmute", "снять mute"),
            BotCommand("blacklist", "чёрный список"),
            BotCommand("unban", "убрать из чёрного списка"),
            BotCommand("set", "изменить пороги"),
            BotCommand("vkpreview", "показать пост для ВК: /vkpreview [morning|evening]"),
            BotCommand("vkpost", "опубликовать пост в ВК сейчас"),
        ])
        if not self.cfg.chat_id:
            log.warning("CHAT_ID не задан: напишите боту /start, он покажет ваш chat_id")

    async def stop(self) -> None:
        for step in (self.app.updater.stop, self.app.stop, self.app.shutdown):
            try:
                await step()
            except Exception:
                log.debug("Ошибка при остановке бота", exc_info=True)

    # ---------- отправка ----------
    def _keyboard(self, symbol: str, blacklisted: bool = False) -> InlineKeyboardMarkup:
        base = symbol.rsplit("-", 1)[0]
        links = [
            InlineKeyboardButton("📈 TradingView", url=f"https://www.tradingview.com/chart/?symbol=BINGX:{base}USDT.P"),
            InlineKeyboardButton("🔗 BingX", url=f"https://bingx.com/en/perpetual/{symbol}/"),
        ]
        if blacklisted:
            actions = [InlineKeyboardButton("↩️ Убрать из ЧС", callback_data=f"unbl:{symbol}")]
        else:
            actions = [
                InlineKeyboardButton(f"🔇 Mute {self.cfg.mute_default_hours}ч", callback_data=f"mute:{symbol}"),
                InlineKeyboardButton("🚫 В чёрный список", callback_data=f"bl:{symbol}"),
            ]
        return InlineKeyboardMarkup([links, actions])

    async def send_text(self, text: str, reply_markup=None) -> None:
        if not self.cfg.chat_id:
            log.info("CHAT_ID не задан, сообщение не отправлено: %s", text[:80])
            return
        attempts = 5
        for attempt in range(1, attempts + 1):
            try:
                await self.app.bot.send_message(
                    chat_id=self.cfg.chat_id, text=text, parse_mode=ParseMode.HTML,
                    reply_markup=reply_markup,
                )
                return
            except RetryAfter as e:  # лимит Telegram — ждём сколько просят
                ra = e.retry_after
                wait = (ra.total_seconds() if hasattr(ra, "total_seconds") else float(ra)) + 1
                log.warning("Telegram: лимит, попытка %d/%d, жду %.0f с", attempt, attempts, wait)
                await asyncio.sleep(wait)
            except (TimedOut, NetworkError) as e:
                log.warning("Telegram: сбой сети, попытка %d/%d: %s: %s",
                            attempt, attempts, type(e).__name__, e)
                await asyncio.sleep(2 * attempt)
        log.error("Не удалось отправить сообщение после %d попыток", attempts)

    async def send_signal(self, sig: Signal) -> None:
        await self.send_text(format_signal(sig), self._keyboard(sig.symbol))

    # ---------- команды ----------
    async def cmd_start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        chat = update.effective_chat
        if chat.id != self.cfg.chat_id:
            if not self.cfg.chat_id:
                await update.message.reply_text(
                    f"Ваш chat_id: {chat.id}\nВпишите его в .env как CHAT_ID и перезапустите бота.")
            else:
                await update.message.reply_text("Это приватный бот.")
            return
        await update.message.reply_html(
            "👋 <b>Бот сигналов BingX Futures</b>\n"
            "Сканирую топ монет по объёму и присылаю:\n"
            "🔥 перегрев → потенциальный short\n"
            "🧊 перепроданность → потенциальный long\n"
            "К каждому сигналу указан объём (высокий/низкий) — это важно для интерпретации.\n\n"
            "/stats — статистика сигналов\n"
            "/status — состояние сканера и режим рынка\n"
            "/mute SYMBOL [часы] · /unmute SYMBOL\n"
            "/blacklist [SYMBOL] · /unban SYMBOL\n"
            "/set — посмотреть и изменить пороги\n\n"
            "<i>Это аналитические сигналы, а не финансовая рекомендация.</i>"
        )

    @owner_only
    async def cmd_stats(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        await update.message.reply_html(format_stats(self.db))

    @owner_only
    async def cmd_status(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        st = self.state
        if not st.last_scan_ts:
            await update.message.reply_text("Первый скан ещё не завершён.")
            return
        ago = int(time.time() - st.last_scan_ts)
        text = (f"🟢 Последний скан: {ago}с назад (длился {st.last_scan_sec:.0f}с)\n"
                f"Монет в скане: {st.n_candidates}\n"
                f"Режим рынка: {REGIME_RU[st.regime]} (BTC 4ч {st.btc_ret4h:+.2f}%, "
                f"растёт {st.breadth * 100:.0f}% монет)\n"
                f"Ошибок подряд: {st.fail_count}")
        if st.last_error:
            text += f"\nПоследняя ошибка: {st.last_error}"
        await update.message.reply_text(text)

    @owner_only
    async def cmd_mute(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not context.args:
            await update.message.reply_text("Использование: /mute SYMBOL [часы]\nНапример: /mute PEPE 12")
            return
        sym = normalize_symbol(context.args[0])
        try:
            hours = float(context.args[1].replace(",", ".")) if len(context.args) > 1 else self.cfg.mute_default_hours
        except ValueError:
            await update.message.reply_text("Часы должны быть числом.")
            return
        self.db.set_mute(sym, time.time() + hours * 3600)
        await update.message.reply_text(f"🔇 {sym} отключена на {hours:g} ч.")

    @owner_only
    async def cmd_unmute(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not context.args:
            mutes = self.db.get_active_mutes(time.time())
            text = "Сейчас в mute:\n" + "\n".join(
                f"• {s} — ещё {max(0, (u - time.time()) / 3600):.1f} ч" for s, u in mutes.items()
            ) if mutes else "Mute-список пуст."
            await update.message.reply_text(text)
            return
        sym = normalize_symbol(context.args[0])
        self.db.remove_mute(sym)
        await update.message.reply_text(f"🔊 {sym}: mute снят.")

    @owner_only
    async def cmd_blacklist(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if context.args:
            sym = normalize_symbol(context.args[0])
            self.db.add_blacklist(sym, time.time())
            await update.message.reply_text(f"🚫 {sym} добавлена в чёрный список.")
            return
        bl = sorted(self.db.get_blacklist())
        await update.message.reply_text(
            "Чёрный список:\n" + "\n".join(f"• {s}" for s in bl) + "\n\nУбрать: /unban SYMBOL"
            if bl else "Чёрный список пуст. Добавить: /blacklist SYMBOL")

    @owner_only
    async def cmd_unban(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not context.args:
            await update.message.reply_text("Использование: /unban SYMBOL")
            return
        sym = normalize_symbol(context.args[0])
        ok = self.db.remove_blacklist(sym)
        await update.message.reply_text(f"↩️ {sym} убрана из чёрного списка." if ok else f"{sym} не было в списке.")

    @owner_only
    async def cmd_set(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        args = context.args
        if len(args) < 2:
            lines = ["⚙️ <b>Текущие параметры</b>"]
            for key, (_, lo, hi, desc) in SETTABLE.items():
                lines.append(f"<code>{key}</code> = <b>{getattr(self.cfg, key)}</b> — {desc}")
            lines.append("\nИзменить: <code>/set score_threshold 2.2</code>")
            await update.message.reply_html("\n".join(lines))
            return
        key, raw = args[0].lower(), args[1]
        try:
            val = set_param(self.cfg, key, raw)
        except ValueError as e:
            await update.message.reply_text(f"❌ {e}")
            return
        self.db.save_setting(key, val)  # сохраняется и переживёт перезапуск
        await update.message.reply_html(f"✅ <code>{key}</code> = <b>{val}</b>")

    async def _vk_cmd(self, update: Update, context: ContextTypes.DEFAULT_TYPE, publish: bool):
        if not self.vk:
            await update.message.reply_text("ВК не настроен: задайте VK_TOKEN и VK_GROUP в .env")
            return
        kind = context.args[0] if context.args and context.args[0] in ("morning", "evening") else "morning"
        try:
            text = await self.vk.build(kind)
            if publish:
                await update.message.reply_text("✅ Опубликовано: " + await self.vk.publish(text))
            else:
                await update.message.reply_text(text)
        except Exception as e:
            await update.message.reply_text(f"❌ {e}")

    @owner_only
    async def cmd_vkpreview(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        await self._vk_cmd(update, context, publish=False)

    @owner_only
    async def cmd_vkpost(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        await self._vk_cmd(update, context, publish=True)

    # ---------- кнопки под сигналом ----------
    @owner_only
    async def on_button(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        q = update.callback_query
        action, _, sym = (q.data or "").partition(":")
        if action == "bl":
            self.db.add_blacklist(sym, time.time())
            await q.answer(f"{sym} в чёрном списке")
            markup = self._keyboard(sym, blacklisted=True)
        elif action == "unbl":
            self.db.remove_blacklist(sym)
            await q.answer(f"{sym} убрана из чёрного списка")
            markup = self._keyboard(sym)
        elif action == "mute":
            self.db.set_mute(sym, time.time() + self.cfg.mute_default_hours * 3600)
            await q.answer(f"{sym} на {self.cfg.mute_default_hours} ч в mute")
            markup = self._keyboard(sym)
        else:
            await q.answer()
            return
        try:
            await q.edit_message_reply_markup(reply_markup=markup)
        except BadRequest:
            pass  # клавиатура не изменилась

    async def on_error(self, update, context: ContextTypes.DEFAULT_TYPE):
        log.error("Ошибка в обработчике Telegram", exc_info=context.error)


# ======================================================================
# ПУБЛИКАЦИЯ В ВК: утренний обзор и вечерние итоги
# ======================================================================
class VKError(Exception):
    def __init__(self, code, msg):
        super().__init__(f"ВК, ошибка {code}: {msg}")
        self.code = code


def coin_tag(symbol: str) -> str:
    """'1000PEPE-USDT' -> '#PEPE'."""
    return "#" + re.sub(r"^\d+", "", symbol.rsplit("-", 1)[0])


SLOT_HEADS = {
    "morning": ["📊 Обзор рынка", "☀️ Утренний обзор крипторынка", "🔎 Что на рынке сегодня"],
    "evening": ["🌙 Итоги дня на крипторынке", "📋 Вечерний обзор рынка"],
}


class VKPoster:
    def __init__(self, cfg, client, db, scanner, state, notifier):
        self.cfg, self.client, self.db = cfg, client, db
        self.scanner, self.state, self.notifier = scanner, state, notifier
        self._group_id: int | None = None
        self._next_try: dict[str, float] = {}

    def _tz(self) -> timezone:
        return timezone(timedelta(hours=self.cfg.vk_tz_offset))

    # ---------- VK API ----------
    async def _api(self, method: str, **params):
        params.update(access_token=self.cfg.vk_token, v=self.cfg.vk_api_version)
        for attempt in range(3):
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=20)) as s:
                async with s.post(f"https://api.vk.com/method/{method}", data=params) as r:
                    data = await r.json(content_type=None)
            err = data.get("error") if isinstance(data, dict) else {"error_code": -1, "error_msg": "странный ответ"}
            if not err:
                return data.get("response")
            if err.get("error_code") == 6 and attempt < 2:  # слишком много запросов в секунду
                await asyncio.sleep(1.5)
                continue
            raise VKError(err.get("error_code"), err.get("error_msg"))

    async def group_id(self) -> int:
        if self._group_id:
            return self._group_id
        g = self.cfg.vk_group.strip().rstrip("/").rsplit("/", 1)[-1].lstrip("-")
        if g.isdigit():
            self._group_id = int(g)
        else:
            r = await self._api("utils.resolveScreenName", screen_name=g)
            if not r or r.get("type") not in ("group", "page", "event"):
                raise VKError(-1, f"не удалось найти группу «{g}»")
            self._group_id = int(r["object_id"])
        return self._group_id

    async def publish(self, text: str) -> str:
        gid = await self.group_id()
        r = await self._api("wall.post", owner_id=-gid, from_group=1, message=text)
        return f"https://vk.com/wall-{gid}_{r['post_id']}"

    async def already_posted(self, slot: str) -> bool:
        """Проверка по стене группы: на бесплатном хостинге диск стирается при перезапуске,
        и отметка в базе пропадает — без этой проверки пост мог бы выйти дважды."""
        try:
            gid = await self.group_id()
            r = await self._api("wall.get", owner_id=-gid, count=10)
        except Exception:
            return False
        today = datetime.now(self._tz()).date()
        for it in (r or {}).get("items", []):
            if datetime.fromtimestamp(it.get("date", 0), self._tz()).date() == today \
                    and any(it.get("text", "").startswith(h) for h in SLOT_HEADS[slot]):
                return True
        return False

    # ---------- текст поста ----------
    async def build(self, kind: str) -> str:
        cfg, st = self.cfg, self.state
        now = time.time()
        tickers = await self.client.get_tickers()
        cands = self.scanner._select_candidates(tickers, now)
        if not cands:
            raise RuntimeError("нет монет для обзора (проверьте фильтры)")
        date_s = datetime.now(self._tz()).strftime("%d.%m.%Y")
        head = random.choice(SLOT_HEADS["morning" if kind == "morning" else "evening"])
        lines = [f"{head} · {date_s}", ""]
        for sym, icon in (("BTC-USDT", "₿"), ("ETH-USDT", "Ξ")):
            t = tickers.get(sym)
            if t:
                lines.append(f"{icon} {sym.split('-')[0]}: {fmt_price(t.last)} ({t.change_pct:+.2f}% за 24ч)")
        lines.append(f"Режим рынка: {REGIME_RU[st.regime]} (BTC за 4ч {st.btc_ret4h:+.2f}%, "
                     f"растёт {st.breadth * 100:.0f}% монет)")

        by_chg = sorted(cands, key=lambda t: t.change_pct, reverse=True)
        top = [t for t in by_chg if t.change_pct > 0][:5]
        bottom = [t for t in reversed(by_chg) if t.change_pct < 0][:5]
        if top:
            lines += ["", "🚀 Лидеры роста за 24ч:"]
            lines += [f"{i}. {t.symbol.split('-')[0]} {t.change_pct:+.1f}%" for i, t in enumerate(top, 1)]
        if bottom:
            lines += ["", "📉 Лидеры падения за 24ч:"]
            lines += [f"{i}. {t.symbol.split('-')[0]} {t.change_pct:+.1f}%" for i, t in enumerate(bottom, 1)]

        try:
            fr = await self.client.get_funding_all()
        except Exception:
            fr = {}
        fl = [(t.symbol, fr[t.symbol][0] * 100) for t in cands if t.symbol in fr]
        if fl:
            hi, lo = max(fl, key=lambda x: x[1]), min(fl, key=lambda x: x[1])
            lines += ["", f"💸 Funding: максимум у {hi[0].split('-')[0]} ({hi[1]:+.3f}%, перекос в лонги), "
                          f"минимум у {lo[0].split('-')[0]} ({lo[1]:+.3f}%)"]

        rows = self.db.signals_since(now - 86400)
        hot = sum(1 for r in rows if r["side"] == "SHORT")
        cold = len(rows) - hot
        if kind == "morning":
            lines += ["", f"🔎 За сутки сканер отметил сигналов: {len(rows)} (🔥 перегрев {hot}, 🧊 перепроданность {cold})"]
        elif rows:
            lines += ["", f"🔎 Сигналы за сутки: {len(rows)} (🔥 {hot} / 🧊 {cold}). Что было дальше:"]
            for r in rows[-6:]:
                mv, label = None, ""
                for col, lb in (("price_4h", "4ч"), ("price_1h", "1ч")):
                    if r[col] and r[col] > 0:
                        mv = (r[col] / r["price"] - 1) * 100 * (-1 if r["side"] == "SHORT" else 1)
                        label = lb
                        break
                icon = "🔥" if r["side"] == "SHORT" else "🧊"
                res = f"{mv:+.1f}% за {label} в сторону сигнала" if mv is not None else "итог ещё не подведён"
                lines.append(f"{icon} {r['symbol'].split('-')[0]} — {res}")
        else:
            lines += ["", "🔎 Сильных сигналов за сутки не было — рынок без экстремумов."]

        tags, seen = [], set()
        coin_tags = [coin_tag(s) for s in ("BTC-USDT", "ETH-USDT")] + [coin_tag(t.symbol) for t in top[:3] + bottom[:2]]
        for tag in cfg.vk_hashtags.split() + coin_tags:
            if tag.lower() not in seen:
                seen.add(tag.lower())
                tags.append(tag)
        lines += ["", cfg.vk_disclaimer, "", cfg.vk_cta, "", " ".join(tags)]
        return "\n".join(lines)

    # ---------- расписание ----------
    async def run(self) -> None:
        c = self.cfg
        log.info("Публикация в ВК включена: утро %s:00, вечер %s:00 (UTC%+d)",
                 c.vk_morning_hour, c.vk_evening_hour, c.vk_tz_offset)
        while True:
            try:
                await self._tick()
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("Ошибка планировщика ВК")
            await asyncio.sleep(60)

    async def _tick(self) -> None:
        if not self.state.last_scan_ts:  # ждём первый скан (нужен режим рынка)
            return
        now = datetime.now(self._tz())
        today = now.date().isoformat()
        for slot, hour in (("morning", self.cfg.vk_morning_hour), ("evening", self.cfg.vk_evening_hour)):
            if hour < 0 or not (hour <= now.hour < hour + 2):  # окно 2 часа, чтобы не постить «утро» ночью
                continue
            if self.db.load_settings().get(f"vk_last_{slot}") == today:
                continue
            if time.time() < self._next_try.get(slot, 0):
                continue
            if await self.already_posted(slot):
                self.db.save_setting(f"vk_last_{slot}", today)
                continue
            try:
                url = await self.publish(await self.build(slot))
            except Exception as e:
                self._next_try[slot] = time.time() + 600  # повтор через 10 минут
                log.exception("Не удалось опубликовать в ВК (%s)", slot)
                await self.notifier.send_text(f"⚠️ Не удалось опубликовать в ВК ({slot}): {html.escape(str(e))[:300]}")
                continue
            self.db.save_setting(f"vk_last_{slot}", today)
            await self.notifier.send_text(f"✅ Опубликовано в ВК ({slot}): {url}")


# ======================================================================
# ТОЧКА ВХОДА
# ======================================================================


def setup_logging(level: str) -> None:
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(name)s: %(message)s")
    root = logging.getLogger()
    root.setLevel(level)
    console = logging.StreamHandler()
    console.setFormatter(fmt)
    file_h = logging.handlers.RotatingFileHandler("bot.log", maxBytes=5_000_000, backupCount=3, encoding="utf-8")
    file_h.setFormatter(fmt)
    root.addHandler(console)
    root.addHandler(file_h)
    # httpx пишет в INFO полные URL с токеном бота — глушим, чтобы токен не попал в лог
    for noisy in ("httpx", "httpcore", "telegram.ext"):
        logging.getLogger(noisy).setLevel(logging.WARNING)


async def start_health_server():
    """Мини-веб-сервер для хостингов вроде Render: им нужен открытый порт (переменная PORT)."""
    port = int(os.getenv("PORT", "0") or 0)
    if not port:
        return None

    async def ok(_request):
        return web.Response(text="ok")

    app = web.Application()
    app.router.add_get("/", ok)
    app.router.add_get("/health", ok)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", port).start()
    log.info("Health-сервер запущен на порту %s", port)
    return runner


async def keepalive() -> None:
    """Раз в 10 минут обращается к собственному адресу, чтобы бесплатный сервис не засыпал."""
    url = os.getenv("RENDER_EXTERNAL_URL")
    if not url:
        return
    while True:
        await asyncio.sleep(600)
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=20)) as sess:
                async with sess.get(url.rstrip("/") + "/health") as r:
                    await r.read()
        except Exception:
            log.debug("keepalive не удался", exc_info=True)


async def run(cfg: Config, last_error: str | None) -> None:
    db = Database(cfg.db_path, cfg.database_url)
    db.fee_pct = cfg.fee_pct
    # Пороги, изменённые через /set, переопределяют значения из .env
    for key, raw in db.load_settings().items():
        if key in SETTABLE:
            try:
                set_param(cfg, key, raw)
            except ValueError:
                log.warning("Игнорирую некорректную сохранённую настройку %s=%s", key, raw)

    state = ScannerState()
    bot = TelegramBot(cfg, db, state)
    client = BingXClient(rate_per_sec=cfg.request_rate)
    scanner = Scanner(cfg, client, db, bot, state)
    poster = VKPoster(cfg, client, db, scanner, state, bot) if cfg.vk_enabled else None
    bot.vk = poster

    await client.start()
    health = await start_health_server()
    await bot.start()
    try:
        if last_error:
            await bot.send_text(f"♻️ Бот перезапущен после ошибки:\n<code>{last_error[:300]}</code>")
        else:
            await bot.send_text("🟢 Бот запущен, сканирую рынок. /status — состояние, /stats — статистика.")
        tasks = [scanner.run(), keepalive()]
        if poster:
            tasks.append(poster.run())  # публикации в ВК
        await asyncio.gather(*tasks)  # бесконечный цикл
    finally:
        if health:
            await health.cleanup()
        await bot.stop()
        await client.close()
        db.close()


def main() -> None:
    cfg = Config()
    setup_logging(cfg.log_level)
    last_error: str | None = None
    delay = 5
    while True:  # автоперезапуск при падении
        started = time.monotonic()
        try:
            asyncio.run(run(cfg, last_error))
        except KeyboardInterrupt:
            log.info("Остановлено пользователем")
            break
        except Exception as e:
            last_error = f"{type(e).__name__}: {e}"
            log.exception("Бот упал, перезапуск через %sс", delay)
            # если работал долго — сбрасываем задержку, иначе наращиваем (до 60с)
            delay = 5 if time.monotonic() - started > 300 else min(delay * 2, 60)
            time.sleep(delay)


if __name__ == "__main__":
    main()
