# -*- coding: utf-8 -*-
# ═══════════════════════════════════════════════════════════════════
#  NG RAXX — Squad Bot v6 (CLEAN & FIXED)
#  4-4 AUTO SQUADS + NEW START MATCH + CHASE MOVEMENT + GUILD + CREATE
#  + BACKGROUND MATCH (Auto Requeue & Stable TCP Keepalive)
# ═══════════════════════════════════════════════════════════════════
import sys, asyncio, httpx, random, json, socket, struct, time, os, uuid
import itertools, secrets, traceback, base64, re, hmac, hashlib, string, ssl
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any
from urllib.parse import urlencode

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception: pass

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME

import aiohttp
import aiohttp.web

try:
    import NgRaxxFF_pb2
except ImportError:
    NgRaxxFF_pb2 = None

try:
    import NgRaxx_pb2
except ImportError:
    NgRaxx_pb2 = None

try:
    import reqClan_pb2
    _CLAN_PB_AVAILABLE = True
except Exception:
    _CLAN_PB_AVAILABLE = False

try:
    import CguFF_pb2
    _START_MATCH_PROTO = CguFF_pb2
except ImportError:
    _START_MATCH_PROTO = NgRaxxFF_pb2 or NgRaxx_pb2

from dashboard_server import start_web_dashboard

# ═══════════════════════════ CONFIG ═══════════════════════════
WEB_HOST = "0.0.0.0"
WEB_PORT = int(os.environ.get("PORT", 20333))
ACCOUNTS_FILE = "accounts.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
TOKEN_CACHE_TTL = 4500

CLAN_ID_DEFAULT = "3105331459"
GUILD_API_BASE = "https://danger-guild-management-web.vercel.app"
GUILD_INFO_SHOW_ON_JOIN = True
GUILD_INFO_SHOW_ON_BOOT = True
ENABLE_GUILD_API = True

BOT_NAME_PREFIX = "LX_"
BOT_NAME_SUFFIX_LEN = 7
START_MATCH_INTERVAL         = 5.0
NEW_MATCH_DELAY              = 8.0
MAX_MATCH_DURATION           = 1800
MATCH_IDLE_TIMEOUT           = 120.0
HANDSHAKE_TIMEOUT            = 60.0
EXP_REFRESH_INTERVAL         = 30.0
EXP_REFRESH_AFTER_MATCH_DELAY = 10.0
MAX_CONSECUTIVE_PARSE_FAILURES = 5
NON_MATCH_RECONNECT_DELAY    = 3.0
SESSION_RETRY_DELAY          = 8.0

BR_MODE_ID             = 1
BR_MAP_ID              = 1

ANTI_AFK_MIN_INTERVAL  = 1.8
ANTI_AFK_MAX_INTERVAL  = 3.5

MATCH_SEARCH_TIMEOUT   = 90.0
MATCH_WATCHDOG_CHECK   = 30.0
REGION_ROTATION_LIST   = ["IND", "ID", "SG", "TH", "MY", "VN", "PH"]
REGION_ROTATE_EVERY_N  = 2
MAX_SEARCH_ATTEMPTS    = 25

SAFE_PLAY_MODE        = True
BYPASS_TIMING_JITTER  = True
BYPASS_PACKET_JITTER  = True
BYPASS_HELLO_DELAY    = True
BYPASS_KA_JITTER      = True

ENABLE_SPEED_MOVEMENT       = True
MOVEMENT_PATTERN            = "circle"
MOVEMENT_TICK_MS            = 240
MOVEMENT_RADIUS             = 180
MOVEMENT_UPDATE_SPEED_EVERY = 4.0
MOVEMENT_SPEED_MIN          = 1.0
MOVEMENT_SPEED_MAX          = 1.4
MOVEMENT_STATE_IDLE_CHANCE   = 0.10
MOVEMENT_STATE_WALK_CHANCE   = 0.28
MOVEMENT_STATE_RUN_CHANCE    = 0.32
MOVEMENT_STATE_SPRINT_CHANCE = 0.10
MOVEMENT_STATE_JUMP_CHANCE   = 0.08
MOVEMENT_STATE_CROUCH_CHANCE = 0.06
MOVEMENT_STATE_PRONE_CHANCE  = 0.06

ENABLE_HTTP_PING = True
PING_INTERVAL    = 20.0
PING_TIMEOUT     = 8.0
PING_URL         = "https://loginbp.ppmainecoonghj.com/Ping"
PING_REAL_IP     = "103.109.214.211"

FALLBACK_UID = ""
FALLBACK_PASSWORD = ""

# ─── SQUAD GROUPING ───
TEAM_MODE               = True
TEAM_SIZE               = 4
TEAM_PEER_WAIT_TIMEOUT  = 25.0
TEAM_CREATE_WAIT        = 4.0
TEAM_INVITE_CYCLE_WAIT  = 4.0
TEAM_INVITE_MAX_TIME    = 120.0
TEAM_HEARTBEAT_INTERVAL = 3.0
TEAM_IDLE_ITERS_TEAM    = 1800
TEAM_MEMBER_START_DELAY = 20.0
TEAM_FINAL_WAIT         = 8.0
TEAM_READY_DELAY        = 5.0
_accept_friend_request  = True
DEBUG_TEAM_PACKETS      = False

# ─── BACKGROUND MATCH RESTART ───
MAX_BG_MATCHES   = 3
BG_RESTART_DELAY = 2.0
BG_CAP_WAIT_MAX  = 15.0

REGION_LANG = {"ME": "ar", "IND": "hi", "ID": "id", "VN": "vi", "TH": "th",
               "BD": "bn", "PK": "ur", "TW": "zh", "RU": "ru", "SAC": "es",
               "BR": "pt", "NA": "pt", "SG": "pt", "US": "pt"}

FORCED_CLIENT_VERSION = "2.133.13"

# ═══════════════════════════ BOT STATE ═══════════════════════════
class BotState:
    def __init__(self):
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.create_progress: List[str] = []
        self.creating = False
        self.start_time = time.time()
        self.refresh_callbacks = {}
        self.guild_cache: Dict[str, dict] = {}

    def log(self, msg, level="info"):
        try:
            t = datetime.now().strftime("%H:%M:%S")
            self.logs.append({"t": time.time(), "time": t, "message": str(msg), "level": level})
            if len(self.logs) > 500: self.logs = self.logs[-500:]
        except Exception: pass

    def register_account(self, uid, nickname, region="IND", level=1, exp=0, likes=0,
                         token=None, auth_uid=None):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid, "nickname": nickname, "region": region,
            "level": level, "exp": exp, "likes": likes,
            "token": token, "auth_uid": auth_uid,
            "status": "ONLINE", "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0), "active_matches": 0,
            "uptime_seconds": existing.get("uptime_seconds", 0),
            "last_match_time": existing.get("last_match_time", "Running..."),
            "is_paused": False,
        }

    def update_status(self, uid, status, matches=0):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            self.accounts[uid]["active_matches"] = matches
            self.accounts[uid]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            a = self.accounts[uid]
            old = a.get("current_exp", 0)
            if exp > old:
                a["gained_exp"] = a.get("gained_exp", 0) + (exp - old)
                self.total_exp_gained += (exp - old)
            a["current_exp"] = exp
            a["exp"] = exp
            if level: a["level"] = level

    def increment_match(self, uid):
        self.total_matches += 1
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["matches"] = self.accounts[uid].get("matches", 0) + 1
            self.accounts[uid]["last_match_time"] = datetime.now().strftime("%H:%M:%S")

    def increment_match_started(self): self.matches_started += 1
    def register_writer(self, uid, w): self.writers.setdefault(str(uid), []).append(w)

    def unregister_writer(self, uid, w):
        try: self.writers.get(str(uid), []).remove(w)
        except Exception: pass

    def is_paused(self, uid): return str(uid) in self.paused

    def toggle_pause(self, uid, state):
        uid = str(uid)
        if state:
            self.paused.add(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = True
                self.accounts[uid]["status"] = "PAUSED"
        else:
            self.paused.discard(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = False
                if self.accounts[uid].get("status") == "PAUSED":
                    self.accounts[uid]["status"] = "ONLINE"

bot_state = BotState()
_ACTIVE_GROUPS: Dict[int, Any] = {}

# ═══════════════════════════ LOG ═══════════════════════════
class Colors:
    GREEN='\033[92m'; FAIL='\033[91m'; WARNING='\033[93m'
    CYAN='\033[96m'; MAGENTA='\033[95m'; WHITE='\033[97m'; ENDC='\033[0m'

def print_colored(t, c=Colors.WHITE):
    try: print(f"{c}{t}{Colors.ENDC}", flush=True)
    except Exception: pass

def print_success(t):
    print_colored(f"[+] {t}", Colors.GREEN)
    try: bot_state.log(t, "success")
    except Exception: pass

def print_error(t):
    print_colored(f"[-] {t}", Colors.FAIL)
    try: bot_state.log(t, "error")
    except Exception: pass

def print_warning(t):
    print_colored(f"[!] {t}", Colors.WARNING)
    try: bot_state.log(t, "warning")
    except Exception: pass

def print_info(t):
    print_colored(f"[i] {t}", Colors.CYAN)
    try: bot_state.log(t, "info")
    except Exception: pass

def banner_team_code(team_code, uid=""):
    if not team_code: return
    box_w = 50
    line = "═" * box_w
    print_colored(f"╔{line}╗", Colors.GREEN)
    title = f"  🎯 TEAM CODE: {team_code}  "
    pad = max(0, (box_w - len(title)) // 2)
    print_colored(f"║{' ' * pad}{title}{' ' * (box_w - pad - len(title))}║", Colors.GREEN)
    if uid:
        s = f"  Leader: {uid}"
        print_colored(f"║{s:<{box_w}}║", Colors.CYAN)
    print_colored(f"╚{line}╝", Colors.GREEN)

def extract_team_code_from_bytes(buf: bytes) -> Optional[str]:
    if not buf or len(buf) < 5: return None
    m = re.search(rb'\x5a[\x06\x07\x08]([0-9]{6,8})', buf)
    if m:
        c = m.group(1).decode('ascii', 'ignore')
        if c.isdigit() and 6 <= len(c) <= 8: return c
    return None

# ═══════════════════════════ SOCKETS & OPTIMIZATION ═══════════════════════════
_DNS_CACHE: Dict[str, Tuple[str, float]] = {}
_DNS_CACHE_TTL = 300.0

async def resolve_host_cloudflare(hostname):
    if not hostname: return hostname
    parts = hostname.split('.')
    if len(parts) == 4 and all(p.isdigit() for p in parts): return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp: return ip
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
            return ip
    except Exception: pass
    return hostname

def optimize_tcp_socket(sock):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        if hasattr(socket, 'IPPROTO_TCP'):
            try:
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPIDLE, 30)
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPINTVL, 10)
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPCNT, 3)
            except Exception: pass
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

def optimize_udp_socket(sock):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

async def safe_close_writer(writer):
    if not writer: return
    try:
        if not writer.is_closing(): writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception: pass

# ═══════════════════════════ HTTP CLIENT & KEYS ═══════════════════════════
client = httpx.AsyncClient(verify=False, timeout=10.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150))
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV  = b'6oyZDr22E3ychjM%'
HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()

KEYSTREAM = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,
                   0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,
                   0x30,0x30,0x30,0x30,0x32,0x30])

GGRE_RAW = bytes.fromhex(
    "47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4"
)

CRC7_TABLE = bytes([
    0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,25,16,11,2,61,52,47,38,
    81,88,67,74,117,124,103,110,50,59,32,41,22,31,4,13,122,115,104,97,94,87,76,69,
    43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,100,109,118,127,64,73,82,91,
    44,37,62,55,8,1,26,19,125,116,111,102,89,80,75,66,53,60,39,46,17,24,3,10,
    86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,79,70,93,84,107,98,121,112,
    7,14,21,28,35,42,49,56,65,72,83,90,101,108,119,126,9,0,27,18,45,36,63,54,
    88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,47,115,122,97,104,87,94,69,76,
    59,50,41,32,31,22,13,4,106,99,120,113,78,71,92,85,34,43,48,57,6,15,20,29,
    37,44,55,62,1,8,19,26,109,100,127,118,73,64,91,82,60,53,46,39,24,17,10,3,
    116,125,102,111,80,89,66,75,23,30,5,12,51,58,33,40,95,86,77,68,123,114,105,96,
    14,7,28,21,42,35,56,49,70,79,84,93,98,107,112,121,
])
_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0:1, 1:2, 2:2, 3:1, 4:2}
_FIELD_NAMES = {0:"sendOption", 1:"cmd", 2:"orderId", 3:"flags", 4:"length"}

# ═══════════════════════════ MATCH COUNTER ═══════════════════════════
_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()

async def _inc_match(uid):
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]

async def _dec_match(uid):
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)

async def _get_match_count(uid):
    async with _match_counter_lock:
        return _match_counters.get(uid, 0)

# ═══════════════════════════ SQUAD GROUP ═══════════════════════════
class TeamGroup:
    def __init__(self, gid: int, size: int = TEAM_SIZE):
        self.gid = gid
        self.size = max(1, min(int(size), TEAM_SIZE))
        self.peers: Dict[str, Any] = {}
        self.leader_uid: Optional[str] = None
        self.team_code: Optional[str] = None
        self.pk_code: Optional[str] = None
        self.members: set = set()
        self.members_lock = asyncio.Lock()
        self.lock = asyncio.Lock()
        self.active = {"flag": True}

    def tag(self) -> str:
        return f"G{self.gid}"

async def team_member_join(grp: TeamGroup, uid):
    uid = str(uid)
    async with grp.members_lock:
        before = len(grp.members)
        grp.members.add(uid)
        after = len(grp.members)
    if after != before:
        print_success(f"[TEAM-{grp.tag()}] 👥 In team ({after}/{grp.size}) | joined: {uid}")
    return after

async def team_member_leave(grp: TeamGroup, uid):
    async with grp.members_lock:
        grp.members.discard(str(uid))

async def team_member_count(grp: TeamGroup):
    async with grp.members_lock:
        return len(grp.members)

async def team_member_reset(grp: TeamGroup, keep_leader=True):
    async with grp.members_lock:
        grp.members.clear()
        if keep_leader and grp.leader_uid:
            grp.members.add(grp.leader_uid)

# ═══════════════════════════ TOKEN CACHE ═══════════════════════════
_token_cache_memo = {}
_token_cache_memo_time = 0.0
_TOKEN_CACHE_MEMO_TTL = 5.0

def _json_serializer(obj):
    if isinstance(obj, (bytes, bytearray)): return {"__bytes_hex__": bytes(obj).hex()}
    raise TypeError(f"not serializable: {type(obj)}")

def _json_deserializer(obj):
    if isinstance(obj, dict):
        if "__bytes_hex__" in obj and len(obj) == 1:
            try: return bytes.fromhex(obj["__bytes_hex__"])
            except Exception: return b""
        return {k: _json_deserializer(v) for k, v in obj.items()}
    if isinstance(obj, list): return [_json_deserializer(x) for x in obj]
    return obj

def _load_token_cache():
    global _token_cache_memo, _token_cache_memo_time
    now = time.time()
    if _token_cache_memo and (now - _token_cache_memo_time) < _TOKEN_CACHE_MEMO_TTL:
        return _token_cache_memo
    if not os.path.exists(TOKEN_CACHE_FILE): return {}
    try:
        with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
            content = f.read().strip()
        if not content: return {}
        data = json.loads(content)
        if not isinstance(data, dict): raise ValueError("root must be dict")
        parsed = _json_deserializer(data)
        _token_cache_memo = parsed; _token_cache_memo_time = now
        return parsed
    except Exception as e:
        print_error(f"Token cache corrupt -> delete: {e}")
        try: os.remove(TOKEN_CACHE_FILE)
        except Exception: pass
        return {}

def _save_token_cache(cache):
    global _token_cache_memo, _token_cache_memo_time
    try:
        tmp = TOKEN_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, default=_json_serializer)
        os.replace(tmp, TOKEN_CACHE_FILE)
        _token_cache_memo = cache; _token_cache_memo_time = time.time()
    except Exception as e: print_error(f"Cache save: {e}")

def cache_get(uid):
    cache = _load_token_cache()
    e = cache.get(str(uid))
    if not e: return None
    if time.time() - e.get("cached_at", 0) > TOKEN_CACHE_TTL:
        cache_invalidate(uid); return None
    if str(e.get("account_id", "")).isdigit(): e["account_id"] = int(e["account_id"])
    if not isinstance(e.get("login_payload_data"), (bytes, bytearray)):
        cache_invalidate(uid); return None
    return e

def cache_set(uid, data):
    cache = _load_token_cache()
    e = dict(data); e["cached_at"] = time.time()
    cache[str(uid)] = e; _save_token_cache(cache)

def cache_invalidate(uid):
    cache = _load_token_cache()
    if str(uid) in cache:
        del cache[str(uid)]; _save_token_cache(cache)

# ═══════════════════════════ CRYPTO & PROTOBUF ═══════════════════════════
async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))

async def get_playstore_version():
    try:
        loop = asyncio.get_event_loop()
        res = await loop.run_in_executor(
            None, lambda: play_scraper('com.dts.freefireth', lang='hi', country='id'))
        return res.get("version")
    except Exception:
        return "1.134.14"

async def version_config(region="IND"):
    app_version = await get_playstore_version()
    lang = REGION_LANG.get(str(region).upper(), "en")
    url = ("https://version.ggwhitehawk.com/live/ver.php"
           f"?version={app_version}&lang={lang}&device=android&channel=android"
           f"&appstore=googleplay&region={str(region).upper()}"
           "&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
    try:
        r = await client.get(url); r.raise_for_status()
        j = r.json()
        su = j.get("server_url"); lr = j.get("latest_release_version")
        if not su: return None
        gops = [u.strip() for u in j.get("gop_url", "").split(";") if u.strip()]
        gop_1 = gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com"
        remote = FORCED_CLIENT_VERSION or j.get("remote_version") or app_version
        return lr, remote, su, gop_1, app_version
    except Exception: return None

async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br", "Connection": "close"
    }
    data = {
        "uid": uid, "password": password, "response_type": "token", "client_type": "2",
        "client_secret": HEX_KEY, "client_id": "100067"
    }
    for attempt in range(5):
        try:
            r = await client.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                d = r.json()
                oid = d.get("open_id"); at = d.get("access_token"); pf = d.get("platform", 4)
                if oid and at: return oid, at, pf
            if r.status_code == 429: await asyncio.sleep(1); continue
        except Exception: pass
        await asyncio.sleep(0.5)
    return None

def generate_signature(payload_str):
    return hmac.new(API_KEY, payload_str.encode(), hashlib.sha256).hexdigest()

async def grant_token(uid, password, gop_url, app_version, max_attempts=5):
    gp = {
        "client_id": 100067, "client_secret": HEX_KEY, "client_type": 2,
        "device_id": f"02-{uuid.uuid4()}", "password": password,
        "response_type": "token", "uid": int(uid),
    }
    payload = json.dumps(gp, separators=(',', ':'))
    sig = generate_signature(payload)
    hdrs = {
        "User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
    }
    urls = [f"{gop_url}/api/v2/oauth/guest/token:grant", f"{gop_url}/api/v2/oauth/guest:token:grant"]
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    for attempt in range(max_attempts):
        for url in urls:
            try:
                async with aiohttp.ClientSession(connector=connector) as s:
                    async with s.post(url, headers=hdrs, data=payload, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                        text = await resp.text()
                        if resp.status == 200:
                            data = json.loads(text)
                            if data.get("code") == 0 and data.get("data"): return data["data"]
            except Exception: pass
        await asyncio.sleep(2.0)
    return None

def decode_varint(data, offset):
    result = 0; shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80): return result, offset
        shift += 7
    return None, offset

def decode_protobuf_2(data):
    result = {}; offset = 0; dl = len(data)
    while offset < dl:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                result[fn] = value.hex()
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def extract_raw_fields(data: bytes) -> dict:
    result = {}; offset = 0; dl = len(data)
    while offset < dl:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            if offset + length > dl: break
            result[fn] = bytes(data[offset:offset+length]); offset += length
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def _parse_results_sync(results):
    out = {}
    for r in results:
        fd = {"wire_type": r.wire_type}
        if r.wire_type == "varint": fd["data"] = r.data
        elif r.wire_type in ("string", "bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"): fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list): fd["data"] = _parse_results_sync(r.data)
            else: fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out

def decode_protobuf_dict(data: bytes) -> dict:
    try: return _parse_results_sync(Parser().parse(data))
    except Exception: return {}

async def decode_protobuf(data):
    try: return json.dumps(_parse_results_sync(Parser().parse(data)))
    except Exception: return "{}"

def encode_varint(n):
    out = bytearray()
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def create_proto(fields):
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(field, str): field = int(field)
        if isinstance(value, dict):
            packet.extend(encode_varint((field << 3) | 2) + encode_varint(len(bytes(create_proto(value)))) + bytes(create_proto(value)))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict): packet.extend(encode_varint((field << 3) | 2) + encode_varint(len(bytes(create_proto(item)))) + bytes(create_proto(item)))
                elif isinstance(item, str): packet.extend(encode_varint((field << 3) | 2) + encode_varint(len(item)) + item.encode())
                elif isinstance(item, int): packet.extend(encode_varint((field << 3) | 0) + encode_varint(item))
        elif isinstance(value, int): packet.extend(encode_varint((field << 3) | 0) + encode_varint(value))
        elif isinstance(value, str): packet.extend(encode_varint((field << 3) | 2) + encode_varint(len(value)) + value.encode())
        elif isinstance(value, (bytes, bytearray)): packet.extend(encode_varint((field << 3) | 2) + encode_varint(len(value)) + bytes(value))
    return bytes(packet)

def encrypt_api(plain_hex):
    return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(bytes.fromhex(plain_hex), AES.block_size)).hex()

def encrypt_aes(hex_data: str) -> str:
    return encrypt_api(hex_data)

def create_packet(Pk, N, K, V):
    if isinstance(K, str): K = bytes.fromhex(K) if len(K) == 32 else K.encode()
    if isinstance(V, str): V = bytes.fromhex(V) if len(V) == 32 else V.encode()
    PkEnc = AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(Pk), 16)).hex()
    L = len(PkEnc) // 2
    hexlen = hex(L)[2:]
    if len(hexlen) % 2 != 0: hexlen = '0' + hexlen
    pad_len = 12 - len(N) - len(hexlen)
    if pad_len < 0: pad_len = 0
    return bytes.fromhex(N + ('0' * pad_len) + hexlen + PkEnc)

# ═══════════ SQUAD & MATCH PACKETS ═══════════
def create_team(key, iv, game_version="1.132.13"):
    fields = {1: 1, 2: {2: bytes.fromhex("01"), 3: 1, 4: 3, 5: "en",
        8: {1: "IDC3", 2: 123, 3: "IND"}, 9: 1, 11: 2, 13: 1,
        14: {1: "08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d", 2: 478, 3: "7e585d55", 4: "y[Z]", 6: 12, 8: str(game_version), 9: 3, 10: 1},
        19: 329, 21: bytes.fromhex("374f521955"), 24: {1: 21}, 27: "a_6534489873065906362"}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def team_fresh(account_id, key, iv):
    return create_packet(create_proto({1: 72, 2: {1: int(account_id)}}).hex(), "0515", key, iv)

def invite_player_in_team(target_uid, key, iv, region="IND"):
    return create_packet(create_proto({1: 2, 2: {1: int(target_uid), 2: region, 4: 1}}).hex(), "0515", key, iv)

def accept_team_invite(target_uid, group_id, key, iv):
    fields = {1: 4, 2: {1: int(target_uid), 3: int(target_uid), 8: 1, 10: str(group_id), 11: {"1": "IDC3", "2": 107, "3": "IND"}, 13: "en"}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def start_match_team(account_id, key, iv, region="IND"):
    fields = {1: 9, 2: {1: int(account_id), 7: {1: "IDC3", 2: 410, 3: region}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def ready_for_game(uid, key, iv):
    return create_packet(create_proto({1: 15, 2: {1: uid, 2: 1}}).hex(), "0519", key, iv)

async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="IND", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc = (await aes_encrypt(token.encode(), key, iv)).hex()
    enc_len = f"{len(enc)//2:08x}"
    reg = str(region).upper() if region else "IND"
    if typ == 'OnLine':
        pfx = '7219' if reg == 'BD' else ('7214' if reg == 'IND' else '7215')
        return f"{pfx}{uid_hex}{ts_hex}00000000{enc_len}{enc}"
    pfx = '8119' if reg == 'BD' else ('8114' if reg == 'IND' else '8115')
    return f"{pfx}{uid_hex}{ts_hex}{enc_len}{enc}"

async def send_keep_alive(region="IND"):
    try:
        reg = str(region).upper() if region else "IND"
        return bytes.fromhex("0219" if reg == "BD" else ("0214" if reg == "IND" else "0215"))
    except Exception:
        return bytes.fromhex("0215")

# ═══════════════════════════ AUTH / LOGIN HELPERS ═══════════════════════════
async def major_login(payload, login_url, release_version):
    url = f"{login_url.rstrip('/')}/MajorLogin"
    hdrs = {"Accept": "*/*", "Authorization": "Bearer ",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_version}",
            "User-Agent": "UnityPlayer/2018.4.12f1",
            "X-GA": "v1 1", "X-GA-SV": str(int(time.time())), "X-Unity-Version": "2018.4.12f1"}
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as resp:
                content = await resp.read()
                if resp.status != 200 or len(content) < 200: return None
                for off in [64, 0, 48, 32, 80, 16, 128, 8, 96]:
                    if off >= len(content): continue
                    try:
                        cand = decode_protobuf_dict(content[off:])
                        if cand and ("8" in cand or 8 in cand):
                            cand["__RAW_HEX__"] = content.hex(); cand["__OFFSET__"] = off
                            return cand
                    except Exception: pass
                return None
    except Exception: return None

async def get_login_data(payload, jwt_token, server_url, release_version):
    url = f"{server_url.rstrip('/')}/GetLoginData"
    hdrs = {"Accept": "*/*", "Authorization": f"Bearer {jwt_token}",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_version}",
            "User-Agent": "UnityPlayer/2018.4.12f1", "X-GA": "v1 1"}
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as r:
                if r.status != 200: return None
                content = await r.read()
                for off in [0, 64, 48, 32, 80, 16]:
                    if off >= len(content): continue
                    try:
                        c = decode_protobuf_dict(content[off:])
                        if c and (("14" in c and "32" in c) or (14 in c and 32 in c)): return c
                    except Exception: pass
        return None
    except Exception: return None

def _extract_key_iv(res_json):
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            raw = bytes.fromhex(res_json["__RAW_HEX__"])
            off = int(res_json["__OFFSET__"])
            rf = extract_raw_fields(raw[off:])
            for kf, vf in [(22, 23), (24, 25), (6, 7)]:
                k = rf.get(kf); v = rf.get(vf)
                if isinstance(k, (bytes, bytearray)) and len(k) == 16 and isinstance(v, (bytes, bytearray)) and len(v) == 16:
                    return bytes(k), bytes(v)
        except Exception: pass
    return None, None

# ═══════════════════════════ DASHBOARD & AUTO-LOAD ═══════════════════════════
def load_accounts():
    accounts = []
    if os.path.exists(ACCOUNTS_FILE):
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, list): accounts = [a for a in data if isinstance(a, dict)]
        except Exception: pass
    return accounts

def make_squad_groups(accounts: List[dict]) -> List[Tuple[TeamGroup, List[dict]]]:
    groups = []
    for gi, i in enumerate(range(0, len(accounts), TEAM_SIZE)):
        chunk = accounts[i:i + TEAM_SIZE]
        grp = TeamGroup(gi, size=len(chunk))
        _ACTIVE_GROUPS[gi] = grp
        groups.append((grp, chunk))
    return groups

async def _autoload_accounts():
    accounts = load_accounts()
    if not accounts:
        print_warning(f"No accounts in {ACCOUNTS_FILE}. Add via dashboard.")
        return
    squads = make_squad_groups(accounts)
    print_success(f"[BOOT] {len(accounts)} account(s) -> {len(squads)} squad(s)")
    for grp, chunk in squads:
        for acc in chunk:
            print_info(f"[SQUAD-{grp.tag()}] Account loaded: {acc.get('uid')}")
            await asyncio.sleep(0.2)

async def main():
    print_colored("=" * 62, Colors.CYAN)
    print_colored("  NG RAXX v6 — Squad Bot (Clean Fresh Build)", Colors.GREEN)
    print_colored("=" * 62, Colors.CYAN)
    
    try:
        await start_web_dashboard(
            WEB_HOST, WEB_PORT, bot_state, _ACTIVE_GROUPS,
            create_accounts_func=None,
            fetch_info_func=None,
            join_guild_func=None,
        )
    except Exception as e:
        print_error(f"Dashboard: {e}")
    print_success(f"Dashboard started at: http://localhost:{WEB_PORT}")

    await _autoload_accounts()

    try:
        while True:
            await asyncio.sleep(10)
    except (KeyboardInterrupt, asyncio.CancelledError):
        print_warning("Shutting down bot server...")
        try: await client.aclose()
        except Exception: pass
        print_success("Closed safely.")

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print_warning("Stopped by user.")