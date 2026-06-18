import base64
import json
import os
import re
import uuid
import secrets
import random
import string
import sqlite3
import socket
import threading
import time
import unicodedata
from datetime import datetime, timedelta
from functools import wraps
from urllib.parse import quote, urlsplit

import requests as http_req

from flask import (
    Flask, render_template, request, redirect, url_for,
    session, flash, jsonify, send_from_directory, abort, g
)
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

import mikrotik as mk
import database as db_mod
import ketamon_agent as agent_mod

# KetaServer endpoint configurable
KS_API = os.environ.get("KETASERVER_API_URL", "http://127.0.0.1:5000")
STANDALONE_MODE = "127.0.0.1" in KS_API or "localhost" in KS_API
KS_ENABLED = False
PROFILE_META_PREFIX = "ketamon-profile:"

KETAMON_TICKET_COMMENT_MARKER = " ##KETAMON## exp="
KETAMON_TICKET_COMMENT_MARKERS = (
    KETAMON_TICKET_COMMENT_MARKER,
    KETAMON_TICKET_COMMENT_MARKER.strip(),
)
KETAMON_TICKET_LOGIN_SCRIPT = "ketamon-ticket-login"
KETAMON_TICKET_EXPIRY_SCRIPT = "ketamon-ticket-expiry"
KETAMON_TICKET_EXPIRY_SCHEDULER = "ketamon-ticket-expiry-runner"
MAX_TICKET_GENERATION_QTY = 500
TICKET_GENERATION_BATCH_SIZE = int(os.environ.get("KETAMON_TICKET_BATCH_SIZE", "100"))
TICKET_GENERATION_BATCH_PAUSE = float(os.environ.get("KETAMON_TICKET_BATCH_PAUSE", "0.05"))
BG_REVENUE_SYNC_INTERVAL = int(os.environ.get("KETAMON_REVENUE_SYNC_INTERVAL", "180"))

_TICKET_GENERATION_LOCKS = {}
_TICKET_GENERATION_STATUS = {}
_TICKET_GENERATION_GUARD = threading.Lock()
_relay_public_url_cache = ""  # mis à jour à chaque requête relay ; lu par les threads de fond


def ks_post(path, data, token=None):
    """POST vers KetaServer API. Retourne (dict, None) ou (None, erreur_str)."""
    global KS_ENABLED
    if not KS_ENABLED:
        return None, "KetaServer indisponible"
    try:
        headers = {"Content-Type": "application/json"}
        if token:
            headers["Authorization"] = f"Bearer {token}"
        r = http_req.post(f"{KS_API}{path}", json=data, headers=headers, timeout=8)
        try:
            return r.json(), None
        except Exception:
            return None, f"KetaServer repondu code {r.status_code}"
    except Exception as e:
        KS_ENABLED = False
        return None, str(e)


APP_DIR = os.path.dirname(os.path.abspath(__file__))
app = Flask(__name__, root_path=APP_DIR, template_folder="templates", static_folder="static")
from werkzeug.middleware.proxy_fix import ProxyFix
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1)

# ── Compression gzip automatique (HTML/JSON/CSS/JS) ──────────────────────────
try:
    from flask_compress import Compress as _Compress
    app.config["COMPRESS_MIMETYPES"] = [
        "text/html", "text/css", "text/plain",
        "application/json", "application/javascript",
    ]
    app.config["COMPRESS_LEVEL"]    = 6
    app.config["COMPRESS_MIN_SIZE"] = 500
    _Compress(app)
except ImportError:
    pass
KETAMON_ENV = (os.environ.get("KETAMON_ENV") or "development").strip().lower()
SECRET_KEY = os.environ.get("KETAMON_SECRET_KEY")
if not SECRET_KEY:
    # Clé persistante stockée dans data/secret.key — générée une seule fois
    _sk_path = os.path.join(os.path.dirname(__file__), "data", "secret.key")
    try:
        if os.path.exists(_sk_path):
            with open(_sk_path, "r") as _f:
                SECRET_KEY = _f.read().strip() or None
        if not SECRET_KEY:
            SECRET_KEY = secrets.token_hex(32)
            os.makedirs(os.path.dirname(_sk_path), exist_ok=True)
            with open(_sk_path, "w") as _f:
                _f.write(SECRET_KEY)
            print("INFO: Clé secrète générée et sauvegardée dans data/secret.key")
        else:
            print("INFO: Clé secrète chargée depuis data/secret.key — sessions persistantes.")
    except Exception as _e:
        SECRET_KEY = secrets.token_hex(32)
        print(f"WARNING: Impossible de lire/écrire data/secret.key ({_e}). Clé éphémère utilisée.")
if KETAMON_ENV in {"prod", "production"} and not os.environ.get("KETAMON_SECRET_KEY"):
    print("WARNING: En production, définissez KETAMON_SECRET_KEY comme variable d'environnement.")
app.secret_key = SECRET_KEY

# ── Sécurité cookies de session ───────────────────────────────────────────────
app.config["SESSION_COOKIE_HTTPONLY"] = True   # Inaccessible au JS (anti XSS)
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"  # Anti CSRF cross-origin
app.config["SESSION_COOKIE_SECURE"]   = KETAMON_ENV in {"prod", "production"}  # HTTPS only en prod
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=30)

# Upload limits and allowed logo extensions
app.config["MAX_CONTENT_LENGTH"] = 5 * 1024 * 1024  # 5 MB
ALLOWED_LOGO_EXT = {".png", ".jpg", ".jpeg", ".gif", ".svg"}

# ── Protection brute-force login (en mémoire, par IP) ─────────────────────────
_login_attempts: dict = {}   # {ip: [timestamps]}
_LOGIN_MAX_ATTEMPTS = 10     # tentatives max
_LOGIN_WINDOW_SEC   = 300    # sur 5 minutes
_LOGIN_LOCKOUT_SEC  = 600    # blocage 10 minutes

def _check_login_rate_limit() -> bool:
    """Retourne True si l'IP est bloquée."""
    ip = request.remote_addr or "unknown"
    now = time.time()
    attempts = _login_attempts.get(ip, [])
    # Nettoyer les anciennes tentatives
    attempts = [t for t in attempts if now - t < _LOGIN_LOCKOUT_SEC]
    _login_attempts[ip] = attempts
    recent = [t for t in attempts if now - t < _LOGIN_WINDOW_SEC]
    return len(recent) >= _LOGIN_MAX_ATTEMPTS

def _record_login_failure():
    ip = request.remote_addr or "unknown"
    _login_attempts.setdefault(ip, []).append(time.time())

def _clear_login_failures():
    ip = request.remote_addr or "unknown"
    _login_attempts.pop(ip, None)

# ── CSRF : génération + protection ────────────────────────────────────────────
@app.before_request
def _wait_for_db():
    """Retourne 503 si la DB n'est pas encore prete (init en cours)."""
    if _db_ready.is_set():
        return
    path = request.path or "/"
    if path == "/health" or path.startswith("/static/") or path == "/sw.js":
        return
    if request.is_json or request.headers.get("Accept","").startswith("application/json"):
        return jsonify({"ok": False, "msg": "Serveur en cours d'initialisation, reessayez dans quelques secondes"}), 503
    return "<html><body style='font-family:sans-serif;padding:2rem'><h2>Demarrage en cours...</h2><p>Le serveur initialise la base de donnees. Rechargez la page dans 10 secondes.</p><script>setTimeout(()=>location.reload(),8000)</script></body></html>", 503


@app.before_request
def _ensure_csrf_and_protect():
    if "csrf_token" not in session:
        session["csrf_token"] = secrets.token_hex(16)
    if request.method == "POST":
        # Exclure les webhooks internes et les endpoints appelés par l'app Android sans session
        _csrf_exempt_prefixes = ("/api/internal/", "/api/ads/report", "/api/vouchers", "/api/hotspot/", "/api/relay/")
        if any(request.path.startswith(p) for p in _csrf_exempt_prefixes):
            return
        token = session.get("csrf_token")
        header = request.headers.get("X-CSRF-Token") or request.form.get("csrf_token")
        if not token or not header or not secrets.compare_digest(token, header):
            if request.is_json or request.headers.get("Accept", "").startswith("application/json"):
                return jsonify({"ok": False, "msg": "Token de sécurité invalide"}), 400
            abort(400)


# ── Headers de sécurité HTTP ──────────────────────────────────────────────────
@app.after_request
def _add_security_headers(response):
    response.headers["X-Frame-Options"]              = "SAMEORIGIN"
    response.headers["X-Content-Type-Options"]       = "nosniff"
    response.headers["Referrer-Policy"]              = "strict-origin-when-cross-origin"
    response.headers["X-XSS-Protection"]             = "1; mode=block"
    # CSP permissif mais fonctionnel (CDN font-awesome)
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline' 'unsafe-eval' https://cdnjs.cloudflare.com; "
        "style-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com https:; "
        "font-src 'self' https://cdnjs.cloudflare.com data: https:; "
        "img-src 'self' data: blob: https:; "
        "connect-src 'self' https:; "
        "frame-src 'self' https:; "
        "frame-ancestors 'self';"
    )
    # Cache long pour les fichiers statiques (CSS/JS/images) — évite les rechargements inutiles
    if request.path.startswith("/static/"):
        response.headers["Cache-Control"] = "public, max-age=604800, immutable"
    dynamic_prefixes = (
        "/api/",
        "/reseau/",
        "/hotspot/",
        "/settings/",
        "/concepteur/",
        "/journaux/",
        "/system/",
        "/dhcp/",
        "/traffic",
        "/report",
        "/impression-rapide",
        "/bons",
    )
    if (
        request.path in {"/", "/login", "/logout", "/sw.js", "/static/manifest.json"}
        or request.path.startswith(dynamic_prefixes)
    ):
        response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
        response.headers["Pragma"] = "no-cache"
        response.headers["Expires"] = "0"
    return response


@app.teardown_request
def _close_request_mikrotik_apis(_exc=None):
    for api in getattr(g, "_mikrotik_apis", []) or []:
        _close_api_quietly(api)
    g._mikrotik_apis = []
    db_mod.release_thread_conn()

@app.context_processor
def inject_csrf_token():
    logo = get_active_ticket_logo()
    return dict(
        csrf_token=session.get("csrf_token", ""),
        ks_enabled=KS_ENABLED,
        standalone_mode=STANDALONE_MODE,
        ticket_logo_url=logo["url"],
        ticket_logo_name=logo["name"],
        ticket_logo_is_custom=logo["is_custom"],
    )

# Initialiser SQLite au démarrage

DATA_DIR         = os.path.join(os.path.dirname(__file__), "data")
ROUTERS_F        = os.path.join(DATA_DIR, "routers.json")
USERS_F          = os.path.join(DATA_DIR, "users.json")
PLANS_F          = os.path.join(DATA_DIR, "plans.json")
SUBSCRIPTIONS_F  = os.path.join(DATA_DIR, "subscriptions.json")
PAY_CONFIG_F     = os.path.join(DATA_DIR, "paiement_config.json")
LOGOS_DIR        = os.path.join(DATA_DIR, "logos")
STATIC_IMG_DIR   = os.path.join(APP_DIR, "static", "img")
DEFAULT_TICKET_LOGO_NAME = "default-ticket-logo.png"
os.makedirs(DATA_DIR, exist_ok=True)
os.makedirs(LOGOS_DIR, exist_ok=True)
os.makedirs(STATIC_IMG_DIR, exist_ok=True)

db_mod.DATA_DIR = DATA_DIR
db_mod.DB_PATH = os.path.join(DATA_DIR, "ketamon.db")
db_mod.LEGACY_USERS_PATH = USERS_F
db_mod.LEGACY_ROUTERS_PATH = ROUTERS_F

_db_ready = threading.Event()
_db_init_error = ""

def _bg_init_db():
    """Init DB en fond : l'app demarre sans attendre, /health repond tout de suite."""
    global _db_init_error
    while True:
        try:
            db_mod.init_db()
            db_mod.release_thread_conn()
            _db_ready.set()
            print("[INIT] DB initialisee avec succes")
            return
        except Exception as _e:
            _db_init_error = f"{type(_e).__name__}: {_e}"
            print(f"[INIT] DB indisponible, retry dans 15s : {_db_init_error}")
            time.sleep(15)

# Init synchrone (SQLite local ou PostgreSQL meme datacenter = rapide)
try:
    db_mod.init_db()
    db_mod.release_thread_conn()
    _db_ready.set()
    print("[INIT] DB initialisee")
except Exception as _e:
    _db_init_error = f"{type(_e).__name__}: {_e}"
    print(f"[INIT] DB erreur, retry en thread: {_e}")
    threading.Thread(target=_bg_init_db, daemon=True, name="db-init").start()


def list_uploaded_logos():
    logos = []
    if not os.path.isdir(LOGOS_DIR):
        return logos
    for filename in os.listdir(LOGOS_DIR):
        if filename.startswith("."):
            continue
        full_path = os.path.join(LOGOS_DIR, filename)
        ext = os.path.splitext(filename)[1].lower()
        if not os.path.isfile(full_path) or ext not in ALLOWED_LOGO_EXT:
            continue
        logos.append({
            "filename": filename,
            "mtime": os.path.getmtime(full_path),
        })
    logos.sort(key=lambda row: (-row["mtime"], row["filename"].lower()))
    return logos


def get_active_ticket_logo():
    uploaded = list_uploaded_logos()
    if uploaded:
        active = uploaded[0]
        return {
            "url": url_for("serve_logo", filename=active["filename"]),
            "name": active["filename"],
            "is_custom": True,
        }
    return {
        "url": url_for("static", filename=f"img/{DEFAULT_TICKET_LOGO_NAME}"),
        "name": DEFAULT_TICKET_LOGO_NAME,
        "is_custom": False,
    }


# ─── Persistence helpers ────────────────────────────────────────────────────

def _current_owner_id():
    """Retourne l'owner_id de l'utilisateur connecté, ou None pour le concepteur (voit tout)."""
    # Contexte session (web)
    if session.get("role") in {"concepteur", "admin"}:
        return None
    if session.get("user_id"):
        return session["user_id"]
    # Contexte API Basic Auth (mobile)
    basic_user = getattr(g, "basic_auth_user", None)
    if basic_user:
        if basic_user.get("role") in {"concepteur", "admin"}:
            return None
        return basic_user.get("email") or basic_user.get("username") or None
    return None

def get_routers():
    return db_mod.db_get_routers(owner_id=_current_owner_id())

def save_routers(routers):
    db_mod.db_replace_routers(routers, owner_id=_current_owner_id())

def get_app_users():
    """Utilisateurs locaux (fallback si KetaServer indispo)."""
    users = db_mod.db_get_local_users()
    if not users:
        initial_pwd = secrets.token_urlsafe(12)
        try:
            db_mod.db_insert_local_user({
                "id": str(uuid.uuid4()),
                "username": "admin",
                "email": "",
                "password": generate_password_hash(initial_pwd),
                "display_name": "admin",
                "role": "admin",
            })
        except db_mod.DuplicateLocalUserError:
            pass
        users = db_mod.db_get_local_users()
        if users:
            print("IMPORTANT: initial admin account created.")
            print(f"  username=admin password={initial_pwd}")
            print("Store this password securely and change it on first login.")
    return users

# ─── Auth helpers ────────────────────────────────────────────────────────────

def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("logged_in"):
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated

def router_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("router_id"):
            # Auto-sélection si un seul routeur enregistré
            routers = get_routers()
            if len(routers) == 1:
                session["router_id"] = routers[0]["id"]
            else:
                flash("Veuillez d'abord sélectionner un routeur.", "warning")
                return redirect(url_for("sessions_list"))
        return f(*args, **kwargs)
    return decorated

def get_active_router():
    rid = session.get("router_id")
    if not rid:
        return None
    for r in get_routers():
        if r["id"] == rid:
            return r
    return None


def _get_requested_router(payload=None):
    routers = get_routers()
    if not routers:
        return None

    payload = payload if isinstance(payload, dict) else {}
    preferred_values = [
        session.get("router_id"),
        payload.get("router_id"),
        payload.get("routerId"),
        payload.get("router"),
        payload.get("router_host"),
        payload.get("routerHost"),
        request.args.get("router_id", ""),
        request.args.get("routerId", ""),
        request.args.get("router", ""),
        request.args.get("host", ""),
        request.headers.get("X-Router-Id", ""),
        request.headers.get("X-Router-Host", ""),
    ]
    for value in preferred_values:
        probe = str(value or "").strip()
        if not probe:
            continue
        for router in routers:
            candidates = {
                str(router.get("id") or "").strip(),
                str(router.get("host") or "").strip(),
                str(router.get("name") or "").strip(),
            }
            if probe in candidates:
                return router
    active_router = get_active_router()
    if active_router:
        return active_router
    return routers[0]

def _local_concepteur_exists() -> bool:
    """Retourne True si un compte concepteur/admin actif existe deja."""
    try:
        for user in db_mod.db_get_local_users():
            role = str(user.get("role") or "").strip().lower()
            if role in {"admin", "concepteur"} and _local_user_is_approved(user) and _local_user_is_active(user):
                return True
    except Exception:
        pass
    return False


def local_register(email, password, display_name=None):
    """Enregistre un utilisateur local dans la base. Retourne user dict."""
    try:
        bootstrap_owner = not _local_concepteur_exists()
        user = db_mod.db_upsert_local_email_user(
            email,
            password_hash=generate_password_hash(password),
            display_name=display_name or email,
            role="concepteur" if bootstrap_owner else "utilisateur",
            approved=1 if bootstrap_owner else 0,
            disabled=0 if bootstrap_owner else 1,
        )
        if user:
            user["displayName"] = user.get("display_name") or user.get("displayName") or email
            user["_bootstrap_owner"] = bool(bootstrap_owner)
        return user
    except db_mod.DuplicateLocalUserError:
        return None
    except Exception:
        return None


def authenticate_local_user(email, password):
    """Verifie un utilisateur local en SQLite. Retourne (user_dict|None)."""
    try:
        user = db_mod.db_get_local_user(email)
        if user:
            stored = user.get("password")
            if stored and check_password_hash(stored, password):
                user["displayName"] = user.get("display_name") or user.get("displayName") or email
                return user
    except Exception:
        pass
    return None


def _local_user_is_approved(user) -> bool:
    try:
        return int((user or {}).get("approved", 1) or 0) == 1
    except Exception:
        return False


def _local_user_is_active(user) -> bool:
    try:
        return int((user or {}).get("disabled", 0) or 0) == 0
    except Exception:
        return False


def _local_user_access_message(user) -> str:
    if not user:
        return "Compte Gmail introuvable."
    if not _local_user_is_approved(user):
        return "Votre compte Gmail est en attente d'activation par le concepteur."
    if not _local_user_is_active(user):
        return "Votre compte Gmail a ete desactive par le concepteur."
    return ""


def _ensure_local_email_shadow(email, password=None, display_name=None, role="utilisateur"):
    email = str(email or "").strip()
    if not is_valid_email(email):
        return None
    existing = db_mod.db_get_local_user(email)
    password_hash = generate_password_hash(password) if password else None
    approved = None
    disabled = None
    if not existing:
        approved = 0
        disabled = 1
    return db_mod.db_upsert_local_email_user(
        email,
        password_hash=password_hash,
        display_name=display_name or email,
        role=role or "utilisateur",
        approved=approved,
        disabled=disabled,
    )


def _check_basic_auth():
    """Vérifie l'en-tête Authorization: Basic pour les endpoints API Android.
    Retourne (ok: bool, user_dict|None). Stocke l'user dans g.basic_auth_user."""
    auth = request.headers.get("Authorization", "")
    if not auth.startswith("Basic "):
        return False, None
    try:
        decoded = base64.b64decode(auth[6:]).decode("utf-8")
        username, _, password = decoded.partition(":")
        user = authenticate_local_user(username, password)
        if user and _local_user_is_approved(user) and _local_user_is_active(user):
            g.basic_auth_user = user
            return True, user
        return False, user
    except Exception:
        return False, None


def build_remote_user_session(resp, fallback_identity, fallback_role="utilisateur"):
    """Normalise les reponses d'auth KetaServer legacy et FastAPI SaaS."""
    if not isinstance(resp, dict):
        return None
    token = resp.get("token") or resp.get("access_token")
    if not token:
        return None
    if resp.get("ok") is False and not resp.get("access_token"):
        return None
    display_name = (
        resp.get("displayName")
        or resp.get("display_name")
        or resp.get("name")
        or fallback_identity
    )
    return {
        "logged_in": True,
        "ks_token": token,
        "ks_refresh_token": resp.get("refresh_token"),
        "username": display_name,
        "role": resp.get("role", fallback_role),
        "user_id": resp.get("user_id") or resp.get("email") or fallback_identity,
        "auth_source": "remote",
    }


def request_payload():
    return request.get_json(silent=True) or request.form

def safe_int(value, default=0, min_val=None, max_val=None):
    """Conversion int sécurisée — jamais de crash sur entrée utilisateur."""
    try:
        v = int(str(value).strip())
        if min_val is not None:
            v = max(min_val, v)
        if max_val is not None:
            v = min(max_val, v)
        return v
    except (ValueError, TypeError):
        return default


class TicketGenerationBusyError(RuntimeError):
    pass


def _ticket_generation_key(router_id):
    key = str(router_id or "").strip()
    return key or "default-router"


def _get_ticket_generation_lock(router_id):
    key = _ticket_generation_key(router_id)
    with _TICKET_GENERATION_GUARD:
        lock = _TICKET_GENERATION_LOCKS.get(key)
        if lock is None:
            lock = threading.Lock()
            _TICKET_GENERATION_LOCKS[key] = lock
        return lock


def _set_ticket_generation_status(router_id, **updates):
    key = _ticket_generation_key(router_id)
    now = datetime.now().isoformat(timespec="seconds")
    with _TICKET_GENERATION_GUARD:
        status = dict(_TICKET_GENERATION_STATUS.get(key) or {})
        status.update(updates)
        status["router_id"] = key
        status["updated_at"] = now
        _TICKET_GENERATION_STATUS[key] = status
        return dict(status)


def get_ticket_generation_status(router_id):
    key = _ticket_generation_key(router_id)
    with _TICKET_GENERATION_GUARD:
        return dict(_TICKET_GENERATION_STATUS.get(key) or {
            "router_id": key,
            "status": "idle",
            "requested": 0,
            "created": 0,
            "profile": "",
            "error": "",
        })


def _ticket_generation_busy_message(router_id):
    status = get_ticket_generation_status(router_id)
    created = int(status.get("created") or 0)
    requested = int(status.get("requested") or 0)
    profile = str(status.get("profile") or "").strip()
    suffix = f" ({created}/{requested} ticket(s)" if requested else ""
    if profile:
        suffix += f", profil {profile}"
    if suffix:
        suffix += ")"
    return f"Une generation est deja en cours sur ce routeur{suffix}. Patiente la fin avant de relancer."


class TicketGenerationJob:
    def __init__(self, router_id, requested, profile="", source="web"):
        self.router_id = _ticket_generation_key(router_id)
        self.requested = int(requested or 0)
        self.profile = str(profile or "").strip()
        self.source = str(source or "web").strip()
        self.lock = _get_ticket_generation_lock(self.router_id)
        self.created = 0
        self.errors = []
        self._finished = False

    def __enter__(self):
        if not self.lock.acquire(blocking=False):
            raise TicketGenerationBusyError(_ticket_generation_busy_message(self.router_id))
        _set_ticket_generation_status(
            self.router_id,
            status="running",
            requested=self.requested,
            created=0,
            profile=self.profile,
            source=self.source,
            started_at=datetime.now().isoformat(timespec="seconds"),
            finished_at="",
            error="",
        )
        return self

    def progress(self, created=None, error=None):
        if created is not None:
            self.created = int(created or 0)
        if error:
            self.errors.append(str(error))
        _set_ticket_generation_status(
            self.router_id,
            status="running",
            requested=self.requested,
            created=self.created,
            profile=self.profile,
            source=self.source,
            error=str(error or ""),
        )

    def finish(self, created=None, errors=None):
        if created is not None:
            self.created = int(created or 0)
        if errors:
            self.errors.extend(str(e) for e in errors if e)
        ok = self.created >= self.requested
        status = "completed" if ok else ("partial" if self.created else "failed")
        last_error = "" if ok else (self.errors[-1] if self.errors else "")
        _set_ticket_generation_status(
            self.router_id,
            status=status,
            requested=self.requested,
            created=self.created,
            profile=self.profile,
            source=self.source,
            finished_at=datetime.now().isoformat(timespec="seconds"),
            error=last_error,
        )
        self._finished = True

    def __exit__(self, exc_type, exc, tb):
        if exc_type is not None and not self._finished:
            _set_ticket_generation_status(
                self.router_id,
                status="failed",
                requested=self.requested,
                created=self.created,
                profile=self.profile,
                source=self.source,
                finished_at=datetime.now().isoformat(timespec="seconds"),
                error=str(exc or "Generation interrompue"),
            )
        elif not self._finished:
            self.finish(self.created, self.errors)
        try:
            self.lock.release()
        except RuntimeError:
            pass
        return False


def _ticket_charset(mode):
    if mode == "chiffres":
        return string.digits
    if mode == "lettres":
        return string.ascii_lowercase
    return string.ascii_lowercase + string.digits


def _load_existing_hotspot_user_names(hotspot_resource):
    try:
        return {
            str(row.get("name") or "").strip()
            for row in hotspot_resource.get()
            if str(row.get("name") or "").strip()
        }
    except Exception:
        return set()


def _next_unique_ticket_name(existing_names, charset, length, prefix):
    for _ in range(250):
        name = prefix + "".join(random.choices(charset, k=length))
        if name not in existing_names:
            existing_names.add(name)
            return name
    raise ValueError("Impossible de generer assez de codes uniques. Augmente la longueur du code ou change le prefixe.")


def _looks_like_duplicate_ticket_error(error):
    text = str(error or "").lower()
    return any(token in text for token in (
        "already",
        "duplicate",
        "existe",
        "exist",
        "same name",
        "with this name",
        "have such",
    ))


def _hotspot_ticket_upsert_source(params):
    params = dict(params or {})
    name = str(params.get("name") or "").strip()
    if not name:
        return ""
    profile = str(params.get("profile") or "default").strip() or "default"
    user_assignments = []
    for key in ("password", "profile", "disabled", "comment", "limit-uptime", "limit-bytes-total", "server"):
        if key in params and str(params.get(key) if params.get(key) is not None else "").strip() != "":
            user_assignments.append(f"{key}={_relay_routeros_quote(params.get(key))}")
    add_assignments = [f"name={_relay_routeros_quote(name)}"] + user_assignments
    return "\n".join([
        f":local ktmProfile [/ip hotspot user profile find where name={_relay_routeros_quote(profile)}];",
        ":if ([:len $ktmProfile] = 0) do={",
        f"  :do {{ /ip hotspot user profile add name={_relay_routeros_quote(profile)}; }} on-error={{}}",
        "}",
        f":local ktmUser [/ip hotspot user find where name={_relay_routeros_quote(name)}];",
        ":if ([:len $ktmUser] > 0) do={",
        f"  /ip hotspot user set $ktmUser {' '.join(user_assignments)};",
        "} else={",
        f"  /ip hotspot user add {' '.join(add_assignments)};",
        "}",
    ])


def _add_or_repair_hotspot_ticket(api, hotspot_resource, params):
    params = dict(params or {})
    if getattr(api, "is_relay_snapshot", False):
        source = _hotspot_ticket_upsert_source(params)
        if not source:
            raise ValueError("Nom ticket manquant.")
        return api.queue_routeros_script(source)
    try:
        return hotspot_resource.add(**params)
    except Exception as ex:
        if not _looks_like_duplicate_ticket_error(ex):
            raise
        name = str(params.get("name") or "").strip()
        if not name:
            raise
        repair_params = dict(params)
        repair_params.pop("name", None)
        item_id = name
        try:
            rows = hotspot_resource.get(name=name)
            if rows:
                item_id = router_action_ref(rows[0])
        except Exception:
            pass
        return hotspot_resource.set(id=item_id, **repair_params)


def create_hotspot_ticket_batch(api, router_id, qty, profile, *,
                                server="", mode="aleatoire", length=8,
                                prefix="", password_mode="identique",
                                comment="", network_name="", data_limit="0",
                                price="0", currency="FCFA",
                                ticket_time_limit="0",
                                ticket_time_limit_label="0",
                                charset_override=None,
                                job=None,
                                source="web"):
    router_id = _ticket_generation_key(router_id)
    qty = safe_int(qty, default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
    profile = str(profile or "default").strip() or "default"
    if job is None:
        with TicketGenerationJob(router_id, qty, profile, source=source) as local_job:
            return create_hotspot_ticket_batch(
                api, router_id, qty, profile,
                server=server, mode=mode, length=length, prefix=prefix,
                password_mode=password_mode, comment=comment,
                network_name=network_name, data_limit=data_limit,
                price=price, currency=currency,
                ticket_time_limit=ticket_time_limit,
                ticket_time_limit_label=ticket_time_limit_label,
                charset_override=charset_override,
                job=local_job,
                source=source,
            )

    hotspot_resource = api.get_resource("/ip/hotspot/user")
    # Ne jamais charger tous les users du routeur avant generation:
    # sur les gros hotspots, cette lecture peut bloquer la PWA.
    existing_names = set()
    charset = charset_override or _ticket_charset(mode)
    now_dt = datetime.now()
    date_str = now_dt.strftime("%Y-%m-%d")
    generated = []
    pricing_batch = []
    errors = []
    data_limit_bytes = None
    if data_limit and data_limit != "0":
        data_limit_bytes = str(int(float(data_limit) * 1024 * 1024))

    batch_size = max(1, int(TICKET_GENERATION_BATCH_SIZE or 100))
    batch_pause = max(0.0, float(TICKET_GENERATION_BATCH_PAUSE or 0))
    max_attempts = max(qty * 5, qty + 50)
    attempts = 0

    def flush_pricing():
        nonlocal pricing_batch
        if pricing_batch:
            db_mod.db_batch_upsert_ticket_pricing(pricing_batch)
            pricing_batch = []

    try:
        while len(generated) < qty and attempts < max_attempts:
            attempts += 1
            try:
                name = _next_unique_ticket_name(existing_names, charset, length, prefix)
            except ValueError as e:
                errors.append(str(e))
                job.progress(len(generated), str(e))
                break

            password = "".join(random.choices(charset, k=length)) if password_mode == "different" else name
            params = {
                "name": name,
                "password": password,
                "profile": profile,
                "disabled": "no",
                "comment": build_hotspot_user_comment(comment, "vc-"),
                "limit-uptime": ticket_time_limit,
            }
            if data_limit_bytes:
                params["limit-bytes-total"] = data_limit_bytes
            if server:
                params["server"] = server

            try:
                _add_or_repair_hotspot_ticket(api, hotspot_resource, params)
            except Exception as ex:
                errors.append(str(ex))
                job.progress(len(generated), str(ex))
                if _looks_like_duplicate_ticket_error(ex):
                    continue
                break

            generated.append({
                "name": name,
                "password": password,
                "profile": profile,
                "price": price,
                "currency": currency,
                "network": network_name,
                "date": date_str,
                "data_limit": data_limit,
                "time_limit": ticket_time_limit_label,
            })
            pricing_batch.append({
                "router_id": router_id,
                "user": name,
                "password": password,
                "prix": float(price) if price and price != "0" else 0.0,
                "devise": currency,
                "profil": profile,
                "reseau": network_name,
            })

            if len(generated) % batch_size == 0:
                flush_pricing()
                job.progress(len(generated))
                if batch_pause:
                    time.sleep(batch_pause)

        flush_pricing()
        job.finish(len(generated), errors)
        return generated, errors
    except Exception as ex:
        errors.append(str(ex))
        job.progress(len(generated), str(ex))
        raise

_EMAIL_RE = re.compile(r"^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$")

def is_valid_email(email: str) -> bool:
    return bool(_EMAIL_RE.match(str(email or "").strip()))

import logging as _logging
_logger = _logging.getLogger("ketamon")

def _flash_err(msg: str, e: Exception = None, level: str = "danger") -> None:
    """Flash un message générique et logue le vrai détail sans l'exposer à l'utilisateur."""
    if e is not None:
        _logger.error("[ketamon] %s — %s: %s", msg, type(e).__name__, e)
    flash(msg, level)


def router_item_id(item):
    if not isinstance(item, dict):
        return ""
    return str(item.get("id") or item.get(".id") or "").strip()


def _is_real_router_item_id(value):
    text = str(value or "").strip()
    return bool(text.startswith("*") and not text.startswith("*db-"))


def router_action_ref(item, name_key="name"):
    if not isinstance(item, dict):
        return ""
    item_id = router_item_id(item)
    if _is_real_router_item_id(item_id):
        return item_id
    return str(item.get(name_key) or "").strip() or item_id


def _routeros_find_target(path, name, name_key="name"):
    path_cmd = _relay_routeros_path(path)
    key = _relay_routeros_key(name_key or "name")
    return f"{path_cmd} find where {key}={_relay_routeros_quote(name)}"


def _routeros_set_by_name_source(path, name, params, name_key="name"):
    path_cmd = _relay_routeros_path(path)
    find_cmd = _routeros_find_target(path, name, name_key=name_key)
    assignments = []
    for key, value in dict(params or {}).items():
        key = _relay_routeros_key(key)
        if not key or key in {"id", ".id"}:
            continue
        assignments.append(f"{key}={_relay_routeros_quote(value)}")
    return "\n".join([
        f":local ktmIds [{find_cmd}];",
        ":if ([:len $ktmIds] > 0) do={",
        f"  {path_cmd} set $ktmIds {' '.join(assignments)};",
        "}",
    ])


def _resource_rows_by_id_or_name(resource, item_id="", name="", name_key="name"):
    item_id = str(item_id or "").strip()
    name = str(name or "").strip()
    rows = []
    if item_id:
        try:
            rows = resource.get(id=item_id)
        except Exception:
            rows = []
    if not rows and name:
        try:
            rows = resource.get(**{name_key: name})
        except Exception:
            rows = []
    if not rows and item_id and not _is_real_router_item_id(item_id):
        try:
            rows = resource.get(**{name_key: item_id})
        except Exception:
            rows = []
    return rows or []


def router_resource_remove_by_id_or_name(api, path, item_id="", name="", name_key="name"):
    resource = api.get_resource(path)
    item_id = str(item_id or "").strip()
    name = str(name or "").strip()
    if _is_real_router_item_id(item_id):
        resource.remove(id=item_id)
        return True
    target_name = name or item_id
    if not target_name:
        return False
    if hasattr(api, "queue_routeros_script"):
        source = f"{_relay_routeros_path(path)} remove [{_routeros_find_target(path, target_name, name_key=name_key)}];"
        api.queue_routeros_script(source)
        return True
    rows = _resource_rows_by_id_or_name(resource, item_id=item_id, name=target_name, name_key=name_key)
    removed = False
    for row in rows:
        rid = router_item_id(row)
        if rid:
            resource.remove(id=rid)
            removed = True
    return removed


def router_resource_set_by_id_or_name(api, path, params, item_id="", name="", name_key="name"):
    resource = api.get_resource(path)
    item_id = str(item_id or "").strip()
    name = str(name or "").strip()
    params = dict(params or {})
    if _is_real_router_item_id(item_id):
        resource.set(id=item_id, **params)
        return True
    target_name = name or item_id
    if not target_name:
        return False
    if hasattr(api, "queue_routeros_script"):
        api.queue_routeros_script(_routeros_set_by_name_source(path, target_name, params, name_key=name_key))
        return True
    rows = _resource_rows_by_id_or_name(resource, item_id=item_id, name=target_name, name_key=name_key)
    updated = False
    for row in rows:
        rid = router_item_id(row)
        if rid:
            resource.set(id=rid, **params)
            updated = True
    return updated


def parse_routeros_duration(value):
    text = str(value or "").strip().lower()
    if not text or text in {"0", "0s", "none", "unlimited", "infinite", "inf", "?"}:
        return None

    total = 0
    for amount, unit in re.findall(r"(\d+)\s*([wdhms])", text):
        amount = int(amount)
        if unit == "w":
            total += amount * 7 * 24 * 3600
        elif unit == "d":
            total += amount * 24 * 3600
        elif unit == "h":
            total += amount * 3600
        elif unit == "m":
            total += amount * 60
        elif unit == "s":
            total += amount
    text = re.sub(r"(\d+)\s*[wdhms]", "", text).strip()

    if text:
        parts = [p for p in text.split(":") if p != ""]
        if len(parts) == 3 and all(part.isdigit() for part in parts):
            hours, minutes, seconds = map(int, parts)
            total += hours * 3600 + minutes * 60 + seconds
        elif len(parts) == 2 and all(part.isdigit() for part in parts):
            minutes, seconds = map(int, parts)
            total += minutes * 60 + seconds
        elif text.isdigit():
            total += int(text)
        else:
            return None

    return total if total > 0 else None


def format_duration_compact(seconds):
    if seconds is None:
        return "∞"
    seconds = max(0, int(seconds))
    if seconds == 0:
        return "0s"

    chunks = []
    for suffix, unit in (("w", 7 * 24 * 3600), ("d", 24 * 3600), ("h", 3600), ("m", 60), ("s", 1)):
        if seconds < unit:
            continue
        value, seconds = divmod(seconds, unit)
        if value:
            chunks.append(f"{value}{suffix}")
        if len(chunks) == 2:
            break
    return " ".join(chunks) or "0s"


def build_active_disconnect_targets(active_rows):
    usernames = []
    addresses = []
    mac_addresses = []
    active_ids = []
    for active in active_rows or []:
        username = str(active.get("user") or "").strip()
        address = str(active.get("address") or "").strip()
        mac_address = str(active.get("mac-address") or "").strip()
        active_id = router_item_id(active)
        if username:
            usernames.append(username)
        if address:
            addresses.append(address)
        if mac_address:
            mac_addresses.append(mac_address)
        if active_id:
            active_ids.append(active_id)
    return usernames, addresses, mac_addresses, active_ids


def find_matching_hotspot_active_rows(api, usernames=None, addresses=None, mac_addresses=None):
    usernames = {str(name or '').strip() for name in (usernames or []) if str(name or '').strip()}
    addresses = {str(address or '').strip() for address in (addresses or []) if str(address or '').strip()}
    mac_addresses = {str(mac or '').strip().lower() for mac in (mac_addresses or []) if str(mac or '').strip()}
    try:
        rows = []
        for row in api.get_resource('/ip/hotspot/active').get():
            username = str(row.get('user') or '').strip()
            address = str(row.get('address') or '').strip()
            mac_address = str(row.get('mac-address') or '').strip().lower()
            if not usernames and not addresses and not mac_addresses:
                rows.append(row)
                continue
            if (username and username in usernames) or (address and address in addresses) or (mac_address and mac_address in mac_addresses):
                rows.append(row)
        return rows
    except Exception:
        return []


def disconnect_hotspot_entities(api, usernames=None, addresses=None, mac_addresses=None, active_ids=None):
    usernames = {str(name or "").strip() for name in (usernames or []) if str(name or "").strip()}
    addresses = {str(address or "").strip() for address in (addresses or []) if str(address or "").strip()}
    mac_addresses = {str(mac or "").strip().lower() for mac in (mac_addresses or []) if str(mac or "").strip()}
    active_ids = {str(active_id or "").strip() for active_id in (active_ids or []) if str(active_id or "").strip()}
    removed = {"active_sessions": 0, "cookies": 0, "hosts": 0}

    try:
        active_resource = api.get_resource("/ip/hotspot/active")
        for active in active_resource.get():
            active_id = router_item_id(active)
            username = str(active.get("user") or "").strip()
            address = str(active.get("address") or "").strip()
            mac_address = str(active.get("mac-address") or "").strip().lower()
            if (
                active_id in active_ids
                or username in usernames
                or address in addresses
                or (mac_address and mac_address in mac_addresses)
            ):
                if address:
                    addresses.add(address)
                if mac_address:
                    mac_addresses.add(mac_address)
                if active_id:
                    active_resource.remove(id=active_id)
                    removed["active_sessions"] += 1
    except Exception:
        pass

    try:
        cookie_resource = api.get_resource("/ip/hotspot/cookie")
        for cookie in cookie_resource.get():
            cookie_id = router_item_id(cookie)
            username = str(cookie.get("user") or "").strip()
            mac_address = str(cookie.get("mac-address") or "").strip().lower()
            if username in usernames or (mac_address and mac_address in mac_addresses):
                if mac_address:
                    mac_addresses.add(mac_address)
                if cookie_id:
                    cookie_resource.remove(id=cookie_id)
                    removed["cookies"] += 1
    except Exception:
        pass

    try:
        host_resource = api.get_resource("/ip/hotspot/host")
        for host in host_resource.get():
            host_id = router_item_id(host)
            address = str(host.get("address") or "").strip()
            mac_address = str(host.get("mac-address") or "").strip().lower()
            if address in addresses or (mac_address and mac_address in mac_addresses):
                if host_id:
                    host_resource.remove(id=host_id)
                    removed["hosts"] += 1
    except Exception:
        pass

    return removed


def compute_active_time_left(active_row, user_row):
    comment = str(user_row.get("comment") or active_row.get("user_comment") or "").strip()
    expire_dt = _extract_ketamon_expire_datetime(comment)
    if expire_dt:
        remaining = int((expire_dt - datetime.now()).total_seconds())
        return format_duration_compact(remaining) if remaining > 0 else "Expiré"

    direct_left = parse_routeros_duration(active_row.get("session-time-left"))
    if direct_left is not None:
        return format_duration_compact(direct_left)

    limit_seconds = parse_routeros_duration(user_row.get("limit-uptime"))
    if limit_seconds is None:
        return "∞"

    used_seconds = parse_routeros_duration(user_row.get("uptime-used"))
    if used_seconds is None:
        used_seconds = parse_routeros_duration(active_row.get("uptime")) or 0
    return format_duration_compact(limit_seconds - used_seconds)


def _fmt_bytes(val):
    """Formate un nombre d'octets en KB / MB / GB lisible."""
    try:
        b = int(val or 0)
    except Exception:
        return "-"
    if b == 0:
        return "0"
    if b < 1024 * 1024:
        return f"{b/1024:.1f} KB"
    if b < 1024 * 1024 * 1024:
        return f"{b/1024/1024:.1f} MB"
    return f"{b/1024/1024/1024:.2f} GB"


def _traffic_client_bytes(active_row):
    """RouterOS active bytes-out = recu par le client, bytes-in = envoye par le client."""
    active_row = dict(active_row or {})
    download = active_row.get("bytes-out", 0)
    upload = active_row.get("bytes-in", 0)
    return download, upload


def normalize_active_sessions(api, active_rows, users_map=None):
    if users_map is None:
        try:
            users_map = {
                str(user.get("name") or "").strip(): dict(user)
                for user in api.get_resource("/ip/hotspot/user").get()
            }
        except Exception:
            users_map = {}

    normalized = []
    for active in active_rows or []:
        row = dict(active)
        row["id"] = router_item_id(active)
        user_row = users_map.get(str(row.get("user") or "").strip(), {})
        row["temps-restant"] = compute_active_time_left(row, user_row)
        download_bytes, upload_bytes = _traffic_client_bytes(row)
        row["debit-down"] = _fmt_bytes(download_bytes)
        row["debit-up"]   = _fmt_bytes(upload_bytes)
        row["download-bytes"] = str(download_bytes or "0")
        row["upload-bytes"] = str(upload_bytes or "0")
        uid = router_item_id(user_row)
        # En mode relay : si pas d'ID MikroTik, le nom suffit pour les operations relay (find where name=...)
        if not uid and getattr(api, "is_relay_snapshot", False):
            uid = str(row.get("user") or "").strip()
        row["user_hotspot_id"] = uid
        profile_val = str(user_row.get("profile") or "").strip()
        row["profile"] = profile_val if profile_val and profile_val != "-" else "-"
        row["limit-uptime"] = str(user_row.get("limit-uptime") or "0")
        row["bytes-in-total"]  = str(user_row.get("bytes-in",  row.get("bytes-in",  0)))
        row["bytes-out-total"] = str(user_row.get("bytes-out", row.get("bytes-out", 0)))
        row["user_disabled"] = str(user_row.get("disabled", "no")).strip().lower() == "yes"
        row["user_comment"] = str(user_row.get("comment") or "")
        normalized.append(row)
    return normalized


def normalize_ticket_time_limit(value):
    text = str(value or "").strip()
    if not text:
        return ""
    seconds = _parse_ticket_time_limit_seconds(text, prefer_legacy_routeros=True)
    if seconds is None:
        return text
    if seconds <= 0:
        return "0"
    return _seconds_to_user_time_limit(seconds)


def normalize_profile_time_limit(value):
    """Normalise une durée stockée dans les métadonnées KetaMon d'un profil."""
    text = str(value or "").strip()
    if not text:
        return ""
    compact = _compact_time_limit_text(text)
    if not compact:
        return ""
    prefer_legacy = compact.lower() == compact and _looks_like_legacy_routeros_time_limit(compact)
    seconds = _parse_ticket_time_limit_seconds(text, prefer_legacy_routeros=prefer_legacy)
    if seconds is None:
        return text
    if seconds <= 0:
        return "0"
    return _seconds_to_user_time_limit(seconds)


_TIME_LIMIT_ZERO_ALIASES = {
    "0", "0s", "0mn", "0m", "none", "illimite", "illimitee", "illimitee",
    "unlimited", "infinite", "inf", "no-limit", "nolimit",
}
_TIME_LIMIT_ERROR = "Durée invalide. Exemples acceptés : 2H, 30mn, 7D, 1M, 0."
_USER_TIME_LIMIT_PATTERN = re.compile(
    r"(\d+)(mn|min|minutes?|minute|heures?|heure|hours?|hour|jours?|jour|days?|day|"
    r"months?|month|mois|weeks?|week|semaines?|semaine|sem|secs?|seconds?|secondes?|"
    r"seconde|[MHDWhdwsmj])",
    re.IGNORECASE,
)


def _normalize_ascii_text(value):
    text = unicodedata.normalize("NFKD", str(value or ""))
    return "".join(ch for ch in text if not unicodedata.combining(ch))


def _compact_time_limit_text(value):
    return re.sub(r"[\s,;]+", "", str(value or "").strip())


def _looks_like_legacy_routeros_time_limit(value):
    compact = _compact_time_limit_text(value).lower()
    if not compact or compact in _TIME_LIMIT_ZERO_ALIASES:
        return False
    return bool(
        re.fullmatch(r"(?:\d+[wdhms])+", compact)
        or re.fullmatch(r"(?:\d+[wdhs])*(?:\d+:\d+(?::\d+)?)", compact)
        or compact.isdigit()
    )


def _parse_user_time_limit_seconds(value):
    compact = _compact_time_limit_text(value)
    normalized = _normalize_ascii_text(compact).lower()
    if not normalized:
        return None
    if normalized in _TIME_LIMIT_ZERO_ALIASES:
        return 0
    if normalized.isdigit():
        return int(normalized)

    total = 0
    pos = 0
    matched = False
    for match in _USER_TIME_LIMIT_PATTERN.finditer(compact):
        if match.start() != pos:
            return None
        matched = True
        amount = int(match.group(1))
        unit = _normalize_ascii_text(match.group(2)).lower()
        if unit in {"mn", "min", "minute", "minutes"}:
            total += amount * 60
        elif unit in {"h", "heure", "heures", "hour", "hours"}:
            total += amount * 3600
        elif unit in {"d", "j", "jour", "jours", "day", "days"}:
            total += amount * 86400
        elif unit in {"w", "week", "weeks", "sem", "semaine", "semaines"}:
            total += amount * 7 * 86400
        elif unit in {"m", "mois", "month", "months"}:
            total += amount * 30 * 86400
        elif unit in {"s", "sec", "secs", "second", "seconds", "seconde", "secondes"}:
            total += amount
        else:
            return None
        pos = match.end()

    if not matched or pos != len(compact):
        return None
    return total


def _parse_ticket_time_limit_seconds(value, prefer_legacy_routeros=False):
    compact = _compact_time_limit_text(value)
    normalized = _normalize_ascii_text(compact).lower()
    if not compact:
        return None
    if normalized in _TIME_LIMIT_ZERO_ALIASES:
        return 0

    if prefer_legacy_routeros and _looks_like_legacy_routeros_time_limit(compact):
        legacy_seconds = parse_routeros_duration(compact)
        if legacy_seconds is not None:
            return legacy_seconds

    user_seconds = _parse_user_time_limit_seconds(compact)
    if user_seconds is not None:
        return user_seconds

    if ":" in compact:
        return parse_routeros_duration(compact)
    return None


def _seconds_to_routeros_time_limit(seconds):
    seconds = max(0, int(seconds or 0))
    if seconds == 0:
        return "0"
    chunks = []
    for suffix, unit in (("w", 7 * 24 * 3600), ("d", 24 * 3600), ("h", 3600), ("m", 60), ("s", 1)):
        value, seconds = divmod(seconds, unit)
        if value:
            chunks.append(f"{value}{suffix}")
    return "".join(chunks) or "0"


def _seconds_to_user_time_limit(seconds):
    seconds = max(0, int(seconds or 0))
    if seconds == 0:
        return "0"
    chunks = []
    for suffix, unit in (("M", 30 * 24 * 3600), ("w", 7 * 24 * 3600), ("d", 24 * 3600), ("h", 3600), ("mn", 60), ("s", 1)):
        value, seconds = divmod(seconds, unit)
        if value:
            chunks.append(f"{value}{suffix}")
    return "".join(chunks) or "0"


def coerce_ticket_time_limit_user(value, empty="", prefer_legacy_routeros=False):
    text = str(value or "").strip()
    if not text:
        return empty
    seconds = _parse_ticket_time_limit_seconds(text, prefer_legacy_routeros=prefer_legacy_routeros)
    if seconds is None:
        raise ValueError(_TIME_LIMIT_ERROR)
    if seconds <= 0:
        return "0"
    return _seconds_to_user_time_limit(seconds)


def coerce_ticket_time_limit_router(value, empty="", prefer_legacy_routeros=False):
    text = str(value or "").strip()
    if not text:
        return empty
    seconds = _parse_ticket_time_limit_seconds(text, prefer_legacy_routeros=prefer_legacy_routeros)
    if seconds is None:
        raise ValueError(_TIME_LIMIT_ERROR)
    if seconds <= 0:
        return "0"
    return _seconds_to_routeros_time_limit(seconds)


def build_profile_comment_metadata(price, currency, expire_mode, lock_user, time_limit="0"):
    payload = {
        "price": str(price or "0"),
        "currency": str(currency or "FCFA"),
        "expire_mode": str(expire_mode or "none"),
        "lock_user": str(lock_user or "yes"),
        "time_limit": coerce_ticket_time_limit_user(time_limit, empty="0", prefer_legacy_routeros=False) or "0",
    }
    return PROFILE_META_PREFIX + json.dumps(payload, ensure_ascii=True, separators=(",", ":"))


def parse_profile_comment_metadata(profile):
    comment = str((profile or {}).get("comment") or "").strip()
    if not comment.startswith(PROFILE_META_PREFIX):
        return {}
    raw = comment[len(PROFILE_META_PREFIX):].strip()
    if not raw:
        return {}
    try:
        payload = json.loads(raw)
    except Exception:
        return {}
    return payload if isinstance(payload, dict) else {}


def get_hotspot_profile_metadata_map(router_id):
    metadata_rows = db_mod.db_get_hotspot_profile_metadata(router_id) or []
    mapping = {}
    for row in metadata_rows:
        profile_name = str(row.get("profile_name") or "").strip()
        if profile_name:
            inferred_time = _infer_time_limit_from_profile_name(profile_name)
            stored_time = str(row.get("time_limit") or "").strip().lower()
            if inferred_time and stored_time in {"", "0", "0s", "none"}:
                row = dict(row)
                row["time_limit"] = inferred_time
                if str(row.get("expire_mode") or "").strip().lower() in {"", "none"}:
                    row["expire_mode"] = "remove and record"
                if str(row.get("lock_user") or "").strip().lower() in {"", "no", "false", "0"}:
                    row["lock_user"] = "yes"
            mapping[profile_name] = row
    return mapping


def _split_ticket_runtime_comment(comment):
    raw_comment = str(comment or "").strip()
    for marker in KETAMON_TICKET_COMMENT_MARKERS:
        pos = raw_comment.find(marker)
        if pos != -1:
            return raw_comment[:pos].rstrip(), raw_comment[pos + len(marker):].strip()
    return raw_comment, None


_ROS_MONTH_MAP = {
    "jan": "01", "feb": "02", "mar": "03", "apr": "04",
    "may": "05", "jun": "06", "jul": "07", "aug": "08",
    "sep": "09", "oct": "10", "nov": "11", "dec": "12",
}

def _ros_date_to_iso(ros_date):
    """Convertit 'may/12/2026' → '2026-05-12'. Retourne '' si invalide."""
    try:
        parts = str(ros_date).strip().split("/")
        if len(parts) == 3:
            mon = _ROS_MONTH_MAP.get(parts[0].lower()[:3])
            if mon:
                return f"{parts[2]}-{mon}-{int(parts[1]):02d}"
    except Exception:
        pass
    return ""

def _extract_ticket_key(username, comment):
    """Construit la clé unique d'un ticket : 'username:expiry' ou 'username' si pas de marqueur."""
    _base_comment, expiry = _split_ticket_runtime_comment(comment)
    if expiry:
        return f"{username}:{expiry}"
    return username


def _parse_ketamon_expire(expire_raw):
    """Parse la valeur d'expiry depuis un commentaire KetaMon.

    Nouveau format (epoch entier, survivant aux reboots) : "1735000000"
    Ancien format (RouterOS datetime, boot-relatif) : "jan/27/2026 15:30:00"
    Retourne un datetime naïf comparable à datetime.now(), ou None si invalide.
    """
    s = (expire_raw or "").strip()
    if s.isdigit() and len(s) >= 9:
        return datetime(1970, 1, 1) + timedelta(seconds=int(s))
    for fmt, size in (
        ("%b/%d/%Y %H:%M:%S", 20),
        ("%Y-%m-%d %H:%M:%S", 19),
        ("%Y-%m-%d %H:%M", 16),
    ):
        try:
            return datetime.strptime(s[:size], fmt)
        except Exception:
            continue
    return None


def _extract_ketamon_expire_datetime(comment):
    """Extrait l'expiration absolue KetaMon depuis un commentaire user."""
    _base_comment, expire_raw = _split_ticket_runtime_comment(comment)
    if expire_raw is None:
        return None
    if not expire_raw:
        return None
    return _parse_ketamon_expire(expire_raw)


def _is_ketamon_ticket_comment(comment):
    base_comment = str(comment or "").strip()
    return (
        base_comment.startswith("vc-")
        or base_comment.startswith("up-")
        or any(marker in base_comment for marker in KETAMON_TICKET_COMMENT_MARKERS)
    )


def _build_first_used_map(router_id):
    first_used_map = {}
    if not router_id:
        return first_used_map
    try:
        # Source primaire : ticket_pricing.first_used_at (fiable même pour tickets gratuits)
        conn = db_mod.get_conn()
        tp_rows = conn.execute(
            "SELECT user, first_used_at FROM ticket_pricing"
            " WHERE router_id=? AND first_used_at IS NOT NULL AND first_used_at != ''",
            (router_id,)
        ).fetchall()
        for row in tp_rows:
            uname = str(row[0] or "").strip()
            fua   = str(row[1] or "").strip()
            if uname and fua:
                first_used_map[uname] = fua[:16]
    except Exception:
        pass
    try:
        # Fallback : ventes (anciens tickets sans first_used_at en DB)
        all_v = db_mod.db_get_ventes(router_id)
        for v in reversed(all_v):
            uname = str(v.get("user") or "").strip()
            if uname and uname not in first_used_map:
                first_used_map[uname] = f"{v.get('date', '')} {v.get('heure', '')[:5]}"
    except Exception:
        pass
    return first_used_map


def _ticket_db_meta(router_id, username):
    router_id = str(router_id or "").strip()
    username = str(username or "").strip()
    if not router_id or not username:
        return {}
    try:
        conn = db_mod.get_conn()
        row = conn.execute("""
            SELECT tp.user, tp.profil, tp.reseau, tp.first_used_at, tp.expire_at,
                   hp.time_limit, hp.expire_mode
            FROM ticket_pricing tp
            LEFT JOIN hotspot_profile_metadata hp
              ON hp.router_id=tp.router_id AND hp.profile_name=tp.profil
            WHERE tp.router_id=? AND tp.user=?
            LIMIT 1
        """, (router_id, username)).fetchone()
        return dict(row) if row else {}
    except Exception:
        return {}


def _infer_time_limit_from_profile_name(profile_name):
    text = str(profile_name or "").strip()
    if not text:
        return ""
    try:
        return coerce_ticket_time_limit_user(text, empty="", prefer_legacy_routeros=False) or ""
    except Exception:
        pass
    match = _USER_TIME_LIMIT_PATTERN.search(text)
    if not match:
        return ""
    try:
        return coerce_ticket_time_limit_user(match.group(0), empty="", prefer_legacy_routeros=False) or ""
    except Exception:
        return ""


def _ticket_meta_time_limit(meta):
    if not meta:
        return ""
    raw = str(meta.get("time_limit") or "").strip()
    if raw and raw.lower() not in {"0", "0s", "none"}:
        return raw
    return _infer_time_limit_from_profile_name(meta.get("profil") or meta.get("profile") or "")


def _enrich_active_users_from_database(router_id, active_rows, users_map):
    users_map = dict(users_map or {})
    for active in active_rows or []:
        username = str((active or {}).get("user") or "").strip()
        if not username:
            continue
        meta = _ticket_db_meta(router_id, username)
        limit_source = _ticket_meta_time_limit(meta) if meta else ""
        limit_uptime = coerce_ticket_time_limit_router(limit_source, empty="0", prefer_legacy_routeros=False) or "0" if limit_source else "0"
        existing = users_map.get(username)
        if existing:
            if limit_uptime and limit_uptime not in {"0", "0s", "none"}:
                current_limit = str(existing.get("limit-uptime") or "").strip().lower()
                if current_limit in {"", "0", "0s", "none"}:
                    existing["limit-uptime"] = limit_uptime
            if not str(existing.get("profile") or "").strip() or str(existing.get("profile") or "").strip() == "-":
                if meta:
                    existing["profile"] = meta.get("profil") or "default"
            if not existing.get("comment") and meta:
                existing["comment"] = "restored-from-database"
            # Garantir un .id pour les operations relay par nom
            if not existing.get(".id") and not existing.get("id"):
                existing[".id"] = username
            users_map[username] = existing
            continue
        # Creer un user_row meme si absent de ticket_pricing (active session connue, ticket inconnu)
        users_map[username] = {
            "name": username,
            ".id": username,  # relay utilise [find where name=...] quand l'ID n'est pas un vrai ID MikroTik
            "profile": (meta.get("profil") or "default") if meta else "-",
            "limit-uptime": limit_uptime,
            "uptime": str((active or {}).get("uptime") or "0"),
            "bytes-in": str((active or {}).get("bytes-in") or "0"),
            "bytes-out": str((active or {}).get("bytes-out") or "0"),
            "disabled": "no",
            "comment": "restored-from-database" if meta else "",
            "_source": "database" if meta else "active-only",
        }
    return users_map


def _cleanup_expired_active_from_database(api, router_id, active_rows, first_used_map):
    cleaned = 0
    now = datetime.now()
    for active in active_rows or []:
        username = str((active or {}).get("user") or "").strip()
        if not username:
            continue
        meta = _ticket_db_meta(router_id, username)
        if not meta:
            continue
        # Source primaire : expire_at sauvegardé en DB (expiration absolue serveur)
        expire_at_str = str(meta.get("expire_at") or "").strip()
        if expire_at_str:
            try:
                expire_check = datetime.fromisoformat(expire_at_str)
                if now < expire_check:
                    continue  # Pas encore expiré
                # Expiré selon DB → couper
            except Exception:
                expire_at_str = ""
        if not expire_at_str:
            # Fallback : calcul depuis first_used + limit_seconds (anciens tickets sans expire_at)
            limit_seconds = parse_routeros_duration(coerce_ticket_time_limit_router(_ticket_meta_time_limit(meta), empty="0", prefer_legacy_routeros=False) or "0")
            first_dt = _effective_first_used_datetime(first_used_map.get(username), active, now=now)
            if not first_dt or not limit_seconds or limit_seconds <= 0:
                continue
            if now < first_dt + timedelta(seconds=limit_seconds):
                continue
        address = str((active or {}).get("address") or "").strip()
        mac = str((active or {}).get("mac-address") or "").strip()
        try:
            if hasattr(api, "queue_routeros_script"):
                source = "\n".join([
                    ':put "KETAMON_EXPIRE_ENFORCE";',
                    f"/ip hotspot active remove [find where user={_relay_routeros_quote(username)}];",
                    f"/ip hotspot cookie remove [find where user={_relay_routeros_quote(username)}];",
                    f"/ip hotspot user remove [find where name={_relay_routeros_quote(username)}];",
                    f"/ip hotspot host remove [find where address={_relay_routeros_quote(address)}];" if address else "",
                    f"/ip hotspot host remove [find where mac-address={_relay_routeros_quote(mac)}];" if mac else "",
                ])
                api.queue_routeros_script(source)
            else:
                disconnect_hotspot_entities(api, usernames=[username], addresses=[address], mac_addresses=[mac])
                rows = api.get_resource("/ip/hotspot/user").get(name=username)
                for row in rows or []:
                    uid = router_item_id(row)
                    if uid:
                        api.get_resource("/ip/hotspot/user").remove(id=uid)
            try:
                db_mod.db_delete_ticket_pricing(router_id, [username])
            except Exception:
                pass
            cleaned += 1
        except Exception:
            pass
    return cleaned


def _relay_snapshot_rows_from_db(router_id, resource):
    try:
        snapshots = db_mod.db_get_router_relay_snapshot(router_id)
        meta = snapshots.get(resource) if isinstance(snapshots, dict) else None
        rows = (meta or {}).get("data") or []
        return [dict(row) for row in rows if isinstance(row, dict)]
    except Exception:
        return []


def _nonzero_time_limit(value):
    text = str(value or "").strip()
    return bool(text and text.lower() not in {"0", "0s", "none"})


def _sync_relay_profile_metadata(router_id, profile_rows):
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0
    synced = 0
    for profile_row in profile_rows or []:
        row = dict(profile_row or {})
        profile_name = str(row.get("name") or "").strip()
        if not profile_name:
            continue
        parsed = parse_profile_comment_metadata(row)
        existing = db_mod.db_get_hotspot_profile_metadata(router_id, profile_name) or {}
        inferred_time = _infer_time_limit_from_profile_name(profile_name)
        existing_time = str(existing.get("time_limit") or "").strip()
        parsed_time = str(parsed.get("time_limit") or "").strip()
        if _nonzero_time_limit(parsed_time):
            time_limit = parsed_time
        elif _nonzero_time_limit(existing_time):
            time_limit = existing_time
        elif inferred_time:
            time_limit = inferred_time
        else:
            time_limit = existing_time or "0"

        price = str(parsed.get("price") if parsed.get("price") is not None else existing.get("price") or "0").strip() or "0"
        currency = str(parsed.get("currency") or existing.get("currency") or "FCFA").strip() or "FCFA"
        expire_mode = str(parsed.get("expire_mode") or existing.get("expire_mode") or "").strip()
        if not expire_mode or (expire_mode.lower() == "none" and inferred_time):
            expire_mode = "remove and record" if inferred_time else "none"
        lock_user = str(parsed.get("lock_user") or existing.get("lock_user") or row.get("add-mac-cookie") or "").strip()
        if not lock_user or (lock_user.lower() in {"no", "false", "0"} and inferred_time):
            lock_user = "yes" if inferred_time else "no"
        try:
            db_mod.db_upsert_hotspot_profile_metadata(
                router_id,
                profile_name,
                price=price,
                currency=currency,
                expire_mode=expire_mode,
                lock_user=lock_user,
                time_limit=time_limit,
            )
            synced += 1
        except Exception:
            continue
    return synced


def _sync_relay_ticket_pricing_from_users(router_id, user_rows):
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0
    metadata_map = get_hotspot_profile_metadata_map(router_id)
    conn = db_mod.get_conn()
    existing_rows = conn.execute(
        "SELECT user, prix, profil FROM ticket_pricing WHERE router_id=?",
        (router_id,),
    ).fetchall()
    existing = {
        str(row["user"] or "").strip(): {
            "prix": float(row["prix"] or 0),
            "profil": str(row["profil"] or "").strip(),
        }
        for row in existing_rows
        if str(row["user"] or "").strip()
    }
    batch = []
    for user_row in user_rows or []:
        row = dict(user_row or {})
        username = str(row.get("name") or "").strip()
        if not username:
            continue
        profile = str(row.get("profile") or "").strip() or "default"
        meta = metadata_map.get(profile, {})
        try:
            meta_price = float(str(meta.get("price") or "0").strip() or 0)
        except Exception:
            meta_price = 0.0
        old = existing.get(username)
        if old and old.get("profil") and (old.get("prix") or 0) > 0:
            continue
        if old and old.get("profil") == profile and (old.get("prix") or 0) == meta_price:
            continue
        batch.append({
            "router_id": router_id,
            "user": username,
            "password": row.get("password") or username,
            "prix": meta_price,
            "devise": meta.get("currency") or "FCFA",
            "profil": profile,
            "reseau": row.get("server") or "",
        })
    if not batch:
        return 0
    db_mod.db_batch_upsert_ticket_pricing(batch)
    return len(batch)


def _sync_relay_snapshot_database(router_id, resources):
    resources = resources if isinstance(resources, dict) else {}
    profile_rows = resources.get("/ip/hotspot/user/profile") or []
    user_rows = resources.get("/ip/hotspot/user") or []
    profiles = _sync_relay_profile_metadata(router_id, profile_rows)
    tickets = _sync_relay_ticket_pricing_from_users(router_id, user_rows)
    return {"profiles": profiles, "tickets": tickets}


_RELAY_AUTO_UPGRADE_LAST = {}


def _relay_resource_counts(resources):
    resources = resources if isinstance(resources, dict) else {}
    return {
        str(resource): len(rows or []) if isinstance(rows, list) else 0
        for resource, rows in resources.items()
    }


def _relay_auto_upgrade_source(token):
    install_url = (
        f"{_relay_public_base_url()}/api/relay/routeros/install.rsc"
        f"?token={quote(str(token or ''))}"
    )
    return "\n".join([
        ':put "KETAMON_RELAY_AUTO_UPGRADE";',
        ':do {',
        '  :do { /system scheduler remove [find name="ketamon-relay-auto-upgrade"]; } on-error={};',
        '  :do { /system script remove [find name="ketamon-relay-auto-upgrade"]; } on-error={};',
        '  /system script add name="ketamon-relay-auto-upgrade" policy=ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon source={',
        '    :delay 3s;',
        '    :do {',
        f'      /tool fetch url="{install_url}" dst-path="ketamon-relay-install.rsc";',
        '      :delay 1s;',
        '      /import file-name="ketamon-relay-install.rsc";',
        '      /file remove [find name="ketamon-relay-install.rsc"];',
        '    } on-error={ :put "KetaMon relay auto-upgrade failed"; }',
        '    :do { /system scheduler remove [find name="ketamon-relay-auto-upgrade"]; } on-error={};',
        '    :do { /system script remove [find name="ketamon-relay-auto-upgrade"]; } on-error={};',
        '  };',
        '  /system scheduler add name="ketamon-relay-auto-upgrade" interval=5s on-event="/system script run ketamon-relay-auto-upgrade" disabled=no;',
        '} on-error={ :put "KetaMon relay auto-upgrade failed"; }',
    ])


def _fresh_relay_snapshot_count(snapshots, resource, fallback=0, max_age_seconds=600):
    try:
        fallback = int(fallback or 0)
    except Exception:
        fallback = 0
    if not isinstance(snapshots, dict):
        return fallback
    meta = snapshots.get(resource)
    if not isinstance(meta, dict):
        return fallback
    rows = meta.get("data")
    if not isinstance(rows, list):
        return fallback
    updated_at = str(meta.get("updated_at") or "")
    if updated_at and max_age_seconds:
        try:
            updated_dt = datetime.fromisoformat(updated_at.replace("Z", "+00:00"))
            if updated_dt.tzinfo is not None:
                updated_dt = updated_dt.replace(tzinfo=None)
            if (datetime.now() - updated_dt).total_seconds() > int(max_age_seconds):
                return fallback
        except Exception:
            pass
    return len(rows)


def _maybe_queue_relay_auto_upgrade(router, token, counts):
    router = dict(router or {})
    router_id = str(router.get("id") or "").strip()
    if not router_id:
        return False
    profile_count = int((counts or {}).get("/ip/hotspot/user/profile") or 0)
    user_count = int((counts or {}).get("/ip/hotspot/user") or 0)
    active_count = int((counts or {}).get("/ip/hotspot/active") or 0)
    try:
        snapshots = db_mod.db_get_router_relay_snapshot(router_id)
        profile_count = _fresh_relay_snapshot_count(snapshots, "/ip/hotspot/user/profile", profile_count)
        user_count = _fresh_relay_snapshot_count(snapshots, "/ip/hotspot/user", user_count)
        active_count = _fresh_relay_snapshot_count(snapshots, "/ip/hotspot/active", active_count)
    except Exception:
        pass
    # Vérifier si la version du script est obsolète (< safe-snapshot-v4)
    needs_version_upgrade = False
    try:
        relay_status_meta = snapshots.get("/ketamon/relay-status", {}) if isinstance(snapshots, dict) else {}
        relay_status_data = relay_status_meta.get("data", []) if isinstance(relay_status_meta, dict) else []
        current_source = str((relay_status_data[0] if relay_status_data else {}).get("source") or "")
        needs_version_upgrade = current_source not in ("safe-snapshot-v7",)
    except Exception:
        pass
    # Déclencher si : snapshot incomplet OU version obsolète
    incomplete_user_snapshot = active_count > 0 and user_count == 0
    incomplete_profile_snapshot = active_count > 0 and profile_count == 0
    if not (incomplete_user_snapshot or incomplete_profile_snapshot or needs_version_upgrade):
        return False
    now = time.time()
    last = float(_RELAY_AUTO_UPGRADE_LAST.get(router_id) or 0)
    if now - last < 1800:
        return False
    source = _relay_auto_upgrade_source(token)
    command = db_mod.db_enqueue_router_relay_command(
        router_id,
        router.get("owner_id", ""),
        "routeros-script",
        {"source": source},
    )
    if command:
        _RELAY_AUTO_UPGRADE_LAST[router_id] = now
    return bool(command)


_RELAY_BOOT_SCRIPT_LAST = {}


def _maybe_queue_relay_boot_script(router, token, resources):
    router = dict(router or {})
    router_id = str(router.get("id") or "").strip()
    if not router_id or not token:
        return False
    # Vérifier si ketamon-relay-boot existe dans le snapshot des schedulers
    try:
        scheduler_rows = (resources or {}).get("/system/scheduler") or []
        names = {str(r.get("name") or "").strip() for r in scheduler_rows if isinstance(r, dict)}
        if "ketamon-relay-boot" in names:
            return False
    except Exception:
        return False
    # Limiter à 1 tentative par heure par routeur
    now = time.time()
    if now - float(_RELAY_BOOT_SCRIPT_LAST.get(router_id) or 0) < 3600:
        return False
    base_url = _relay_public_base_url()
    install_url = f"{base_url}/api/relay/routeros/install.rsc?token={quote(str(token or ''))}"
    source = "\n".join([
        ":do { /system script remove [find name=\"ketamon-relay-boot\"]; } on-error={}",
        ":do { /system scheduler remove [find name=\"ketamon-relay-boot\"]; } on-error={}",
        f":do {{ /system script add name=\"ketamon-relay-boot\" policy=ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon source={{:local exists [/system scheduler find where name=\"ketamon-relay-poll\"]; :if ([:len $exists] = 0) do={{:do {{/tool fetch url=\"{install_url}\" dst-path=\"ketamon-relay-install.rsc\"; :delay 2s; /import file-name=\"ketamon-relay-install.rsc\"; /file remove [find name=\"ketamon-relay-install.rsc\"]; }} on-error={{}}; }} }}; }} on-error={{}}",
        ":do { /system scheduler add name=\"ketamon-relay-boot\" start-time=startup interval=0 on-event=\"/system script run ketamon-relay-boot\" disabled=no; } on-error={}",
    ])
    command = db_mod.db_enqueue_router_relay_command(
        router_id, router.get("owner_id", ""), "routeros-script", {"source": source},
    )
    if command:
        _RELAY_BOOT_SCRIPT_LAST[router_id] = now
    return bool(command)


def _profile_metadata_map_for_display(router_id, profiles):
    metadata_map = get_hotspot_profile_metadata_map(router_id)
    for profile in profiles or []:
        profile_row = dict(profile or {})
        name = str(profile_row.get("name") or "").strip()
        if not name:
            continue
        normalized = normalize_hotspot_profile(profile_row, metadata_map.get(name, {}))
        meta = dict(metadata_map.get(name, {}) or {})
        meta.setdefault("profile_name", name)
        if not _nonzero_time_limit(meta.get("time_limit")) and _nonzero_time_limit(normalized.get("time-limit")):
            meta["time_limit"] = normalized.get("time-limit")
        else:
            meta["time_limit"] = meta.get("time_limit") or normalized.get("time-limit") or "0"
        meta["price"] = meta.get("price") or normalized.get("price") or "0"
        meta["currency"] = meta.get("currency") or normalized.get("currency") or "FCFA"
        if str(meta.get("expire_mode") or "").strip().lower() in {"", "none"}:
            meta["expire_mode"] = normalized.get("expire-mode") or "none"
        if str(meta.get("lock_user") or "").strip().lower() in {"", "no", "false", "0"}:
            meta["lock_user"] = normalized.get("add-mac-cookie") or "no"
        metadata_map[name] = meta
    return metadata_map


def _relay_expired_cleanup_source(expired_rows):
    lines = [':put "KETAMON_EXPIRE_ENFORCE";']
    seen = set()
    for row in expired_rows or []:
        username = str(row.get("username") or row.get("name") or row.get("user") or "").strip()
        if not username or username in seen:
            continue
        seen.add(username)
        address = str(row.get("address") or "").strip()
        mac = str(row.get("mac-address") or row.get("mac") or "").strip()
        lines.extend([
            f':do {{ /ip hotspot active remove [find where user={_relay_routeros_quote(username)}]; }} on-error={{}}',
            f':do {{ /ip hotspot cookie remove [find where user={_relay_routeros_quote(username)}]; }} on-error={{}}',
            f':do {{ /ip hotspot user remove [find where name={_relay_routeros_quote(username)}]; }} on-error={{}}',
        ])
        if address:
            lines.append(
                f':do {{ /ip hotspot host remove [find where address={_relay_routeros_quote(address)}]; }} on-error={{}}'
            )
        if mac and mac != "00:00:00:00:00:00":
            lines.append(
                f':do {{ /ip hotspot host remove [find where mac-address={_relay_routeros_quote(mac)}]; }} on-error={{}}'
            )
    return "\n".join(lines) if len(lines) > 1 else ""


def _enforce_relay_snapshot_expirations(router):
    router = dict(router or {})
    router_id = str(router.get("id") or router.get("host") or "").strip()
    if not router_id:
        return {"expired": 0, "patched": 0, "cleaned": 0, "recorded": 0}

    users = _relay_snapshot_rows_from_db(router_id, "/ip/hotspot/user")
    active = _relay_snapshot_rows_from_db(router_id, "/ip/hotspot/active")
    fresh_active, _updated_at, _age = _relay_snapshot_state(router_id, "/ip/hotspot/active")
    active = active if fresh_active else []

    recorded = 0
    if active:
        try:
            recorded = _record_active_revenues_from_database(router_id, active)
        except Exception:
            recorded = 0

    first_used_map = _build_first_used_map(router_id)
    relay_api = RelaySnapshotApi(router)
    cleaned = 0
    patched = 0
    if active:
        try:
            cleaned = _cleanup_expired_active_from_database(relay_api, router_id, active, first_used_map)
        except Exception:
            cleaned = 0
        if not cleaned:
            try:
                users_map = {str(row.get("name") or "").strip(): dict(row) for row in users if str(row.get("name") or "").strip()}
                patched = _repair_active_ticket_epochs(
                    relay_api,
                    router_id,
                    active_rows=active,
                    users_map=users_map,
                    first_used_map=first_used_map,
                )
            except Exception:
                patched = 0
        else:
            patched = 0
        try:
            patched = int(patched or 0)
        except Exception:
            patched = 0

    now = datetime.now()
    active_by_user = {
        str(row.get("user") or "").strip(): row
        for row in active
        if str(row.get("user") or "").strip()
    }
    expired = []
    for user in users:
        username = str(user.get("name") or "").strip()
        if not username:
            continue
        expire_dt = _extract_ketamon_expire_datetime(user.get("comment"))
        if not expire_dt or now < expire_dt:
            continue
        merged = dict(user)
        merged["username"] = username
        active_row = active_by_user.get(username) or {}
        if active_row:
            merged.setdefault("address", active_row.get("address"))
            merged.setdefault("mac-address", active_row.get("mac-address"))
        expired.append(merged)

    if expired:
        source = _relay_expired_cleanup_source(expired[:200])
        if source:
            db_mod.db_enqueue_router_relay_command(
                router_id,
                router.get("owner_id", ""),
                "routeros-script",
                {"source": source},
            )
            try:
                db_mod.db_delete_ticket_pricing(router_id, [row.get("username") for row in expired])
            except Exception:
                pass

    # Fix 3 : vérifier TOUS les tickets via ticket_pricing+ventes, pas uniquement le snapshot 100-users
    snapshot_usernames = {str(u.get("name") or "").strip() for u in users if str(u.get("name") or "").strip()}
    db_extra_expired = []
    try:
        conn = db_mod.get_conn()
        all_tp = conn.execute(
            "SELECT tp.user, tp.profil, hp.time_limit"
            " FROM ticket_pricing tp"
            " LEFT JOIN hotspot_profile_metadata hp"
            "   ON hp.router_id=tp.router_id AND hp.profile_name=tp.profil"
            " WHERE tp.router_id=?",
            (router_id,)
        ).fetchall()
        for tp in all_tp:
            username = str(tp[0] or "").strip()
            if not username or username in snapshot_usernames:
                continue
            first_use_str = first_used_map.get(username)
            if not first_use_str:
                continue  # jamais utilisé → ne pas toucher
            profil = str(tp[1] or "").strip()
            tl_raw = str(tp[2] or "").strip() or _infer_time_limit_from_profile_name(profil)
            if not tl_raw or tl_raw.lower() in {"0", "0s", "none"}:
                continue
            limit_seconds = parse_routeros_duration(
                coerce_ticket_time_limit_router(tl_raw, empty="0", prefer_legacy_routeros=False) or "0"
            )
            if not limit_seconds or limit_seconds <= 0:
                continue
            first_dt = _effective_first_used_datetime(first_use_str, None, now=now)
            if not first_dt:
                continue
            if now < first_dt + timedelta(seconds=limit_seconds):
                continue
            merged = {"username": username, "name": username}
            active_row = active_by_user.get(username) or {}
            if active_row:
                merged["address"] = active_row.get("address")
                merged["mac-address"] = active_row.get("mac-address")
            db_extra_expired.append(merged)
    except Exception:
        pass
    if db_extra_expired:
        for i in range(0, len(db_extra_expired), 200):
            batch = db_extra_expired[i:i + 200]
            source = _relay_expired_cleanup_source(batch)
            if source:
                db_mod.db_enqueue_router_relay_command(
                    router_id,
                    router.get("owner_id", ""),
                    "routeros-script",
                    {"source": source},
                )
        try:
            db_mod.db_delete_ticket_pricing(router_id, [row["username"] for row in db_extra_expired])
        except Exception:
            pass

    return {"expired": len(expired) + len(db_extra_expired), "patched": patched, "cleaned": cleaned, "recorded": recorded}


def _record_active_revenues_from_database(router_id, active_rows):
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0
    conn = db_mod.get_conn()
    now = datetime.now()
    inserted = 0
    for active in active_rows or []:
        username = str((active or {}).get("user") or "").strip()
        if not username:
            continue
        existing_vente = conn.execute(
            "SELECT id, prix FROM ventes WHERE router_id=? AND user=? LIMIT 1",
            (router_id, username),
        ).fetchone()
        pricing = conn.execute(
            "SELECT prix, devise, profil, reseau FROM ticket_pricing WHERE router_id=? AND user=? LIMIT 1",
            (router_id, username),
        ).fetchone()
        if not pricing:
            continue
        price = float(pricing["prix"] or 0)
        profil = str(pricing["profil"] or "").strip()
        # Si prix=0, chercher le vrai prix depuis hotspot_profile_metadata (source de verite)
        if price <= 0 and profil:
            try:
                meta_row = conn.execute(
                    "SELECT price, currency FROM hotspot_profile_metadata"
                    " WHERE router_id=? AND profile_name=? LIMIT 1",
                    (router_id, profil),
                ).fetchone()
                if meta_row:
                    meta_price = float(str(meta_row[0] or "0") or 0)
                    if meta_price > 0:
                        price = meta_price
                        conn.execute(
                            "UPDATE ticket_pricing SET prix=?, devise=? WHERE router_id=? AND user=?",
                            (price, str(meta_row[1] or "FCFA"), router_id, username),
                        )
            except Exception:
                pass
        if price <= 0:
            continue  # ticket genuinement gratuit ou profil sans prix configure
        if existing_vente:
            # Vente deja enregistree : corriger le prix si elle etait a 0
            if float(existing_vente[1] or 0) <= 0:
                try:
                    conn.execute(
                        "UPDATE ventes SET prix=?, devise=? WHERE id=?",
                        (price, pricing["devise"] or "FCFA", existing_vente[0]),
                    )
                    conn.commit()
                except Exception:
                    pass
            continue  # Toujours une seule vente par ticket
        # Utilise le debut de session comme date de premiere utilisation (plus precis que now)
        session_start = _active_started_datetime(active, now=now) or now
        try:
            db_mod.db_insert_vente({
                "id": uuid.uuid4().hex,
                "router_id": router_id,
                "date": session_start.strftime("%Y-%m-%d"),
                "heure": session_start.strftime("%H:%M:%S"),
                "user": username,
                "profil": pricing["profil"] or "",
                "prix": price,
                "devise": pricing["devise"] or "FCFA",
                "reseau": pricing["reseau"] or "",
                "data_limit": "0",
                "ticket_key": f"{username}:{int(session_start.timestamp())}",
            })
            inserted += 1
        except Exception:
            pass
    return inserted


def _parse_first_used_datetime(first_used_raw):
    text = str(first_used_raw or "").strip()
    if not text:
        return None
    try:
        return datetime.strptime(text[:16], "%Y-%m-%d %H:%M")
    except Exception:
        return None


def _active_started_datetime(active_row, now=None):
    active_row = dict(active_row or {})
    now = now if isinstance(now, datetime) else datetime.now()
    uptime_seconds = parse_routeros_duration(active_row.get("uptime"))
    if uptime_seconds is None or uptime_seconds < 0:
        return None
    return now - timedelta(seconds=uptime_seconds)


def _effective_first_used_datetime(first_used_raw, active_row=None, now=None):
    first_dt = _parse_first_used_datetime(first_used_raw)
    active_dt = _active_started_datetime(active_row, now=now)
    candidates = [dt for dt in (first_dt, active_dt) if isinstance(dt, datetime)]
    return min(candidates) if candidates else None


def _compose_active_ticket_comment(comment, expire_epoch):
    base_comment, _expire_raw = _split_ticket_runtime_comment(comment)
    if base_comment:
        return f"{base_comment}{KETAMON_TICKET_COMMENT_MARKER}{int(expire_epoch)}"
    return f"{KETAMON_TICKET_COMMENT_MARKER.strip()}{int(expire_epoch)}"


def _datetime_to_ketamon_epoch(dt):
    if not isinstance(dt, datetime):
        return 0
    return int((dt - datetime(1970, 1, 1)).total_seconds())


def _repair_active_ticket_epochs(api, router_id, active_rows=None, users_map=None, first_used_map=None):
    """
    Répare l'expiration absolue des tickets déjà utilisés.
    Ne touche jamais aux tickets non utilisés.
    """
    active_rows = list(active_rows or [])
    if not router_id:
        return 0

    if users_map is None:
        try:
            users_map = {
                str(user.get("name") or "").strip(): dict(user)
                for user in api.get_resource("/ip/hotspot/user").get()
            }
        except Exception:
            users_map = {}

    if first_used_map is None:
        first_used_map = _build_first_used_map(router_id)

    if not users_map:
        return 0

    active_by_username = {}
    for active_row in active_rows:
        active_username = str(active_row.get("user") or "").strip()
        if active_username:
            active_by_username[active_username] = active_row

    user_resource = api.get_resource("/ip/hotspot/user")
    server_now = datetime.now()
    patched = 0

    for username, user_row in users_map.items():
        username = str(username or "").strip()
        if not username:
            continue

        active_row = active_by_username.get(username)

        current_comment = str(user_row.get("comment") or "").strip()
        current_expire_dt = _extract_ketamon_expire_datetime(current_comment)

        if not (_is_ketamon_ticket_comment(current_comment) or current_expire_dt or username in first_used_map or active_row):
            continue

        limit_seconds = parse_routeros_duration(user_row.get("limit-uptime"))
        if limit_seconds is None or limit_seconds <= 0:
            meta = _ticket_db_meta(router_id, username)
            try:
                limit_seconds = parse_routeros_duration(
                    coerce_ticket_time_limit_router(_ticket_meta_time_limit(meta), empty="0", prefer_legacy_routeros=False) or "0"
                )
            except Exception:
                limit_seconds = None
        if limit_seconds is None or limit_seconds <= 0:
            continue

        # Expiration absolue déjà définie et dans le futur → VERROUILLÉE, ne jamais recalculer
        if current_expire_dt and current_expire_dt > server_now:
            continue

        first_used_dt = _effective_first_used_datetime(first_used_map.get(username), active_row, now=server_now)
        if first_used_dt:
            expire_dt = first_used_dt + timedelta(seconds=limit_seconds)
            actual_first_used = first_used_dt
        else:
            if not active_row:
                continue
            # Utilise le debut de session comme proxy de premiere utilisation
            session_start = _active_started_datetime(active_row, now=server_now)
            if not session_start:
                continue
            expire_dt = session_start + timedelta(seconds=limit_seconds)
            actual_first_used = session_start

        if current_expire_dt:
            drift = abs(int((current_expire_dt - expire_dt).total_seconds()))
            if drift <= 120:
                continue

        expire_epoch = _datetime_to_ketamon_epoch(expire_dt)
        if expire_epoch <= 0:
            continue
        user_id = router_item_id(user_row)

        new_comment = _compose_active_ticket_comment(current_comment, expire_epoch)
        try:
            user_id_text = str(user_id or "").strip()
            if hasattr(api, "queue_routeros_script") and (not user_id_text or user_id_text.startswith("*db-")):
                source = "\n".join([
                    f":local uid [/ip hotspot user find where name={_relay_routeros_quote(username)}];",
                    ":if ([:len $uid] > 0) do={",
                    f"    /ip hotspot user set $uid comment={_relay_routeros_quote(new_comment)} limit-uptime=0;",
                    "}",
                ])
                api.queue_routeros_script(source)
            else:
                if not user_id_text:
                    continue
                user_resource.set(id=user_id_text, comment=new_comment, **{"limit-uptime": "0"})
            user_row["comment"] = new_comment
            user_row["limit-uptime"] = "0"
            if active_row is not None:
                active_row["user_comment"] = new_comment
            patched += 1
            # Sauvegarder en DB lors du PREMIER écriture de l'epoch (expiration absolue persistante)
            if not current_expire_dt:
                try:
                    db_mod.db_set_ticket_expiry(
                        router_id, username,
                        first_used_at=actual_first_used.strftime("%Y-%m-%d %H:%M:%S"),
                        expire_at=expire_dt.strftime("%Y-%m-%d %H:%M:%S"),
                    )
                except Exception:
                    pass
        except Exception:
            continue

    return patched


def _close_api_quietly(api):
    try:
        if api:
            api.close()
    except Exception:
        pass


def _sync_ventes_for_router(router_info, timeout=8):
    """Sync tickets actifs (bytes-in>0) pour un routeur → SQLite.
    Un ticket est compté comme revenu uniquement quand il est utilisé.
    La date de vente = date de la sync (jour où le client s'est connecté).
    Chaque ticket identifié par ticket_key = username:expiry_timestamp."""
    host      = router_info.get("host", "")
    router_id = router_info.get("id") or host
    api, err = mk.safe_connect_router(router_info, timeout=timeout)
    if err or not api:
        return 0

    conn = None
    try:
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        conn = db_mod.get_conn()

        # Charge les ticket_keys ET les usernames déjà enregistrés
        existing_rows = conn.execute(
            "SELECT user, ticket_key FROM ventes WHERE router_id=?", (router_id,)
        ).fetchall()
        existing_keys  = set(r[1] for r in existing_rows)
        existing_users = set(r[0] for r in existing_rows)

        # Date/heure de la sync = date réelle d'utilisation du ticket
        now_dt   = datetime.now()
        date_str = now_dt.strftime("%Y-%m-%d")
        time_str = now_dt.strftime("%H:%M:%S")

        all_users = api.get_resource("/ip/hotspot/user").get()
        new_count = 0

        # Sessions actives : bytes-in en temps réel (user account bytes-in = 0 pendant session active)
        try:
            active_sessions = api.get_resource("/ip/hotspot/active").get()
            users_map = {
                str(user.get("name") or "").strip(): dict(user)
                for user in all_users
                if str(user.get("name") or "").strip()
            }
            _repair_active_ticket_epochs(
                api,
                router_id,
                active_rows=active_sessions,
                users_map=users_map,
                first_used_map=_build_first_used_map(router_id),
            )
            active_with_traffic = set()
            for sess in active_sessions:
                try:
                    b = int(sess.get("bytes-in", 0) or 0)
                except (ValueError, TypeError):
                    b = 0
                if b > 0:
                    active_with_traffic.add(str(sess.get("user", "") or "").strip())
        except Exception:
            active_with_traffic = set()

        import uuid as _uuid
        for u in all_users:
            username = str(u.get("name", "") or "").strip()
            if not username:
                continue

            comment = str(u.get("comment", "") or "")

            try:
                bytes_in = int(u.get("bytes-in", 0) or 0)
            except (ValueError, TypeError):
                bytes_in = 0

            # Ticket "utilisé" : bytes-in>0, session active, OU marqueur ##KETAMON## (preuve d'utilisation)
            has_ketamon = any(m in comment for m in KETAMON_TICKET_COMMENT_MARKERS)
            if bytes_in == 0 and username not in active_with_traffic and not has_ketamon:
                continue

            ticket_key = _extract_ticket_key(username, comment)

            if ticket_key in existing_keys:
                continue

            if username in existing_users:
                if ticket_key != username:
                    conn.execute(
                        "UPDATE ventes SET ticket_key=? WHERE router_id=? AND user=? AND ticket_key=?",
                        (ticket_key, router_id, username, username)
                    )
                    conn.commit()
                    existing_keys.add(ticket_key)
                    existing_keys.discard(username)
                if username in active_with_traffic:
                    row = conn.execute(
                        "SELECT date FROM ventes WHERE router_id=? AND user=? LIMIT 1",
                        (router_id, username)
                    ).fetchone()
                    if row and str(row[0] or "") != date_str:
                        conn.execute(
                            "UPDATE ventes SET date=?, heure=? WHERE router_id=? AND user=?",
                            (date_str, time_str, router_id, username)
                        )
                        conn.commit()
                continue

            profile = str(u.get("profile", "default") or "default")

            pricing = conn.execute(
                "SELECT prix, devise, profil, reseau FROM ticket_pricing WHERE router_id=? AND user=?",
                (router_id, username)
            ).fetchone()
            if pricing:
                price    = float(pricing[0] or 0)
                currency = pricing[1] or "FCFA"
                profile  = pricing[2] or profile
                reseau   = pricing[3] or ""
            elif profile in profiles_meta:
                meta     = profiles_meta[profile]
                price    = float(meta.get("price", "0") or "0")
                currency = meta.get("currency", "FCFA") or "FCFA"
                reseau   = str(u.get("server") or "")
                if price > 0:
                    try:
                        db_mod.db_batch_upsert_ticket_pricing([{
                            "router_id": router_id, "user": username,
                            "password": username, "prix": price,
                            "devise": currency, "profil": profile, "reseau": reseau,
                        }])
                    except Exception:
                        pass
            else:
                # Profil non configuré → chercher le prix depuis d'autres tickets du même profil
                price    = 0.0
                currency = "FCFA"
                reseau   = str(u.get("server") or "")

            # Si toujours prix=0, inférer depuis ticket_pricing ou ventes existantes (même profil)
            if price <= 0:
                row = conn.execute(
                    "SELECT prix, devise FROM ticket_pricing WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
                    (router_id, profile)
                ).fetchone()
                if not row:
                    row = conn.execute(
                        "SELECT prix, devise FROM ventes WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
                        (router_id, profile)
                    ).fetchone()
                if row:
                    price    = float(row[0] or 0)
                    currency = str(row[1] or "FCFA")

            db_mod.db_insert_vente({
                "id":         _uuid.uuid4().hex,
                "router_id":  router_id,
                "date":       date_str,
                "heure":      time_str,
                "user":       username,
                "profil":     profile,
                "prix":       price,
                "devise":     currency,
                "reseau":     reseau,
                "data_limit": "0",
                "ticket_key": ticket_key,
            })
            existing_keys.add(ticket_key)
            existing_users.add(username)
            new_count += 1

        return new_count
    except Exception as _e:
        _logger.exception("[SYNC] ERREUR router %s", router_info.get("host", "?"))
        return 0
    finally:
        _close_api_quietly(api)


# Suivi temps réel du statut de sync par routeur
_sync_stats = {}  # {router_id: {"last_sync": "ISO", "new": N, "ok": bool, "error": str, "host": str}}


def _write_missing_epochs_for_router(api, router_id, host="?"):
    # Desactive ici: le secours Python actif vit dans ketamon_agent.py.
    # app.py garde seulement la sync revenus et l'installation des scripts.
    return 0


def _expire_tickets_for_router(api, host="?"):
    # Desactive ici: le secours Python actif vit dans ketamon_agent.py.
    # Il coupe uniquement les tickets deja marques exp=... si MikroTik echoue.
    return 0


def _backfill_ventes_prix_zero(router_id, conn):
    """Corrige les ventes enregistrées avec prix=0 en cherchant le prix depuis ticket_pricing ou d'autres ventes du même profil."""
    rows = conn.execute(
        "SELECT id, profil FROM ventes WHERE router_id=? AND (prix IS NULL OR prix<=0)",
        (router_id,)
    ).fetchall()
    fixed = 0
    for row in rows:
        vid, profil = row[0], str(row[1] or "")
        if not profil:
            continue
        ref = conn.execute(
            "SELECT prix, devise FROM ticket_pricing WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
            (router_id, profil)
        ).fetchone()
        if not ref:
            ref = conn.execute(
                "SELECT prix, devise FROM ventes WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
                (router_id, profil)
            ).fetchone()
        if not ref:
            meta_row = conn.execute(
                "SELECT price, currency FROM hotspot_profile_metadata WHERE router_id=? AND profile_name=? AND CAST(price AS REAL)>0 LIMIT 1",
                (router_id, profil)
            ).fetchone()
            if meta_row and float(meta_row[0] or 0) > 0:
                ref = (float(meta_row[0]), str(meta_row[1] or "FCFA"))
        if ref and float(ref[0] or 0) > 0:
            conn.execute(
                "UPDATE ventes SET prix=?, devise=? WHERE id=?",
                (float(ref[0]), str(ref[1] or "FCFA"), vid)
            )
            fixed += 1
    if fixed:
        conn.commit()
    return fixed


def _sync_ventes_from_relay(router):
    """Sync revenus depuis le snapshot relais (pas de connexion directe MikroTik)."""
    router_id = str(router.get("id") or router.get("host") or "").strip()
    if not router_id:
        return 0
    if not _router_has_relay_snapshots(router):
        return 0

    import uuid as _uuid
    conn = db_mod.get_conn()
    _backfill_ventes_prix_zero(router_id, conn)
    # SELECT ticket_key en premier pour que r[0]=ticket_key, r[1]=user
    existing_rows = conn.execute(
        "SELECT ticket_key, user FROM ventes WHERE router_id=?", (router_id,)
    ).fetchall()
    existing_keys  = {str(r[0] or "").strip() for r in existing_rows}  # ticket_key
    existing_users = {str(r[1] or "").strip() for r in existing_rows}  # user

    # Utilisateurs actifs depuis snapshot relais (bytes-in en cours de session)
    active_snap = db_mod.db_get_router_relay_snapshot(router_id, "/ip/hotspot/active") or []
    active_with_traffic = set()
    for sess in active_snap:
        try:
            b = int(sess.get("bytes-in", 0) or 0)
        except (ValueError, TypeError):
            b = 0
        if b > 0:
            active_with_traffic.add(str(sess.get("user") or "").strip())

    user_snap = db_mod.db_get_router_relay_snapshot(router_id, "/ip/hotspot/user") or []
    profiles_meta = get_hotspot_profile_metadata_map(router_id)
    now_dt   = datetime.now()
    date_str = now_dt.strftime("%Y-%m-%d")
    time_str = now_dt.strftime("%H:%M:%S")
    new_count = 0

    for u in user_snap:
        username = str(u.get("name") or "").strip()
        if not username:
            continue
        comment  = str(u.get("comment") or "")
        try:
            bytes_in = int(u.get("bytes-in", 0) or 0)
        except (ValueError, TypeError):
            bytes_in = 0

        # Ticket "utilisé" : bytes-in>0, session active, OU marqueur ##KETAMON## (preuve d'utilisation)
        has_ketamon = any(m in comment for m in KETAMON_TICKET_COMMENT_MARKERS)
        if bytes_in == 0 and username not in active_with_traffic and not has_ketamon:
            continue

        ticket_key = _extract_ticket_key(username, comment)

        if ticket_key in existing_keys:
            continue
        if username in existing_users:
            if ticket_key != username:
                conn.execute(
                    "UPDATE ventes SET ticket_key=? WHERE router_id=? AND user=? AND ticket_key=?",
                    (ticket_key, router_id, username, username)
                )
                conn.commit()
            if username in active_with_traffic:
                row = conn.execute(
                    "SELECT date FROM ventes WHERE router_id=? AND user=? LIMIT 1",
                    (router_id, username)
                ).fetchone()
                if row and str(row[0] or "") != date_str:
                    conn.execute(
                        "UPDATE ventes SET date=?, heure=? WHERE router_id=? AND user=?",
                        (date_str, time_str, router_id, username)
                    )
                    conn.commit()
            continue

        profile = str(u.get("profile") or "default").strip() or "default"
        pricing = conn.execute(
            "SELECT prix, devise, profil, reseau FROM ticket_pricing WHERE router_id=? AND user=?",
            (router_id, username)
        ).fetchone()
        if pricing:
            price    = float(pricing[0] or 0)
            currency = pricing[1] or "FCFA"
            profile  = pricing[2] or profile
            reseau   = pricing[3] or ""
        elif profile in profiles_meta:
            meta     = profiles_meta[profile]
            price    = float(meta.get("price", "0") or "0")
            currency = meta.get("currency", "FCFA") or "FCFA"
            reseau   = str(u.get("server") or "")
            if price > 0:
                try:
                    db_mod.db_batch_upsert_ticket_pricing([{
                        "router_id": router_id, "user": username,
                        "password": username, "prix": price,
                        "devise": currency, "profil": profile, "reseau": reseau,
                    }])
                except Exception:
                    pass
        else:
            # Profil non configuré → chercher le prix depuis d'autres tickets du même profil
            price    = 0.0
            currency = "FCFA"
            reseau   = str(u.get("server") or "")

        # Si toujours prix=0, inférer depuis ticket_pricing ou ventes existantes (même profil)
        if price <= 0:
            row = conn.execute(
                "SELECT prix, devise FROM ticket_pricing WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
                (router_id, profile)
            ).fetchone()
            if not row:
                row = conn.execute(
                    "SELECT prix, devise FROM ventes WHERE router_id=? AND profil=? AND prix>0 LIMIT 1",
                    (router_id, profile)
                ).fetchone()
            if row:
                price    = float(row[0] or 0)
                currency = str(row[1] or "FCFA")

        db_mod.db_insert_vente({
            "id":         _uuid.uuid4().hex,
            "router_id":  router_id,
            "user":       username,
            "profil":     profile,
            "prix":       price,
            "devise":     currency,
            "reseau":     reseau,
            "data_limit": "",
            "date":       date_str,
            "heure":      time_str,
            "ticket_key": ticket_key,
        })
        existing_keys.add(ticket_key)
        existing_users.add(username)
        new_count += 1

    return new_count


def _bg_ventes_loop():
    """Thread daemon : sync revenus. Intervalle allonge pour les gros routeurs."""
    time.sleep(120)
    while True:
        try:
            for router in db_mod.db_get_routers():
                rid  = router.get("id") or router.get("host", "")
                host = router.get("host", "?")
                try:
                    if int(router.get("relay_enabled") or 0):
                        n = _sync_ventes_from_relay(router)
                    else:
                        n = _sync_ventes_for_router(router, timeout=6)
                    _sync_stats[rid] = {
                        "last_sync": datetime.now().isoformat(timespec="seconds"),
                        "new":       n,
                        "ok":        True,
                        "error":     "",
                        "host":      host,
                        "name":      router.get("name", ""),
                    }
                    if n:
                        _logger.info("[SYNC] %s : %d nouvelle(s) vente(s)", host, n)
                    # Partage des stats avec l'agent moniteur
                    agent_mod.set_sync_stats({rid: {
                        "last_ok":    datetime.now().isoformat(timespec="seconds"),
                        "last_error": "",
                        "host":       host,
                        "name":       router.get("name",""),
                    }})
                except Exception as _e:
                    _sync_stats[rid] = {
                        "last_sync": datetime.now().isoformat(timespec="seconds"),
                        "new":       0,
                        "ok":        False,
                        "error":     str(_e),
                        "host":      host,
                        "name":      router.get("name", ""),
                    }
                    agent_mod.set_sync_stats({rid: {
                        "last_ok":    "",
                        "last_error": str(_e),
                        "host":       host,
                        "name":       router.get("name",""),
                    }})
        except Exception as _e:
            _logger.error("[SYNC] boucle erreur: %s", _e)
        finally:
            db_mod.release_thread_conn()
        time.sleep(max(60, BG_REVENUE_SYNC_INTERVAL))


def _bg_runtime_support_loop():
    """Thread daemon : aligne durablement les scripts ticket sur tous les routeurs/profils."""
    time.sleep(12)
    while True:
        try:
            for router in db_mod.db_get_routers():
                if int(router.get("relay_enabled") or 0):
                    try:
                        _relay_queue_expiry_install(router)
                    except Exception as _e:
                        _logger.warning("[RUNTIME] relay %s: %s", router.get("host", "?"), _e)
                    continue
                api = None
                try:
                    api, err = mk.safe_connect_router(router, timeout=8)
                    if err or not api:
                        continue
                    ensure_ticket_runtime_support(api)
                except Exception as _e:
                    _logger.warning("[RUNTIME] erreur %s: %s", router.get("host", "?"), _e)
                finally:
                    _close_api_quietly(api)
        except Exception as _e:
            _logger.error("[RUNTIME] boucle erreur: %s", _e)
        finally:
            db_mod.release_thread_conn()
        time.sleep(900)


def _bg_keepalive_loop():
    """Empeche Render (free tier) de s'endormir : ping /health toutes les 4 min."""
    time.sleep(90)
    import urllib.request as _ur
    while True:
        try:
            url = (os.environ.get("KETAMON_PUBLIC_URL") or "").rstrip("/")
            if url:
                _ur.urlopen(f"{url}/health", timeout=8)
        except Exception:
            pass
        time.sleep(240)


threading.Thread(target=_bg_ventes_loop, daemon=True).start()
threading.Thread(target=_bg_runtime_support_loop, daemon=True).start()


if KETAMON_ENV in {"prod", "production"}:
    threading.Thread(target=_bg_keepalive_loop, daemon=True).start()
agent_mod.start()


def get_profile_time_limit(router_id, profile_name):
    metadata = db_mod.db_get_hotspot_profile_metadata(router_id, profile_name) or {}
    stored_time = normalize_profile_time_limit(metadata.get("time_limit"))
    if stored_time and stored_time.lower() not in {"0", "0s", "none"}:
        return stored_time
    return _infer_time_limit_from_profile_name(profile_name) or stored_time


def resolve_ticket_time_limit(router_id, profile_name, requested_time_limit):
    normalized_requested = coerce_ticket_time_limit_router(requested_time_limit, empty="", prefer_legacy_routeros=False)
    if normalized_requested != "":
        return normalized_requested
    profile_time_limit = get_profile_time_limit(router_id, profile_name)
    return coerce_ticket_time_limit_router(profile_time_limit, empty="0", prefer_legacy_routeros=False) or "0"


def resolve_ticket_time_limit_display(router_id, profile_name, requested_time_limit):
    normalized_requested = coerce_ticket_time_limit_user(requested_time_limit, empty="", prefer_legacy_routeros=False)
    if normalized_requested != "":
        return normalized_requested
    profile_time_limit = get_profile_time_limit(router_id, profile_name)
    return profile_time_limit or "0"


def strip_ticket_runtime_comment(comment):
    base_comment, _expire_raw = _split_ticket_runtime_comment(comment)
    return base_comment


def build_hotspot_user_comment(user_comment, mode="vc-"):
    base_comment = strip_ticket_runtime_comment(user_comment)
    return f"{mode}{base_comment}" if base_comment else mode


def sanitize_router_script_name(prefix, value, max_length=63):
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", str(value or "").strip()).strip("-") or "default"
    return f"{prefix}-{slug}"[:max_length]


def build_ticket_login_wrapper_script(existing_script_name):
    safe_name = str(existing_script_name or "").replace("\\", "\\\\").replace('"', '\\"')
    return "\n".join([
        f':local legacy [/system script find where name="{safe_name}"];',
        ':if ([:len $legacy] > 0) do={ /system script run $legacy; }',
        f':local ketamon [/system script find where name="{KETAMON_TICKET_LOGIN_SCRIPT}"];',
        ':if ([:len $ketamon] > 0) do={ /system script run $ketamon; }',
    ])


def _build_routeros_local_epoch_lines(indent=""):
    prefix = str(indent or "")
    lines = [
        ':local cdate [/system clock get date];',
        ':local ctime [/system clock get time];',
        ':local year 0;',
        ':local month 0;',
        ':local day 0;',
        ':if ([:find $cdate "-"] != nil) do={',
        '    :set year  [:tonum [:pick $cdate 0 4]];',
        '    :set month [:tonum [:pick $cdate 5 7]];',
        '    :set day   [:tonum [:pick $cdate 8 10]];',
        '} else={',
        '    :local monTxt [:pick $cdate 0 3];',
        '    :set day  [:tonum [:pick $cdate 4 6]];',
        '    :set year [:tonum [:pick $cdate 7 11]];',
        '    :if ($monTxt = "jan") do={ :set month 1; }',
        '    :if ($monTxt = "feb") do={ :set month 2; }',
        '    :if ($monTxt = "mar") do={ :set month 3; }',
        '    :if ($monTxt = "apr") do={ :set month 4; }',
        '    :if ($monTxt = "may") do={ :set month 5; }',
        '    :if ($monTxt = "jun") do={ :set month 6; }',
        '    :if ($monTxt = "jul") do={ :set month 7; }',
        '    :if ($monTxt = "aug") do={ :set month 8; }',
        '    :if ($monTxt = "sep") do={ :set month 9; }',
        '    :if ($monTxt = "oct") do={ :set month 10; }',
        '    :if ($monTxt = "nov") do={ :set month 11; }',
        '    :if ($monTxt = "dec") do={ :set month 12; }',
        '}',
        ':if (($year < 2020) || ($month < 1) || ($day < 1)) do={ :return; }',
        ':local hh [:tonum [:pick $ctime 0 2]];',
        ':local mm [:tonum [:pick $ctime 3 5]];',
        ':local ss [:tonum [:pick $ctime 6 8]];',
        ':local moff 0;',
        ':if ($month > 1)  do={ :set moff ($moff + 31); }',
        ':if ($month > 2)  do={ :set moff ($moff + 28); }',
        ':if ($month > 3)  do={ :set moff ($moff + 31); }',
        ':if ($month > 4)  do={ :set moff ($moff + 30); }',
        ':if ($month > 5)  do={ :set moff ($moff + 31); }',
        ':if ($month > 6)  do={ :set moff ($moff + 30); }',
        ':if ($month > 7)  do={ :set moff ($moff + 31); }',
        ':if ($month > 8)  do={ :set moff ($moff + 31); }',
        ':if ($month > 9)  do={ :set moff ($moff + 30); }',
        ':if ($month > 10) do={ :set moff ($moff + 31); }',
        ':if ($month > 11) do={ :set moff ($moff + 30); }',
        ':local y ($year - 1970);',
        ':local leaps (($y + 1) / 4 - ($y + 69) / 100 + ($y + 369) / 400);',
        ':local dse (($y * 365) + $leaps + $moff + ($day - 1));',
        ':if ($month > 2) do={',
        '    :if ($year % 4   = 0) do={ :set dse ($dse + 1); }',
        '    :if ($year % 100 = 0) do={ :set dse ($dse - 1); }',
        '    :if ($year % 400 = 0) do={ :set dse ($dse + 1); }',
        '}',
        ':local nowEpoch (($dse * 86400) + ($hh * 3600) + ($mm * 60) + $ss);',
    ]
    return [prefix + line for line in lines]


def build_ketamon_ticket_login_script_source():
    # Expiration absolue horloge murale (wall-clock) :
    # - 1ère connexion  : epoch stocké = now + limit-uptime ; limit-uptime effacé
    # - Reconnexion valide : limit-uptime = (expireEpoch - now), uptime reset → MikroTik coupe exactement à l'expiry
    # - Reconnexion expirée : session/cookie/user supprimés immédiatement → internet coupé
    # - 1 ticket = 1 appareil : MAC verrouillée à la 1ère connexion
    _epoch_lines = _build_routeros_local_epoch_lines(indent="")
    return "\n".join([
        ':local uname $user;',
        ':local loginMac $"mac-address";',
        ':if ([:len $uname] = 0) do={ :return; }',
        ':local userId [/ip hotspot user find where name=$uname];',
        ':if ([:len $userId] = 0) do={ :return; }',
        # Calcul epoch (NTP) — si horloge non synchro (année < 2020) le :return est dans _epoch_lines
        *_epoch_lines,
        # Lecture commentaire et détection du marqueur d'expiry
        ':local currentComment [:tostr [/ip hotspot user get $userId comment]];',
        f':local marker "{KETAMON_TICKET_COMMENT_MARKER}";',
        f':local markerAlt "{KETAMON_TICKET_COMMENT_MARKER.strip()}";',
        ':local markerLen [:len $marker];',
        ':local markerPos [:find $currentComment $marker];',
        ':if ($markerPos = nil) do={',
        '    :set markerPos [:find $currentComment $markerAlt];',
        '    :if ($markerPos != nil) do={ :set markerLen [:len $markerAlt]; }',
        '}',
        # --- Ticket déjà utilisé (marqueur présent) ---
        ':if ($markerPos != nil) do={',
        '    :local startPos ($markerPos + $markerLen);',
        '    :local expireRaw [:pick $currentComment $startPos [:len $currentComment]];',
        '    :local expireEpoch [:tonum $expireRaw];',
        '    :if ($expireEpoch >= 1000000000) do={',
        '        :if ($nowEpoch >= $expireEpoch) do={',
        '            :foreach activeId in=[/ip hotspot active find where user=$uname] do={',
        '                /ip hotspot active remove $activeId;',
        '            }',
        '            :foreach cookieId in=[/ip hotspot cookie find where user=$uname] do={',
        '                /ip hotspot cookie remove $cookieId;',
        '            }',
        '            /ip hotspot user remove $userId;',
        '            :return;',
        '        }',
        # Reconnexion valide : limit-uptime = uptime_actuel + remaining
        # uptime est read-only (accumulé) → il faut ajouter remaining pour que MikroTik coupe au bon moment
        '        :local remainSec ($expireEpoch - $nowEpoch);',
        '        :if ($remainSec > 0) do={',
        '            :local utimeSec 0;',
        '            :do {',
        '                :local utimeStr [:tostr [/ip hotspot user get $userId uptime]];',
        '                :local uwVal $utimeStr;',
        '                :local uwPos [:find $uwVal "w"];',
        '                :if ($uwPos != nil) do={',
        '                    :set utimeSec ($utimeSec + ([:tonum [:pick $uwVal 0 $uwPos]] * 604800));',
        '                    :set uwVal [:pick $uwVal ($uwPos + 1) [:len $uwVal]];',
        '                }',
        '                :local udPos [:find $uwVal "d"];',
        '                :if ($udPos != nil) do={',
        '                    :set utimeSec ($utimeSec + ([:tonum [:pick $uwVal 0 $udPos]] * 86400));',
        '                    :set uwVal [:pick $uwVal ($udPos + 1) [:len $uwVal]];',
        '                }',
        '                :local ucPos [:find $uwVal ":"];',
        '                :if ($ucPos != nil) do={',
        '                    :set utimeSec ($utimeSec + ([:tonum [:pick $uwVal 0 2]] * 3600) + ([:tonum [:pick $uwVal 3 5]] * 60) + [:tonum [:pick $uwVal 6 8]]);',
        '                } else={',
        '                    :local uhPos [:find $uwVal "h"];',
        '                    :if ($uhPos != nil) do={',
        '                        :set utimeSec ($utimeSec + ([:tonum [:pick $uwVal 0 $uhPos]] * 3600));',
        '                        :set uwVal [:pick $uwVal ($uhPos + 1) [:len $uwVal]];',
        '                    }',
        '                    :local umPos [:find $uwVal "m"];',
        '                    :if ($umPos != nil) do={',
        '                        :set utimeSec ($utimeSec + ([:tonum [:pick $uwVal 0 $umPos]] * 60));',
        '                        :set uwVal [:pick $uwVal ($umPos + 1) [:len $uwVal]];',
        '                    }',
        '                    :local usPos [:find $uwVal "s"];',
        '                    :if ($usPos != nil) do={ :set utimeSec ($utimeSec + [:tonum [:pick $uwVal 0 $usPos]]); }',
        '                }',
        '            } on-error={};',
        '            :local newLimit ($utimeSec + $remainSec);',
        '            :do { /ip hotspot user set $userId limit-uptime=([:tostr $newLimit] . "s"); } on-error={};',
        '        }',
        '    }',
        '    :return;',
        '}',
        # --- Première connexion ---
        # Verrouillage MAC sur cet appareil
        ':local storedMac [:tostr [/ip hotspot user get $userId mac-address]];',
        ':if (([:len $loginMac] > 0) && (($storedMac = "") || ($storedMac = "00:00:00:00:00:00"))) do={ /ip hotspot user set $userId mac-address=$loginMac; }',
        # Lecture limit-uptime (durée du ticket)
        ':local limitVal [:tostr [/ip hotspot user get $userId limit-uptime]];',
        ':if (([:len $limitVal] = 0) || ($limitVal = "0") || ($limitVal = "0s") || ($limitVal = "none")) do={ :return; }',
        # Conversion durée → secondes
        ':local durSec 0;',
        ':local workVal $limitVal;',
        ':local wPos [:find $workVal "w"];',
        ':if ($wPos != nil) do={',
        '    :set durSec ($durSec + ([:tonum [:pick $workVal 0 $wPos]] * 604800));',
        '    :set workVal [:pick $workVal ($wPos + 1) [:len $workVal]];',
        '}',
        ':local dPos [:find $workVal "d"];',
        ':if ($dPos != nil) do={',
        '    :set durSec ($durSec + ([:tonum [:pick $workVal 0 $dPos]] * 86400));',
        '    :set workVal [:pick $workVal ($dPos + 1) [:len $workVal]];',
        '}',
        ':local colonPos [:find $workVal ":"];',
        ':if ($colonPos != nil) do={',
        '    :local dHH [:tonum [:pick $workVal 0 2]];',
        '    :local dMM [:tonum [:pick $workVal 3 5]];',
        '    :local dSS [:tonum [:pick $workVal 6 8]];',
        '    :set durSec ($durSec + ($dHH * 3600) + ($dMM * 60) + $dSS);',
        '} else={',
        '    :local hPos [:find $workVal "h"];',
        '    :if ($hPos != nil) do={',
        '        :set durSec ($durSec + ([:tonum [:pick $workVal 0 $hPos]] * 3600));',
        '        :set workVal [:pick $workVal ($hPos + 1) [:len $workVal]];',
        '    }',
        '    :local mPos [:find $workVal "m"];',
        '    :if ($mPos != nil) do={',
        '        :set durSec ($durSec + ([:tonum [:pick $workVal 0 $mPos]] * 60));',
        '        :set workVal [:pick $workVal ($mPos + 1) [:len $workVal]];',
        '    }',
        '    :local sPos [:find $workVal "s"];',
        '    :if ($sPos != nil) do={ :set durSec ($durSec + [:tonum [:pick $workVal 0 $sPos]]); }',
        '}',
        ':if ($durSec <= 0) do={ :return; }',
        # Calcul et stockage de l'epoch d'expiration absolue ; limit-uptime effacé
        ':local expireEpoch ($nowEpoch + $durSec);',
        ':if ([:len $currentComment] > 0) do={',
        '    /ip hotspot user set $userId comment=($currentComment . $marker . [:tostr $expireEpoch]) limit-uptime=0;',
        '} else={',
        '    /ip hotspot user set $userId comment=($markerAlt . [:tostr $expireEpoch]) limit-uptime=0;',
        '}',
    ])


def build_ketamon_ticket_expiry_script_source():
    # Seuls les tickets UTILISÉS ont le marqueur ##KETAMON## exp=...
    # Les tickets non utilisés (bytes-in=0, pas de marqueur) ne sont JAMAIS touchés.
    # Quand un ticket expiré est détecté : sessions/cookies/hosts coupés + ticket SUPPRIMÉ.
    # L'expiry est stockée en secondes depuis epoch (Jan 1 1970 heure locale) pour survivre
    # aux redémarrages du routeur ([:timestamp] était relatif au boot, inutilisable ici).
    return "\n".join([
        f':local marker "{KETAMON_TICKET_COMMENT_MARKER}";',
        f':local markerAlt "{KETAMON_TICKET_COMMENT_MARKER.strip()}";',
        *_build_routeros_local_epoch_lines(),
        ':local expiredIds [:toarray ""];',
        '/ip hotspot user',
        ':foreach userId in=[find] do={',
        '    :local comment [:tostr [get $userId comment]];',
        '    :local markerPos [:find $comment $marker];',
        '    :local markerLen [:len $marker];',
        '    :if ($markerPos = nil) do={',
        '        :set markerPos [:find $comment $markerAlt];',
        '        :set markerLen [:len $markerAlt];',
        '    }',
        '    :if ($markerPos != nil) do={',
        '        :local startPos ($markerPos + $markerLen);',
        '        :local expireRaw [:pick $comment $startPos [:len $comment]];',
        '        :if ([:len $expireRaw] > 0) do={',
        '            :local expireEpoch [:tonum $expireRaw];',
        '            :if ($expireEpoch >= 1000000000) do={',
        '                :if ($nowEpoch >= $expireEpoch) do={',
        '                    :local uname [:tostr [get $userId name]];',
        '                    :local lockedMac [:tostr [get $userId mac-address]];',
        '                    :foreach activeId in=[/ip hotspot active find where user=$uname] do={',
        '                        :local activeAddress [:tostr [/ip hotspot active get $activeId address]];',
        '                        :local activeMac [:tostr [/ip hotspot active get $activeId mac-address]];',
        '                        :if ([:len $activeAddress] > 0) do={ /ip hotspot host remove [find where address=$activeAddress]; }',
        '                        :if (([:len $activeMac] > 0) && ($activeMac != "00:00:00:00:00:00")) do={ /ip hotspot host remove [find where mac-address=$activeMac]; }',
        '                        /ip hotspot active remove $activeId;',
        '                    }',
        '                    :foreach cookieId in=[/ip hotspot cookie find where user=$uname] do={',
        '                        :local cookieMac [:tostr [/ip hotspot cookie get $cookieId mac-address]];',
        '                        :if (([:len $cookieMac] > 0) && ($cookieMac != "00:00:00:00:00:00")) do={ /ip hotspot host remove [find where mac-address=$cookieMac]; }',
        '                        /ip hotspot cookie remove $cookieId;',
        '                    }',
        '                    :if (([:len $lockedMac] > 0) && ($lockedMac != "00:00:00:00:00:00")) do={ /ip hotspot host remove [find where mac-address=$lockedMac]; }',
        '                    :set expiredIds ($expiredIds, $userId);',
        '                }',
        '            }',
        '        }',
        '    }',
        '}',
        ':foreach eid in=$expiredIds do={ /ip hotspot user remove $eid; }',
    ])


def upsert_router_script(api, name, source):
    if getattr(api, "is_relay_snapshot", False):
        # Relay: pas de snapshot /system/script — upsert inline RouterOS (add ou set)
        policy = "ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon"
        escaped = _relay_routeros_quote(source)
        upsert_src = "\n".join([
            f':if ([:len [/system script find name="{name}"]] > 0) do={{',
            f'  /system script set [find name="{name}"] source={escaped} policy="{policy}";',
            f'}} else={{',
            f'  /system script add name="{name}" source={escaped} policy="{policy}";',
            f'}}',
        ])
        api.queue_routeros_script(upsert_src)
        return
    resource = api.get_resource("/system/script")
    params = {
        "name": name,
        "source": source,
        "policy": "ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon",
    }
    rows = resource.get(name=name)
    if rows:
        resource.set(id=router_item_id(rows[0]), **params)
    else:
        resource.add(**params)


def upsert_router_scheduler(api, name, on_event, interval="30s", start_time="00:00:00"):
    resource = api.get_resource("/system/scheduler")
    params = {
        "name": name,
        "interval": interval,
        "on-event": on_event,
        "start-time": start_time,
        "disabled": "no",
        "policy": "ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon",
    }
    rows = resource.get(name=name)
    if rows:
        resource.set(id=router_item_id(rows[0]), **params)
    else:
        resource.add(**params)


def _get_ros_major_version(api):
    try:
        rows = api.get_resource("/system/resource").get()
        ver = str(rows[0].get("version", "6") if rows else "6")
        return int(ver.split(".")[0])
    except Exception:
        return 6

def ensure_ntp_configured(api):
    # Google Public NTP — IPs stables, compatibles v6 (pas de DNS) et v7
    NTP_V7_SERVER  = "pool.ntp.org"
    NTP_V6_PRIMARY = "216.239.35.0"   # time1.google.com
    NTP_V6_SECONDARY = "216.239.35.4" # time2.google.com
    try:
        major = _get_ros_major_version(api)
        res = api.get_resource("/system/ntp/client")
        rows = res.get()
        current = rows[0] if rows else {}
        enabled = str(current.get("enabled", "no")).strip().lower()

        if major >= 7:
            servers = str(current.get("servers", "")).strip()
            if enabled != "yes" or NTP_V7_SERVER not in servers:
                res.set(enabled="yes", servers=NTP_V7_SERVER)
        else:
            primary = str(current.get("primary-ntp", "")).strip()
            if enabled != "yes" or primary != NTP_V6_PRIMARY:
                res.set(**{"enabled": "yes", "primary-ntp": NTP_V6_PRIMARY, "secondary-ntp": NTP_V6_SECONDARY})
    except Exception:
        pass


def _ensure_ticket_runtime_profile_binding(api, profile_resource, profile_row):
    profile_name = str(profile_row.get("name") or "").strip()
    if not profile_name:
        return
    current_on_login = str(profile_row.get("on-login") or "").strip()
    wrapper_name = sanitize_router_script_name("ketamon-login", profile_name)
    desired_on_login = KETAMON_TICKET_LOGIN_SCRIPT

    if current_on_login and current_on_login not in {KETAMON_TICKET_LOGIN_SCRIPT, wrapper_name}:
        upsert_router_script(api, wrapper_name, build_ticket_login_wrapper_script(current_on_login))
        desired_on_login = wrapper_name
    elif current_on_login == wrapper_name:
        desired_on_login = wrapper_name

    if current_on_login != desired_on_login:
        item_id = router_item_id(profile_row)
        if item_id:
            profile_resource.set(id=item_id, **{"on-login": desired_on_login})
        elif profile_name:
            # Profil synthétique (DB seulement, pas encore dans snapshot) — set par nom
            profile_resource.set(id=profile_name, **{"on-login": desired_on_login})


def ensure_ticket_runtime_support(api, profile_name=None):
    ensure_ntp_configured(api)
    upsert_router_script(api, KETAMON_TICKET_LOGIN_SCRIPT, build_ketamon_ticket_login_script_source())
    upsert_router_script(api, KETAMON_TICKET_EXPIRY_SCRIPT, build_ketamon_ticket_expiry_script_source())
    upsert_router_scheduler(api, KETAMON_TICKET_EXPIRY_SCHEDULER, KETAMON_TICKET_EXPIRY_SCRIPT)

    profile_resource = api.get_resource("/ip/hotspot/user/profile")
    profile_name = str(profile_name or "").strip()
    profiles = profile_resource.get(name=profile_name) if profile_name else profile_resource.get()
    if not profiles:
        return

    for profile_row in profiles:
        _ensure_ticket_runtime_profile_binding(api, profile_resource, profile_row)


def _build_ketamon_installer_rsc():
    """
    Génère un fichier .rsc RouterOS qui installe ketamon-ticket-login, ketamon-ticket-expiry
    et leur scheduler via la syntaxe source={...} — aucun quoting, aucun échappement.
    Stratégie remove+add (idempotent, pas de if/else imbriqué).
    Compatible RouterOS v6 et v7.
    """
    policy     = "ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon"
    exp_name   = KETAMON_TICKET_EXPIRY_SCRIPT
    login_name = KETAMON_TICKET_LOGIN_SCRIPT
    sch_name   = KETAMON_TICKET_EXPIRY_SCHEDULER
    login_src  = build_ketamon_ticket_login_script_source()
    expiry_src = build_ketamon_ticket_expiry_script_source()
    lines = [
        "# KetaMon ticket scripts installer v2 — file-based, no quoting",
        # Script login : remove puis add (idempotent)
        f':do {{ /system script remove [find name="{login_name}"]; }} on-error={{}}',
        f'/system script add name="{login_name}" policy="{policy}" source={{',
        login_src,
        '}',
        # Script expiry : remove puis add (idempotent)
        f':do {{ /system script remove [find name="{exp_name}"]; }} on-error={{}}',
        f'/system script add name="{exp_name}" policy="{policy}" source={{',
        expiry_src,
        '}',
        # Scheduler : remove puis add
        f':do {{ /system scheduler remove [find name="{sch_name}"]; }} on-error={{}}',
        f'/system scheduler add name="{sch_name}" interval=30s on-event="{exp_name}" start-time=00:00:00 disabled=no',
        # Attacher on-login sur tous les profils hotspot sans on-login personnalisé
        f':foreach pId in=[/ip hotspot user profile find] do={{',
        f'  :local cur [:tostr [/ip hotspot user profile get $pId on-login]];',
        f'  :if (($cur = "") || ($cur = "none") || ($cur = "{login_name}")) do={{',
        f'    /ip hotspot user profile set $pId on-login="{login_name}";',
        f'  }};',
        f'}}',
    ]
    return "\n".join(lines)


def _relay_queue_expiry_install(router):
    """
    Routeur relais : met en file un script RouterOS qui installe ou met à jour
    le script d'expiry, le script de login, et leur scheduler.
    Idempotent — s'exécute sans connexion directe, indépendamment de l'état du serveur.
    Si l'URL publique est connue, utilise l'approche fichier (download + import) — aucun quoting.
    Sinon, fallback sur source embeddée échappée.
    """
    router_id = str(router.get("id") or router.get("host") or "").strip()
    owner_id  = str(router.get("owner_id") or "").strip()
    if not router_id:
        return
    token    = str(router.get("relay_token") or "").strip()
    base_url = (
        os.environ.get("KETAMON_PUBLIC_URL", "").strip().rstrip("/")
        or _relay_public_url_cache
    )
    if base_url and token:
        # Approche fiable : MikroTik télécharge un .rsc et l'importe — zéro quoting/échappement
        installer_url = f"{base_url}/api/relay/scripts/installer.rsc?token={quote(token)}"
        source = (
            f':do {{ /tool fetch url="{installer_url}" dst-path="ktm-install.rsc" duration=20s; '
            f':delay 1s; /import file-name="ktm-install.rsc"; '
            f':do {{ /file remove [find name="ktm-install.rsc"]; }} on-error={{}}; }} on-error={{}}'
        )
    else:
        # Fallback local : source embeddée avec échappement (pas d'URL publique disponible)
        policy     = "ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon"
        exp_name   = KETAMON_TICKET_EXPIRY_SCRIPT
        login_name = KETAMON_TICKET_LOGIN_SCRIPT
        sch_name   = KETAMON_TICKET_EXPIRY_SCHEDULER
        esc_exp    = _relay_routeros_quote(build_ketamon_ticket_expiry_script_source())
        esc_login  = _relay_routeros_quote(build_ketamon_ticket_login_script_source())
        source = "\n".join([
            f':if ([:len [/system script find name="{exp_name}"]] > 0) do={{',
            f'  /system script set [find name="{exp_name}"] source={esc_exp} policy="{policy}";',
            f'}} else={{',
            f'  /system script add name="{exp_name}" source={esc_exp} policy="{policy}";',
            f'}};',
            f':if ([:len [/system script find name="{login_name}"]] > 0) do={{',
            f'  /system script set [find name="{login_name}"] source={esc_login} policy="{policy}";',
            f'}} else={{',
            f'  /system script add name="{login_name}" source={esc_login} policy="{policy}";',
            f'}};',
            f':if ([:len [/system scheduler find name="{sch_name}"]] > 0) do={{',
            f'  /system scheduler set [find name="{sch_name}"] interval=30s on-event="{exp_name}" disabled=no;',
            f'}} else={{',
            f'  /system scheduler add name="{sch_name}" interval=30s on-event="{exp_name}"'
            f' start-time=00:00:00 disabled=no;',
            f'}};',
            f':foreach pId in=[/ip hotspot user profile find] do={{',
            f'  :local cur [:tostr [/ip hotspot user profile get $pId on-login]];',
            f'  :if (($cur = "") || ($cur = "none") || ($cur = "{login_name}")) do={{',
            f'    /ip hotspot user profile set $pId on-login="{login_name}";',
            f'  }};',
            f'}};',
        ])
    db_mod.db_enqueue_router_relay_command(router_id, owner_id, "routeros-script", {"source": source})


def normalize_hotspot_profile(profile, metadata=None):
    row = dict(profile or {})
    meta = dict(metadata or {})
    if not meta:
        meta = parse_profile_comment_metadata(row)
    profile_name = str(row.get("name") or meta.get("profile_name") or "").strip()
    inferred_time = _infer_time_limit_from_profile_name(profile_name)
    meta_time = str(meta.get("time_limit") or "").strip()
    if inferred_time and meta_time.lower() in {"", "0", "0s", "none"}:
        meta["time_limit"] = inferred_time
        if str(meta.get("expire_mode") or "").strip().lower() in {"", "none"}:
            meta["expire_mode"] = "remove and record"
        if str(meta.get("lock_user") or "").strip().lower() in {"", "no", "false", "0"}:
            meta["lock_user"] = "yes"
    if meta.get("expire_mode"):
        row["expire-mode"] = meta.get("expire_mode")
    if meta.get("lock_user"):
        row["add-mac-cookie"] = meta.get("lock_user")
    if meta.get("price") is not None:
        row["price"] = meta.get("price")
    if meta.get("currency"):
        row["currency"] = meta.get("currency")
    row["time-limit"] = normalize_profile_time_limit(meta.get("time_limit")) or "0"
    row["_ketamon_meta"] = bool(meta)
    return row


def _relay_fallback_rows(router_id, path):
    router_id = str(router_id or "").strip()
    path = str(path or "").rstrip("/")
    if not router_id:
        return []
    conn = db_mod.get_conn()
    if path == "/ip/hotspot/user/profile":
        rows = conn.execute("""
            SELECT profile_name, price, currency, expire_mode, lock_user, time_limit
            FROM hotspot_profile_metadata
            WHERE router_id=?
            ORDER BY profile_name
        """, (router_id,)).fetchall()
        return [{
            ".id": f"*db-prof-{idx}",
            "name": row["profile_name"],
            "rate-limit": "",
            "shared-users": "1",
            "address-pool": "",
            "price": row["price"],
            "currency": row["currency"],
            "expire-mode": row["expire_mode"],
            "add-mac-cookie": row["lock_user"],
            "time-limit": row["time_limit"],
            "_source": "database",
        } for idx, row in enumerate(rows, start=1)]
    if path == "/ip/hotspot/user":
        rows = conn.execute("""
            SELECT tp.user, tp.profil, tp.created_at, hp.time_limit
            FROM ticket_pricing tp
            LEFT JOIN hotspot_profile_metadata hp
              ON hp.router_id=tp.router_id
             AND hp.profile_name=tp.profil
            WHERE tp.router_id=?
            ORDER BY tp.created_at DESC, tp.user
            LIMIT 1000
        """, (router_id,)).fetchall()
        restored = []
        for idx, row in enumerate(rows, start=1):
            limit_uptime = coerce_ticket_time_limit_router(row["time_limit"], empty="0", prefer_legacy_routeros=False) or "0"
            restored.append({
                ".id": f"*db-user-{idx}",
                "name": row["user"],
                "password": row["user"],
                "profile": row["profil"] or "default",
                "disabled": "no",
                "limit-uptime": limit_uptime,
                "uptime": "0",
                "comment": "restored-from-database",
                "_source": "database",
            })
        return restored
    if path == "/ip/hotspot":
        row = conn.execute("""
            SELECT reseau
            FROM ticket_pricing
            WHERE router_id=? AND COALESCE(reseau,'')!=''
            GROUP BY reseau
            ORDER BY COUNT(*) DESC
            LIMIT 1
        """, (router_id,)).fetchone()
        if row and row["reseau"]:
            return [{".id": "*db-hotspot-1", "name": row["reseau"], "_source": "database"}]
    if path == "/interface":
        iface_name = "ether1"
        try:
            hs_rows = db_mod.db_get_router_relay_snapshot(router_id, "/ip/hotspot")
            if hs_rows:
                iface_name = str(hs_rows[0].get("interface") or "ether1")
        except Exception:
            pass
        return [{
            ".id": "*1",
            "name": iface_name,
            "type": "ether",
            "running": "true",
            "disabled": "false",
            "mtu": "1500",
            "actual-mtu": "1500",
            "mac-address": "",
            "rx-byte": "0",
            "tx-byte": "0",
            "rx-packet": "0",
            "tx-packet": "0",
            "_source": "fallback",
        }]
    return []


def _relay_database_dashboard_data(router):
    router = dict(router or {})
    router_id = str(router.get("id") or router.get("host") or "").strip()
    conn = db_mod.get_conn()
    tickets = conn.execute("SELECT COUNT(*) FROM ticket_pricing WHERE router_id=?", (router_id,)).fetchone()[0]
    profiles = conn.execute("SELECT COUNT(*) FROM hotspot_profile_metadata WHERE router_id=?", (router_id,)).fetchone()[0]
    active = 0
    fresh_active, _updated_at, _age = _relay_snapshot_state(router_id, "/ip/hotspot/active")
    if fresh_active:
        active = len(db_mod.db_get_router_relay_snapshot(router_id, "/ip/hotspot/active"))
    server = conn.execute("""
        SELECT reseau
        FROM ticket_pricing
        WHERE router_id=? AND COALESCE(reseau,'')!=''
        GROUP BY reseau
        ORDER BY COUNT(*) DESC
        LIMIT 1
    """, (router_id,)).fetchone()
    # Lire les ressources systeme depuis les snapshots relay
    res = {}
    ident = {}
    clock = {}
    rb = {}
    try:
        rows = db_mod.db_get_router_relay_snapshot(router_id, "/system/resource")
        if rows and isinstance(rows, list):
            res = dict(rows[0])
    except Exception:
        pass
    try:
        rows = db_mod.db_get_router_relay_snapshot(router_id, "/system/identity")
        if rows and isinstance(rows, list):
            ident = dict(rows[0])
    except Exception:
        pass
    try:
        rows = db_mod.db_get_router_relay_snapshot(router_id, "/system/clock")
        if rows and isinstance(rows, list):
            clock = dict(rows[0])
    except Exception:
        pass
    try:
        rows = db_mod.db_get_router_relay_snapshot(router_id, "/system/routerboard")
        if rows and isinstance(rows, list):
            rb = dict(rows[0])
    except Exception:
        pass
    total_mem = int(res.get("total-memory", 0) or 0)
    free_mem  = int(res.get("free-memory",  0) or 0)
    total_hdd = int(res.get("total-hdd-space", 0) or 0)
    free_hdd  = int(res.get("free-hdd-space",  0) or 0)
    mem_pct   = round((total_mem - free_mem) / total_mem * 100) if total_mem else 0
    identity  = ident.get("name") or res.get("board-name") or router.get("name") or "MikroTik"
    board     = rb.get("model") or res.get("board-name") or "Relais KetaMon"
    clk_time  = clock.get("time") or ""
    clk_date  = clock.get("date") or router.get("relay_last_seen") or ""
    return {
        "identity": identity,
        "board": board,
        "version": res.get("version") or "RouterOS",
        "uptime": res.get("uptime") or "",
        "cpu_load": str(res.get("cpu-load") or "0"),
        "total_mem": mk.format_bytes(total_mem) if total_mem else "",
        "free_mem": mk.format_bytes(free_mem) if free_mem else "",
        "mem_pct": mem_pct,
        "total_hdd": mk.format_bytes(total_hdd) if total_hdd else "",
        "free_hdd": mk.format_bytes(free_hdd) if free_hdd else "",
        "time": clk_time,
        "date": clk_date,
        "hs_users": tickets,
        "hs_active": active,
        "hs_profiles": profiles,
        "hs_servers": [server["reseau"]] if server and server["reseau"] else [router.get("name", "")],
        "router_host": router.get("host", ""),
        "router_port": str(router.get("port", "8728")),
        "restored_from_db": True,
    }


RELAY_ACTIVE_SNAPSHOT_TTL_SECONDS = safe_int(
    os.environ.get("KETAMON_RELAY_ACTIVE_TTL", "300"),
    default=300,
    min_val=30,
    max_val=3600,
)
RELAY_VOLATILE_RESOURCES = {"/ip/hotspot/active"}


def _relay_snapshot_state(router_id, resource, ttl_seconds=RELAY_ACTIVE_SNAPSHOT_TTL_SECONDS):
    router_id = str(router_id or "").strip()
    resource = str(resource or "").rstrip("/") or "/"
    if not router_id:
        return False, "", None
    try:
        snapshots = db_mod.db_get_router_relay_snapshot(router_id)
        if not isinstance(snapshots, dict):
            snapshots = {}
        meta = snapshots.get(resource)
        updated_at = str((meta or {}).get("updated_at") or "")
        age = None
        if updated_at:
            updated_dt = datetime.fromisoformat(updated_at.replace("Z", "+00:00"))
            if updated_dt.tzinfo is not None:
                updated_dt = updated_dt.replace(tzinfo=None)
            age = max(0, int((datetime.now() - updated_dt).total_seconds()))
            if age <= int(ttl_seconds or 120):
                return True, updated_at, age
        # La ressource spécifique est obsolète ou absente.
        # Si /ketamon/relay-status est frais, le relay tourne mais la ressource est vide (ex: 0 sessions actives).
        relay_meta = snapshots.get("/ketamon/relay-status")
        relay_updated_at = str((relay_meta or {}).get("updated_at") or "")
        if relay_updated_at:
            relay_dt = datetime.fromisoformat(relay_updated_at.replace("Z", "+00:00"))
            if relay_dt.tzinfo is not None:
                relay_dt = relay_dt.replace(tzinfo=None)
            relay_age = max(0, int((datetime.now() - relay_dt).total_seconds()))
            if relay_age <= int(ttl_seconds or 120):
                return True, updated_at, age
        return False, updated_at, age
    except Exception:
        return False, "", None


class RelaySnapshotResource:
    def __init__(self, relay_api, path):
        self._api = relay_api
        self._path = str(path or "").rstrip("/") or "/"

    def _rows(self):
        if self._path in RELAY_VOLATILE_RESOURCES:
            fresh, updated_at, age = _relay_snapshot_state(self._api.router_id, self._path)
            if not fresh:
                self._api.stale_resources[self._path] = {
                    "updated_at": updated_at,
                    "age": age,
                    "ttl": RELAY_ACTIVE_SNAPSHOT_TTL_SECONDS,
                }
                return []
        rows = db_mod.db_get_router_relay_snapshot(self._api.router_id, self._path)
        normalized = [dict(row) for row in (rows or []) if isinstance(row, dict)]
        if self._path == "/ip/hotspot/user/profile":
            metadata_map = get_hotspot_profile_metadata_map(self._api.router_id)
            seen = set()
            enriched = []
            for row in normalized:
                name = str(row.get("name") or "").strip()
                if name:
                    seen.add(name)
                enriched.append(normalize_hotspot_profile(row, metadata_map.get(name, {})))
            for name, meta in metadata_map.items():
                if name not in seen:
                    enriched.append(normalize_hotspot_profile({"name": name, "_source": "database"}, meta))
            return enriched
        if self._path == "/ip/hotspot/user":
            metadata_map = get_hotspot_profile_metadata_map(self._api.router_id)
            for row in normalized:
                username = str(row.get("name") or "").strip()
                if not username:
                    continue
                meta = _ticket_db_meta(self._api.router_id, username)
                profile = str(row.get("profile") or meta.get("profil") or "").strip()
                if profile and not row.get("profile"):
                    row["profile"] = profile
                if not str(row.get("limit-uptime") or "").strip() or str(row.get("limit-uptime") or "").strip() == "0":
                    duration = metadata_map.get(profile, {}).get("time_limit") if profile else ""
                    if not duration:
                        duration = _ticket_meta_time_limit(meta)
                    limit = coerce_ticket_time_limit_router(duration, empty="0", prefer_legacy_routeros=False) or "0"
                    row["limit-uptime"] = limit
        if normalized:
            return normalized
        return _relay_fallback_rows(self._api.router_id, self._path)

    def get(self, **filters):
        rows = self._rows()
        if not filters:
            return rows
        filtered = []
        for row in rows:
            matched = True
            for key, value in filters.items():
                probe_keys = [key]
                if key == "id":
                    probe_keys.append(".id")
                    if not str(value).strip().startswith("*"):
                        probe_keys.append("name")
                elif key == ".id":
                    probe_keys.append("id")
                expected = str(value)
                if not any(str(row.get(k, "")) == expected for k in probe_keys):
                    matched = False
                    break
            if matched:
                filtered.append(row)
        return filtered

    def add(self, **params):
        source = _relay_build_resource_command(self._path, "add", params)
        return self._api.queue_routeros_script(source)

    def set(self, **params):
        params = dict(params or {})
        item_id = params.pop("id", params.pop(".id", ""))
        if item_id and not _is_real_router_item_id(item_id):
            source = _routeros_set_by_name_source(self._path, item_id, params)
        else:
            source = _relay_build_resource_command(self._path, "set", params, item_id=item_id)
        return self._api.queue_routeros_script(source)

    def remove(self, id):
        item_id = str(id or "").strip()
        if item_id and not _is_real_router_item_id(item_id):
            source = f"{_relay_routeros_path(self._path)} remove [{_routeros_find_target(self._path, item_id)}];"
        else:
            source = _relay_build_resource_command(self._path, "remove", {}, item_id=item_id)
        return self._api.queue_routeros_script(source)

    def call(self, command, extra_params=None):
        command = str(command or "").strip()
        extra_params = dict(extra_params or {})
        if command == "print" and "count-only" in extra_params:
            return len(self._rows())
        source = _relay_build_resource_command(self._path, command, extra_params)
        return self._api.queue_routeros_script(source)


class RelaySnapshotApi:
    def __init__(self, router):
        self.router = dict(router or {})
        self.router_id = str(self.router.get("id") or self.router.get("host") or "").strip()
        self.owner_id = str(self.router.get("owner_id") or "").strip()
        self.is_relay_snapshot = True
        self.stale_resources = {}

    def get_resource(self, path):
        return RelaySnapshotResource(self, path)

    def queue_routeros_script(self, source):
        if not self.router_id:
            raise RuntimeError("Routeur relais introuvable")
        command = db_mod.db_enqueue_router_relay_command(
            self.router_id,
            self.owner_id,
            "routeros-script",
            {"source": str(source or "")},
        )
        if not command:
            raise RuntimeError("Impossible de creer la commande relais")
        return command["id"]

    def close(self):
        return None


def _router_has_relay_snapshots(router) -> bool:
    router_id = str((router or {}).get("id") or (router or {}).get("host") or "").strip()
    if not router_id:
        return False
    try:
        snapshots = db_mod.db_get_router_relay_snapshot(router_id)
        return bool(snapshots)
    except Exception:
        return False


def _relay_routeros_path(path):
    parts = [part for part in str(path or "").strip("/").split("/") if part]
    return "/" + " ".join(parts) if parts else "/"


def _relay_routeros_quote(value):
    text = str(value if value is not None else "")
    text = text.replace("\\", "\\\\").replace('"', '\\"').replace("$", "\\$")
    text = text.replace("\r", "").replace("\n", "\\n")
    return f'"{text}"'


def _relay_routeros_key(key):
    return str(key or "").strip().replace("_", "-")


def _relay_build_resource_command(path, action, params=None, item_id=""):
    path_cmd = _relay_routeros_path(path)
    action = str(action or "").strip()
    params = dict(params or {})
    parts = [path_cmd, action]
    if item_id:
        parts.append(_relay_routeros_quote(item_id))
    for key, value in params.items():
        key = _relay_routeros_key(key)
        if not key:
            continue
        if key in {"id", ".id"}:
            continue
        parts.append(f"{key}={_relay_routeros_quote(value)}")
    return " ".join(parts) + ";"


def get_api():
    r = get_active_router()
    if not r:
        return None, "Aucun routeur actif"
    if int(r.get("relay_enabled") or 0):
        return RelaySnapshotApi(r), None
    api, err = mk.safe_connect_router(r)
    if api:
        apis = getattr(g, "_mikrotik_apis", None)
        if apis is None:
            apis = []
            g._mikrotik_apis = apis
        apis.append(api)
    return api, err


def _connect_router_universal(router):
    router = dict(router or {})
    api, err = mk.safe_connect_router(router)
    if not err and api:
        return api, None
    if int(router.get("relay_enabled") or 0):
        return RelaySnapshotApi(router), None
    return api, err


def _apply_ticket_runtime_to_router(router_info, timeout=8):
    """
    Tente d'installer immédiatement les scripts ticket sur un routeur.
    Retourne (ok, message) sans lever d'exception bloquante pour le parcours UI.
    """
    router_info = dict(router_info or {})
    api = None
    try:
        api, err = mk.safe_connect_router(router_info, timeout=timeout)
        if err or not api:
            return False, str(err or "connexion impossible")
        ensure_ntp_configured(api)
        ensure_ticket_runtime_support(api)
        return True, ""
    except Exception as e:
        return False, str(e)
    finally:
        _close_api_quietly(api)


def _normalize_router_count(value):
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value.strip())
        except Exception:
            return None
    if isinstance(value, dict):
        return _normalize_router_count(value.get("ret") or value.get("count"))
    if isinstance(value, (list, tuple)):
        if not value:
            return 0
        if len(value) == 1:
            parsed = _normalize_router_count(value[0])
            if parsed is not None:
                return parsed
        return len(value)
    return None


def resource_count(api, path):
    resource = api.get_resource(path)
    try:
        raw_count = resource.call("print", {"count-only": ""})
        if raw_count not in (None, [], (), ""):
            direct_count = _normalize_router_count(raw_count)
            if direct_count is not None:
                return direct_count
    except Exception:
        pass
    try:
        items = resource.get()
        return len(list(items or []))
    except Exception:
        return 0

# ─── Context processor ───────────────────────────────────────────────────────
def resource_first(api, path):
    try:
        rows = api.get_resource(path).get()
        return rows[0] if rows else {}
    except Exception:
        return {}


def _invalidate_routers_cache():
    _layout_routers_cache["ts"] = 0.0

# Cache court pour la liste des routeurs (évite une requête SQL à chaque render)
_layout_routers_cache: dict = {"data": [], "ts": 0.0, "owner": ""}
_LAYOUT_ROUTERS_TTL = 4  # secondes

# Cache permanent pour la version CSS/JS/PWA (mtime calcule une seule fois au boot)
_css_ver_cache: dict = {"v": 0}
_js_ver_cache: dict = {"v": 0}
_pwa_ver_cache: dict = {"v": ""}

def _get_css_ver():
    if not _css_ver_cache["v"]:
        try:
            _css_ver_cache["v"] = int(os.path.getmtime(
                os.path.join(os.path.dirname(__file__), "static", "css", "style.css")
            ))
        except Exception:
            _css_ver_cache["v"] = 1
    return _css_ver_cache["v"]


def _get_js_ver():
    if not _js_ver_cache["v"]:
        try:
            _js_ver_cache["v"] = int(os.path.getmtime(
                os.path.join(os.path.dirname(__file__), "static", "js", "main.js")
            ))
        except Exception:
            _js_ver_cache["v"] = 1
    return _js_ver_cache["v"]


def _get_pwa_ver():
    if _pwa_ver_cache["v"]:
        return _pwa_ver_cache["v"]

    override = os.environ.get("KETAMON_PWA_VERSION", "").strip()
    if override:
        cleaned = re.sub(r"[^0-9A-Za-z_.-]", "", override)
        _pwa_ver_cache["v"] = cleaned or "1"
        return _pwa_ver_cache["v"]

    watched_paths = [
        ("app.py",),
        ("database.py",),
        ("ketamon_agent.py",),
        ("templates", "base.html"),
        ("templates", "login.html"),
        ("static", "sw.js"),
        ("static", "manifest.json"),
        ("static", "css", "style.css"),
        ("static", "js", "main.js"),
    ]
    mtimes = []
    for parts in watched_paths:
        try:
            mtimes.append(int(os.path.getmtime(os.path.join(APP_DIR, *parts))))
        except Exception:
            pass
    for root_parts in (("templates",), ("static", "css"), ("static", "js")):
        root_dir = os.path.join(APP_DIR, *root_parts)
        try:
            for dirpath, _dirnames, filenames in os.walk(root_dir):
                for filename in filenames:
                    try:
                        mtimes.append(int(os.path.getmtime(os.path.join(dirpath, filename))))
                    except Exception:
                        pass
        except Exception:
            pass
    _pwa_ver_cache["v"] = str(max(mtimes) if mtimes else int(time.time()))
    return _pwa_ver_cache["v"]

def _safe_agent_count(logged_in: bool) -> int:
    try:
        if logged_in and session.get("role") == "concepteur":
            return db_mod.db_agent_count_open()
    except Exception:
        pass
    return 0


@app.context_processor
def inject_layout_context():
    logged_in = bool(session.get("logged_in"))
    routers = []
    if logged_in:
        owner = _current_owner_id() or ""
        now = time.time()
        if (now - _layout_routers_cache["ts"] > _LAYOUT_ROUTERS_TTL
                or _layout_routers_cache["owner"] != owner):
            _layout_routers_cache["data"]  = get_routers()
            _layout_routers_cache["ts"]    = now
            _layout_routers_cache["owner"] = owner
        routers = _layout_routers_cache["data"]
    return {
        "routers": routers,
        "active_router": get_active_router() if logged_in else None,
        "current_page": request.endpoint or "",
        "adsense_pub_id":       os.environ.get("ADSENSE_PUB_ID", ""),
        "adsense_banner_slot":  "",
        "adsense_inter_slot":   "",
        "adsterra_banner_code": "",
        "adsterra_inter_code":  "",
        "_css_ver": _get_css_ver(),
        "_js_ver": _get_js_ver(),
        "_pwa_ver": _get_pwa_ver(),
        "agent_open_count": _safe_agent_count(logged_in),
    }

@app.route("/login", methods=["GET", "POST"])
def login():
    if session.get("logged_in"):
        return redirect(url_for("index"))

    # Variables pour re-afficher la page avec le bon mode/sous-mode
    tpl_vars = {"mode": "utilisateur", "submode": "login",
                "prefill_email": "", "reset_token": None}

    if request.method == "POST":
        # ── Protection brute-force ─────────────────────────────────────────
        if _check_login_rate_limit():
            flash("Trop de tentatives de connexion. Réessayez dans 10 minutes.", "danger")
            return render_template("login.html", **tpl_vars)

        mode    = request.form.get("mode", "email")      # "username" | "email"
        submode = request.form.get("submode", "login")   # "login"|"register"|"forgot"|"reset"
        tpl_vars["mode"]    = "concepteur" if mode == "username" else "utilisateur"
        tpl_vars["submode"] = submode

        # ── CONCEPTEUR (username + password) ──────────────────────────────
        if mode == "username":
            username = request.form.get("username", "").strip()
            password = request.form.get("password", "")
            tpl_vars["mode"] = "concepteur"
            resp, err = ks_post("/api/auth/login", {"username": username, "password": password})
            if resp and resp.get("ok"):
                _clear_login_failures()
                session.permanent = True
                session.update({
                    "logged_in": True, "ks_token": resp.get("token"),
                    "username": resp.get("displayName") or username,
                    "role": "concepteur", "user_id": username,
                })
                return redirect(url_for("index"))
            else:
                # Fallback : fichier concepteur local
                creds_ok = False
                creds_file = os.environ.get("KETASERVER_CONCEPTEUR_FILE") or os.path.join(DATA_DIR, "concepteur.json")
                try:
                    with open(creds_file, encoding="utf-8") as f:
                        creds = json.load(f)
                    stored = creds.get("password", "")
                    if stored and stored.startswith(("pbkdf2:", "scrypt:")):
                        if check_password_hash(stored, password) and str(creds.get("username") or "").casefold() == username.casefold():
                            creds_ok = True
                            display = creds.get("displayName", username)
                    else:
                        _logger.warning("Mot de passe concepteur non hashé dans concepteur.json — utilisez un hash Werkzeug (pbkdf2: ou scrypt:).")
                        flash("Mot de passe concepteur non hashé. Regénérez-le avec un hash Werkzeug.", "danger")
                except Exception:
                    pass
                if creds_ok:
                    _clear_login_failures()
                    session.permanent = True
                    session.update({
                        "logged_in": True, "ks_token": None,
                        "username": display,
                        "role": "concepteur", "user_id": username,
                    })
                    return redirect(url_for("index"))

                local_admin = authenticate_local_user(username, password)
                if local_admin and str(local_admin.get("role") or "").lower() in {"admin", "concepteur"}:
                    if not _local_user_is_approved(local_admin) or not _local_user_is_active(local_admin):
                        flash(_local_user_access_message(local_admin), "warning")
                        return render_template("login.html", **tpl_vars)
                    _clear_login_failures()
                    session.permanent = True
                    session.update({
                        "logged_in": True,
                        "ks_token": None,
                        "ks_refresh_token": None,
                        "username": local_admin.get("displayName") or username,
                        "role": local_admin.get("role", "admin"),
                        "user_id": local_admin.get("email") or local_admin.get("username") or username,
                        "auth_source": "local",
                    })
                    return redirect(url_for("index"))
                _record_login_failure()
                flash("Identifiants concepteur incorrects.", "danger")

        # ── UTILISATEUR EMAIL — CONNEXION ──────────────────────────────────
        elif submode == "login":
            email    = request.form.get("email", "").strip()
            password = request.form.get("password", "")
            tpl_vars["prefill_email"] = email
            resp, err = ks_post("/api/auth/login", {"email": email, "password": password})
            remote_session = build_remote_user_session(resp, email)
            if err:
                # Try local fallback
                user = authenticate_local_user(email, password)
                if user:
                    if not _local_user_is_approved(user) or not _local_user_is_active(user):
                        flash(_local_user_access_message(user), "warning")
                        return render_template("login.html", **tpl_vars)
                    _clear_login_failures()
                    session.permanent = True
                    session.update({
                        "logged_in": True, "ks_token": None,
                        "ks_refresh_token": None,
                        "username": user.get("displayName") or email,
                        "role": user.get("role", "utilisateur"), "user_id": email,
                        "auth_source": "local",
                    })
                    return redirect(url_for("index"))
                _record_login_failure()
                flash("KetaServer indisponible ou identifiants incorrects.", "danger")
            elif remote_session:
                shadow = _ensure_local_email_shadow(
                    email,
                    password=password,
                    display_name=remote_session.get("username") or email,
                    role=remote_session.get("role", "utilisateur"),
                )
                if not shadow:
                    flash("Impossible de verifier l'activation de ce compte Gmail.", "danger")
                    return render_template("login.html", **tpl_vars)
                if not _local_user_is_approved(shadow) or not _local_user_is_active(shadow):
                    flash(_local_user_access_message(shadow), "warning")
                    return render_template("login.html", **tpl_vars)
                _clear_login_failures()
                session.permanent = True
                session.update(remote_session)
                return redirect(url_for("index"))
            else:
                _record_login_failure()
                flash("Email ou mot de passe incorrect.", "danger")

        # ── INSCRIPTION ────────────────────────────────────────────────────
        elif submode == "register":
            email    = request.form.get("email", "").strip()
            password = request.form.get("password", "")
            confirm  = request.form.get("confirm_password", "")
            display  = request.form.get("display_name", "").strip()
            tpl_vars["prefill_email"] = email
            if not is_valid_email(email):
                flash("Adresse email invalide.", "danger")
            elif password != confirm:
                flash("Les mots de passe ne correspondent pas.", "danger")
            elif len(password) < 8:
                flash("Mot de passe min. 8 caracteres.", "danger")
            else:
                existing_local = db_mod.db_get_local_user(email)
                if (
                    existing_local
                    and _local_concepteur_exists()
                    and _local_user_is_approved(existing_local)
                    and _local_user_is_active(existing_local)
                ):
                    flash("Ce compte Gmail existe deja. Connectez-vous.", "warning")
                    tpl_vars["submode"] = "login"
                    return render_template("login.html", **tpl_vars)

                shadow = local_register(email, password, display)
                if shadow and shadow.get("_bootstrap_owner"):
                    _clear_login_failures()
                    session.permanent = True
                    session.update({
                        "logged_in": True,
                        "ks_token": None,
                        "ks_refresh_token": None,
                        "username": shadow.get("displayName") or email,
                        "role": shadow.get("role", "concepteur"),
                        "user_id": shadow.get("email") or email,
                        "auth_source": "local",
                    })
                    flash("Compte concepteur cloud cree. Vous pouvez maintenant activer les autres comptes.", "success")
                    return redirect(url_for("index"))

                resp, err = ks_post("/api/auth/register",
                                    {"email": email, "password": password, "displayName": display})
                if not shadow:
                    flash("Inscription impossible. Réessayez.", "danger")
                elif err:
                    flash("Compte Gmail cree. En attente d'activation par le concepteur.", "success")
                    tpl_vars["submode"] = "login"
                    return render_template("login.html", **tpl_vars)
                elif resp and resp.get("ok"):
                    flash("Compte Gmail cree. En attente d'activation par le concepteur.", "success")
                    tpl_vars["submode"] = "login"
                    return render_template("login.html", **tpl_vars)
                else:
                    flash(
                        resp.get("message", "Compte en attente d'activation par le concepteur.") if resp
                        else "Compte en attente d'activation par le concepteur.",
                        "warning"
                    )
                    tpl_vars["submode"] = "login"
                    return render_template("login.html", **tpl_vars)

        # ── MOT DE PASSE OUBLIÉ ────────────────────────────────────────────
        elif submode == "forgot":
            email = request.form.get("email", "").strip()
            tpl_vars["prefill_email"] = email
            resp, err = ks_post("/api/auth/forgot-password", {"email": email})
            if err:
                flash("KetaServer indisponible — réinitialisation non disponible.", "danger")
            elif resp and resp.get("ok"):
                raw_token = (resp.get("resetUrl") or "").split("token=")[-1] or ""
                if raw_token:
                    # Stocker le token en session (jamais dans le HTML)
                    session["_pwd_reset_token"] = raw_token
                    tpl_vars["submode"] = "reset"
                    flash("Entrez votre nouveau mot de passe ci-dessous.", "success")
                else:
                    flash("Lien envoyé si l'email existe.", "success")
            else:
                flash(resp.get("message", "Erreur.") if resp else "Erreur.", "danger")

        # ── RESET MOT DE PASSE ─────────────────────────────────────────────
        elif submode == "reset":
            # Token lu depuis la session (jamais depuis le formulaire HTML)
            token    = session.get("_pwd_reset_token", "")
            new_pass = request.form.get("new_password", "")
            if not token:
                flash("Session expirée. Recommencez la demande de réinitialisation.", "danger")
                tpl_vars["submode"] = "forgot"
                return render_template("login.html", **tpl_vars)
            if len(new_pass) < 6:
                tpl_vars["submode"] = "reset"
                flash("Mot de passe min. 6 caractères.", "danger")
            else:
                resp, err = ks_post("/api/auth/reset-password",
                                    {"token": token, "newPassword": new_pass})
                if err:
                    flash("KetaServer indisponible.", "danger")
                elif resp and resp.get("ok"):
                    session.pop("_pwd_reset_token", None)  # Consommer le token
                    flash("Mot de passe modifié. Connectez-vous.", "success")
                    tpl_vars["submode"] = "login"
                else:
                    tpl_vars["submode"] = "reset"
                    flash("Erreur lors de la réinitialisation. Recommencez.", "danger")

    return render_template("login.html", **tpl_vars)

@app.route("/logout")
def logout():
    try:
        session.clear()
    except Exception:
        pass
    response = redirect(url_for("login"))
    response.delete_cookie("session")
    return response

@app.route("/")
@login_required
def index():
    if session.get("router_id"):
        return redirect(url_for("dashboard"))
    return redirect(url_for("sessions_list"))

# ─── Tableau de bord ─────────────────────────────────────────────────────────

@app.route("/tableau-de-bord")
@login_required
@router_required
def dashboard():
    active_router_info = get_active_router() or {}
    relay_mode = bool(int(active_router_info.get("relay_enabled") or 0))
    relay_commands = db_mod.db_get_router_relay_commands(active_router_info.get("id", ""), limit=8) if relay_mode else []
    data = {}
    router_error = ""
    if relay_mode:
        try:
            data = _relay_database_dashboard_data(active_router_info)
        except Exception as e:
            router_error = str(e)
    else:
        api, err = get_api()
        if err:
            router_error = str(err)
            flash(err, "danger")
        else:
            try:
                res_rows = api.get_resource("/system/resource").get()
                ident_rows = api.get_resource("/system/identity").get()
                clock_rows = api.get_resource("/system/clock").get()
                rb_rows = api.get_resource("/system/routerboard").get()
                res   = res_rows[0] if res_rows else {}
                ident = ident_rows[0] if ident_rows else {}
                clock = clock_rows[0] if clock_rows else {}
                rb    = rb_rows[0] if rb_rows else {}
                hs_users    = resource_count(api, "/ip/hotspot/user")
                hs_active   = resource_count(api, "/ip/hotspot/active")
                hs_profiles = resource_count(api, "/ip/hotspot/user/profile")
                hs_list     = api.get_resource("/ip/hotspot").get()

                total_mem  = int(res.get("total-memory", 0))
                free_mem   = int(res.get("free-memory", 0))
                total_hdd  = int(res.get("total-hdd-space", 0))
                free_hdd   = int(res.get("free-hdd-space", 0))
                mem_used   = total_mem - free_mem
                mem_pct    = round(mem_used / total_mem * 100) if total_mem else 0

                router = get_active_router() or {}
                data = {
                    "identity":     ident.get("name", "MikroTik"),
                    "board":        rb.get("model", res.get("board-name", "?")),
                    "version":      res.get("version", "?"),
                    "uptime":       res.get("uptime", "?"),
                    "cpu_load":     res.get("cpu-load", "0"),
                    "total_mem":    mk.format_bytes(total_mem),
                    "free_mem":     mk.format_bytes(free_mem),
                    "mem_pct":      mem_pct,
                    "total_hdd":    mk.format_bytes(total_hdd),
                    "free_hdd":     mk.format_bytes(free_hdd),
                    "time":         clock.get("time", ""),
                    "date":         clock.get("date", ""),
                    "hs_users":     hs_users,
                    "hs_active":    hs_active,
                    "hs_profiles":  hs_profiles,
                    "hs_servers":   [h.get("name", "") for h in hs_list],
                    "router_host":  router.get("host", ""),
                    "router_port":  str(router.get("port", "8728")),
                }
            except Exception as e:
                router_error = str(e)
                _flash_err("Erreur de communication MikroTik.", e)
    return render_template("dashboard.html", data=data, router_error=router_error, relay_mode=relay_mode, relay_commands=relay_commands)

# ─── Hotspot : Utilisateurs ──────────────────────────────────────────────────

@app.route("/reseau/clients")
@app.route("/hotspot/utilisateurs", endpoint="hotspot_users")
@login_required
@router_required
def reseau_clients():
    api, err = get_api()
    users, profiles, servers = [], [], []
    if err:
        flash(err, "danger")
    else:
        try:
            router_id_c = session.get("router_id", "")
            prof_filter = request.args.get("profil", "tous")
            comm_filter = request.args.get("commentaire", "")
            exp_filter  = request.args.get("expire", "")
            profiles = api.get_resource("/ip/hotspot/user/profile").get()
            servers  = api.get_resource("/ip/hotspot").get()
            if getattr(api, "is_relay_snapshot", False):
                # Relay : lire TOUS les tickets depuis ticket_pricing + hotspot_profile_metadata
                conn_c = db_mod.get_conn()
                if prof_filter and prof_filter != "tous":
                    rows_c = conn_c.execute(
                        "SELECT tp.user, tp.password, tp.profil, hp.time_limit"
                        " FROM ticket_pricing tp"
                        " LEFT JOIN hotspot_profile_metadata hp"
                        "   ON hp.router_id=tp.router_id AND hp.profile_name=tp.profil"
                        " WHERE tp.router_id=? AND tp.profil=? ORDER BY tp.user",
                        (router_id_c, prof_filter)
                    ).fetchall()
                else:
                    rows_c = conn_c.execute(
                        "SELECT tp.user, tp.password, tp.profil, hp.time_limit"
                        " FROM ticket_pricing tp"
                        " LEFT JOIN hotspot_profile_metadata hp"
                        "   ON hp.router_id=tp.router_id AND hp.profile_name=tp.profil"
                        " WHERE tp.router_id=? ORDER BY tp.user",
                        (router_id_c,)
                    ).fetchall()
                # Lire le snapshot pour les infos disabled/comment (100 max, best effort)
                snap_users = {
                    str(u.get("name") or "").strip(): u
                    for u in _relay_snapshot_rows_from_db(router_id_c, "/ip/hotspot/user")
                    if str(u.get("name") or "").strip()
                }
                users = []
                for r in rows_c:
                    uname = str(r[0] or "").strip()
                    profil = str(r[2] or "default").strip()
                    tl = str(r[3] or "").strip()
                    snap = snap_users.get(uname, {})
                    limit_uptime = coerce_ticket_time_limit_router(
                        tl or _infer_time_limit_from_profile_name(profil),
                        empty="0", prefer_legacy_routeros=False
                    ) or "0"
                    users.append({
                        "name": uname,
                        "password": str(r[1] or ""),
                        "profile": profil,
                        "limit-uptime": limit_uptime,
                        "disabled": snap.get("disabled", "no"),
                        "comment": snap.get("comment", ""),
                    })
            elif comm_filter:
                users = api.get_resource("/ip/hotspot/user").get(**{"comment": comm_filter})
            elif exp_filter:
                users = api.get_resource("/ip/hotspot/user").get(**{"limit-uptime": "1s"})
            elif prof_filter != "tous":
                users = api.get_resource("/ip/hotspot/user").get(**{"profile": prof_filter})
            else:
                users = api.get_resource("/ip/hotspot/user").get()

            active_by_user = {}
            for active in find_matching_hotspot_active_rows(api):
                username = str(active.get("user") or "").strip()
                if username:
                    active_by_user.setdefault(username, []).append(active)

            normalized_users = []
            for user in users:
                row = dict(user)
                username = str(row.get("name") or "").strip()
                row["id"] = router_action_ref(row, "name")
                row["limit-uptime"] = normalize_ticket_time_limit(row.get("limit-uptime")) or "0"
                is_disabled = str(row.get("disabled", "no")).strip().lower() == "yes"
                active_rows = active_by_user.get(username, [])
                row["_active_sessions"] = len(active_rows)
                row["_is_connected"] = bool(active_rows)
                if is_disabled:
                    row["_live_state"] = "disabled"
                    row["_live_state_label"] = "Desactive"
                    row["_live_state_badge"] = "badge-red"
                elif active_rows:
                    row["_live_state"] = "connected"
                    row["_live_state_label"] = "Connecte"
                    row["_live_state_badge"] = "badge-green"
                else:
                    row["_live_state"] = "offline"
                    row["_live_state_label"] = "Hors ligne"
                    row["_live_state_badge"] = "badge-orange"
                normalized_users.append(row)
            users = normalized_users
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("reseau/clients.html",
        users=users, profiles=profiles, servers=servers,
        prof_filter=request.args.get("profil","tous"))

@app.route("/reseau/clients/ajouter", methods=["GET", "POST"])
@app.route("/hotspot/utilisateurs/ajouter", methods=["GET", "POST"], endpoint="hotspot_add_user")
@login_required
@router_required
def reseau_ajouter_client():
    api, err = get_api()
    profiles, servers = [], []
    router_id = session.get("router_id", "")
    if err:
        flash(err, "danger")
        return redirect(url_for("reseau_clients"))
    try:
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        servers  = api.get_resource("/ip/hotspot").get()
    except Exception as e:
        _flash_err("Une erreur est survenue.", e)

    if request.method == "POST":
        try:
            name    = request.form["name"].strip()
            passwd  = request.form.get("password", name).strip() or name
            profile = (request.form.get("profile", "default") or "default").strip() or "default"
            server  = (request.form.get("server", "") or "").strip()
            tlimit  = resolve_ticket_time_limit(router_id, profile, request.form.get("time_limit", ""))
            dlimit  = (request.form.get("data_limit", "0") or "0").strip() or "0"
            comment = request.form.get("comment", "")
            mode    = "vc-" if name == passwd else "up-"

            ensure_ticket_runtime_support(api, profile)

            params = {
                "name": name, "password": passwd, "profile": profile,
                "disabled": "no", "limit-uptime": tlimit or "0",
                "limit-bytes-total": str(int(dlimit) * 1048576) if dlimit != "0" else "0",
                "comment": build_hotspot_user_comment(comment, mode),
            }
            if server:
                params["server"] = server
            api.get_resource("/ip/hotspot/user").add(**params)
            # Enregistrer immédiatement dans ticket_pricing + ventes (relay ou direct)
            try:
                profiles_meta = get_hotspot_profile_metadata_map(router_id)
                meta = profiles_meta.get(profile, {})
                db_mod.db_batch_upsert_ticket_pricing([{
                    "router_id": router_id,
                    "user": name,
                    "password": passwd,
                    "prix": float(meta.get("price") or 0),
                    "devise": meta.get("currency") or "FCFA",
                    "profil": profile,
                    "reseau": server or "",
                }])
                db_mod.db_backfill_ventes_from_ticket_pricing(router_id)
            except Exception:
                pass
            relay_note = " Les tickets seront actifs sur le routeur dans ~30 secondes (mode relais)." if getattr(api, "is_relay_snapshot", False) else ""
            flash(f'Client "{name}" cree.{relay_note}', "success")
            return redirect(url_for("reseau_clients"))
        except ValueError as e:
            flash(str(e), "warning")
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("reseau/ajouter_client.html", profiles=profiles, servers=servers)

@app.route("/hotspot/utilisateurs/modifier/<uid>", methods=["GET", "POST"])
@app.route("/reseau/clients/modifier/<uid>", methods=["GET", "POST"], endpoint="reseau_modifier_client")
@login_required
@router_required
def hotspot_edit_user(uid):
    api, err = get_api()
    if err:
        flash(err, "danger")
        return redirect(url_for("hotspot_users"))
    try:
        users    = api.get_resource("/ip/hotspot/user").get(id=uid)
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        servers  = api.get_resource("/ip/hotspot").get()
        user = users[0] if users else {}
        if user:
            user["limit-uptime"] = normalize_ticket_time_limit(user.get("limit-uptime")) or "0"
    except Exception as e:
        _flash_err("Une erreur est survenue.", e)
        return redirect(url_for("hotspot_users"))

    if request.method == "POST":
        try:
            name     = request.form["name"]
            password = request.form.get("password", "") or name
            profile  = request.form.get("profile", "default")
            comment  = request.form.get("comment", "")
            server   = (request.form.get("server", "") or "").strip()
            router_id = session.get("router_id", "")

            # Normaliser la limite de temps (accepte "1h30m", "3600s", "0", etc.)
            time_limit_raw = request.form.get("time_limit", "0") or "0"
            time_limit = coerce_ticket_time_limit_router(time_limit_raw, empty="0", prefer_legacy_routeros=False) or "0"

            # Convertir Mo → octets (comme à l'ajout)
            data_limit_mo = request.form.get("data_limit", "0") or "0"
            try:
                dl_val = float(data_limit_mo)
                data_limit_bytes = str(int(dl_val * 1024 * 1024)) if dl_val > 0 else "0"
            except (ValueError, TypeError):
                data_limit_bytes = "0"

            # Préserver le préfixe de commentaire interne
            existing_comment = str(user.get("comment", "") or "")
            if existing_comment.startswith("vc-") or existing_comment.startswith("up-"):
                mode = existing_comment[:3]
            else:
                mode = "up-"
            new_comment = build_hotspot_user_comment(comment, mode)

            params = {
                "id":              uid,
                "name":            name,
                "password":        password,
                "profile":         profile,
                "comment":         new_comment,
                "limit-uptime":    time_limit,
                "limit-bytes-total": data_limit_bytes,
            }
            if server:
                params["server"] = server
            api.get_resource("/ip/hotspot/user").set(**params)
            flash("Utilisateur modifié.", "success")
            return redirect(url_for("reseau_clients"))
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("reseau/modifier_client.html", user=user, profiles=profiles, servers=servers)

@app.route("/hotspot/utilisateurs/supprimer", methods=["POST"])
@app.route("/reseau/clients/supprimer", methods=["POST"], endpoint="reseau_supprimer_client")
@login_required
@router_required
def hotspot_delete_user():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        payload = request_payload()
        uid = (payload.get("id") or "").strip()
        username_payload = str(payload.get("name") or payload.get("user") or "").strip()
        if not uid and username_payload:
            uid = username_payload
        if not uid and not username_payload:
            return jsonify({"ok": False, "msg": "Identifiant utilisateur introuvable."}), 400
        user_resource = api.get_resource("/ip/hotspot/user")
        users = _resource_rows_by_id_or_name(user_resource, item_id=uid, name=username_payload)
        username = str(users[0].get("name") or "") if users else ""
        if not username and not _is_real_router_item_id(uid):
            username = uid
        active_rows = find_matching_hotspot_active_rows(api, usernames=[username])
        usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(active_rows)
        if not router_resource_remove_by_id_or_name(api, "/ip/hotspot/user", item_id=uid, name=username):
            return jsonify({"ok": False, "msg": "Utilisateur hotspot introuvable sur le routeur."}), 404
        disconnected = disconnect_hotspot_entities(
            api,
            usernames=usernames or [username],
            addresses=addresses,
            mac_addresses=mac_addresses,
            active_ids=active_ids,
        )
        try:
            if username:
                db_mod.db_delete_ticket_pricing(session.get("router_id", ""), [username])
        except Exception:
            pass
        return jsonify({"ok": True, "disconnected": disconnected})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/hotspot/utilisateurs/basculer", methods=["POST"])
@app.route("/reseau/clients/basculer", methods=["POST"], endpoint="reseau_basculer_client")
@login_required
@router_required
def hotspot_toggle_user():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        payload = request_payload()
        uid = (payload.get("id") or "").strip()
        username_payload = str(payload.get("name") or payload.get("user") or "").strip()
        if not uid and username_payload:
            uid = username_payload
        disabled = str(payload.get("disabled", "yes")).strip().lower() or "yes"
        if not uid and not username_payload:
            return jsonify({"ok": False, "msg": "Identifiant utilisateur introuvable."}), 400

        user_resource = api.get_resource("/ip/hotspot/user")
        users = _resource_rows_by_id_or_name(user_resource, item_id=uid, name=username_payload)
        if not users:
            return jsonify({"ok": False, "msg": "Utilisateur hotspot introuvable sur le routeur."}), 404

        username = str(users[0].get("name") or "").strip()
        active_rows = find_matching_hotspot_active_rows(api, usernames=[username])
        usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(active_rows)

        router_resource_set_by_id_or_name(api, "/ip/hotspot/user", {"disabled": disabled}, item_id=uid, name=username)

        disconnected = {"active_sessions": 0, "cookies": 0, "hosts": 0}
        if disabled == "yes":
            remaining_active = active_rows
            for _ in range(3):
                batch = disconnect_hotspot_entities(
                    api,
                    usernames=usernames or [username],
                    addresses=addresses,
                    mac_addresses=mac_addresses,
                    active_ids=active_ids,
                )
                for key, value in batch.items():
                    disconnected[key] += int(value or 0)

                remaining_active = find_matching_hotspot_active_rows(
                    api,
                    usernames=usernames or [username],
                    addresses=addresses,
                    mac_addresses=mac_addresses,
                )
                if not remaining_active:
                    return jsonify({
                        "ok": True,
                        "msg": "Utilisateur desactive et acces Internet coupe.",
                        "disconnected": disconnected,
                    })

                usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(remaining_active)
                time.sleep(0.2)

            return jsonify({
                "ok": False,
                "msg": "Utilisateur desactive, mais la session Internet est encore active sur le routeur.",
                "disconnected": disconnected,
            }), 409

        return jsonify({
            "ok": True,
            "msg": "Utilisateur active. Il peut se reconnecter.",
            "disconnected": disconnected,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/hotspot/utilisateurs/reinitialiser", methods=["POST"])
@login_required
@router_required
def hotspot_reset_user():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        payload = request_payload()
        uid = (payload.get("id") or "").strip()
        if not uid:
            return jsonify({"ok": False, "msg": "Identifiant utilisateur introuvable."}), 400

        users = api.get_resource("/ip/hotspot/user").get(id=uid)
        if not users:
            return jsonify({"ok": False, "msg": "Utilisateur hotspot introuvable sur le routeur."}), 404

        user_row = users[0]
        username = str(user_row.get("name") or "").strip()
        locked_mac = str(user_row.get("mac-address") or "").strip()
        active_rows = find_matching_hotspot_active_rows(
            api,
            usernames=[username],
            mac_addresses=[locked_mac] if locked_mac else None,
        )
        usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(active_rows)
        disconnected = disconnect_hotspot_entities(
            api,
            usernames=usernames or [username],
            addresses=addresses,
            mac_addresses=mac_addresses or ([locked_mac] if locked_mac else []),
            active_ids=active_ids,
        )

        clean_comment = strip_ticket_runtime_comment(user_row.get("comment", ""))
        api.get_resource("/ip/hotspot/user").set(
            id=uid,
            disabled="no",
            **{
                "uptime": "0s",
                "bytes-in": "0",
                "bytes-out": "0",
                "mac-address": "00:00:00:00:00:00",
                "comment": clean_comment,
            },
        )
        return jsonify({
            "ok": True,
            "msg": "Ticket reinitialise. Il sera relie au premier appareil qui se reconnecte.",
            "disconnected": disconnected,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Hotspot : Generer utilisateurs ──────────────────────────────────────────

@app.route("/hotspot/generer", methods=["GET", "POST"])
@app.route("/reseau/clients/creer-comptes", methods=["GET", "POST"], endpoint="reseau_creer_comptes")
@login_required
@router_required
def hotspot_generate():
    profiles, servers = [], []
    generated = []
    router_id = session.get("router_id", "")
    selected_profile = (request.values.get("profile", "") or "").strip()
    api = None
    err = None
    skip_profile_load = False
    # Charger les métadonnées (prix) de chaque profil depuis SQLite
    profiles_meta = get_hotspot_profile_metadata_map(router_id)

    if request.method == "POST":
        try:
            qty          = safe_int(request.form.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
            profile      = (request.form.get("profile", "default") or "default").strip() or "default"
            selected_profile = profile
            server       = (request.form.get("server", "") or "").strip()
            mode          = request.form.get("mode", "aleatoire")
            password_mode = request.form.get("password_mode", "identique")
            prefix        = (request.form.get("prefix", "") or "").strip()
            length        = safe_int(request.form.get("length", 8), default=8, min_val=4, max_val=32)
            comment      = request.form.get("comment", "")
            network_name = (request.form.get("network_name", "") or "").strip()
            data_limit   = (request.form.get("data_limit", "0") or "0").strip()
            time_limit_override = (request.form.get("time_limit_override", "") or "").strip()

            ticket_time_limit = resolve_ticket_time_limit(router_id, profile, time_limit_override) or "0"
            ticket_time_limit_label = resolve_ticket_time_limit_display(router_id, profile, time_limit_override) or "0"

            # ensure_ticket_runtime_support : exécuter une seule fois par session router
            _erts_key = f"erts_done_{router_id}"
            if not session.get(_erts_key):
                try:
                    ensure_ticket_runtime_support(api, profile)
                    session[_erts_key] = True
                except Exception:
                    pass

            meta               = profiles_meta.get(profile, {})
            price_from_form    = (request.form.get("price_input", "0") or "0").strip()
            currency_from_form = (request.form.get("currency_input", "") or "").strip()
            try:
                price_from_form_f = float(price_from_form) if price_from_form else 0.0
            except (ValueError, TypeError):
                price_from_form_f = 0.0
            if price_from_form_f > 0:
                price    = price_from_form
                currency = currency_from_form or meta.get("currency", "FCFA") or "FCFA"
                try:
                    db_mod.db_upsert_hotspot_profile_metadata(
                        router_id, profile,
                        price=price, currency=currency,
                        expire_mode=meta.get("expire_mode", "none"),
                        lock_user=meta.get("lock_user", "no"),
                        time_limit=meta.get("time_limit", "0"),
                    )
                except Exception:
                    pass
            else:
                price    = meta.get("price", "0") or "0"
                currency = currency_from_form or meta.get("currency", "FCFA") or "FCFA"

            if mode == "chiffres":
                charset = string.digits
            elif mode == "lettres":
                charset = string.ascii_lowercase
            else:
                charset = string.ascii_lowercase + string.digits
            existing_names = set()

            now_dt   = datetime.now()
            date_str = now_dt.strftime("%Y-%m-%d")

            hotspot_resource = api.get_resource("/ip/hotspot/user")
            pricing_batch = []
            gen_errors = []
            attempts = 0
            max_attempts = max(qty * 5, qty + 50)
            while len(generated) < qty and attempts < max_attempts:
                attempts += 1
                try:
                    name = _next_unique_ticket_name(existing_names, charset, length, prefix)
                except ValueError as ex:
                    gen_errors.append(str(ex))
                    break
                if password_mode == "different":
                    password = "".join(random.choices(charset, k=length))
                else:
                    password = name
                params = {
                    "name": name, "password": password, "profile": profile,
                    "disabled": "no", "comment": build_hotspot_user_comment(comment, "vc-"),
                    "limit-uptime": ticket_time_limit,
                }
                if data_limit and data_limit != "0":
                    params["limit-bytes-total"] = str(int(float(data_limit) * 1024 * 1024))
                if server:
                    params["server"] = server
                try:
                    _add_or_repair_hotspot_ticket(api, hotspot_resource, params)
                    generated.append({
                        "name":       name,
                        "password":   password,
                        "profile":    profile,
                        "price":      price,
                        "currency":   currency,
                        "network":    network_name,
                        "date":       date_str,
                        "data_limit": data_limit,
                        "time_limit": ticket_time_limit_label,
                    })
                    pricing_batch.append({
                        "router_id": router_id,
                        "user":      name,
                        "password":  password,
                        "prix":      float(price) if price and price != "0" else 0.0,
                        "devise":    currency,
                        "profil":    profile,
                        "reseau":    network_name,
                    })
                except Exception as ex:
                    gen_errors.append(str(ex))
                    if _looks_like_duplicate_ticket_error(ex):
                        continue
                    break
            if pricing_batch:
                db_mod.db_batch_upsert_ticket_pricing(pricing_batch)
                try:
                    _pf = float(price) if price else 0.0
                except (ValueError, TypeError):
                    _pf = 0.0
                if _pf > 0:
                    try:
                        _conn = db_mod.get_conn()
                        _conn.execute(
                            "UPDATE ticket_pricing SET prix=?, devise=? WHERE router_id=? AND profil=? AND (prix IS NULL OR prix<=0)",
                            (_pf, currency, router_id, profile)
                        )
                        _conn.commit()
                        _backfill_ventes_prix_zero(router_id, _conn)
                    except Exception:
                        pass
                try:
                    db_mod.db_backfill_ventes_from_ticket_pricing(router_id)
                except Exception:
                    pass

            if len(generated) == qty:
                flash(f"{len(generated)} ticket(s) crees.", "success")
            else:
                detail = gen_errors[-1] if gen_errors else "quantite partielle"
                flash(f"{len(generated)}/{qty} ticket(s) crees. {detail}", "warning")
        except ValueError as e:
            flash(str(e), "warning")
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)

    if not selected_profile and profiles:
        first_profile = profiles[0] or {}
        selected_profile = str(first_profile.get("name", "") if isinstance(first_profile, dict) else "")

    return render_template("reseau/creer_comptes.html",
        profiles=profiles, servers=servers, generated=generated,
        profiles_meta=profiles_meta, selected_profile=selected_profile)

# ─── Hotspot : Profils ───────────────────────────────────────────────────────

def hotspot_generate_safe():
    profiles, servers = [], []
    generated = []
    router_id = session.get("router_id", "")
    selected_profile = (request.values.get("profile", "") or "").strip()
    profiles_meta = get_hotspot_profile_metadata_map(router_id)
    api = None
    err = None
    skip_profile_load = False

    if request.method == "POST":
        try:
            qty = safe_int(request.form.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
            profile = (request.form.get("profile", "default") or "default").strip() or "default"
            selected_profile = profile
            server = (request.form.get("server", "") or "").strip()
            mode = request.form.get("mode", "aleatoire")
            password_mode = request.form.get("password_mode", "identique")
            prefix = (request.form.get("prefix", "") or "").strip()
            length = safe_int(request.form.get("length", 8), default=8, min_val=4, max_val=32)
            comment = request.form.get("comment", "")
            network_name = (request.form.get("network_name", "") or "").strip()
            data_limit = (request.form.get("data_limit", "0") or "0").strip()
            time_limit_override = (request.form.get("time_limit_override", "") or "").strip()

            ticket_time_limit = resolve_ticket_time_limit(router_id, profile, time_limit_override) or "0"
            ticket_time_limit_label = resolve_ticket_time_limit_display(router_id, profile, time_limit_override) or "0"
            meta = profiles_meta.get(profile, {})
            price = meta.get("price", "0") or "0"
            currency = meta.get("currency", "FCFA") or "FCFA"

            with TicketGenerationJob(router_id, qty, profile, source="web") as job:
                api, err = get_api()
                if err:
                    raise RuntimeError(err)

                _erts_key = f"erts_done_{router_id}"
                if not session.get(_erts_key):
                    try:
                        ensure_ticket_runtime_support(api, profile)
                        session[_erts_key] = True
                    except Exception:
                        pass

                generated, gen_errors = create_hotspot_ticket_batch(
                    api, router_id, qty, profile,
                    server=server,
                    mode=mode,
                    length=length,
                    prefix=prefix,
                    password_mode=password_mode,
                    comment=comment,
                    network_name=network_name,
                    data_limit=data_limit,
                    price=price,
                    currency=currency,
                    ticket_time_limit=ticket_time_limit,
                    ticket_time_limit_label=ticket_time_limit_label,
                    job=job,
                    source="web",
                )

            relay_note = " Ils seront actifs sur le routeur dans ~30 secondes (mode relais)." if getattr(api, "is_relay_snapshot", False) else ""
            if len(generated) == qty:
                flash(f"{len(generated)} ticket(s) crees.{relay_note}", "success")
            else:
                detail = gen_errors[-1] if gen_errors else "quantite partielle"
                flash(f"{len(generated)}/{qty} ticket(s) crees. {detail}{relay_note}", "warning")
        except TicketGenerationBusyError as e:
            skip_profile_load = True
            flash(str(e), "warning")
        except ValueError as e:
            flash(str(e), "warning")
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)

    if not skip_profile_load:
        if api is None:
            api, err = get_api()
        if err:
            flash(err, "danger")
        else:
            try:
                profiles = api.get_resource("/ip/hotspot/user/profile").get()
                servers = api.get_resource("/ip/hotspot").get()
            except Exception as e:
                _flash_err("Une erreur est survenue.", e)

    if not selected_profile and profiles:
        first_profile = profiles[0] or {}
        selected_profile = str(first_profile.get("name", "") if isinstance(first_profile, dict) else "")

    return render_template(
        "reseau/creer_comptes.html",
        profiles=profiles,
        servers=servers,
        generated=generated,
        profiles_meta=profiles_meta,
        selected_profile=selected_profile,
    )


app.view_functions["hotspot_generate"] = hotspot_generate_safe
app.view_functions["reseau_creer_comptes"] = hotspot_generate_safe


@app.route("/hotspot/profils")
@app.route("/reseau/profils", endpoint="reseau_profils")
@login_required
@router_required
def hotspot_profiles():
    api, err = get_api()
    profiles = []
    if err:
        flash(err, "danger")
    else:
        try:
            router_id = session.get("router_id", "")
            metadata_map = get_hotspot_profile_metadata_map(router_id)
            profiles = [
                normalize_hotspot_profile(
                    profile,
                    metadata_map.get(str(profile.get("name") or "").strip())
                )
                for profile in api.get_resource("/ip/hotspot/user/profile").get()
            ]
            for profile in profiles:
                profile["id"] = router_action_ref(profile, "name")
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("hotspot/profiles.html", profiles=profiles)

@app.route("/hotspot/profils/ajouter", methods=["GET", "POST"])
@app.route("/reseau/profils/ajouter", methods=["GET", "POST"], endpoint="reseau_ajouter_profil")
@login_required
@router_required
def hotspot_add_profile():
    api, err = get_api()
    pools = []
    router_id = session.get("router_id", "")
    if err:
        flash(err, "danger")
        return redirect(url_for("hotspot_profiles"))
    try:
        pools = api.get_resource("/ip/pool").get()
    except Exception:
        pass

    if request.method == "POST":
        try:
            name         = request.form["name"].replace(" ", "-")
            shared_users = "1"
            rate_limit   = request.form.get("rate_limit", "")
            expire_mode  = request.form.get("expire_behavior") or request.form.get("expire_mode", "none")
            addr_pool    = request.form.get("addr_pool", "")
            lock_user    = "yes"
            time_limit   = coerce_ticket_time_limit_user(request.form.get("time_limit", ""), empty="0", prefer_legacy_routeros=False) or "0"
            price        = request.form.get("price", "0")
            currency     = request.form.get("currency", "FCFA")
            router_params = {
                "name": name,
                "shared-users": shared_users,
            }
            if rate_limit:
                router_params["rate-limit"] = rate_limit
            if addr_pool:
                router_params["address-pool"] = addr_pool

            profile_resource = api.get_resource("/ip/hotspot/user/profile")
            profile_resource.add(**router_params)

            metadata_warning = None
            runtime_warning = None
            try:
                db_mod.db_upsert_hotspot_profile_metadata(
                    router_id,
                    name,
                    price=price,
                    currency=currency,
                    expire_mode=expire_mode,
                    lock_user=lock_user,
                    time_limit=time_limit,
                )
            except Exception as meta_exc:
                metadata_warning = str(meta_exc)

            try:
                ensure_ticket_runtime_support(api, name)
            except Exception as runtime_exc:
                runtime_warning = str(runtime_exc)

            flash(f'Profil "{name}" cree. Duree par defaut: {time_limit or "0"}.', "success")
            if metadata_warning:
                flash(
                    "Profil cree, mais les options KetaMon locales n'ont pas pu etre sauvegardees : "
                    f"{metadata_warning}",
                    "warning",
                )
            if runtime_warning:
                flash(
                    "Profil cree, mais le verrou 1 ticket = 1 appareil n'a pas pu etre installe sur le routeur : "
                    f"{runtime_warning}",
                    "warning",
                )
            return redirect(url_for("hotspot_profiles"))
        except ValueError as e:
            flash(str(e), "warning")
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)

    return render_template("hotspot/add_profile.html", pools=pools)

@app.route("/hotspot/profils/supprimer", methods=["POST"])
@app.route("/reseau/profils/modifier-meta", methods=["POST"], endpoint="reseau_modifier_profil_meta")
@login_required
@router_required
def hotspot_update_profile_meta():
    """Met à jour les métadonnées KetaMon d'un profil (prix, devise, durée) sans toucher MikroTik."""
    router_id = session.get("router_id", "")
    payload   = request_payload()
    name      = str(payload.get("name", "")).strip()
    price     = str(payload.get("price", "0")).strip()
    currency  = str(payload.get("currency", "FCFA")).strip()
    time_limit = coerce_ticket_time_limit_user(payload.get("time_limit", "0"), empty="0", prefer_legacy_routeros=False) or "0"
    expire_mode= str(payload.get("expire_mode", "none")).strip()
    if not name:
        return jsonify({"ok": False, "msg": "Nom de profil manquant."})
    try:
        db_mod.db_upsert_hotspot_profile_metadata(
            router_id, name,
            price=price, currency=currency,
            expire_mode=expire_mode, lock_user="yes", time_limit=time_limit
        )
        return jsonify({"ok": True})
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/reseau/profils/supprimer", methods=["POST"], endpoint="reseau_supprimer_profil")
@login_required
@router_required
def hotspot_delete_profile():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        payload = request_payload()
        pid = (payload.get("id") or "").strip()
        profile_name_payload = str(payload.get("name") or payload.get("profile") or payload.get("nom") or "").strip()
        if not pid and profile_name_payload:
            pid = profile_name_payload
        if not pid and not profile_name_payload:
            return jsonify({"ok": False, "msg": "Identifiant profil introuvable."}), 400
        profile_resource = api.get_resource("/ip/hotspot/user/profile")
        existing = _resource_rows_by_id_or_name(profile_resource, item_id=pid, name=profile_name_payload)
        profile_name = str(existing[0].get("name") or "") if existing else ""
        if not profile_name and not _is_real_router_item_id(pid):
            profile_name = pid
        if not router_resource_remove_by_id_or_name(api, "/ip/hotspot/user/profile", item_id=pid, name=profile_name):
            return jsonify({"ok": False, "msg": "Profil hotspot introuvable sur le routeur."}), 404
        if profile_name:
            db_mod.db_delete_hotspot_profile_metadata(session.get("router_id", ""), profile_name)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Hotspot : Actifs ────────────────────────────────────────────────────────

@app.route("/hotspot/actifs")
@app.route("/reseau/sessions", endpoint="reseau_sessions")
@login_required
@router_required
def hotspot_active():
    api, err = get_api()
    actifs, servers = [], []
    if err:
        flash(err, "danger")
    else:
        try:
            server_filter = request.args.get("serveur", "")
            servers = api.get_resource("/ip/hotspot").get()
            if server_filter:
                actifs = api.get_resource("/ip/hotspot/active").get(**{"server": server_filter})
            else:
                actifs = api.get_resource("/ip/hotspot/active").get()
            stale_active = getattr(api, "stale_resources", {}).get("/ip/hotspot/active")
            if stale_active:
                age = stale_active.get("age")
                updated_at = stale_active.get("updated_at") or "jamais"
                detail = f" Dernier snapshot: {updated_at}."
                if age is not None:
                    detail = f" Dernier snapshot il y a {format_duration_compact(age)}."
                flash(
                    "Sessions actives non affichees car le relais MikroTik n'a pas envoye de donnees recentes."
                    + detail,
                    "warning",
                )
            users_map = {
                str(user.get("name") or "").strip(): dict(user)
                for user in api.get_resource("/ip/hotspot/user").get()
                if str(user.get("name") or "").strip()
            }
            # Enrichir avec expire_at et first_used_at
            router_id = session.get("router_id", "")
            _record_active_revenues_from_database(router_id, actifs)
            first_used_map = _build_first_used_map(router_id)
            users_map = _enrich_active_users_from_database(router_id, actifs, users_map)
            _cleanup_expired_active_from_database(api, router_id, actifs, first_used_map)
            _repair_active_ticket_epochs(
                api,
                router_id,
                active_rows=actifs,
                users_map=users_map,
                first_used_map=first_used_map,
            )
            actifs = normalize_active_sessions(api, actifs, users_map=users_map)
            for a in actifs:
                comment = a.get("user_comment", "")
                uname = str(a.get("user") or "").strip()
                fu = first_used_map.get(uname, "")
                if not fu:
                    uptime_sec = parse_routeros_duration(str(a.get("uptime", "") or ""))
                    if uptime_sec is not None and uptime_sec > 0:
                        fu_dt = datetime.now() - timedelta(seconds=uptime_sec)
                        fu = fu_dt.strftime("%Y-%m-%d %H:%M")
                a["first_used_at"] = fu
                a["expire_estimated"] = False
                # 1. Chercher epoch exact dans le commentaire
                expire_at = ""
                expire_dt = _extract_ketamon_expire_datetime(comment)
                if expire_dt:
                    expire_at = expire_dt.strftime("%d/%m/%Y %H:%M")
                # 2. Fallback : calculer depuis first_used_at + limit-uptime
                if not expire_at:
                    first_used_str = a.get("first_used_at", "")
                    dur_sec = parse_routeros_duration(a.get("limit-uptime", "0"))
                    if first_used_str and dur_sec and dur_sec > 0:
                        try:
                            fdt = datetime.strptime(first_used_str[:16], "%Y-%m-%d %H:%M")
                            expire_at = (fdt + timedelta(seconds=dur_sec)).strftime("%d/%m/%Y %H:%M")
                            a["expire_estimated"] = True
                        except Exception:
                            pass
                a["expire_at"] = expire_at
                # Toujours afficher le temps restant a partir de l'expiration absolue si connue.
                if expire_at:
                    try:
                        expire_dt = datetime.strptime(expire_at, "%d/%m/%Y %H:%M")
                        remaining = int((expire_dt - datetime.now()).total_seconds())
                        a["temps-restant"] = format_duration_compact(remaining) if remaining > 0 else "Expiré"
                    except Exception:
                        pass
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("hotspot/active.html", actifs=actifs, servers=servers,
        server_filter=request.args.get("serveur",""))

@app.route("/hotspot/scripts/reinstaller", methods=["POST"])
@login_required
def hotspot_reinstall_scripts():
    """Réinstalle les scripts MikroTik (expiration + login) sur les routeurs de l'utilisateur."""
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré."})
    ok_count = 0
    errors = []
    for router_info in routers:
        try:
            rhost = router_info.get("host","")
            api2, err2 = mk.safe_connect_router(router_info)
            if err2:
                errors.append(f"{rhost}: {err2}")
                continue
            ensure_ticket_runtime_support(api2)
            ok_count += 1
        except Exception as e:
            errors.append(f"{router_info.get('host','?')}: {e}")
    if ok_count:
        msg = f"Scripts mis à jour sur {ok_count} routeur(s)."
        if errors:
            msg += f" Erreurs: {'; '.join(errors)}"
        return jsonify({"ok": True, "msg": msg})
    return jsonify({"ok": False, "msg": "; ".join(errors) or "Echec."})


@app.route("/hotspot/actifs/supprimer", methods=["POST"])
@app.route("/reseau/sessions/supprimer", methods=["POST"], endpoint="reseau_supprimer_session")
@login_required
@router_required
def hotspot_remove_active():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        payload = request_payload()
        aid  = str(payload.get("id")   or "").strip()
        user = str(payload.get("user") or "").strip()
        mac  = str(payload.get("mac")  or "").strip()

        removed_total = 0
        active_resource = api.get_resource("/ip/hotspot/active")

        if aid:
            # Suppression directe par ID — pas besoin de charger toutes les sessions
            targets = [{"id": aid, "user": user, "mac": mac.lower(), "ip": ""}]
        else:
            # Filtre par user ou mac : charge toutes les sessions une seule fois
            all_active = active_resource.get()
            targets = []
            for a in all_active:
                row_id  = router_item_id(a)
                row_usr = str(a.get("user") or "").strip()
                row_mac = str(a.get("mac-address") or "").strip().lower()
                row_ip  = str(a.get("address") or "").strip()
                if (
                    (user and row_usr == user) or
                    (mac  and row_mac == mac.lower())
                ):
                    targets.append({"id": row_id, "user": row_usr, "mac": row_mac, "ip": row_ip})

        if not targets:
            return jsonify({"ok": False, "msg": "Session introuvable ou deja fermee."})

        last_err = ""
        for t in targets:
            # 1. Supprimer session active
            removed_this = False
            if t["id"]:
                try:
                    active_resource.remove(id=t["id"])
                    removed_this = True
                except Exception as e:
                    last_err = str(e)
            if removed_this:
                removed_total += 1
            # 2. Supprimer cookie (empêche reconnexion automatique)
            try:
                cookie_res = api.get_resource("/ip/hotspot/cookie")
                for c in cookie_res.get():
                    c_usr = str(c.get("user","")).strip()
                    c_mac = str(c.get("mac-address","")).strip().lower()
                    if (t["user"] and c_usr == t["user"]) or \
                       (t["mac"]  and c_mac == t["mac"]):
                        cid = c.get(".id") or c.get("id")
                        if cid:
                            try:
                                cookie_res.remove(id=cid)
                            except Exception:
                                pass
            except Exception:
                pass
            # 3. Supprimer hôte (force reconnexion via portail)
            try:
                host_res = api.get_resource("/ip/hotspot/host")
                for h in host_res.get():
                    h_ip  = str(h.get("address","")).strip()
                    h_mac = str(h.get("mac-address","")).strip().lower()
                    if (t["ip"]  and h_ip  == t["ip"]) or \
                       (t["mac"] and h_mac == t["mac"]):
                        hid = h.get(".id") or h.get("id")
                        if hid:
                            try:
                                host_res.remove(id=hid)
                            except Exception:
                                pass
            except Exception:
                pass

        if removed_total == 0:
            msg = last_err if last_err else "Session introuvable ou deja fermee."
            return jsonify({"ok": False, "msg": msg})
        return jsonify({"ok": True, "removed": removed_total})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Hotspot : Hotes ─────────────────────────────────────────────────────────

@app.route("/hotspot/hotes")
@app.route("/reseau/appareils", endpoint="reseau_appareils")
@login_required
@router_required
def hotspot_hosts():
    api, err = get_api()
    hosts = []
    if err:
        flash(err, "danger")
    else:
        try:
            hosts = api.get_resource("/ip/hotspot/host").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("hotspot/hosts.html", hosts=hosts)

@app.route("/hotspot/hotes/supprimer", methods=["POST"])
@app.route("/reseau/appareils/supprimer", methods=["POST"], endpoint="reseau_supprimer_appareil")
@login_required
@router_required
def hotspot_remove_host():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        hid = request.json.get("id")
        api.get_resource("/ip/hotspot/host").remove(id=hid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Hotspot : Liaisons IP ───────────────────────────────────────────────────

@app.route("/hotspot/liaisons-ip")
@app.route("/reseau/reservations-ip", endpoint="reseau_reservations_ip")
@login_required
@router_required
def hotspot_ip_bindings():
    api, err = get_api()
    bindings = []
    if err:
        flash(err, "danger")
    else:
        try:
            bindings = api.get_resource("/ip/hotspot/ip-binding").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("hotspot/ip_bindings.html", bindings=bindings)

@app.route("/hotspot/liaisons-ip/ajouter", methods=["POST"])
@app.route("/reseau/reservations-ip/ajouter", methods=["POST"], endpoint="reseau_ajouter_reservation")
@login_required
@router_required
def hotspot_add_binding():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        data = request.json
        params = {"type": data.get("type", "regular")}
        if data.get("mac"):
            params["mac-address"] = data["mac"]
        if data.get("address"):
            params["address"] = data["address"]
        if data.get("to_address"):
            params["to-address"] = data["to_address"]
        if data.get("server"):
            params["server"] = data["server"]
        api.get_resource("/ip/hotspot/ip-binding").add(**params)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/hotspot/liaisons-ip/supprimer", methods=["POST"])
@app.route("/reseau/reservations-ip/supprimer", methods=["POST"], endpoint="reseau_supprimer_reservation")
@login_required
@router_required
def hotspot_remove_binding():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        bid = request.json.get("id")
        api.get_resource("/ip/hotspot/ip-binding").remove(id=bid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/hotspot/liaisons-ip/basculer", methods=["POST"])
@app.route("/reseau/reservations-ip/basculer", methods=["POST"], endpoint="reseau_basculer_reservation")
@login_required
@router_required
def hotspot_toggle_binding():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        bid      = request.json.get("id")
        disabled = request.json.get("disabled", "yes")
        api.get_resource("/ip/hotspot/ip-binding").set(id=bid, disabled=disabled)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Hotspot : Cookies ───────────────────────────────────────────────────────

@app.route("/hotspot/cookies")
@app.route("/reseau/jetons", endpoint="reseau_jetons")
@login_required
@router_required
def hotspot_cookies():
    api, err = get_api()
    cookies = []
    if err:
        flash(err, "danger")
    else:
        try:
            cookies = api.get_resource("/ip/hotspot/cookie").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("hotspot/cookies.html", cookies=cookies)

@app.route("/hotspot/cookies/supprimer", methods=["POST"])
@app.route("/reseau/jetons/supprimer", methods=["POST"], endpoint="reseau_supprimer_jeton")
@login_required
@router_required
def hotspot_remove_cookie():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        cid = request.json.get("id")
        api.get_resource("/ip/hotspot/cookie").remove(id=cid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Impression Rapide ───────────────────────────────────────────────────────

@app.route("/impression-rapide")
@login_required
@router_required
def quick_print():
    api, err = get_api()
    quick_items, profiles, servers = [], [], []
    router_id = session.get("router_id", "")
    profiles_meta = {}
    if err:
        flash(err, "danger")
    else:
        try:
            scripts = api.get_resource("/system/script").get(**{"comment": "KetaMonQuickPrint"})
            for s in scripts:
                src = s.get("source", "")
                parts = src.split("#")
                quick_items.append({
                    "id":      s.get("id", ""),
                    "name":    s.get("name", ""),
                    "profile": parts[1] if len(parts) > 1 else "",
                    "server":  parts[2] if len(parts) > 2 else "",
                    "mode":    parts[3] if len(parts) > 3 else "",
                    "length":  parts[4] if len(parts) > 4 else "",
                    "prefix":  parts[5] if len(parts) > 5 else "",
                    "qty":     parts[6] if len(parts) > 6 else "1",
                    "price":   parts[7] if len(parts) > 7 else "0",
                    "network": parts[8] if len(parts) > 8 else "",
                })
            profiles = api.get_resource("/ip/hotspot/user/profile").get()
            servers  = api.get_resource("/ip/hotspot").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
    return render_template("quick_print.html", quick_items=quick_items,
                           profiles=profiles, servers=servers, profiles_meta=profiles_meta)


@app.route("/impression-rapide/generer", methods=["POST"], endpoint="quick_print_generer")
@login_required
@router_required
def quick_print_generer():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    data = request.get_json(silent=True) or {}
    script_id = data.get("id", "")
    try:
        scripts = api.get_resource("/system/script").get(id=script_id)
        if not scripts:
            return jsonify({"ok": False, "msg": "Modèle introuvable."})
        s = scripts[0]
        src = s.get("source", "")
        parts = src.split("#")
        profile = parts[1] if len(parts) > 1 else "default"
        server  = parts[2] if len(parts) > 2 else ""
        mode    = parts[3] if len(parts) > 3 else "aleatoire"
        length  = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 8
        prefix  = parts[5] if len(parts) > 5 else ""
        qty     = safe_int(parts[6] if len(parts) > 6 else 1, default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
        price   = parts[7] if len(parts) > 7 else "0"
        network = parts[8] if len(parts) > 8 else ""
    except Exception as e:
        return jsonify({"ok": False, "msg": f"Erreur lecture modèle: {e}"})
    router_id = session.get("router_id", "")
    if mode == "chiffres":
        charset = string.digits
    elif mode == "lettres":
        charset = string.ascii_lowercase
    else:
        charset = string.ascii_lowercase + string.digits
    try:
        ensure_ticket_runtime_support(api, profile)
    except Exception:
        pass
    ticket_time_limit = resolve_ticket_time_limit(router_id, profile, "") or "0"
    ticket_time_limit_label = get_profile_time_limit(router_id, profile) or "0"
    profiles_meta = get_hotspot_profile_metadata_map(router_id)
    meta = profiles_meta.get(profile, {})
    currency = meta.get("currency", "FCFA") or "FCFA"
    if not price or price == "0":
        price = meta.get("price", "0") or "0"
    date_str = datetime.now().strftime("%Y-%m-%d")
    generated = []
    pricing_batch = []
    hotspot_resource = api.get_resource("/ip/hotspot/user")
    existing_names = set()
    gen_errors = []
    attempts = 0
    max_attempts = max(qty * 5, qty + 50)
    while len(generated) < qty and attempts < max_attempts:
        attempts += 1
        try:
            name = _next_unique_ticket_name(existing_names, charset, length, prefix)
        except ValueError as ex:
            gen_errors.append(str(ex))
            break
        password = name
        params = {
            "name": name, "password": password, "profile": profile,
            "disabled": "no", "comment": "vc-",
            "limit-uptime": ticket_time_limit,
        }
        if server:
            params["server"] = server
        try:
            _add_or_repair_hotspot_ticket(api, hotspot_resource, params)
            generated.append({
                "name": name, "password": password, "profile": profile,
                "price": price, "currency": currency, "network": network,
                "date": date_str, "time_limit": ticket_time_limit_label,
            })
            pricing_batch.append({
                "router_id": router_id, "user": name,
                "password": password,
                "prix": float(price) if price and price != "0" else 0.0,
                "devise": currency, "profil": profile, "reseau": network,
            })
        except Exception as ex:
            gen_errors.append(str(ex))
            if _looks_like_duplicate_ticket_error(ex):
                continue
            break
    if pricing_batch:
        db_mod.db_batch_upsert_ticket_pricing(pricing_batch)
    return jsonify({
        "ok": len(generated) == qty,
        "tickets": generated,
        "count": len(generated),
        "requested": qty,
        "msg": "" if len(generated) == qty else (gen_errors[-1] if gen_errors else "Generation partielle"),
    })


def quick_print_generer_safe():
    router_id = session.get("router_id", "")
    data = request.get_json(silent=True) or {}
    script_id = data.get("id", "")
    try:
        with TicketGenerationJob(router_id, 0, source="quick-print") as job:
            api, err = get_api()
            if err:
                raise RuntimeError(err)

            scripts = api.get_resource("/system/script").get(id=script_id)
            if not scripts:
                return jsonify({"ok": False, "msg": "Modele introuvable."})

            src = scripts[0].get("source", "")
            parts = src.split("#")
            profile = parts[1] if len(parts) > 1 else "default"
            server = parts[2] if len(parts) > 2 else ""
            mode = parts[3] if len(parts) > 3 else "aleatoire"
            length = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 8
            prefix = parts[5] if len(parts) > 5 else ""
            qty = safe_int(parts[6] if len(parts) > 6 else 1, default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
            price = parts[7] if len(parts) > 7 else "0"
            network = parts[8] if len(parts) > 8 else ""
            job.requested = qty
            job.profile = profile
            job.progress(0)

            try:
                ensure_ticket_runtime_support(api, profile)
            except Exception:
                pass

            ticket_time_limit = resolve_ticket_time_limit(router_id, profile, "") or "0"
            ticket_time_limit_label = resolve_ticket_time_limit_display(router_id, profile, "") or "0"
            profiles_meta = get_hotspot_profile_metadata_map(router_id)
            meta = profiles_meta.get(profile, {})
            currency = meta.get("currency", "FCFA") or "FCFA"
            if not price or price == "0":
                price = meta.get("price", "0") or "0"

            generated, gen_errors = create_hotspot_ticket_batch(
                api, router_id, qty, profile,
                server=server,
                mode=mode,
                length=length,
                prefix=prefix,
                password_mode="identique",
                comment="",
                network_name=network,
                price=price,
                currency=currency,
                ticket_time_limit=ticket_time_limit,
                ticket_time_limit_label=ticket_time_limit_label,
                job=job,
                source="quick-print",
            )

        return jsonify({
            "ok": len(generated) == qty,
            "tickets": generated,
            "count": len(generated),
            "requested": qty,
            "msg": "" if len(generated) == qty else (gen_errors[-1] if gen_errors else "Generation partielle"),
        })
    except TicketGenerationBusyError as e:
        return jsonify({"ok": False, "msg": str(e), "busy": True}), 409
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


app.view_functions["quick_print_generer"] = quick_print_generer_safe


@app.route("/impression-rapide/creer", methods=["POST"], endpoint="quick_print_creer")
@login_required
@router_required
def quick_print_creer():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    data = request.get_json(silent=True) or {}
    name    = (data.get("name", "") or "").strip()
    profile = (data.get("profile", "default") or "default").strip()
    server  = (data.get("server", "") or "").strip()
    mode    = data.get("mode", "aleatoire")
    length  = safe_int(data.get("length", 8), default=8, min_val=4, max_val=32)
    prefix  = (data.get("prefix", "") or "").strip()
    qty     = safe_int(data.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
    price   = (data.get("price", "0") or "0").strip()
    network = (data.get("network", "") or "").strip()
    if not name:
        return jsonify({"ok": False, "msg": "Le nom est requis."})
    source = f"#{profile}#{server}#{mode}#{length}#{prefix}#{qty}#{price}#{network}"
    try:
        api.get_resource("/system/script").add(name=name, source=source, comment="KetaMonQuickPrint")
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/impression-rapide/supprimer", methods=["POST"], endpoint="quick_print_supprimer")
@login_required
@router_required
def quick_print_supprimer():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    data = request.get_json(silent=True) or {}
    sid = data.get("id", "")
    try:
        api.get_resource("/system/script").remove(id=sid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Bons de connexion ───────────────────────────────────────────────────────

@app.route("/bons")
@login_required
@router_required
def vouchers():
    api, err = get_api()
    profiles, vouchers_data = [], {}
    router_id = session.get("router_id", "")
    profiles_meta = {}
    if err:
        flash(err, "danger")
    else:
        try:
            profiles = api.get_resource("/ip/hotspot/user/profile").get()
        except Exception as e:
            _flash_err("Erreur lors du chargement des profils.", e)
        try:
            if getattr(api, "is_relay_snapshot", False):
                # Relay : lire TOUS les tickets depuis ticket_pricing (pas limité à 100)
                conn = db_mod.get_conn()
                rows = conn.execute(
                    "SELECT user, password, profil FROM ticket_pricing WHERE router_id=? ORDER BY user",
                    (router_id,)
                ).fetchall()
                all_users = [{"name": str(r[0] or ""), "password": str(r[1] or ""), "profile": str(r[2] or "default")} for r in rows]
            else:
                all_users = api.get_resource("/ip/hotspot/user").get()
            for u in all_users:
                pname = u.get("profile") or "default"
                vouchers_data.setdefault(pname, []).append(u)
        except Exception as e:
            _flash_err("Erreur lors du chargement des utilisateurs.", e)
        if not profiles and vouchers_data:
            profiles = [{"name": k} for k in vouchers_data]
        profiles_meta = _profile_metadata_map_for_display(router_id, profiles)
    return render_template("vouchers.html", profiles=profiles, vouchers_data=vouchers_data,
                           profiles_meta=profiles_meta)



# ─── Journaux ────────────────────────────────────────────────────────────────

@app.route("/bons/imprimer")
@login_required
@router_required
def vouchers_print_view():
    api, err = get_api()
    if err:
        flash(err, "danger")
        return redirect(url_for("vouchers"))

    router_id = session.get("router_id", "")
    router = get_active_router() or {}
    selected_profile = (request.args.get("profile", "all") or "all").strip()
    auto_print = str(request.args.get("print", "")).lower() in {"1", "true", "yes", "on"}
    try:
        profile_rows_for_meta = api.get_resource("/ip/hotspot/user/profile").get()
    except Exception:
        profile_rows_for_meta = []
    profiles_meta = _profile_metadata_map_for_display(router_id, profile_rows_for_meta)
    cards = []

    try:
        if getattr(api, "is_relay_snapshot", False):
            # Relay : lire TOUS les tickets depuis ticket_pricing (pas limité à 100)
            conn = db_mod.get_conn()
            rows = conn.execute(
                "SELECT user, password, profil FROM ticket_pricing WHERE router_id=? ORDER BY user",
                (router_id,)
            ).fetchall()
            all_users = [{"name": str(r[0] or ""), "password": str(r[1] or ""), "profile": str(r[2] or "default")} for r in rows]
        else:
            all_users = api.get_resource("/ip/hotspot/user").get()
    except Exception as e:
        _flash_err("Erreur lors du chargement des bons.", e)
        return redirect(url_for("vouchers"))

    for user_row in all_users:
        profile_name = str(user_row.get("profile") or "default")
        if selected_profile != "all" and profile_name != selected_profile:
            continue

        meta = profiles_meta.get(profile_name, {})
        duration = str(meta.get("time_limit") or "")
        price = str(meta.get("price") or "")
        currency = str(meta.get("currency") or "FCFA")
        parts = [profile_name]
        if duration and duration != "0":
            parts.append(duration)
        if price and price != "0":
            parts.append(f"{price} {currency}")

        cards.append({
            "num": len(cards) + 1,
            "code": str(user_row.get("name") or ""),
            "profile": profile_name,
            "info": " - ".join(parts),
        })

    title = "Tous les bons" if selected_profile == "all" else selected_profile
    wifi_name = str(router.get("wifi_name") or "").strip() or "WiFi"
    return render_template(
        "vouchers_print.html",
        title=title,
        cards=cards,
        wifi_name=wifi_name,
        printed_at=datetime.now().strftime("%d/%m/%Y %H:%M"),
        auto_print=auto_print,
    )


def _relay_logs_from_ventes(router_id, limit=300):
    """Construit un journal de connexions depuis la table ventes (mode relay)."""
    try:
        rows = db_mod.db_get_ventes(router_id)
    except Exception:
        rows = []
    logs = []
    for v in reversed(rows or []):
        user    = str(v.get("user")   or "").strip()
        profil  = str(v.get("profil") or "").strip()
        prix    = v.get("prix", 0)
        devise  = str(v.get("devise") or "FCFA").strip()
        reseau  = str(v.get("reseau") or "").strip()
        date_s  = str(v.get("date")   or "").strip()
        heure_s = str(v.get("heure")  or "").strip()[:5]
        parts = [f"{user} connecte"]
        if profil:
            parts.append(f"profil:{profil}")
        if prix and float(prix or 0) > 0:
            parts.append(f"{prix} {devise}")
        if reseau:
            parts.append(f"reseau:{reseau}")
        logs.append({
            "time":    heure_s,
            "topics":  "hotspot,info",
            "message": "  ".join(parts),
            "_date":   date_s,
        })
    return logs[:limit]


@app.route("/journaux/hotspot")
@login_required
@router_required
def log_hotspot():
    api, err = get_api()
    logs = []
    router_id = session.get("router_id", "")
    if err:
        flash(err, "danger")
    elif getattr(api, "is_relay_snapshot", False):
        logs = _relay_logs_from_ventes(router_id, limit=200)
    else:
        try:
            all_logs = api.get_resource("/log").get()
            logs = [
                l for l in all_logs
                if "hotspot" in l.get("topics", "")
                and not l.get("message", "").startswith("->:")
            ]
            logs = list(reversed(logs))[:200]
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("logs/hotspot_log.html", logs=logs)

@app.route("/journaux/utilisateurs")
@login_required
@router_required
def log_users():
    api, err = get_api()
    logs = []
    router_id = session.get("router_id", "")
    if err:
        flash(err, "danger")
    elif getattr(api, "is_relay_snapshot", False):
        logs = _relay_logs_from_ventes(router_id, limit=300)
    else:
        try:
            all_logs = api.get_resource("/log").get()
            relevant = ("account", "hotspot", "system", "wireless", "manager")
            logs = [
                l for l in all_logs
                if any(t in l.get("topics", "") for t in relevant)
                and not l.get("message", "").startswith("->:")
            ]
            logs = list(reversed(logs))[:300]
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("logs/user_log.html", logs=logs)

# ─── Baux DHCP ───────────────────────────────────────────────────────────────

@app.route("/baux-dhcp")
@login_required
@router_required
def dhcp_leases():
    api, err = get_api()
    leases = []
    if err:
        flash(err, "danger")
    else:
        try:
            leases = api.get_resource("/ip/dhcp-server/lease").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("dhcp.html", leases=leases)


@app.route("/baux-dhcp/liberer", methods=["POST"], endpoint="dhcp_liberer")
@login_required
@router_required
def dhcp_liberer():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    data = request.get_json(silent=True) or {}
    lid = data.get("id", "")
    try:
        api.get_resource("/ip/dhcp-server/lease").remove(id=lid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/baux-dhcp/rendre-statique", methods=["POST"], endpoint="dhcp_rendre_statique")
@login_required
@router_required
def dhcp_rendre_statique():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    data = request.get_json(silent=True) or {}
    lid = data.get("id", "")
    try:
        api.get_resource("/ip/dhcp-server/lease").call("make-static", {".id": lid})
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Moniteur Trafic ─────────────────────────────────────────────────────────

@app.route("/moniteur-trafic")
@login_required
@router_required
def traffic_monitor():
    api, err = get_api()
    interfaces = []
    is_relay = getattr(api, "is_relay_snapshot", False) if api else False
    relay_snap_age = None
    if err:
        flash(err, "danger")
    else:
        try:
            raw_ifaces = api.get_resource("/interface").get()
            # Normalisation : interface "running" = true si non désactivée OU a des compteurs > 0
            for iface in (raw_ifaces or []):
                run = str(iface.get("running") or "").strip().lower()
                dis = str(iface.get("disabled") or "").strip().lower()
                rx  = int(iface.get("rx-byte") or 0)
                tx  = int(iface.get("tx-byte") or 0)
                if run not in ("true", "yes") and (dis not in ("true", "yes") or rx > 0 or tx > 0):
                    iface["running"] = "true"
            interfaces = raw_ifaces or []
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)

    # Mettre l'interface hotspot en tête de liste (c'est là où passe le trafic clients)
    if interfaces:
        try:
            hotspot_iface = ""
            router_id = session.get("router_id", "")
            hs_rows = db_mod.db_get_router_relay_snapshot(router_id, "/ip/hotspot") if is_relay else []
            if hs_rows:
                hotspot_iface = str((hs_rows[0] if hs_rows else {}).get("interface") or "").strip()
            if not hotspot_iface:
                # Essai via API directe
                try:
                    hs = api.get_resource("/ip/hotspot").get()
                    hotspot_iface = str((hs[0] if hs else {}).get("interface") or "").strip()
                except Exception:
                    pass
            if hotspot_iface:
                interfaces = sorted(
                    interfaces,
                    key=lambda i: (0 if str(i.get("name") or "") == hotspot_iface else 1)
                )
        except Exception:
            pass

    if is_relay:
        try:
            router_id = session.get("router_id", "")
            conn = db_mod.get_conn()
            row = conn.execute(
                "SELECT updated_at FROM router_relay_snapshots WHERE router_id=? AND resource=? LIMIT 1",
                (router_id, "/interface")
            ).fetchone()
            if row and row["updated_at"]:
                dt = datetime.fromisoformat(str(row["updated_at"]).replace("Z", "+00:00")).replace(tzinfo=None)
                relay_snap_age = max(0, int((datetime.now() - dt).total_seconds()))
        except Exception:
            pass
    return render_template("traffic.html", interfaces=interfaces, is_relay=is_relay, relay_snap_age=relay_snap_age)

@app.route("/api/interfaces")
@login_required
@router_required
def api_interfaces():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "interfaces": []})
    try:
        ifaces = api.get_resource("/interface").get()
        result = []
        for i in ifaces:
            name = str(i.get("name", ""))
            if name:
                result.append({
                    "name": name,
                    "type": str(i.get("type", "")),
                    "running": str(i.get("running", "false")).lower() == "true",
                })
        return jsonify({"ok": True, "interfaces": result})
    except Exception as e:
        return jsonify({"ok": False, "interfaces": [], "msg": str(e)})

# Stockage du dernier état d'interface pour calcul différentiel du débit
_last_iface_bytes = {}  # clé: "router_id:iface" → (rx_bytes, tx_bytes, timestamp)
_relay_iface_snap = {}  # mode relais : clé → (prev_rx, prev_tx, snap_ts_str, rx_rate, tx_rate)


@app.route("/api/trafic")
@login_required
@router_required
def api_traffic():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        iface     = request.args.get("interface", "ether1")
        router_id = session.get("router_id", "")
        data = api.get_resource("/interface").get(**{"name": iface})
        if not data:
            return jsonify({"ok": False, "msg": "Interface introuvable"})
        d = data[0]
        rx_bytes = int(d.get("rx-byte", 0) or 0)
        tx_bytes = int(d.get("tx-byte", 0) or 0)
        now      = time.time()
        key      = f"{router_id}:{iface}"

        if getattr(api, "is_relay_snapshot", False):
            # Mode relais : snapshot toutes les ~30s — calculer le taux sur l'intervalle snapshot
            # et le maintenir entre deux cycles pour éviter les zéros permanents.
            snap_ts = ""
            try:
                # Requête légère : récupère uniquement updated_at, pas les données complètes
                conn = db_mod.get_conn()
                row = conn.execute(
                    "SELECT updated_at FROM router_relay_snapshots WHERE router_id=? AND resource=? LIMIT 1",
                    (router_id, "/interface")
                ).fetchone()
                if row:
                    snap_ts = str(row["updated_at"] or "")
            except Exception:
                pass
            cached = _relay_iface_snap.get(key)
            if cached and snap_ts and cached[2] == snap_ts:
                # Même snapshot qu'avant — retourner le taux mis en cache
                rx_rate, tx_rate = cached[3], cached[4]
            elif cached and snap_ts and cached[2] != snap_ts and cached[2]:
                # Nouveau snapshot — recalculer le taux sur l'intervalle réel
                prev_rx, prev_tx, prev_snap_ts = cached[0], cached[1], cached[2]
                try:
                    t1 = datetime.fromisoformat(prev_snap_ts.replace("Z", "+00:00")).replace(tzinfo=None)
                    t2 = datetime.fromisoformat(snap_ts.replace("Z", "+00:00")).replace(tzinfo=None)
                    elapsed = max(1.0, (t2 - t1).total_seconds())
                except Exception:
                    elapsed = 30.0
                rx_rate = int(max(0, (rx_bytes - prev_rx) / elapsed))
                tx_rate = int(max(0, (tx_bytes - prev_tx) / elapsed))
                _relay_iface_snap[key] = (rx_bytes, tx_bytes, snap_ts, rx_rate, tx_rate)
            else:
                rx_rate = tx_rate = 0
                _relay_iface_snap[key] = (rx_bytes, tx_bytes, snap_ts, 0, 0)
        else:
            last = _last_iface_bytes.get(key)
            if last:
                prev_rx, prev_tx, prev_t = last
                elapsed = now - prev_t
                rx_rate = int(max(0, (rx_bytes - prev_rx) / elapsed)) if elapsed > 0 else 0
                tx_rate = int(max(0, (tx_bytes - prev_tx) / elapsed)) if elapsed > 0 else 0
            else:
                rx_rate = tx_rate = 0
            _last_iface_bytes[key] = (rx_bytes, tx_bytes, now)

        return jsonify({
            "ok": True,
            "rx": rx_bytes, "tx": tx_bytes,
            "rx_rate": rx_rate, "tx_rate": tx_rate,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── API Revenus (réels, MikroTik) ──────────────────────────────────────────

def _parse_vente_source(src):
    """Parse 'date=X heure=X user=X profil=X prix=X devise=X reseau=X' → dict."""
    out = {}
    for part in str(src or "").split():
        if "=" in part:
            k, _, v = part.partition("=")
            out[k.strip()] = v.strip()
    return out

@app.route("/api/sync-ventes", methods=["POST"])
@login_required
@router_required
def api_sync_ventes():
    """Sync manuelle du routeur actif — retourne immédiatement le nombre de nouveaux tickets."""
    try:
        router = get_active_router()
        if not router:
            return jsonify({"ok": False, "msg": "Aucun routeur actif", "new": 0})
        router_id = str(router.get("id") or router.get("host") or "")
        if int(router.get("relay_enabled") or 0):
            new_count = _sync_ventes_from_relay(router)
        else:
            new_count = _sync_ventes_for_router(router, timeout=8)
        return jsonify({"ok": True, "new": new_count})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e), "new": 0})


@app.route("/api/sync-etat")
@login_required
def api_sync_etat():
    """Retourne le statut de la dernière sync pour le routeur actif."""
    router_id = session.get("router_id", "")
    stats = _sync_stats.get(router_id, {})
    return jsonify({"ok": True, "stats": stats})


@app.route("/api/wifi-name", methods=["GET", "POST"])
def api_wifi_name():
    payload = request.get_json(silent=True) if request.method == "POST" else {}
    if not session.get("logged_in"):
        auth_ok, _ = _check_basic_auth()
        if not auth_ok:
            return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    owner_id = _current_owner_id()
    router = _get_requested_router(payload)
    if not router:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503

    router_id = str(router.get("id", "") or router.get("host", "")).strip()
    if not router_id:
        return jsonify({"ok": False, "msg": "Routeur invalide"}), 400

    if request.method == "POST":
        name = str(payload.get("wifi_name", "") or payload.get("network_name", "") or payload.get("network", "")).strip()[:64]
        db_mod.db_update_router(router_id, owner_id, {"wifi_name": name})
        _invalidate_routers_cache()
        return jsonify({"ok": True, "wifi_name": name, "network": name, "router_id": router_id})

    wifi_name = str(router.get("wifi_name", "") or "")
    return jsonify({"ok": True, "wifi_name": wifi_name, "network": wifi_name, "router_id": router_id})


@app.route("/api/revenus")
@login_required
@router_required
def api_revenus():
    try:
        router_id = session.get("router_id", "")
        today_str = datetime.now().strftime("%Y-%m-%d")
        month_str = datetime.now().strftime("%Y-%m")
        s = db_mod.db_get_ventes_summary(router_id, today_str, month_str)
        return jsonify({
            "ok": True,
            "today_count": s["today_count"], "today_total": round(s["today_total"], 0),
            "month_count": s["month_count"], "month_total": round(s["month_total"], 0),
            "currency":    s["currency"],
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e),
                        "today_count": 0, "today_total": 0.0,
                        "month_count": 0, "month_total": 0.0,
                        "currency": "FCFA"})

# ─── Rapport de ventes ───────────────────────────────────────────────────────

@app.route("/rapport")
@login_required
@router_required
def report():
    router_id    = session.get("router_id", "")
    filtre_jour   = request.args.get("jour", "")
    filtre_mois   = request.args.get("mois", "")
    filtre_annee  = request.args.get("annee", "")
    filtre_q      = request.args.get("q", "")
    filtre_profil = request.args.get("profil", "")

    today_str = datetime.now().strftime("%Y-%m-%d")
    month_str = datetime.now().strftime("%Y-%m")

    if filtre_annee and filtre_mois:
        mois_filtre = f"{filtre_annee}-{filtre_mois.zfill(2)}"
    elif filtre_mois:
        mois_filtre = f"{datetime.now().year}-{filtre_mois.zfill(2)}"
    elif filtre_annee:
        mois_filtre = f"{filtre_annee}-{datetime.now().strftime('%m')}"
    else:
        mois_filtre = month_str

    summ = db_mod.db_get_ventes_summary(router_id, today_str, month_str)
    rows = db_mod.db_get_ventes(router_id, jour=filtre_jour.zfill(2) if filtre_jour else "",
                                mois=filtre_mois.zfill(2) if filtre_mois else "",
                                annee=filtre_annee, q=filtre_q, profil=filtre_profil)

    conn = db_mod.get_conn()
    total_row = conn.execute(
        "SELECT COUNT(*) cnt, COALESCE(SUM(prix),0) tot FROM ventes WHERE router_id=?",
        (router_id,)
    ).fetchone()
    total_global_count = total_row[0] if total_row else 0
    total_global       = float(total_row[1]) if total_row else 0.0

    profils_rows = conn.execute(
        "SELECT DISTINCT profil FROM ventes WHERE router_id=? ORDER BY profil", (router_id,)
    ).fetchall()
    profils_disponibles = [r[0] for r in profils_rows if r[0]]

    sales = [{
        "id":    r["id"],
        "date":  r["date"],
        "heure": r["heure"],
        "user":  r["user"],
        "profil":r["profil"],
        "prix":  r["prix"],
        "devise":r["devise"],
        "reseau":r["reseau"],
    } for r in rows]

    return render_template("report.html", sales=sales, total=len(sales),
                           today_count=summ["today_count"], today_total=summ["today_total"],
                           month_count=summ["month_count"], month_total=summ["month_total"],
                           month_str=month_str,
                           currency=summ["currency"],
                           total_global=total_global,
                           total_global_count=total_global_count,
                           mois_filtre=mois_filtre,
                           profils_disponibles=profils_disponibles)

@app.route("/rapport/supprimer-mois", methods=["POST"])
@login_required
@router_required
def report_supprimer_mois():
    try:
        router_id = session.get("router_id", "")
        mois = (request.json or {}).get("mois", "")
        if not mois:
            return jsonify({"ok": False, "msg": "Mois requis"})
        deleted = db_mod.db_delete_ventes_mois(router_id, mois)
        return jsonify({"ok": True, "deleted": deleted})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/rapport/supprimer-vente", methods=["POST"])
@login_required
@router_required
def report_supprimer_vente():
    try:
        router_id = session.get("router_id", "")
        vid = (request.json or {}).get("id", "")
        if not vid:
            return jsonify({"ok": False, "msg": "ID requis"})
        ok = db_mod.db_delete_vente(vid, router_id)
        return jsonify({"ok": ok})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ─── Systeme ─────────────────────────────────────────────────────────────────

@app.route("/systeme/planificateur")
@login_required
@router_required
def system_scheduler():
    api, err = get_api()
    schedulers = []
    if err:
        flash(err, "danger")
    else:
        try:
            schedulers = api.get_resource("/system/scheduler").get()
        except Exception as e:
            _flash_err("Une erreur est survenue.", e)
    return render_template("system/scheduler.html", schedulers=schedulers)

@app.route("/systeme/planificateur/basculer", methods=["POST"])
@login_required
@router_required
def system_scheduler_toggle():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        sid      = request.json.get("id")
        disabled = request.json.get("disabled", "yes")
        api.get_resource("/system/scheduler").set(id=sid, disabled=disabled)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/systeme/planificateur/supprimer", methods=["POST"])
@login_required
@router_required
def system_scheduler_remove():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        sid = request.json.get("id")
        api.get_resource("/system/scheduler").remove(id=sid)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/systeme/redemarrer", methods=["POST"])
@login_required
@router_required
def system_reboot():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        api.get_resource("/system").call("reboot")
    except Exception:
        pass  # MikroTik coupe la connexion immédiatement au reboot — c'est attendu
    return jsonify({"ok": True})

@app.route("/systeme/eteindre", methods=["POST"])
@login_required
@router_required
def system_shutdown():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        api.get_resource("/system").call("shutdown")
    except Exception:
        pass  # MikroTik coupe la connexion immédiatement
    return jsonify({"ok": True})

# ─── Parametres : Sessions / Routeurs ────────────────────────────────────────

@app.route("/parametres/routeurs")
@login_required
def sessions_list():
    routers = get_routers()
    return render_template("settings/routers.html", routers=routers)

@app.route("/parametres/routeurs/ajouter", methods=["GET", "POST"])
@login_required
def settings_add_router():
    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        host     = request.form.get("host", "").strip()
        fallback_host = request.form.get("fallback_host", "").strip()
        port     = db_mod._normalize_port(request.form.get("port", 8728))
        user     = request.form.get("user", "admin").strip() or "admin"
        password = request.form.get("password", "")
        currency = request.form.get("currency", "FCFA").strip()

        if not name or not host:
            flash("Nom et hote sont obligatoires.", "danger")
        else:
            owner_id = _current_owner_id() or ""
            try:
                router_info = {
                    "id": str(uuid.uuid4()),
                    "name": name,
                    "host": host,
                    "fallback_host": fallback_host,
                    "port": port,
                    "user": user,
                    "password": password,
                    "currency": currency,
                    "relay_enabled": 1,
                    "relay_token": secrets.token_urlsafe(32),
                    "created_at": datetime.now().isoformat(),
                }
                db_mod.db_add_router(router_info, owner_id=owner_id)
                _invalidate_routers_cache()
                flash(f"Routeur \"{name}\" enregistre avec relais cloud actif.", "success")
                return redirect(url_for("sessions_list"))
            except db_mod.RouterLimitExceededError:
                flash("Chaque compte Gmail a droit a un seul routeur.", "warning")
    return render_template("settings/add_router.html")

@app.route("/parametres/routeurs/<rid>/connecter")
@login_required
def connect_router(rid):
    routers = get_routers()
    for r in routers:
        if r["id"] == rid:
            api_test = None
            api_test, err = mk.safe_connect_router(r)
            if err:
                if int(r.get("relay_enabled") or 0):
                    session["router_id"] = r["id"]
                    session["router_name"] = r["name"]
                    if _router_has_relay_snapshots(r):
                        flash(
                            f"Connecte a \"{r['name']}\" via relais. Les pages affichent uniquement les derniers contenus reels envoyes par ce MikroTik.",
                            "success",
                        )
                    else:
                        flash(
                            f"Connecte a \"{r['name']}\" via relais. En attente du premier snapshot reel du MikroTik.",
                            "warning",
                        )
                    return redirect(url_for("dashboard"))
                _flash_err("Connexion au routeur echouee. Verifiez les parametres (hote, port, identifiants).", err)
                return redirect(url_for("sessions_list"))
            try:
                ensure_ntp_configured(api_test)
                ensure_ticket_runtime_support(api_test)
            except Exception:
                pass
            finally:
                _close_api_quietly(api_test)
            session["router_id"]   = r["id"]
            session["router_name"] = r["name"]
            flash(f"Connecte a \"{r['name']}\".", "success")
            return redirect(url_for("dashboard"))
    flash("Routeur introuvable.", "danger")
    return redirect(url_for("sessions_list"))

@app.route("/api/test-connexion", methods=["POST"])
@login_required
def api_test_connexion():
    """Teste la connexion à un routeur MikroTik sans le sélectionner."""
    data = request.get_json(silent=True) or {}
    host = str(data.get("host", "")).strip()
    fallback_host = str(data.get("fallback_host", "")).strip()
    user = str(data.get("user", "admin")).strip() or "admin"
    pwd  = str(data.get("password", ""))
    port = int(data.get("port", 8728) or 8728)
    driver = str(data.get("driver", "mikrotik") or "mikrotik").strip() or "mikrotik"
    if not host:
        return jsonify({"ok": False, "msg": "Adresse IP manquante."})
    api_t = None
    try:
        api_t, err = mk.safe_connect(host, user, pwd, port, timeout=8, driver=driver, fallback_host=fallback_host)
        if err:
            return jsonify({"ok": False, "msg": f"Connexion echouee : {err}"})
        identity = api_t.get_resource("/system/identity").get()
        name = identity[0].get("name", host) if identity else host
        return jsonify({"ok": True, "msg": f"Connexion reussie — routeur : {name}"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})
    finally:
        _close_api_quietly(api_t)

def _is_local_relay_host(host):
    host = str(host or "").strip().lower().strip("[]")
    return (
        not host
        or host == "localhost"
        or host == "::1"
        or host.startswith("127.")
    )


def _is_usable_lan_ip(ip):
    ip = str(ip or "").strip()
    if not ip or ":" in ip:
        return False
    return not (
        ip.startswith("127.")
        or ip.startswith("169.254.")
        or ip == "0.0.0.0"
    )


def _relay_ip_preference(ip):
    ip = str(ip or "").strip()
    if ip.startswith("192.168."):
        return 0
    if ip.startswith("172.16.") or ip.startswith("172.17.") or ip.startswith("172.18.") or ip.startswith("172.19."):
        return 1
    if re.match(r"^172\.(2[0-9]|3[0-1])\.", ip):
        return 1
    if ip.startswith("10."):
        return 2
    return 3


def _detect_lan_ip_for_relay():
    """Find an address reachable by MikroTik when localhost is used in the browser."""
    forced_ip = os.environ.get("KETAMON_RELAY_LAN_IP", "").strip()
    if _is_usable_lan_ip(forced_ip):
        return forced_ip
    targets = []
    try:
        owner_id = _current_owner_id()
        routers = db_mod.db_get_routers(owner_id=owner_id) if owner_id else db_mod.db_get_routers()
    except Exception:
        routers = []
    for router in routers or []:
        host = str(router.get("host") or "").strip()
        if host and not _is_local_relay_host(host) and not re.search(r"[a-zA-Z]", host):
            targets.append((host, int(router.get("port") or 8728)))
    targets.extend([("10.10.10.1", 8728), ("192.168.88.1", 8728), ("192.168.1.1", 8728), ("1.1.1.1", 80)])
    seen = set()
    candidates = []
    for host, port in targets:
        key = (host, port)
        if key in seen:
            continue
        seen.add(key)
        sock = None
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.settimeout(0.3)
            sock.connect((host, int(port or 8728)))
            ip = sock.getsockname()[0]
            if _is_usable_lan_ip(ip):
                candidates.append(ip)
        except Exception:
            continue
        finally:
            try:
                if sock:
                    sock.close()
            except Exception:
                pass
    if candidates:
        return sorted(set(candidates), key=_relay_ip_preference)[0]
    return ""


def _relay_public_base_url():
    global _relay_public_url_cache
    configured = os.environ.get("KETAMON_PUBLIC_URL", "").strip().rstrip("/")
    if configured:
        _relay_public_url_cache = configured
        return configured
    root = request.url_root.rstrip("/")
    try:
        parsed = urlsplit(root)
        host = parsed.hostname or ""
        if not _is_local_relay_host(host):
            _relay_public_url_cache = root
            return root
        lan_ip = _detect_lan_ip_for_relay()
        if lan_ip:
            port = f":{parsed.port}" if parsed.port else ""
            scheme = parsed.scheme or "http"
            result = f"{scheme}://{lan_ip}{port}"
            _relay_public_url_cache = result
            return result
    except Exception:
        pass
    _relay_public_url_cache = root
    return root


def _relay_token_from_request():
    data = request.get_json(silent=True) if request.method == "POST" else None
    data = data if isinstance(data, dict) else {}
    return (
        request.headers.get("X-KetaMon-Relay-Token")
        or request.headers.get("X-Relay-Token")
        or data.get("token")
        or request.args.get("token")
        or ""
    ).strip()


def _relay_router_from_request():
    token = _relay_token_from_request()
    router = db_mod.db_get_router_by_relay_token(token)
    if not router:
        return None, token
    db_mod.db_touch_router_relay(router["id"], "online")
    return router, token


def _relay_unescape_value(value):
    text = str(value or "")
    out = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            code = text[i + 1]
            if code == "n":
                out.append("\n")
            elif code == "r":
                out.append("\r")
            elif code == "t":
                out.append("\t")
            elif code == "p":
                out.append("|")
            elif code == "\\":
                out.append("\\")
            else:
                out.append(code)
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _parse_relay_snapshot_text(text):
    resources = {}
    for raw_line in str(text or "").splitlines():
        line = raw_line.strip()
        if not line or line == "KETAMON_SNAPSHOT_V1":
            continue
        parts = line.split("|")
        resource = ""
        row = {}
        for part in parts:
            if "=" not in part:
                continue
            key, value = part.split("=", 1)
            key = key.strip()
            value = _relay_unescape_value(value)
            if key in {"R", "RESOURCE", "resource"}:
                resource = value.strip()
            elif key:
                row[key] = value
        if resource:
            resources.setdefault(resource, []).append(row)
    return resources


@app.route("/api/relay/snapshot", methods=["POST"])
def api_relay_snapshot():
    router, token = _relay_router_from_request()
    if not router:
        return jsonify({"ok": False, "msg": "Token relais invalide."}), 401
    data = request.get_json(silent=True)
    if isinstance(data, dict):
        resources = data.get("resources") if isinstance(data.get("resources"), dict) else data
    else:
        resources = _parse_relay_snapshot_text(request.get_data(as_text=True))
    counts = _relay_resource_counts(resources)
    relay_status_rows = resources.get("/ketamon/relay-status") if isinstance(resources, dict) else []
    relay_status = relay_status_rows[0] if isinstance(relay_status_rows, list) and relay_status_rows else {}
    saved = db_mod.db_upsert_router_relay_snapshots(router["id"], resources)
    db_mod.db_touch_router_relay(router["id"], "snapshot")
    synced = _sync_relay_snapshot_database(router["id"], resources)
    expiry = _enforce_relay_snapshot_expirations(router)
    upgrade_queued = _maybe_queue_relay_auto_upgrade(router, token, counts)
    boot_queued = _maybe_queue_relay_boot_script(router, token, resources)
    print(
        "[RELAY][SNAPSHOT] "
        f"router={router.get('name') or router.get('id')} "
        f"profiles={counts.get('/ip/hotspot/user/profile', 0)} "
        f"users={counts.get('/ip/hotspot/user', 0)} "
        f"active={counts.get('/ip/hotspot/active', 0)} "
        f"status={relay_status} "
        f"synced={synced} expiry={expiry} upgrade={upgrade_queued} boot={boot_queued}",
        flush=True,
    )
    return jsonify({
        "ok": True,
        "saved": saved,
        "synced": synced,
        "counts": counts,
        "upgrade_queued": upgrade_queued,
        "router_id": router["id"],
        "expiry": expiry,
        "server_time": datetime.now().isoformat(),
    })


@app.route("/api/relay/ping", methods=["GET", "POST"])
def api_relay_ping():
    router, _token = _relay_router_from_request()
    if not router:
        return jsonify({"ok": False, "msg": "Token relais invalide."}), 401
    payload = request.get_json(silent=True) if request.method == "POST" else {}
    payload = payload if isinstance(payload, dict) else {}
    status = payload.get("status") or request.args.get("status") or "online"
    db_mod.db_touch_router_relay(router["id"], status)
    return jsonify({
        "ok": True,
        "router_id": router["id"],
        "router_name": router.get("name", ""),
        "server_time": datetime.now().isoformat(),
    })


@app.route("/api/relay/commands/next", methods=["GET", "POST"])
def api_relay_next_command():
    router, _token = _relay_router_from_request()
    if not router:
        return jsonify({"ok": False, "msg": "Token relais invalide."}), 401
    command = db_mod.db_claim_next_router_relay_command(router["id"])
    if not command:
        return jsonify({"ok": True, "empty": True, "server_time": datetime.now().isoformat()})
    try:
        payload = json.loads(command.get("payload") or "{}")
    except Exception:
        payload = {}
    return jsonify({
        "ok": True,
        "empty": False,
        "command": {
            "id": command["id"],
            "type": command["command"],
            "payload": payload,
        },
    })


@app.route("/api/relay/commands/result", methods=["GET", "POST"])
def api_relay_command_result():
    router, _token = _relay_router_from_request()
    if not router:
        return jsonify({"ok": False, "msg": "Token relais invalide."}), 401
    data = request.get_json(silent=True) if request.method == "POST" else {}
    data = data if isinstance(data, dict) else {}
    command_id = data.get("id") or request.args.get("id") or ""
    ok_raw = data.get("ok", request.args.get("ok", "0"))
    ok = str(ok_raw).strip().lower() in {"1", "true", "yes", "ok"}
    result = data.get("result")
    if result is None:
        result = request.args.get("msg", "")
    if not command_id:
        return jsonify({"ok": False, "msg": "ID commande manquant."}), 400
    saved = db_mod.db_complete_router_relay_command(command_id, router["id"], ok, result)
    return jsonify({"ok": bool(saved), "saved": bool(saved)})


def _router_clock_datetime_from_snapshot(router_id):
    try:
        rows = db_mod.db_get_router_relay_snapshot(router_id, "/system/clock")
        row = rows[0] if rows else {}
        clock_time = str(row.get("time") or "").strip()
        clock_date = str(row.get("date") or "").strip()
        if not clock_time or not clock_date:
            return None
        if "/" in clock_date:
            clock_date = _ros_date_to_iso(clock_date)
        if not clock_date:
            return None
        return datetime.strptime(f"{clock_date} {clock_time[:8]}", "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None


def _router_clock_drift_seconds(router_id):
    router_dt = _router_clock_datetime_from_snapshot(router_id)
    if not router_dt:
        return None
    return int((datetime.now() - router_dt).total_seconds())


def _server_clock_routeros_source():
    now = datetime.now() + timedelta(seconds=2)
    iso_date = now.strftime("%Y-%m-%d")
    ros_date = now.strftime("%b/%d/%Y").lower()
    clock_time = now.strftime("%H:%M:%S")
    return "\n".join([
        ":do { /system clock set time-zone-autodetect=no time-zone-name=Africa/Abidjan; } on-error={ :do { /system clock set time-zone-name=manual gmt-offset=+00:00; } on-error={} }",
        f":do {{ /system clock set time={_relay_routeros_quote(clock_time)}; }} on-error={{}}",
        f":do {{ /system clock set date={_relay_routeros_quote(iso_date)}; }} on-error={{ :do {{ /system clock set date={_relay_routeros_quote(ros_date)}; }} on-error={{}} }}",
        ':do { /system ntp client set enabled=yes servers="pool.ntp.org,time.google.com"; } on-error={ :do { /system ntp client set enabled=yes primary-ntp=216.239.35.0 secondary-ntp=216.239.35.4; } on-error={} }',
    ])


def _clock_sync_source_if_needed(router_id):
    drift = _router_clock_drift_seconds(router_id)
    if drift is None or abs(drift) <= 300:
        return ""
    return _server_clock_routeros_source()


@app.route("/api/relay/routeros/next", methods=["GET"])
def api_relay_routeros_next():
    router, token = _relay_router_from_request()
    if not router:
        return ":put \"KetaMon relay: token invalide\"\n", 401, {"Content-Type": "text/plain; charset=utf-8"}
    clock_sync_source = _clock_sync_source_if_needed(router["id"])
    if clock_sync_source:
        return (
            ':do {\n'
            f'{clock_sync_source}\n'
            ':put "KetaMon relay: horloge synchronisee";\n'
            '} on-error={ :put "KetaMon relay: erreur sync horloge"; }\n'
        ), 200, {"Content-Type": "text/plain; charset=utf-8"}
    command = db_mod.db_claim_next_router_relay_command(router["id"])
    if not command:
        return ":put \"KetaMon relay: aucune commande\"\n", 200, {"Content-Type": "text/plain; charset=utf-8"}
    print(
        "[RELAY][NEXT] "
        f"router={router.get('name') or router.get('id')} "
        f"command={command.get('command')} id={command.get('id')}",
        flush=True,
    )
    command_id = command["id"]
    result_url = (
        f"{_relay_public_base_url()}/api/relay/routeros/result"
        f"?token={quote(token)}&id={quote(command_id)}"
    )
    if command["command"] == "ping":
        source = (
            ':put "KetaMon relay: ping";\n'
            f'{clock_sync_source}\n'
            f':do {{ /tool fetch url="{result_url}&ok=1&msg=pong" keep-result=no duration=15s; }} on-error={{}}\n'
        )
    elif command["command"] == "routeros-script":
        try:
            payload = json.loads(command.get("payload") or "{}")
        except Exception:
            payload = {}
        script_source = str(payload.get("source") or "").strip()
        if not script_source:
            source = (
                ':put "KetaMon relay: script vide";\n'
                f':do {{ /tool fetch url="{result_url}&ok=0&msg=script_vide" keep-result=no duration=15s; }} on-error={{}}\n'
            )
        else:
            source = (
                ':do {\n'
                f'{clock_sync_source}\n'
                f'{script_source}\n'
                f':do {{ /tool fetch url="{result_url}&ok=1&msg=done" keep-result=no duration=15s; }} on-error={{}}\n'
                '} on-error={\n'
                f':do {{ /tool fetch url="{result_url}&ok=0&msg=error" keep-result=no duration=15s; }} on-error={{}}\n'
                '}\n'
            )
    else:
        source = (
            f':put "KetaMon relay: commande non supportee {command["command"]}";\n'
            f':do {{ /tool fetch url="{result_url}&ok=0&msg=commande_non_supportee" keep-result=no duration=15s; }} on-error={{}}\n'
        )
    return source, 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.route("/api/relay/routeros/result", methods=["GET", "POST"])
def api_relay_routeros_result():
    return api_relay_command_result()


@app.route("/api/relay/routers/<rid>/ping", methods=["POST"])
@login_required
def api_relay_queue_ping(rid):
    owner_id = _current_owner_id()
    router = db_mod.db_get_router(rid, owner_id)
    if not router:
        return jsonify({"ok": False, "msg": "Routeur introuvable ou non autorise."}), 404
    if not int(router.get("relay_enabled") or 0):
        return jsonify({"ok": False, "msg": "Relais cloud non active sur ce routeur."}), 400
    command = db_mod.db_enqueue_router_relay_command(
        rid,
        router.get("owner_id", ""),
        "ping",
        {"from": "web-test"},
    )
    if not command:
        return jsonify({"ok": False, "msg": "Impossible de creer la commande relais."}), 500
    return jsonify({
        "ok": True,
        "msg": "Test relais envoye. Si le MikroTik poll, le statut passera de queued a done.",
        "command_id": command["id"],
    })


def _build_routeros_relay_script(base_url, token):
    base_url = str(base_url or "").rstrip("/")
    token = str(token or "").strip()
    next_url = f"{base_url}/api/relay/routeros/next?token={token}"
    ping_url = f"{base_url}/api/relay/ping?token={token}"
    snapshot_url = f"{base_url}/api/relay/snapshot?token={token}"
    return "\n".join([
        "# KetaMon Cloud Relay - polling + real snapshot",
        "/system script remove [find name=\"ketamon-relay-poll\"]",
        "/system scheduler remove [find name=\"ketamon-relay-poll\"]",
        "/system scheduler remove [find name=\"ketamon-relay-watchdog\"]",
        "/system script add name=\"ketamon-relay-poll\" policy=ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon source={",
        "  :global ktmEsc do={",
        "    :local v [:tostr $1];",
        "    :local out \"\";",
        "    :for i from=0 to=([:len $v] - 1) do={",
        "      :local ch [:pick $v $i ($i + 1)];",
        "      :if ($ch = \"\\\\\") do={ :set out ($out . \"\\\\\\\\\"); } else={",
        "        :if ($ch = \"|\") do={ :set out ($out . \"\\\\p\"); } else={",
        "          :if ($ch = \"\\n\") do={ :set out ($out . \"\\\\n\"); } else={ :set out ($out . $ch); }",
        "        }",
        "      }",
        "    }",
        "    :return $out;",
        "  };",
        "  :local NL \"\\n\";",
        "  :for ktmCmd from=1 to=3 do={",
        f"    :do {{ /tool fetch url=\"{next_url}\" dst-path=\"ketamon-relay-next.rsc\" keep-result=yes; :delay 1s; /import file-name=\"ketamon-relay-next.rsc\"; /file remove [find name=\"ketamon-relay-next.rsc\"]; }} on-error={{}}",
        "  }",
        "  :local payload (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :set payload ($payload . \"R=/ketamon/relay-status|source=safe-snapshot-v3|hotspot-users-found=\" . [$ktmEsc [:len [/ip hotspot user find]]] . $NL); } on-error={};",
        "  :do { :set payload ($payload . \"R=/system/identity|name=\" . [$ktmEsc [/system identity get name]] . $NL); } on-error={};",
        "  :do { :set payload ($payload . \"R=/system/resource|version=\" . [$ktmEsc [/system resource get version]] . \"|uptime=\" . [$ktmEsc [/system resource get uptime]] . \"|cpu-load=\" . [$ktmEsc [/system resource get cpu-load]] . \"|total-memory=\" . [$ktmEsc [/system resource get total-memory]] . \"|free-memory=\" . [$ktmEsc [/system resource get free-memory]] . \"|total-hdd-space=\" . [$ktmEsc [/system resource get total-hdd-space]] . \"|free-hdd-space=\" . [$ktmEsc [/system resource get free-hdd-space]] . \"|board-name=\" . [$ktmEsc [/system resource get board-name]] . $NL); } on-error={};",
        "  :do { :set payload ($payload . \"R=/system/clock|time=\" . [$ktmEsc [/system clock get time]] . \"|date=\" . [$ktmEsc [/system clock get date]] . $NL); } on-error={};",
        "  :do { :set payload ($payload . \"R=/system/routerboard|model=\" . [$ktmEsc [/system routerboard get model]] . $NL); } on-error={};",
        "  :do { :foreach i in=[/ip hotspot print as-value] do={ :set payload ($payload . \"R=/ip/hotspot|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|interface=\" . [$ktmEsc ($i->\"interface\")] . \"|address-pool=\" . [$ktmEsc ($i->\"address-pool\")] . \"|profile=\" . [$ktmEsc ($i->\"profile\")] . $NL); } } on-error={};",
        "  :do { :foreach uid in=[/ip hotspot user find] do={ :local name \"\"; :local profile \"\"; :local disabled \"\"; :local limitUptime \"\"; :local uptime \"\"; :local bytesIn \"\"; :local bytesOut \"\"; :local limitBytes \"\"; :local mac \"\"; :local server \"\"; :local comment \"\"; :do { :set name [/ip hotspot user get $uid name]; } on-error={}; :do { :set profile [/ip hotspot user get $uid profile]; } on-error={}; :do { :set disabled [/ip hotspot user get $uid disabled]; } on-error={}; :do { :set limitUptime [/ip hotspot user get $uid limit-uptime]; } on-error={}; :do { :set uptime [/ip hotspot user get $uid uptime]; } on-error={}; :do { :set bytesIn [/ip hotspot user get $uid bytes-in]; } on-error={}; :do { :set bytesOut [/ip hotspot user get $uid bytes-out]; } on-error={}; :do { :set limitBytes [/ip hotspot user get $uid limit-bytes-total]; } on-error={}; :do { :set mac [/ip hotspot user get $uid mac-address]; } on-error={}; :do { :set server [/ip hotspot user get $uid server]; } on-error={}; :do { :set comment [/ip hotspot user get $uid comment]; } on-error={}; :set payload ($payload . \"R=/ip/hotspot/user|.id=\" . [$ktmEsc $uid] . \"|name=\" . [$ktmEsc $name] . \"|profile=\" . [$ktmEsc $profile] . \"|disabled=\" . [$ktmEsc $disabled] . \"|limit-uptime=\" . [$ktmEsc $limitUptime] . \"|uptime=\" . [$ktmEsc $uptime] . \"|bytes-in=\" . [$ktmEsc $bytesIn] . \"|bytes-out=\" . [$ktmEsc $bytesOut] . \"|limit-bytes-total=\" . [$ktmEsc $limitBytes] . \"|mac-address=\" . [$ktmEsc $mac] . \"|server=\" . [$ktmEsc $server] . \"|comment=\" . [$ktmEsc $comment] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip hotspot user profile print as-value] do={ :set payload ($payload . \"R=/ip/hotspot/user/profile|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|rate-limit=\" . [$ktmEsc ($i->\"rate-limit\")] . \"|shared-users=\" . [$ktmEsc ($i->\"shared-users\")] . \"|address-pool=\" . [$ktmEsc ($i->\"address-pool\")] . \"|session-timeout=\" . [$ktmEsc ($i->\"session-timeout\")] . \"|idle-timeout=\" . [$ktmEsc ($i->\"idle-timeout\")] . \"|keepalive-timeout=\" . [$ktmEsc ($i->\"keepalive-timeout\")] . \"|mac-cookie-timeout=\" . [$ktmEsc ($i->\"mac-cookie-timeout\")] . \"|add-mac-cookie=\" . [$ktmEsc ($i->\"add-mac-cookie\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip hotspot active print as-value] do={ :set payload ($payload . \"R=/ip/hotspot/active|.id=\" . [$ktmEsc ($i->\".id\")] . \"|user=\" . [$ktmEsc ($i->\"user\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|uptime=\" . [$ktmEsc ($i->\"uptime\")] . \"|session-time-left=\" . [$ktmEsc ($i->\"session-time-left\")] . \"|bytes-in=\" . [$ktmEsc ($i->\"bytes-in\")] . \"|bytes-out=\" . [$ktmEsc ($i->\"bytes-out\")] . \"|server=\" . [$ktmEsc ($i->\"server\")] . \"|login-by=\" . [$ktmEsc ($i->\"login-by\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip hotspot host print as-value] do={ :set payload ($payload . \"R=/ip/hotspot/host|.id=\" . [$ktmEsc ($i->\".id\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|to-address=\" . [$ktmEsc ($i->\"to-address\")] . \"|server=\" . [$ktmEsc ($i->\"server\")] . \"|authorized=\" . [$ktmEsc ($i->\"authorized\")] . \"|blocked=\" . [$ktmEsc ($i->\"blocked\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip hotspot ip-binding print as-value] do={ :set payload ($payload . \"R=/ip/hotspot/ip-binding|.id=\" . [$ktmEsc ($i->\".id\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|to-address=\" . [$ktmEsc ($i->\"to-address\")] . \"|server=\" . [$ktmEsc ($i->\"server\")] . \"|type=\" . [$ktmEsc ($i->\"type\")] . \"|disabled=\" . [$ktmEsc ($i->\"disabled\")] . \"|comment=\" . [$ktmEsc ($i->\"comment\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip hotspot cookie print as-value] do={ :set payload ($payload . \"R=/ip/hotspot/cookie|.id=\" . [$ktmEsc ($i->\".id\")] . \"|user=\" . [$ktmEsc ($i->\"user\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|expires-in=\" . [$ktmEsc ($i->\"expires-in\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip dhcp-server lease print as-value] do={ :set payload ($payload . \"R=/ip/dhcp-server/lease|.id=\" . [$ktmEsc ($i->\".id\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|host-name=\" . [$ktmEsc ($i->\"host-name\")] . \"|status=\" . [$ktmEsc ($i->\"status\")] . \"|dynamic=\" . [$ktmEsc ($i->\"dynamic\")] . \"|comment=\" . [$ktmEsc ($i->\"comment\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/interface print as-value] do={ :set payload ($payload . \"R=/interface|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|type=\" . [$ktmEsc ($i->\"type\")] . \"|running=\" . [$ktmEsc ($i->\"running\")] . \"|disabled=\" . [$ktmEsc ($i->\"disabled\")] . \"|rx-byte=\" . [$ktmEsc ($i->\"rx-byte\")] . \"|tx-byte=\" . [$ktmEsc ($i->\"tx-byte\")] . \"|rx-packet=\" . [$ktmEsc ($i->\"rx-packet\")] . \"|tx-packet=\" . [$ktmEsc ($i->\"tx-packet\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/system scheduler print as-value] do={ :set payload ($payload . \"R=/system/scheduler|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|start-date=\" . [$ktmEsc ($i->\"start-date\")] . \"|start-time=\" . [$ktmEsc ($i->\"start-time\")] . \"|interval=\" . [$ktmEsc ($i->\"interval\")] . \"|disabled=\" . [$ktmEsc ($i->\"disabled\")] . \"|next-run=\" . [$ktmEsc ($i->\"next-run\")] . \"|on-event=\" . [$ktmEsc ($i->\"on-event\")] . $NL); } } on-error={};",
        "  :do { :foreach i in=[/ip pool print as-value] do={ :set payload ($payload . \"R=/ip/pool|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|ranges=\" . [$ktmEsc ($i->\"ranges\")] . $NL); } } on-error={};",
        "  :do { :local c 0; :foreach i in=[/log print as-value] do={ :if ($c < 40) do={ :set payload ($payload . \"R=/log|.id=\" . [$ktmEsc ($i->\".id\")] . \"|time=\" . [$ktmEsc ($i->\"time\")] . \"|topics=\" . [$ktmEsc ($i->\"topics\")] . \"|message=\" . [$ktmEsc ($i->\"message\")] . $NL); :set c ($c + 1); } } } on-error={};",
        f"  :do {{ /tool fetch url=\"{snapshot_url}\" http-method=post http-header-field=\"Content-Type: text/plain\" http-data=$payload keep-result=no; }} on-error={{ /tool fetch url=\"{snapshot_url}\" http-method=post http-data=$payload keep-result=no; }}",
        f"  /tool fetch url=\"{ping_url}\" keep-result=no;",
        f"  /tool fetch url=\"{next_url}\" dst-path=\"ketamon-relay-next.rsc\" keep-result=yes;",
        "  :delay 1s;",
        "  /import file-name=\"ketamon-relay-next.rsc\";",
        "  /file remove [find name=\"ketamon-relay-next.rsc\"];",
        "}",
        "/system scheduler add name=\"ketamon-relay-poll\" interval=30s on-event=\"/system script run ketamon-relay-poll\" disabled=no",
        "/system scheduler add name=\"ketamon-relay-watchdog\" interval=2m on-event=\":do { /system script run ketamon-relay-poll; } on-error={}\" disabled=no",
        ":delay 2s",
        ":do { /system script run ketamon-relay-poll; } on-error={}",
    ])


def _build_routeros_relay_script(base_url, token):
    base_url = str(base_url or "").rstrip("/")
    token = str(token or "").strip()
    next_url = f"{base_url}/api/relay/routeros/next?token={token}"
    ping_url = f"{base_url}/api/relay/ping?token={token}"
    snapshot_url = f"{base_url}/api/relay/snapshot?token={token}"

    def send_line(payload_var="p"):
        return (
            f"  :do {{ /tool fetch url=\"{snapshot_url}\" http-method=post "
            f"http-header-field=\"Content-Type: text/plain\" http-data=${payload_var} keep-result=no duration=10s; }} on-error={{}}"
        )

    return "\n".join([
        "# KetaMon Cloud Relay - safe snapshots v7 (mutex + active-first + count-sentinel + keepalive)",
        "/system script remove [find name=\"ketamon-relay-poll\"]",
        "/system scheduler remove [find name=\"ketamon-relay-poll\"]",
        "/system scheduler remove [find name=\"ketamon-relay-watchdog\"]",
        "/system scheduler remove [find name=\"ketamon-relay-keepalive\"]",
        "/system script add name=\"ketamon-relay-poll\" policy=ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon source={",
        "  :global ktmBusy;",
        "  :if ($ktmBusy = \"1\") do={ :error \"relay busy\"; };",
        "  :set ktmBusy \"1\";",
        "  :do {",
        "  :global ktmEsc do={",
        "    :local v [:tostr $1];",
        "    :local out \"\";",
        "    :for i from=0 to=([:len $v] - 1) do={",
        "      :local ch [:pick $v $i ($i + 1)];",
        "      :if ($ch = \"\\\\\") do={ :set out ($out . \"\\\\\\\\\"); } else={",
        "        :if ($ch = \"|\") do={ :set out ($out . \"\\\\p\"); } else={",
        "          :if ($ch = \"\\n\") do={ :set out ($out . \"\\\\n\"); } else={ :set out ($out . $ch); }",
        "        }",
        "      }",
        "    }",
        "    :return $out;",
        "  };",
        "  :local NL \"\\n\";",
        "  :local p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :set p ($p . \"R=/ketamon/relay-status|source=safe-snapshot-v7|hotspot-users-found=\" . [$ktmEsc [:len [/ip hotspot user find]]] . $NL); } on-error={};",
        "  :local activeCount 0;",
        "  :do { :foreach aid in=[/ip hotspot active find] do={ :local user [/ip hotspot active get $aid user]; :local addr [/ip hotspot active get $aid address]; :local mac [/ip hotspot active get $aid mac-address]; :if ([:len $mac] = 0) do={ :local hid [/ip hotspot host find where address=$addr]; :if ([:len $hid] > 0) do={ :set mac [/ip hotspot host get [:pick $hid 0] mac-address]; } }; :set p ($p . \"R=/ip/hotspot/active|.id=\" . [$ktmEsc $aid] . \"|user=\" . [$ktmEsc $user] . \"|address=\" . [$ktmEsc $addr] . \"|mac-address=\" . [$ktmEsc $mac] . \"|uptime=\" . [$ktmEsc [/ip hotspot active get $aid uptime]] . \"|session-time-left=\" . [$ktmEsc [/ip hotspot active get $aid session-time-left]] . \"|bytes-in=\" . [$ktmEsc [/ip hotspot active get $aid bytes-in]] . \"|bytes-out=\" . [$ktmEsc [/ip hotspot active get $aid bytes-out]] . \"|server=\" . [$ktmEsc [/ip hotspot active get $aid server]] . $NL); :set activeCount ($activeCount + 1); } } on-error={};",
        "  :set p ($p . \"R=/ip/hotspot/active|_count=\" . $activeCount . $NL);",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :set p ($p . \"R=/system/identity|name=\" . [$ktmEsc [/system identity get name]] . $NL); } on-error={};",
        "  :do { :set p ($p . \"R=/system/resource|version=\" . [$ktmEsc [/system resource get version]] . \"|uptime=\" . [$ktmEsc [/system resource get uptime]] . \"|cpu-load=\" . [$ktmEsc [/system resource get cpu-load]] . \"|total-memory=\" . [$ktmEsc [/system resource get total-memory]] . \"|free-memory=\" . [$ktmEsc [/system resource get free-memory]] . \"|total-hdd-space=\" . [$ktmEsc [/system resource get total-hdd-space]] . \"|free-hdd-space=\" . [$ktmEsc [/system resource get free-hdd-space]] . \"|board-name=\" . [$ktmEsc [/system resource get board-name]] . $NL); } on-error={};",
        "  :do { :set p ($p . \"R=/system/clock|time=\" . [$ktmEsc [/system clock get time]] . \"|date=\" . [$ktmEsc [/system clock get date]] . $NL); } on-error={};",
        "  :do { :set p ($p . \"R=/system/routerboard|model=\" . [$ktmEsc [/system routerboard get model]] . $NL); } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :foreach i in=[/ip hotspot print as-value] do={ :set p ($p . \"R=/ip/hotspot|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|interface=\" . [$ktmEsc ($i->\"interface\")] . \"|address-pool=\" . [$ktmEsc ($i->\"address-pool\")] . \"|profile=\" . [$ktmEsc ($i->\"profile\")] . $NL); } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :foreach i in=[/ip hotspot user profile print as-value] do={ :set p ($p . \"R=/ip/hotspot/user/profile|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|rate-limit=\" . [$ktmEsc ($i->\"rate-limit\")] . \"|shared-users=\" . [$ktmEsc ($i->\"shared-users\")] . \"|address-pool=\" . [$ktmEsc ($i->\"address-pool\")] . $NL); } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do {",
        "    :local c 0;",
        "    :local total 0;",
        "    :foreach uid in=[/ip hotspot user find] do={",
        "      :if ($total < 5000) do={",
        "        :local name \"\"; :local profile \"\"; :local disabled \"\";",
        "        :local limitUptime \"\"; :local bytesIn \"\"; :local bytesOut \"\";",
        "        :local mac \"\"; :local server \"\"; :local comment \"\";",
        "        :do { :set name [/ip hotspot user get $uid name]; } on-error={};",
        "        :do { :set profile [/ip hotspot user get $uid profile]; } on-error={};",
        "        :do { :set disabled [/ip hotspot user get $uid disabled]; } on-error={};",
        "        :do { :set limitUptime [/ip hotspot user get $uid limit-uptime]; } on-error={};",
        "        :do { :set bytesIn [/ip hotspot user get $uid bytes-in]; } on-error={};",
        "        :do { :set bytesOut [/ip hotspot user get $uid bytes-out]; } on-error={};",
        "        :do { :set mac [/ip hotspot user get $uid mac-address]; } on-error={};",
        "        :do { :set server [/ip hotspot user get $uid server]; } on-error={};",
        "        :do { :set comment [/ip hotspot user get $uid comment]; } on-error={};",
        "        :set p ($p . \"R=/ip/hotspot/user|.id=\" . [$ktmEsc $uid] . \"|name=\" . [$ktmEsc $name] . \"|profile=\" . [$ktmEsc $profile] . \"|disabled=\" . [$ktmEsc $disabled] . \"|limit-uptime=\" . [$ktmEsc $limitUptime] . \"|bytes-in=\" . [$ktmEsc $bytesIn] . \"|bytes-out=\" . [$ktmEsc $bytesOut] . \"|mac-address=\" . [$ktmEsc $mac] . \"|server=\" . [$ktmEsc $server] . \"|comment=\" . [$ktmEsc $comment] . $NL);",
        "        :set c ($c + 1);",
        "        :set total ($total + 1);",
        f"        :if ($c >= 100) do={{ :do {{ /tool fetch url=\"{snapshot_url}\" http-method=post http-header-field=\"Content-Type: text/plain\" http-data=$p keep-result=no duration=10s; }} on-error={{}}; :set p (\"KETAMON_SNAPSHOT_V1\" . $NL); :set c 0; }}",
        "      }",
        "    }",
        f"    :if ($c > 0) do={{ :do {{ /tool fetch url=\"{snapshot_url}\" http-method=post http-header-field=\"Content-Type: text/plain\" http-data=$p keep-result=no duration=10s; }} on-error={{}}; }}",
        "  } on-error={};",
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :local c 0; :foreach i in=[/ip hotspot host print as-value] do={ :if ($c < 100) do={ :set p ($p . \"R=/ip/hotspot/host|.id=\" . [$ktmEsc ($i->\".id\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|to-address=\" . [$ktmEsc ($i->\"to-address\")] . \"|server=\" . [$ktmEsc ($i->\"server\")] . \"|authorized=\" . [$ktmEsc ($i->\"authorized\")] . $NL); :set c ($c + 1); } } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :foreach i in=[/interface print as-value] do={ :set p ($p . \"R=/interface|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|type=\" . [$ktmEsc ($i->\"type\")] . \"|running=\" . [$ktmEsc ($i->\"running\")] . \"|disabled=\" . [$ktmEsc ($i->\"disabled\")] . \"|actual-mtu=\" . [$ktmEsc ($i->\"actual-mtu\")] . \"|mtu=\" . [$ktmEsc ($i->\"mtu\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|rx-byte=\" . [$ktmEsc ($i->\"rx-byte\")] . \"|tx-byte=\" . [$ktmEsc ($i->\"tx-byte\")] . \"|rx-packet=\" . [$ktmEsc ($i->\"rx-packet\")] . \"|tx-packet=\" . [$ktmEsc ($i->\"tx-packet\")] . $NL); } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :local c 0; :foreach i in=[/ip dhcp-server lease print as-value] do={ :if ($c < 500) do={ :set p ($p . \"R=/ip/dhcp-server/lease|.id=\" . [$ktmEsc ($i->\".id\")] . \"|address=\" . [$ktmEsc ($i->\"address\")] . \"|mac-address=\" . [$ktmEsc ($i->\"mac-address\")] . \"|host-name=\" . [$ktmEsc ($i->\"host-name\")] . \"|status=\" . [$ktmEsc ($i->\"status\")] . \"|dynamic=\" . [$ktmEsc ($i->\"dynamic\")] . \"|comment=\" . [$ktmEsc ($i->\"comment\")] . $NL); :set c ($c + 1); } } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :local c 0; :foreach i in=[/log print as-value] do={ :if ($c < 20) do={ :set p ($p . \"R=/log|.id=\" . [$ktmEsc ($i->\".id\")] . \"|time=\" . [$ktmEsc ($i->\"time\")] . \"|topics=\" . [$ktmEsc ($i->\"topics\")] . \"|message=\" . [$ktmEsc ($i->\"message\")] . $NL); :set c ($c + 1); } } } on-error={};",
        send_line(),
        "  :set p (\"KETAMON_SNAPSHOT_V1\" . $NL);",
        "  :do { :foreach i in=[/system scheduler print as-value] do={ :set p ($p . \"R=/system/scheduler|.id=\" . [$ktmEsc ($i->\".id\")] . \"|name=\" . [$ktmEsc ($i->\"name\")] . \"|interval=\" . [$ktmEsc ($i->\"interval\")] . \"|disabled=\" . [$ktmEsc ($i->\"disabled\")] . \"|next-run=\" . [$ktmEsc ($i->\"next-run\")] . \"|on-event=\" . [$ktmEsc ($i->\"on-event\")] . $NL); } } on-error={};",
        send_line(),
        f"  :do {{ /tool fetch url=\"{ping_url}\" keep-result=no duration=10s; }} on-error={{}}",
        "  :for ktmCmd from=1 to=2 do={",
        f"    :do {{ /tool fetch url=\"{next_url}\" dst-path=\"ketamon-relay-next.rsc\" keep-result=yes duration=10s; :delay 1s; /import file-name=\"ketamon-relay-next.rsc\"; /file remove [find name=\"ketamon-relay-next.rsc\"]; }} on-error={{}}",
        "  }",
        "  } on-error={}",
        "  :set ktmBusy \"\";",
        "}",
        "/system scheduler add name=\"ketamon-relay-poll\" interval=30s on-event=\"/system script run ketamon-relay-poll\" disabled=no",
        "/system scheduler add name=\"ketamon-relay-watchdog\" interval=2m on-event=\":do { /system script run ketamon-relay-poll; } on-error={}\" disabled=no",
        f"/system scheduler add name=\"ketamon-relay-keepalive\" interval=1m on-event=\":do {{ /tool fetch url=\\\"{ping_url}\\\" keep-result=no duration=5s; }} on-error={{}}\" disabled=no",
        # Script de boot : réinstalle le relay automatiquement si les schedulers disparaissent (reset config, firmware update, etc.)
        ":do { /system script remove [find name=\"ketamon-relay-boot\"]; } on-error={}",
        ":do { /system scheduler remove [find name=\"ketamon-relay-boot\"]; } on-error={}",
        f"/system script add name=\"ketamon-relay-boot\" policy=ftp,reboot,read,write,policy,test,password,sniff,sensitive,romon source={{:global ktmBusy; :set ktmBusy \"\"; :local exists [/system scheduler find where name=\"ketamon-relay-poll\"]; :if ([:len $exists] = 0) do={{:do {{/tool fetch url=\"{base_url}/api/relay/routeros/install.rsc?token={token}\" dst-path=\"ketamon-relay-install.rsc\" duration=30s; :delay 2s; /import file-name=\"ketamon-relay-install.rsc\"; /file remove [find name=\"ketamon-relay-install.rsc\"]; }} on-error={{}}; }} }}",
        "/system scheduler add name=\"ketamon-relay-boot\" start-time=startup interval=5m on-event=\"/system script run ketamon-relay-boot\" disabled=no",
        ":delay 2s",
        ":do { /system script run ketamon-relay-poll; } on-error={}",
    ])


@app.route("/api/relay/routeros/install.rsc", methods=["GET"])
def api_relay_routeros_install_script():
    router, token = _relay_router_from_request()
    if not router:
        return ":put \"KetaMon relay: token invalide\"\n", 401, {"Content-Type": "text/plain; charset=utf-8"}
    print(
        "[RELAY][INSTALL] "
        f"router={router.get('name') or router.get('id')} script=safe-snapshot-v2",
        flush=True,
    )
    return _build_routeros_relay_script(_relay_public_base_url(), token) + "\n", 200, {
        "Content-Type": "text/plain; charset=utf-8",
        "Cache-Control": "no-store",
    }


@app.route("/api/relay/scripts/installer.rsc", methods=["GET"])
def api_relay_scripts_installer():
    """
    Sert le fichier .rsc qui installe ketamon-ticket-login et ketamon-ticket-expiry
    en utilisant la syntaxe source={...} — aucun quoting, aucun problème d'échappement.
    Authentifié par token relay.
    """
    router, _token = _relay_router_from_request()
    if not router:
        return "# KetaMon: token invalide\n", 401, {"Content-Type": "text/plain; charset=utf-8"}
    print(
        "[RELAY][INSTALLER] "
        f"router={router.get('name') or router.get('id')}",
        flush=True,
    )
    return _build_ketamon_installer_rsc() + "\n", 200, {
        "Content-Type": "text/plain; charset=utf-8",
        "Cache-Control": "no-store",
    }


@app.route("/parametres/routeurs/<rid>/relais", methods=["GET", "POST"])
@login_required
def router_relay_settings(rid):
    owner_id = _current_owner_id()
    router = db_mod.db_get_router(rid, owner_id)
    if not router:
        flash("Routeur introuvable ou non autorise.", "danger")
        return redirect(url_for("sessions_list"))

    if request.method == "POST":
        action = request.form.get("action", "").strip()
        if action == "enable":
            token = router.get("relay_token") or secrets.token_urlsafe(32)
            db_mod.db_set_router_relay(rid, owner_id, enabled=True, token=token)
            flash("Relais cloud active pour ce routeur.", "success")
        elif action == "disable":
            db_mod.db_set_router_relay(rid, owner_id, enabled=False)
            flash("Relais cloud desactive pour ce routeur.", "info")
        elif action == "rotate":
            db_mod.db_set_router_relay(rid, owner_id, enabled=True, token=secrets.token_urlsafe(32))
            flash("Nouveau token relais genere.", "success")
        elif action == "queue_ping":
            router = db_mod.db_get_router(rid, owner_id)
            if not int(router.get("relay_enabled") or 0):
                flash("Activez d'abord le relais cloud.", "warning")
            else:
                db_mod.db_enqueue_router_relay_command(rid, router.get("owner_id", ""), "ping", {"from": "web"})
                flash("Commande test envoyee. Le MikroTik la prendra au prochain polling.", "success")
        elif action == "queue_upgrade":
            router = db_mod.db_get_router(rid, owner_id)
            token = str((router or {}).get("relay_token") or "").strip()
            if not int((router or {}).get("relay_enabled") or 0) or not token:
                flash("Activez d'abord le relais cloud pour ce routeur.", "warning")
            else:
                command = db_mod.db_enqueue_router_relay_command(
                    rid,
                    router.get("owner_id", ""),
                    "routeros-script",
                    {"source": _relay_auto_upgrade_source(token), "from": "web-force-upgrade"},
                )
                if command:
                    flash("Mise a jour relais envoyee. Le MikroTik l'appliquera au prochain polling.", "success")
                else:
                    flash("Impossible de creer la commande de mise a jour relais.", "danger")
        return redirect(url_for("router_relay_settings", rid=rid))

    router = db_mod.db_get_router(rid, owner_id)
    commands = db_mod.db_get_router_relay_commands(rid, limit=12)
    base_url = _relay_public_base_url()
    install_script = ""
    install_url = ""
    bootstrap_command = ""
    if router.get("relay_token"):
        token = router.get("relay_token")
        install_url = f"{base_url}/api/relay/routeros/install.rsc?token={quote(token)}"
        bootstrap_command = (
            f'/tool fetch url="{install_url}" dst-path="ketamon-relay-install.rsc"; '
            '/import file-name="ketamon-relay-install.rsc"; '
            '/file remove [find name="ketamon-relay-install.rsc"]'
        )
        install_script = _build_routeros_relay_script(base_url, token)
    return render_template(
        "settings/relay_router.html",
        router=router,
        commands=commands,
        relay_base_url=base_url,
        install_url=install_url,
        bootstrap_command=bootstrap_command,
        install_script=install_script,
    )


@app.route("/parametres/routeurs/<rid>/supprimer", methods=["POST"])
@login_required
def delete_router(rid):
    owner_id = _current_owner_id()
    deleted = db_mod.db_delete_router(rid, owner_id=owner_id)
    if not deleted:
        flash("Routeur introuvable ou non autorise.", "danger")
        return redirect(url_for("sessions_list"))
    _invalidate_routers_cache()
    if session.get("router_id") == rid:
        session.pop("router_id", None)
        session.pop("router_name", None)
    flash("Routeur supprime.", "success")
    return redirect(url_for("sessions_list"))

@app.route("/parametres/routeurs/<rid>/modifier", methods=["GET", "POST"])
@login_required
def edit_router(rid):
    routers = get_routers()
    router  = next((r for r in routers if r["id"] == rid), None)
    if not router:
        flash("Routeur introuvable.", "danger")
        return redirect(url_for("sessions_list"))
    if request.method == "POST":
        new_host = request.form.get("host", router["host"]).strip()
        fallback_host = request.form.get("fallback_host", router.get("fallback_host", "")).strip()
        # Si on migre vers une adresse directe et qu'aucun secours n'est fourni,
        # on conserve l'ancien host comme fallback automatique.
        if not fallback_host and new_host and new_host != str(router.get("host", "")).strip():
            fallback_host = str(router.get("host", "")).strip()
        fields = {
            "name":     request.form.get("name", router["name"]).strip(),
            "host":     new_host,
            "fallback_host": fallback_host,
            "port":     request.form.get("port", router.get("port", 8728)),
            "user":     (request.form.get("user", router.get("user") or "admin").strip() or "admin"),
            "currency": request.form.get("currency", router.get("currency", "FCFA")).strip(),
        }
        pwd = request.form.get("password", "")
        if pwd:
            fields["password"] = pwd
        db_mod.db_update_router(rid, _current_owner_id(), fields)
        updated_router = dict(router)
        updated_router.update(fields)
        runtime_ok, runtime_msg = _apply_ticket_runtime_to_router(updated_router)
        if runtime_ok:
            flash("Routeur modifie et scripts d'expiration reinstalles.", "success")
        else:
            flash(
                "Routeur modifie. Le push direct des scripts MikroTik est en attente car l'API 8728 est inaccessible. "
                f"L'expiration serveur/fallback reste active. Detail: {runtime_msg}",
                "warning",
            )
        return redirect(url_for("sessions_list"))
    return render_template("settings/edit_router.html", router=router)

@app.route("/parametres/deconnecter-routeur")
@login_required
def disconnect_router():
    session.pop("router_id", None)
    session.pop("router_name", None)
    flash("Routeur deconnecte.", "info")
    return redirect(url_for("sessions_list"))

# ─── Parametres : Compte ─────────────────────────────────────────────────────

@app.route("/parametres/compte", methods=["GET", "POST"])
@login_required
def settings_account():
    if request.method == "POST":
        uid          = session.get("user_id", "")
        current_pass = request.form.get("current_password", "")
        new_pass     = request.form.get("new_password", "")
        confirm_pass = request.form.get("confirm_password", "")
        if not current_pass or not new_pass:
            flash("Tous les champs sont obligatoires.", "danger")
        elif new_pass != confirm_pass:
            flash("Les deux nouveaux mots de passe ne correspondent pas.", "danger")
        else:
            user_row = db_mod.db_get_local_user(uid)
            if not user_row:
                flash("Compte introuvable.", "danger")
            elif not check_password_hash(user_row.get("password", ""), current_pass):
                flash("Mot de passe actuel incorrect.", "danger")
            elif db_mod.db_update_local_user_password(uid, generate_password_hash(new_pass)):
                flash("Mot de passe modifie avec succes.", "success")
            else:
                flash("Erreur lors de la mise a jour.", "warning")
    return render_template("settings/account.html")

# ─── Upload Logo ─────────────────────────────────────────────────────────────

@app.route("/parametres/logo", methods=["GET", "POST"])
@login_required
def upload_logo():
    if request.method == "POST":
        f = request.files.get("logo")
        if f and f.filename:
            fname = secure_filename(f.filename)
            ext = os.path.splitext(fname)[1].lower()
            if ext not in ALLOWED_LOGO_EXT:
                flash("Type de fichier non autorise.", "danger")
            else:
                try:
                    f.save(os.path.join(LOGOS_DIR, fname))
                    flash(f"Logo \"{fname}\" uploade et applique aux tickets.", "success")
                except Exception as e:
                    _flash_err("Erreur lors de l upload du fichier.", e)
    logos = list_uploaded_logos()
    active_logo = get_active_ticket_logo()
    return render_template("settings/upload_logo.html", logos=logos, active_logo=active_logo)

@app.route("/logos/<filename>")
def serve_logo(filename):
    return send_from_directory(LOGOS_DIR, filename)

# ─── A propos ────────────────────────────────────────────────────────────────

@app.route("/a-propos")
@login_required
def about():
    import sys
    try:
        version = get_app_version()
    except Exception:
        version = "1.0.0"
    import flask as _fl
    return render_template("about.html",
        version=version,
        python_version=sys.version.split()[0],
        flask_version=_fl.__version__,
        active_router=get_active_router()
    )

@app.route("/contact")
def contact():
    return render_template("contact.html", active_router=None)

@app.route("/politique-de-confidentialite")
def privacy():
    return render_template("privacy.html", active_router=None)

@app.route("/sw.js")
def service_worker():
    sw_path = os.path.join(app.static_folder, "sw.js")
    try:
        with open(sw_path, encoding="utf-8") as f:
            body = f.read()
    except Exception:
        body = ""
    body = body.replace("__PWA_VERSION__", _get_pwa_ver())
    response = app.response_class(body, mimetype="application/javascript")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response

@app.route("/offline")
def offline_page():
    return render_template("offline.html"), 200


@app.route("/pwa-reset")
def pwa_reset_page():
    html = """<!doctype html>
<html lang="fr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>KetaMon - Reparation PWA</title>
<style>
body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:#0f172a;color:#f8fafc;font-family:Arial,sans-serif}
main{width:min(420px,calc(100% - 32px));background:#1f2937;border:1px solid #334155;border-radius:16px;padding:24px;text-align:center}
a,button{display:inline-block;margin-top:14px;background:#0ea5e9;color:#fff;border:0;border-radius:10px;padding:11px 16px;text-decoration:none;font-weight:700}
p{color:#cbd5e1}
</style>
</head>
<body>
<main>
<h1>KetaMon</h1>
<p>Nettoyage du cache PWA en cours...</p>
<button id="retry" type="button">Ouvrir la connexion</button>
</main>
<script>
(function(){
  function go(){ window.location.replace('/login?cache=cleaned&t=' + Date.now()); }
  document.getElementById('retry').addEventListener('click', go);
  var clearCaches = 'caches' in window
    ? caches.keys().then(function(keys){ return Promise.all(keys.map(function(k){ return caches.delete(k); })); }).catch(function(){})
    : Promise.resolve();
  var unregister = navigator.serviceWorker && navigator.serviceWorker.getRegistrations
    ? navigator.serviceWorker.getRegistrations().then(function(regs){ return Promise.all(regs.map(function(reg){ return reg.unregister(); })); }).catch(function(){})
    : Promise.resolve();
  Promise.all([clearCaches, unregister]).then(function(){ setTimeout(go, 300); });
})();
</script>
</body>
</html>"""
    response = app.response_class(html, mimetype="text/html")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response

# ─── API Log Hotspot (live dashboard) ────────────────────────────────────────

@app.route("/api/log-hotspot")
@login_required
@router_required
def api_log_hotspot():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err, "logs": []})
    try:
        all_logs = api.get_resource("/log").get()
        hs_logs = [l for l in all_logs if "hotspot" in l.get("topics", "")]
        hs_logs = list(reversed(hs_logs))[:20]
        out = []
        for l in hs_logs:
            msg = l.get("message", "")
            user = ""; ip = ""
            # Extraire user et IP du message type "user BXFBZ9455 logged in from 10.10.10.53"
            import re as _re
            m = _re.search(r"user\s+(\S+)", msg, _re.IGNORECASE)
            if m: user = m.group(1)
            m2 = _re.search(r"(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})", msg)
            if m2: ip = m2.group(1)
            out.append({"time": l.get("time",""), "message": msg, "user": user, "ip": ip})
        return jsonify({"ok": True, "logs": out})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e), "logs": []})

# ─── API Systeme Ressources (live) ────────────────────────────────────────────

@app.route("/api/ressources")
@login_required
@router_required
def api_resources():
    api, err = get_api()
    if err:
        return jsonify({"ok": False, "msg": err})
    try:
        res       = resource_first(api, "/system/resource")
        total_mem = int(res.get("total-memory", 1) or 1)
        free_mem  = int(res.get("free-memory", 0)  or 0)
        total_hdd = int(res.get("total-hdd-space", 0) or 0)
        free_hdd  = int(res.get("free-hdd-space",  0) or 0)
        try:
            rb    = resource_first(api, "/system/routerboard")
            board = rb.get("model", res.get("board-name", "—"))
        except Exception:
            board = res.get("board-name", "—")
        return jsonify({
            "ok":       True,
            "cpu":      res.get("cpu-load", "0"),
            "uptime":   res.get("uptime", ""),
            "version":  res.get("version", ""),
            "board":    board,
            "free_mem": mk.format_bytes(free_mem),
            "mem_pct":  round((total_mem - free_mem) / total_mem * 100) if total_mem else 0,
            "free_hdd": mk.format_bytes(free_hdd) if total_hdd else "—",
            "hdd_pct":  round((total_hdd - free_hdd) / total_hdd * 100) if total_hdd else 0,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/health")
def health_check():
    bg_thread = next((t for t in threading.enumerate() if t.name == "db-init"), None)
    return jsonify({
        "ok": True,
        "time": datetime.now().isoformat(),
        "db_ready": _db_ready.is_set(),
        "db_error": _db_init_error if not _db_ready.is_set() else None,
        "db_thread": bg_thread.is_alive() if bg_thread else None,
        "threads": [t.name for t in threading.enumerate()],
        "thread_count": threading.active_count(),
    })


# ─── API Android : tickets hotspot ───────────────────────────────────────────

@app.route("/api/ping")
def api_ping():
    """Test de connectivité + validation des identifiants pour l'app Android."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    return jsonify({"ok": True, "service": "ketamon"})


@app.route("/api/dashboard", methods=["GET"])
def api_dashboard():
    """Stats MikroTik en temps réel pour l'app Android (auth HTTP Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503

    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503

    try:
        res   = resource_first(api, "/system/resource")
        ident = resource_first(api, "/system/identity")
        hs_active  = resource_count(api, "/ip/hotspot/active")
        hs_tickets = resource_count(api, "/ip/hotspot/user")
        total_mem  = int(res.get("total-memory", 0))
        free_mem   = int(res.get("free-memory", 0))
        mem_pct    = round((total_mem - free_mem) / total_mem * 100) if total_mem else 0
        return jsonify({
            "ok":        True,
            "identity":  ident.get("name", "MikroTik"),
            "version":   res.get("version", "?"),
            "uptime":    res.get("uptime", "?"),
            "cpu_load":  str(res.get("cpu-load", "0")),
            "mem_pct":   mem_pct,
            "hs_active": hs_active,
            "hs_tickets": hs_tickets,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/vouchers", methods=["POST"])
def api_create_voucher():
    """Crée un ticket hotspot depuis l'app Android (auth HTTP Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    data    = request.get_json(silent=True) or {}
    code    = str(data.get("code", "")).strip()
    profile = str(data.get("profile", "default")).strip() or "default"
    uptime_raw = str(data.get("uptime", "") or data.get("time_limit", "")).strip()
    uptime = "1h"

    if not code or not re.match(r"^[A-Za-z0-9\-_]{1,64}$", code):
        return jsonify({"ok": False, "msg": "Code invalide"}), 400
    if not re.match(r"^\d+[smhd]$", uptime):
        return jsonify({"ok": False, "msg": "Format durée invalide (ex: 1h, 30m)"}), 400
    if not re.match(r"^[\w\-]{1,64}$", profile):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400

    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503

    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503

    try:
        try:
            ensure_ticket_runtime_support(api, profile)
        except Exception:
            pass  # Ne pas bloquer la création si les scripts échouent
        api.get_resource("/ip/hotspot/user").add(
            name=code,
            password=code,
            profile=profile,
            disabled="no",
            comment=f"vc-{datetime.now().strftime('%d/%m %H:%M')}",
            **{"limit-uptime": uptime}
        )
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/vouchers/summary", methods=["GET"])
def api_hotspot_vouchers_summary():
    """Résumé des bons de connexion par profil (nombre de tickets + métadonnées)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503
    try:
        users    = api.get_resource("/ip/hotspot/user").get()
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        router_id     = r.get("id", "") or r.get("host", "")
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        count_by_profil = {}
        for u in users:
            p = str(u.get("profile", "default")).strip()
            count_by_profil[p] = count_by_profil.get(p, 0) + 1
        result = [{"nom": "all", "count": len(users), "prix": "", "duree": ""}]
        for p in profiles:
            nom  = str(p.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val  = str(meta.get("price", "0") or "0")
            devise    = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            result.append({
                "nom":   nom,
                "count": count_by_profil.get(nom, 0),
                "prix":  f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else "",
            })
        return jsonify({"ok": True, "profiles": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/vouchers/generate", methods=["POST"])
def api_hotspot_vouchers_generate():
    """Génère N bons de connexion pour un profil depuis l'app Android."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data   = request.get_json(silent=True) or {}
    profil = str(data.get("profil", "default")).strip() or "default"
    qty    = safe_int(data.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
    if not re.match(r"^[\w\-]{1,64}$", profil):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503
    try:
        router_id         = r.get("id", "") or r.get("host", "")
        ticket_time_limit = get_profile_time_limit(router_id, profil) or "0"
        try:
            ensure_ticket_runtime_support(api, profil)
        except Exception:
            pass
        resource  = api.get_resource("/ip/hotspot/user")
        generated = []
        existing_names = set()
        gen_errors = []
        attempts = 0
        max_attempts = max(qty * 5, qty + 50)
        while len(generated) < qty and attempts < max_attempts:
            attempts += 1
            try:
                code = _next_unique_ticket_name(existing_names, "ABCDEFGHJKLMNPQRSTUVWXYZ23456789", 8, "")
            except ValueError as ex:
                gen_errors.append(str(ex))
                break
            try:
                resource.add(
                    name=code, password=code, profile=profil,
                    disabled="no",
                    comment=f"vc-{datetime.now().strftime('%d/%m %H:%M')}",
                    **{"limit-uptime": ticket_time_limit}
                )
                generated.append(code)
            except Exception as ex:
                gen_errors.append(str(ex))
                if _looks_like_duplicate_ticket_error(ex):
                    continue
                break
        return jsonify({
            "ok": len(generated) == qty,
            "codes": generated,
            "count": len(generated),
            "requested": qty,
            "msg": "" if len(generated) == qty else (gen_errors[-1] if gen_errors else "Generation partielle"),
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users", methods=["GET"])
def api_hotspot_users():
    """Liste les utilisateurs hotspot (tickets + sessions actives) depuis MikroTik."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503
    try:
        users    = api.get_resource("/ip/hotspot/user").get()
        sessions = api.get_resource("/ip/hotspot/active").get()
        active_by_user = {}
        for s in sessions:
            uname = str(s.get("user", "")).strip()
            if uname and uname not in active_by_user:
                active_by_user[uname] = s
        result = []
        for u in users:
            nom  = str(u.get("name", "")).strip()
            sess = active_by_user.get(nom)
            is_disabled = str(u.get("disabled", "no")).strip().lower() == "yes"
            if is_disabled:
                etat = "desactive"
            elif sess:
                etat = "actif"
            else:
                etat = "hors_ligne"
            mac = str(u.get("mac-address", "") or (sess.get("mac-address", "") if sess else ""))
            download_bytes, upload_bytes = _traffic_client_bytes(sess or {})
            result.append({
                "id":        str(u.get(".id", "")),
                "nom":       nom,
                "profil":    str(u.get("profile", "default")),
                "etat":      etat,
                "ip":        str(sess.get("address", "") if sess else ""),
                "mac":       mac,
                "bytesIn":   str(sess.get("bytes-in", "0") if sess else "0"),
                "bytesOut":  str(sess.get("bytes-out", "0") if sess else "0"),
                "downloadBytes": str(download_bytes or "0"),
                "uploadBytes": str(upload_bytes or "0"),
                "uptime":    str(sess.get("uptime", "") if sess else ""),
                "sessionId": str(sess.get(".id", "") if sess else ""),
            })
        return jsonify({"ok": True, "users": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users/disconnect", methods=["POST"])
def api_hotspot_disconnect():
    """Déconnecte un utilisateur actif du hotspot."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom  = str(data.get("nom", "")).strip()
    if not nom or not re.match(r"^[\w\-\.@]{1,64}$", nom):
        return jsonify({"ok": False, "msg": "Nom utilisateur invalide"}), 400
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503
    try:
        active_rows = find_matching_hotspot_active_rows(api, usernames=[nom])
        usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(active_rows)
        disconnected = disconnect_hotspot_entities(
            api, usernames=usernames or [nom],
            addresses=addresses, mac_addresses=mac_addresses, active_ids=active_ids,
        )
        return jsonify({"ok": True, "disconnected": disconnected})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/profiles", methods=["GET"])
def api_hotspot_profiles():
    """Liste les profils hotspot depuis MikroTik avec leurs métadonnées prix/durée."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503
    try:
        profiles      = api.get_resource("/ip/hotspot/user/profile").get()
        router_id     = r.get("id", "") or r.get("host", "")
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        result = []
        for p in profiles:
            nom  = str(p.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val  = str(meta.get("price", "0") or "0")
            devise    = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            result.append({
                "nom":   nom,
                "debit": str(p.get("rate-limit", "") or "illimité"),
                "prix":  f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else "",
            })
        return jsonify({"ok": True, "profiles": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/tickets/list", methods=["GET"])
def api_list_tickets():
    """Liste les tickets hotspot réels depuis MikroTik (auth HTTP Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503

    r = routers[0]
    api, err = _connect_router_universal(r)
    if err:
        return jsonify({"ok": False, "msg": "Routeur inaccessible : " + err}), 503

    try:
        users = api.get_resource("/ip/hotspot/user").get()
        tickets = []
        now = datetime.now()
        marker = KETAMON_TICKET_COMMENT_MARKER

        for u in users:
            comment  = str(u.get("comment", ""))
            duree_raw = str(u.get("limit-uptime", "0") or "0")
            statut   = "actif"
            expire_at = ""

            marker_pos = comment.find(marker)
            if marker_pos != -1:
                expire_raw = comment[marker_pos + len(marker):].strip()
                expire_dt = _parse_ketamon_expire(expire_raw)
                if expire_dt is not None:
                    expire_at = expire_dt.strftime("%d/%m %H:%M")
                    statut = "expire" if now >= expire_dt else "utilise"
                else:
                    statut = "utilise"

            clean_comment = strip_ticket_runtime_comment(comment)
            # Extraire la date de création du préfixe "vc-DD/MM HH:MM"
            if clean_comment.startswith("vc-"):
                cree_le = clean_comment[3:].strip()
            else:
                cree_le = clean_comment
            tickets.append({
                "code":      u.get("name", ""),
                "profil":    u.get("profile", "default"),
                "duree":     duree_raw,
                "cree_le":   cree_le,
                "statut":    statut,
                "expire_at": expire_at,
            })

        return jsonify({"ok": True, "tickets": tickets})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


# ─── Concepteur : Mise à jour de l'application ───────────────────────────────

VERSION_FILE = os.path.join(os.path.dirname(__file__), "data", "version.txt")

def get_app_version():
    try:
        with open(VERSION_FILE, encoding="utf-8") as f:
            return f.read().strip()
    except Exception:
        return "1.0.0"

def set_app_version(v):
    with open(VERSION_FILE, "w", encoding="utf-8") as f:
        f.write(str(v).strip())

@app.route("/api/version")
def api_version():
    """Endpoint public — retourne la version actuelle (pour auto-check dans le navigateur)."""
    return jsonify({"version": get_app_version(), "ok": True})


# ─── API Android : journaux, système, DHCP, interfaces, rapport ───────────────

def _mk_connect_first_router():
    """Connecte au premier routeur configuré. Retourne (api, erreur_str|None)."""
    routers = get_routers()
    if not routers:
        return None, "Aucun routeur configuré"
    r = routers[0]
    if int(r.get("relay_enabled") or 0):
        return RelaySnapshotApi(r), None
    api, err = mk.safe_connect_router(r)
    return (api, err) if not err else (None, err)


def _mk_connect_request_router(payload=None):
    """Connecte au routeur demandÃ© si prÃ©cisÃ©, sinon au routeur actif / premier disponible."""
    router = _get_requested_router(payload)
    if not router:
        return None, "Aucun routeur configurÃ©"
    if int(router.get("relay_enabled") or 0):
        return RelaySnapshotApi(router), None
    api, err = _connect_router_universal(router)
    return (api, err) if not err else (None, err)


def _mk_connect_first_router(payload=None):
    if payload is None:
        payload = request.get_json(silent=True) or request.form or request.args
    return _mk_connect_request_router(payload)


def _fmt_bytes(b):
    b = int(b or 0)
    if b >= 1_073_741_824: return f"{b/1_073_741_824:.1f} Go"
    if b >= 1_048_576:     return f"{b/1_048_576:.0f} Mo"
    if b >= 1_024:         return f"{b/1_024:.0f} Ko"
    return f"{b} o"


@app.route("/api/network/traffic", methods=["GET"])
def api_network_traffic():
    """Débit réseau en temps réel — différentiel mis en cache, aucun blocage."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    payload = request.get_json(silent=True) or request.form or request.args
    router = _get_requested_router(payload)
    if not router:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    router_id = str(router.get("id") or router.get("host") or "")
    api, err = _mk_connect_request_router(payload)
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        now = time.time()
        ifaces = {i.get("name", ""): i for i in api.get_resource("/interface").get()}
        result = []
        for nom, iface in ifaces.items():
            disabled = str(iface.get("disabled", "no")).lower() == "yes"
            running  = str(iface.get("running",  "no")).lower() == "yes"
            rx2 = int(iface.get("rx-byte", 0) or 0)
            tx2 = int(iface.get("tx-byte", 0) or 0)
            key  = f"{router_id}:{nom}"
            last = _last_iface_bytes.get(key)
            if last:
                prev_rx, prev_tx, prev_t = last
                elapsed = now - prev_t
                rx_bps = int(max(0, (rx2 - prev_rx) / elapsed)) if elapsed > 0 else 0
                tx_bps = int(max(0, (tx2 - prev_tx) / elapsed)) if elapsed > 0 else 0
            else:
                rx_bps = tx_bps = 0
            _last_iface_bytes[key] = (rx2, tx2, now)
            result.append({
                "nom":       nom,
                "actif":     running and not disabled,
                "desactive": disabled,
                "rxBps":     (_fmt_bytes(rx_bps) + "/s") if rx_bps > 0 else "0 o/s",
                "txBps":     (_fmt_bytes(tx_bps) + "/s") if tx_bps > 0 else "0 o/s",
                "_rx":      rx_bps,
                "_tx":      tx_bps,
            })
        max_bps = max((max(r["_rx"], r["_tx"]) for r in result), default=1) or 1
        for r in result:
            r["rxPct"] = min(100, round(r["_rx"] / max_bps * 100))
            r["txPct"] = min(100, round(r["_tx"] / max_bps * 100))
            del r["_rx"]; del r["_tx"]
        return jsonify({"ok": True, "interfaces": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


@app.route("/api/network/ping", methods=["GET"])
def api_network_ping():
    """Ping depuis MikroTik vers une cible (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    hote  = request.args.get("hote", "").strip()
    count = min(safe_int(request.args.get("count", 4), default=4, min_val=1, max_val=10), 10)
    if not hote:
        return jsonify({"ok": False, "msg": "Hôte obligatoire"}), 400
    if not re.match(r'^[\w.\-:]+$', hote):
        return jsonify({"ok": False, "msg": "Cible invalide"}), 400
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        # api.get_resource("") -> _Resource(lrt, "") -> call("ping") -> /ping
        raw = api.get_resource("").call("ping", {"address": hote, "count": str(count)})
        resultats = []
        resume    = {}
        seq = 1
        for r in raw:
            if "time" in r or "status" in r:
                tmo = str(r.get("status", "")).lower() == "timeout" or not r.get("time")
                resultats.append({
                    "seq":    seq,
                    "delai":  str(r.get("time", "timeout")) if not tmo else "timeout",
                    "statut": "timeout" if tmo else "ok",
                    "ttl":    str(r.get("ttl", "")),
                    "taille": str(r.get("size", "64"))
                })
                seq += 1
            elif "sent" in r or "received" in r:
                resume = {
                    "envoyes": str(r.get("sent", count)),
                    "recus":   str(r.get("received", 0)),
                    "pertes":  str(r.get("packet-loss", "?")),
                    "minRtt":  str(r.get("min-rtt", "")),
                    "avgRtt":  str(r.get("avg-rtt", "")),
                    "maxRtt":  str(r.get("max-rtt", ""))
                }
        if not resume and resultats:
            recus = sum(1 for r in resultats if r["statut"] == "ok")
            resume = {
                "envoyes": str(len(resultats)),
                "recus":   str(recus),
                "pertes":  f"{(len(resultats) - recus) * 100 // len(resultats)}%" if resultats else "?",
                "minRtt": "", "avgRtt": "", "maxRtt": ""
            }
        return jsonify({"ok": True, "hote": hote, "resultats": resultats, "resume": resume})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/logs", methods=["GET"])
def api_logs():
    """Journal MikroTik temps réel (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    limit = min(safe_int(request.args.get("limit", 150), default=150, min_val=1, max_val=500), 500)
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        entries = api.get_resource("/log").get()
        result = []
        for e in reversed(entries[-limit:]):
            topics = str(e.get("topics", ""))
            if "error" in topics or "critical" in topics:
                type_ = "erreur"
            elif "warning" in topics:
                type_ = "avertissement"
            else:
                type_ = "info"
            result.append({
                "temps":   str(e.get("time", "")),
                "message": str(e.get("message", "")),
                "topics":  topics,
                "type":    type_
            })
        return jsonify({"ok": True, "entries": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/system/info", methods=["GET"])
def api_system_info():
    """Informations système détaillées MikroTik (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res   = resource_first(api, "/system/resource")
        ident = resource_first(api, "/system/identity")
        total_mem = int(res.get("total-memory", 0) or 0)
        free_mem  = int(res.get("free-memory",  0) or 0)
        total_hdd = int(res.get("total-hdd-space", 0) or 0)
        free_hdd  = int(res.get("free-hdd-space",  0) or 0)
        ram_pct   = round((total_mem - free_mem) / total_mem * 100) if total_mem else 0
        modele = str(res.get("board-name", ""))
        try:
            rb = resource_first(api, "/system/routerboard")
            modele = str(rb.get("model", modele))
        except Exception:
            pass
        return jsonify({
            "ok":            True,
            "identite":      str(ident.get("name", "MikroTik")),
            "version":       str(res.get("version", "?")),
            "uptime":        str(res.get("uptime", "?")),
            "architecture":  str(res.get("architecture-name", "?")),
            "modele":        modele,
            "cpuLoad":       str(res.get("cpu-load", "0")),
            "ramTotal":      _fmt_bytes(total_mem),
            "ramLibre":      _fmt_bytes(free_mem),
            "ramPct":        ram_pct,
            "stockageTotal": _fmt_bytes(total_hdd) if total_hdd else "",
            "stockageLibre": _fmt_bytes(free_hdd)  if total_hdd else "",
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/dhcp/leases", methods=["GET"])
def api_dhcp_leases():
    """Baux DHCP actifs depuis MikroTik (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        leases = api.get_resource("/ip/dhcp-server/lease").get()
        result = []
        for l in leases:
            result.append({
                "id":      str(l.get(".id", "")),
                "ip":      str(l.get("active-address", "") or l.get("address", "")),
                "mac":     str(l.get("mac-address", "")),
                "nomHote": str(l.get("host-name", "") or l.get("active-host-name", "") or "—"),
                "statut":  str(l.get("status", "waiting")),
                "expireAt":str(l.get("expires-after", "")),
                "serveur": str(l.get("server", ""))
            })
        return jsonify({"ok": True, "leases": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/network/interfaces", methods=["GET"])
def api_network_interfaces():
    """Interfaces réseau MikroTik avec compteurs trafic (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        interfaces = api.get_resource("/interface").get()
        result = []
        for iface in interfaces:
            disabled = str(iface.get("disabled", "no")).lower() == "yes"
            running  = str(iface.get("running",  "no")).lower() == "yes"
            result.append({
                "nom":        str(iface.get("name", "")),
                "type":       str(iface.get("type", "")),
                "actif":      running and not disabled,
                "desactive":  disabled,
                "rxBytes":    str(iface.get("rx-byte", "0") or "0"),
                "txBytes":    str(iface.get("tx-byte", "0") or "0"),
                "mac":        str(iface.get("mac-address", "")),
                "commentaire":str(iface.get("comment", ""))
            })
        return jsonify({"ok": True, "interfaces": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/rapport", methods=["GET"])
def api_rapport():
    """Rapport agrégé hotspot depuis MikroTik (auth Basic requise)."""
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        users    = api.get_resource("/ip/hotspot/user").get()
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        active   = api.get_resource("/ip/hotspot/active").get()
        marker   = KETAMON_TICKET_COMMENT_MARKER
        now      = datetime.now()
        actifs = utilises = expires = 0
        count_by_profil = {}
        for u in users:
            comment = str(u.get("comment", ""))
            profil  = str(u.get("profile", "default"))
            count_by_profil[profil] = count_by_profil.get(profil, 0) + 1
            if marker in comment:
                expire_raw = comment[comment.find(marker) + len(marker):].strip()
                expire_dt = _parse_ketamon_expire(expire_raw)
                if expire_dt is not None and now >= expire_dt:
                    expires += 1
                else:
                    utilises += 1
            else:
                actifs += 1
        routers = get_routers()
        router_id     = (routers[0].get("id", "") or routers[0].get("host", "")) if routers else ""
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        par_profil = []
        for p in profiles:
            nom  = str(p.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val  = str(meta.get("price", "0") or "0")
            devise    = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            par_profil.append({
                "nom":   nom,
                "count": count_by_profil.get(nom, 0),
                "prix":  f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else ""
            })
        return jsonify({
            "ok":              True,
            "ticketsActifs":   actifs,
            "ticketsUtilises": utilises,
            "ticketsExpires":  expires,
            "ticketsTotal":    len(users),
            "usersActifs":     len(active),
            "parProfil":       par_profil
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


# ─── API Android : endpoints supplémentaires ─────────────────────────────────

@app.route("/api/hotspot/active", methods=["GET"])
def api_hotspot_active():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        sessions = api.get_resource("/ip/hotspot/active").get()
        result = []
        for s in sessions:
            download_bytes, upload_bytes = _traffic_client_bytes(s)
            result.append({
                "id":       str(s.get(".id", "")),
                "nom":      str(s.get("user", "")),
                "mac":      str(s.get("mac-address", "")),
                "ip":       str(s.get("address", "")),
                "serveur":  str(s.get("server", "")),
                "uptime":   str(s.get("uptime", "")),
                "bytesIn":  str(s.get("bytes-in", "0")),
                "bytesOut": str(s.get("bytes-out", "0")),
                "downloadBytes": str(download_bytes or "0"),
                "uploadBytes": str(upload_bytes or "0"),
                "loginBy":  str(s.get("login-by", "")),
            })
        return jsonify({"ok": True, "sessions": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/hosts", methods=["GET"])
def api_hotspot_hosts():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        hosts = api.get_resource("/ip/hotspot/host").get()
        result = []
        for h in hosts:
            result.append({
                "id":      str(h.get(".id", "")),
                "mac":     str(h.get("mac-address", "")),
                "ip":      str(h.get("address", "")),
                "serveur": str(h.get("server", "")),
                "bypass":  str(h.get("to-address", "")),
            })
        return jsonify({"ok": True, "hosts": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/ip-bindings", methods=["GET"])
def api_hotspot_ip_bindings():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        bindings = api.get_resource("/ip/hotspot/ip-binding").get()
        result = []
        for b in bindings:
            result.append({
                "id":     str(b.get(".id", "")),
                "mac":    str(b.get("mac-address", "")),
                "ip":     str(b.get("address", "")),
                "toIp":   str(b.get("to-address", "")),
                "server": str(b.get("server", "")),
                "type":   str(b.get("type", "")),
                "actif":  str(b.get("disabled", "no")).lower() != "yes",
            })
        return jsonify({"ok": True, "bindings": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/cookies", methods=["GET"])
def api_hotspot_cookies():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        cookies = api.get_resource("/ip/hotspot/cookie").get()
        result = []
        for c in cookies:
            result.append({
                "id":     str(c.get(".id", "")),
                "nom":    str(c.get("user", "")),
                "mac":    str(c.get("mac-address", "")),
                "cookie": str(c.get("cookie", "")),
                "expiry": str(c.get("expires-in", "")),
            })
        return jsonify({"ok": True, "cookies": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/system/scheduler", methods=["GET"])
def api_system_scheduler():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        tasks = api.get_resource("/system/scheduler").get()
        result = []
        for t in tasks:
            result.append({
                "id":        str(t.get(".id", "")),
                "nom":       str(t.get("name", "")),
                "startTime": str(t.get("start-time", "")),
                "startDate": str(t.get("start-date", "")),
                "interval":  str(t.get("interval", "")),
                "actif":     str(t.get("disabled", "no")).lower() != "yes",
                "script":    str(t.get("on-event", ""))[:200],
            })
        return jsonify({"ok": True, "taches": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users/add", methods=["POST"])
def api_hotspot_users_add():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    password = str(data.get("userPassword", "") or data.get("password", "")).strip()
    profil = str(data.get("profile", "") or data.get("profil", "default")).strip() or "default"
    server = str(data.get("server", "") or data.get("serveur", "")).strip()
    comment = str(data.get("comment", "") or data.get("commentaire", "")).strip()
    limit_uptime = str(data.get("limitUptime", "") or data.get("limit-uptime", "")).strip()
    if not nom or not re.match(r"^[\w\-\.@]{1,64}$", nom):
        return jsonify({"ok": False, "msg": "Nom invalide"}), 400
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    router = routers[0]
    router_id = router.get("id", "") or router.get("host", "")
    api, err = _connect_router_universal(router)
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        try:
            ensure_ticket_runtime_support(api, profil)
        except Exception:
            pass
        res = api.get_resource("/ip/hotspot/user")
        resolved_limit = resolve_ticket_time_limit(router_id, profil, limit_uptime) or "0"
        params = {"name": nom, "profile": profil, "password": password or nom, "disabled": "no", "limit-uptime": resolved_limit}
        if server:
            params["server"] = server
        if comment:
            params["comment"] = comment
        res.add(**params)
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} ajouté"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users/delete", methods=["POST"])
def api_hotspot_users_delete():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res = api.get_resource("/ip/hotspot/user")
        rows = _resource_rows_by_id_or_name(res, item_id=nom, name=nom)
        if not rows:
            return jsonify({"ok": False, "msg": "Utilisateur introuvable"}), 404
        router_resource_remove_by_id_or_name(api, "/ip/hotspot/user", item_id=router_action_ref(rows[0], "name"), name=nom)
        try:
            db_mod.db_delete_ticket_pricing(session.get("router_id", ""), [nom])
        except Exception:
            pass
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} supprimé"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users/toggle", methods=["POST"])
def api_hotspot_users_toggle():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res = api.get_resource("/ip/hotspot/user")
        rows = _resource_rows_by_id_or_name(res, item_id=nom, name=nom)
        if not rows:
            return jsonify({"ok": False, "msg": "Utilisateur introuvable"}), 404
        uid = router_action_ref(rows[0], "name")
        username = str(rows[0].get("name") or "").strip() or nom
        disable_req = data.get("disabled", data.get("disable", None))
        if disable_req is None:
            disable_req = str(rows[0].get("disabled", "no")).lower() != "yes"
        elif isinstance(disable_req, str):
            disable_req = disable_req.lower() in ("yes", "true", "1")
        router_resource_set_by_id_or_name(api, "/ip/hotspot/user", {"disabled": "yes" if disable_req else "no"}, item_id=uid, name=username)
        disconnected = {"active_sessions": 0, "cookies": 0, "hosts": 0}
        if disable_req:
            remaining_active = find_matching_hotspot_active_rows(api, usernames=[username])
            for _ in range(3):
                usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(remaining_active)
                batch = disconnect_hotspot_entities(
                    api,
                    usernames=usernames or [username],
                    addresses=addresses,
                    mac_addresses=mac_addresses,
                    active_ids=active_ids,
                )
                for key, value in batch.items():
                    disconnected[key] += int(value or 0)
                remaining_active = find_matching_hotspot_active_rows(
                    api,
                    usernames=usernames or [username],
                    addresses=addresses,
                    mac_addresses=mac_addresses,
                )
                if not remaining_active:
                    return jsonify({
                        "ok": True,
                        "msg": f"Utilisateur {nom} désactivé et accès coupé",
                        "disconnected": disconnected,
                    })
                time.sleep(0.2)
            return jsonify({
                "ok": False,
                "msg": f"Utilisateur {nom} désactivé, mais la session est encore active",
                "disconnected": disconnected,
            }), 409
        state = "désactivé" if disable_req else "activé"
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} {state}", "disconnected": disconnected})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/users/edit", methods=["POST"])
def api_hotspot_users_edit():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    routers = get_routers()
    if not routers:
        return jsonify({"ok": False, "msg": "Aucun routeur configuré"}), 503
    router = routers[0]
    router_id = router.get("id", "") or router.get("host", "")
    api, err = _connect_router_universal(router)
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res = api.get_resource("/ip/hotspot/user")
        rows = res.get(**{"name": nom})
        if not rows:
            return jsonify({"ok": False, "msg": "Utilisateur introuvable"}), 404
        uid = rows[0][".id"]
        params = {"id": uid}
        new_name = str(data.get("newName", "")).strip()
        if new_name and new_name != nom:
            params["name"] = new_name
        pwd = str(data.get("userPassword", "") or data.get("password", "")).strip()
        if pwd:
            params["password"] = pwd
        profil = str(data.get("profile", "") or data.get("profil", "")).strip()
        effective_profile = profil or str(rows[0].get("profile", "")).strip() or "default"
        if profil:
            try:
                ensure_ticket_runtime_support(api, effective_profile)
            except Exception:
                pass
            params["profile"] = profil
        comment = str(data.get("comment", "") or data.get("commentaire", "")).strip()
        if comment:
            params["comment"] = comment
        tlimit = str(data.get("limitUptime", "") or data.get("limit-uptime", "")).strip()
        if tlimit:
            params["limit-uptime"] = resolve_ticket_time_limit(router_id, effective_profile, tlimit) or "0"
        res.set(**params)
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} modifié"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/profiles/add", methods=["POST"])
def api_hotspot_profiles_add():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("profileName", "") or data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res = api.get_resource("/ip/hotspot/user/profile")
        params = {"name": nom, "shared-users": str(data.get("sharedUsers", "1") or "1")}
        if data.get("rateLimit"):
            params["rate-limit"] = str(data["rateLimit"])
        if data.get("addressPool"):
            params["address-pool"] = str(data["addressPool"])
        res.add(**params)
        routers = get_routers()
        if routers:
            rid = routers[0].get("id", "") or routers[0].get("host", "")
            try:
                db_mod.db_upsert_hotspot_profile_metadata(
                    rid, nom,
                    price=str(data.get("priceCfa", "0") or "0"),
                    currency=str(data.get("currency", "FCFA") or "FCFA"),
                    expire_mode=str(data.get("expiredMode", "none") or "none"),
                    lock_user="yes",
                    time_limit="0",
                )
            except Exception:
                pass
        return jsonify({"ok": True, "msg": f"Profil {nom} ajouté"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


@app.route("/api/hotspot/profiles/delete", methods=["POST"])
def api_hotspot_profiles_delete():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    api, err = _mk_connect_first_router()
    if err:
        return jsonify({"ok": False, "msg": err}), 503
    try:
        res = api.get_resource("/ip/hotspot/user/profile")
        rows = _resource_rows_by_id_or_name(res, item_id=nom, name=nom)
        if not rows:
            return jsonify({"ok": False, "msg": "Profil introuvable"}), 404
        router_resource_remove_by_id_or_name(api, "/ip/hotspot/user/profile", item_id=router_action_ref(rows[0], "name"), name=nom)
        try:
            db_mod.db_delete_hotspot_profile_metadata(session.get("router_id", ""), nom)
        except Exception:
            pass
        return jsonify({"ok": True, "msg": f"Profil {nom} supprimé"})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500


def _api_pick_router(payload=None):
    router = _get_requested_router(payload)
    if not router:
        return None, (jsonify({"ok": False, "msg": "Aucun routeur configurÃ©"}), 503)
    return router, None


def _api_connect_router(router):
    if int((router or {}).get("relay_enabled") or 0):
        return RelaySnapshotApi(router), None
    api, err = _connect_router_universal(router)
    if err or not api:
        return None, (jsonify({"ok": False, "msg": "Routeur inaccessible : " + str(err or "")}), 503)
    return api, None


def api_dashboard_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        res = resource_first(api, "/system/resource")
        ident = resource_first(api, "/system/identity")
        hs_active = resource_count(api, "/ip/hotspot/active")
        hs_tickets = resource_count(api, "/ip/hotspot/user")
        total_mem = int(res.get("total-memory", 0))
        free_mem = int(res.get("free-memory", 0))
        mem_pct = round((total_mem - free_mem) / total_mem * 100) if total_mem else 0
        return jsonify({
            "ok": True,
            "identity": ident.get("name", "MikroTik"),
            "version": res.get("version", "?"),
            "uptime": res.get("uptime", "?"),
            "cpu_load": str(res.get("cpu-load", "0")),
            "mem_pct": mem_pct,
            "hs_active": hs_active,
            "hs_tickets": hs_tickets,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_create_voucher_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    code = str(data.get("code", "")).strip()
    profile = str(data.get("profile", "default")).strip() or "default"
    uptime_raw = str(data.get("uptime", "") or data.get("time_limit", "")).strip()
    if not code or not re.match(r"^[A-Za-z0-9\-_]{1,64}$", code):
        return jsonify({"ok": False, "msg": "Code invalide"}), 400
    if not re.match(r"^[\w\-]{1,64}$", profile):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        router_id = router.get("id", "") or router.get("host", "")
        wifi_name = str(data.get("wifi_name", "") or data.get("network_name", "") or data.get("network", "")).strip()[:64]
        if wifi_name:
            db_mod.db_update_router(router_id, _current_owner_id(), {"wifi_name": wifi_name})
            _invalidate_routers_cache()
        else:
            wifi_name = str(router.get("wifi_name", "") or "")
        uptime = resolve_ticket_time_limit(router_id, profile, uptime_raw) or "0"
        try:
            ensure_ticket_runtime_support(api, profile)
        except Exception:
            pass
        api.get_resource("/ip/hotspot/user").add(
            name=code,
            password=code,
            profile=profile,
            disabled="no",
            comment=f"vc-{datetime.now().strftime('%d/%m %H:%M')}",
            **{"limit-uptime": uptime},
        )
        return jsonify({
            "ok": True,
            "code": code,
            "profile": profile,
            "time_limit": normalize_ticket_time_limit(uptime) or "0",
            "wifi_name": wifi_name,
            "network": wifi_name,
            "router_id": router_id,
        })
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)}), 400
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_vouchers_summary_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        users = api.get_resource("/ip/hotspot/user").get()
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        router_id = router.get("id", "") or router.get("host", "")
        wifi_name = str(router.get("wifi_name", "") or "")
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        count_by_profil = {}
        for user in users:
            profil = str(user.get("profile", "default")).strip()
            count_by_profil[profil] = count_by_profil.get(profil, 0) + 1
        result = [{"nom": "all", "count": len(users), "prix": "", "duree": ""}]
        for profile_row in profiles:
            nom = str(profile_row.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val = str(meta.get("price", "0") or "0")
            devise = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            result.append({
                "nom": nom,
                "count": count_by_profil.get(nom, 0),
                "prix": f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else "",
            })
        return jsonify({"ok": True, "profiles": result, "wifi_name": wifi_name, "network": wifi_name, "router_id": router_id})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_vouchers_generate_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    profil = str(data.get("profil", "default")).strip() or "default"
    qty = safe_int(data.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
    if not re.match(r"^[\w\-]{1,64}$", profil):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        router_id = router.get("id", "") or router.get("host", "")
        wifi_name = str(data.get("wifi_name", "") or data.get("network_name", "") or data.get("network", "")).strip()[:64]
        if wifi_name:
            db_mod.db_update_router(router_id, _current_owner_id(), {"wifi_name": wifi_name})
            _invalidate_routers_cache()
        else:
            wifi_name = str(router.get("wifi_name", "") or "")
        ticket_time_limit = resolve_ticket_time_limit(router_id, profil, "") or "0"
        try:
            ensure_ticket_runtime_support(api, profil)
        except Exception:
            pass
        resource = api.get_resource("/ip/hotspot/user")
        generated = []
        generated_tickets = []
        existing_names = set()
        gen_errors = []
        attempts = 0
        max_attempts = max(qty * 5, qty + 50)
        while len(generated) < qty and attempts < max_attempts:
            attempts += 1
            try:
                code = _next_unique_ticket_name(existing_names, "ABCDEFGHJKLMNPQRSTUVWXYZ23456789", 8, "")
            except ValueError as ex:
                gen_errors.append(str(ex))
                break
            try:
                resource.add(
                    name=code,
                    password=code,
                    profile=profil,
                    disabled="no",
                    comment=f"vc-{datetime.now().strftime('%d/%m %H:%M')}",
                    **{"limit-uptime": ticket_time_limit},
                )
                generated.append(code)
                generated_tickets.append({
                    "code": code,
                    "profile": profil,
                    "time_limit": normalize_ticket_time_limit(ticket_time_limit) or "0",
                    "wifi_name": wifi_name,
                    "network": wifi_name,
                })
            except Exception as ex:
                gen_errors.append(str(ex))
                if _looks_like_duplicate_ticket_error(ex):
                    continue
                break
        return jsonify({
            "ok": len(generated) == qty,
            "codes": generated,
            "tickets": generated_tickets,
            "count": len(generated),
            "requested": qty,
            "msg": "" if len(generated) == qty else (gen_errors[-1] if gen_errors else "Generation partielle"),
            "profile": profil,
            "time_limit": normalize_ticket_time_limit(ticket_time_limit) or "0",
            "wifi_name": wifi_name,
            "network": wifi_name,
            "router_id": router_id,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_users_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        users = api.get_resource("/ip/hotspot/user").get()
        sessions = api.get_resource("/ip/hotspot/active").get()
        active_by_user = {}
        for session_row in sessions:
            uname = str(session_row.get("user", "")).strip()
            if uname and uname not in active_by_user:
                active_by_user[uname] = session_row
        result = []
        for user in users:
            nom = str(user.get("name", "")).strip()
            sess = active_by_user.get(nom)
            is_disabled = str(user.get("disabled", "no")).strip().lower() == "yes"
            if is_disabled:
                etat = "desactive"
            elif sess:
                etat = "actif"
            else:
                etat = "hors_ligne"
            mac = str(user.get("mac-address", "") or (sess.get("mac-address", "") if sess else ""))
            download_bytes, upload_bytes = _traffic_client_bytes(sess or {})
            result.append({
                "id": str(user.get(".id", "")),
                "nom": nom,
                "profil": str(user.get("profile", "default")),
                "etat": etat,
                "ip": str(sess.get("address", "") if sess else ""),
                "mac": mac,
                "bytesIn": str(sess.get("bytes-in", "0") if sess else "0"),
                "bytesOut": str(sess.get("bytes-out", "0") if sess else "0"),
                "downloadBytes": str(download_bytes or "0"),
                "uploadBytes": str(upload_bytes or "0"),
                "uptime": str(sess.get("uptime", "") if sess else ""),
                "limitUptime": normalize_ticket_time_limit(user.get("limit-uptime")) or "0",
                "sessionId": str(sess.get(".id", "") if sess else ""),
            })
        return jsonify({"ok": True, "users": result})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_disconnect_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("nom", "")).strip()
    if not nom or not re.match(r"^[\w\-\.@]{1,64}$", nom):
        return jsonify({"ok": False, "msg": "Nom utilisateur invalide"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        active_rows = find_matching_hotspot_active_rows(api, usernames=[nom])
        usernames, addresses, mac_addresses, active_ids = build_active_disconnect_targets(active_rows)
        disconnected = disconnect_hotspot_entities(
            api,
            usernames=usernames or [nom],
            addresses=addresses,
            mac_addresses=mac_addresses,
            active_ids=active_ids,
        )
        return jsonify({"ok": True, "disconnected": disconnected})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_profiles_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        router_id = router.get("id", "") or router.get("host", "")
        wifi_name = str(router.get("wifi_name", "") or "")
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        result = []
        for profile_row in profiles:
            nom = str(profile_row.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val = str(meta.get("price", "0") or "0")
            devise = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            result.append({
                "nom": nom,
                "debit": str(profile_row.get("rate-limit", "") or "illimitÃ©"),
                "prix": f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else "",
            })
        return jsonify({"ok": True, "profiles": result, "wifi_name": wifi_name, "network": wifi_name, "router_id": router_id})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_list_tickets_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        users = api.get_resource("/ip/hotspot/user").get()
        wifi_name = str(router.get("wifi_name", "") or "")
        tickets = []
        now = datetime.now()
        for user in users:
            comment = str(user.get("comment", ""))
            duree_raw = normalize_ticket_time_limit(str(user.get("limit-uptime", "0") or "0")) or "0"
            expire_dt = _extract_ketamon_expire_datetime(comment)
            statut = "actif"
            expire_at = ""
            if expire_dt is not None:
                expire_at = expire_dt.strftime("%d/%m %H:%M")
                statut = "expire" if now >= expire_dt else "utilise"
            clean_comment = strip_ticket_runtime_comment(comment)
            cree_le = clean_comment[3:].strip() if clean_comment.startswith("vc-") else clean_comment
            tickets.append({
                "code": user.get("name", ""),
                "profil": user.get("profile", "default"),
                "duree": duree_raw,
                "cree_le": cree_le,
                "statut": statut,
                "expire_at": expire_at,
                "wifi_name": wifi_name,
                "network": wifi_name,
            })
        return jsonify({"ok": True, "tickets": tickets, "wifi_name": wifi_name, "network": wifi_name})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_rapport_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    router, error_response = _api_pick_router()
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        users = api.get_resource("/ip/hotspot/user").get()
        profiles = api.get_resource("/ip/hotspot/user/profile").get()
        active = api.get_resource("/ip/hotspot/active").get()
        now = datetime.now()
        actifs = utilises = expires = 0
        count_by_profil = {}
        for user in users:
            comment = str(user.get("comment", ""))
            profil = str(user.get("profile", "default"))
            count_by_profil[profil] = count_by_profil.get(profil, 0) + 1
            expire_dt = _extract_ketamon_expire_datetime(comment)
            if expire_dt is not None:
                if now >= expire_dt:
                    expires += 1
                else:
                    utilises += 1
            else:
                actifs += 1
        router_id = router.get("id", "") or router.get("host", "")
        profiles_meta = get_hotspot_profile_metadata_map(router_id)
        par_profil = []
        for profile_row in profiles:
            nom = str(profile_row.get("name", "")).strip()
            meta = profiles_meta.get(nom, {})
            prix_val = str(meta.get("price", "0") or "0")
            devise = str(meta.get("currency", "FCFA") or "FCFA")
            duree_val = normalize_profile_time_limit(str(meta.get("time_limit", "0") or "0")) or "0"
            par_profil.append({
                "nom": nom,
                "count": count_by_profil.get(nom, 0),
                "prix": f"{prix_val} {devise}" if prix_val != "0" else "",
                "duree": duree_val if duree_val != "0" else "",
            })
        return jsonify({
            "ok": True,
            "ticketsActifs": actifs,
            "ticketsUtilises": utilises,
            "ticketsExpires": expires,
            "ticketsTotal": len(users),
            "usersActifs": len(active),
            "parProfil": par_profil,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_users_add_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    password = str(data.get("userPassword", "") or data.get("password", "")).strip()
    profil = str(data.get("profile", "") or data.get("profil", "default")).strip() or "default"
    server = str(data.get("server", "") or data.get("serveur", "")).strip()
    comment = str(data.get("comment", "") or data.get("commentaire", "")).strip()
    limit_uptime = str(data.get("limitUptime", "") or data.get("limit-uptime", "")).strip()
    if not nom or not re.match(r"^[\w\-\.@]{1,64}$", nom):
        return jsonify({"ok": False, "msg": "Nom invalide"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        router_id = router.get("id", "") or router.get("host", "")
        try:
            ensure_ticket_runtime_support(api, profil)
        except Exception:
            pass
        resolved_limit = resolve_ticket_time_limit(router_id, profil, limit_uptime) or "0"
        params = {"name": nom, "profile": profil, "password": password or nom, "disabled": "no", "limit-uptime": resolved_limit}
        if server:
            params["server"] = server
        if comment:
            params["comment"] = comment
        api.get_resource("/ip/hotspot/user").add(**params)
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} ajoutÃ©"})
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)}), 400
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_users_edit_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        router_id = router.get("id", "") or router.get("host", "")
        res = api.get_resource("/ip/hotspot/user")
        rows = res.get(**{"name": nom})
        if not rows:
            return jsonify({"ok": False, "msg": "Utilisateur introuvable"}), 404
        uid = rows[0][".id"]
        params = {"id": uid}
        new_name = str(data.get("newName", "")).strip()
        if new_name and new_name != nom:
            params["name"] = new_name
        pwd = str(data.get("userPassword", "") or data.get("password", "")).strip()
        if pwd:
            params["password"] = pwd
        profil = str(data.get("profile", "") or data.get("profil", "")).strip()
        effective_profile = profil or str(rows[0].get("profile", "")).strip() or "default"
        if profil:
            try:
                ensure_ticket_runtime_support(api, effective_profile)
            except Exception:
                pass
            params["profile"] = profil
        comment = str(data.get("comment", "") or data.get("commentaire", "")).strip()
        if comment:
            params["comment"] = comment
        tlimit = str(data.get("limitUptime", "") or data.get("limit-uptime", "")).strip()
        if tlimit:
            params["limit-uptime"] = resolve_ticket_time_limit(router_id, effective_profile, tlimit) or "0"
        res.set(**params)
        return jsonify({"ok": True, "msg": f"Utilisateur {nom} modifiÃ©"})
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)}), 400
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_profiles_add_v2():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401
    data = request.get_json(silent=True) or {}
    nom = str(data.get("profileName", "") or data.get("name", "") or data.get("nom", "")).strip()
    if not nom:
        return jsonify({"ok": False, "msg": "Nom requis"}), 400
    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response
    api, error_response = _api_connect_router(router)
    if error_response:
        return error_response
    try:
        res = api.get_resource("/ip/hotspot/user/profile")
        params = {"name": nom, "shared-users": str(data.get("sharedUsers", "1") or "1")}
        if data.get("rateLimit"):
            params["rate-limit"] = str(data["rateLimit"])
        if data.get("addressPool"):
            params["address-pool"] = str(data["addressPool"])
        res.add(**params)
        try:
            ensure_ticket_runtime_support(api, nom)
        except Exception:
            pass
        rid = router.get("id", "") or router.get("host", "")
        db_mod.db_upsert_hotspot_profile_metadata(
            rid,
            nom,
            price=str(data.get("priceCfa", "0") or "0"),
            currency=str(data.get("currency", "FCFA") or "FCFA"),
            expire_mode=str(data.get("expiredMode", "none") or "none"),
            lock_user="yes",
            time_limit=coerce_ticket_time_limit_user(
                data.get("timeLimit", "") or data.get("time_limit", "") or data.get("limitUptime", ""),
                empty="0",
                prefer_legacy_routeros=False,
            ) or "0",
        )
        return jsonify({"ok": True, "msg": f"Profil {nom} ajoutÃ©"})
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)}), 400
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_create_voucher_v2_safe():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    data = request.get_json(silent=True) or {}
    code = str(data.get("code", "")).strip()
    profile = str(data.get("profile", "default")).strip() or "default"
    uptime_raw = str(data.get("uptime", "") or data.get("time_limit", "")).strip()
    if not code or not re.match(r"^[A-Za-z0-9\-_]{1,64}$", code):
        return jsonify({"ok": False, "msg": "Code invalide"}), 400
    if not re.match(r"^[\w\-]{1,64}$", profile):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400

    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response

    router_id = router.get("id", "") or router.get("host", "")
    api = None
    try:
        with TicketGenerationJob(router_id, 1, profile, source="api-single") as job:
            api, error_response = _api_connect_router(router)
            if error_response:
                return error_response

            wifi_name = str(data.get("wifi_name", "") or data.get("network_name", "") or data.get("network", "")).strip()[:64]
            if wifi_name:
                db_mod.db_update_router(router_id, _current_owner_id(), {"wifi_name": wifi_name})
                _invalidate_routers_cache()
            else:
                wifi_name = str(router.get("wifi_name", "") or "")

            uptime = resolve_ticket_time_limit(router_id, profile, uptime_raw) or "0"
            try:
                ensure_ticket_runtime_support(api, profile)
            except Exception:
                pass

            hotspot_resource = api.get_resource("/ip/hotspot/user")
            _add_or_repair_hotspot_ticket(api, hotspot_resource, {
                "name": code,
                "password": code,
                "profile": profile,
                "disabled": "no",
                "comment": build_hotspot_user_comment("", "vc-"),
                "limit-uptime": uptime,
            })

            meta = get_hotspot_profile_metadata_map(router_id).get(profile, {})
            db_mod.db_batch_upsert_ticket_pricing([{
                "router_id": router_id,
                "user": code,
                "password": code,
                "prix": float(meta.get("price", "0") or 0),
                "devise": meta.get("currency", "FCFA") or "FCFA",
                "profil": profile,
                "reseau": wifi_name,
            }])
            job.finish(1, [])

        return jsonify({
            "ok": True,
            "code": code,
            "profile": profile,
            "time_limit": normalize_ticket_time_limit(uptime) or "0",
            "wifi_name": wifi_name,
            "network": wifi_name,
            "router_id": router_id,
        })
    except TicketGenerationBusyError as e:
        return jsonify({"ok": False, "msg": str(e), "busy": True}), 409
    except ValueError as e:
        return jsonify({"ok": False, "msg": str(e)}), 400
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


def api_hotspot_vouchers_generate_v2_safe():
    auth_ok, _ = _check_basic_auth()
    if not auth_ok:
        return jsonify({"ok": False, "msg": "Authentification requise"}), 401

    data = request.get_json(silent=True) or {}
    profil = str(data.get("profil", "default")).strip() or "default"
    qty = safe_int(data.get("qty", 1), default=1, min_val=1, max_val=MAX_TICKET_GENERATION_QTY)
    if not re.match(r"^[\w\-]{1,64}$", profil):
        return jsonify({"ok": False, "msg": "Profil invalide"}), 400

    router, error_response = _api_pick_router(data)
    if error_response:
        return error_response

    router_id = router.get("id", "") or router.get("host", "")
    api = None
    try:
        with TicketGenerationJob(router_id, qty, profil, source="api-vouchers") as job:
            api, error_response = _api_connect_router(router)
            if error_response:
                return error_response

            wifi_name = str(data.get("wifi_name", "") or data.get("network_name", "") or data.get("network", "")).strip()[:64]
            if wifi_name:
                db_mod.db_update_router(router_id, _current_owner_id(), {"wifi_name": wifi_name})
                _invalidate_routers_cache()
            else:
                wifi_name = str(router.get("wifi_name", "") or "")

            ticket_time_limit = resolve_ticket_time_limit(router_id, profil, "") or "0"
            ticket_time_limit_label = resolve_ticket_time_limit_display(router_id, profil, "") or "0"
            profiles_meta = get_hotspot_profile_metadata_map(router_id)
            meta = profiles_meta.get(profil, {})
            price = meta.get("price", "0") or "0"
            currency = meta.get("currency", "FCFA") or "FCFA"
            try:
                ensure_ticket_runtime_support(api, profil)
            except Exception:
                pass

            generated_rows, gen_errors = create_hotspot_ticket_batch(
                api, router_id, qty, profil,
                mode="aleatoire",
                length=8,
                prefix="",
                password_mode="identique",
                comment="",
                network_name=wifi_name,
                price=price,
                currency=currency,
                ticket_time_limit=ticket_time_limit,
                ticket_time_limit_label=ticket_time_limit_label,
                charset_override="ABCDEFGHJKLMNPQRSTUVWXYZ23456789",
                job=job,
                source="api-vouchers",
            )

        codes = [row["name"] for row in generated_rows]
        generated_tickets = [{
            "code": row["name"],
            "profile": profil,
            "time_limit": normalize_ticket_time_limit(ticket_time_limit) or "0",
            "wifi_name": wifi_name,
            "network": wifi_name,
        } for row in generated_rows]
        return jsonify({
            "ok": len(generated_rows) == qty,
            "codes": codes,
            "tickets": generated_tickets,
            "count": len(generated_rows),
            "requested": qty,
            "msg": "" if len(generated_rows) == qty else (gen_errors[-1] if gen_errors else "Generation partielle"),
            "profile": profil,
            "time_limit": normalize_ticket_time_limit(ticket_time_limit) or "0",
            "wifi_name": wifi_name,
            "network": wifi_name,
            "router_id": router_id,
        })
    except TicketGenerationBusyError as e:
        return jsonify({"ok": False, "msg": str(e), "busy": True}), 409
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)}), 500
    finally:
        _close_api_quietly(api)


@app.route("/api/hotspot/generation-status", methods=["GET"])
@login_required
@router_required
def api_hotspot_generation_status():
    router_id = session.get("router_id", "")
    return jsonify({"ok": True, "status": get_ticket_generation_status(router_id)})


app.view_functions["api_dashboard"] = api_dashboard_v2
app.view_functions["api_create_voucher"] = api_create_voucher_v2_safe
app.view_functions["api_hotspot_vouchers_summary"] = api_hotspot_vouchers_summary_v2
app.view_functions["api_hotspot_vouchers_generate"] = api_hotspot_vouchers_generate_v2_safe
app.view_functions["api_hotspot_users"] = api_hotspot_users_v2
app.view_functions["api_hotspot_disconnect"] = api_hotspot_disconnect_v2
app.view_functions["api_hotspot_profiles"] = api_hotspot_profiles_v2
app.view_functions["api_list_tickets"] = api_list_tickets_v2
app.view_functions["api_rapport"] = api_rapport_v2
app.view_functions["api_hotspot_users_add"] = api_hotspot_users_add_v2
app.view_functions["api_hotspot_users_edit"] = api_hotspot_users_edit_v2
app.view_functions["api_hotspot_profiles_add"] = api_hotspot_profiles_add_v2


# ─── Main ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import sys
    port = int(os.environ.get("PORT", 5001))
    dev_mode = "--dev" in sys.argv or os.environ.get("KETAMON_DEV", "") == "1"
    sys.stdout.reconfigure(encoding="utf-8")
    print("KetaMon -- Gestionnaire MikroTik")
    print(f"http://localhost:{port}")
    if dev_mode:
        print("Mode DEV — rechargement automatique activé")
        app.config["SEND_FILE_MAX_AGE_DEFAULT"] = 0
        app.run(host="0.0.0.0", port=port, debug=True, use_reloader=True)
    else:
        try:
            from waitress import serve
            print("Serveur Waitress (production) — 1000+ utilisateurs")
            serve(app, host="0.0.0.0", port=port, threads=16,
                  connection_limit=1000, channel_timeout=60)
        except ImportError:
            print("Waitress absent — mode dev (1 utilisateur)")
            app.run(host="0.0.0.0", port=port, debug=False)
