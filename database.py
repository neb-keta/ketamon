"""
Base de données SQLite WAL — thread-safe, 1000+ utilisateurs simultanés.
Gère : plans, abonnements, config paiement.
"""
import sqlite3
import json
import os
import re
import threading
import time
import uuid
from datetime import datetime, timedelta
from urllib.parse import parse_qsl, urlencode, urlparse, urlunparse

try:
    import psycopg
except Exception:  # psycopg is only required when DATABASE_URL is configured.
    psycopg = None

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
DB_PATH = os.path.join(DATA_DIR, "ketamon.db")
LEGACY_USERS_PATH = os.path.join(DATA_DIR, "users.json")
LEGACY_ROUTERS_PATH = os.path.join(DATA_DIR, "routers.json")
_local  = threading.local()

# Semaphore: limite le nombre de connexions PostgreSQL simultanées ouvertes.
# Evite la saturation sur les plans cloud avec max_connections faible (Aiven free ~5-8).
_PG_MAX_CONN = int(os.environ.get("KETAMON_PG_MAX_CONN", "1"))
_pg_sem: threading.Semaphore | None = None
_pg_sem_lock = threading.Lock()

def _get_pg_sem() -> threading.Semaphore:
    global _pg_sem
    if _pg_sem is None:
        with _pg_sem_lock:
            if _pg_sem is None:
                _pg_sem = threading.Semaphore(_PG_MAX_CONN)
    return _pg_sem

def release_thread_conn():
    """Ferme la connexion thread-local et libere le slot de semaphore."""
    c = getattr(_local, "conn", None)
    if c is not None:
        try: c.close()
        except Exception: pass
        _local.conn = None
        if USE_POSTGRES and getattr(_local, "_pg_sem_held", False):
            try: _get_pg_sem().release()
            except Exception: pass
            _local._pg_sem_held = False

DATABASE_URL = (
    os.environ.get("DATABASE_URL")
    or os.environ.get("POSTGRES_URL")
    or os.environ.get("POSTGRESQL_URL")
    or ""
).strip()
USE_POSTGRES = bool(DATABASE_URL)
DB_INTEGRITY_ERRORS = (sqlite3.IntegrityError,)
if psycopg is not None:
    DB_INTEGRITY_ERRORS = (sqlite3.IntegrityError, psycopg.IntegrityError)

_PG_NOW_TEXT = "TO_CHAR(CURRENT_TIMESTAMP AT TIME ZONE 'UTC', 'YYYY-MM-DD\"T\"HH24:MI:SS.MS')"


def _env_truthy(name: str, default: bool = False) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


ALLOW_LEGACY_JSON_IMPORT = _env_truthy(
    "KETAMON_IMPORT_LEGACY_JSON",
    default=not USE_POSTGRES,
)


def _boot_log(message: str):
    print(f"[KETAMON][DB] {message}", flush=True)


class CompatRow(dict):
    """Small row object compatible with sqlite3.Row key and index access."""

    def __init__(self, keys, values):
        super().__init__(zip(keys, values))
        self._values = list(values)

    def __getitem__(self, key):
        if isinstance(key, int):
            return self._values[key]
        return super().__getitem__(key)


class _VirtualCursor:
    def __init__(self, rows=None, rowcount=-1):
        self._rows = list(rows or [])
        self._index = 0
        self.rowcount = rowcount

    def fetchone(self):
        if self._index >= len(self._rows):
            return None
        row = self._rows[self._index]
        self._index += 1
        return row

    def fetchall(self):
        rows = self._rows[self._index :]
        self._index = len(self._rows)
        return rows

    def __iter__(self):
        return iter(self.fetchall())


def _postgres_dsn():
    dsn = DATABASE_URL
    if dsn.startswith("postgres://"):
        dsn = "postgresql://" + dsn[len("postgres://") :]
    parsed = urlparse(dsn)
    host = (parsed.hostname or "").lower()
    is_local = host in {"localhost", "127.0.0.1", "::1"}
    query = parse_qsl(parsed.query, keep_blank_values=True)
    has_sslmode = any(k.lower() == "sslmode" for k, _ in query)
    if parsed.scheme.startswith("postgres") and not has_sslmode and not is_local:
        query.append(("sslmode", os.environ.get("KETAMON_POSTGRES_SSLMODE", "require")))
        dsn = urlunparse(parsed._replace(query=urlencode(query)))
    return dsn


def _public_database_uri():
    if not USE_POSTGRES:
        return f"SQLite local - {DB_PATH}"
    parsed = urlparse(_postgres_dsn())
    if parsed.password:
        safe_netloc = parsed.netloc.replace(f":{parsed.password}@", ":***@")
        parsed = parsed._replace(netloc=safe_netloc)
    return urlunparse(parsed)


def _split_sql_script(script: str):
    statements, buf = [], []
    in_single = in_double = False
    i = 0
    while i < len(script):
        ch = script[i]
        nxt = script[i + 1] if i + 1 < len(script) else ""
        if ch == "'" and not in_double:
            buf.append(ch)
            if in_single and nxt == "'":
                buf.append(nxt)
                i += 2
                continue
            in_single = not in_single
        elif ch == '"' and not in_single:
            in_double = not in_double
            buf.append(ch)
        elif ch == ";" and not in_single and not in_double:
            stmt = "".join(buf).strip()
            if stmt:
                statements.append(stmt)
            buf = []
        else:
            buf.append(ch)
        i += 1
    tail = "".join(buf).strip()
    if tail:
        statements.append(tail)
    return statements


def _convert_qmark_placeholders(sql: str):
    out = []
    in_single = in_double = False
    i = 0
    while i < len(sql):
        ch = sql[i]
        nxt = sql[i + 1] if i + 1 < len(sql) else ""
        if ch == "'" and not in_double:
            out.append(ch)
            if in_single and nxt == "'":
                out.append(nxt)
                i += 2
                continue
            in_single = not in_single
        elif ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
        elif ch == "?" and not in_single and not in_double:
            out.append("%s")
        else:
            out.append(ch)
        i += 1
    return "".join(out)


def _convert_named_placeholders(sql: str):
    out = []
    in_single = in_double = False
    i = 0
    while i < len(sql):
        ch = sql[i]
        nxt = sql[i + 1] if i + 1 < len(sql) else ""
        if ch == "'" and not in_double:
            out.append(ch)
            if in_single and nxt == "'":
                out.append(nxt)
                i += 2
                continue
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if (
            ch == ":"
            and not in_single
            and not in_double
            and nxt
            and (nxt.isalpha() or nxt == "_")
        ):
            j = i + 1
            while j < len(sql) and (sql[j].isalnum() or sql[j] == "_"):
                j += 1
            name = sql[i + 1 : j]
            out.append(f"%({name})s")
            i = j
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _escape_psycopg_percent_literals(sql: str):
    out = []
    i = 0
    while i < len(sql):
        ch = sql[i]
        if ch != "%":
            out.append(ch)
            i += 1
            continue
        if sql.startswith("%s", i):
            out.append("%s")
            i += 2
            continue
        if sql.startswith("%(", i):
            end = sql.find(")s", i + 2)
            if end != -1:
                out.append(sql[i : end + 2])
                i = end + 2
                continue
        out.append("%%")
        i += 1
    return "".join(out)


def _quote_postgres_user_identifier(sql: str):
    """Quote legacy `user` columns for PostgreSQL without touching :user params."""
    out = []
    in_single = in_double = False
    i = 0
    while i < len(sql):
        ch = sql[i]
        nxt = sql[i + 1] if i + 1 < len(sql) else ""
        if ch == "'" and not in_double:
            out.append(ch)
            if in_single and nxt == "'":
                out.append(nxt)
                i += 2
                continue
            in_single = not in_single
            i += 1
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            i += 1
            continue
        if (
            not in_single
            and not in_double
            and sql[i : i + 4].lower() == "user"
            and (i == 0 or not (sql[i - 1].isalnum() or sql[i - 1] == "_" or sql[i - 1] == ":"))
            and (i + 4 >= len(sql) or not (sql[i + 4].isalnum() or sql[i + 4] == "_"))
        ):
            out.append('"user"')
            i += 4
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _translate_postgres_sql(sql: str, params=None):
    translated = str(sql)
    translated = re.sub(
        r"datetime\(\s*'now'\s*(?:,\s*'localtime'\s*)?\)",
        _PG_NOW_TEXT,
        translated,
        flags=re.IGNORECASE,
    )
    translated = re.sub(
        r"\bINSERT\s+OR\s+IGNORE\s+INTO\b",
        "INSERT INTO",
        translated,
        count=1,
        flags=re.IGNORECASE,
    )
    if re.search(r"^\s*INSERT\s+INTO\b", translated, flags=re.IGNORECASE) and re.search(
        r"\bOR\s+IGNORE\b", str(sql), flags=re.IGNORECASE
    ):
        translated = translated.rstrip().rstrip(";")
        if not re.search(r"\bON\s+CONFLICT\b", translated, flags=re.IGNORECASE):
            translated += " ON CONFLICT DO NOTHING"
    translated = re.sub(
        r"\bALTER\s+TABLE\s+(\S+)\s+ADD\s+COLUMN\s+(?!IF\s+NOT\s+EXISTS\b)",
        r"ALTER TABLE \1 ADD COLUMN IF NOT EXISTS ",
        translated,
        flags=re.IGNORECASE,
    )
    if re.search(r"DELETE\s+FROM\s+ventes\s+WHERE\s+rowid\s+NOT\s+IN", translated, flags=re.IGNORECASE | re.DOTALL):
        translated = """
            DELETE FROM ventes a
            USING ventes b
            WHERE a.router_id=b.router_id
              AND a.user=b.user
              AND a.ctid > b.ctid
        """
    translated = _quote_postgres_user_identifier(translated)
    if isinstance(params, dict):
        translated = _convert_named_placeholders(translated)
    else:
        translated = _convert_qmark_placeholders(translated)
    translated = _escape_psycopg_percent_literals(translated)
    return translated, params


class PostgresCursor:
    def __init__(self, cursor):
        self._cursor = cursor

    @property
    def rowcount(self):
        return self._cursor.rowcount

    def _columns(self):
        return [
            getattr(col, "name", col[0] if col else "")
            for col in (self._cursor.description or [])
        ]

    def _wrap(self, row):
        if row is None:
            return None
        if isinstance(row, dict):
            return CompatRow(list(row.keys()), list(row.values()))
        return CompatRow(self._columns(), row)

    def fetchone(self):
        return self._wrap(self._cursor.fetchone())

    def fetchall(self):
        return [self._wrap(row) for row in self._cursor.fetchall()]

    def __iter__(self):
        return iter(self.fetchall())


class PostgresConnection:
    def __init__(self, conn):
        self._conn = conn
        self.total_changes = 0

    def _ensure_meta(self):
        with self._conn.cursor() as cur:
            cur.execute("""
                CREATE TABLE IF NOT EXISTS ketamon_meta (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL DEFAULT ''
                )
            """)
            cur.execute("""
                INSERT INTO ketamon_meta(key, value)
                VALUES('user_version', '0')
                ON CONFLICT(key) DO NOTHING
            """)

    def _execute_pragma(self, sql: str):
        text = " ".join(str(sql).strip().split())
        table_match = re.match(r"PRAGMA\s+table_info\(([^)]+)\)", text, flags=re.IGNORECASE)
        if table_match:
            table = table_match.group(1).strip().strip('"').strip("'")
            with self._conn.cursor() as cur:
                cur.execute("""
                    SELECT column_name, data_type, is_nullable, column_default
                    FROM information_schema.columns
                    WHERE table_schema='public' AND table_name=%s
                    ORDER BY ordinal_position
                """, (table,))
                rows = []
                for idx, (name, data_type, nullable, default) in enumerate(cur.fetchall()):
                    rows.append(CompatRow(
                        ["cid", "name", "type", "notnull", "dflt_value", "pk"],
                        [idx, name, data_type, 1 if nullable == "NO" else 0, default, 0],
                    ))
                return _VirtualCursor(rows)
        version_set = re.match(r"PRAGMA\s+user_version\s*=\s*(\d+)", text, flags=re.IGNORECASE)
        if version_set:
            self._ensure_meta()
            with self._conn.cursor() as cur:
                cur.execute("""
                    INSERT INTO ketamon_meta(key, value)
                    VALUES('user_version', %s)
                    ON CONFLICT(key) DO UPDATE SET value=EXCLUDED.value
                """, (version_set.group(1),))
            return _VirtualCursor(rowcount=1)
        if re.match(r"PRAGMA\s+user_version\b", text, flags=re.IGNORECASE):
            self._ensure_meta()
            with self._conn.cursor() as cur:
                cur.execute("SELECT value FROM ketamon_meta WHERE key='user_version'")
                row = cur.fetchone()
            version = int(row[0] if row else 0)
            return _VirtualCursor([CompatRow(["user_version"], [version])])
        return _VirtualCursor([])

    def execute(self, sql, params=None):
        if str(sql).strip().upper().startswith("PRAGMA"):
            return self._execute_pragma(sql)
        translated, translated_params = _translate_postgres_sql(sql, params)
        cur = self._conn.cursor()
        if translated_params is None:
            cur.execute(translated)
        else:
            cur.execute(translated, translated_params)
        if cur.rowcount and cur.rowcount > 0:
            self.total_changes += cur.rowcount
        return PostgresCursor(cur)

    def executemany(self, sql, seq_of_params):
        rows = list(seq_of_params or [])
        if not rows:
            return _VirtualCursor(rowcount=0)
        translated, _ = _translate_postgres_sql(sql, rows[0])
        cur = self._conn.cursor()
        cur.executemany(translated, rows)
        if cur.rowcount and cur.rowcount > 0:
            self.total_changes += cur.rowcount
        return PostgresCursor(cur)

    def executescript(self, script):
        last = _VirtualCursor([])
        for statement in _split_sql_script(script):
            last = self.execute(statement)
        return last

    def commit(self):
        self._conn.commit()

    def rollback(self):
        self._conn.rollback()

    def close(self):
        self._conn.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc_type:
            self.rollback()
        else:
            self.commit()
        return False


class DuplicateReferenceError(ValueError):
    """Raised when a payment reference already exists."""

    def __init__(self, reference: str):
        self.reference = reference
        super().__init__(f"Reference already exists: {reference}")


class DuplicateLocalUserError(ValueError):
    """Raised when a local user already exists."""

    def __init__(self, identity: str):
        self.identity = identity
        super().__init__(f"Local user already exists: {identity}")


class RouterLimitExceededError(ValueError):
    """Raised when a user tries to own more routers than allowed."""

    def __init__(self, owner_id: str, limit: int = 1):
        self.owner_id = owner_id
        self.limit = limit
        super().__init__(f"Router limit exceeded for {owner_id}: max {limit}")


def _load_json_file(path, default):
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    return default


_ROUTERS_FERNET = None
try:
    from cryptography.fernet import Fernet
    _rf_key = os.environ.get("KETAMON_ROUTERS_KEY")
    if _rf_key:
        try:
            _ROUTERS_FERNET = Fernet(_rf_key)
        except Exception:
            _ROUTERS_FERNET = None
except Exception:
    _ROUTERS_FERNET = None


def get_conn():
    """Connexion SQLite par thread (thread-local) avec WAL activé."""
    conn = getattr(_local, "conn", None)
    if conn is not None:
        try:
            conn.execute("SELECT 1")
            return conn
        except Exception:
            release_thread_conn()  # libere aussi le semaphore si postgres

    if USE_POSTGRES:
        if psycopg is None:
            raise RuntimeError(
                "DATABASE_URL est configure mais le paquet psycopg n'est pas installe."
            )
        sem = _get_pg_sem()
        acquired = sem.acquire(timeout=20)
        if not acquired:
            raise RuntimeError("Impossible d'obtenir un slot de connexion PostgreSQL (timeout 20s)")
        try:
            connect_timeout = int(os.environ.get("KETAMON_PG_CONNECT_TIMEOUT", "8"))
            dsn = _postgres_dsn()
            # Les poolers (PgBouncer/Neon) rejettent les options de session au demarrage
            use_pooler = "-pooler." in dsn or "pgbouncer" in dsn.lower()
            connect_kwargs: dict = {"connect_timeout": connect_timeout}
            if not use_pooler:
                st = int(os.environ.get("KETAMON_PG_STATEMENT_TIMEOUT_MS", "30000"))
                connect_kwargs["options"] = f"-c statement_timeout={st} -c lock_timeout={st}"
            _boot_log("connexion PostgreSQL en cours")
            raw_conn = psycopg.connect(dsn, **connect_kwargs)
            # SQLite accepte qu'une migration "ADD COLUMN" echoue sans casser la suite.
            # En PostgreSQL, une erreur laisse la transaction inutilisable; autocommit
            # garde ces migrations idempotentes independantes les unes des autres.
            raw_conn.autocommit = True
            _boot_log("connexion PostgreSQL OK")
            conn = PostgresConnection(raw_conn)
            _local.conn = conn
            _local._pg_sem_held = True
            return conn
        except Exception:
            sem.release()
            raise

    conn = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")   # lectures non bloquantes
    conn.execute("PRAGMA synchronous=NORMAL") # bon compromis perf/sécurité
    conn.execute("PRAGMA cache_size=-8000")   # 8 Mo de cache
    conn.execute("PRAGMA foreign_keys=ON")
    _local.conn = conn
    return conn


def _decrypt_router_password(value):
    if not value or not _ROUTERS_FERNET:
        return value or ""
    try:
        return _ROUTERS_FERNET.decrypt(str(value).encode()).decode()
    except Exception:
        return value


def _encrypt_router_password(value):
    plain = _decrypt_router_password(value)
    if not plain or not _ROUTERS_FERNET:
        return plain
    try:
        return _ROUTERS_FERNET.encrypt(str(plain).encode()).decode()
    except Exception:
        return plain


def _normalize_port(value):
    try:
        port = int(value or 8728)
    except Exception:
        return 8728
    return port if port > 0 else 8728


def _normalize_router_driver(value):
    driver = str(value or "mikrotik").strip().lower() or "mikrotik"
    try:
        import mikrotik as mk_mod
        if mk_mod.get_driver(driver) is not None:
            return driver
    except Exception:
        pass
    return "mikrotik"


def _sanitize_router_host(value):
    host = str(value or "").strip()
    if any(ch.isspace() for ch in host):
        return ""
    return host


def _normalize_local_user(user):
    username = str(user.get("username") or user.get("email") or "").strip()
    email = str(user.get("email") or (username if "@" in username else "")).strip()
    role = str(user.get("role") or "utilisateur").strip() or "utilisateur"
    approved_raw = user.get("approved", 1)
    try:
        approved = 1 if int(approved_raw or 0) else 0
    except Exception:
        approved = 1 if str(approved_raw).strip().lower() in {"yes", "true", "on"} else 0
    disabled_default = 0 if approved else 1
    disabled_raw = user.get("disabled", disabled_default)
    try:
        disabled = 1 if int(disabled_raw or 0) else 0
    except Exception:
        disabled = 1 if str(disabled_raw).strip().lower() in {"yes", "true", "on"} else 0
    approved_at = str(user.get("approved_at") or "").strip()
    if approved and not approved_at:
        approved_at = datetime.now().isoformat()
    return {
        "id": str(user.get("id") or uuid.uuid4()),
        "username": username,
        "email": email,
        "password": str(user.get("password") or ""),
        "display_name": str(
            user.get("display_name") or user.get("displayName") or username
        ).strip(),
        "role": role,
        "created_at": str(user.get("created_at") or datetime.now().isoformat()),
        "disabled": disabled,
        "approved": approved,
        "approved_at": approved_at,
    }


def _normalize_router(router):
    password = _decrypt_router_password(router.get("password") or "")
    relay_token = str(router.get("relay_token") or "").strip()
    return {
        "id": str(router.get("id") or uuid.uuid4()),
        "name": str(router.get("name") or "").strip(),
        "host": _sanitize_router_host(router.get("host")),
        "fallback_host": _sanitize_router_host(router.get("fallback_host")),
        "port": _normalize_port(router.get("port")),
        "user": str(router.get("user") or "admin").strip() or "admin",
        "password": _encrypt_router_password(password),
        "currency": str(router.get("currency") or "FCFA").strip() or "FCFA",
        "driver": _normalize_router_driver(router.get("driver")),
        "wifi_name": str(router.get("wifi_name") or "").strip(),
        "relay_enabled": 1 if int(router.get("relay_enabled") or 0) else 0,
        "relay_token": relay_token,
        "relay_last_seen": str(router.get("relay_last_seen") or "").strip(),
        "relay_status": str(router.get("relay_status") or "").strip(),
        "created_at": str(router.get("created_at") or datetime.now().isoformat()),
    }


def _migrate_legacy_local_users(conn):
    if not ALLOW_LEGACY_JSON_IMPORT:
        _boot_log("import users.json ignore en mode PostgreSQL/cloud")
        return
    if conn.execute("SELECT COUNT(*) FROM local_users").fetchone()[0] > 0:
        return
    users = _load_json_file(LEGACY_USERS_PATH, [])
    if not isinstance(users, list):
        return
    seen = set()
    for user in users:
        normalized = _normalize_local_user(user)
        username = normalized["username"]
        if not username or not normalized["password"]:
            continue
        key = username.casefold()
        if key in seen:
            continue
        conn.execute("""
            INSERT OR IGNORE INTO local_users
            (id, username, email, password, display_name, role, created_at, disabled, approved, approved_at)
            VALUES (:id, :username, :email, :password, :display_name, :role, :created_at, :disabled, :approved, :approved_at)
        """, normalized)
        seen.add(key)


def _migrate_legacy_routers(conn):
    if not ALLOW_LEGACY_JSON_IMPORT:
        _boot_log("import routers.json ignore en mode PostgreSQL/cloud")
        return
    if conn.execute("SELECT COUNT(*) FROM routers").fetchone()[0] > 0:
        return
    routers = _load_json_file(LEGACY_ROUTERS_PATH, [])
    if not isinstance(routers, list):
        return
    for router in routers:
        normalized = _normalize_router(router)
        if not normalized["name"] or not normalized["host"]:
            continue
        conn.execute("""
            INSERT OR IGNORE INTO routers
            (id, name, host, port, user, password, currency, driver, created_at)
            VALUES (:id, :name, :host, :port, :user, :password, :currency, :driver, :created_at)
        """, normalized)


def _migrate_routers_owner_id(conn):
    """Ajoute la colonne owner_id à la table routers si elle n'existe pas encore."""
    columns = {row[1] for row in conn.execute("PRAGMA table_info(routers)").fetchall()}
    if "owner_id" not in columns:
        conn.execute("ALTER TABLE routers ADD COLUMN owner_id TEXT NOT NULL DEFAULT ''")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_routers_owner ON routers(owner_id)")


def _normalize_duplicate_references(conn):
    """Makes historical duplicate references unique before adding the constraint."""
    duplicates = conn.execute("""
        SELECT reference
        FROM subscriptions
        WHERE TRIM(reference) <> ''
        GROUP BY reference
        HAVING COUNT(*) > 1
    """).fetchall()
    for dup in duplicates:
        reference = dup["reference"]
        rows = conn.execute("""
            SELECT id, fraude_flags, fraude_detail
            FROM subscriptions
            WHERE reference=?
            ORDER BY
                CASE statut WHEN 'actif' THEN 0 WHEN 'en_attente' THEN 1 ELSE 2 END,
                demande_le ASC,
                id ASC
        """, (reference,)).fetchall()
        for row in rows[1:]:
            try:
                flags = json.loads(row["fraude_flags"] or "[]")
            except Exception:
                flags = []
            if "REFERENCE_DOUBLON_HISTORIQUE" not in flags:
                flags.append("REFERENCE_DOUBLON_HISTORIQUE")
            detail = row["fraude_detail"] or "OK"
            if "REFERENCE_DOUBLON_HISTORIQUE" not in detail:
                detail = f"{detail} | REFERENCE_DOUBLON_HISTORIQUE".strip(" |")
            conn.execute("""
                UPDATE subscriptions
                SET reference=?, fraude_flags=?, fraude_detail=?
                WHERE id=?
            """, (
                f"{reference}__DUP__{row['id'][:8]}",
                json.dumps(flags),
                detail,
                row["id"],
            ))


def _ensure_subscription_reference_constraint(conn):
    """Creates a unique index for non-empty references after migrating legacy data."""
    _normalize_duplicate_references(conn)
    conn.execute("DROP INDEX IF EXISTS idx_sub_ref")
    conn.execute("""
        CREATE UNIQUE INDEX IF NOT EXISTS uq_subscriptions_reference_nonempty
        ON subscriptions(reference)
        WHERE TRIM(reference) <> ''
    """)


def _ensure_hotspot_profile_metadata_columns(conn):
    columns = {row[1] for row in conn.execute("PRAGMA table_info(hotspot_profile_metadata)").fetchall()}
    if not columns:
        return
    if "time_limit" not in columns:
        conn.execute(
            "ALTER TABLE hotspot_profile_metadata ADD COLUMN time_limit TEXT NOT NULL DEFAULT '0'"
        )


def _ensure_ticket_pricing_columns(conn):
    columns = {row[1] for row in conn.execute("PRAGMA table_info(ticket_pricing)").fetchall()}
    if not columns:
        return
    if "password" not in columns:
        conn.execute("ALTER TABLE ticket_pricing ADD COLUMN password TEXT NOT NULL DEFAULT ''")
        conn.execute("UPDATE ticket_pricing SET password=user WHERE TRIM(password)=''")


def _migrate_ventes_v1(conn):
    """Migration v1 : supprime les ventes enregistrées à la CRÉATION du ticket.
    Migration v2 : supprime les ventes avec prix=0 (sync sans ticket_pricing).
    Le thread background re-synchronise avec les bons prix depuis ticket_pricing."""
    version = conn.execute("PRAGMA user_version").fetchone()[0]
    if version < 1:
        conn.execute("DELETE FROM ventes")
        conn.execute("PRAGMA user_version = 1")
        conn.commit()
    if version < 2:
        conn.execute("DELETE FROM ventes WHERE prix = 0")
        conn.execute("PRAGMA user_version = 2")
        conn.commit()
    if version < 3:
        # Re-supprimer les ventes à prix=0 (ré-ajoutées avant le filtre ticket_pricing)
        conn.execute("DELETE FROM ventes WHERE prix = 0")
        conn.execute("PRAGMA user_version = 3")
        conn.commit()
    if version < 4:
        # Supprimer les doublons (race condition thread background + frontend sync)
        # Garder uniquement la vente avec le min(rowid) pour chaque (router_id, user)
        conn.execute("""
            DELETE FROM ventes WHERE rowid NOT IN (
                SELECT MIN(rowid) FROM ventes GROUP BY router_id, user
            )
        """)
        # Ajouter contrainte unique pour éviter tout doublon futur
        conn.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS idx_ventes_unique_user
            ON ventes(router_id, user)
        """)
        conn.execute("PRAGMA user_version = 4")
        conn.commit()
    if version < 5:
        # Migration v5 : ticket_key = identifiant unique du ticket
        # (username + timestamp d'expiration) pour permettre le recomptage
        # d'un même username recyclé après expiration d'un ancien ticket.
        try:
            conn.execute("ALTER TABLE ventes ADD COLUMN ticket_key TEXT NOT NULL DEFAULT ''")
        except Exception:
            pass
        conn.execute("UPDATE ventes SET ticket_key = user WHERE ticket_key = ''")
        conn.execute("DROP INDEX IF EXISTS idx_ventes_unique_user")
        conn.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS idx_ventes_unique_ticket
            ON ventes(router_id, ticket_key)
        """)
        conn.execute("PRAGMA user_version = 5")
        conn.commit()
    if version < 6:
        # Migration v6 : nom WiFi par routeur (affiché sur les tickets imprimés)
        try:
            conn.execute("ALTER TABLE routers ADD COLUMN wifi_name TEXT NOT NULL DEFAULT ''")
        except Exception:
            pass
        conn.execute("PRAGMA user_version = 6")
        conn.commit()

    if version < 7:
        # Migration v7 : hote de secours pour VPN prioritaire + fallback auto
        try:
            conn.execute("ALTER TABLE routers ADD COLUMN fallback_host TEXT NOT NULL DEFAULT ''")
        except Exception:
            pass
        conn.execute("PRAGMA user_version = 7")
        conn.commit()


def init_db():
    """Crée les tables si elles n'existent pas."""
    started = time.monotonic()
    _boot_log(f"initialisation schema demarree ({'postgres' if USE_POSTGRES else 'sqlite'})")
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    conn = get_conn()
    _boot_log("creation/verif tables principales")
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS plans (
        id         TEXT PRIMARY KEY,
        nom        TEXT NOT NULL,
        duree      INTEGER NOT NULL DEFAULT 30,
        prix       REAL NOT NULL DEFAULT 0,
        devise     TEXT NOT NULL DEFAULT 'FCFA',
        actif      INTEGER NOT NULL DEFAULT 1,
        created_at TEXT DEFAULT (datetime('now'))
    );

    CREATE TABLE IF NOT EXISTS subscriptions (
        id              TEXT PRIMARY KEY,
        user_id         TEXT NOT NULL,
        username        TEXT NOT NULL DEFAULT '',
        plan_id         TEXT NOT NULL,
        plan_nom        TEXT NOT NULL DEFAULT '',
        prix_plan       REAL NOT NULL DEFAULT 0,
        devise_plan     TEXT NOT NULL DEFAULT 'FCFA',
        prix_plan_base  REAL NOT NULL DEFAULT 0,
        montant_paye    REAL NOT NULL DEFAULT 0,
        devise_paye     TEXT NOT NULL DEFAULT 'FCFA',
        montant_base    REAL NOT NULL DEFAULT 0,
        devise_base     TEXT NOT NULL DEFAULT 'FCFA',
        duree_jours     INTEGER NOT NULL DEFAULT 30,
        methode         TEXT NOT NULL DEFAULT '',
        reference       TEXT NOT NULL DEFAULT '',
        fraude_flags    TEXT NOT NULL DEFAULT '[]',
        fraude_detail   TEXT NOT NULL DEFAULT 'OK',
        statut          TEXT NOT NULL DEFAULT 'en_attente',
        demande_le      TEXT NOT NULL DEFAULT (datetime('now')),
        active_le       TEXT,
        expire_le       TEXT
    );

    CREATE INDEX IF NOT EXISTS idx_sub_user    ON subscriptions(user_id);
    CREATE INDEX IF NOT EXISTS idx_sub_statut  ON subscriptions(statut);

    CREATE TABLE IF NOT EXISTS local_users (
        id           TEXT PRIMARY KEY,
        username     TEXT NOT NULL,
        email        TEXT NOT NULL DEFAULT '',
        password     TEXT NOT NULL DEFAULT '',
        display_name TEXT NOT NULL DEFAULT '',
        role         TEXT NOT NULL DEFAULT 'utilisateur',
        created_at   TEXT DEFAULT (datetime('now')),
        disabled     INTEGER NOT NULL DEFAULT 0,
        approved     INTEGER NOT NULL DEFAULT 1,
        approved_at  TEXT NOT NULL DEFAULT ''
    );
    CREATE UNIQUE INDEX IF NOT EXISTS uq_local_users_username
        ON local_users(username);
    CREATE UNIQUE INDEX IF NOT EXISTS uq_local_users_email_nonempty
        ON local_users(email)
        WHERE TRIM(email) <> '';

    CREATE TABLE IF NOT EXISTS routers (
        id         TEXT PRIMARY KEY,
        name       TEXT NOT NULL,
        host       TEXT NOT NULL,
        fallback_host TEXT NOT NULL DEFAULT '',
        port       INTEGER NOT NULL DEFAULT 8728,
        user       TEXT NOT NULL DEFAULT 'admin',
        password   TEXT NOT NULL DEFAULT '',
        currency   TEXT NOT NULL DEFAULT 'FCFA',
        driver     TEXT NOT NULL DEFAULT 'mikrotik',
        owner_id   TEXT NOT NULL DEFAULT '',
        wifi_name  TEXT NOT NULL DEFAULT '',
        relay_enabled INTEGER NOT NULL DEFAULT 0,
        relay_token TEXT NOT NULL DEFAULT '',
        relay_last_seen TEXT NOT NULL DEFAULT '',
        relay_status TEXT NOT NULL DEFAULT '',
        created_at TEXT DEFAULT (datetime('now'))
    );
    CREATE INDEX IF NOT EXISTS idx_routers_name    ON routers(name);

    CREATE TABLE IF NOT EXISTS router_relay_commands (
        id           TEXT PRIMARY KEY,
        router_id    TEXT NOT NULL,
        owner_id     TEXT NOT NULL DEFAULT '',
        command      TEXT NOT NULL,
        payload      TEXT NOT NULL DEFAULT '{}',
        status       TEXT NOT NULL DEFAULT 'queued',
        result       TEXT NOT NULL DEFAULT '',
        created_at   TEXT NOT NULL DEFAULT (datetime('now')),
        claimed_at   TEXT NOT NULL DEFAULT '',
        completed_at TEXT NOT NULL DEFAULT ''
    );
    CREATE INDEX IF NOT EXISTS idx_relay_commands_router_status
        ON router_relay_commands(router_id, status, created_at);

    CREATE TABLE IF NOT EXISTS router_relay_snapshots (
        router_id  TEXT NOT NULL,
        resource   TEXT NOT NULL,
        data       TEXT NOT NULL DEFAULT '[]',
        updated_at TEXT NOT NULL,
        PRIMARY KEY (router_id, resource)
    );

    CREATE TABLE IF NOT EXISTS pay_config (
        key   TEXT PRIMARY KEY,
        value TEXT NOT NULL DEFAULT '{}'
    );

    CREATE TABLE IF NOT EXISTS hotspot_profile_metadata (
        router_id    TEXT NOT NULL,
        profile_name TEXT NOT NULL,
        price        TEXT NOT NULL DEFAULT '0',
        currency     TEXT NOT NULL DEFAULT 'FCFA',
        expire_mode  TEXT NOT NULL DEFAULT 'none',
        lock_user    TEXT NOT NULL DEFAULT 'no',
        time_limit   TEXT NOT NULL DEFAULT '0',
        created_at   TEXT NOT NULL DEFAULT (datetime('now')),
        updated_at   TEXT NOT NULL DEFAULT (datetime('now')),
        PRIMARY KEY (router_id, profile_name)
    );
    CREATE INDEX IF NOT EXISTS idx_hotspot_profile_metadata_router
        ON hotspot_profile_metadata(router_id);

    CREATE TABLE IF NOT EXISTS ventes (
        id          TEXT PRIMARY KEY,
        router_id   TEXT NOT NULL DEFAULT '',
        date        TEXT NOT NULL,
        heure       TEXT NOT NULL,
        user        TEXT NOT NULL,
        profil      TEXT NOT NULL DEFAULT '',
        prix        REAL NOT NULL DEFAULT 0,
        devise      TEXT NOT NULL DEFAULT 'FCFA',
        reseau      TEXT NOT NULL DEFAULT '',
        data_limit  TEXT NOT NULL DEFAULT '0',
        created_at  TEXT NOT NULL DEFAULT (datetime('now'))
    );
    CREATE INDEX IF NOT EXISTS idx_ventes_router_date ON ventes(router_id, date);

    CREATE TABLE IF NOT EXISTS ticket_pricing (
        router_id  TEXT NOT NULL,
        user       TEXT NOT NULL,
        password   TEXT NOT NULL DEFAULT '',
        prix       REAL NOT NULL DEFAULT 0,
        devise     TEXT NOT NULL DEFAULT 'FCFA',
        profil     TEXT NOT NULL DEFAULT '',
        reseau     TEXT NOT NULL DEFAULT '',
        created_at TEXT NOT NULL DEFAULT (datetime('now')),
        PRIMARY KEY (router_id, user)
    );

    CREATE TABLE IF NOT EXISTS agent_incidents (
        id          TEXT PRIMARY KEY,
        created_at  TEXT NOT NULL DEFAULT (datetime('now','localtime')),
        level       TEXT NOT NULL DEFAULT 'warning',
        category    TEXT NOT NULL DEFAULT 'general',
        title       TEXT NOT NULL,
        description TEXT,
        router_id   TEXT,
        router_name TEXT,
        auto_fixed  INTEGER NOT NULL DEFAULT 0,
        fix_status  TEXT NOT NULL DEFAULT 'pending',
        fix_action  TEXT,
        fix_result  TEXT,
        resolved    INTEGER NOT NULL DEFAULT 0,
        resolved_at TEXT
    );
    CREATE INDEX IF NOT EXISTS idx_agent_incidents_resolved ON agent_incidents(resolved, created_at);
    """)
    _boot_log("migrations schema complementaires")
    _ensure_subscription_reference_constraint(conn)
    _ensure_hotspot_profile_metadata_columns(conn)
    _ensure_ticket_pricing_columns(conn)
    _migrate_legacy_local_users(conn)
    _migrate_legacy_routers(conn)
    _migrate_ventes_v1(conn)
    _migrate_routers_owner_id(conn)
    try:
        conn.execute("ALTER TABLE routers ADD COLUMN fallback_host TEXT NOT NULL DEFAULT ''")
    except Exception:
        pass
    try:
        conn.execute("ALTER TABLE routers ADD COLUMN wifi_name TEXT NOT NULL DEFAULT ''")
    except Exception:
        pass
    for sql in (
        "ALTER TABLE routers ADD COLUMN relay_enabled INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE routers ADD COLUMN relay_token TEXT NOT NULL DEFAULT ''",
        "ALTER TABLE routers ADD COLUMN relay_last_seen TEXT NOT NULL DEFAULT ''",
        "ALTER TABLE routers ADD COLUMN relay_status TEXT NOT NULL DEFAULT ''",
    ):
        try:
            conn.execute(sql)
        except Exception:
            pass
    conn.execute("CREATE INDEX IF NOT EXISTS idx_routers_relay_token ON routers(relay_token)")
    conn.execute("""
        CREATE TABLE IF NOT EXISTS router_relay_commands (
            id           TEXT PRIMARY KEY,
            router_id    TEXT NOT NULL,
            owner_id     TEXT NOT NULL DEFAULT '',
            command      TEXT NOT NULL,
            payload      TEXT NOT NULL DEFAULT '{}',
            status       TEXT NOT NULL DEFAULT 'queued',
            result       TEXT NOT NULL DEFAULT '',
            created_at   TEXT NOT NULL DEFAULT (datetime('now')),
            claimed_at   TEXT NOT NULL DEFAULT '',
            completed_at TEXT NOT NULL DEFAULT ''
        )
    """)
    conn.execute("""
        CREATE INDEX IF NOT EXISTS idx_relay_commands_router_status
        ON router_relay_commands(router_id, status, created_at)
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS router_relay_snapshots (
            router_id  TEXT NOT NULL,
            resource   TEXT NOT NULL,
            data       TEXT NOT NULL DEFAULT '[]',
            updated_at TEXT NOT NULL,
            PRIMARY KEY (router_id, resource)
        )
    """)
    conn.commit()
    # Ajoute la colonne disabled si absente (migration non destructive)
    try:
        conn.execute("ALTER TABLE local_users ADD COLUMN disabled INTEGER NOT NULL DEFAULT 0")
    except Exception:
        pass
    try:
        conn.execute("ALTER TABLE local_users ADD COLUMN approved INTEGER NOT NULL DEFAULT 1")
    except Exception:
        pass
    try:
        conn.execute("ALTER TABLE local_users ADD COLUMN approved_at TEXT NOT NULL DEFAULT ''")
    except Exception:
        pass
    try:
        conn.execute("""
            UPDATE local_users
            SET approved_at = COALESCE(NULLIF(approved_at, ''), created_at, datetime('now'))
            WHERE CAST(COALESCE(approved, 1) AS INTEGER) = 1
              AND TRIM(COALESCE(approved_at, '')) = ''
        """)
    except Exception:
        pass
    conn.commit()

    # Migration : first_used_at + expire_at dans ticket_pricing (expiration absolue côté serveur)
    for _sql in (
        "ALTER TABLE ticket_pricing ADD COLUMN first_used_at TEXT DEFAULT NULL",
        "ALTER TABLE ticket_pricing ADD COLUMN expire_at TEXT DEFAULT NULL",
    ):
        try:
            conn.execute(_sql)
        except Exception:
            pass
    conn.commit()

    # Plans par défaut
    existing = conn.execute("SELECT COUNT(*) FROM plans").fetchone()[0]
    if existing == 0:
        conn.executemany(
            "INSERT OR IGNORE INTO plans(id,nom,duree,prix,devise,actif) VALUES(?,?,?,?,?,1)",
            [
                ("mensuel",  "Mensuel",    30,  5000,  "FCFA"),
                ("trimestr", "Trimestriel",90,  12000, "FCFA"),
                ("annuel",   "Annuel",     365, 40000, "FCFA"),
            ]
        )
        conn.commit()
    _boot_log(f"initialisation schema terminee en {time.monotonic() - started:.2f}s")


# ── Plans ─────────────────────────────────────────────────────────────────────

def db_backend_name() -> str:
    return "postgres" if USE_POSTGRES else "sqlite"


def db_status() -> dict:
    conn = get_conn()
    conn.execute("SELECT 1")
    return {
        "connected": True,
        "backend": db_backend_name(),
        "uri": _public_database_uri(),
        "dbName": urlparse(_postgres_dsn()).path.lstrip("/") if USE_POSTGRES else os.path.basename(DB_PATH),
        "pingMs": 0,
    }


def db_table_stats() -> dict:
    conn = get_conn()
    collections = []
    if USE_POSTGRES:
        rows = conn.execute("""
            SELECT table_name AS name
            FROM information_schema.tables
            WHERE table_schema='public' AND table_type='BASE TABLE'
            ORDER BY table_name
        """).fetchall()
    else:
        rows = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' ORDER BY name"
        ).fetchall()
    for row in rows:
        try:
            tname = str(row["name"])
        except Exception:
            tname = str(row[0])
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", tname):
            continue
        cnt = conn.execute(f'SELECT COUNT(*) FROM "{tname}"').fetchone()[0]
        collections.append({"name": tname, "count": int(cnt or 0), "size": "-"})
    total_size = "-"
    if not USE_POSTGRES:
        try:
            db_size = os.path.getsize(DB_PATH) if os.path.exists(DB_PATH) else 0
            total_size = f"{db_size // 1024} KB" if db_size < 1024 * 1024 else f"{db_size // (1024 * 1024)} MB"
        except Exception:
            total_size = "-"
    return {"collections": collections, "totalSize": total_size}


def db_get_local_users():
    conn = get_conn()
    return [
        dict(r) for r in conn.execute(
            "SELECT * FROM local_users ORDER BY created_at ASC, username ASC"
        ).fetchall()
    ]


def db_get_local_user(identity: str):
    identity = str(identity or "").strip()
    if not identity:
        return None
    conn = get_conn()
    row = conn.execute("""
        SELECT *
        FROM local_users
        WHERE id=? OR username=? OR email=?
        ORDER BY
            CASE
                WHEN id=? THEN 0
                WHEN username=? THEN 1
                ELSE 2
            END
        LIMIT 1
    """, (identity, identity, identity, identity, identity)).fetchone()
    return dict(row) if row else None


def db_insert_local_user(user: dict):
    record = _normalize_local_user(user)
    try:
        conn = get_conn()
        conn.execute("""
            INSERT INTO local_users
            (id, username, email, password, display_name, role, created_at, disabled, approved, approved_at)
            VALUES (:id, :username, :email, :password, :display_name, :role, :created_at, :disabled, :approved, :approved_at)
        """, record)
        conn.commit()
        return db_get_local_user(record["id"])
    except DB_INTEGRITY_ERRORS as exc:
        if (
            "local_users.username" in str(exc)
            or "local_users.email" in str(exc)
            or "uq_local_users_username" in str(exc)
            or "uq_local_users_email_nonempty" in str(exc)
        ):
            raise DuplicateLocalUserError(record["username"] or record["email"]) from exc
        raise


def db_update_local_user_password(identity: str, password_hash: str) -> bool:
    user = db_get_local_user(identity)
    if not user:
        return False
    conn = get_conn()
    conn.execute(
        "UPDATE local_users SET password=? WHERE id=?",
        (str(password_hash or ""), user["id"])
    )
    conn.commit()
    return True


def db_upsert_local_email_user(
    email: str,
    *,
    password_hash: str | None = None,
    display_name: str | None = None,
    role: str | None = "utilisateur",
    approved: int | None = None,
    disabled: int | None = None,
) -> dict | None:
    email = str(email or "").strip()
    if not email:
        return None

    existing = db_get_local_user(email)
    conn = get_conn()
    if existing:
        fields = []
        params = []
        if password_hash is not None:
            fields.append("password=?")
            params.append(str(password_hash or ""))
        if display_name is not None and str(display_name).strip():
            fields.append("display_name=?")
            params.append(str(display_name).strip())
        if role is not None and str(role).strip():
            fields.append("role=?")
            params.append(str(role).strip())
        if approved is not None:
            approved_val = 1 if int(approved or 0) else 0
            fields.append("approved=?")
            params.append(approved_val)
            if approved_val and not str(existing.get("approved_at") or "").strip():
                fields.append("approved_at=?")
                params.append(datetime.now().isoformat())
        if disabled is not None:
            fields.append("disabled=?")
            params.append(1 if int(disabled or 0) else 0)
        if fields:
            params.append(existing["id"])
            conn.execute(
                f"UPDATE local_users SET {', '.join(fields)} WHERE id=?",
                tuple(params)
            )
            conn.commit()
        return db_get_local_user(existing["id"])

    record = _normalize_local_user({
        "id": str(uuid.uuid4()),
        "username": email,
        "email": email,
        "password": str(password_hash or ""),
        "display_name": display_name or email,
        "role": role or "utilisateur",
        "approved": 0 if approved is None else approved,
        "disabled": 1 if disabled is None else disabled,
        "approved_at": datetime.now().isoformat() if int(approved or 0) else "",
    })
    return db_insert_local_user(record)


def db_set_local_user_active(identity: str, active: bool) -> dict | None:
    user = db_get_local_user(identity)
    if not user:
        return None
    conn = get_conn()
    if active:
        approved_at = str(user.get("approved_at") or "").strip() or datetime.now().isoformat()
        conn.execute(
            "UPDATE local_users SET disabled=0, approved=1, approved_at=? WHERE id=?",
            (approved_at, user["id"])
        )
    else:
        conn.execute("UPDATE local_users SET disabled=1 WHERE id=?", (user["id"],))
    conn.commit()
    return db_get_local_user(user["id"])


def db_get_routers(owner_id=None):
    """Retourne les routeurs. Si owner_id fourni, filtre sur ce propriétaire."""
    conn = get_conn()
    if owner_id:
        rows = conn.execute(
            "SELECT * FROM routers WHERE owner_id=? ORDER BY created_at ASC, name ASC",
            (str(owner_id),)
        ).fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM routers ORDER BY created_at ASC, name ASC"
        ).fetchall()
    routers = []
    for row in rows:
        router = dict(row)
        router["password"] = _decrypt_router_password(router.get("password", ""))
        router["host"] = _sanitize_router_host(router.get("host"))
        router["fallback_host"] = _sanitize_router_host(router.get("fallback_host"))
        routers.append(router)
    return routers


def db_count_routers(owner_id: str | None) -> int:
    owner = str(owner_id or "").strip()
    if not owner:
        return 0
    conn = get_conn()
    row = conn.execute(
        "SELECT COUNT(*) FROM routers WHERE owner_id=?",
        (owner,)
    ).fetchone()
    return int(row[0] or 0) if row else 0


def db_get_router(router_id: str, owner_id: str | None = None):
    router_id = str(router_id or "").strip()
    if not router_id:
        return None
    conn = get_conn()
    if owner_id:
        row = conn.execute(
            "SELECT * FROM routers WHERE id=? AND owner_id=?",
            (router_id, str(owner_id))
        ).fetchone()
    else:
        row = conn.execute("SELECT * FROM routers WHERE id=?", (router_id,)).fetchone()
    if not row:
        return None
    router = dict(row)
    router["password"] = _decrypt_router_password(router.get("password", ""))
    router["host"] = _sanitize_router_host(router.get("host"))
    router["fallback_host"] = _sanitize_router_host(router.get("fallback_host"))
    return router


def db_set_router_relay(router_id: str, owner_id: str | None, *, enabled=None, token=None):
    router = db_get_router(router_id, owner_id)
    if not router:
        return None
    fields = []
    params = []
    if enabled is not None:
        fields.append("relay_enabled=?")
        params.append(1 if enabled else 0)
    if token is not None:
        fields.append("relay_token=?")
        params.append(str(token or "").strip())
    if not fields:
        return router
    params.append(str(router_id))
    if owner_id:
        params.append(str(owner_id))
        where = "id=? AND owner_id=?"
    else:
        where = "id=?"
    conn = get_conn()
    conn.execute(f"UPDATE routers SET {', '.join(fields)} WHERE {where}", tuple(params))
    conn.commit()
    return db_get_router(router_id, owner_id)


def db_get_router_by_relay_token(token: str):
    token = str(token or "").strip()
    if not token:
        return None
    conn = get_conn()
    row = conn.execute(
        "SELECT * FROM routers WHERE relay_enabled=1 AND relay_token=?",
        (token,)
    ).fetchone()
    if not row:
        return None
    router = dict(row)
    router["password"] = _decrypt_router_password(router.get("password", ""))
    router["host"] = _sanitize_router_host(router.get("host"))
    router["fallback_host"] = _sanitize_router_host(router.get("fallback_host"))
    return router


def db_touch_router_relay(router_id: str, status: str = "online"):
    conn = get_conn()
    conn.execute(
        "UPDATE routers SET relay_last_seen=?, relay_status=? WHERE id=?",
        (datetime.now().isoformat(), str(status or "online"), str(router_id or ""))
    )
    conn.commit()


def db_enqueue_router_relay_command(router_id: str, owner_id: str | None, command: str, payload=None):
    payload_text = json.dumps(payload or {}, ensure_ascii=False)
    row = {
        "id": str(uuid.uuid4()),
        "router_id": str(router_id or ""),
        "owner_id": str(owner_id or ""),
        "command": str(command or "").strip(),
        "payload": payload_text,
        "created_at": datetime.now().isoformat(),
    }
    if not row["router_id"] or not row["command"]:
        return None
    conn = get_conn()
    existing = conn.execute("""
        SELECT *
        FROM router_relay_commands
        WHERE router_id=? AND command=? AND payload=? AND status='queued'
        ORDER BY created_at ASC
        LIMIT 1
    """, (row["router_id"], row["command"], row["payload"])).fetchone()
    if existing:
        return dict(existing)
    conn.execute("""
        INSERT INTO router_relay_commands
        (id, router_id, owner_id, command, payload, status, created_at)
        VALUES (:id, :router_id, :owner_id, :command, :payload, 'queued', :created_at)
    """, row)
    conn.commit()
    return db_get_router_relay_command(row["id"])


def db_get_router_relay_command(command_id: str):
    conn = get_conn()
    row = conn.execute(
        "SELECT * FROM router_relay_commands WHERE id=?",
        (str(command_id or ""),)
    ).fetchone()
    return dict(row) if row else None


def db_claim_next_router_relay_command(router_id: str):
    conn = get_conn()
    threshold = (datetime.now() - timedelta(minutes=10)).isoformat()
    conn.execute("""
        UPDATE router_relay_commands
        SET status='queued', claimed_at=''
        WHERE router_id=?
          AND status='claimed'
          AND COALESCE(completed_at, '')=''
          AND COALESCE(claimed_at, '') < ?
    """, (str(router_id or ""), threshold))
    row = conn.execute("""
        SELECT *
        FROM router_relay_commands
        WHERE router_id=? AND status='queued'
        ORDER BY
          CASE
            WHEN command='routeros-script' AND payload LIKE '%KETAMON_EXPIRE_ENFORCE%' THEN 0
            WHEN command='routeros-script' AND payload LIKE '%ketamon-ticket-login%' THEN 1
            WHEN command='routeros-script' AND payload LIKE '%ketamon-ticket-expiry%' THEN 1
            WHEN command='routeros-script' AND payload LIKE '%ketamon-ticket-expiry-runner%' THEN 1
            WHEN command='routeros-script' AND payload LIKE '%on-login=%' THEN 1
            WHEN command='routeros-script' AND payload LIKE '%/ip hotspot user add name=%' THEN 2
            WHEN command='ping' THEN 3
            WHEN command='routeros-script' AND payload LIKE '%restored-from-database%' THEN 5
            ELSE 4
          END,
          created_at ASC
        LIMIT 1
    """, (str(router_id or ""),)).fetchone()
    if not row:
        return None
    command_id = row["id"]
    conn.execute(
        "UPDATE router_relay_commands SET status='claimed', claimed_at=? WHERE id=? AND status='queued'",
        (datetime.now().isoformat(), command_id)
    )
    conn.commit()
    return db_get_router_relay_command(command_id)


def db_complete_router_relay_command(command_id: str, router_id: str, ok: bool, result=None):
    status = "done" if ok else "error"
    if isinstance(result, str):
        result_text = result
    else:
        result_text = json.dumps(result or {}, ensure_ascii=False)
    conn = get_conn()
    cur = conn.execute("""
        UPDATE router_relay_commands
        SET status=?, result=?, completed_at=?
        WHERE id=? AND router_id=?
    """, (
        status,
        result_text[:10000],
        datetime.now().isoformat(),
        str(command_id or ""),
        str(router_id or ""),
    ))
    conn.commit()
    return cur.rowcount > 0


def db_get_router_relay_commands(router_id: str, limit: int = 10):
    conn = get_conn()
    rows = conn.execute("""
        SELECT *
        FROM router_relay_commands
        WHERE router_id=?
        ORDER BY created_at DESC
        LIMIT ?
    """, (str(router_id or ""), max(1, min(int(limit or 10), 100)))).fetchall()
    return [dict(r) for r in rows]


def db_upsert_router_relay_snapshots(router_id: str, resources: dict):
    router_id = str(router_id or "").strip()
    if not router_id or not isinstance(resources, dict):
        return 0
    now = datetime.now().isoformat()

    resource_keys = {str(k or "").strip() for k in resources if str(k or "").strip()}
    is_user_chunk_only = (resource_keys == {"/ip/hotspot/user"})

    conn = get_conn()

    # Pour les POSTs contenant uniquement /ip/hotspot/user (chunks v7),
    # accumuler au lieu d'écraser : comparer updated_at de relay-status vs users.
    # Si users a été mis à jour APRÈS relay-status → même cycle → APPEND.
    # Sinon (nouveau cycle ou premier chunk) → REPLACE.
    append_users = False
    if is_user_chunk_only:
        rs_row = conn.execute(
            "SELECT updated_at FROM router_relay_snapshots WHERE router_id=? AND resource=?",
            (router_id, "/ketamon/relay-status")
        ).fetchone()
        u_row = conn.execute(
            "SELECT updated_at FROM router_relay_snapshots WHERE router_id=? AND resource=?",
            (router_id, "/ip/hotspot/user")
        ).fetchone()
        rs_ts = rs_row["updated_at"] if rs_row else None
        u_ts = u_row["updated_at"] if u_row else None
        if rs_ts and u_ts and u_ts > rs_ts:
            append_users = True

    rows = []
    for resource, data in resources.items():
        resource = str(resource or "").strip()
        if not resource:
            continue
        if isinstance(data, dict):
            normalized = [data]
        elif isinstance(data, list):
            normalized = [dict(item) for item in data if isinstance(item, dict)]
        else:
            normalized = []

        if resource == "/ip/hotspot/user" and append_users:
            existing_row = conn.execute(
                "SELECT data FROM router_relay_snapshots WHERE router_id=? AND resource=?",
                (router_id, "/ip/hotspot/user")
            ).fetchone()
            existing = []
            if existing_row:
                try:
                    existing = json.loads(existing_row["data"] or "[]")
                    if not isinstance(existing, list):
                        existing = []
                except Exception:
                    existing = []
            existing_keys = {str(u.get(".id") or u.get("name") or "") for u in existing}
            for u in normalized:
                k = str(u.get(".id") or u.get("name") or "")
                if k not in existing_keys:
                    existing.append(u)
                    existing_keys.add(k)
            normalized = existing

        rows.append({
            "router_id": router_id,
            "resource": resource,
            "data": json.dumps(normalized, ensure_ascii=False),
            "updated_at": now,
        })
    if not rows:
        return 0
    conn.executemany("""
        INSERT INTO router_relay_snapshots(router_id, resource, data, updated_at)
        VALUES(:router_id, :resource, :data, :updated_at)
        ON CONFLICT(router_id, resource)
        DO UPDATE SET data=excluded.data, updated_at=excluded.updated_at
    """, rows)
    conn.commit()
    return len(rows)


def db_get_router_relay_snapshot(router_id: str, resource: str | None = None):
    router_id = str(router_id or "").strip()
    if not router_id:
        return {} if resource is None else []
    conn = get_conn()
    if resource is not None:
        row = conn.execute("""
            SELECT data
            FROM router_relay_snapshots
            WHERE router_id=? AND resource=?
            LIMIT 1
        """, (router_id, str(resource or "").strip())).fetchone()
        if not row:
            return []
        try:
            data = json.loads(row["data"] or "[]")
            return data if isinstance(data, list) else []
        except Exception:
            return []
    rows = conn.execute("""
        SELECT resource, data, updated_at
        FROM router_relay_snapshots
        WHERE router_id=?
    """, (router_id,)).fetchall()
    out = {}
    for row in rows:
        try:
            data = json.loads(row["data"] or "[]")
        except Exception:
            data = []
        out[str(row["resource"])] = {
            "data": data if isinstance(data, list) else [],
            "updated_at": row["updated_at"],
        }
    return out


def db_get_router_counts_by_owner() -> dict:
    conn = get_conn()
    rows = conn.execute("""
        SELECT owner_id, COUNT(*) AS count
        FROM routers
        WHERE TRIM(COALESCE(owner_id, '')) <> ''
        GROUP BY owner_id
    """).fetchall()
    return {str(r["owner_id"] or ""): int(r["count"] or 0) for r in rows}


def db_replace_routers(routers, owner_id=None):
    """Remplace tous les routeurs. Si owner_id fourni, ne touche qu'aux routeurs de ce propriétaire."""
    conn = get_conn()
    normalized = []
    for router in routers or []:
        record = _normalize_router(router)
        if not record["name"] or not record["host"]:
            continue
        record["owner_id"] = str(owner_id or "")
        normalized.append(record)
    with conn:
        if owner_id:
            conn.execute("DELETE FROM routers WHERE owner_id=?", (str(owner_id),))
        else:
            conn.execute("DELETE FROM routers")
        conn.executemany("""
            INSERT INTO routers
            (id, name, host, fallback_host, port, user, password, currency, driver, owner_id,
             relay_enabled, relay_token, relay_last_seen, relay_status, created_at)
            VALUES (:id, :name, :host, :fallback_host, :port, :user, :password, :currency, :driver, :owner_id,
                    :relay_enabled, :relay_token, :relay_last_seen, :relay_status, :created_at)
        """, normalized)


def db_add_router(router_data: dict, owner_id: str) -> dict:
    """Ajoute un routeur appartenant à owner_id et retourne l'enregistrement créé."""
    record = _normalize_router(router_data)
    record["owner_id"] = str(owner_id or "")
    if record["owner_id"] and db_count_routers(record["owner_id"]) >= 1:
        raise RouterLimitExceededError(record["owner_id"], limit=1)
    conn = get_conn()
    conn.execute("""
        INSERT INTO routers
        (id, name, host, fallback_host, port, user, password, currency, driver, owner_id,
         relay_enabled, relay_token, relay_last_seen, relay_status, created_at)
        VALUES (:id, :name, :host, :fallback_host, :port, :user, :password, :currency, :driver, :owner_id,
                :relay_enabled, :relay_token, :relay_last_seen, :relay_status, :created_at)
    """, record)
    conn.commit()
    record["password"] = _decrypt_router_password(record["password"])
    return record


def db_delete_router(router_id: str, owner_id: str | None = None) -> bool:
    """Supprime un routeur par id. Si owner_id fourni, vérifie l'appartenance."""
    conn = get_conn()
    if owner_id:
        cur = conn.execute(
            "DELETE FROM routers WHERE id=? AND owner_id=?",
            (str(router_id), str(owner_id))
        )
    else:
        cur = conn.execute("DELETE FROM routers WHERE id=?", (str(router_id),))
    conn.commit()
    return cur.rowcount > 0


def db_update_router(router_id: str, owner_id: str | None, fields: dict) -> bool:
    """Met à jour les champs d'un routeur. Retourne True si une ligne a été modifiée."""
    allowed = {"name", "host", "fallback_host", "port", "user", "password", "currency", "driver", "wifi_name"}
    updates = {}
    for k, v in fields.items():
        if k not in allowed:
            continue
        if k == "password":
            updates[k] = _encrypt_router_password(str(v or ""))
        elif k == "port":
            updates[k] = _normalize_port(v)
        elif k == "driver":
            updates[k] = _normalize_router_driver(v)
        elif k in {"host", "fallback_host"}:
            updates[k] = _sanitize_router_host(v)
        else:
            updates[k] = str(v or "").strip()
    if not updates:
        return False
    conn = get_conn()
    set_clause = ", ".join(f"{k}=:{k}" for k in updates)
    params = {**updates, "rid": str(router_id)}
    if owner_id:
        params["oid"] = str(owner_id)
        cur = conn.execute(
            f"UPDATE routers SET {set_clause} WHERE id=:rid AND owner_id=:oid",
            params
        )
    else:
        cur = conn.execute(
            f"UPDATE routers SET {set_clause} WHERE id=:rid",
            params
        )
    conn.commit()
    return cur.rowcount > 0


def db_get_plans(actif_only=False):
    conn = get_conn()
    q = "SELECT * FROM plans"
    if actif_only:
        q += " WHERE actif=1"
    q += " ORDER BY prix ASC"
    return [dict(r) for r in conn.execute(q).fetchall()]


def db_get_hotspot_profile_metadata(router_id: str, profile_name: str | None = None):
    router_id = str(router_id or "").strip()
    if not router_id:
        return None if profile_name else []
    conn = get_conn()
    if profile_name is None:
        rows = conn.execute("""
            SELECT *
            FROM hotspot_profile_metadata
            WHERE router_id=?
            ORDER BY profile_name ASC
        """, (router_id,)).fetchall()
        return [dict(row) for row in rows]

    row = conn.execute("""
        SELECT *
        FROM hotspot_profile_metadata
        WHERE router_id=? AND profile_name=?
        LIMIT 1
    """, (router_id, str(profile_name or "").strip())).fetchone()
    return dict(row) if row else None


def db_upsert_hotspot_profile_metadata(router_id: str, profile_name: str, price="0", currency="FCFA", expire_mode="none", lock_user="no", time_limit="0"):
    router_id = str(router_id or "").strip()
    profile_name = str(profile_name or "").strip()
    if not router_id or not profile_name:
        return None
    record = {
        "router_id": router_id,
        "profile_name": profile_name,
        "price": str(price or "0").strip() or "0",
        "currency": str(currency or "FCFA").strip() or "FCFA",
        "expire_mode": str(expire_mode or "none").strip() or "none",
        "lock_user": str(lock_user or "no").strip() or "no",
        "time_limit": str(time_limit or "0").strip() or "0",
    }
    conn = get_conn()
    conn.execute("""
        INSERT INTO hotspot_profile_metadata(
            router_id, profile_name, price, currency, expire_mode, lock_user, time_limit, created_at, updated_at
        ) VALUES (
            :router_id, :profile_name, :price, :currency, :expire_mode, :lock_user, :time_limit, datetime('now'), datetime('now')
        )
        ON CONFLICT(router_id, profile_name) DO UPDATE SET
            price=excluded.price,
            currency=excluded.currency,
            expire_mode=excluded.expire_mode,
            lock_user=excluded.lock_user,
            time_limit=excluded.time_limit,
            updated_at=datetime('now')
    """, record)
    conn.commit()
    return db_get_hotspot_profile_metadata(router_id, profile_name)


def db_delete_hotspot_profile_metadata(router_id: str, profile_name: str | None = None):
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0
    conn = get_conn()
    if profile_name is None:
        result = conn.execute(
            "DELETE FROM hotspot_profile_metadata WHERE router_id=?",
            (router_id,),
        )
    else:
        result = conn.execute(
            "DELETE FROM hotspot_profile_metadata WHERE router_id=? AND profile_name=?",
            (router_id, str(profile_name or "").strip()),
        )
    conn.commit()
    return int(getattr(result, "rowcount", 0) or 0)


def db_save_plan(plan: dict):
    conn = get_conn()
    conn.execute("""
        INSERT INTO plans(id,nom,duree,prix,devise,actif)
        VALUES(:id,:nom,:duree,:prix,:devise,:actif)
        ON CONFLICT(id) DO UPDATE SET
            nom=excluded.nom, duree=excluded.duree, prix=excluded.prix,
            devise=excluded.devise, actif=excluded.actif
    """, plan)
    conn.commit()


def db_delete_plan(plan_id: str):
    conn = get_conn()
    conn.execute("DELETE FROM plans WHERE id=?", (plan_id,))
    conn.commit()


# ── Abonnements ───────────────────────────────────────────────────────────────

def db_expire_old_subscriptions():
    conn = get_conn()
    conn.execute("""
        UPDATE subscriptions SET statut='expire'
        WHERE statut='actif' AND expire_le IS NOT NULL AND expire_le < ?
    """, (datetime.utcnow().isoformat(),))
    conn.commit()


def db_get_subscriptions(user_id=None):
    db_expire_old_subscriptions()
    conn = get_conn()
    if user_id:
        rows = conn.execute(
            "SELECT * FROM subscriptions WHERE user_id=? ORDER BY demande_le DESC",
            (user_id,)
        ).fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM subscriptions ORDER BY demande_le DESC"
        ).fetchall()
    result = []
    for r in rows:
        d = dict(r)
        try:
            d["fraude_flags"] = json.loads(d.get("fraude_flags", "[]"))
        except Exception:
            d["fraude_flags"] = []
        result.append(d)
    return result


def db_get_active_sub(user_id: str):
    """Retourne l'abonnement actif de l'utilisateur ou None."""
    db_expire_old_subscriptions()
    now  = datetime.utcnow().isoformat()
    conn = get_conn()
    row  = conn.execute("""
        SELECT * FROM subscriptions
        WHERE user_id=? AND statut='actif' AND expire_le > ?
        ORDER BY expire_le DESC LIMIT 1
    """, (user_id, now)).fetchone()
    if not row:
        return None
    d = dict(row)
    try:
        d["fraude_flags"] = json.loads(d.get("fraude_flags", "[]"))
    except Exception:
        d["fraude_flags"] = []
    return d


def db_reference_exists(reference: str) -> bool:
    reference = str(reference or "").strip()
    if not reference:
        return False
    conn = get_conn()
    row  = conn.execute(
        "SELECT id FROM subscriptions WHERE reference=?", (reference,)
    ).fetchone()
    return row is not None


def db_insert_subscription(sub: dict):
    conn = get_conn()
    flags = sub.get("fraude_flags", [])
    reference = str(sub.get("reference") or "").strip()
    try:
        conn.execute("""
            INSERT INTO subscriptions
            (id,user_id,username,plan_id,plan_nom,prix_plan,devise_plan,
             prix_plan_base,montant_paye,devise_paye,montant_base,devise_base,
             duree_jours,methode,reference,fraude_flags,fraude_detail,statut,
             demande_le,active_le,expire_le)
            VALUES
            (:id,:user_id,:username,:plan_id,:plan_nom,:prix_plan,:devise_plan,
             :prix_plan_base,:montant_paye,:devise_paye,:montant_base,:devise_base,
             :duree_jours,:methode,:reference,:fraude_flags,:fraude_detail,:statut,
             :demande_le,:active_le,:expire_le)
        """, {**sub, "reference": reference, "fraude_flags": json.dumps(flags)})
        conn.commit()
    except DB_INTEGRITY_ERRORS as exc:
        if reference and (
            "subscriptions.reference" in str(exc)
            or "uq_subscriptions_reference_nonempty" in str(exc)
        ):
            raise DuplicateReferenceError(reference) from exc
        raise


def db_update_sub_statut(sub_id: str, statut: str, active_le=None, expire_le=None):
    conn = get_conn()
    conn.execute("""
        UPDATE subscriptions SET statut=?, active_le=?, expire_le=?
        WHERE id=?
    """, (statut, active_le, expire_le, sub_id))
    # Marquer expirés automatiquement
    conn.execute("""
        UPDATE subscriptions SET statut='expire'
        WHERE statut='actif' AND expire_le < ?
    """, (datetime.utcnow().isoformat(),))
    conn.commit()


def db_delete_sub(sub_id: str):
    conn = get_conn()
    conn.execute("DELETE FROM subscriptions WHERE id=?", (sub_id,))
    conn.commit()


# ── Config paiement ───────────────────────────────────────────────────────────

_DEFAULT_PAY_CFG = {
    "devise_base": "FCFA",
    "trial_days": 45,
    "taux_change": {"USD": 606.0, "EUR": 655.0, "FCFA": 1.0, "XOF": 1.0},
    "tolerance_pct": 0,
    "methodes": [
        {"id": "orange-money", "nom": "Orange Money", "numero": "", "instructions": "Envoyez le montant exact.", "actif": False},
        {"id": "moov-money",   "nom": "Moov Money",   "numero": "", "instructions": "Envoyez le montant exact.", "actif": False},
        {"id": "wave",         "nom": "Wave",          "numero": "", "instructions": "Transfert Wave.", "actif": False},
        {"id": "mtn-money",    "nom": "MTN Money",     "numero": "", "instructions": "Envoyez le montant exact.", "actif": False},
    ],
}


def db_get_pay_config() -> dict:
    conn = get_conn()
    row  = conn.execute("SELECT value FROM pay_config WHERE key='main'").fetchone()
    if row:
        try:
            return json.loads(row["value"])
        except Exception:
            pass
    return dict(_DEFAULT_PAY_CFG)


def db_save_pay_config(cfg: dict):
    conn = get_conn()
    conn.execute(
        "INSERT INTO pay_config(key,value) VALUES('main',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (json.dumps(cfg),)
    )
    conn.commit()


# ── Ventes locales ─────────────────────────────────────────────────────────────

def db_insert_vente(vente: dict):
    conn = get_conn()
    conn.execute(
        """INSERT OR IGNORE INTO ventes(id,router_id,date,heure,user,profil,prix,devise,reseau,data_limit,ticket_key)
           VALUES(:id,:router_id,:date,:heure,:user,:profil,:prix,:devise,:reseau,:data_limit,:ticket_key)""",
        vente
    )
    conn.commit()


def db_upsert_ticket_pricing(data: dict):
    """Enregistre le prix d'un ticket au moment de sa création (pour récupération lors du sync)."""
    db_batch_upsert_ticket_pricing([data])


def db_batch_upsert_ticket_pricing(data_list: list):
    """Enregistre les prix d'un lot de tickets en une seule transaction."""
    if not data_list:
        return
    conn = get_conn()
    rows = [
        {
            "router_id": d.get("router_id", ""),
            "user":      d.get("user", ""),
            "password":  d.get("password", "") or d.get("pass", "") or d.get("user", "") or "",
            "prix":      float(d.get("prix", 0) or 0),
            "devise":    d.get("devise", "FCFA") or "FCFA",
            "profil":    d.get("profil", "") or "",
            "reseau":    d.get("reseau", "") or "",
        }
        for d in data_list
    ]
    conn.executemany(
        """INSERT INTO ticket_pricing(router_id,user,password,prix,devise,profil,reseau)
           VALUES(:router_id,:user,:password,:prix,:devise,:profil,:reseau)
           ON CONFLICT(router_id,user) DO UPDATE SET
               password=excluded.password, prix=excluded.prix, devise=excluded.devise,
               profil=excluded.profil, reseau=excluded.reseau""",
        rows
    )
    conn.commit()


def db_backfill_ventes_from_ticket_pricing(router_id: str) -> int:
    """Crée des entrées ventes pour tous les tickets de ticket_pricing sans vente.
    Logique métier : un ticket créé = une vente (indépendamment de l'utilisation).
    Utilise ticket_pricing.created_at comme date de vente."""
    import uuid as _uuid
    from datetime import datetime as _dt
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0
    conn = get_conn()
    rows = conn.execute("""
        SELECT tp.router_id, tp.user, tp.profil,
               CAST(tp.prix AS REAL) AS prix,
               tp.devise, tp.reseau, tp.created_at
        FROM ticket_pricing tp
        LEFT JOIN ventes v ON v.router_id = tp.router_id AND v.user = tp.user
        WHERE tp.router_id = ?
          AND CAST(tp.prix AS REAL) > 0
          AND v.id IS NULL
    """, (router_id,)).fetchall()
    if not rows:
        return 0
    ventes = []
    for row in rows:
        created_at = str(row["created_at"] or "")
        try:
            dt = _dt.fromisoformat(created_at.replace("Z", "+00:00")).replace(tzinfo=None)
            date_str = dt.strftime("%Y-%m-%d")
            time_str = dt.strftime("%H:%M:%S")
        except Exception:
            now = _dt.now()
            date_str = now.strftime("%Y-%m-%d")
            time_str = now.strftime("%H:%M:%S")
        ventes.append({
            "id":         _uuid.uuid4().hex,
            "router_id":  row["router_id"],
            "date":       date_str,
            "heure":      time_str,
            "user":       row["user"],
            "profil":     row["profil"] or "",
            "prix":       float(row["prix"] or 0),
            "devise":     row["devise"] or "FCFA",
            "reseau":     row["reseau"] or "",
            "data_limit": "0",
            "ticket_key": row["user"],
        })
    if not ventes:
        return 0
    conn.executemany(
        """INSERT OR IGNORE INTO ventes(id,router_id,date,heure,user,profil,prix,devise,reseau,data_limit,ticket_key)
           VALUES(:id,:router_id,:date,:heure,:user,:profil,:prix,:devise,:reseau,:data_limit,:ticket_key)""",
        ventes
    )
    conn.commit()
    return len(ventes)


def db_set_ticket_expiry(router_id: str, username: str, first_used_at: str, expire_at: str):
    """Sauvegarde first_used_at et expire_at dans ticket_pricing pour un ticket.
    Persistance côté serveur de l'expiration absolue, indépendante du commentaire MikroTik."""
    router_id = str(router_id or "").strip()
    username  = str(username  or "").strip()
    if not router_id or not username:
        return
    conn = get_conn()
    conn.execute(
        "UPDATE ticket_pricing SET first_used_at=?, expire_at=? WHERE router_id=? AND user=?",
        (str(first_used_at or ""), str(expire_at or ""), router_id, username),
    )
    conn.commit()


def db_delete_ticket_pricing(router_id: str, users) -> int:
    """Supprime de la DB les tickets/prix qui n'existent plus sur le MikroTik."""
    router_id = str(router_id or "").strip()
    usernames = sorted({
        str(user or "").strip()
        for user in (users or [])
        if str(user or "").strip()
    })
    if not router_id or not usernames:
        return 0

    conn = get_conn()
    before = conn.total_changes
    conn.executemany(
        "DELETE FROM ticket_pricing WHERE router_id=? AND user=?",
        [(router_id, username) for username in usernames],
    )
    conn.commit()
    return max(conn.total_changes - before, 0)


def db_prune_missing_ticket_pricing(router_id: str, existing_users) -> int:
    """Nettoie les tickets/prix DB absents de /ip/hotspot/user pour ce routeur."""
    router_id = str(router_id or "").strip()
    if not router_id:
        return 0

    existing = {
        str(user or "").strip()
        for user in (existing_users or [])
        if str(user or "").strip()
    }
    conn = get_conn()
    rows = conn.execute(
        "SELECT user FROM ticket_pricing WHERE router_id=?",
        (router_id,),
    ).fetchall()
    missing = [
        str(row["user"] or "").strip()
        for row in rows
        if str(row["user"] or "").strip() and str(row["user"] or "").strip() not in existing
    ]
    return db_delete_ticket_pricing(router_id, missing)


def _router_clause(router_ids):
    """Retourne (clause SQL, params) pour filtrer par un ou plusieurs router_ids."""
    if isinstance(router_ids, str):
        router_ids = [router_ids]
    router_ids = [r for r in router_ids if r]
    if not router_ids:
        return "1=0", []
    if len(router_ids) == 1:
        return "router_id = ?", [router_ids[0]]
    placeholders = ",".join("?" * len(router_ids))
    return f"router_id IN ({placeholders})", list(router_ids)


def db_get_ventes(router_id, date_from: str = "",
                  jour: str = "", mois: str = "", annee: str = "", q: str = "", profil: str = ""):
    """router_id peut être un str ou une liste de str."""
    conn = get_conn()
    rid_clause, params = _router_clause(router_id)
    clauses = [rid_clause]
    if annee and mois:
        try:
            y, m = int(annee), int(mois)
            nm, ny = (m + 1, y) if m < 12 else (1, y + 1)
            clauses.append("date >= ? AND date < ?")
            params += [f"{y:04d}-{m:02d}-01", f"{ny:04d}-{nm:02d}-01"]
        except ValueError:
            clauses.append("substr(date,1,7) = ?")
            params.append(f"{annee}-{mois}")
        if jour:
            clauses.append("substr(date,9,2) = ?"); params.append(jour.zfill(2))
    elif annee:
        clauses.append("date LIKE ?"); params.append(f"{annee}-%")
        if jour:
            clauses.append("substr(date,9,2) = ?"); params.append(jour.zfill(2))
    elif mois:
        clauses.append("substr(date,6,2) = ?"); params.append(mois.zfill(2))
        if jour:
            clauses.append("substr(date,9,2) = ?"); params.append(jour.zfill(2))
    elif jour:
        clauses.append("substr(date,9,2) = ?"); params.append(jour.zfill(2))
    if profil:
        clauses.append("profil = ?"); params.append(profil)
    if q:
        clauses.append("(user LIKE ? OR profil LIKE ? OR reseau LIKE ?)")
        params += [f"%{q}%", f"%{q}%", f"%{q}%"]
    sql = "SELECT * FROM ventes WHERE " + " AND ".join(clauses) + " ORDER BY date DESC, heure DESC"
    return [dict(r) for r in conn.execute(sql, params).fetchall()]


def db_get_ventes_summary(router_id, today_str: str, month_str: str):
    """router_id peut être un str ou une liste de str (tous les routeurs de l'utilisateur)."""
    conn = get_conn()
    rid_clause, base_params = _router_clause(router_id)
    today = conn.execute(
        f"SELECT COUNT(*) cnt, COALESCE(SUM(prix),0) tot, devise FROM ventes WHERE {rid_clause} AND date=? GROUP BY devise ORDER BY tot DESC LIMIT 1",
        base_params + [today_str]
    ).fetchone()
    month = conn.execute(
        f"SELECT COUNT(*) cnt, COALESCE(SUM(prix),0) tot, devise FROM ventes WHERE {rid_clause} AND date LIKE ? GROUP BY devise ORDER BY tot DESC LIMIT 1",
        base_params + [f"{month_str}-%"]
    ).fetchone()
    today = dict(today) if today else {}
    month = dict(month) if month else {}
    cur = today.get("devise") or month.get("devise") or "FCFA"
    return {
        "today_count": today.get("cnt", 0),
        "today_total": today.get("tot", 0.0),
        "month_count": month.get("cnt", 0),
        "month_total": month.get("tot", 0.0),
        "currency":    cur,
    }

def db_delete_vente(vente_id: str, router_id: str) -> bool:
    conn = get_conn()
    cur = conn.execute("DELETE FROM ventes WHERE id=? AND router_id=?", (vente_id, router_id))
    conn.commit()
    return cur.rowcount > 0

def db_delete_ventes_mois(router_id: str, mois: str) -> int:
    conn = get_conn()
    cur = conn.execute(
        "DELETE FROM ventes WHERE router_id=? AND date LIKE ?",
        (router_id, f"{mois}-%")
    )
    conn.commit()
    return cur.rowcount


# ── Agent incidents ────────────────────────────────────────────────────────────

def db_agent_create_incident(level: str, category: str, title: str,
                              description: str = "", router_id: str = "",
                              router_name: str = "", fix_action: str = "",
                              auto_fixed: bool = False) -> str:
    conn = get_conn()
    inc_id = str(uuid.uuid4())
    fix_status = "auto_fixed" if auto_fixed else "pending"
    conn.execute(
        """INSERT INTO agent_incidents
           (id, level, category, title, description, router_id, router_name,
            auto_fixed, fix_status, fix_action)
           VALUES (?,?,?,?,?,?,?,?,?,?)""",
        (inc_id, level, category, title, description,
         router_id or "", router_name or "",
         1 if auto_fixed else 0, fix_status, fix_action or "")
    )
    conn.commit()
    return inc_id


def db_agent_incident_exists(category: str, router_id: str = "", title: str = "") -> bool:
    """Vérifie si un incident non résolu du même type existe déjà (évite les doublons)."""
    conn = get_conn()
    if router_id:
        row = conn.execute(
            "SELECT id FROM agent_incidents WHERE category=? AND router_id=? AND title=? AND resolved=0",
            (category, router_id, title)
        ).fetchone()
    else:
        row = conn.execute(
            "SELECT id FROM agent_incidents WHERE category=? AND title=? AND resolved=0",
            (category, title)
        ).fetchone()
    return row is not None


def db_agent_get_incidents(resolved: bool = False, limit: int = 100) -> list:
    conn = get_conn()
    rows = conn.execute(
        "SELECT * FROM agent_incidents WHERE resolved=? ORDER BY created_at DESC LIMIT ?",
        (1 if resolved else 0, limit)
    ).fetchall()
    return [dict(r) for r in rows]


def db_agent_count_open() -> int:
    conn = get_conn()
    row = conn.execute("SELECT COUNT(*) FROM agent_incidents WHERE resolved=0").fetchone()
    return row[0] if row else 0


def db_agent_get_incident(inc_id: str) -> dict | None:
    conn = get_conn()
    row = conn.execute("SELECT * FROM agent_incidents WHERE id=?", (inc_id,)).fetchone()
    return dict(row) if row else None


def db_agent_approve_incident(inc_id: str) -> bool:
    conn = get_conn()
    cur = conn.execute(
        "UPDATE agent_incidents SET fix_status='approved' WHERE id=? AND resolved=0",
        (inc_id,)
    )
    conn.commit()
    return cur.rowcount > 0


def db_agent_reject_incident(inc_id: str) -> bool:
    conn = get_conn()
    cur = conn.execute(
        """UPDATE agent_incidents SET fix_status='rejected', resolved=1,
           resolved_at=datetime('now','localtime') WHERE id=?""",
        (inc_id,)
    )
    conn.commit()
    return cur.rowcount > 0


def db_agent_resolve_incident(inc_id: str, fix_result: str = "") -> bool:
    conn = get_conn()
    cur = conn.execute(
        """UPDATE agent_incidents SET resolved=1, fix_status='done',
           fix_result=?, resolved_at=datetime('now','localtime') WHERE id=?""",
        (fix_result, inc_id)
    )
    conn.commit()
    return cur.rowcount > 0


def db_agent_requeue_incident(inc_id: str, fix_result: str = "") -> bool:
    conn = get_conn()
    cur = conn.execute(
        """UPDATE agent_incidents
           SET fix_status='pending', fix_result=?, resolved=0, resolved_at=NULL
           WHERE id=? AND resolved=0""",
        (fix_result, inc_id)
    )
    conn.commit()
    return cur.rowcount > 0


def db_agent_resolve_by_category(category: str, router_id: str = "") -> int:
    conn = get_conn()
    if router_id:
        cur = conn.execute(
            """UPDATE agent_incidents SET resolved=1, resolved_at=datetime('now','localtime')
               WHERE category=? AND router_id=? AND resolved=0""",
            (category, router_id)
        )
    else:
        cur = conn.execute(
            """UPDATE agent_incidents SET resolved=1, resolved_at=datetime('now','localtime')
               WHERE category=? AND resolved=0""",
            (category,)
        )
    conn.commit()
    return cur.rowcount
