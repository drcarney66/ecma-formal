#!/usr/bin/env python3
"""Serves the debugger's page and its Worker build on 127.0.0.1.

    serve.py [--port N] [--test] [--plain] [--engine ECMA_DBG [--claim-s S]] [--page PATH] ROOT...
    serve.py --engine .lake/build/bin/ecma-dbg --page ui/index.html tools/dbg
    serve.py --page index.html dist                 # the built site (scripts/build_site.py)

Each ROOT is a directory, whose files are served by their paths under it, or a
file, served as /NAME; a path is looked up in the roots in order, a directory's
`DIR/` as its index.html (and `DIR` redirected to `DIR/`). `/` is
the page, --page (test.html by default; a query in it is kept in the printed
URL). Every response is cross-origin isolated (COOP same-origin, COEP
require-corp, CORP same-origin), which SharedArrayBuffer needs in the page and
its Worker (tools/dbg/ring.mjs); with --plain, none is (a plain static host, where
coi-serviceworker.js isolates the page). The wasm is `application/wasm` and has no
caching headers; everything else is `no-store`, so an edited page loads anew.

With --test, `POST /log` prints a line to stderr, and `POST /result` takes the
page's JSON result ({passed, failed, ...}), prints it on stdout as one line and
ends the server: status 0 if nothing failed and something passed, else 1.

With --engine, the page's sessions run native ecma-dbg (the `native-http`
transport of tools/dbg/client.mjs), and the printed URL has `?native`:
  POST /session {program: {name, source} | null}
      spawns ecma-dbg in a new directory, the program written to work/NAME in
      it; answers 201 {id, program} (the program's path, relative to the
      engine's directory)
  POST /session/ID REQUEST   writes the request as a line to its stdin; a
      `pause` request first sets the poll file's byte (`--dbg-poll`)
  POST /session/ID/pause     sets the poll byte only
  POST /session/ID/close     closes its stdin
  GET /session/ID/events     Server-Sent Events, once per session: each
      stdout line as `data`, each stderr line as event `stderr`, then event
      `exit` with its status; a dropped stream kills the engine (noticed at
      the next keepalive or two, ~2*KEEPALIVE_S); a session whose events are
      not asked for within --claim-s seconds of its creation is killed
  DELETE /session/ID         kills it
Session requests need the server's own Host, a same-origin Origin if any, and
POSTs a JSON body (`application/json`), so another site's page cannot drive
them. At most MAX_SESSIONS engines run at once; all are killed at the end.
At most MAX_QUEUE lines of a session wait for its stream; beyond them the
engine waits.
"""

import argparse
import json
import os
import queue
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlparse

TYPES = {
    ".html": "text/html; charset=utf-8",
    ".mjs": "text/javascript; charset=utf-8",
    ".js": "text/javascript; charset=utf-8",
    ".json": "application/json",
    ".wasm": "application/wasm",
    ".dbg": "text/plain; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".svg": "image/svg+xml",
    ".txt": "text/plain; charset=utf-8",
}
ISOLATION = {
    "Cross-Origin-Opener-Policy": "same-origin",
    "Cross-Origin-Embedder-Policy": "require-corp",
    "Cross-Origin-Resource-Policy": "same-origin",
}
MAX_POST = 16 << 20
MAX_SESSIONS = 8
MAX_QUEUE = 4096
CLAIM_S = 10.0
PROGRAM_NAME = re.compile(r"[A-Za-z0-9_][A-Za-z0-9._-]{0,127}")
KEEPALIVE_S = 5


class Session:
    """One native ecma-dbg: its directory, poll file, pipes and the queue of its events."""

    def __init__(self, engine: str, program: dict | None):
        self.dir = Path(tempfile.mkdtemp(prefix="ecma-dbg-"))
        self.poll = self.dir / "poll"
        self.program = None if program is None else f"work/{program['name']}"
        self.events: queue.Queue[tuple[str, str]] = queue.Queue(MAX_QUEUE)
        self.listening = False
        self.expired = False
        self.abandoned = False
        self.lock = threading.Lock()
        try:
            self.poll.write_bytes(b"\0")
            if program is not None:
                (self.dir / "work").mkdir()
                (self.dir / self.program).write_text(program["source"], encoding="utf-8")
            self.proc = subprocess.Popen(
                [engine, "--dbg-poll", str(self.poll)],
                cwd=self.dir,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
        except OSError:
            shutil.rmtree(self.dir, ignore_errors=True)
            raise
        readers = [
            threading.Thread(target=self.read, args=(self.proc.stdout, "message"), daemon=True),
            threading.Thread(target=self.read, args=(self.proc.stderr, "stderr"), daemon=True),
        ]
        for t in readers:
            t.start()
        threading.Thread(target=self.reap, args=(readers,), daemon=True).start()

    def put(self, event: tuple[str, str]) -> None:
        """An event to the queue, waiting while it is full; dropped once nobody will read it."""
        while not self.abandoned:
            try:
                self.events.put(event, timeout=1)
                return
            except queue.Full:
                pass

    def read(self, stream, kind: str) -> None:
        for raw in stream:
            self.put((kind, raw.decode("utf-8", "replace").rstrip("\r\n")))

    def reap(self, readers: list[threading.Thread]) -> None:
        for t in readers:
            t.join()
        code = self.proc.wait()
        shutil.rmtree(self.dir, ignore_errors=True)
        self.put(("exit", str(code if code >= 0 else 128 - code)))

    def alive(self) -> bool:
        return self.proc.poll() is None

    def pause(self) -> None:
        """The poll byte to 1, in place: the engine keeps the file open."""
        try:
            fd = os.open(self.poll, os.O_WRONLY)
        except OSError:
            return
        try:
            os.pwrite(fd, b"\1", 0)
        finally:
            os.close(fd)

    def write(self, data: bytes | None) -> bool:
        """A line to stdin (None: close it); False if it is closed."""
        with self.lock:
            try:
                if data is None:
                    self.proc.stdin.close()
                else:
                    self.proc.stdin.write(data + b"\n")
                    self.proc.stdin.flush()
                return True
            except (OSError, ValueError):
                return False

    def kill(self) -> None:
        if self.alive():
            self.proc.kill()


class Sessions:
    """The live sessions by id."""

    def __init__(self, engine: str, claim_s: float = CLAIM_S):
        self.engine = engine
        self.claim_s = claim_s
        self.by_id: dict[str, Session] = {}
        self.lock = threading.Lock()

    def new(self, program: dict | None) -> tuple[str, Session] | None:
        with self.lock:
            if sum(s.alive() for s in self.by_id.values()) >= MAX_SESSIONS:
                return None
            sid = secrets.token_hex(8)
            s = self.by_id[sid] = Session(self.engine, program)
        timer = threading.Timer(self.claim_s, self.expire, (sid, s))
        timer.daemon = True
        timer.start()
        return sid, s

    def expire(self, sid: str, s: Session) -> None:
        """Kills and drops the session if its events are not streamed yet."""
        with s.lock:
            if s.listening:
                return
            s.expired = s.abandoned = True
        self.drop(sid)

    def get(self, sid: str) -> Session | None:
        with self.lock:
            return self.by_id.get(sid)

    def drop(self, sid: str) -> None:
        with self.lock:
            s = self.by_id.pop(sid, None)
        if s:
            s.kill()

    def kill_all(self) -> None:
        with self.lock:
            live, self.by_id = list(self.by_id.values()), {}
        for s in live:
            s.abandoned = True
            s.kill()
            try:
                s.proc.wait(5)
            except subprocess.TimeoutExpired:
                pass
            shutil.rmtree(s.dir, ignore_errors=True)


def lookup(roots: list[Path], url_path: str) -> Path | None:
    """The file that `url_path` names in the first root that has it, or None.

    The path is checked before symlinks are followed: a Bazel runfiles tree
    is links out of it."""
    parts = [p for p in unquote(url_path).split("/") if p]
    if not parts or any(p in (".", "..") or "\\" in p or "\0" in p for p in parts):
        return None
    for root in roots:
        if root.is_file():
            if len(parts) == 1 and parts[0] == root.name:
                return root
        else:
            f = root.joinpath(*parts)
            if f.is_file():
                return f
            if f.is_dir() and (f / "index.html").is_file():
                return f / "index.html" if url_path.endswith("/") else f
    return None


def program_of(body: object) -> dict | None | str:
    """POST /session's program ({name, source} or None), or why it is refused."""
    if not isinstance(body, dict):
        return "the body is not an object"
    p = body.get("program")
    if p is None:
        return None
    if not isinstance(p, dict) or not isinstance(p.get("name"), str) or not isinstance(p.get("source"), str):
        return "program is not {name, source}"
    if not PROGRAM_NAME.fullmatch(p["name"]):
        return "the program's name is not a plain file name"
    return {"name": p["name"], "source": p["source"]}


def make_handler(roots: list[Path], test: bool, done, sessions: Sessions | None = None, page: str = "test.html", plain: bool = False):
    isolation = {} if plain else ISOLATION

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):
            pass

        def send(self, status: int, body: bytes, ctype: str, cache: bool = False) -> None:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            for k, v in isolation.items():
                self.send_header(k, v)
            if not cache:
                self.send_header("Cache-Control", "no-store")
            if self.close_connection:
                self.send_header("Connection", "close")
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)

        def send_json(self, status: int, value: object) -> None:
            self.send(status, json.dumps(value).encode(), "application/json")

        def refuse(self, status: int, why: str) -> None:
            """An error, and the connection closed: the request's body may be unread."""
            self.close_connection = True
            self.send(status, (why + "\n").encode(), "text/plain; charset=utf-8")

        def length(self) -> int | None:
            """The request's Content-Length (0 if none), or None if it is not a number."""
            try:
                return int(self.headers.get("Content-Length") or 0)
            except ValueError:
                return None

        def own_origin(self) -> bool:
            """The Host is this server's and the Origin, if any, too: no other site, no DNS rebinding."""
            port = self.server.server_address[1]
            hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
            origin = self.headers.get("Origin")
            return self.headers.get("Host") in hosts and (origin is None or origin in {f"http://{h}" for h in hosts})

        def session_route(self, path: str) -> tuple[str, str] | None:
            """(id, rest) of a /session/ID[/rest] path, ("", "") for /session, or None."""
            if path == "/session":
                return "", ""
            m = re.fullmatch(r"/session/([0-9a-f]{16})(/[a-z]+)?", path)
            return (m.group(1), m.group(2) or "") if m else None

        def json_body(self) -> object:
            """The POST's JSON body, or a str: why it is refused."""
            if self.headers.get_content_type() != "application/json":
                return "the body must be application/json"
            n = self.length()
            if n is None:
                return "the body's length is not a number"
            if not 0 <= n <= MAX_POST:
                return "the body is too large"
            raw = self.rfile.read(n)
            if not raw:
                return None
            try:
                return json.loads(raw)
            except ValueError:
                return "the body is not JSON"

        def session_request(self, route: tuple[str, str]) -> None:
            if not self.own_origin():
                self.refuse(403, "not this server's origin")
                return
            sid, rest = route
            if self.command == "POST":
                body = self.json_body()
                if isinstance(body, str):
                    self.refuse(415 if "application/json" in body else 400, body)
                    return
            if sid == "":
                if self.command != "POST":
                    self.refuse(405, "POST /session")
                    return
                program = program_of(body if body is not None else {})
                if isinstance(program, str):
                    self.refuse(400, program)
                    return
                try:
                    made = sessions.new(program)
                except OSError as e:
                    self.refuse(500, f"cannot start the engine: {e}")
                    return
                if made is None:
                    self.refuse(503, f"{MAX_SESSIONS} sessions already run")
                    return
                try:
                    self.send_json(201, {"id": made[0], "program": made[1].program})
                except OSError:
                    sessions.drop(made[0])
                return
            s = sessions.get(sid)
            if s is None:
                self.refuse(404, "no such session")
                return
            match self.command, rest:
                case "GET", "/events":
                    self.stream(sid, s)
                case "DELETE", "":
                    sessions.drop(sid)
                    self.send(204, b"", "text/plain")
                case "POST", "":
                    if not isinstance(body, dict):
                        self.refuse(400, "a request is a JSON object")
                        return
                    if body.get("command") == "pause":
                        s.pause()
                    ok = s.write(json.dumps(body).encode())
                    self.send(204, b"", "text/plain") if ok else self.refuse(410, "the engine's input is closed")
                case "POST", "/pause":
                    s.pause()
                    self.send(204, b"", "text/plain")
                case "POST", "/close":
                    s.write(None)
                    self.send(204, b"", "text/plain")
                case _:
                    self.refuse(404, "not found")

        def stream(self, sid: str, s: Session) -> None:
            """The session's events as Server-Sent Events, until its exit."""
            with s.lock:
                expired = s.expired
                taken, s.listening = s.listening, True
            if expired:
                self.refuse(404, "no such session")
                return
            if taken:
                self.refuse(409, "the session's events are already streamed")
                return
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            for k, v in isolation.items():
                self.send_header(k, v)
            self.end_headers()
            self.close_connection = True
            try:
                while True:
                    try:
                        kind, data = s.events.get(timeout=KEEPALIVE_S)
                    except queue.Empty:
                        self.wfile.write(b":\n\n")
                        self.wfile.flush()
                        continue
                    head = b"" if kind == "message" else f"event: {kind}\n".encode()
                    self.wfile.write(head + b"data: " + data.encode() + b"\n\n")
                    self.wfile.flush()
                    if kind == "exit":
                        break
            except OSError:
                pass
            s.abandoned = True
            sessions.drop(sid)

        def do_DELETE(self):
            route = self.session_route(urlparse(self.path).path) if sessions else None
            if route is None:
                self.refuse(404, "not found")
                return
            self.session_request(route)

        def do_GET(self):
            path = urlparse(self.path).path
            route = self.session_route(path) if sessions and self.command == "GET" else None
            if route is not None:
                self.session_request(route)
                return
            if path == "/":
                path = "/" + page
            f = lookup(roots, path)
            if f is None:
                self.send(404, b"not found\n", "text/plain; charset=utf-8")
                return
            if f.is_dir():  # a directory with an index.html, named without its slash
                self.send_response(301)
                self.send_header("Location", path + "/")
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            ctype = TYPES.get(f.suffix, "application/octet-stream")
            self.send(200, f.read_bytes(), ctype, cache=f.suffix == ".wasm")

        do_HEAD = do_GET

        def do_POST(self):
            path = urlparse(self.path).path
            route = self.session_route(path) if sessions else None
            if route is not None:
                self.session_request(route)
                return
            n = self.length()
            if n is None:
                self.refuse(400, "the body's length is not a number")
                return
            if not test or path not in ("/log", "/result") or not 0 <= n <= MAX_POST:
                self.refuse(404, "not found")
                return
            body = self.rfile.read(n)
            if path == "/log":
                print(body.decode("utf-8", "replace"), file=sys.stderr, flush=True)
                self.send(204, b"", "text/plain")
                return
            try:
                result = json.loads(body)
                ok = isinstance(result, dict) and result.get("failed") == 0 and (result.get("passed") or 0) > 0
            except ValueError:
                result, ok = {"unparsed": body.decode("utf-8", "replace")}, False
            self.send(204, b"", "text/plain")
            print(json.dumps(result), flush=True)
            done(0 if ok else 1)

    return Handler


class Server(ThreadingHTTPServer):
    """A thread per request; a client that went away is not an error."""

    daemon_threads = True
    # A burst of connections (a client without a per-host limit) waits instead of being reset.
    request_queue_size = 128

    def handle_error(self, request, client_address):
        if not isinstance(sys.exc_info()[1], ConnectionError):
            super().handle_error(request, client_address)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", type=int, default=0, help="0 (the default): any free port")
    ap.add_argument("--test", action="store_true", help="accept POST /log and /result; end at the result")
    ap.add_argument("--plain", action="store_true", help="no cross-origin isolation headers")
    ap.add_argument("--engine", help="native ecma-dbg: serve /session (the page's native-http transport)")
    ap.add_argument("--claim-s", type=float, default=CLAIM_S, help="seconds a new session waits for its events' stream")
    ap.add_argument("--page", default="test.html", help="the page `/` serves and the printed URL names, with its query if any")
    ap.add_argument("roots", nargs="+", type=Path, metavar="ROOT")
    args = ap.parse_args()
    page, _, page_query = args.page.lstrip("/").partition("?")
    roots = [r.absolute() for r in args.roots]
    missing = [str(r) for r in roots if not r.exists()]
    if missing:
        print(f"serve.py: no such root: {', '.join(missing)}", file=sys.stderr)
        return 2
    sessions = None
    if args.engine:
        engine = shutil.which(args.engine) if os.sep not in args.engine else str(Path(args.engine).absolute())
        if not engine or not os.access(engine, os.X_OK):
            print(f"serve.py: the engine is not an executable: {args.engine}", file=sys.stderr)
            return 2
        sessions = Sessions(engine, args.claim_s)
    status = []
    finished = threading.Event()

    def done(code: int) -> None:
        status.append(code)
        finished.set()

    server = Server(("127.0.0.1", args.port), make_handler(roots, args.test, done, sessions, page, args.plain))
    threading.Thread(target=lambda: finished.wait() and server.shutdown(), daemon=True).start()
    query = "&".join(q for q, on in ((page_query, page_query), ("test", args.test), ("native", sessions)) if on)
    url = f"http://127.0.0.1:{server.server_address[1]}/{page}" + (f"?{query}" if query else "")
    # SIGTERM ends it as ^C does, through the `finally` that kills the engines.
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt))
    print(f"serving {url}", file=sys.stderr if args.test else sys.stdout, flush=True)
    if args.test:
        print(url, flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        if sessions:
            sessions.kill_all()
    return status[0] if status else 0


if __name__ == "__main__":
    sys.exit(main())
