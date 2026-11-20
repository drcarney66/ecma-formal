#!/usr/bin/env python3
"""tools/dbg/serve.py: what the debugger's page needs from it.

Every response carries COOP, COEP and CORP, none with --plain; the wasm is `application/wasm` with no
Cache-Control, a module `text/javascript`; `/` is test.html, or --page's page (its
query kept in the printed URL); a file root is served
by its name; `..` and paths outside the roots are 404; without --test POST is
404; with it, /result ends the server with status 0 on a passing result and 1 on
a failing one. With --engine (a stand-in engine here), a session writes its
program, passes requests in order, sets the poll byte for `pause`, streams stdout,
stderr and the exit status as Server-Sent Events, ends at close and DELETE, is
killed if its events are not asked for in time, and refuses another Host or
Origin, a non-JSON body, a junk Content-Length and a name with a path.

    bazel test //:dbg_serve_test
"""

import http.client
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
import urllib.error
import urllib.request
from pathlib import Path

SERVE = Path("tools/dbg/serve.py")

# The stand-in engine: answers each request line with {request_seq, command, poll}
# (the poll byte), `read` with its program's text too, says "bye" on stderr at the
# end of its input and exits 3.
ENGINE = r"""
import json, sys
poll = sys.argv[sys.argv.index("--dbg-poll") + 1]
for line in sys.stdin:
    req = json.loads(line)
    out = {"type": "response", "request_seq": req["seq"], "command": req["command"], "poll": open(poll, "rb").read(1)[0]}
    if req["command"] == "read":
        out["text"] = open(req["arguments"]["path"]).read()
    print(json.dumps(out), flush=True)
print("bye", file=sys.stderr, flush=True)
sys.exit(3)
"""


def start(test: bool, *roots: Path, engine: Path | None = None, tmp: Path | None = None, claim_s: float | None = None, page: str | None = None, plain: bool = False) -> tuple[subprocess.Popen, str, str]:
    """serve.py on `roots` (its TMPDIR `tmp`), its base URL and its first line."""
    claim = ["--claim-s", str(claim_s)] if claim_s else []
    pages = ["--page", page] if page else []
    p = subprocess.Popen(
        [sys.executable, str(SERVE), *(["--test"] if test else []), *(["--plain"] if plain else []), *(["--engine", str(engine)] if engine else []), *claim, *pages, *map(str, roots)],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        env={**os.environ, **({"TMPDIR": str(tmp)} if tmp else {})},
    )
    line = p.stdout.readline().strip()
    url = line.removeprefix("serving ")
    return p, url[: url.index("/", len("http://"))], line


def get(url: str, method: str = "GET", data: bytes | None = None, headers: dict | None = None):
    req = urllib.request.Request(url, method=method, data=data, headers=headers or {})
    try:
        with urllib.request.urlopen(req, timeout=10) as r:
            return r.status, dict(r.headers), r.read()
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers), e.read()


class ServeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        d = Path(self.tmp.name)
        self.root = d / "root"
        (self.root / "sub").mkdir(parents=True)
        (self.root / "test.html").write_text("<p>page</p>")
        (self.root / "a.mjs").write_text("export {};")
        (self.root / "sub" / "b.json").write_text("{}")
        (d / "secret.txt").write_text("no")
        self.wasm = d / "web" / "x.wasm"
        self.wasm.parent.mkdir()
        self.wasm.write_bytes(b"\0asm")

    def tearDown(self):
        self.tmp.cleanup()

    def serve(self, test=False):
        p, base, line = start(test, self.root, self.wasm)
        self.addCleanup(lambda: (p.kill(), p.wait(), p.stdout.close()))
        self.assertEqual(line, base + "/test.html?test" if test else "serving " + base + "/test.html")
        return p, base

    def test_headers_and_types(self):
        _, base = self.serve()
        for path, ctype in [
            ("/", "text/html"),
            ("/a.mjs", "text/javascript"),
            ("/sub/b.json", "application/json"),
            ("/x.wasm", "application/wasm"),
        ]:
            status, h, _ = get(base + path)
            self.assertEqual(status, 200, path)
            self.assertTrue(h["Content-Type"].startswith(ctype), (path, h["Content-Type"]))
            self.assertEqual(h["Cross-Origin-Opener-Policy"], "same-origin")
            self.assertEqual(h["Cross-Origin-Embedder-Policy"], "require-corp")
            self.assertEqual(h["Cross-Origin-Resource-Policy"], "same-origin")
            self.assertEqual("Cache-Control" in h, path != "/x.wasm", path)
        self.assertEqual(get(base + "/x.wasm")[2], b"\0asm")

    def test_plain(self):
        p, base, _ = start(True, self.root, self.wasm, plain=True)
        self.addCleanup(lambda: (p.kill(), p.wait(), p.stdout.close()))
        for path in ["/", "/a.mjs", "/x.wasm"]:
            status, h, _ = get(base + path)
            self.assertEqual(status, 200, path)
            self.assertFalse({"Cross-Origin-Opener-Policy", "Cross-Origin-Embedder-Policy", "Cross-Origin-Resource-Policy"} & set(h), path)
        self.assertEqual(get(base + "/result", "POST", b'{"passed": 1, "failed": 0}')[0], 204)
        self.assertEqual(p.wait(10), 0)

    def test_outside_the_roots(self):
        _, base = self.serve()
        for path in [
            "/../secret.txt",
            "/%2e%2e/secret.txt",
            "/sub/../../secret.txt",
            "/missing",
            "/web/x.wasm",
            "/sub",
        ]:
            self.assertEqual(get(base + path)[0], 404, path)

    def test_page(self):
        (self.root / "sub" / "p.html").write_text("<p>ui</p>")
        for test, want in [(False, "serving {}/sub/p.html?x=1"), (True, "{}/sub/p.html?x=1&test")]:
            p, base, line = start(test, self.root, page="sub/p.html?x=1")
            self.addCleanup(lambda p=p: (p.kill(), p.wait(), p.stdout.close()))
            self.assertEqual(line, want.format(base))
            status, h, body = get(base + "/")
            self.assertEqual((status, body), (200, b"<p>ui</p>"))
            self.assertTrue(h["Content-Type"].startswith("text/html"))
            self.assertEqual(get(base + "/test.html")[2], b"<p>page</p>")

    def test_post_needs_test(self):
        _, base = self.serve()
        self.assertEqual(get(base + "/result", "POST", b"{}")[0], 404)

    def test_result_status(self):
        for result, want in [
            ({"passed": 3, "failed": 0}, 0),
            ({"passed": 3, "failed": 1}, 1),
            ({"passed": 0, "failed": 0}, 1),
        ]:
            p, base = self.serve(test=True)
            self.assertEqual(get(base + "/log", "POST", b"line")[0], 204)
            self.assertEqual(get(base + "/result", "POST", json.dumps(result).encode())[0], 204)
            self.assertEqual(p.wait(10), want, result)
            self.assertEqual(json.loads(p.stdout.readline()), result)


JSON = {"Content-Type": "application/json"}


def post(url: str, value=None, headers: dict | None = None):
    return get(url, "POST", b"" if value is None else json.dumps(value).encode(), {**JSON, **(headers or {})})


def events(resp) -> list[tuple[str, str]]:
    """The (event, data) pairs of a Server-Sent Events stream, until it ends."""
    out, name, data = [], "message", []
    for raw in resp:
        line = raw.decode().rstrip("\n")
        if line == "":
            if data:
                out.append((name, "\n".join(data)))
            name, data = "message", []
        elif line.startswith("event: "):
            name = line[7:]
        elif line.startswith("data: "):
            data.append(line[6:])
    return out


class EngineTest(unittest.TestCase):
    CLAIM_S = 3.0

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        d = Path(self.tmp.name)
        (d / "root").mkdir()
        self.engine = d / "engine"
        self.engine.write_text(f"#!{sys.executable}\n{ENGINE}")
        self.engine.chmod(0o755)
        self.dirs = d / "tmp"
        self.dirs.mkdir()
        p, self.base, line = start(False, d / "root", engine=self.engine, tmp=self.dirs, claim_s=self.CLAIM_S)
        self.addCleanup(self.tmp.cleanup)
        self.addCleanup(lambda: self.assertEqual(list((d / "tmp").iterdir()), []))
        self.addCleanup(lambda: (p.terminate(), p.wait(10), p.stdout.close()))
        self.assertEqual(line, "serving " + self.base + "/test.html?native")

    def session(self, program=None) -> tuple[str, dict]:
        status, _, body = post(self.base + "/session", {"program": program})
        self.assertEqual(status, 201, body)
        made = json.loads(body)
        return self.base + "/session/" + made["id"], made

    def test_session(self):
        url, made = self.session({"name": "a.js", "source": "print(1);\n"})
        self.assertEqual(made["program"], "work/a.js")
        with urllib.request.urlopen(url + "/events", timeout=10) as r:
            self.assertEqual(r.headers["Content-Type"], "text/event-stream")
            self.assertEqual(r.headers["Cross-Origin-Embedder-Policy"], "require-corp")
            msgs = []
            for seq, command, args in [(1, "read", {"path": made["program"]}), (2, "next", {}), (3, "pause", {})]:
                self.assertEqual(post(url, {"seq": seq, "type": "request", "command": command, "arguments": args})[0], 204)
                msgs.append(json.loads(r.readline().decode().removeprefix("data: ")))
                self.assertEqual(r.readline(), b"\n")
            self.assertEqual(post(url + "/close")[0], 204)
            got = events(r)
        self.assertEqual([m["command"] for m in msgs], ["read", "next", "pause"])
        self.assertEqual(msgs[0]["text"], "print(1);\n")
        self.assertEqual([m["poll"] for m in msgs], [0, 0, 1])
        self.assertEqual(got, [("stderr", "bye"), ("exit", "3")])
        self.assertEqual(get(url + "/events")[0], 404)

    def test_pause_and_delete(self):
        url, made = self.session()
        self.assertIsNone(made["program"])
        self.assertEqual(post(url + "/pause")[0], 204)
        self.assertEqual(post(url, {"seq": 1, "type": "request", "command": "next"})[0], 204)
        with urllib.request.urlopen(url + "/events", timeout=10) as r:
            first = r.readline() + r.readline()
            self.assertEqual(json.loads(first.decode()[6:])["poll"], 1)
            self.assertEqual(get(url + "/events")[0], 409)
            self.assertEqual(get(url, "DELETE")[0], 204)
            got = events(r)
        self.assertEqual(got[-1][0], "exit")
        self.assertNotEqual(got[-1][1], "0")
        self.assertEqual(get(url, "DELETE")[0], 404)

    def test_unclaimed(self):
        url, _ = self.session()
        self.assertEqual(len(list(self.dirs.iterdir())), 1)
        deadline = time.monotonic() + self.CLAIM_S + 10
        while list(self.dirs.iterdir()) and time.monotonic() < deadline:
            time.sleep(0.2)
        self.assertEqual(list(self.dirs.iterdir()), [])
        self.assertEqual(get(url + "/events")[0], 404)
        self.assertEqual(post(url, {"seq": 1, "type": "request", "command": "next"})[0], 404)

    def test_refused(self):
        port = self.base.rsplit(":", 1)[1]
        prog = {"program": None}
        self.assertEqual(post(self.base + "/session", prog, {"Host": "evil.example:" + port})[0], 403)
        self.assertEqual(post(self.base + "/session", prog, {"Origin": "http://evil.example"})[0], 403)
        self.assertEqual(post(self.base + "/session", prog, {"Origin": self.base})[0], 201)
        self.assertEqual(get(self.base + "/session", "POST", json.dumps(prog).encode(), {"Content-Type": "text/plain"})[0], 415)
        for name in ["../x.js", "a/b.js", ".x", ""]:
            self.assertEqual(post(self.base + "/session", {"program": {"name": name, "source": ""}})[0], 400, name)
        self.assertEqual(post(self.base + "/session/0123456789abcdef", {"seq": 1})[0], 404)
        self.assertEqual(get(self.base + "/session")[0], 405)
        c = http.client.HTTPConnection(self.base.removeprefix("http://"), timeout=10)
        c.putrequest("POST", "/session")
        c.putheader("Content-Type", "application/json")
        c.putheader("Content-Length", "abc")
        c.endheaders()
        r = c.getresponse()
        self.assertEqual((r.status, r.getheader("Connection")), (400, "close"))
        c.close()


if __name__ == "__main__":
    unittest.main()
