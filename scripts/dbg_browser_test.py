#!/usr/bin/env python3
"""The debugger suite in a headless browser, or in node for comparison.

    python3 scripts/dbg_browser_test.py --browser chrome --exe CHROME --web build/web/ecma-dbg-web.mjs \\
        --bundle build/dbg-tests.json
    python3 scripts/dbg_browser_test.py --browser chrome --exe CHROME --native .lake/build/bin/ecma-dbg \\
        --bundle build/dbg-tests.json
    python3 scripts/dbg_browser_test.py --browser node --exe NODE --web build/web/ecma-dbg-web.mjs \\
        --bundle build/dbg-tests.json

A browser: tools/dbg/serve.py --test serves tools/dbg, the Worker build and the
bundle, and the browser, on a profile in a new temporary directory, opens
test.html?test, which runs the suite (tools/dbg/runner.mjs) and POSTs its result,
which ends the server. The wait also ends when the browser's process group is
gone or at the timeout (inside a caller's TEST_TIMEOUT). The browser is then killed (its process
group), and the status is the server's: 0 if nothing failed. Node: tools/dbg/transcript.mjs
--suite. Either way the result's JSON is printed after `result:` (and written to
--result FILE).

With --native ECMA_DBG instead of --web, the sessions are native ecma-dbg behind
serve.py --engine (client.mjs's native-http transport): the page runs with
`?native`, and node runs transcript.mjs --native-http against the server.

With --page PATH[?query] (a browser only), the browser opens that page under
tools/dbg instead of test.html, with `?test`: ui/index.html runs the UI's
self-test (tools/dbg/ui/selftest.mjs), ui/index.html?demo the demo's scripts
(tools/dbg/ui/demotest.mjs), which POST their result the same way.

With --site DIST (scripts/build_site.py's dist/, or a tarball of it), serve.py --plain serves the site, with
no cross-origin isolation headers, as a plain static host does: the debugger's page isolates itself
(coi-serviceworker.js). --page then names a page of the site (debugger/?gallery&build=literal: the examples
and the selector, tools/dbg/ui/gallerytest.mjs; debugger/?demo; debugger/, the UI's self-test), and --bundle,
if given, is served as debugger/dbg-tests.json beside it (the self-test's programs; the site has no tests).
The site's layout is checked first: its VERSION, the pages, the shim, the builds and the WebAssembly build,
and no tests.
"""

import argparse
import json
import os
import queue
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from pathlib import Path

TOOLS = Path("tools/dbg")


def kill_group(p: subprocess.Popen) -> None:
    """Kills `p` and its children (its own process group, made by start_new_session)."""
    if p.poll() is None:
        try:
            os.killpg(p.pid, signal.SIGTERM)
            p.wait(5)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            pass
    # The group outlives its leader if a child is left (a browser's helpers).
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass
    try:
        p.wait(5)
    except subprocess.TimeoutExpired:
        pass


def browser_command(browser: str, exe: str, profile: str, url: str) -> list[str]:
    if browser == "chrome":
        return [
            exe,
            "--headless=new",
            f"--user-data-dir={profile}",
            "--no-first-run",
            "--no-default-browser-check",
            "--disable-extensions",
            "--use-mock-keychain",
            "--password-store=basic",
            url,
        ]
    return [exe, "--headless", "--profile", profile, "--no-remote", url]


def short_tmp(prefix: str) -> str:
    """A new directory under /tmp if it is writable, else under $TMPDIR.

    Bazel's $TMPDIR is too long for the AF_UNIX socket path (104 bytes) of
    Chrome's ProcessSingleton."""
    try:
        return tempfile.mkdtemp(prefix=prefix, dir="/tmp")
    except OSError:
        return tempfile.mkdtemp(prefix=prefix)


def group_alive(pgid: int) -> bool:
    """Whether any process is left in the process group `pgid`."""
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


SITE_FILES = ["VERSION", ".nojekyll", "index.html", "examples.html", "debugger/index.html", "debugger/VERSION",
              "debugger/coi-serviceworker.js", "debugger/builds.json", "debugger/examples.json",
              "debugger/ecma-dbg-web.mjs", "debugger/ecma-dbg-web.wasm", "debugger/ui/app.mjs"]


def site_dir(site: Path, tmp: str) -> Path:
    """The site's directory, the tarball extracted below `tmp`."""
    if site.is_dir():
        return site
    out = Path(tmp, "site")
    out.mkdir()
    with tarfile.open(site) as tar:
        tar.extractall(out, filter="data")
    return out


def site_problems(site: Path) -> list[str]:
    """What is wrong with the site's layout: a file missing, an empty VERSION or a test."""
    names = [str(f.relative_to(site)) for f in site.rglob("*") if f.is_file()]
    bad = [f"missing {n}" for n in SITE_FILES if n not in names]
    bad += [f"not for the site: {n}" for n in names if n.endswith("_test.mjs") or n.endswith("dbg-tests.json")]
    if "VERSION" in names and not (site / "VERSION").read_text().strip():
        bad.append("VERSION is empty")
    return bad


def serve_command(args, mjs: Path | None, test: bool) -> list[str]:
    """serve.py on tools/dbg, the bundle and the Worker build or (--native) the engine; --site: the site alone."""
    if args.site:
        extra = [str(args.extra_root)] if args.extra_root else []
        return [sys.executable, str(TOOLS / "serve.py"), "--plain", *(["--test"] if test else []), "--page", args.page,
                str(args.site_dir), *extra]
    roots = [str(TOOLS), args.bundle] + ([str(mjs), str(mjs.with_suffix(".wasm"))] if mjs else [])
    engine = ["--engine", args.native] if args.native else []
    page = ["--page", args.page] if args.page else []
    return [sys.executable, str(TOOLS / "serve.py"), *(["--test"] if test else []), *engine, *page, *roots]


def run_browser(args, mjs: Path | None) -> tuple[int, str]:
    """The server's status and its result line; ends at the result, the browser's exit or the timeout."""
    browser = serve = None
    tmp = short_tmp(f"dbg-{args.browser}-")
    profile, log = Path(tmp, "profile"), Path(tmp, "browser.log")
    profile.mkdir()
    try:
        if args.site:
            args.site_dir = site_dir(args.site, tmp)
            bad = site_problems(args.site_dir)
            for b in bad:
                print(f"site: {b}")
            if bad:
                return 1, ""
            print(f"site: VERSION {(args.site_dir / 'VERSION').read_text().strip()}", flush=True)
            args.extra_root = None
            if args.bundle:
                args.extra_root = Path(tmp, "extra")
                (args.extra_root / "debugger").mkdir(parents=True)
                shutil.copy(args.bundle, args.extra_root / "debugger/dbg-tests.json")
        serve = subprocess.Popen(
            serve_command(args, mjs, test=True),
            stdout=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        lines: queue.Queue[str] = queue.Queue()
        threading.Thread(target=lambda: [lines.put(l) for l in serve.stdout] + [lines.put("")], daemon=True).start()
        url = lines.get(timeout=30).strip()
        if not url.startswith("http://"):
            print(f"serve.py printed no URL: {url!r}")
            return 1, ""
        print(f"{args.browser}: {url}", flush=True)
        with log.open("wb") as err:
            browser = subprocess.Popen(
                browser_command(args.browser, args.exe, str(profile), url),
                stdin=subprocess.DEVNULL,
                stdout=err,
                stderr=None if args.verbose else err,
                env={**os.environ, "TMPDIR": tmp + "/"},
                start_new_session=True,
            )
        deadline = time.monotonic() + args.timeout
        while True:
            try:
                line = lines.get(timeout=1).strip()
                break
            except queue.Empty:
                pass
            if browser.poll() is not None and not group_alive(browser.pid):
                print(f"{args.browser} exited ({browser.returncode}) before a result")
                print_tail(log)
                return 1, ""
            if time.monotonic() > deadline:
                print(f"no result within {args.timeout:.0f} s")
                print_tail(log)
                return 1, ""
        if not line:
            print(f"serve.py exited ({serve.wait()}) without a result")
            return 1, ""
        try:
            status = serve.wait(10)
        except subprocess.TimeoutExpired:
            status = 1
        return (status if status >= 0 else 1), line
    except queue.Empty:
        print("serve.py printed no URL within 30 s")
        return 1, ""
    finally:
        if browser:
            kill_group(browser)
        if serve:
            kill_group(serve)
        shutil.rmtree(tmp, ignore_errors=True)


def print_tail(log: Path, n: int = 40) -> None:
    """The last `n` lines of the browser's output."""
    try:
        tail = log.read_text(errors="replace").splitlines()[-n:]
    except OSError:
        return
    for l in tail:
        print(f"  | {l}")


def run_node(args, mjs: Path | None) -> tuple[int, str]:
    serve = None
    if args.native:
        serve = subprocess.Popen(serve_command(args, None, test=False), stdout=subprocess.PIPE, text=True, start_new_session=True)
        first = serve.stdout.readline().strip()
        if not first.startswith("serving http://"):
            kill_group(serve)
            print(f"serve.py printed no URL: {first!r}")
            return 1, ""
        transport = ["--native-http", first.removeprefix("serving ").split("test.html")[0]]
    else:
        transport = ["--wasm-node", str(mjs)]
    cmd = [args.exe, str(TOOLS / "transcript.mjs"), *transport, "--suite", args.bundle]
    if args.stack_mb:
        cmd += ["--stack-mb", str(args.stack_mb)]
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, text=True, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        print(f"no result within {args.timeout} s")
        return 1, ""
    finally:
        if serve:
            kill_group(serve)
    lines = r.stdout.strip().splitlines()
    return r.returncode, lines[-1] if lines else ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--browser", required=True, choices=["chrome", "firefox", "node"])
    ap.add_argument("--exe", required=True, help="the browser, or node")
    engine = ap.add_mutually_exclusive_group(required=True)
    engine.add_argument("--web", help="ecma-dbg-web.mjs (its .wasm beside it)")
    engine.add_argument("--native", help="native ecma-dbg, behind serve.py --engine")
    engine.add_argument("--site", type=Path, help="the built site (dist/) or a tarball of it, served without isolation headers")
    ap.add_argument("--bundle", help="dbg-tests.json (scripts/dbg_browser_bundle.py); with --site, served beside the debugger's page")
    ap.add_argument("--page", help="a browser's page under tools/dbg instead of test.html (ui/index.html: the UI's self-test)")
    # Inside a caller's timeout ($TEST_TIMEOUT), if it sets one, so that the browser is still killed.
    timeout = min(1200.0, float(os.environ.get("TEST_TIMEOUT", 1260)) - 60)
    ap.add_argument("--timeout", type=float, default=timeout)
    ap.add_argument("--stack-mb", type=int, help="node only: the Worker's stack")
    ap.add_argument("--result", type=Path, help="write the result's JSON here too")
    ap.add_argument("--verbose", action="store_true", help="the browser's stderr too")
    args = ap.parse_args()
    if args.page and args.browser == "node":
        ap.error("--page needs a browser")
    if args.site and not (args.page and args.browser != "node"):
        ap.error("--site needs a browser and --page")
    if not args.site and not args.bundle:
        ap.error("--bundle is required without --site")
    # A caller's timeout or interrupt is SIGTERM: exit through run_browser's `finally`, which kills the browser.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    # A path without `.mjs` names the module beside it.
    mjs = None if args.native or args.site else Path(args.web if args.web.endswith(".mjs") else args.web + ".mjs")
    t0 = time.monotonic()
    status, line = (run_node if args.browser == "node" else run_browser)(args, mjs)
    print(f"{args.browser} ({'native' if args.native else 'site' if args.site else 'wasm'}): {time.monotonic() - t0:.0f} s, status {status}")
    if not line:
        return status or 1
    try:
        result = json.loads(line)
    except ValueError:
        print(f"not a result: {line[:500]}")
        return 1
    for f in result.get("failures", []):
        print(f"FAIL {f['name']}: {f['why']}")
    print(f"{result.get('passed', 0)} passed, {result.get('failed', 0)} failed")
    print("result: " + json.dumps(result))
    if args.result:
        args.result.write_text(json.dumps(result, indent=1) + "\n")
    return status


if __name__ == "__main__":
    sys.exit(main())
