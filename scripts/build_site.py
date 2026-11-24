#!/usr/bin/env python3
"""dist/: the whole site, the debugger with it, in one command.

    nix develop ~/.local/state/ecma-formal/devshell-wasm -c python3 scripts/build_site.py \\
        [--out dist] [--no-wasm] [-j N] [--build NAME=PATH[,ARG...]]... [--stale-ok] \\
        [--test262-record RECORD]

Run in the flake's wasm shell. It runs no Lean build: the Lean build's products in .lake/build must be there
and of the sources as they are (`lake build ecma-run ecma-dbg ecma-bundle`); if one is missing or of another
source, it stops and says so (--stale-ok goes on, says so, and the site's VERSION says so too). Then:

1. build/examples.json: the examples (tools/dbg/gallery.json, scripts/dbg_gallery.py).
2. build/web/ecma-dbg-web.{mjs,wasm}: the debugger's WebAssembly build (scripts/build_wasm.py; emcc over the
   Lean build's C, incremental). --no-wasm reuses build/web as it is.
3. build/builds.json: the debugger's builds, tools/dbg/builds.json's and one more for each --build: NAME's
   WebAssembly build at PATH (NAME.wasm with its .mjs beside it, built elsewhere, from another branch, by
   build_wasm.py), with its launch arguments ARG...; a known NAME has its label (BUILDS), another is labelled
   by its name.
4. The examples' check (tools/dbg/ui/gallery_test.mjs) on native ecma-dbg and on each WebAssembly build in node:
   every example must reach what its check says under every build it lists. A failure stops the build.
5. The errata's programs, run on native ecma-run under each reading the errata page states an outcome of
   (scripts/errata_page.py run: build/errata-runs.json); a run that differs stops the build.
5a. The spec issues' examples (docs/spec-issues/examples) as the debugger's spec-examples.json
   (scripts/dbg_spec_examples.py), each run on native ecma-dbg and on the WebAssembly build in node to the
   write-up's step and its recorded end (tools/dbg/ui/spec_examples_test.mjs); a failure stops the build.
6. The pages (scripts/site_pages.py: the reading pages, errata.html, the spec issues' write-ups under
   spec-issues/, 404.html, examples.html, debugger/index.html,
   test262.html from the run's record tests/test262/results/suite.tsv when it is there, or --test262-record,
   proposal.html from the proposal branch's record site/proposal-defer-import-eval.json when it is there, or
   --proposal-record), then dist/debugger/: the debugger's client, Worker host and UI (no node tests),
   demo/, the WebAssembly builds, builds.json, examples.json, spec-examples.json (which the debugger's menu
   lists), coi-serviceworker.js.
7. The site checked (scripts/site_pages.py --check).

Cross-origin isolation, which the debugger's Worker needs for its SharedArrayBuffer: on GitHub Pages (which sends
no custom headers) the debugger's page loads coi-serviceworker.js, whose service worker adds the headers and
reloads the page once. Locally: `python3 tools/dbg/serve.py --page index.html dist` sends them itself.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_wasm  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
BIN = ROOT / ".lake/build/bin"
DBG = ROOT / "tools/dbg"
EXAMPLES = ROOT / "docs/spec-issues/examples"
# The Lean executables the site needs, by their roots (lakefile.toml).
EXES = {"ecma-run": "Engine.Cli.Main", "ecma-dbg": "Debugger.Main", "ecma-bundle": "Engine.Cli.Bundle"}
# The debugger's files a page loads (tools/dbg), and ui/'s but its node tests and the page served alone.
PAGE = ["client.mjs", "engine-worker.mjs", "ring.mjs", "coi-serviceworker.js", "coi-serviceworker.LICENSE"]
# Builds named by --build whose label is known.
BUILDS = {
    "defer": ("Proposal (Stage 3): import defer", "tc39/proposal-defer-import-eval (with PR #97) applied to ECMA-262."),
    "import-text": ("Proposal (Stage 3): Import Text", "tc39/proposal-import-text (Stage 4 candidate) applied to ECMA-262."),
    "thenable-curtailment": ("Proposal (Stage 3): Thenable Curtailment", "tc39/proposal-thenable-curtailment (with PRs #22 and #26) applied to ECMA-262."),
    "deferred-reexports": ("Proposal (Stage 2.7): Deferred Re-exports", "tc39/proposal-deferred-reexports applied to ECMA-262."),
    "json-parseimmutable": ("Proposal (Stage 2.7): JSON.parse Options", "tc39/proposal-json-parseimmutable (PR #27: nullPrototypeObjects) applied to ECMA-262."),
    "esm-phase-imports": ("Proposal (Stage 2.7): ESM Phase Imports", "tc39/proposal-esm-phase-imports (PR #65) applied to ECMA-262."),
    "immutable-arraybuffer": ("Proposal (Stage 2.7): Immutable ArrayBuffers", "tc39/proposal-immutable-arraybuffer applied to ECMA-262."),
    "error-code-property": ("Proposal (Stage 2): Error.code", "tc39/proposal-error-code-property applied to ECMA-262."),
    "fma": ("Proposal (Stage 2): Math.fusedMultiplyAdd", "tc39/proposal-fma applied to ECMA-262."),
    "composites": ("Proposal (Stage 2): Composites", "tc39/proposal-composites applied to ECMA-262."),
    "cancellation": ("Proposal (Stage 1): Cancellation (AbortController)", "tc39/proposal-cancellation (PR #35 spec draft) applied to ECMA-262."),
    "iterator-transfer": ("Proposal (Stage 0): Iterator.prototype.transfer", "jasnell/proposal-iterator-transfer applied to ECMA-262."),
    "trim-chars": ("Proposal (Stage 0): Trim Specific Characters", "eemeli/proposal-trim-chars applied to ECMA-262."),
    "popcount": ("Proposal (Stage 0): Math.popcount32 / ctz32", "js-choi/proposal-popcount applied to ECMA-262."),
}


def run(*cmd, **kw) -> subprocess.CompletedProcess:
    print("+", " ".join(str(c) for c in cmd), flush=True)
    return subprocess.run([str(c) for c in cmd], cwd=ROOT, check=True, **kw)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()


def lean_products() -> list[str]:
    """What is wrong with the Lean build's products: an executable missing, or older than its modules' C, or
    a module's C not of its source as it is now."""
    bad = []
    for exe, root in EXES.items():
        b = BIN / exe
        mods = build_wasm.closure(root)
        if not b.is_file():
            bad.append(f"no {b.relative_to(ROOT)}")
            continue
        stale = build_wasm.stale_modules(mods)
        if stale:
            bad.append(f"{exe}: {len(stale)} of {len(mods)} modules not built from their source as it is "
                       f"({', '.join(stale[:4])}{', ...' if len(stale) > 4 else ''})")
            continue
        newest = max((build_wasm.IR / (m.replace(".", "/") + ".c")).stat().st_mtime for m in mods)
        if b.stat().st_mtime < newest:
            bad.append(f"{exe} is older than its modules' C")
    return bad


def parse_build(text: str) -> dict:
    """--build NAME=PATH[,ARG...]."""
    name, eq, rest = text.partition("=")
    if not eq or not rest:
        raise SystemExit(f"--build {text}: NAME=PATH[,ARG...]")
    path, *args = rest.split(",")
    wasm = Path(path).resolve()
    if wasm.suffix != ".wasm" or not wasm.is_file() or not wasm.with_suffix(".mjs").is_file():
        raise SystemExit(f"--build {text}: {wasm} is not a .wasm with its .mjs beside it")
    label, desc = BUILDS.get(name, (name, f"The WebAssembly build {wasm.name}."))
    return {"id": name, "label": label, "description": desc, "wasm": f"ecma-dbg-web-{name}.wasm", "args": args,
            "source": str(wasm)}


def spec_examples(out: Path) -> None:
    """The spec issues' examples: each directory as ecma-bundle's bundle with the model's run of it, then the JSON."""
    flags: list[str] = []
    with tempfile.TemporaryDirectory() as t:
        for d in sorted(p for p in EXAMPLES.iterdir() if p.is_dir()):
            js, res = Path(t) / f"{d.name}.js", Path(t) / f"{d.name}.run"
            with open(js, "w") as f:
                run(BIN / "ecma-bundle", f"{d}/", stdout=f)
            r = subprocess.run([BIN / "ecma-run", "--module", "--module-dir", f"{d}/", d / "main.mjs"],
                               cwd=ROOT, capture_output=True, text=True, check=False)
            res.write_text(f"exit {r.returncode}\n{r.stdout}")
            flags += ["--bundle", f"{d.name}={js}", "--model-run", f"{d.name}={res}"]
        run(sys.executable, "scripts/dbg_spec_examples.py", "--examples", EXAMPLES, "--reports", EXAMPLES.parent,
            *flags, "--out", out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=ROOT / "dist")
    ap.add_argument("--no-wasm", action="store_true", help="reuse build/web/ecma-dbg-web.{mjs,wasm} as it is")
    ap.add_argument("--build", action="append", default=[], metavar="NAME=PATH[,ARG...]",
                    help="one more build for the debugger's selector: a WebAssembly build built elsewhere")
    ap.add_argument("--stale-ok", action="store_true", help="go on from Lean products not of the sources as they are")
    ap.add_argument("--node", default="node")
    ap.add_argument("-j", "--jobs", type=int, help="emcc jobs of the WebAssembly build (scripts/build_wasm.py's default: one per CPU)")
    ap.add_argument("--proposal-record", type=Path, default=ROOT / "site/proposal-defer-import-eval.json",
                    help="a proposal branch's record (scripts/proposal_record.py); used when it is there")
    ap.add_argument("--test262-record", type=Path, default=ROOT / "tests/test262/results/suite.tsv",
                    help="a test262 run's record (scripts/test262_report.py record); used when it is there")
    ap.add_argument("--base-path", help="URL prefix where the site is hosted (site_pages.py's default: /ecma-formal/)")
    a = ap.parse_args()
    try:
        rev = git("rev-parse", "HEAD")
    except subprocess.CalledProcessError:  # no commit yet
        rev = "uncommitted"
    dirty = bool(git("status", "--porcelain", "--untracked-files=no"))

    bad = lean_products()
    if bad:
        msg = "build_site.py: the Lean build's products are missing or stale:\n  " + "\n  ".join(bad)
        msg += "\n(run `lake build ecma-run ecma-dbg ecma-bundle` in the dev shell first; this script runs no Lean build)"
        if not a.stale_ok:
            sys.exit(msg)
        print(f"warning: {msg}\ngoing on (--stale-ok)", file=sys.stderr)
    BUILD.mkdir(exist_ok=True)

    # 1, 2: the examples and the WebAssembly build.
    run(sys.executable, "scripts/dbg_gallery.py", "--out", BUILD / "examples.json")
    web = BUILD / "web"
    if not a.no_wasm:
        run(sys.executable, "scripts/build_wasm.py", "--out", web, *(["--stale-ok"] if a.stale_ok else []),
            *(["--jobs", a.jobs] if a.jobs else []))
    for f in ("ecma-dbg-web.mjs", "ecma-dbg-web.wasm"):
        if not (web / f).is_file():
            sys.exit(f"build_site.py: no {web / f} (build it: drop --no-wasm)")

    # 3: the builds.
    table = json.loads((DBG / "builds.json").read_text())
    extra = [parse_build(b) for b in a.build]
    for b in extra:
        if any(x["id"] == b["id"] for x in table["builds"]):
            sys.exit(f"--build {b['id']}: a build of that name exists")
    builds = {"builds": table["builds"] + [{k: v for k, v in b.items() if k != "source"} for b in extra]}
    (BUILD / "builds.json").write_text(json.dumps(builds, indent=1, ensure_ascii=False) + "\n")
    wasm_dir = BUILD / "site-wasm"
    shutil.rmtree(wasm_dir, ignore_errors=True)
    wasm_dir.mkdir()
    for f in ("ecma-dbg-web.mjs", "ecma-dbg-web.wasm"):
        os.link(web / f, wasm_dir / f)
    for b in extra:
        src = Path(b["source"])
        shutil.copy(src, wasm_dir / b["wasm"])
        shutil.copy(src.with_suffix(".mjs"), wasm_dir / Path(b["wasm"]).with_suffix(".mjs"))

    # 4: the examples' check, natively and on each WebAssembly build in node.
    native_for = []
    for b in extra:
        cand = Path(b["source"]).parent.parent / "bin/ecma-dbg"
        if cand.is_file():
            native_for += ["--native-for", f"{b['id']}={cand}"]
    checks = []
    for name, engine in (("native", ["--native", BIN / "ecma-dbg", *native_for]), ("wasm", ["--wasm-node", wasm_dir])):
        out = BUILD / f"examples-check-{name}.json"
        run(a.node, "tools/dbg/ui/gallery_test.mjs", "--gallery", BUILD / "examples.json", "--builds",
            BUILD / "builds.json", *engine, "--json", out)
        checks += ["--checked", out]

    # 5: the errata's programs.
    run(sys.executable, "scripts/errata_page.py", "run", "--ecma-run", BIN / "ecma-run", "--out",
        BUILD / "errata-runs.json", "-j", "3")

    # 5a: the spec issues' examples, checked natively and on the WebAssembly build in node.
    spec_examples(BUILD / "spec-examples.json")
    for engine in (["--native", BIN / "ecma-dbg"], ["--wasm-node", wasm_dir / "ecma-dbg-web.mjs"]):
        run(sys.executable, "scripts/dbg_demo_test.py", "--node", a.node, *engine, "--json", BUILD / "spec-examples.json")

    # 6: the pages, then the debugger's files.
    out = a.out
    shutil.rmtree(out, ignore_errors=True)
    t262 = ["--test262-record", a.test262_record] if a.test262_record.is_file() else []
    if not t262:
        print(f"note: no {a.test262_record}: the site has no test262 page", flush=True)
    prop = ["--proposal-record", a.proposal_record] if a.proposal_record.is_file() else []
    if not prop:
        print(f"note: no {a.proposal_record}: the site has no page on applying a proposal", flush=True)
    base = ["--base-path", a.base_path] if a.base_path else []
    run(sys.executable, "scripts/site_pages.py", "--out", out, *t262, *prop, *base, "--errata-runs", BUILD / "errata-runs.json",
        "--examples", BUILD / "examples.json",
        "--builds", BUILD / "builds.json", *checks, "--debugger", "--no-check")
    dbg = out / "debugger"
    for f in PAGE:
        shutil.copy(DBG / f, dbg / f)
    shutil.copytree(DBG / "ui", dbg / "ui", ignore=shutil.ignore_patterns("*_test.mjs", "index.html"))
    (dbg / "demo").mkdir()
    for f in [*sorted((DBG / "demo").glob("*.js")), DBG / "demo/script.mjs"]:
        shutil.copy(f, dbg / "demo" / f.name)
    for f in wasm_dir.iterdir():
        shutil.copy(f, dbg / f.name)
    shutil.copy(BUILD / "builds.json", dbg / "builds.json")
    shutil.copy(BUILD / "examples.json", dbg / "examples.json")
    shutil.copy(BUILD / "spec-examples.json", dbg / "spec-examples.json")
    # The stamp says how the site was built; scripts/deploy_site.sh refuses one with uncommitted changes or made
    # with --stale-ok.
    stamp = (f"ecma-formal {rev}{' with uncommitted changes' if dirty else ''}"
             f"{' from stale Lean products' if bad else ''}{' (built with --stale-ok)' if a.stale_ok else ''}\n")
    (dbg / "VERSION").write_text(stamp)
    (out / "VERSION").write_text(stamp)
    (out / ".nojekyll").write_text("")  # Pages serves the files as they are

    # 7: the check.
    run(sys.executable, "scripts/site_pages.py", "--check", out, *base)
    print(f"{out}: the site and the debugger at {stamp.strip()}; serve it with "
          f"python3 tools/dbg/serve.py --page index.html {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
