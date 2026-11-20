#!/usr/bin/env python3
"""Run the examples of docs/spec-issues/ on three engines and the formal
model, and write docs/spec-issues/examples/RESULTS.md.

The engines are V8 (`node`), SpiderMonkey (`js140`) and JavaScriptCore
(`bun`), from the flake's engines dev shell; the model is the repository's
`.lake/build/bin/ecma-run` (build it first: `lake build ecma-run`), which runs
Scripts only, on its fixed host. From the repository root:

    nix develop .#engines --profile ~/.local/state/ecma-formal/devshell-engines-jsc -c true
    nix develop ~/.local/state/ecma-formal/devshell-engines-jsc -c python3 scripts/spec_issues_run.py

Goals. A `.js` example is a Script, a directory's `main.mjs` a Module. The
SpiderMonkey shell runs a file as a Script and `-m FILE` as a Module. Node
runs a `.js` file as CommonJS (a function body) and Bun as a Module, so for
a Script both run a CommonJS shim that evaluates the file with
`vm.runInThisContext` (ScriptEvaluation in the main realm: sloppy, `this` is
the global object, Annex B applies); a Module is run directly (`node
main.mjs`, `bun main.mjs`). Python only drives the engines; every run has a
timeout (TIMEOUT seconds), and a run that hits it is recorded as such.

`--engines` runs some of them only; `--reuse FILE` (repeatable) takes the
runs of the others from earlier outputs (the model in one shell, the
engines in another):

    python3 scripts/spec_issues_run.py --engines model --output model.md
    nix develop ~/.local/state/ecma-formal/devshell-engines-jsc -c python3 scripts/spec_issues_run.py \
        --engines v8,spidermonkey,jsc --reuse model.md
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "docs/spec-issues/examples"
TIMEOUT = 120

# Evaluates argv[2] as a classic Script in the main realm (node and bun).
SCRIPT_SHIM = """\
// Evaluates the file named by argv[2] as a Script (ScriptEvaluation) in this realm.
const fs = require("node:fs"), vm = require("node:vm");
const file = process.argv[2];
vm.runInThisContext(fs.readFileSync(file, "utf8"), { filename: file });
"""

ENGINES = ["v8", "spidermonkey", "jsc", "model"]
ENGINE_TITLE = {
    "v8": "V8 (node)",
    "spidermonkey": "SpiderMonkey (js140)",
    "jsc": "JavaScriptCore (bun)",
    "model": "the formal model (ecma-run)",
}

# Extra runs: example -> engine -> list of argument lists (each one run). An
# engine not listed runs once, with no extra argument.
VARIANTS = {
    "04-execute-module-tla-dispose": {"spidermonkey": [[], ["--enable-explicit-resource-management"]]},
    "09-atomics-waitasync-timeout-assert.js": {"spidermonkey": [[], ["-P", "atomics_wait_async=true"]]},
    "15-synthetic-module-link": {"spidermonkey": [[], ["--enable-import-attributes"]]},
}

# Model-only runs of tests the reports cite: (report, file, arguments).
MODEL_EXTRA = [
    ("11", "tests/run/regexp_lastindex_inside_pair_nonempty.js", []),
    ("13", "tests/run/null_realm_job.js", []),
]


def run(cmd, cwd):
    """(exit status or "TIMEOUT", stdout, stderr) of `cmd` in `cwd`."""
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=TIMEOUT, stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""
        err = e.stderr or b""
        return f"TIMEOUT after {TIMEOUT} s", out.decode("utf-8", "replace"), err.decode("utf-8", "replace")
    return p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")


def first_line(cmd):
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=TIMEOUT, stdin=subprocess.DEVNULL)
    except (OSError, subprocess.TimeoutExpired):
        return None
    text = (p.stdout or p.stderr).decode().strip()
    return text.splitlines()[0] if text else None


def versions(model):
    v = {}
    v["v8"] = first_line(["node", "-p", 'process.version + " (V8 " + process.versions.v8 + ")"'])
    v["spidermonkey"] = first_line(["js140", "--version"])
    bun = first_line(["bun", "--revision"])
    webkit = first_line(["bun", "-e", "console.log(process.versions.webkit)"])
    v["jsc"] = bun and f"Bun {bun} (JavaScriptCore of oven-sh/WebKit {webkit})"
    # The binary's sources are not knowable from here (the build may predate
    # the checkout's last commit); the README names them.
    v["model"] = model.exists() and "`.lake/build/bin/ecma-run` built from the checkout (its sources: the README)"
    return v


def commands(engine, example, extra, shim, model):
    """(argv, cwd, shown) for one run, None for the model on a Module; `shown` is the command as the
    report prints it."""
    path = EXAMPLES / example
    module = path.is_dir()
    cwd = path if module else EXAMPLES
    target = "main.mjs" if module else example
    if engine == "v8":
        argv = ["node", *extra] + ([target] if module else [str(shim), target])
        shown = ["node", *extra] + ([target] if module else ["script-shim.cjs", target])
    elif engine == "jsc":
        argv = ["bun", *extra] + ([target] if module else [str(shim), target])
        shown = ["bun", *extra] + ([target] if module else ["script-shim.cjs", target])
    elif engine == "spidermonkey":
        argv = ["js140", *extra] + (["-m", target] if module else [target])
        shown = argv
    elif module:
        return None
    else:
        argv = [str(model), *extra, target]
        shown = ["ecma-run", *extra, target]
    return argv, cwd, shown


def normalize(text, shim):
    """Replaces the absolute paths of a run by short names."""
    for path, name in [(str(shim), "script-shim.cjs"), (str(EXAMPLES) + "/", ""), (str(ROOT) + "/", "")]:
        text = text.replace(path, name)
    return text


def block(text):
    fence = "```"
    while fence in text:
        fence += "`"
    return f"{fence}\n{text.rstrip(chr(10))}\n{fence}\n" if text.strip() else "(nothing)\n"


def report(label, shown, result, shim):
    status, out, err = result
    lines = [f"`{' '.join(shown)}`" + (f" ({label})" if label else "") + f": exit status {status}\n"]
    lines.append("\nstdout:\n\n" + block(normalize(out, shim)))
    if err.strip():
        lines.append("\nstderr:\n\n" + block(normalize(err, shim)))
    return "".join(lines)


def reused(path):
    """{(section, engine title): its runs' texts} of an earlier RESULTS.md, and its version table's rows."""
    runs, rows, section, title, fence = {}, {}, None, None, None
    for line in path.read_text().splitlines(keepends=True):
        if fence is not None or line.startswith("```"):
            if fence is None:
                fence = re.match(r"`+", line).group()
            elif line.rstrip("\n") == fence:
                fence = None
            if title is not None:
                runs[(section, title)][-1] += line
            continue
        m = re.match(r"\| (.+) \| (.+) \|$", line)
        if section is None and m:
            rows[m.group(1)] = m.group(2)
        if line.startswith("## "):
            section, title = line[3:].strip(), None
        elif line.startswith("### ") and section is not None:
            title = line[4:].strip()
            runs.setdefault((section, title), []).append("")
        elif title is not None:
            runs[(section, title)][-1] += line
    return runs, rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--model", type=Path, default=ROOT / ".lake/build/bin/ecma-run")
    parser.add_argument("--engines", default=",".join(ENGINES), help="the engines to run (comma-separated)")
    parser.add_argument("--reuse", type=Path, action="append", default=[],
                        help="an earlier output: the runs of the engines not run, from it (repeatable)")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--output", type=Path, default=EXAMPLES / "RESULTS.md")
    args = parser.parse_args()
    for path in args.reuse:
        if not path.is_file():
            parser.error(f"--reuse: no file {path}")
    examples = sorted(p.name for p in EXAMPLES.iterdir() if p.suffix == ".js" or p.is_dir())
    wanted = args.engines.split(",")
    if not set(wanted) <= set(ENGINES):
        parser.error(f"--engines: not one of {','.join(ENGINES)}: {','.join(set(wanted) - set(ENGINES))}")
    vers = versions(args.model)
    engines = [e for e in ENGINES if e in wanted and vers[e]]
    for e in wanted:
        if not vers[e]:
            print(f"spec_issues_run: {ENGINE_TITLE[e]} not found; not run", file=sys.stderr)
    old, old_rows = {}, {}
    for path in args.reuse:
        runs, rows = reused(path)
        old.update(runs)
        old_rows.update(rows)
    kept = [e for e in ENGINES if e not in engines and ENGINE_TITLE[e] in old_rows]
    for e in kept:
        vers[e] = old_rows[ENGINE_TITLE[e]]
    shown_engines = [e for e in ENGINES if e in engines or e in kept]
    with tempfile.TemporaryDirectory() as tmp:
        shim = Path(tmp) / "script-shim.cjs"
        shim.write_text(SCRIPT_SHIM)
        jobs = []
        for ex in examples:
            for e in engines:
                for extra in VARIANTS.get(ex, {}).get(e, [[]]):
                    c = commands(e, ex, extra, shim, args.model)
                    if c:
                        jobs.append((ex, e, extra, *c))
        extra_jobs = []
        if "model" in engines:
            for num, test, extra in MODEL_EXTRA:
                argv = [str(args.model), *extra, test]
                shown = ["ecma-run", *extra, test]
                extra_jobs.append((num, argv, ROOT, shown))
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            results = list(pool.map(lambda j: run(j[3], j[4]), jobs))
            extra_results = list(pool.map(lambda j: run(j[1], j[2]), extra_jobs))
        out = [
            "# Results of the examples\n\n",
            "Generated by `scripts/spec_issues_run.py` (do not edit; run it again). ",
            "Each run's exit status, standard output and standard error, exactly ",
            "(absolute paths shortened).\n\n",
            "| Engine | Version |\n|---|---|\n",
        ]
        out += [f"| {ENGINE_TITLE[e]} | {vers[e]} |\n" for e in shown_engines]
        out.append(
            "\nA `.js` example is a Script: SpiderMonkey runs the file; node and bun run "
            "`script-shim.cjs`, which evaluates it with `vm.runInThisContext` (a Script in the "
            "main realm, not CommonJS or a Module):\n\n" + block(SCRIPT_SHIM) +
            "\nA directory's `main.mjs` is a Module (`node main.mjs`, `bun main.mjs`, "
            "`js140 -m main.mjs`), run in the directory; the model runs Scripts only, "
            "on ecma-run's fixed host, which defines `print`.\n"
        )
        for ex in examples:
            out.append(f"\n## {ex}\n")
            for e in shown_engines:
                if e in kept:
                    for text in old.get((ex, ENGINE_TITLE[e]), []):
                        out.append(f"\n### {ENGINE_TITLE[e]}\n" + text.rstrip("\n") + "\n")
                    continue
                for (jex, je, extra, argv, cwd, shown), res in zip(jobs, results):
                    if jex == ex and je == e:
                        out.append(f"\n### {ENGINE_TITLE[e]}\n\n" + report("", shown, res, shim))
        extra_title = "Tests of the model cited by the reports"
        if extra_jobs:
            out.append(f"\n## {extra_title}\n")
            for (num, argv, cwd, shown), res in zip(extra_jobs, extra_results):
                out.append(f"\n### Report {num}\n\n" + report("", shown, res, shim))
        elif "model" in kept:
            kept_extra = [(t, text) for (sec, t), texts in old.items() if sec == extra_title for text in texts]
            if kept_extra:
                out.append(f"\n## {extra_title}\n")
                out += [f"\n### {t}\n" + text.rstrip("\n") + "\n" for t, text in kept_extra]
    args.output.write_text("".join(out))
    print(f"spec_issues_run: wrote {os.path.relpath(args.output, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
