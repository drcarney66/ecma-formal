#!/usr/bin/env python3
"""The spec-issue examples as the debugger's examples (spec-examples.json, scripts/build_site.py).

    dbg_spec_examples.py --examples DIR --reports DIR [--bundle ID=FILE --model-run ID=FILE]...
        --out spec-examples.json

Every entry of docs/spec-issues/examples (DIR) is one example: a `.js` file
a Script, a directory (main.mjs and its modules) the d8 bundle ecma-bundle wrote
of it (`--bundle ID=FILE`, one per directory). Its id is the file's name
without `.js`, or the directory's (`ui/?example=ID`); its label the number and
title of the report with that number (docs/spec-issues/NN-*.md, --reports).
The breakpoint is the first clause and step the report's Location line names
as "(`#sec-id`), step S"; `NO_BREAKPOINT` lists the examples whose run on the
default host does not reach it, `BREAKPOINT` those that have another step it
names instead. Where the model's run ends at an erratum's or an Assert's stop,
the `stop` filter is on, so the debugger pauses there too. `expect` is the
model's run (the result line, the printed lines, the exit status): RESULTS.md's
for a Script, and for a directory, which RESULTS.md does not run on the model,
`--model-run ID=FILE` (`exit N`, then ecma-run's stdout: `ecma-run
--module --module-dir DIR DIR/main.mjs`). `UNRUNNABLE` gives the reason an
example is listed but not run.

The JSON: {examples: [{id, number, label, title, report, name, source, module,
args, breakpoints, filters, expect, unrunnable}]}, in the directory's order.
"""

import argparse
import json
import re
import sys
from pathlib import Path

# The examples whose run on the model does not reach the report's step: id -> why.
NO_BREAKPOINT: dict[str, str] = {
    "05-parsetext-error-objects": "the run does not reach ParseText step 4",
    "06-dowait-sync-timeout": "the default host's agent cannot block: DoWait throws at step 12",
    "14-nativefunction-initialname": "the source text is available: toString returns at step 2",
    "33-createintrinsics-async-argument-position": "CreateIntrinsics runs in the realm's setup, before the entry",
    "29-propname-coverinitializedname": "no run asks PropertyNameList of a cover: the parse rejects it first",
}

# The examples whose breakpoint is another step the Location line names, the first not reached.
BREAKPOINT: dict[str, dict] = {
    "13-promise-job-abrupt-completion": {"alg": "sec-newpromisereactionjob", "path": "1.i"},
}

# The examples the Worker build cannot run: id -> a one-line reason.
UNRUNNABLE: dict[str, str] = {
    "46-covered-node-tail-call": "the run does not end within RESULTS.md's 120 s natively, and the Worker build is slower",
}

# The model's options per example (ecma-run's, as launch `args`); RESULTS.md runs every one with none.
ARGS: dict[str, list[str]] = {}

# A model stop the `stop` filter pauses at: an Assert's at a step (not a fuel
# limit's, nor one at a Job's end, whose step is `-`).
STOPS = re.compile(r"stop: (erratum|assertFailed|assertion failed) .* (?!-$)\S+$")
LOCATION_STEP = re.compile(r"\(`#([^`]+)`\),\s+steps?\s+(\d+(?:\.[0-9a-z]+)*)")


def title_of(report: Path) -> str:
    """The report's title, its `# NN. ` and Markdown marks dropped."""
    first = report.read_text().splitlines()[0]
    t = re.sub(r"^#\s*\d+\.\s*", "", first)
    return re.sub(r"[`*|]", "", t).replace("\\", "").strip()


def location(report: Path) -> str:
    """The report's Location item, its lines joined."""
    out, on = [], False
    for line in report.read_text().splitlines():
        if line.startswith("- **Location:**"):
            on = True
        elif on and (line.startswith("- **") or not line.strip()):
            break
        if on:
            out.append(line.strip())
    return " ".join(out)


def breakpoint_of(report: Path) -> dict | None:
    """The first `(#sec-id), step S` of the Location line as {alg, path}, or None."""
    m = LOCATION_STEP.search(location(report))
    return {"alg": m.group(1), "path": m.group(2)} if m else None


def model_runs(results: Path) -> dict[str, dict]:
    """RESULTS.md's model run per example heading: {exit, line, printed}."""
    runs = {}
    sections = re.split(r"^## ", results.read_text(), flags=re.M)[1:]
    for s in sections:
        name = s.splitlines()[0].strip()
        m = re.search(r"### the formal model \(ecma-run\)\n\n`[^`]*`: exit status (\d+)\n\nstdout:\n\n```\n(.*?)```", s, re.S)
        if not m:
            continue
        lines = m.group(2).splitlines()
        runs[name] = {"exit": int(m.group(1)), "line": lines[0] if lines else "", "printed": lines[1:]}
    return runs


def model_run(path: Path) -> dict:
    """A `--model-run` file's run: {exit, line, printed}."""
    first, *lines = path.read_text().splitlines()
    return {"exit": int(first.removeprefix("exit ")), "line": lines[0] if lines else "", "printed": lines[1:]}


def pairs(ap: argparse.ArgumentParser, flag: str, values: list[str]) -> dict[str, Path]:
    """`ID=FILE` values by ID."""
    out = {}
    for v in values:
        k, sep, f = v.partition("=")
        if not sep:
            ap.error(f"{flag} {v}: not ID=FILE")
        out[k] = Path(f)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--examples", required=True, type=Path)
    ap.add_argument("--reports", required=True, type=Path)
    ap.add_argument("--bundle", action="append", default=[], help="ID=FILE: ecma-bundle's output for the directory ID")
    ap.add_argument("--model-run", action="append", default=[], help="ID=FILE: the model's run of the directory ID")
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    bundles = pairs(ap, "--bundle", args.bundle)
    module_runs = pairs(ap, "--model-run", args.model_run)
    reports = {p.name[:2]: p for p in args.reports.glob("[0-9][0-9]-*.md")}
    runs = model_runs(args.examples / "RESULTS.md")
    examples, bad = [], []
    for p in sorted(args.examples.iterdir()):
        module = p.is_dir()
        if not (module or p.suffix == ".js") or p.name.startswith("."):
            continue
        ident = p.name if module else p.stem
        report = reports.get(p.name[:2])
        if report is None:
            bad.append(f"{p.name}: no report {p.name[:2]}-*.md")
            continue
        if module:
            if ident not in bundles:
                bad.append(f"{p.name}: a directory with no --bundle")
                continue
            if ident not in module_runs:
                bad.append(f"{p.name}: a directory with no --model-run")
                continue
            source = bundles.pop(ident).read_text()
            expect = model_run(module_runs.pop(ident))
        else:
            source = p.read_text()
            expect = runs.get(p.name)
        bp = None if ident in NO_BREAKPOINT else BREAKPOINT.get(ident) or breakpoint_of(report)
        title = title_of(report)
        examples.append({
            "id": ident,
            "number": p.name[:2],
            "label": f"{p.name[:2]} {title}",
            "title": title,
            "report": report.name,
            "name": f"{ident}.js",
            "source": source,
            "module": module,
            "args": ARGS.get(ident, []),
            "breakpoints": [bp] if bp else [],
            "filters": ["stop"] if expect and STOPS.match(expect["line"]) else [],
            "expect": expect,
            "unrunnable": UNRUNNABLE.get(ident),
        })
        if not module and p.name not in runs and ident not in UNRUNNABLE:
            bad.append(f"{p.name}: no model run in RESULTS.md")
    bad += [f"--bundle {k}: no such directory" for k in bundles] + [f"--model-run {k}: no such directory" for k in module_runs]
    stale = [k for k in [*NO_BREAKPOINT, *BREAKPOINT, *UNRUNNABLE, *ARGS] if k not in {e["id"] for e in examples}]
    bad += [f"{k}: listed in this script, not an example" for k in stale]
    if bad:
        for b in bad:
            print(f"dbg_spec_examples.py: {b}", file=sys.stderr)
        return 1
    args.out.write_text(json.dumps({"examples": examples}, indent=1, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
