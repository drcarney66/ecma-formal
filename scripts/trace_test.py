#!/usr/bin/env python3
"""The machine's step traces name the specification's steps: every traced (section, path) is a step of
`spec-gen steps`.

Every tests/trace/*.js runs as `ecma-run FILE` with `JS_TRACE_STEPS=1`; the lines
after ecma-run's `ecma-run: trace` line on stderr are `<sec-id> <path>. <text>`. Each (sec-id,
path) must be a row of `spec-gen --spec=SPEC --overlay=DIR steps` (columns: class, number, sec-id,
path, text), whose paths are numbered as the machine's are. Sections of the overlay (`ph-`, `formal-`,
`sort-`, an erratum's reading `erratum/sec@step/reading`), which that listing does not have, are
counted and skipped. A case that traces no
spec.html step fails, so that the check is not vacuous.

    python3 scripts/trace_test.py --run .lake/build/bin/ecma-run --gen target/release/spec-gen \\
        --overlay spec/formal

SPEC is the text (`scripts/spec_text.py`), or `--spec FILE-OR-DIR`.
"""

import argparse
import concurrent.futures
import os
import subprocess
import sys
from pathlib import Path

import spec_text

SUITE = Path("tests/trace")
MARK = "ecma-run: trace"
OVERLAY_SECS = ("ph-", "formal-", "sort-")


def listing(gen: str, spec: str, overlay: str) -> set[tuple[str, str]]:
    """The (sec-id, path) of every step `spec-gen steps` lists."""
    r = subprocess.run([gen, f"--spec={spec}", f"--overlay={overlay}", "steps"], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"spec-gen steps: exit {r.returncode}\n{r.stderr}")
    rows = set()
    for line in r.stdout.splitlines():
        cols = line.split("\t")
        if len(cols) >= 4:
            rows.add((cols[2], cols[3]))
    return rows


def traced(run: str, case: Path, args: list[str]) -> list[tuple[str, str]]:
    """The (sec-id, path) of each step ecma-run's trace of `case` enters."""
    env = dict(os.environ, JS_TRACE_STEPS="1")
    r = subprocess.run([run, *args, str(case)], capture_output=True, text=True, env=env)
    lines = r.stderr.splitlines()
    if MARK not in lines:
        sys.exit(f"{case}: no `{MARK}` line on stderr (exit {r.returncode})")
    out = []
    for line in lines[lines.index(MARK) + 1:]:
        sec, _, rest = line.partition(" ")
        path = rest.split(" ", 1)[0]
        if not sec or not path.endswith("."):
            sys.exit(f"{case}: not a trace line: {line!r}")
        out.append((sec, path[:-1]))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="ecma-run")
    ap.add_argument("--gen", required=True, help="the generator, spec-gen")
    ap.add_argument("--spec", help="a spec.html or its directory (default: the text, scripts/spec_text.py)")
    ap.add_argument("--overlay", required=True, help="the overlay directory, spec/formal")
    ap.add_argument("--suite", default=str(SUITE))
    ap.add_argument("--arg", action="append", default=[], help="an argument added to ecma-run's runs")
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    a = ap.parse_args()
    spec = spec_text.resolve(a.spec)
    rows = listing(a.gen, spec, a.overlay)
    bad: dict[tuple[str, str], str] = {}
    lines = skipped = 0
    cases = sorted(Path(a.suite).glob("*.js"))
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        runs = list(ex.map(lambda c: traced(a.run, c, a.arg), cases))
    for case, steps in zip(cases, runs):
        mine = [s for s in steps if not s[0].startswith(OVERLAY_SECS) and "/" not in s[0]]
        if not mine:
            print(f"{case.name}: no spec.html step traced")
            bad[("-", case.name)] = case.name
        lines += len(mine)
        skipped += len(steps) - len(mine)
        for s in mine:
            if s not in rows:
                bad.setdefault(s, case.name)
    for (sec, path), case in sorted(bad.items()):
        if sec != "-":
            print(f"{sec} {path}. not a step of `spec-gen steps` (first in {case})")
    print(f"trace_test: {lines} lines traced, {skipped} of the overlay skipped, {len(bad)} steps not in the listing")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
