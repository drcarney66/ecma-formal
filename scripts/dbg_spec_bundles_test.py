#!/usr/bin/env python3
"""The debugger's bundles of the spec-issue module examples run as their directories do.

    dbg_spec_bundles_test.py --run ECMA_RUN --examples DIR --json spec-examples.json

For each module example of spec-examples.json (scripts/dbg_spec_examples.py: the
bundle ecma-bundle wrote of the directory, main.mjs its entrypoint), the model
(`ecma-run`) runs the bundle (`--bundle`) and the directory (`--module
--module-dir DIR/ID DIR/ID/main.mjs`): the exit status and standard output must
be the same, and the same as the example's `expect`. Every directory of DIR
must have its example.
"""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

TIMEOUT_S = 600


def run(cmd: list[str]) -> tuple[int | str, str]:
    """`cmd`'s exit status and stdout; a run past TIMEOUT_S is `timeout`."""
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    return p.returncode, p.stdout


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="ecma-run")
    ap.add_argument("--examples", required=True, type=Path)
    ap.add_argument("--json", required=True, type=Path)
    args = ap.parse_args()
    examples = {e["id"]: e for e in json.loads(args.json.read_text())["examples"] if e["module"]}
    failed = 0
    dirs = sorted(p.name for p in args.examples.iterdir() if p.is_dir())
    for d in dirs:
        if d not in examples:
            print(f"FAIL {d}: no module example")
            failed += 1
    with tempfile.TemporaryDirectory() as tmp:
        for ident, e in sorted(examples.items()):
            bundle = Path(tmp, e["name"])
            bundle.write_text(e["source"])
            directory = args.examples / ident
            b = run([args.run, "--bundle", str(bundle)])
            m = run([args.run, "--module", "--module-dir", str(directory), str(directory / "main.mjs")])
            want = e["expect"]
            lines = m[1].splitlines()
            bad = []
            if b != m:
                bad.append(f"the bundle: exit {b[0]}, {b[1]!r}; the directory: exit {m[0]}, {m[1]!r}")
            if not want or (m[0], lines[:1], lines[1:]) != (want["exit"], [want["line"]], want["printed"]):
                bad.append(f"the directory's run is not the example's expect {want!r}")
            if not lines or lines[0].startswith("stop: bundle"):
                bad.append(f"no run: {m[1]!r}")
            for x in bad:
                print(f"FAIL {ident}: {x}")
            failed += bool(bad)
            print(f"{'FAIL' if bad else 'ok'} {ident}: exit {m[0]}, {lines[:1]}")
    print(f"{len(examples)} bundles, {failed} failed")
    return 1 if failed or not examples else 0


if __name__ == "__main__":
    sys.exit(main())
