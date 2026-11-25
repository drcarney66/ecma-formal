#!/usr/bin/env python3
"""The debugger suite's bundle (tools/dbg/runner.mjs `runSuite`): one JSON file.

    dbg_browser_bundle.py --run BIN --out FILE [FILE...]

Each FILE.dbg is a transcript, with FILE.js beside it as its program if there is
one; each other FILE.js is a program run to its end, with the depth ladder's
programs (DEPTHS) after them. A program's expectation is native `ecma-run`'s
run of it: the outcome line (its first line), the rest of its stdout and its
status, which must be 0. `nativeMs` is that run's wall time, JOBS at a time. With no FILE, the suite's
files: tests/dbg's transcripts and programs, then the tests/run programs of SUITE.
"""

import argparse
import concurrent.futures
import json
import subprocess
import sys
import time
from pathlib import Path

JOBS = 4
ROOT = Path(__file__).resolve().parent.parent
# The suite's tests/run programs, run to their end after tests/dbg's transcripts.
SUITE = ["empty_script", "logical_not", "unary_bigint", "string_concat", "function_declaration", "stmt_finally_break",
         "s2_error_message", "proto_setter", "stmt_try", "s2_catch_type_error", "s2_let_tdz", "stmt_loops", "relational",
         "s2_object_keys", "number_tostring", "stmt_label_nested", "s2_array_builtins", "string_replaceall_positions",
         "s2_strict_closure", "optional_chain"]
TIMEOUT_S = 300

# Recursion by plain calls, and through Array.prototype.map's callback (a sub-run a
# level): (name, depth, source).
RECURSION = "var d = 0;\nfunction f(n) {{ if (n === {n}) return d; ++d; return f(++n); }}\nf(0);\n"
THROUGH_MAP = "var d = 0;\nfunction g(n) {{ if (n === {n}) return d; ++d; return [++n].map(g)[0]; }}\ng(0);\n"
DEPTHS = [(f"depth_call_{n}.js", n, RECURSION.format(n=n)) for n in (10, 25, 50, 100)] + [
    (f"depth_map_{n}.js", n, THROUGH_MAP.format(n=n)) for n in (10, 25, 50)
]


def expect(run_bin: str, name: str, source: str, tmp: Path) -> dict:
    """`name`'s entry: its source and native ecma-run's result."""
    path = tmp / name
    path.write_text(source)
    t0 = time.monotonic()
    r = subprocess.run([run_bin, str(path)], capture_output=True, text=True, timeout=TIMEOUT_S)
    ms = round((time.monotonic() - t0) * 1000)
    if r.returncode != 0:
        raise SystemExit(f"{name}: ecma-run exited {r.returncode}: {r.stdout[:200]}{r.stderr[-400:]}")
    outcome, _, rest = r.stdout.partition("\n")
    return {"name": name, "source": source, "stdout": rest, "outcome": outcome, "exitCode": 0, "nativeMs": ms}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="ecma-run")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("files", nargs="*", type=Path)
    args = ap.parse_args()
    if not args.files:
        args.files = [ROOT / f"tests/run/{p}.js" for p in SUITE] + [
            p for p in sorted((ROOT / "tests/dbg").iterdir()) if not p.name.startswith("proposal_")
        ]
    dbgs = sorted(f for f in args.files if f.suffix == ".dbg")
    beside = {d.with_suffix(".js") for d in dbgs}
    progs = [f for f in args.files if f.suffix == ".js" and f not in beside]
    transcripts = []
    for d in dbgs:
        js = d.with_suffix(".js")
        program = {"name": js.name, "source": js.read_text()} if js.is_file() else None
        transcripts.append({"name": d.name, "dbg": d.read_text(), "program": program})
    todo = [(p.name, None, p.read_text()) for p in progs] + DEPTHS
    tmp = args.out.parent / (args.out.name + ".programs")
    tmp.mkdir(parents=True, exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(JOBS) as ex:
        entries = list(ex.map(lambda t: expect(args.run, t[0], t[2], tmp), todo))
    for (_, depth, _), e in zip(todo, entries):
        if depth is not None:
            e["depth"] = depth
    args.out.write_text(json.dumps({"transcripts": transcripts, "programs": entries}, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
