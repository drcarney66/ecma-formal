#!/usr/bin/env python3
"""The debugger's tests: the transcripts of tests/dbg and the trace check.

Every tests/dbg/*.dbg runs against native ecma-dbg (tools/dbg/transcript.mjs:
requests sent, the engine's messages matched as subsets), or with `--wasm-node`
against its WebAssembly build in a node Worker (tools/dbg/client.mjs). Then, on two
programs, `stepIn` from the entry to the end pauses at exactly the steps that
`JS_TRACE_STEPS=1 ecma-run` prints after setup (`sec-id path.`). Each pause's step
(reading, path, text) is in its algorithm's `specAlgorithm` listing. On a native engine, every
tests/dbg program but spin.js and each PROGRAM is stepped in by statements, and at each pause
the JS stack has one frame per execution context (`--check-js-stack`).

    python3 scripts/dbg_transcripts_test.py --node NODE --dbg .lake/build/bin/ecma-dbg --run .lake/build/bin/ecma-run [PROGRAM...]
    python3 scripts/dbg_transcripts_test.py --node NODE --wasm-node build/web/ecma-dbg-web.mjs --run .lake/build/bin/ecma-run
"""

import argparse
import subprocess
import sys
from pathlib import Path

TRACE_PROGRAMS = ["tests/dbg/stepping.js", "tests/dbg/stop.js"]
# Not stepped by statements: spin.js runs 8,100 iterations, for the pause test.
JS_STACK_SKIP = {"spin.js"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--node", required=True)
    engine = ap.add_mutually_exclusive_group(required=True)
    engine.add_argument("--dbg", help="native ecma-dbg")
    engine.add_argument("--wasm-node", help="ecma-dbg-web.mjs (its .wasm beside it)")
    ap.add_argument("--run", required=True, help="ecma-run")
    ap.add_argument("programs", nargs="*", help="more programs for the JS stack check (native only)")
    args = ap.parse_args()
    runner = "tools/dbg/transcript.mjs"
    transcripts = sorted(str(p) for p in Path("tests/dbg").glob("*.dbg"))
    if not transcripts:
        print("no transcripts in tests/dbg")
        return 1
    status = 0
    # A path without `.mjs` names the module beside it.
    mjs = args.wasm_node if not args.wasm_node or args.wasm_node.endswith(".mjs") else args.wasm_node + ".mjs"
    transport = ["--native", args.dbg] if args.dbg else ["--wasm-node", mjs]
    trace = ["--trace", args.run]
    runs = [([], transcripts), (trace, TRACE_PROGRAMS)]
    if args.dbg:
        programs = sorted(str(p) for p in Path("tests/dbg").glob("*.js") if p.name not in JS_STACK_SKIP)
        programs += args.programs
        runs.append((["--check-js-stack"], programs))
    for extra, files in runs:
        r = subprocess.run([args.node, runner, *transport, *extra, *files])
        status = status or r.returncode
    return status


if __name__ == "__main__":
    sys.exit(main())
