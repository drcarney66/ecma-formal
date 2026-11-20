#!/usr/bin/env python3
"""The debugger demo's scripts in node, on native ecma-dbg or its WebAssembly build.

tools/dbg/demo/demo_test.mjs walks each script of tools/dbg/demo/script.mjs on the
UI's model (tools/dbg/ui/model.mjs) and checks what each stop shows. The browser's
side: tools/dbg/ui/demotest.mjs. With --json spec-examples.json,
tools/dbg/ui/spec_examples_test.mjs runs the spec issues' examples instead (the
browser's side: tools/dbg/ui/spectest.mjs).

    python3 scripts/dbg_demo_test.py --node NODE --native .lake/build/bin/ecma-dbg [--dump] [NAME.js...]
    python3 scripts/dbg_demo_test.py --node NODE --wasm-node build/web/ecma-dbg-web.mjs
    python3 scripts/dbg_demo_test.py --node NODE --native .lake/build/bin/ecma-dbg \\
        --json build/site/spec-examples.json [ID...]
"""

import argparse
import os
import subprocess
import sys


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--node", required=True)
    engine = ap.add_mutually_exclusive_group(required=True)
    engine.add_argument("--native", help="native ecma-dbg")
    engine.add_argument("--wasm-node", help="ecma-dbg-web.mjs (its .wasm beside it)")
    ap.add_argument("--dump", action="store_true", help="print each stop's observation")
    ap.add_argument("--json", help="spec-examples.json: run the spec issues' examples instead")
    ap.add_argument("programs", nargs="*", help="only these programs (NAME.js, or the examples' IDs)")
    args = ap.parse_args()
    transport = ["--native", args.native] if args.native else ["--wasm-node", args.wasm_node]
    if args.json:
        if args.dump:
            ap.error("--json takes no --dump")
        cmd = [args.node, "tools/dbg/ui/spec_examples_test.mjs", "--json", args.json, *transport, *args.programs]
    else:
        cmd = [args.node, "tools/dbg/demo/demo_test.mjs", *transport, *(["--dump"] if args.dump else []), *args.programs]
    # Inside a caller's timeout (TEST_TIMEOUT), if it sets one.
    timeout = float(os.environ.get("TEST_TIMEOUT", 660)) - 60
    try:
        return subprocess.run(cmd, timeout=timeout).returncode
    except subprocess.TimeoutExpired:
        print(f"no result within {timeout:.0f} s")
        return 1


if __name__ == "__main__":
    sys.exit(main())
