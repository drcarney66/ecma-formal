#!/usr/bin/env python3
"""The debugger UI's model and pure parts in node, against native ecma-dbg.

tools/dbg/ui/model_test.mjs runs tools/dbg/ui/model.mjs on sessions of native
ecma-dbg as child processes (client.mjs's native-process transport), on the
programs of tests/dbg (the heap and state panes' requests among them), and
checks the panes' pure parts; then tools/dbg/ui/builds_test.mjs checks the build selector's logic (the table,
the order of a launch's arguments, the configuration kept per build, the page's URL) and what the page asks
of a browser. The browser's side: scripts/dbg_browser_test.py.

    python3 scripts/dbg_ui_test.py --node NODE --dbg .lake/build/bin/ecma-dbg
"""

import argparse
import subprocess
import sys


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--node", required=True)
    ap.add_argument("--dbg", required=True, help="native ecma-dbg")
    args = ap.parse_args()
    cmd = [args.node, "tools/dbg/ui/model_test.mjs", "--native", args.dbg, "--dir", "tests/dbg"]
    try:
        first = subprocess.run(cmd, timeout=600).returncode
        return first or subprocess.run([args.node, "tools/dbg/ui/builds_test.mjs"], timeout=60).returncode
    except subprocess.TimeoutExpired:
        print("no result within the time")
        return 1


if __name__ == "__main__":
    sys.exit(main())
