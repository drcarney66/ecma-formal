#!/usr/bin/env python3
"""The bijection between the Lean specification data and `spec/spectec/**/*.spectec`.

    python3 scripts/bijection.py [--print .lake/build/bin/ecma-print] [--spec-dir spec/spectec]
                                 [--json FILE] [-v]

`ecma-print` (`lean/SpecPrint.lean`) prints every file in `spec/spectec/` (outside `prose/`) back from
`Ecma.Gen.*` and `Ecma.Grammar.Gen.*` as `@@file <rel_path> ... @@end` blocks using `Ecma.Print.SpecTec` and
`Ecma.Grammar.PrintSpecTec`. (`spec/spectec/prose/*.spectec` is checked by `spectec roundtrip` and
`ids_regenerated` in `scripts/quick_check.py`.) This script checks that:

- `ecma-print` emits the exact set of non-prose `.spectec` files under `spec/spectec/` once each;
- every emitted file matches its `.spectec` file on disk byte for byte.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(os.path.abspath(__file__)).parent.parent
MAX_SHOWN = 30


def first_diff(a: str, b: str) -> tuple[int, str, str]:
    """The first 0-based line index where `a` and `b` differ, and the two lines."""
    x, y = a.split("\n"), b.split("\n")
    k = next((k for k in range(min(len(x), len(y))) if x[k] != y[k]), min(len(x), len(y)))
    return k, (x[k] if k < len(x) else "<end>"), (y[k] if k < len(y) else "<end>")


def parse_blocks(report: str) -> tuple[dict[str, str], list[str]]:
    """Parse `@@file <rel> ... @@end` blocks from `ecma-print` stdout."""
    files: dict[str, str] = {}
    dups: list[str] = []
    lines = report.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        line = lines[i].rstrip("\r\n")
        if not line:
            i += 1
            continue
        if not line.startswith("@@file "):
            raise SystemExit(f"ecma-print: line {i + 1} outside @@file block: {line[:80]!r}")
        rel = line[len("@@file "):]
        i += 1
        chunks: list[str] = []
        while i < len(lines) and lines[i].rstrip("\r\n") != "@@end":
            chunks.append(lines[i])
            i += 1
        if i >= len(lines):
            raise SystemExit(f"ecma-print: unterminated @@file {rel}")
        i += 1
        if rel in files:
            dups.append(rel)
        files[rel] = "".join(chunks)
    return files, dups


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--print", dest="printer", default=str(ROOT / ".lake/build/bin/ecma-print"))
    ap.add_argument("--spec-dir", default=str(ROOT / "spec/spectec"))
    ap.add_argument("--json", metavar="FILE", help="write machine-readable summary JSON")
    ap.add_argument("-v", action="store_true", help="print per-file status")
    a = ap.parse_args()

    printer = Path(a.printer)
    if not printer.is_file():
        print(f"FAIL bijection: {printer} not found (run `lake build ecma-print`)")
        return 1

    spec_dir = Path(a.spec_dir)
    want = {
        p.relative_to(spec_dir).as_posix(): p
        for p in sorted(spec_dir.rglob("*.spectec"))
        if p.relative_to(spec_dir).parts[0] != "prose"
    }
    if not want:
        print(f"FAIL bijection: no .spectec files under {spec_dir}")
        return 1

    proc = subprocess.run([str(printer)], capture_output=True, text=True)
    if proc.returncode != 0:
        print(f"FAIL bijection: {printer} exited {proc.returncode}:\n{proc.stderr.strip()}")
        return 1

    got, dups = parse_blocks(proc.stdout)
    issues: list[str] = []
    for d in dups:
        issues.append(f"duplicate @@file {d}")
    for missing in sorted(want.keys() - got.keys()):
        issues.append(f"missing in ecma-print: {missing}")
    for extra in sorted(got.keys() - want.keys()):
        issues.append(f"extra in ecma-print: {extra}")

    matched = 0
    total_bytes = 0
    for rel, path in want.items():
        disk_bytes = path.read_bytes()
        total_bytes += len(disk_bytes)
        if rel not in got:
            continue
        disk_text = disk_bytes.decode("utf-8")
        pr_text = got[rel]
        if disk_text == pr_text:
            matched += 1
            if a.v:
                print(f"ok   {rel} ({len(disk_bytes)} bytes)")
        else:
            k, expected, actual = first_diff(disk_text, pr_text)
            issues.append(
                f"{rel}: line {k + 1} differs:\n  spec:  {expected!r}\n  print: {actual!r}"
            )

    if a.json:
        Path(a.json).write_text(
            json.dumps(
                {
                    "spec_dir": str(spec_dir),
                    "total_files": len(want),
                    "matched_files": matched,
                    "total_bytes": total_bytes,
                    "issues": issues,
                },
                indent=2,
            )
            + "\n"
        )

    for msg in issues[:MAX_SHOWN]:
        print("FAIL " + msg)
    if len(issues) > MAX_SHOWN:
        print(f"... {len(issues) - MAX_SHOWN} more differences omitted")

    if issues:
        print(f"FAIL bijection: {matched}/{len(want)} SpecTec files match ({len(issues)} issue(s))")
        return 1

    print(f"ok  bijection: {matched}/{len(want)} SpecTec files match byte-for-byte ({total_bytes} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
