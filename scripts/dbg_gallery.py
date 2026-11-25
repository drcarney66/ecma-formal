#!/usr/bin/env python3
"""The debugger's examples: tools/dbg/gallery.json compiled into the gallery the site and the debugger read.

    dbg_gallery.py [--gallery tools/dbg/gallery.json] --out build/gallery.json

An example's id names its program: `demo/NAME` is tools/dbg/demo/NAME.js, `dbg/NAME` tests/dbg/NAME.js,
`run/NAME` tests/run/NAME.js, whose `// module: yes` header becomes `--module` and whose `// args:` header
its arguments (tests/run's headers, as scripts/js_run_test.py reads them); an example's own `args` come
after those. Each example is written with its program's name and source, its arguments, and the rest of
its entry as it is (tools/dbg/ui/gallery.mjs says what it means). The gallery is checked first: every id
names a program, every group exists, every example has a title, a line and a check for each build it
lists, each check its pauses and its end. tools/dbg/ui/gallery_test.mjs runs the checks.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GALLERY = ROOT / "tools/dbg/gallery.json"
DIRS = {"demo": ROOT / "tools/dbg/demo", "dbg": ROOT / "tests/dbg", "run": ROOT / "tests/run"}
FIELDS = {"id", "group", "title", "line", "builds", "breakpoints", "lines", "filters", "args", "demo", "note", "expand"}


def header_args(src: str) -> list[str]:
    """The driver arguments tests/run's headers give: `--module` for `// module: yes`, then `// args:`."""
    out = []
    if re.search(r"(?m)^// module: yes\s*$", src):
        out.append("--module")
    m = re.search(r"(?m)^// args:(.*)$", src)
    if m:
        out += m.group(1).split()
    return out


def compile_gallery(path: Path) -> dict:
    g = json.loads(path.read_text())
    errs: list[str] = []
    groups = {x["id"] for x in g["groups"]}
    seen: set[str] = set()
    out = []
    for e in g["examples"]:
        eid = e.get("id", "")
        if eid in seen:
            errs.append(f"{eid}: a second example of this id")
        seen.add(eid)
        kind, _, name = eid.partition("/")
        if kind not in DIRS or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            errs.append(f"{eid!r}: an id is demo/NAME, dbg/NAME or run/NAME")
            continue
        f = DIRS[kind] / f"{name}.js"
        if not f.is_file():
            errs.append(f"{eid}: no {f.relative_to(ROOT)}")
            continue
        extra = set(e) - FIELDS
        if extra:
            errs.append(f"{eid}: unknown fields {sorted(extra)}")
        if e.get("group") not in groups:
            errs.append(f"{eid}: no group {e.get('group')!r}")
        for k in ("title", "line"):
            if not isinstance(e.get(k), str) or not e[k].strip():
                errs.append(f"{eid}: no {k}")
        builds = e.get("builds")
        if not isinstance(builds, dict) or not builds:
            errs.append(f"{eid}: no builds")
            builds = {}
        for b, c in builds.items():
            if not isinstance(c, dict) or not isinstance(c.get("pauses"), list) or not isinstance(c.get("end"), str):
                errs.append(f"{eid} [{b}]: a check is {{pauses: [...], end: LINE}}")
                continue
            for p in c["pauses"]:
                if not (isinstance(p, dict) and isinstance(p.get("alg"), str) and isinstance(p.get("path"), str)):
                    errs.append(f"{eid} [{b}]: a pause is {{alg, path, frames?}}")
        src = f.read_text()
        out.append({
            **e,
            "name": f.name,
            "file": f.relative_to(ROOT).as_posix(),
            "source": src,
            "args": (header_args(src) if kind == "run" else []) + list(e.get("args", [])),
            "breakpoints": e.get("breakpoints", []),
            "lines": e.get("lines", []),
            "filters": e.get("filters", []),
        })
    if errs:
        raise SystemExit("dbg_gallery.py: " + path.name + ":\n  " + "\n  ".join(errs))
    return {"groups": g["groups"], "examples": out}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gallery", type=Path, default=GALLERY)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    g = compile_gallery(a.gallery)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(g, ensure_ascii=False, indent=1) + "\n")
    print(f"{a.out}: {len(g['examples'])} examples in {len(g['groups'])} groups")
    return 0


if __name__ == "__main__":
    sys.exit(main())
