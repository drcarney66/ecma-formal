#!/usr/bin/env python3
"""Collect diff and LOC metrics across all 14 ECMA-262 proposal branches for TC39 #117.

    nix develop ~/.local/state/ecma-formal/devshell -c python3 scripts/proposals_summary.py [--base main] [--out site/proposals-117.json]

For each proposal on the November 2026 TC39 agenda (117th meeting), inspects `git diff --numstat BASE..BRANCH`
(with generated code gitignored, every line in the diff is hand-written) and records:
- `algorithms_loc`: lines added/removed in `spec/formal/*.emu` and `spec/proposals/**` (English/overlay readings,
  resolutions, and any draft spec text)
- `model_loc`: lines added/removed in `lean/Ecma/**` and `lean/Engine/**` outside `Proofs/`, `Pins.lean`, `Claims.lean`
- `proofs_loc`: lines added/removed in `lean/Engine/Proofs/**`, `lean/Engine/Pins.lean`, `lean/Engine/Claims.lean`
- `tests_loc`: lines added/removed in `tests/**`
- `spec_emu_lines`: upstream proposal spec lines (when checked out or recorded)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUT = ROOT / "site/proposals-117.json"

AGENDA_117 = [
    {
        "id": "defer-import-eval",
        "build": "defer",
        "branch": "proposal-defer-import-eval",
        "stage": "3",
        "title": "import defer (with PR #97 cycle/TLA fix)",
        "presenter": "Nicolò Ribaudo",
        "repo": "https://github.com/tc39/proposal-defer-import-eval",
        "example": "run/import_defer_basic",
    },
    {
        "id": "import-text",
        "build": "import-text",
        "branch": "proposal-import-text",
        "stage": "3",
        "title": "Import Text (for Stage 4)",
        "presenter": "Eemeli Aro",
        "repo": "https://github.com/tc39/proposal-import-text",
        "example": "dbg/proposal_import_text",
    },
    {
        "id": "thenable-curtailment",
        "build": "thenable-curtailment",
        "branch": "proposal-thenable-curtailment",
        "stage": "3",
        "title": "Thenable Curtailment (PRs #22 & #26)",
        "presenter": "Matthew Gaudet",
        "repo": "https://github.com/tc39/proposal-thenable-curtailment",
        "example": "dbg/proposal_thenable_curtailment",
    },
    {
        "id": "deferred-reexports",
        "build": "deferred-reexports",
        "branch": "proposal-deferred-reexports",
        "stage": "2.7",
        "title": "Deferred Re-exports (export defer)",
        "presenter": "Nicolò Ribaudo",
        "repo": "https://github.com/tc39/proposal-deferred-reexports",
        "example": "dbg/proposal_deferred_reexports",
    },
    {
        "id": "json-parseimmutable",
        "build": "json-parseimmutable",
        "branch": "proposal-json-parseimmutable",
        "stage": "2.7",
        "title": "JSON.parse Options (PR #27 nullPrototypeObjects)",
        "presenter": "Peter Klecha",
        "repo": "https://github.com/tc39/proposal-json-parseimmutable",
        "example": "dbg/proposal_json_parseimmutable",
    },
    {
        "id": "esm-phase-imports",
        "build": "esm-phase-imports",
        "branch": "proposal-esm-phase-imports",
        "stage": "2.7",
        "title": "ESM Phase Imports (PR #65)",
        "presenter": "Guy Bedford",
        "repo": "https://github.com/tc39/proposal-esm-phase-imports",
        "example": "dbg/proposal_esm_phase_imports",
    },
    {
        "id": "immutable-arraybuffer",
        "build": "immutable-arraybuffer",
        "branch": "proposal-immutable-arraybuffer",
        "stage": "2.7",
        "title": "Immutable ArrayBuffers (for Stage 3)",
        "presenter": "Richard Gibson",
        "repo": "https://github.com/tc39/proposal-immutable-arraybuffer",
        "example": "dbg/proposal_immutable_arraybuffer",
    },
    {
        "id": "error-code-property",
        "build": "error-code-property",
        "branch": "proposal-error-code-property",
        "stage": "2",
        "title": "Error code property (to Stage 2.7)",
        "presenter": "James M Snell",
        "repo": "https://github.com/tc39/proposal-error-code-property",
        "example": "dbg/proposal_error_code_property",
    },
    {
        "id": "fma",
        "build": "fma",
        "branch": "proposal-fma",
        "stage": "2",
        "title": "Math.fusedMultiplyAdd (to Stage 2.7)",
        "presenter": "Waldemar Horwat",
        "repo": "https://github.com/tc39/proposal-fma",
        "example": "dbg/proposal_fma",
    },
    {
        "id": "composites",
        "build": "composites",
        "branch": "proposal-composites",
        "stage": "2",
        "title": "Composites",
        "presenter": "Ashley Claymore",
        "repo": "https://github.com/tc39/proposal-composites",
        "example": "dbg/proposal_composites",
    },
    {
        "id": "cancellation",
        "build": "cancellation",
        "branch": "proposal-cancellation",
        "stage": "1",
        "title": "Cancellation: AbortController & AbortSignal (PR #35)",
        "presenter": "Kevin Gibbons",
        "repo": "https://github.com/tc39/proposal-cancellation",
        "example": "dbg/proposal_cancellation",
    },
    {
        "id": "iterator-transfer",
        "build": "iterator-transfer",
        "branch": "proposal-iterator-transfer",
        "stage": "0",
        "title": "Iterator.prototype.transfer",
        "presenter": "James M Snell",
        "repo": "https://github.com/jasnell/proposal-iterator-transfer",
        "example": "dbg/proposal_iterator_transfer",
    },
    {
        "id": "trim-chars",
        "build": "trim-chars",
        "branch": "proposal-trim-chars",
        "stage": "0",
        "title": "Trim Specific Characters",
        "presenter": "Eemeli Aro",
        "repo": "https://github.com/eemeli/proposal-trim-chars",
        "example": "dbg/proposal_trim_chars",
    },
    {
        "id": "popcount",
        "build": "popcount",
        "branch": "proposal-popcount",
        "stage": "0",
        "title": "Bitwise counting (Math.popcount32 / Math.ctz32)",
        "presenter": "Richard Gibson",
        "repo": "https://github.com/js-choi/proposal-popcount",
        "example": "dbg/proposal_popcount",
    },
]


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout


def branch_exists(name: str) -> bool:
    return subprocess.run(["git", "rev-parse", "--verify", "--quiet", name], cwd=ROOT, capture_output=True).returncode == 0


def classify(path: str) -> str:
    if path.startswith("lean/"):
        if "/Gen/" in path:
            return "generated"
        if path.startswith("lean/Engine/Proofs/") or path in ("lean/Engine/Pins.lean", "lean/Engine/Claims.lean"):
            return "proofs"
        return "model"
    if (path.startswith("spec/formal/") and path.endswith(".emu")) or path.startswith("spec/proposals/"):
        return "algorithms"
    if path.startswith("tests/") and not path.endswith(".expected"):
        return "tests"
    return "meta"


def inspect_branch(entry: dict, base: str) -> dict:
    br = entry["branch"]
    if not branch_exists(br):
        return {**entry, "status": "missing"}
    head = git("rev-parse", br).strip()
    mb = git("merge-base", base, br).strip()
    buckets = {k: {"added": 0, "removed": 0, "files": 0} for k in ("algorithms", "model", "proofs", "tests", "meta", "generated")}
    for ln in git("diff", "--numstat", mb, head).splitlines():
        if not ln.strip():
            continue
        a, r, p = ln.split("\t")
        cat = classify(p)
        buckets[cat]["added"] += int(a) if a != "-" else 0
        buckets[cat]["removed"] += int(r) if r != "-" else 0
        buckets[cat]["files"] += 1

    # Upstream spec size if committed under spec/proposals/<id>/spec.* or submodule commit recorded
    pcommit = ""
    spec_lines = 0
    try:
        props_txt = git("show", f"{head}:spec/proposals.txt")
        prop_lines = [
            ln.split("#", 1)[0].split()
            for ln in props_txt.splitlines()
            if ln.split("#", 1)[0].split()
        ]
        # Prefer the line matching entry['id'] when multiple proposals are chained
        ordered = sorted(prop_lines, key=lambda ps: 0 if ps[0] == entry["id"] else 1)
        for parts in ordered:
            ppath = parts[1]
            # Check if ppath is inside a submodule gitlink (e.g. external/proposal-fma/spec.emu)
            sub_parts = Path(ppath).parts
            if len(sub_parts) >= 2 and sub_parts[0] == "external":
                sub_dir = f"{sub_parts[0]}/{sub_parts[1]}"
                sub_rel = "/".join(sub_parts[2:]) or "spec.emu"
                ls = git("ls-tree", head, sub_dir).strip()
                if ls.startswith("160000 "):
                    full_sha = ls.split()[2]
                    pcommit = full_sha[:7]
                    wt_file = ROOT / "build/worktrees" / entry["id"] / sub_dir / sub_rel
                    ext_file = ROOT / sub_dir / sub_rel
                    for cand in (wt_file, ext_file):
                        if cand.exists():
                            spec_lines = len(cand.read_text().splitlines())
                            break
                    break
            ls = git("ls-tree", head, ppath).strip()
            if ls and not ls.startswith("160000 ") and spec_lines == 0:
                blob = git("show", f"{head}:{ppath}")
                spec_lines = len(blob.splitlines())
                break
    except subprocess.CalledProcessError:
        pass

    return {
        **entry,
        "status": "ready",
        "commit": head[:7],
        "merge_base": mb[:7],
        "proposal_commit": pcommit,
        "spec_lines": spec_lines,
        "diff": buckets,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", default="main")
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    a = ap.parse_args()

    rows = [inspect_branch(e, a.base) for e in AGENDA_117]
    ready = [r for r in rows if r["status"] == "ready"]
    data = {
        "meeting": "117th Meeting of Ecma TC39 (November 30 – December 3, 2026)",
        "agenda": "https://github.com/tc39/agendas/blob/main/2026/11.md",
        "base": a.base,
        "proposals": rows,
    }
    out_path = a.out.resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(f"{out_path.relative_to(ROOT)}: {len(ready)}/{len(rows)} proposal branches ready")
    for r in ready:
        d = r["diff"]
        print(f"  {r['id']:22} [S{r['stage']:3}] alg=+{d['algorithms']['added']}/-{d['algorithms']['removed']}  "
              f"model=+{d['model']['added']}/-{d['model']['removed']}  "
              f"proofs=+{d['proofs']['added']}/-{d['proofs']['removed']}  "
              f"tests=+{d['tests']['added']}  gen={d['generated']['files']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
