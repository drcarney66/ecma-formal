#!/usr/bin/env python3
"""The text: the specification every generator, check and page of this repository reads.

    python3 scripts/spec_text.py            # make it if it is stale; print its directory
    python3 scripts/spec_text.py --check    # exit 1 if it would have to be made again
    python3 scripts/spec_text.py --report   # make it; print what each proposal's merge did

The text is ECMA-262 as pinned (`external/ecma262`) with the proposals `spec/proposals.txt` names applied to it in
order, each by `scripts/apply_proposal.py` with its answers file. With no proposal named, it is
`external/ecma262` itself, and every consumer reads exactly that.

With a proposal named, the text is a build product: `build/text/` holds the merged `spec.html`, beside it the files
spec.html imports and the figures (`img/`, the base's and the proposals'), and `inputs.txt`, the digest of
everything it was made from (the list, the base's files, each proposal's spec.emu and figures, each answers file,
this script and the merge tool). A consumer calls `spec_html()` or `spec_dir()`: when `inputs.txt` does not match
the inputs as they are, the text is made again (in well under a second) before it is read, so a stale copy is
never read. A merge that refuses stops the consumer, with the refusals.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / "external/ecma262"
LIST = ROOT / "spec/proposals.txt"
OUT = ROOT / "build/text"
IDS_OUT = ROOT / "build/ids"
# beside spec.html, what a consumer reads besides it: the imported tables, ESMeta's ignore list (gen_spec.py)
BESIDE = ("esmeta-ignore.json",)


def ids_dir() -> Path:
    """The directory holding the active *-ids.txt tables: build/ids when generated, else spec/formal."""
    if (IDS_OUT / "clause-ids.txt").exists():
        return IDS_OUT
    return ROOT / "spec/formal"


def proposals() -> list[tuple[str, Path, Path | None]]:
    """The proposals spec/proposals.txt names, in order: name, spec.emu, answers file (or none)."""
    out = []
    if not LIST.exists():
        return out
    for n, line in enumerate(LIST.read_text().splitlines(), 1):
        f = line.split("#", 1)[0].split()
        if not f:
            continue
        if len(f) not in (2, 3):
            sys.exit(f"{LIST.relative_to(ROOT)}:{n}: want NAME SPEC.EMU [ANSWERS], got {line!r}")
        emu = ROOT / f[1]
        emu = emu / "spec.emu" if emu.is_dir() else emu
        out.append((f[0], emu, ROOT / f[2] if len(f) == 3 else None))
    return out


def _inputs(props: list[tuple[str, Path, Path | None]]) -> str:
    """The digest of every input, one line each: what `inputs.txt` records."""
    files = [LIST, Path(__file__).resolve(), ROOT / "scripts/apply_proposal.py", BASE / "spec.html"]
    files += sorted(BASE.glob("table-*.html")) + [BASE / b for b in BESIDE] + sorted((BASE / "img").glob("*"))
    for _, emu, ans in props:
        files += [emu, *sorted((emu.parent / "img").glob("*"))] + ([ans] if ans else [])
    lines = []
    for f in files:
        h = hashlib.sha256(f.read_bytes()).hexdigest() if f.is_file() else "missing"
        lines.append(f"{h}  {os.path.relpath(f, ROOT)}")
    return "\n".join(lines) + "\n"


def stale() -> bool:
    """Whether the text would have to be made again before it is read."""
    props = proposals()
    if not props:
        return False
    rec = OUT / "inputs.txt"
    return not rec.exists() or rec.read_text() != _inputs(props) or not (OUT / "spec.html").exists()


def make(verbose: bool = False) -> Path:
    """Make build/text from the inputs (each proposal merged in turn); a refusal exits with the refusals."""
    sys.path.insert(0, str(ROOT / "scripts"))
    import apply_proposal as ap

    props = proposals()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    tmp = Path(tempfile.mkdtemp(prefix=".text-", dir=OUT.parent))
    try:
        for f in [*BASE.glob("table-*.html"), *(BASE / b for b in BESIDE)]:
            if f.is_file():
                shutil.copyfile(f, tmp / f.name)
        if (BASE / "img").is_dir():
            shutil.copytree(BASE / "img", tmp / "img")
        text = (BASE / "spec.html").read_text(encoding="utf-8")
        for name, emu, ans in props:
            out, rep = ap.merge(text, emu.read_text(encoding="utf-8"), ap.read_resolutions(str(ans) if ans else None))
            if rep["refusals"]:
                for r in rep["refusals"]:
                    print(f"REFUSED {r['clause']} block {r['block']}: {r['message']}", file=sys.stderr)
                    if r["diff"]:
                        print("    " + r["diff"].replace("\n", "\n    "), file=sys.stderr)
                sys.exit(f"spec_text: the merge of proposal {name} refused {len(rep['refusals'])} time(s)"
                         f" (answer in {ans.relative_to(ROOT) if ans else 'an answers file'}); the text is not made")
            copied, problems = ap.copy_images(str(emu.parent), str(tmp), out, str(tmp))
            rep["images"] = copied
            rep["image_problems"] = problems
            (tmp / f"report-{name}.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False))
            c, log = rep["checks"], rep["log"]
            if verbose or rep["warnings"] or problems:
                print(f"spec_text: {name}: {len(log['replaced'])} clauses changed, {len(log['inserted'])} inserted, "
                      f"{len(log['removed'])} removed, {len(copied)} figures; <ins> missing {len(c['ins_missing'])}, "
                      f"<del> left {len(c['del_left'])}, clause tree {'as expected' if c['tree_ok'] else 'NOT as expected'}",
                      file=sys.stderr)
                for w in rep["warnings"] + problems:
                    print(f"spec_text: {name}: warning: {w}", file=sys.stderr)
            text = out
        (tmp / "spec.html").write_text(text, encoding="utf-8")
        (tmp / "inputs.txt").write_text(_inputs(props))
        old = OUT.parent / f".old-{os.getpid()}"
        if OUT.exists():
            OUT.rename(old)
        tmp.rename(OUT)
        shutil.rmtree(old, ignore_errors=True)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return OUT


def spec_dir() -> Path:
    """The directory of the text's spec.html (and the files beside it), made first if it is stale."""
    if not proposals():
        return BASE
    if stale():
        make()
    return OUT


def spec_html() -> Path:
    """The text's spec.html, made first if it is stale."""
    return spec_dir() / "spec.html"


def resolve(arg: str | os.PathLike | None) -> str:
    """A consumer's `--spec` argument (a spec.html or its directory; none: the text) as a spec.html path."""
    if arg is None:
        return str(spec_html())
    arg = str(arg)
    return arg if arg.endswith(".html") else os.path.join(arg, "spec.html")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="exit 1 if the text is stale (nothing is made)")
    ap.add_argument("--report", action="store_true", help="make the text again and say what each merge did")
    a = ap.parse_args()
    if a.check:
        s = stale()
        print(f"{OUT.relative_to(ROOT)} is {'stale' if s else 'current'}" if proposals() else
              f"no proposal named: the text is {BASE.relative_to(ROOT)}")
        return 1 if s else 0
    if a.report and proposals():
        make(verbose=True)
    print(spec_dir())
    return 0


if __name__ == "__main__":
    sys.exit(main())
