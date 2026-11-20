#!/usr/bin/env python3
"""spec.html's algorithm notation as data (crates/spec-gen, its binary `spec-gen`).

    scripts/gen_spec.py --roundtrip --gen target/release/spec-gen --overlay spec/formal
    scripts/gen_spec.py --write --gen target/release/spec-gen   # regenerate lean/Ecma/Gen
    scripts/gen_spec.py --report --gen target/release/spec-gen --overlay spec/formal
                                       # coverage, ambiguity, residue, early errors, memory model, types

spec.html is the text (`scripts/spec_text.py`: ECMA-262 as pinned, with the proposals spec/proposals.txt names);
`--spec FILE-OR-DIR` reads another.

--roundtrip checks the generator's half of the bijection. The parser's own round trip: every step and every
emu-alg body prints back from its tree and from its data byte for byte, and so does section 29 (the memory model)
outside its emu-algs (`spec-gen roundtrip`). Regeneration: the generator's output is the checked-in lean/Ecma/Gen,
and the names `Ecma.Known` (lean/Ecma/Notation/Syntax.lean) fixes are at their ids in it. The residue only
shrinks: no line of `spec-gen residue -lines` is missing from spec/formal/residue.txt; errata.txt is `spec-gen
errata -lines` (where the literal errata stop, and their reports). So do the type findings: no line of `spec-gen
types -lines` is missing from spec/formal/type-findings.txt, and no dyn site of `spec-gen types -dyn` from
spec/formal/type-dyn-sites.txt. The other half, that the Lean data itself prints back to spec.html and the overlay,
is `scripts/bijection.py`.
"""

import argparse
import filecmp
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import spec_text

ROOT = Path(os.path.abspath(__file__)).parent.parent
DATA = Path("lean/Ecma/Gen")
# modules the generator also writes whose data types this repository does not have
DROPPED = ("Examples", "Host", "Memory")


def kept(name: str) -> bool:
    return not name.startswith(DROPPED)


OVERLAY: list[str] = []

# The frozen phrase, primitive, sort, field and enum ids: the generator numbers by these files and appends new names.
# The kept clause, SDO, concrete-method, erratum, residue reason and residue kind ids (crates/spec-gen ids.rs): a
# number per name, a new name the next unused number, a name the text no longer has kept, marked retired.
# The kept table ids likewise (`table-ids.txt`, by the table's Lean name). The kept production, nonterminal and
# parameter ids (prod-, nt-, param-ids.txt) are crates/jsgrammar's, which scripts/jsgrammar.py --write writes; spec-gen
# reads them.
INDEXES = [Path(f"spec/formal/{t}-ids.txt") for t in ("phrase", "prim", "sort", "field", "enum", "clause", "sdo", "method", "erratum", "reason", "note", "table")]


def generate(gen: str, spec: str, out: Path) -> None:
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "emit", f"--out={out}"], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"spec-gen emit failed:\n{r.stderr}")


def check_regen(gen: str, spec: str) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        generate(gen, spec, Path(tmp))
        new = sorted(p.name for p in Path(tmp).glob("*.lean") if kept(p.name))
        old = sorted(p.name for p in (ROOT / DATA).glob("*.lean"))
        if new != old:
            return [f"the data's files differ from the generator's: {sorted(set(new) ^ set(old))[:5]}"]
        bad = [n for n in new if not filecmp.cmp(Path(tmp) / n, ROOT / DATA / n, shallow=False)]
        problems = [f"{DATA}/{n} is not the generator's output (scripts/gen_spec.py --write)" for n in bad[:5]]
        for f in INDEXES:
            if not (ROOT / f).exists() or (Path(tmp) / f.name).read_text() != (ROOT / f).read_text():
                problems.append(f"{f} is not the generator's numbering of the data's names (scripts/gen_spec.py --write writes it)")
        return problems


# The Known id constants whose names abbreviate the declaration at their id (others spell it, up to case and
# punctuation): constant -> the declared name.
KNOWN_ALIASES = {
    "fCodeState": "code evaluation state", "pF": "𝔽", "pR": "ℝ", "pZ": "ℤ", "pEmptyString": "the empty String",
    "pConcat": "string-concatenation", "pClamp": "clamping", "pOwnLookup": "OwnPropertyLookup",
    "pOwnCreate": "OwnPropertyCreate", "pOwnReplace": "OwnPropertyReplace",
    "pOwnSetAttribute": "OwnPropertySetAttribute", "pOwnRemove": "OwnPropertyRemove",
    "pApprox": "implementation-approximated", "pHostChoice": "implementation-defined choice",
    "pWebBrowser": "the host is a web browser", "pOwnHas": "OwnPropertyHas",
}


def check_known() -> list[str]:
    """The generated sorts begin with Ecma.Known.sorts (lean/Ecma/Notation/Syntax.lean), and each Known enum, field
    and primitive id constant names the declaration the generated data has at its id (KNOWN_ALIASES, or its name up
    to case and punctuation)."""
    syn = (ROOT / "lean/Ecma/Notation/Syntax.lean").read_text()
    known = syn[syn.index("namespace Known"):syn.index("end Known")]
    decls = (ROOT / DATA / "Decls.lean").read_text()
    problems = []
    tables = {}
    for t in ("enums", "fields", "sorts", "prims"):
        d = re.search(rf"def {t} : Array String :=\s*(.*?)\n\n", decls, re.S)
        tables[t] = re.findall(r'"((?:[^"\\]|\\.)*)"', d.group(1))
    m = re.search(r"def sorts : Array String := #\[(.*?)\]", known, re.S)
    want = re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1)) if m else []
    if not want:
        problems.append("Known.sorts not found")
    elif tables["sorts"][: len(want)] != want:
        problems.append("Decls.sorts does not begin with Known.sorts")
    norm = lambda x: re.sub(r"[^a-z0-9]", "", x.lower())
    for t, ty, pre in (("enums", "EnumId", "e"), ("fields", "FieldId", "f"), ("prims", "PrimId", "p")):
        for d, i in re.findall(rf"def ({pre}\w+) : {ty} := (\d+)", known):
            got = tables[t][int(i)] if int(i) < len(tables[t]) else None
            if got is None or (KNOWN_ALIASES.get(d, d[1:]) != got and norm(KNOWN_ALIASES.get(d, d[1:])) != norm(got)):
                problems.append(f"Known.{d} := {i}, but Decls.{t} has {got} there")
    return problems


def check_residue(gen: str, spec: str) -> list[str]:
    """No residue line that spec/formal/residue.txt lacks (`spec-gen residue -check`), and
spec/formal/permanent-sentences.txt as generated (`spec-gen residue -check-permanent`)."""
    ov = [o.removeprefix("--overlay=") for o in OVERLAY]
    if not ov:
        return []
    f = Path(ov[0]) / "residue.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "residue", "-check", str(f)])
    out = [] if r.returncode == 0 else [f"new residue (above): add it to {f.name} only with the coordinator's approval"]
    p = Path(ov[0]) / "permanent-sentences.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "residue", "-check-permanent", str(p)])
    return out + ([] if r.returncode == 0 else [f"{p.name} differs (above): regenerate it with `spec-gen residue -permanent`; an added line needs the coordinator's approval"])


def check_asserts(gen: str, spec: str) -> list[str]:
    """No open Assert that spec/formal/asserts-open.txt lacks (`spec-gen asserts -check`), and
spec/formal/assert-sites.txt as generated (`spec-gen asserts -check-all`)."""
    ov = [o.removeprefix("--overlay=") for o in OVERLAY]
    if not ov:
        return []
    f = Path(ov[0]) / "asserts-open.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "asserts", "-check", str(f)])
    out = [] if r.returncode == 0 else [f"new open Assert (above): add it to {f.name} only with the coordinator's approval"]
    p = Path(ov[0]) / "assert-sites.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "asserts", "-check-all", str(p)])
    return out + ([] if r.returncode == 0 else [f"{p.name} differs (above): regenerate it with `spec-gen asserts -all`"])


def check_errata(gen: str, spec: str) -> list[str]:
    """spec/formal/errata.txt as generated (`spec-gen errata -check`): per erratum its resolution, where
a literal one stops, its spec-issue reports."""
    ov = [o.removeprefix("--overlay=") for o in OVERLAY]
    if not ov:
        return []
    f = Path(ov[0]) / "errata.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "errata", "-check", str(f)])
    return [] if r.returncode == 0 else [f"{f.name} differs (above): regenerate it with `spec-gen errata -lines`; an added line needs the user's approval"]


def check_types(gen: str, spec: str) -> list[str]:
    """No type finding that spec/formal/type-findings.txt lacks (`spec-gen types -check`), no dyn site that
type-dyn-sites.txt lacks (`spec-gen types -check-dyn`), the type data is current (`spec-gen types -check-lean`); the findings by
algorithm against ESMeta's ignore list (`spec-gen types -esmeta`), printed when it is beside spec.html."""
    ov = [o.removeprefix("--overlay=") for o in OVERLAY]
    if not ov:
        return []
    f = Path(ov[0]) / "type-findings.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "types", "-check", str(f)])
    out = [] if r.returncode == 0 else [f"new type finding (above): add it to {f.name} only with the coordinator's approval"]
    dyn = Path(ov[0]) / "type-dyn-sites.txt"
    r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "types", "-check-dyn", str(dyn)])
    if r.returncode != 0:
        out.append(f"new dyn site (above): add it to {dyn.name} only with the coordinator's approval")
    if os.path.exists(os.path.join(os.path.dirname(spec), "esmeta-ignore.json")):
        print("type findings by algorithm against ESMeta's ignore list:", flush=True)
        r = subprocess.run([gen, f"--spec={spec}", *OVERLAY, "types", "-esmeta"])
        if r.returncode != 0:
            out.append("`spec-gen types -esmeta` failed (above)")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gen", required=True, help="the generator, spec-gen")
    ap.add_argument("--spec", help="a spec.html or its directory (default: the text, scripts/spec_text.py)")
    ap.add_argument("--overlay", help="the overlay directory, spec/formal")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--roundtrip", action="store_true")
    mode.add_argument("--report", action="store_true")
    mode.add_argument("--write", action="store_true")
    a, rest = ap.parse_known_args()
    spec = spec_text.resolve(a.spec)
    if not os.path.exists(spec):
        sys.exit(f"{spec}: no spec.html (is external/ecma262 checked out at its pin? git submodule update --init external/ecma262)")
    if a.overlay:
        OVERLAY.append(f"--overlay={os.path.dirname(a.overlay) if a.overlay.endswith('.emu') else a.overlay}")
    if a.write:
        ws = str(ROOT)
        OVERLAY[:] = [f"--overlay={Path(ws) / 'spec/formal'}"]
        data = Path(ws) / DATA
        # into a scratch directory first: a failed emission leaves the data as it was
        with tempfile.TemporaryDirectory(dir=data.parent) as tmp:
            generate(a.gen, spec, Path(tmp))
            for p in data.glob("*.lean"):
                p.unlink()
            for p in Path(tmp).glob("*.lean"):
                if kept(p.name):
                    p.replace(data / p.name)
            for f in INDEXES:
                (Path(tmp) / f.name).replace(Path(ws) / f)
        print(f"wrote {DATA}")
        return 0
    if a.report:
        for cmd in ("report", "residue", "early", "memmodel", "types"):
            r = subprocess.run([a.gen, f"--spec={spec}", *OVERLAY, cmd, *rest])
            if r.returncode != 0:
                return r.returncode
        return 0
    r = subprocess.run([a.gen, f"--spec={spec}", *OVERLAY, "roundtrip"])
    problems = [] if r.returncode == 0 else ["the parser's round trip failed (above)"]
    problems += check_regen(a.gen, spec)
    problems += check_residue(a.gen, spec)
    problems += check_asserts(a.gen, spec)
    problems += check_errata(a.gen, spec)
    problems += check_types(a.gen, spec)
    problems += check_known()
    for p in problems[:30]:
        print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
