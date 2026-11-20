#!/usr/bin/env python3
"""ECMA-262's grammars as Lean data: regenerate them, and check the regeneration.

`crates/jsgrammar` (its binary `jsgrammar`) writes lean/Ecma/Grammar/Gen/*.lean from spec.html's definition blocks
(docs/parser/GRAMMAR.md), and json.emu's (`--json`) after them; spec.html is the text (`scripts/spec_text.py`).

    scripts/jsgrammar.py --write --gen target/release/jsgrammar --readings spec/formal/readings.emu \
        --readings spec/formal/syntax.emu --json spec/formal/json.emu
    scripts/jsgrammar.py --check-regen --gen target/release/jsgrammar --index tests/parser/grammar_index.txt \
        --readings spec/formal/readings.emu --readings spec/formal/syntax.emu --json spec/formal/json.emu

The production, nonterminal and parameter ids are the kept ones of spec/formal/prod-ids.txt, nt-ids.txt and
param-ids.txt (crates/jsgrammar ids.rs): --write writes them back there, and --check-regen checks that regenerating
writes them and the modules as they are. --check-regen also checks the docstrings verbatim (spec.html's text of
every definition, exactly, under its own docstring), with spec.html's blocks found here, independently of the
generator, and that the generator's production ids are the index's `prod` lines. That the data itself prints as
spec.html's blocks, and the rules' readings as the overlay's, is `scripts/bijection.py`.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import spec_text

ROOT = Path(os.path.abspath(__file__)).parent.parent
GEN = Path("lean/Ecma/Grammar/Gen")

# The kept production, nonterminal and parameter ids (crates/jsgrammar ids.rs): read from here, written back by --write.
IDS = Path("spec/formal")
ID_TABLES = ("prod-ids.txt", "nt-ids.txt", "param-ids.txt")

BLOCK = re.compile(r'<emu-grammar type="definition">(.*?)</emu-grammar>', re.S)
DOC = re.compile(r"/-- `([^`]*)`, (spec\.html|json\.emu)\.\n\n~~~\n(.*?)\n~~~\n-/", re.S)


def spec_blocks(spec: str) -> list[tuple[int, str]]:
    """spec.html's definition blocks (not the examples): the line of the
    opening tag, and the text between the tags."""
    return [(spec.count("\n", 0, m.start()) + 1, m.group(1)) for m in BLOCK.finditer(spec)]


def is_comment(line: str) -> bool:
    return line.strip() == "// emu-format ignore"


def grammar_lines(text: str) -> list[str]:
    """A block's lines without blank lines and formatter comments, less the
    block's indentation (as spec.html has them otherwise)."""
    lines = [l for l in text.split("\n") if l.strip() and not is_comment(l)]
    base = min(len(l) - len(l.lstrip()) for l in lines)
    return [l[base:] for l in lines]


def check_verbatim(file: str, spec: str, gen_dir: Path) -> list[str]:
    """Every definition block of `file` (spec.html or json.emu, text `spec`) is its rules' docstrings, exactly: the
    rules of the blocks (each a line at the block's indentation and the lines below it) and the docstrings are the
    same texts, each as often. The docstrings cite no line (crates/jsgrammar emit.rs), so they are matched by text."""
    from collections import Counter
    found = Counter(m.group(3) for f in sorted(gen_dir.glob("*.lean")) for m in DOC.finditer(f.read_text()) if m.group(2) == file)
    rules: Counter = Counter()
    problems = []
    for line, text in spec_blocks(spec):
        lines = grammar_lines(text)
        if not lines:
            problems.append(f"{file}:{line}: an empty definition block")
            continue
        cur: list[str] = []
        for l in lines:
            if not l.startswith(" ") and cur:
                rules["\n".join(cur)] += 1
                cur = []
            cur.append(l)
        rules["\n".join(cur)] += 1
    for t in sorted((rules - found).elements()):
        problems.append(f"{file}: a rule with no docstring in {GEN} (or with one that is not its text):\n{t}")
    for t in sorted((found - rules).elements()):
        problems.append(f"{GEN}: a docstring for {file} that is no rule's text:\n{t}")
    if sum(found.values()) != sum(rules.values()):
        problems.append(f"{GEN}: {sum(found.values())} rule docstrings for {file}'s {sum(rules.values())} rules")
    return problems


def run_gen(gen: str, spec_path: str, out: Path, readings: list[str], json: str | None) -> None:
    extra = [x for f in readings for x in ("--readings", f)] + (["--json", json] if json else []) + ["--ids", str(ROOT / IDS)]
    r = subprocess.run([gen, "--spec", spec_path, "--out", str(out)] + extra, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"jsgrammar failed:\n{r.stderr}")


def check_prods(gen: str, spec_path: str, index_path: str, json: str | None) -> list[str]:
    """The generator's production ids are the index's `prod` lines."""
    r = subprocess.run([gen, "--spec", spec_path, "--prods", "--ids", str(ROOT / IDS)] + (["--json", json] if json else []), capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"jsgrammar --prods failed:\n{r.stderr}")
    got = r.stdout.split("\n")[:-1]
    want = [l for l in Path(index_path).read_text().split("\n") if l.startswith("prod ")]
    if got == want:
        return []
    diff = next((i for i, (x, y) in enumerate(zip(got, want)) if x != y), min(len(got), len(want)))
    return [f"{index_path}: the generator's production ids differ from the index's at line {diff} of {len(want)}: {got[diff:diff + 1]} vs {want[diff:diff + 1]}"]


def check_regen(gen: str, spec_path: str, index_path: str, readings: list[str], json: str | None) -> int:
    problems = []
    with tempfile.TemporaryDirectory() as tmp:
        run_gen(gen, spec_path, Path(tmp), readings, json)
        new = {p.name: p.read_text() for p in Path(tmp).glob("*.lean") if p.name != "Keys.lean"}
        tables = {t: (Path(tmp) / t).read_text() for t in ID_TABLES}
    old = {p.name: p.read_text() for p in (ROOT / GEN).glob("*.lean")}
    for name in sorted(set(new) | set(old)):
        if new.get(name) != old.get(name):
            problems.append(f"{GEN / name}: not what `scripts/jsgrammar.py --write` writes")
    for t, text in tables.items():
        if not (ROOT / IDS / t).exists() or (ROOT / IDS / t).read_text() != text:
            problems.append(f"{IDS / t}: not what `scripts/jsgrammar.py --write` writes (the kept ids)")
    problems += check_verbatim("spec.html", Path(spec_path).read_text(), ROOT / GEN)
    if json:
        problems += check_verbatim("json.emu", Path(json).read_text(), ROOT / GEN)
    problems += check_prods(gen, spec_path, index_path, json)
    for p in problems:
        print(p)
    print(f"{len(new)} generated files, {len(tables)} id tables: " + ("OK" if not problems else f"{len(problems)} problem(s)"))
    return 1 if problems else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check-regen", action="store_true")
    ap.add_argument("--gen", help="the generator, target/release/jsgrammar")
    ap.add_argument("--spec", help="a spec.html, or its directory (default: the text, scripts/spec_text.py)")
    ap.add_argument("--index", help="tests/parser/grammar_index.txt")
    ap.add_argument("--readings", action="append", default=[], help="an overlay file with readings of rules (spec/formal/*.emu); repeated, in order")
    ap.add_argument("--json", help="spec/formal/json.emu: the JSON text grammar")
    a = ap.parse_args()
    spec = spec_text.resolve(a.spec)
    if not os.path.exists(spec):
        sys.exit(f"{spec}: no spec.html (is external/ecma262 checked out at its pin? git submodule update --init external/ecma262)")
    if a.write:
        ws = str(ROOT)
        run_gen(a.gen, spec, Path(ws) / GEN, a.readings, a.json)
        (Path(ws) / GEN / "Keys.lean").unlink(missing_ok=True)  # the key blocks' resolutions: not kept here
        for t in ID_TABLES:
            (Path(ws) / GEN / t).replace(Path(ws) / IDS / t)
        print(f"wrote {GEN}")
        return 0
    return check_regen(a.gen, spec, a.index, a.readings, a.json)


if __name__ == "__main__":
    sys.exit(main())
