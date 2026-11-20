#!/usr/bin/env python3
"""The spec-issue write-ups (docs/spec-issues/NN-*.md): their data, their quotations checked, their pages.

    python3 scripts/spec_issues.py check [-v] [NN...]   # the write-ups' form and every quotation of the text

Each write-up is read for its number and title (the first line, `# NN. Title`), its header items (`- **Location:**`,
`- **Kind:**`, `- **Model erratum:**`, …), and its sections. Its errata are the rows of spec/formal/errata.txt
whose last column names it; an erratum the editors fixed is named by docs/spec-issues/README.md's "Fixed upstream".

A quotation of the specification is a block quotation (`> …`). Each is checked against the pinned spec.html
(scripts/spec_text.py), as the laws' quotations are (scripts/law_quotes.py `norm`: tags, entities, ecmarkdown's
emphasis and white space dropped on both sides; an ellipsis skips text, the parts around it in order):

- a paragraph that starts with a step's label (`4.`, `b.`, `ii.`) is a step: its text must be the text of a step
  of that label in an algorithm of a clause the write-up names, and the labels of the steps it is quoted under
  (by indentation) must be that step's parents: the step numbers are the pinned text's;
- any other paragraph must occur in a clause the write-up names; one that starts `§N.N …:` must occur in §N.N.

The clauses a write-up names are the ids it gives in backquotes (`#sec-…`) and the clause numbers it gives (§N.N).
A block quotation of another text (IEEE 754, test262, an earlier revision of ECMA-262) is preceded by a line
`<!-- quote: WHAT -->` and is not checked; `check -v` lists them. A quotation in double quotes inside a sentence is
checked the same way when it is at least four words long and occurs in a clause the write-up names; the others
are listed (`-v`), not failed: a double-quoted phrase is as often a name or a program's output as a quotation.

Each write-up has an Upstream item (`- **Upstream:** Checked YYYY-MM-DD: …`), and it names only issues, pull
requests and commits that docs/spec-issues/upstream.tsv records for that write-up, with the record's state and
month, and every one the record has for it (scripts/spec_issues_upstream.py).
"""

from __future__ import annotations

import argparse
import html
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import errata_page  # noqa: E402
import law_quotes  # noqa: E402
import spec_issues_upstream as upstream  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
DIR = ROOT / "docs/spec-issues"
EXAMPLES = DIR / "examples"
ERRATA = ROOT / "spec/formal/errata.txt"

ID_RE = re.compile(r"`#((?:sec|prod|table|figure|eqn|await|step)[A-Za-z0-9_.%@-]*)`")
SECNUM_RE = re.compile(r"§\s?((?:[A-Z]|\d+)(?:\.\d+)*)")
STEP_RE = re.compile(r"^(\s*)(\d+(?:\.(?:[a-z]{1,2}|[ivxl]+))*|[a-z]{1,2}|[ivxl]+)\.\s+(.*)$")
MARK_RE = re.compile(r"^<!--\s*quote:\s*(.*?)\s*-->\s*$")


@dataclass
class Issue:
    number: int
    slug: str  # 01-number-multiply-zero-sign
    path: Path
    title: str  # the Markdown of the title, without `# NN. `
    text: str
    header: dict[str, str]  # Location, Kind, Upstream, Model erratum, …: their Markdown
    sections: list[str]
    errata: list[str] = field(default_factory=list)  # errata.txt's rows naming it
    retired: list[str] = field(default_factory=list)  # errata the editors fixed (README.md, Fixed upstream)
    example: Path | None = None  # docs/spec-issues/examples/NN-*.js or NN-*/

    @property
    def num(self) -> str:
        return f"{self.number:02d}"


def header_items(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    cur = None
    for ln in text.split("\n")[1:]:
        if ln.startswith("## "):
            break
        m = re.match(r"^- \*\*([^*:]+):\*\*\s*(.*)$", ln)
        if m:
            cur = m.group(1)
            out[cur] = m.group(2)
        elif cur and ln.startswith("  ") and ln.strip():
            out[cur] += " " + ln.strip()
        elif not ln.strip() and cur:
            cur = None
    return out


def fixed_upstream_names() -> dict[str, list[str]]:
    """README.md's "Fixed upstream": the write-up's number → the errata the editors' fix retired."""
    t = (DIR / "README.md").read_text()
    m = re.search(r"(?ms)^## Fixed upstream\n(.*?)(?=^## |\Z)", t)
    out: dict[str, list[str]] = {}
    for item in re.findall(r"(?ms)^- \[(\d+)\]\([^)]*\): (.*?), by\s", m.group(1) if m else ""):
        out[item[0]] = re.split(r",? and |, ", re.sub(r"\s+", " ", item[1]).strip())
    return out


def issues() -> list[Issue]:
    rows: dict[str, list[str]] = {}
    for ln in ERRATA.read_text().split("\n"):
        if ln.strip() and not ln.startswith("#"):
            f = ln.split("\t")
            for p in f[5].split():
                rows.setdefault(Path(p).name, []).append(f[0])
    fixed = fixed_upstream_names()
    out = []
    for p in sorted(DIR.glob("[0-9][0-9]-*.md")):
        text = p.read_text()
        first = text.split("\n", 1)[0]
        m = re.match(r"^# (\d+)\.\s+(.*)$", first)
        if not m:
            raise SystemExit(f"{p.relative_to(ROOT)}: the first line is not `# NN. Title`")
        if int(m.group(1)) != int(p.name[:2]):
            raise SystemExit(f"{p.relative_to(ROOT)}: its title's number is {m.group(1)}")
        ex = [x for x in EXAMPLES.iterdir() if x.name.startswith(p.name[:3]) and (x.suffix == ".js" or x.is_dir())]
        out.append(Issue(int(m.group(1)), p.stem, p, m.group(2).strip(), text, header_items(text),
                         re.findall(r"(?m)^## (.*)$", text), rows.get(p.name, []), fixed.get(p.name[:2], []),
                         ex[0] if ex else None))
    return out


# ---------------------------------------------------------------------------------------------------------------
# The quotations


def md_norm(t: str) -> str:
    """Markdown's text as the check compares it: its escapes and links dropped, then law_quotes.norm."""
    t = re.sub(r"\\([\\`*_{}\[\]()#+\-.!|<>~])", r"\1", t)
    t = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", t)
    return law_quotes.norm(t)


def parts_in(text: str, quote: str) -> bool:
    pos = 0
    for part in re.split(r"\s*(?:…|\.\.\.)\s*", quote):
        p = md_norm(part)
        if not p:
            continue
        i = text.find(p, pos)
        if i < 0:
            return False
        pos = i + len(p)
    return True


@dataclass
class Item:
    kind: str  # "step", "prose", "gap"
    text: str
    labels: list[str] = field(default_factory=list)  # a step's label and its parents' labels, outermost first
    line: int = 0


@dataclass
class Block:
    line: int  # 1-based, of the first `>`
    mark: str | None  # the `<!-- quote: … -->` above it
    paras: list[list[Item]]


def blocks(text: str) -> list[Block]:
    lines = text.split("\n")
    out: list[Block] = []
    k = 0
    fence = False
    while k < len(lines):
        ln = lines[k]
        if ln.startswith("```"):
            fence = not fence
        if fence or not ln.startswith(">"):
            k += 1
            continue
        start = k
        mark = None
        j = k - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j >= 0 and (mm := MARK_RE.match(lines[j])):
            mark = mm.group(1)
        body = []
        while k < len(lines) and lines[k].startswith(">"):
            body.append((k + 1, re.sub(r"^> ?", "", lines[k])))
            k += 1
        paras: list[list[Item]] = []
        cur: list[Item] = []
        stack: list[tuple[int, str]] = []  # (indent, label)
        for no, b in body:
            if not b.strip():
                if cur:
                    paras.append(cur)
                cur, stack = [], []
                continue
            sm = STEP_RE.match(b)
            if sm and (not cur or cur[-1].kind != "prose" or not cur[-1].text):
                ind = len(sm.group(1))
                while stack and stack[-1][0] >= ind:
                    stack.pop()
                comps = sm.group(2).split(".")
                if len(comps) > 1:  # a step given by its path, `10.b.`
                    stack = []
                stack += [(ind, c) for c in comps]
                cur.append(Item("step", sm.group(3), [x for _, x in stack], no))
            elif re.match(r"^\s*- ", b):  # an item of a list
                cur.append(Item("prose", re.sub(r"^\s*- ", "", b), [], no))
            elif b.strip() in ("…", "...", "⋮"):
                cur.append(Item("gap", "", [], no))
            elif cur and cur[-1].kind in ("step", "prose"):
                cur[-1].text += " " + b.strip()
            else:
                cur.append(Item("prose", b.strip(), [], no))
        if cur:
            paras.append(cur)
        out.append(Block(start + 1, mark, paras))
    return out


class Checker:
    def __init__(self) -> None:
        self.sp = errata_page.Text()
        self.by_num = {v: k for k, v in self.sp.nums.items()}
        self._steps: dict[str, list[tuple[str, str]]] = {}

    def clauses_of(self, iss: Issue) -> list[str]:
        ids = ID_RE.findall(iss.text)
        ids += [self.by_num[n] for n in SECNUM_RE.findall(iss.text) if n in self.by_num]
        seen: list[str] = []
        for c in ids:
            if c not in seen:
                seen.append(c)
        return seen

    def steps(self, cid: str) -> list[tuple[str, str]]:
        if cid not in self._steps:
            raw = self.sp.raw(cid) or ""
            self._steps[cid] = [st for alg in re.findall(r"<emu-alg\b[^>]*>(.*?)</emu-alg>", raw, re.DOTALL)
                                for st in errata_page.alg_steps(alg)]
        return self._steps[cid]

    def text(self, cid: str) -> str:
        return self.sp.text(cid) or ""

    def check(self, iss: Issue) -> tuple[list[str], list[str], int]:
        """(failures, notes, quotations checked) of a write-up."""
        fails, notes, n = [], [], 0
        rel = iss.path.relative_to(ROOT).as_posix()
        cl = self.clauses_of(iss)
        for c in ID_RE.findall(iss.text):
            if not self.sp.exists(c):
                fails.append(f"{rel}: no element `#{c}` in spec.html")
        for b in blocks(iss.text):
            if b.mark:
                notes.append(f"{rel}:{b.line}: not checked ({b.mark})")
                continue
            for para in b.paras:
                where = cl
                first = para[0]
                if first.kind == "prose":
                    pm = re.match(r"^§\s?((?:[A-Z]|\d+)(?:\.\d+)*)\b[^:]{0,80}:\s+", first.text)
                    if pm and pm.group(1) in self.by_num:
                        where = [self.by_num[pm.group(1)]]
                        first.text = first.text[pm.end():]
                for it in para:
                    if it.kind == "gap":
                        continue
                    n += 1
                    why = self.item(it, where)
                    if why:
                        fails.append(f"{rel}:{it.line}: {why}")
        # The Upstream item quotes GitHub's titles, not the text.
        for no, q in inline_quotes(re.sub(r"(?ms)^- \*\*Upstream:\*\*.*?(?=^- \*\*|^\s*$)", lambda m: "\n" * m.group(0).count("\n"), iss.text)):
            if len(q.split()) < 4:
                continue
            if any(parts_in(self.text(c), q) for c in cl):
                n += 1
            else:
                notes.append(f"{rel}:{no}: an inline quotation not found in its clauses: \"{q[:80]}\"")
        return fails, notes, n

    def item(self, it: Item, where: list[str]) -> str | None:
        if it.kind == "prose":
            if any(parts_in(self.text(c), it.text) for c in where):
                return None
            return f"not in {', '.join(where[:4])}{'…' if len(where) > 4 else ''}: {it.text[:90]!r}"
        want = it.labels
        hits, near = [], []
        for c in where:
            for path, t in self.steps(c):
                if not parts_in(law_quotes.norm(t), it.text):
                    continue
                comps = path.split(".")
                if comps[-len(want):] == want:
                    hits.append((c, path))
                else:
                    near.append((c, path))
        if hits:
            return None
        if near:
            return (f"step {'.'.join(want)} {it.text[:60]!r} is step {near[0][1]} of {near[0][0]}"
                    + (f" (and {len(near) - 1} more)" if len(near) > 1 else ""))
        return f"no step {'.'.join(want)} of {', '.join(where[:4])} says {it.text[:90]!r}"


def inline_quotes(text: str) -> list[tuple[int, str]]:
    """Double-quoted text in the write-up's sentences (not in code, a block quotation or a table)."""
    out = []
    fence = False
    paras: list[tuple[int, str]] = []
    buf: list[str] = []
    start = 0
    for k, ln in enumerate(text.split("\n"), 1):
        if ln.startswith("```"):
            fence = not fence
            continue
        if fence or ln.startswith((">", "|", "#")) or not ln.strip():
            if buf:
                paras.append((start, " ".join(buf)))
            buf = []
            continue
        if not buf:
            start = k
        buf.append(ln.strip())
    if buf:
        paras.append((start, " ".join(buf)))
    for no, p in paras:
        p = re.sub(r"`[^`]*`", "", p)
        for m in re.finditer(r'"([^"]+)"|“([^”]+)”', p):
            out.append((no, m.group(1) or m.group(2)))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("-v", action="store_true")
    c.add_argument("only", nargs="*")
    a = ap.parse_args()
    ck = Checker()
    rec = upstream.by_writeup()
    bad = total = 0
    for iss in issues():
        if a.only and iss.num not in a.only:
            continue
        fails, notes, n = ck.check(iss)
        rel = iss.path.relative_to(ROOT).as_posix()
        fails += [f"{rel}: {x}" for x in upstream.check(iss.num, iss.header.get("Upstream"), rec.get(iss.num, []))]
        total += n
        bad += len(fails)
        for f in fails:
            print(f"FAIL {f}")
        if a.v:
            for x in notes:
                print(f"note {x}")
    nrec = sum(len(v) for k, v in rec.items() if not a.only or k in a.only)
    print(f"{'FAIL' if bad else 'ok  '} spec issues: {total} quotations checked, {nrec} upstream records named, "
          f"{bad} failing")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
