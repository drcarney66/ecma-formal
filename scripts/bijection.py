#!/usr/bin/env python3
"""The bijection between the specification's data and its text.

    python3 scripts/bijection.py [--print .lake/build/bin/ecma-print] [--spec FILE-OR-DIR] [--overlay DIR]
                                 [--json FILE] [-v]

`ecma-print` (lean/SpecPrint.lean) prints every value of lean/Ecma/Gen and lean/Ecma/Grammar/Gen that holds the
specification's text, as Ecma.Print and Ecma.Grammar print it. This check finds every item again in the text
(`scripts/spec_text.py`: spec.html as pinned, with the proposals spec/proposals.txt names) and in the overlay
(spec/formal/*.emu), by the markup alone and independently of the generators: an algorithm as the `idx`th
`emu-alg` of its innermost clause, an SDO equation as a bullet `The X of <emu-grammar>…`, an early-error rule as a
top-level bullet of an Early Errors clause, a table as an `emu-table` element, a grammar block as an
`<emu-grammar type="definition">`, a reading by the SHA-256 of the step it reads (its `hash=`). It requires:

- each printed item to be its text, byte for byte;
- every algorithm, SDO equation, early-error rule, table and grammar block of spec.html to be printed exactly once,
  and so every SDO row's grammar key, which the data holds verbatim;
- every element of the overlay to be printed exactly once (each part of it the data holds), or to be in a class
  that is not data, named here with the reason; what the data has and the overlay does not to be the generator's
  own, as the generator holds it;
- where the machine reads a field the printer does not, the field to agree with its printed twin: a hexadecimal
  numeral's, a code unit's and a code point's value with its digits, a grammar key's production ids with its text.

It prints a line per class with its counts, the characters of spec.html by class (printed from trees, held
verbatim, data without a printer, not data), and the overlay's elements by class; `--json FILE` writes the same as
JSON. On a difference it fails with at most 30 messages, each saying what differs, where, and the two lines.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from html import unescape as html_unescape
from pathlib import Path

import jsgrammar
import spec_text

ROOT = Path(os.path.abspath(__file__)).parent.parent
OVERLAY = ROOT / "spec/formal"
# a twin early-error row's index offset (crates/spec-gen data.rs TWIN_IDX): a rule reading's copy, no bullet
TWIN_IDX = 1000
MAX_SHOWN = 30


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def first_diff(a: str, b: str) -> tuple[int, str, str]:
    """The first line at which `a` and `b` differ, and the two lines."""
    x, y = a.split("\n"), b.split("\n")
    k = next((k for k in range(min(len(x), len(y))) if x[k] != y[k]), min(len(x), len(y)))
    return k, (x[k] if k < len(x) else "<end>"), (y[k] if k < len(y) else "<end>")


# ---------------------------------------------------------------------------------------------------------------
# The printed items

@dataclass
class Item:
    kind: str
    args: list[str]
    text: str
    alts: list[tuple[str, str]] = field(default_factory=list)
    sdo: str | None = None

    def where(self) -> str:
        return f"{self.kind} {' '.join(self.args)}"


def read_items(report: str) -> list[Item]:
    """The items of ecma-print's output: `@@KIND ARGS`, its text, `@@alt NAME` before each reading's text,
    `@@end`; an early-error rule's text begins with a line `@@sdo NAME`."""
    out: list[Item] = []
    lines = report.split("\n")
    i = 0
    while i < len(lines):
        if not lines[i].startswith("@@"):
            if lines[i]:
                raise SystemExit(f"ecma-print: line {i + 1} is outside an item: {lines[i][:80]!r}")
            i += 1
            continue
        kind, _, rest = lines[i][2:].partition(" ")
        it = Item(kind, rest.split(" ") if rest else [], "")
        i += 1
        if kind == "early" and lines[i].startswith("@@sdo "):
            it.sdo = lines[i][6:]
            i += 1
        parts: list[list[str]] = [[]]
        names: list[str] = []
        while lines[i] != "@@end":
            if lines[i].startswith("@@alt "):
                names.append(lines[i][6:])
                parts.append([])
            else:
                parts[-1].append(lines[i])
            i += 1
        it.text = "\n".join(parts[0])
        it.alts = [(n, "\n".join(p)) for n, p in zip(names, parts[1:])]
        out.append(it)
        i += 1
    return out


# ---------------------------------------------------------------------------------------------------------------
# spec.html's items, found by their markup

@dataclass
class Want:
    """An item of the text: its kind, its text, where it is (file, offset of the text's first character)."""
    kind: str
    text: str
    file: str
    pos: int
    span: tuple[int, int] | None = None  # the characters of spec.html it covers


class Html:
    def __init__(self, path: str):
        self.path = path
        self.dir = Path(path).parent
        self.src = Path(path).read_text()
        # (clause id, index) -> Want: every emu-alg but the examples by its index among its clause's (examples
        # counted), then each equation bullet
        self.algs: dict[tuple[str, int], Want] = {}
        self.examples: list[tuple[int, int]] = []
        self.early: dict[tuple[str, int], Want] = {}
        self.tables: dict[tuple[str, int], Want] = {}
        self.blocks: list[Want] = []
        self.keys: dict[tuple[str, int], list[Want]] = {}
        self._algs_and_equations()
        self._early()
        self._tables()
        self._blocks()

    def at(self, pos: int) -> str:
        return f"spec.html:{line_of(self.src, pos)}"

    def _algs_and_equations(self) -> None:
        """Every emu-alg by its innermost clause with an id and its index among that clause's (examples counted,
        and kept apart), then each equation bullet (`<li>The X of <emu-grammar>…`), numbered after them. An
        algorithm's grammar key: the last `<emu-grammar>` of its clause before it, if no algorithm is between."""
        spec = self.src
        stack: list[tuple[str | None, int]] = []
        count: dict[str, int] = {}
        eqs: list[tuple[str, int, int]] = []
        last_alg_end: dict[int, int] = {}
        tags = re.compile(r"<(/?)(emu-clause|emu-annex|emu-alg|li)\b([^>]*)>")
        pos = 0
        while (m := tags.search(spec, pos)) is not None:
            close, tag, attrs = m.groups()
            pos = m.end()
            cid, start = next(((c, s) for c, s in reversed(stack) if c), (None, 0))
            if tag == "li":
                if close or attrs:
                    continue
                end = spec.find("</li>", m.end())
                if cid and re.match(r"\s*The \w+ of <emu-grammar", spec[m.end():end]):
                    eqs.append((cid, m.end(), end))
                continue
            if tag == "emu-alg":
                if close:
                    continue
                end = spec.index("</emu-alg>", m.end())
                pos = end + len("</emu-alg>")
                if cid is None:
                    continue
                i = count.get(cid, 0)
                count[cid] = i + 1
                lo = max(start, last_alg_end.get(start, start))
                last_alg_end[start] = pos
                if "example" in attrs:
                    self.examples.append((m.start(), pos))
                    continue
                self.algs[(cid, i)] = Want("alg", spec[m.end():end], "spec.html", m.end(), (m.end(), end))
                g = spec.rfind("<emu-grammar", lo, m.start())
                if g >= 0:
                    a = spec.index(">", g) + 1
                    b = spec.index("</emu-grammar>", a)
                    self.keys[(cid, i)] = [Want("key", spec[a:b], "spec.html", a, (a, b))]
            elif close:
                stack.pop()
            else:
                idm = re.search(r'\bid="([^"]+)"', attrs)
                stack.append((idm.group(1) if idm else None, m.end()))
        for cid, a, b in eqs:
            i = count.get(cid, 0)
            count[cid] = i + 1
            self.algs[(cid, i)] = Want("row", spec[a:b], "spec.html", a, (a, b))
        self.counts = count

    def instance(self, cid: str, idx: int) -> Want | None:
        """An instance `TEMPLATE/Name`'s body: the template clause's, with its heading's parameter `<var>P</var>`
        replaced by Name in code and String forms, and a code form that is one quoted String written as that
        String; None unless Name is a `<dfn>%Name%</dfn>`."""
        tmpl, _, name = cid.partition("/")
        h1 = re.search(rf'<emu-clause id="{re.escape(tmpl)}"[^>]*>\s*<h1>(.*?)</h1>', self.src)
        param = re.search(r"_(\w+)_", h1.group(1)) if h1 else None
        base = self.algs.get((tmpl, idx))
        if not param or base is None or f"<dfn>%{name}%</dfn>" not in self.src:
            return None
        var = f"<var>{param.group(1)}</var>"

        def sub(m: re.Match) -> str:
            if m.group(1) is not None:
                inner = m.group(1).replace(var, name)
                return f"*{inner}*" if re.fullmatch(r'"[^"]*"', inner) else f"<code>{inner}</code>"
            return '*"' + m.group(2).replace(var, name) + '"*'

        return Want("alg", re.sub(r'<code>(.*?)</code>|\*"(.*?)"\*', sub, base.text), "spec.html", base.pos)

    def _early(self) -> None:
        """(clause id, index) -> content: each top-level `<li>` of a `<ul>` at an Early Errors clause's own column,
        numbered after the clause's emu-algs and equation bullets."""
        spec = self.src
        for m in re.finditer(r'<emu-(?:clause|annex) id="([^"]+)"[^>]*>\n( *)<h1>Static Semantics: Early Errors</h1>', spec):
            cid, col = m.group(1), len(m.group(2))
            end = min(x for x in (spec.find(k, m.end()) for k in ("<emu-clause", "<emu-annex", "</emu-clause>", "</emu-annex>")) if x >= 0)
            i = self.counts.get(cid, 0)
            # each bullet list's key blocks: those since the last list
            last = m.end()
            for u in re.finditer(rf"^ {{{col}}}<ul>", spec[m.end():end], re.M):
                at = m.end() + u.start() + col + 4
                keys = [(k.start(1), k.end(1)) for k in re.finditer(r"<emu-grammar>(.*?)</emu-grammar>", spec[last:at], re.S)]
                keys = [(a + last, b + last) for a, b in keys]
                depth, start = 0, None
                for t in re.finditer(r"<(/?)(ul|li)\b[^>]*>", spec[at:end]):
                    close, tag = t.groups()
                    if tag == "ul":
                        if close and depth == 0:
                            last = at + t.end()
                            break
                        depth += -1 if close else 1
                    elif depth == 0 and not close:
                        start = at + t.end()
                    elif depth == 0:
                        self.early[(cid, i)] = Want("early", spec[start:at + t.start()], "spec.html", start, (start, at + t.start()))
                        self.keys[(cid, i)] = [Want("key", spec[a:b], "spec.html", a, (a, b)) for a, b in keys]
                        i += 1

    def _tables(self) -> None:
        """Every emu-table element, by its innermost clause with an id and its index among that clause's tables;
        an imported table after the document's own, counted in its emu-import's clause."""
        spec = self.src
        stack: list[str | None] = []
        count: dict[str, int] = {}
        for m in re.finditer(r"<(/?)(emu-clause|emu-annex|emu-table)\b([^>]*)>", spec):
            close, tag, attrs = m.groups()
            if tag == "emu-table":
                if close:
                    continue
                end = spec.index("</emu-table>", m.end()) + len("</emu-table>")
                cid = next((c for c in reversed(stack) if c), None)
                if cid is not None:
                    i = count.get(cid, 0)
                    count[cid] = i + 1
                    self.tables[(cid, i)] = Want("table", spec[m.start():end], "spec.html", m.start(), (m.start(), end))
            elif close:
                stack.pop()
            else:
                idm = re.search(r'\bid="([^"]+)"', attrs)
                stack.append(idm.group(1) if idm else None)
        stack = []
        for m in re.finditer(r'<(/?)(emu-clause|emu-annex)\b([^>]*)>|<emu-import href="([^"]+)"', spec):
            close, tag, attrs, href = m.groups()
            if href:
                cid = next((c for c in reversed(stack) if c), None)
                src = (self.dir / href).read_text()
                a = src.find("<emu-table")
                if cid is not None and a >= 0:
                    i = count.get(cid, 0)
                    count[cid] = i + 1
                    self.tables[(cid, i)] = Want("table", src[a:src.index("</emu-table>", a) + len("</emu-table>")], href, a)
            elif close:
                stack.pop()
            else:
                idm = re.search(r'\bid="([^"]+)"', attrs)
                stack.append(idm.group(1) if idm else None)

    def _blocks(self) -> None:
        """The definition blocks (not the examples, jsgrammar.BLOCK): the text between the tags, and the innermost
        clause with an id of each."""
        for m in jsgrammar.BLOCK.finditer(self.src):
            self.blocks.append(Want("block", m.group(1), "spec.html", m.start(1), (m.start(1), m.end(1))))
        self.block_clauses = clauses_at(self.src, [w.pos for w in self.blocks])


# ---------------------------------------------------------------------------------------------------------------
# The overlay's elements, found by their markup

@dataclass
class El:
    """An element of the overlay: its tag, attributes, content, file and offset; `parts` are what the data holds
    of it, each printed exactly once when the element is accounted for."""
    tag: str
    attrs: dict[str, str]
    body: str
    file: str
    pos: int
    end: int
    parent: "El | None" = None
    parts: dict[str, int] = field(default_factory=dict)

    def at(self) -> str:
        return f"spec/formal/{self.file}:{line_of(SRC[self.file], self.pos)}"

    def name(self) -> str:
        a = self.attrs
        return a.get("id") or a.get("name") or a.get("clause", "") + " " + (a.get("step") or a.get("steps") or a.get("grammar") or a.get("rule") or "")


SRC: dict[str, str] = {}


class Generator:
    """What the generator holds of the notation besides the text and the overlay (crates/spec-gen): its own
    primitives' documentation (residue.rs `PRIMS`: name, signature, meaning) and the phrases it gives a meaning
    (conv.rs `BUILTIN_MEANINGS`, and the two forms its parser builds, `strcat-colon` and `assoc-table`)."""

    def __init__(self) -> None:
        src = ROOT / "crates/spec-gen/src"
        rs = (src / "residue.rs").read_text()
        body = rs[rs.index("pub const PRIMS"):]
        body = body[:body.index("\n];")]
        lit = r'"((?:[^"\\]|\\.)*)"'
        unq = lambda s: re.sub(r"\\(.)", r"\1", s)
        self.prims = {unq(n): (unq(s), unq(m)) for n, s, m in re.findall(rf"Prim \{{ name: {lit}, sig: {lit}, meaning: {lit}", body)}
        cv = (src / "conv.rs").read_text()
        body = cv[cv.index("const BUILTIN_MEANINGS"):]
        body = body[:body.index("\n];")]
        self.meanings = set(re.findall(r'^\s*\(\s*"(\w+)",\s*"([^"]+)",', body, re.M)) | {("P", "strcat-colon"), ("P", "assoc-table")}
        self.builtin_meanings = len(self.meanings) - 2


GENERATOR: Generator

# the overlay's elements that are not data, and why
NOT_DATA = {
    "emu-note": "informative: why a reading, an erratum or a phrase says what it says",
    "emu-host-law": "the host's dispositions of the requirements of spec.html's prose, read by the generator's "
                    "requirement check; the laws themselves are lean/Ecma/Host, each quoting its sentence (law_quotes.py)",
    "emu-permanent": "the Asserts that stay as sentences, read by the generator's Assert and residue checks "
                     "(spec/formal/permanent-sentences.txt, assert-sites.txt)",
    "emu-fields": "the record fields' types, read by the generator's type check (spec/formal/type-findings.txt)",
    "emu-guard": "the type check's guards: an operation's test of a sort (spec/formal/type-findings.txt)",
    "prose": "the overlay's sections, headings and paragraphs: what a file or an element is about, and the "
             "prose readings that hand-written lean/Ecma states (formal-early-errors-cover-rules-first)",
}
# the overlay's elements the data holds without a printer here, and why
UNPRINTED = {
    "emu-steps-name": "the name of a clause's operation (Decls.ops)",
    "emu-result-type": "an operation's result type (its header's)",
    "emu-orphan-row": "an equation row with no production (its SdoRow's empty prods)",
}


def elements(file: str, text: str) -> list[El]:
    """Every element of an overlay file, with its parent."""
    out: list[El] = []
    stack: list[tuple[El, int]] = []
    for m in re.finditer(r"<(/?)([a-zA-Z][\w-]*)\b([^>]*)>", text):
        close, tag, attrs = m.groups()
        if tag in ("br", "img", "meta", "link", "hr"):
            continue
        if close:
            while stack and stack[-1][0].tag != tag:
                stack.pop()
            if stack:
                e, a = stack.pop()
                e.body = text[a:m.start()]
                e.end = m.end()
            continue
        a = dict(re.findall(r'([\w-]+)="([^"]*)"', attrs))
        for w in re.sub(r'[\w-]+="[^"]*"', "", attrs).split():
            a.setdefault(w, "")
        e = El(tag, a, "", file, m.start(), m.end(), stack[-1][0] if stack else None)
        out.append(e)
        stack.append((e, m.end()))
    return out


def unique(check: "Check", els: list[El], key, what: str) -> dict:
    """The elements by `key`; a second element of one key fails (an element duplicated)."""
    out: dict = {}
    for e in els:
        k = key(e)
        if k in out:
            check.fail(f"FAIL {e.tag} {e.name()} ({e.at()}): a second {what} of {k if isinstance(k, str) else ' '.join(k)}, "
                       f"after {out[k].at()}")
            continue
        out[k] = e
    return out


def child(e: El, els: list[El], tag: str) -> list[El]:
    return [x for x in els if x.parent is e and x.tag == tag]


def shifted(body: str, col: int) -> list[str]:
    """The step lines of an emu-alg body, its first step's column moved to `col`."""
    lines = body.split("\n")[1:-1]
    base = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    return [" " * col + l[base:] if l.strip() else l for l in lines]


def steps0(body: str) -> str:
    """An emu-alg body's steps from column 0, as a reading's steps are printed."""
    return "\n".join(shifted(body, 0))


def squash(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


class Overlay:
    def __init__(self) -> None:
        self.files = sorted(OVERLAY.glob("*.emu"))
        self.els: list[El] = []
        for f in self.files:
            SRC[f.name] = f.read_text()
            self.els += elements(f.name, SRC[f.name])

    def by(self, tag: str) -> list[El]:
        return [e for e in self.els if e.tag == tag]


# ---------------------------------------------------------------------------------------------------------------
# The check

class Check:
    def __init__(self, html: Html, ov: Overlay, items: list[Item]):
        self.html, self.ov, self.items = html, ov, items
        self.problems: list[str] = []
        self.counts: dict[str, Counter] = defaultdict(Counter)
        # spec.html's characters by class: printed items' spans
        self.spans: dict[str, list[tuple[int, int]]] = defaultdict(list)
        self.by_kind: dict[str, list[Item]] = defaultdict(list)
        for it in items:
            self.by_kind[it.kind].append(it)

    def fail(self, msg: str) -> None:
        self.problems.append(msg)

    def differs(self, what: str, want: Want, got: str, where: str | None = None) -> None:
        k, a, b = first_diff(want.text, got)
        if where is None:
            src = self.html.src if want.file == "spec.html" else (SRC.get(want.file.removeprefix("spec/formal/")) or "")
            where = f"{want.file}:{line_of(src, want.pos) + k}" if src else want.file
        self.fail(f"FAIL {what} differs at {where} (line {k + 1} of its text):\n  text:  {a}\n  print: {b}")

    # -- spec.html's five classes, and the overlay's algorithms ------------------------------------------------

    def algorithms(self) -> None:
        html, ov = self.html, self.ov
        want: dict[tuple[str, int], Want] = dict(html.algs)
        overlay: dict[tuple[str, int], tuple[Want, El]] = {}
        # the overlay's algorithms: a phrase's steps, an operation's, a sort's test, a row an SDO lacks
        for e in ov.els:
            alg = None
            if e.tag == "emu-phrase":
                key = e.attrs.get("id")
                alg = child(e, ov.els, "emu-alg")
            elif e.tag == "emu-clause" and e.attrs.get("type") in ("abstract operation", "built-in function"):
                key = e.attrs.get("id")
                alg = child(e, ov.els, "emu-alg")
            elif e.tag == "emu-sort":
                key = "sort-" + e.attrs.get("name", "").replace(" ", "-")
                alg = child(e, ov.els, "emu-alg")
            elif e.tag == "emu-reading" and "grammar" in e.attrs and "rule" not in e.attrs:
                key = e.attrs.get("id")
                alg = [a for a in child(e, ov.els, "emu-alg") if a.attrs.get("reading") in (None, "test262 proposed")]
            if alg:
                a = alg[0]
                if (key, 0) in overlay:
                    self.fail(f"FAIL {e.tag} {key} ({e.at()}): a second algorithm of that id, after {overlay[(key, 0)][1].at()}")
                    continue
                overlay[(key, 0)] = (Want("alg", a.body, f"spec/formal/{a.file}", a.pos + len(SRC[a.file][a.pos:].split(">", 1)[0]) + 1), e)
                e.parts["steps"] = 0
        # an emu-step-patch: its steps before the patched algorithm's own (and an algorithm it nests below them)
        patched: dict[tuple[str, int], El] = {}
        for e in ov.by("emu-step-patch"):
            a = e.attrs
            key = (a["clause"], int(a["alg"]))
            old = want.get(key)
            if old is None or sha(old.text) != a["hash"]:
                self.fail(f"FAIL {e.at()}: emu-step-patch on {key[0]} {key[1]}: spec.html has no algorithm there with its hash")
                continue
            body = child(e, ov.els, "emu-alg")[0].body
            col = len(old.text.split("\n")[1]) - len(old.text.split("\n")[1].lstrip())
            lines = shifted(body, col)
            if "nest" in a:
                c, k = a["nest"].split(" ")
                last = next(l for l in reversed(lines) if re.match(r" *1\. ", l))
                lines += shifted(want[(c, int(k))].text, len(last) - len(last.lstrip()) + 2)
            want[key] = Want("alg", "\n" + "\n".join(lines) + "\n" + old.text[1:], "spec.html", old.pos, old.span)
            patched[key] = e
            e.parts["steps"] = 0
        self.alg_text = want
        seen: dict[tuple[str, int], int] = Counter()
        templates: set[tuple[str, int]] = set()
        for it in self.by_kind["alg"] + self.by_kind["row"]:
            cid, idx = it.args[0], int(it.args[1])
            key = (cid, idx)
            seen[key] += 1
            if seen[key] == 2:
                self.fail(f"FAIL {it.where()} printed twice")
            if key in overlay:
                w, e = overlay[key]
                e.parts["steps"] += 1
                if w.text != it.text:
                    self.differs(it.where(), w, it.text)
                self.counts["overlay algorithms"]["printed"] += 1
                continue
            if "/" in cid and key not in want:
                inst = html.instance(cid, idx)
                if inst is not None:
                    want[key] = inst
                    templates.add((cid.partition("/")[0], idx))
            w = want.get(key)
            if w is None:
                self.fail(f"FAIL {it.where()}: neither spec.html nor spec/formal has such an algorithm")
                continue
            if w.text != it.text:
                self.differs(it.where(), w, it.text)
            if key in patched:
                patched[key].parts["steps"] += 1
            if w.span:
                self.spans["algorithm steps" if w.kind == "alg" else "SDO equations"].append(w.span)
                self.counts["algorithm steps" if w.kind == "alg" else "SDO equations"]["printed"] += 1
            else:
                self.counts["algorithm steps"]["instances of a parameterized clause's, printed"] += 1
        for key, w in sorted(html.algs.items()):
            if key not in seen and key not in templates:
                self.fail(f"FAIL {'emu-alg' if w.kind == 'alg' else 'equation'} {key[0]} {key[1]} ({html.at(w.pos)}) not printed")
        for key in templates:
            w = html.algs[key]
            self.spans["algorithm steps"].append(w.span)
            self.counts["algorithm steps"]["parameterized clauses' (printed through their instances)"] += 1
        for key, (w, e) in overlay.items():
            if e.parts["steps"] == 0:
                self.fail(f"FAIL {e.tag} {key[0]} ({e.at()}): its steps are not printed")
        self.counts["algorithm steps"]["in spec.html"] = sum(1 for w in html.algs.values() if w.kind == "alg")
        self.counts["SDO equations"]["in spec.html"] = sum(1 for w in html.algs.values() if w.kind == "row")
        self.counts["algorithm steps"]["of them patched by the overlay (emu-step-patch), printed with the patch's steps first"] = len(patched)
        self.counts["algorithm steps"]["examples (not data)"] = len(html.examples)
        self.counts["overlay algorithms"]["in spec/formal"] = len(overlay)

    def keys(self) -> None:
        """Every SDO row's and early-error row's grammar keys as the data holds them (`@@key CLAUSE IDX K`) are
        the `<emu-grammar>` blocks before its algorithm or its bullet list, verbatim."""
        html = self.html
        got: dict[tuple[str, int], list[str]] = defaultdict(list)
        for it in self.by_kind["key"]:
            got[(it.args[0], int(it.args[1]))].append(it.text)
        rows = {e.attrs["id"]: e for e in self.ov.by("emu-reading") if "grammar" in e.attrs and "id" in e.attrs}
        for key, texts in sorted(got.items()):
            w = html.keys.get(key)
            if key[0] in rows:
                # a row the overlay adds: its key is the reading's `grammar=`
                e = rows[key[0]]
                if texts != [e.attrs["grammar"]]:
                    self.fail(f"FAIL key {key[0]} {key[1]}: {texts} printed, the overlay's grammar= is {e.attrs['grammar']!r} ({e.at()})")
                e.parts["key"] = e.parts.get("key", 0) + 1
                self.counts["grammar keys"]["of the overlay's rows (grammar=)"] += len(texts)
                continue
            if w is None:
                self.fail(f"FAIL key {key[0]} {key[1]}: spec.html has no such row")
                continue
            if [x.text for x in w] != texts:
                if len(w) != len(texts):
                    self.fail(f"FAIL key {key[0]} {key[1]}: {len(texts)} printed, spec.html has {len(w)} ({html.at(w[0].pos) if w else html.at(0)})")
                    continue
                for x, t in zip(w, texts):
                    if x.text != t:
                        self.differs(f"key {key[0]} {key[1]}", x, t)
            for x in w:
                self.spans["grammar keys"].append(x.span)
            self.counts["grammar keys"]["printed"] += len(texts)
        # every SDO row with an emu-alg and every early-error rule has its keys printed
        for it in self.by_kind["row"]:
            key = (it.args[0], int(it.args[1]))
            if key in html.keys and html.algs.get(key) is not None and html.algs[key].kind == "alg" and key not in got:
                self.fail(f"FAIL row {key[0]} {key[1]}: its grammar key ({html.at(html.keys[key][0].pos)}) is not printed")
        for key in html.early:
            if key not in got and html.keys.get(key):
                self.fail(f"FAIL early-error rule {key[0]} {key[1]}: its grammar key ({html.at(html.keys[key][0].pos)}) is not printed")

    def early(self) -> None:
        html = self.html
        seen: Counter = Counter()
        for it in self.by_kind["early"]:
            cid, idx = it.args[0], int(it.args[1])
            key = (cid, idx)
            seen[key] += 1
            if seen[key] == 2:
                self.fail(f"FAIL early-error row {cid} {idx} printed twice")
            if it.sdo != "Early Errors":
                self.fail(f"FAIL early-error row {cid} {idx}: of the SDO {it.sdo!r}, not Early Errors")
            if idx >= TWIN_IDX:
                # a bullet's twin for further productions: printed by its readings, so only that bullet is checked
                if (cid, idx - TWIN_IDX) not in html.early:
                    self.fail(f"FAIL early-error twin row {cid} {idx}: spec.html has no bullet {idx - TWIN_IDX}")
                self.counts["early-error rules"]["twins (a reading's copy for further productions)"] += 1
                continue
            w = html.early.get(key)
            if w is None:
                self.fail(f"FAIL early-error row {cid} {idx}: spec.html has no such bullet")
                continue
            if w.text != it.text:
                self.differs(f"early-error row {cid} {idx}", w, it.text)
            self.spans["early-error rules"].append(w.span)
            self.counts["early-error rules"]["printed"] += 1
        for key, w in sorted(html.early.items()):
            if key not in seen:
                self.fail(f"FAIL early-error bullet {key[0]} {key[1]} ({html.at(w.pos)}) not printed")
        self.counts["early-error rules"]["in spec.html"] = len(html.early)

    def tables(self) -> None:
        html = self.html
        seen: Counter = Counter()
        for it in self.by_kind["table"]:
            key = (it.args[0], int(it.args[1]))
            seen[key] += 1
            if seen[key] == 2:
                self.fail(f"FAIL table {key[0]} {key[1]} printed twice")
            w = html.tables.get(key)
            if w is None:
                self.fail(f"FAIL table {key[0]} {key[1]}: spec.html has no such emu-table")
                continue
            if w.text != it.text:
                if w.file == "spec.html":
                    self.differs(f"table {key[0]} {key[1]}", w, it.text)
                else:
                    k, a, b = first_diff(w.text, it.text)
                    self.fail(f"FAIL table {key[0]} {key[1]} differs at {w.file} (line {k + 1} of its text):\n  text:  {a}\n  print: {b}")
            if w.span:
                self.spans["tables"].append(w.span)
            else:
                self.counts["tables"]["of them imported (outside spec.html)"] += 1
            self.counts["tables"]["printed"] += 1
        for key, w in sorted(html.tables.items()):
            if key not in seen:
                self.fail(f"FAIL emu-table {key[0]} {key[1]} ({w.file}:{line_of(html.src, w.pos) if w.file == 'spec.html' else '?'}) not printed")
        self.counts["tables"]["in spec.html"] = len(html.tables)

    def blocks(self) -> None:
        """The grammar's definition blocks: spec.html's, then json.emu's, each printed once, in order."""
        html, ov = self.html, self.ov
        want = [(w, "spec.html") for w in html.blocks]
        json_blocks = [e for e in ov.els if e.file == "json.emu" and e.tag == "emu-grammar" and e.attrs.get("type") == "definition"]
        for e in json_blocks:
            want.append((Want("block", e.body, "spec/formal/json.emu", e.pos + len(SRC[e.file][e.pos:].split(">", 1)[0]) + 1), "json.emu"))
            e.parts["block"] = 0
        got = self.by_kind["block"]
        # a block is named by its clause and the line of its opening tag
        heads = []
        for (w, f), c in zip(want, html.block_clauses + ["formal-json"] * len(json_blocks)):
            src = html.src if f == "spec.html" else SRC["json.emu"]
            heads.append([c, str(line_of(src, src.rfind("<emu-grammar", 0, w.pos)))])
        if [it.args for it in got] != heads:
            k = next((i for i, (a, b) in enumerate(zip([it.args for it in got], heads)) if a != b), min(len(got), len(want)))
            self.fail(f"FAIL the data's {len(got)} grammar blocks are not spec.html's and json.emu's {len(want)} in order: "
                      f"the {k}th is {' '.join(got[k].args) if k < len(got) else 'none'}, the text's {' '.join(heads[k]) if k < len(heads) else 'none'}")
        for it, (w, f) in zip(got, want):
            if w.text != it.text:
                self.differs(it.where(), w, it.text)
            if f == "spec.html":
                self.spans["grammar productions"].append(w.span)
                self.counts["grammar productions"]["printed"] += 1
            else:
                self.counts["grammar productions"]["printed, of json.emu"] += 1
        for e in json_blocks:
            e.parts["block"] = 1
        self.counts["grammar productions"]["in spec.html"] = len(html.blocks)

    # -- the overlay's readings ------------------------------------------------------------------------------

    def step_readings(self) -> None:
        """A step with readings (`@@reading CLAUSE IDX ID`): its line, as spec.html has it, is the step the overlay's
        emu-reading names by the SHA-256 of its text; each reading's steps are the overlay's emu-alg."""
        ov = self.ov
        readings = [e for e in ov.by("emu-reading") if "step" in e.attrs or "steps" in e.attrs]
        # each step a reading names, by its clause and its hash: the first is the one it reads, the others
        # (`steps=`, `hashes=`) later steps it also replaces, which have no steps under its readings
        by_hash: dict[tuple[str, str], list[tuple[El, int]]] = defaultdict(list)
        for e in readings:
            hs = (e.attrs.get("hash") or e.attrs.get("hashes", "")).split(" ")
            for k, h in enumerate(hs):
                by_hash[(e.attrs["clause"], h)].append((e, k))
            e.parts["reading"] = 0
            e.covered = [0] * len(hs)
        anchors = set()
        for it in self.by_kind["reading"]:
            cid, idx, rid = it.args[0], int(it.args[1]), it.args[2]
            h = sha(it.text)
            cands = by_hash.get((cid, h)) or by_hash.get((cid.partition("/")[0], h)) or []
            if rid.startswith("erratum-"):
                cands = [(e, k) for e, k in cands if e.parent is not None and e.parent.tag == "emu-erratum" and e.parent.attrs.get("id") == rid]
            else:
                cands = [(e, k) for e, k in cands if e.parent is None or e.parent.tag != "emu-erratum"]
                cands = [(e, k) for e, k in cands if (e.attrs.get("id") or f"definition-{e.attrs['clause']}-{e.attrs['steps'].split(' ')[0]}") == rid]
            if len(cands) != 1:
                self.fail(f"FAIL {it.where()}: {'no' if not cands else len(cands)} emu-reading of spec/formal names the step {it.text[:70]!r} in {cid} by its hash")
                continue
            e, k = cands[0]
            e.covered[k] += 1
            if k == 0:
                e.parts["reading"] += 1
            anchors.add((cid.partition("/")[0], h))
            # the algorithm as the data has it: patched by an emu-step-patch, whose steps then come first
            w = self.alg_text.get((cid, idx)) or (self.html.instance(cid, idx) if "/" in cid else None)
            path = (e.attrs.get("step") or e.attrs["steps"]).split(" ")[k]
            if w is None or (path, it.text) not in step_paths(w.text):
                self.fail(f"FAIL {it.where()}: spec.html's algorithm {cid} {idx} has no step {path} {it.text[:70]!r}")
            want = []
            for a in child(e, ov.els, "emu-alg"):
                for r in a.attrs.get("reading", "").split(" "):
                    want.append((r, steps0(a.body) if k == 0 else ""))
            if k > 0:
                self.counts["step readings"]["later steps a reading also replaces (no steps of their own)"] += 1
            if [n for n, _ in want] != [n for n, _ in it.alts]:
                self.fail(f"FAIL {it.where()} ({e.at()}): readings {[n for n, _ in it.alts]} printed, the overlay has {[n for n, _ in want]}")
                continue
            for (n, t), (_, p) in zip(want, it.alts):
                if t != p:
                    k, a, b = first_diff(t, p)
                    self.fail(f"FAIL {it.where()}: its {n} reading differs at {e.at()} (line {k + 1} of its steps):\n  text:  {a}\n  print: {b}")
            if k == 0:
                self.counts["step readings"]["printed"] += 1
        for e in readings:
            n = e.parts["reading"]
            if n == 0:
                self.fail(f"FAIL emu-reading {e.name()} ({e.at()}) not printed")
            hs = (e.attrs.get("hash") or e.attrs.get("hashes", "")).split(" ")
            paths = (e.attrs.get("step") or e.attrs.get("steps", "")).split(" ")
            for k, h in enumerate(hs[1:], 1):
                if e.covered[k] or (e.attrs["clause"], h) in anchors:
                    # printed, under this reading or with an erratum of its own
                    continue
                # a step inside the one it reads, or its `Else` arm, is a part of that step
                steps = [s for (c, _), w in self.alg_text.items() if w.kind == "alg" and c == e.attrs["clause"]
                         for s in step_paths(w.text) if s[0] == paths[k] and sha(s[1]) == h]
                if steps and (paths[k].startswith(paths[0] + ".") or re.match(r"Else\b", steps[0][1])):
                    self.counts["step readings"]["later steps a reading also replaces, inside the step it reads or its Else arm"] += 1
                    continue
                self.fail(f"FAIL emu-reading {e.name()} ({e.at()}): the step {paths[k]} it also replaces is not printed")
        self.counts["step readings"]["in spec/formal"] = len(readings)
        inst = sum(e.parts["reading"] - 1 for e in readings if e.parts["reading"] > 1)
        if inst:
            self.counts["step readings"]["printed again, for another instance of a template clause"] = inst
        for e in readings:
            if e.parts["reading"] > 1 and not any(it.args[0].startswith(e.attrs["clause"] + "/") for it in self.by_kind["reading"]):
                self.fail(f"FAIL emu-reading {e.name()} ({e.at()}) printed {e.parts['reading']} times")

    def rule_readings(self) -> None:
        """An early-error rule with readings (`@@rule-reading CLAUSE IDX ID`): the overlay's emu-reading with `rule=`
        of that erratum (or definition reading), whose `hash=` is the SHA-256 of the rule's bullet in spec.html
        (a twin, IDX + 1000, is its copy for the productions `also=` names); its readings' sentences are the
        overlay's `<p reading=…>`, each as written."""
        ov = self.ov
        readings = [e for e in ov.by("emu-reading") if "rule" in e.attrs]
        for e in readings:
            e.parts["reading"] = 0
            e.twins = 0

        def rid_of(e: El) -> str:
            if e.parent is not None and e.parent.tag == "emu-erratum":
                return e.parent.attrs["id"]
            return f"definition-{e.attrs['clause']}-rule-{e.attrs['hash'][:12]}"
        for it in self.by_kind["rule-reading"]:
            cid, idx, rid = it.args[0], int(it.args[1]), it.args[2]
            twin = idx >= TWIN_IDX
            w = self.html.early.get((cid, idx - TWIN_IDX if twin else idx))
            if w is None:
                self.fail(f"FAIL {it.where()}: spec.html has no such early-error rule")
                continue
            cands = [e for e in readings if rid_of(e) == rid and e.attrs.get("clause") == cid and e.attrs.get("hash") == sha(w.text)]
            if len(cands) != 1:
                self.fail(f"FAIL {it.where()}: {len(cands)} emu-reading of spec/formal names the rule {cid} {idx} ({self.html.at(w.pos)}) by its hash")
                continue
            e = cands[0]
            if twin:
                e.twins += 1
                if "also" not in e.attrs:
                    self.fail(f"FAIL {it.where()}: a twin of a reading without also= ({e.at()})")
                self.counts["early-error rule readings"]["printed again, for the productions also= names"] += 1
            else:
                e.parts["reading"] += 1
                self.counts["early-error rule readings"]["printed"] += 1
            want = [(p.attrs["reading"], p.body) for p in child(e, ov.els, "p") if "reading" in p.attrs]
            if [n for n, _ in want] != [n for n, _ in it.alts]:
                self.fail(f"FAIL {it.where()} ({e.at()}): readings {[n for n, _ in it.alts]} printed, the overlay has {[n for n, _ in want]}")
                continue
            for (n, x), (_, y) in zip(want, it.alts):
                if x != y:
                    k, a, b = first_diff(x, y)
                    self.fail(f"FAIL {it.where()}: its {n} reading differs at {e.at()}:\n  text:  {a}\n  print: {b}")
        for e in readings:
            if e.parts["reading"] != 1 or e.twins != (1 if "also" in e.attrs else 0):
                self.fail(f"FAIL emu-reading {e.name()} ({e.at()}) printed {e.parts['reading']} times, {e.twins} as a twin")
        self.counts["early-error rule readings"]["in spec/formal"] = len(readings)

    def grammar_readings(self) -> None:
        """A grammar rule's reading (`@@grammar-reading CLAUSE LINE RULE HASH ID`): the overlay's emu-rule-reading,
        its definition block the printed one, its hash that of the rule's definition in spec.html."""
        ov = self.ov
        els = ov.by("emu-rule-reading")
        for e in els:
            e.parts["reading"] = 0
        for it in self.by_kind["grammar-reading"]:
            cid, line, rule, h, rid = it.args
            cands = [e for e in els if e.attrs.get("clause") == cid and e.attrs.get("rule") == rule and e.attrs.get("hash") == h]
            if len(cands) != 1:
                self.fail(f"FAIL {it.where()}: {len(cands)} emu-rule-reading for {rule} in {cid} with its hash")
                continue
            e = cands[0]
            e.parts["reading"] += 1
            g = child(e, ov.els, "emu-grammar")[0]
            if g.body != it.text:
                k, a, b = first_diff(g.body, it.text)
                self.fail(f"FAIL {it.where()} differs at {g.at()} (line {k + 1} of its text):\n  text:  {a}\n  print: {b}")
            if line_of(SRC[g.file], g.pos) != int(line):
                self.fail(f"FAIL {it.where()}: the overlay's block is at line {line_of(SRC[g.file], g.pos)}")
            # its hash: the pinned definition's text in its clause
            defs = []
            for w, c in zip(self.html.blocks, self.html.block_clauses):
                if c != cid:
                    continue
                lines = jsgrammar.grammar_lines(w.text)
                for k, l in enumerate(lines):
                    if re.match(rf"{re.escape(rule)}\b", l):
                        end = next((j for j in range(k + 1, len(lines)) if not lines[j].startswith(" ")), len(lines))
                        defs.append("\n".join(lines[k:end]))
            if len(defs) != 1 or sha(defs[0]) != h:
                self.fail(f"FAIL {it.where()}: its hash is not that of the pinned {rule} in {cid}")
            erratum = e.parent.attrs.get("id") if e.parent is not None and e.parent.tag == "emu-erratum" else "-"
            if erratum != rid:
                self.fail(f"FAIL {it.where()}: of {rid}, but the overlay's is of {erratum}")
            self.counts["grammar rule readings"]["printed"] += 1
        for e in els:
            if e.parts["reading"] != 1:
                self.fail(f"FAIL emu-rule-reading {e.name()} ({e.at()}) printed {e.parts['reading']} times")
        self.counts["grammar rule readings"]["in spec/formal"] = len(els)

    # -- the overlay's declarations ----------------------------------------------------------------------------

    def params(self) -> None:
        """An overlay algorithm's parameters (`@@params ID`): a phrase's `<emu-params>`, an operation's heading's,
        a sort test's `_v_: anything` (its one parameter, the value tested)."""
        ov = self.ov
        want: dict[str, tuple[str, El]] = {}
        for e in ov.els:
            if e.tag == "emu-phrase":
                p = child(e, ov.els, "emu-params")
                if child(e, ov.els, "emu-alg"):
                    want[e.attrs["id"]] = (p[0].body if p else "", e)
            elif e.tag == "emu-clause" and e.attrs.get("type") in ("abstract operation", "built-in function"):
                h1 = child(e, ov.els, "h1")[0].body
                want[e.attrs["id"]] = (header_params(h1), e)
            elif e.tag == "emu-sort" and child(e, ov.els, "emu-alg"):
                want["sort-" + e.attrs["name"].replace(" ", "-")] = ("_v_: anything", e)
        seen: Counter = Counter()
        for it in self.by_kind["params"]:
            cid = it.args[0]
            seen[cid] += 1
            if cid not in want:
                self.fail(f"FAIL {it.where()}: spec/formal has no such algorithm")
                continue
            t, e = want[cid]
            # the generator's own parameters of a rule's phrase: which alternative of its choices, a repeated part
            got = [x for x in it.text.split(", ") if not re.fullmatch(r"_(choice|repeat) \d+_(: )?", x)]
            if len(got) < len(it.text.split(", ")):
                self.counts["overlay parameters"]["the generator's own (a rule's choice or repetition)"] += len(it.text.split(", ")) - len(got)
            if squash(t) != squash(", ".join(got)):
                self.fail(f"FAIL {it.where()} differs at {e.at()}:\n  text:  {squash(t)}\n  print: {squash(', '.join(got))}")
            e.parts["params"] = e.parts.get("params", 0) + 1
            self.counts["overlay parameters"]["printed"] += 1
        for cid, (t, e) in want.items():
            if seen[cid] != 1:
                self.fail(f"FAIL the parameters of {cid} ({e.at()}) printed {seen[cid]} times")

    def prims(self) -> None:
        """A primitive (`@@prim NAME`): its `<emu-signature>`, then its first paragraph (white space squashed), the
        meaning the data documents it by."""
        ov = self.ov
        els = unique(self, ov.by("emu-primitive"), lambda e: e.attrs.get("name"), "emu-primitive")
        for it in self.by_kind["prim"]:
            name = " ".join(it.args)
            e = els.get(name)
            if e is None:
                # the generator's own primitive: its documentation is the generator's table's
                if GENERATOR.prims.get(name) != tuple(it.text.split("\n", 1)):
                    self.fail(f"FAIL {it.where()}: no emu-primitive of spec/formal, and not as the generator documents it "
                              f"(crates/spec-gen/src/residue.rs PRIMS): {it.text[:80]!r}")
                self.counts["primitives"]["the generator's own (residue.rs PRIMS), as it documents them"] += 1
                continue
            sig = child(e, ov.els, "emu-signature")[0].body
            ps = child(e, ov.els, "p")
            want = sig + "\n" + (squash(ps[0].body) if ps else "")
            if want != it.text:
                k, a, b = first_diff(want, it.text)
                self.fail(f"FAIL {it.where()} differs at {e.at()}:\n  text:  {a}\n  print: {b}")
            e.parts["prim"] = e.parts.get("prim", 0) + 1
            self.counts["primitives"]["printed"] += 1
        for e in els.values():
            if e.parts.get("prim", 0) != 1:
                self.fail(f"FAIL emu-primitive {e.attrs.get('name')} ({e.at()}) printed {e.parts.get('prim', 0)} times")
        self.counts["primitives"]["in spec/formal"] = len(els)

    def phrases(self) -> None:
        """A phrase (`@@phrase N CAT`), named by spec/formal/phrase-ids.txt (its category and its `rule=` or id): its
        template, then its meaning (`steps ID` for one with steps, else its `meaning=`, the variables numbered as the
        template's holes and the subject as `subject`). A phrase of the overlay's own has its `<emu-pattern>` as
        its template, the variables numbered in order; one that claims a rule of the generator's notation
        (`rule=`) has that rule's template, and its pattern must be one of the template's spellings (a choice
        `⟨a | b⟩` made, the holes' kinds and the spaces left out)."""
        ov = self.ov
        ids = [tuple(l.split(" ", 1)) for l in (OVERLAY / "phrase-ids.txt").read_text().splitlines()]
        cats = {"step": ("Step",), "expression": ("P",), "condition": ("CA",), "predicate": ("PRED",), "type": ("T", "HT", "HT1")}
        unique(self, ov.by("emu-phrase"), lambda e: e.attrs["id"], "emu-phrase")
        els = unique(self, [e for e in ov.by("emu-phrase") if e.attrs.get("kind") in cats],
                     lambda e: (cats[e.attrs["kind"]][0], e.attrs.get("rule") or e.attrs["id"]), "phrase")
        for (c, n), e in list(els.items()):
            for c2 in cats[e.attrs["kind"]][1:]:
                els[(c2, n)] = e
        for it in self.by_kind["phrase"]:
            n = int(it.args[0])
            key = ids[n] if n < len(ids) else None
            e = els.get(key)
            if e is None:
                tmpl_got, _, meaning_got = it.text.partition("\n")
                if not it.text.strip():
                    self.counts["phrases"]["retired ids (a kept number, no phrase)"] += 1
                elif meaning_got and key not in GENERATOR.meanings:
                    # an overlay phrase always has a meaning: one with no element is the overlay's, dropped
                    self.fail(f"FAIL {it.where()} ({key[0]} {key[1]}): a phrase with the meaning {meaning_got!r}, but no "
                              f"emu-phrase of spec/formal and no built-in meaning of the generator gives it one")
                elif meaning_got:
                    self.counts["phrases"]["the generator's own, with its built-in meaning"] += 1
                else:
                    self.counts["phrases"]["the generator's own, with no meaning (read by the generator's rules)"] += 1
                continue
            e.parts["pattern"] = e.parts.get("pattern", 0) + 1
            pat = squash(child(e, ov.els, "emu-pattern")[0].body)
            holes: list[str] = []

            def hole(m: re.Match) -> str:
                holes.append(m.group(1))
                return f"_{len(holes)}_"

            tmpl = re.sub(r"(?<![\w])_([A-Za-z][A-Za-z0-9]*)_", hole, pat)
            subject = e.attrs.get("subject", "").strip("_")
            if "meaning" in e.attrs:
                meaning = re.sub(r"(?<![\w])_([A-Za-z][A-Za-z0-9]*)_", lambda m: "subject" if m.group(1) == subject else
                                 f"_{holes.index(m.group(1)) + 1}_" if m.group(1) in holes else m.group(0), e.attrs["meaning"])
            else:
                meaning = "steps " + e.attrs["id"]
            tmpl_got, _, meaning_got = it.text.partition("\n")
            if "rule" in e.attrs:
                shape = lambda s: re.sub(r"\s+", "", re.sub(r"_\d+(?::\w+)?_", "_", s))
                if shape(tmpl) not in {shape(x) for x in spellings(tmpl_got)}:
                    self.fail(f"FAIL {it.where()} ({e.attrs['id']}): its pattern is no spelling of its rule's template, at {e.at()}:\n"
                              f"  text:  {pat}\n  print: {tmpl_got}")
                self.counts["phrases"]["printed, the template of a rule of the generator's notation"] += 1
            else:
                if tmpl != tmpl_got:
                    self.fail(f"FAIL {it.where()} ({e.attrs['id']}): its pattern differs at {e.at()}:\n  text:  {tmpl}\n  print: {tmpl_got}")
                self.counts["phrases"]["printed, the overlay's pattern"] += 1
            if meaning != meaning_got:
                self.fail(f"FAIL {it.where()} ({e.attrs['id']}): its meaning differs at {e.at()}:\n  text:  {meaning}\n  print: {meaning_got}")
        for e in ov.by("emu-phrase"):
            if e.parts.get("pattern", 0) != 1:
                self.fail(f"FAIL emu-phrase {e.attrs['id']} ({e.at()}) printed {e.parts.get('pattern', 0)} times")
        self.counts["phrases"]["in spec/formal"] = len(ov.by("emu-phrase"))
        self.counts["phrases"]["the generator's built-in meanings (conv.rs BUILTIN_MEANINGS)"] = GENERATOR.builtin_meanings

    def sorts(self) -> None:
        """A sort (`@@sort NAME`): `record` or `sort`, its supersorts, its test (`steps sort-NAME`, the operation
        `alg=` names, or `test=`'s primitive), its context phrase: the overlay's `<emu-sort>` attributes."""
        ov = self.ov
        els = unique(self, ov.by("emu-sort"), lambda e: e.attrs["name"], "emu-sort")
        for it in self.by_kind["sort"]:
            name = " ".join(it.args)
            e = els.get(name)
            if e is None:
                # a name of the text the generator declares a sort of, with no definition
                if it.text != "sort":
                    self.fail(f"FAIL {it.where()}: a sort with a definition ({it.text}), but no emu-sort of spec/formal")
                self.counts["sorts"]["the text's, with no definition"] += 1
                continue
            a = e.attrs
            want = "record" if "record" in a else "sort"
            if a.get("super"):
                want += " super: " + ", ".join(x.strip() for x in a["super"].split(","))
            if child(e, ov.els, "emu-alg"):
                want += " test: steps sort-" + name.replace(" ", "-")
            elif "alg" in a:
                want += " test: steps " + a["alg"]
            elif "test" in a:
                want += " test: " + a["test"].replace("_v_", "subject")
            if "context" in a:
                want += " context: steps " + a["context"]
            got = it.text
            # an operation's test names the operation after its clause id: `steps CLAUSE (Name)`
            got_cmp = re.sub(r" test: steps (\S+) \(([^)]*)\)", lambda m: f" test: steps {m.group(2)}", got)
            if want != got_cmp:
                self.fail(f"FAIL {it.where()} differs at {e.at()}:\n  text:  {want}\n  print: {got}")
            e.parts["sort"] = e.parts.get("sort", 0) + 1
            self.counts["sorts"]["printed"] += 1
        for e in els.values():
            if e.parts.get("sort", 0) != 1:
                self.fail(f"FAIL emu-sort {e.attrs['name']} ({e.at()}) printed {e.parts.get('sort', 0)} times")
        self.counts["sorts"]["in spec/formal"] = len(els)

    def errata(self) -> None:
        """An erratum (`@@erratum ID NAME READING`): the overlay's `<emu-erratum>` of that id, its name, and the
        reading the model applies by default: its resolution (`pending` read as `proposed`)."""
        ov = self.ov
        els = unique(self, ov.by("emu-erratum"), lambda e: e.attrs["id"], "emu-erratum")
        for it in self.by_kind["erratum"]:
            eid, name, reading = it.args
            e = els.get(eid)
            if e is None:
                if eid.startswith("definition-"):
                    self.counts["errata"]["definition readings (no erratum)"] += 1
                    continue
                self.fail(f"FAIL {it.where()}: spec/formal has no such emu-erratum")
                continue
            r = e.attrs.get("resolution")
            want = f"{e.attrs.get('name')} {'proposed' if r == 'pending' else r}"
            if want != f"{name} {reading}":
                self.fail(f"FAIL {it.where()} differs at {e.at()}:\n  text:  {want}\n  print: {name} {reading}")
            e.parts["erratum"] = e.parts.get("erratum", 0) + 1
            self.counts["errata"]["printed"] += 1
        for e in els.values():
            if e.parts.get("erratum", 0) != 1:
                self.fail(f"FAIL emu-erratum {e.attrs['id']} ({e.at()}) printed {e.parts.get('erratum', 0)} times")
        self.counts["errata"]["in spec/formal"] = len(els)

    # -- the overlay's elements, each accounted for -----------------------------------------------------------

    def overlay_classes(self) -> dict[str, dict]:
        """Every element of the overlay in one class: printed (what the data holds of it printed, each part once,
        which the checks above require), a part of a printed element, data without a printer, not data (and why),
        or inline markup of a text. An element of no class fails."""
        ov = self.ov
        out: dict[str, dict] = {}

        def add(cls: str, e: El, status: str, why: str = "") -> None:
            c = out.setdefault(cls, {"status": status, "elements": 0, "why": why})
            c["elements"] += 1

        def is_op(e: El | None) -> bool:
            return e is not None and e.tag == "emu-clause" and e.attrs.get("type") in ("abstract operation", "built-in function")
        printed = {"emu-phrase": "phrases", "emu-primitive": "primitives", "emu-sort": "sorts", "emu-erratum": "errata",
                   "emu-rule-reading": "grammar rule readings", "emu-step-patch": "step patches"}
        parts = {"emu-pattern", "emu-params", "emu-alg", "emu-signature", "emu-grammar"}
        inline = {"emu-xref", "emu-grammar", "code", "sup", "sub", "a", "emu-not-ref", "emu-meta", "var", "i", "b", "em",
                  "strong", "span", "ins", "del"}
        for e in ov.els:
            par = e.parent
            if e.tag in printed:
                add(printed[e.tag], e, "printed")
            elif is_op(e):
                add("operations", e, "printed")
            elif e.tag == "emu-reading":
                add("early-error rule readings" if "rule" in e.attrs else "row readings" if "grammar" in e.attrs else "step readings", e, "printed")
            elif e.tag == "emu-grammar" and e.file == "json.emu" and par is not None and par.tag == "emu-clause":
                add("grammar productions (json.emu)", e, "printed")
            elif e.tag in parts and par is not None and (par.tag in printed or par.tag == "emu-reading" or is_op(par)):
                add("parts of printed elements", e, "printed")
            elif e.tag == "p" and par is not None and par.tag == "emu-reading" and "reading" in e.attrs:
                add("parts of printed elements", e, "printed")
            elif e.tag == "p" and par is not None and par.tag == "emu-primitive" and child(par, ov.els, "p")[0] is e:
                add("parts of printed elements", e, "printed")
            elif e.tag in ("h1", "dl", "dt", "dd") and (is_op(par) or (par is not None and is_op(par.parent))):
                add("operation headers", e, "data without a printer",
                    "an overlay operation's heading and description: its parameters are printed (@@params), its "
                    "result type and description are header data no printer reads")
            elif e.tag in UNPRINTED:
                add(e.tag, e, "data without a printer", UNPRINTED[e.tag])
            elif e.tag in NOT_DATA:
                add(e.tag, e, "not data", NOT_DATA[e.tag])
            elif e.tag == "emu-clause" or (e.tag in ("h1", "p", "ul", "li", "ol") and par is not None):
                add("prose", e, "not data", NOT_DATA["prose"])
            elif e.tag in inline and par is not None:
                add("inline markup", e, "within a text", "markup inside the text of another element")
            else:
                self.fail(f"FAIL {e.tag} at {e.at()}: an element of the overlay in no class")
        return out

    # -- spec.html's characters --------------------------------------------------------------------------------

    def coverage(self) -> dict[str, dict]:
        html = self.html
        src = html.src
        cls = bytearray(len(src))
        names = ["other prose and markup", "algorithm steps", "SDO equations", "early-error rules", "tables",
                 "grammar productions", "grammar keys", "headers", "notes", "examples", "emu-eqn", "figures"]
        status = {"algorithm steps": "printed from trees", "SDO equations": "printed from trees", "early-error rules":
                  "printed from trees", "tables": "printed from trees", "grammar productions": "printed from trees",
                  "grammar keys": "held verbatim", "headers": "data without a printer", "notes": "not data",
                  "examples": "not data", "emu-eqn": "not data", "figures": "not data", "other prose and markup": "not data"}
        idx = {n: i for i, n in enumerate(names)}

        def mark(spans, n, over=False) -> None:
            k = idx[n]
            for a, b in spans:
                if over:
                    cls[a:b] = bytes([k]) * (b - a)
                else:
                    for i in range(a, b):
                        if cls[i] == 0:
                            cls[i] = k
        # not data first, then what is data over it (a note inside an algorithm is the algorithm's)
        for tag, n in (("emu-note", "notes"), ("emu-eqn", "emu-eqn"), ("figure", "figures"), ("emu-figure", "figures")):
            mark(spans_of(src, tag), n, True)
        mark(html.examples, "examples", True)
        mark([(m.start(), m.end()) for m in re.finditer(r'<emu-grammar type="definition" example>.*?</emu-grammar>', src, re.S)], "examples", True)
        # the headers of the clauses whose algorithms are data: the heading and the header list
        hdr = []
        alg_clauses = {k[0] for k in html.algs} | {k[0].partition("/")[0] for k in html.algs}
        for m in re.finditer(r'<emu-(?:clause|annex) id="([^"]+)"[^>]*>\s*(<h1>.*?</h1>)(\s*<dl class="header">.*?</dl>)?', src, re.S):
            if m.group(1) in alg_clauses:
                hdr.append((m.start(2), m.end(2)))
                if m.group(3):
                    hdr.append((m.start(3), m.end(3)))
        mark(hdr, "headers", True)
        for n in ("tables", "algorithm steps", "SDO equations", "early-error rules", "grammar productions", "grammar keys"):
            mark(self.spans[n], n, True)
        counts = Counter(cls)
        out = {}
        for n in names:
            out[n] = {"characters": counts.get(idx[n], 0), "status": status[n]}
        return out

    def side_checks(self) -> None:
        """What the machine reads where the printer reads a twin: a hexadecimal numeral's, a code unit's and a code
        point's value (`Numeral.hex n d`, `Expr.codeUnit n d _`, `Expr.codePoint n d _`, as the generated modules
        write them) is the number its written digits `d` denote."""
        names = {"hex": "hexadecimal numerals", "codeUnit": "code units", "codePoint": "code points"}
        for f in sorted((ROOT / "lean/Ecma/Gen").glob("*.lean")):
            src = f.read_text()
            for m in re.finditer(r'\.(hex|codeUnit|codePoint) (\d+) "([0-9A-Fa-f]+)"', src):
                kind, n, d = m.groups()
                if int(d, 16) != int(n):
                    self.fail(f"FAIL {f.relative_to(ROOT)}:{line_of(src, m.start())}: the {names[kind][:-1]} written {d} is "
                              f"{int(d, 16)}, but the data's value is {n}")
                self.counts["values against their written digits"][names[kind]] += 1

    def key_ids(self) -> None:
        """What the machine reads of a grammar key, the production ids (`SdoRow.prods`, `EarlyRow.prods`,
        `Expr.prod`, as the generated modules write them), names the productions its printed twin, the key's text
        (`keys`, `raw`), names: each id's production (spec/formal/prod-ids.txt: its left-hand side, written
        right-hand side and presences) is one a line of the key stands for, and each line of the key has an id.
        A row the overlay's emu-orphan-row names has none."""
        prods: dict[int, tuple[str, tuple]] = {}
        for l in (OVERLAY / "prod-ids.txt").read_text().splitlines():
            f = l.split("\t")
            if l.startswith("#") or len(f) < 2 or "retired" in f[2:]:
                continue
            g, mask, text = f[1].split(" ", 2)
            m = re.match(r"(\S+) :{1,3} ?(.*)$", text)
            prods[int(f[0])] = (m.group(1), next(presences(grammar_symbols(m.group(2)), mask)))
        orphans = {squash(e.attrs.get("grammar", "")) for e in self.ov.by("emu-orphan-row")}
        lean_str = lambda s: re.sub(r"\\(.)", lambda m: {"n": "\n", "t": "\t"}.get(m.group(1), m.group(1)), s)
        for f in sorted((ROOT / "lean/Ecma/Gen").glob("*.lean")):
            src = f.read_text()
            sites = [(m.start(), m.group(1), [m.group(2)]) for m in re.finditer(r'\.prod \[([\d, ]*)\] "((?:[^"\\]|\\.)*)"', src)]
            sites += [(m.start(), m.group(1), re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(2))) for m in
                      re.finditer(r'prods := \[([\d, ]*)\]\n\s*keys := \[((?:"(?:[^"\\]|\\.)*"(?:, )?)*)\]', src)]
            for pos, ids, keys in sites:
                ids = [int(x) for x in ids.split(",") if x.strip()]
                text = "\n".join(re.sub(r"</?emu-grammar>", "", lean_str(k)) for k in keys)
                lines = key_productions(text)
                got = [prods.get(i) for i in ids]
                where = f"{f.relative_to(ROOT)}:{line_of(src, pos)}"
                if not ids and squash(text) in orphans:
                    self.counts["grammar keys against their production ids"]["a row an erratum says names no production"] += 1
                    continue
                bad = [i for i, p in zip(ids, got) if p is None or not any(p[0] == lhs and p[1] in ex for lhs, ex in lines)]
                missing = [lhs for lhs, ex in lines if not any(p is not None and p[0] == lhs and p[1] in ex for p in got)]
                if bad or missing or not lines:
                    self.fail(f"FAIL {where}: the production ids {ids} are not the key's {squash(text)!r}"
                              f"{f' (ids naming no production of it: {bad})' if bad else ''}{f' (lines with no id: {missing})' if missing else ''}")
                self.counts["grammar keys against their production ids"]["keys"] += 1

    def run(self) -> None:
        self.algorithms()
        self.keys()
        self.early()
        self.tables()
        self.blocks()
        self.step_readings()
        self.rule_readings()
        self.grammar_readings()
        self.params()
        self.prims()
        self.phrases()
        self.sorts()
        self.errata()
        self.side_checks()
        self.key_ids()
        known = {"alg", "row", "key", "early", "table", "block", "reading", "rule-reading", "grammar-reading", "params",
                 "prim", "phrase", "sort", "erratum"}
        for k in sorted(set(self.by_kind) - known):
            self.fail(f"FAIL ecma-print printed {len(self.by_kind[k])} items of a kind this check does not know: {k}")


def spans_of(src: str, tag: str) -> list[tuple[int, int]]:
    """The outermost elements `tag` of `src`, from their opening tag to their closing tag."""
    out = []
    depth, start = 0, 0
    for m in re.finditer(rf"<(/?){re.escape(tag)}\b[^>]*>", src):
        if m.group(1):
            depth -= 1
            if depth == 0:
                out.append((start, m.end()))
        else:
            if depth == 0:
                start = m.start()
            depth += 1
    return out


def clauses_at(src: str, positions: list[int]) -> list[str | None]:
    """The id of the innermost clause with an id around each of the (ascending) `positions`."""
    out: list[str | None] = []
    stack: list[str | None] = []
    ps = iter(positions)
    p = next(ps, None)
    for m in re.finditer(r"<(/?)(emu-clause|emu-annex)\b([^>]*)>", src):
        while p is not None and p < m.start():
            out.append(next((c for c in reversed(stack) if c), None))
            p = next(ps, None)
        if m.group(1):
            stack.pop()
        else:
            idm = re.search(r'\bid="([^"]+)"', m.group(3))
            stack.append(idm.group(1) if idm else None)
    while p is not None:
        out.append(None)
        p = next(ps, None)
    return out


def step_paths(body: str) -> list[tuple[str, str]]:
    """An emu-alg body's steps: each step's path (`3.a.ii`: numbers, letters, roman numerals by depth) and its
    text (the line after its marker and its `[attributes]`)."""
    out: list[tuple[str, str]] = []
    stack: list[tuple[int, int]] = []  # (column, count) of each open depth
    lines = [l for l in body.split("\n") if re.match(r" *1\. ", l)]
    labels: list[str] = []
    for l in lines:
        col = len(l) - len(l.lstrip())
        while stack and stack[-1][0] > col:
            stack.pop()
            labels.pop()
        if stack and stack[-1][0] == col:
            stack[-1] = (col, stack[-1][1] + 1)
            labels.pop()
        else:
            stack.append((col, 1))
        depth, n = len(stack) - 1, stack[-1][1]
        labels.append(str(n) if depth % 3 == 0 else letters(n) if depth % 3 == 1 else roman(n))
        text = re.sub(r"^ *1\. (?:\[[^\]]*\] )?", "", l)
        out.append((".".join(labels), text))
    return out


def letters(n: int) -> str:
    s = ""
    while n > 0:
        s = chr(ord("a") + (n - 1) % 26) + s
        n = (n - 1) // 26
    return s


def roman(n: int) -> str:
    out = ""
    for v, r in ((1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")):
        while n >= v:
            out += r
            n -= v
    return out


def grammar_symbols(rhs: str) -> list[str]:
    """A right-hand side's symbols as a key names them (§5.2.2): terminals and nonterminals as written, `X?` an
    optional one; its annotations (`[lookahead …]`, `[no LineTerminator here]`, guards, a nonterminal's arguments,
    `[empty]`) and labels left out, named character references decoded."""
    s = re.sub(r"&(?!#)\w+;", lambda m: html_unescape(m.group(0)), rhs)
    out: list[str] = []
    i = 0

    def terminal_end(j: int) -> int:
        # a terminal's closing backtick: the first after its first character not followed by another
        k = j + 2
        while k < len(s) and not (s[k] == "`" and (k + 1 == len(s) or s[k + 1] != "`")):
            k += 1
        return k
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
        elif c == "`":
            j = terminal_end(i)
            out.append(s[i:j + 1])
            i = j + 1
        elif c == "[":
            depth, j = 0, i
            while j < len(s):
                if s[j] == "`":
                    j = terminal_end(j)
                elif s[j] == "[":
                    depth += 1
                elif s[j] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            i = j + 1
            if i < len(s) and s[i] == "?" and out:
                out[-1] += "?"
                i += 1
        elif c == "#":
            while i < len(s) and not s[i].isspace():
                i += 1
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "[`":
                j += 1
            out.append(s[i:j])
            i = j
    return out


def presences(syms: list[str], mask: str | None = None):
    """The right-hand sides a list of symbols stands for, each optional symbol absent or present (§5.1.6); with
    `mask` (`0`/`1` per optional symbol, `-` for none), the one it names."""
    opt = [k for k, x in enumerate(syms) if x.endswith("?") and not x.startswith("`")]
    masks = [tuple(int(b) for b in mask)] if mask not in (None, "-") else [()] if mask == "-" else itertools.product([0, 1], repeat=len(opt))
    for bits in masks:
        on = dict(zip(opt, bits))
        yield tuple(x[:-1] if k in on else x for k, x in enumerate(syms) if on.get(k, 1))


def key_productions(key: str) -> list[tuple[str, set]]:
    """The productions a key block names: per line `Lhs : rhs` (or a definition's lines), its left-hand side and the
    right-hand sides it stands for; a `one of` line's terminals one by one."""
    out: list[tuple[str, set]] = []
    cur: tuple[str, bool] | None = None
    for l in (x.strip() for x in key.split("\n")):
        if not l:
            cur = None
            continue
        m = re.match(r"^(\w+)(?:\[[^\]]*\])?\s*:{1,3}\s*(.*)$", l)
        if m:
            lhs, rest = m.groups()
            if rest.startswith("one of "):
                out += [(lhs, {(x,)}) for x in grammar_symbols(rest[7:])]
            elif rest and rest != "one of":
                out.append((lhs, set(presences(grammar_symbols(rest)))))
            cur = None if rest and rest != "one of" else (lhs, rest == "one of")
        elif cur:
            if cur[1]:
                out += [(cur[0], {(x,)}) for x in grammar_symbols(l)]
            else:
                out.append((cur[0], set(presences(grammar_symbols(l)))))
    return out


def spellings(tmpl: str, limit: int = 4096) -> list[str]:
    """Every spelling of a printed template: each choice `⟨ a | b ⟩` (nested ones too) made every way."""
    def alts(s: str, i: int) -> tuple[list[str], int]:
        # the spellings of s[i:] up to an unmatched `|` or `⟩`, and where it stopped
        out = [""]
        while i < len(s) and s[i] not in "|⟩":
            if s[i] == "⟨":
                opts: list[str] = []
                i += 1
                while True:
                    sub, i = alts(s, i)
                    opts += sub
                    if i >= len(s) or s[i] == "⟩":
                        i += 1
                        break
                    i += 1
                out = [a + b for a in out for b in opts][:limit]
            else:
                out = [a + s[i] for a in out]
                i += 1
        return out, i
    return alts(tmpl, 0)[0]


def header_params(h1: str) -> str:
    """An operation heading's parameters as `_x_: T, _y_: U`: an abstract operation's `_x_: T,` lines, a
    built-in function's names (optional ones in brackets), without types."""
    m = re.search(r"\((.*)\)", h1, re.S)
    inner = m.group(1) if m else ""
    if ":" in inner:
        parts = [p.strip() for p in inner.split("\n") if p.strip()]
        out = []
        for p in parts:
            p = p.rstrip(",")
            p = re.sub(r"^optional ", "", p)
            out.append(p)
        return ", ".join(out)
    return ", ".join(f"_{n}_" for n in re.findall(r"_(\w+)_", inner))


def report_items(path: str | None, exe: str) -> str:
    if path:
        return Path(path).read_text()
    if not Path(exe).exists():
        raise SystemExit(f"{exe}: not built (lake build ecma-print)")
    r = subprocess.run([exe], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"{exe} failed:\n{r.stderr[-2000:]}")
    return r.stdout


def main() -> int:
    global GENERATOR, OVERLAY
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--print", default=str(ROOT / ".lake/build/bin/ecma-print"), help="the printer, ecma-print")
    ap.add_argument("--report", help="ecma-print's output, read from a file instead of running it")
    ap.add_argument("--spec", help="a spec.html or its directory (default: the text, scripts/spec_text.py)")
    ap.add_argument("--overlay", default=str(OVERLAY), help="the overlay's directory (default: spec/formal)")
    ap.add_argument("--json", help="write the classes and their counts here")
    ap.add_argument("-v", action="store_true", help="every problem, not the first 30")
    a = ap.parse_args()
    GENERATOR = Generator()
    OVERLAY = Path(a.overlay)
    items = read_items(report_items(a.report, a.print))
    html = Html(spec_text.resolve(a.spec))
    ov = Overlay()
    c = Check(html, ov, items)
    c.run()
    ovc = c.overlay_classes()
    cov = c.coverage()
    total = len(html.src)
    for p in c.problems[: None if a.v else MAX_SHOWN]:
        print(p)
    if len(c.problems) > MAX_SHOWN and not a.v:
        print(f"... and {len(c.problems) - MAX_SHOWN} more (-v shows them all)")
    order = ["algorithm steps", "SDO equations", "early-error rules", "tables", "grammar productions", "grammar keys",
             "overlay algorithms", "step readings", "early-error rule readings", "grammar rule readings",
             "overlay parameters", "primitives", "phrases", "sorts", "errata", "values against their written digits", "grammar keys against their production ids"]
    for k in order + sorted(set(c.counts) - set(order)):
        if k in c.counts:
            print(f"{k}: " + ", ".join(f"{n} {x}" for n, x in c.counts[k].items()))
    by_status: Counter = Counter()
    for n, v in cov.items():
        by_status[v["status"]] += v["characters"]
    print(f"spec.html, {total} characters: " + ", ".join(f"{s} {x} ({100 * x / total:.1f}%)" for s, x in by_status.items()))
    for n, v in cov.items():
        print(f"  {v['status']}: {n} {v['characters']}")
    print("spec/formal's elements: " + ", ".join(f"{n} {v['elements']} ({v['status']})" for n, v in ovc.items()))
    ok = not c.problems
    print(f"{'ok  ' if ok else 'FAIL'} the bijection: {len(items)} items printed by ecma-print, {len(c.problems)} problems")
    if a.json:
        Path(a.json).write_text(json.dumps({
            "spec": os.path.relpath(html.path, ROOT), "characters": total, "items": len(items),
            "problems": len(c.problems),
            "classes": {k: dict(v) for k, v in c.counts.items()},
            "spec_characters": cov, "spec_characters_by_status": dict(by_status),
            "overlay": ovc,
        }, indent=1, ensure_ascii=False) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
