#!/usr/bin/env python3
"""Lean sources as reading pages: each declaration's docstring as prose, then its Lean.

    python3 scripts/render_lean.py [--spec spec.html] FILE.lean… > fragment.html

A library for `scripts/site_pages.py`, which lays the pages out; run alone it prints the fragment of the files
named, for a look. A file is read as Lean commands in source order. Module docstrings (`/-! … -/`) are prose;
`def`, `structure`, `inductive` (and the other declaration keywords) are entries, each with a stable anchor (its
name without the root namespace `Ecma.`: `#Host.TimeLaws.timeoutAfter`). A structure's fields and an inductive's
constructors are entries of their own. A field of a `structure … : Prop` whose docstring keeps the laws'
convention (`scripts/law_quotes.py`: a clause id, the quoted sentence(s), `Reading:`; or `No sentence:`) is a law
and is laid out sentence first: the clause, the specification's sentence quoted, the reading, the Lean folded.

Docstrings are read as the sources write them: Markdown paragraphs, lists and headings, `**strong**`, and
ecmarkdown's emphasis (`_var_`, `*value*`, `~constant~`, `|Nonterminal|`). A backquoted name that is an entry on
some page links to it; so does a name in the Lean. A clause id (`sec-…`) links to the specification
(`CLAUSE_URL`) and must be an element of spec.html.

The renderer fails (`RenderError`) on a command it does not know (so every declaration of a rendered file is
rendered), on a clause id spec.html does not have, and on a law of `law_quotes.FILES` it did not lay out as one.
"""

from __future__ import annotations

import argparse
import html
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import law_quotes

ROOT = Path(__file__).resolve().parent.parent
CLAUSE_URL = "https://tc39.es/ecma262/#{}"
ID_RE = re.compile(r"(?<![\w/#-])(" + law_quotes.ID + r")")

# Commands that only set the context of the declarations after them.
CONTEXT = ("module", "public import", "import", "@[expose] public section", "namespace", "end", "section",
           "variable", "open", "universe", "set_option")
DECL_KEYWORDS = ("def", "structure", "inductive", "abbrev", "theorem", "class", "instance", "opaque", "axiom")
LEAN_KEYWORDS = {
    "def", "structure", "inductive", "abbrev", "theorem", "class", "instance", "where", "extends", "fun", "match",
    "with", "if", "then", "else", "let", "do", "return", "by", "have", "show", "from", "deriving", "in", "open",
    "namespace", "end", "section", "variable", "Prop", "Type", "for", "unless", "mut", "pure", "guard",
}


class RenderError(Exception):
    pass


# ---------------------------------------------------------------------------------------------------------------
# Reading a file


@dataclass
class Member:
    """A structure's field or an inductive's constructor."""

    name: str
    doc: str | None
    code: str
    line: int
    anchor: str = ""


@dataclass
class Decl:
    kind: str
    name: str  # as written
    full: str  # with the namespace, `Ecma.` included
    anchor: str
    doc: str | None
    code: str  # the whole command
    head: str  # a structure's or inductive's header (to `where`), else the whole command
    line: int
    path: Path
    ns: list[str]
    members: list[Member] = field(default_factory=list)
    extends: list[str] = field(default_factory=list)
    is_prop: bool = False
    tail: str = ""  # a `deriving` clause after the members


@dataclass
class ModDoc:
    text: str
    line: int
    ns: list[str]


@dataclass
class Module:
    path: Path
    items: list  # ModDoc | Decl


def anchor_of(full: str) -> str:
    return full.removeprefix("Ecma.")


def _comment_end(src: str, i: int) -> int:
    """The index after the `-/` closing the comment opened at `i` (comments nest)."""
    depth, j = 0, i
    while j < len(src):
        if src.startswith("/-", j):
            depth += 1
            j += 2
        elif src.startswith("-/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
        else:
            j += 1
    raise RenderError(f"unclosed comment at offset {i}")


def _starts_command(line: str) -> bool:
    if not line or line[0] in " \t":
        return False
    w = line.split(None, 1)[0]
    return (line.startswith(("/-", "--", "@[")) or w in DECL_KEYWORDS or w in ("module", "public", "import",
            "namespace", "end", "section", "variable", "open", "universe", "set_option", "private", "noncomputable",
            "protected", "mutual", "macro", "syntax", "attribute", "example", "notation", "macro_rules"))


def parse_file(path: Path) -> Module:
    src = path.read_text()
    lines_at = [0]
    for m in re.finditer("\n", src):
        lines_at.append(m.end())

    def lineno(i: int) -> int:
        lo, hi = 0, len(lines_at)
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if lines_at[mid] <= i:
                lo = mid
            else:
                hi = mid
        return lo + 1

    items: list = []
    stack: list[tuple[str, list[str]]] = []
    i, doc, doc_line, prefix = 0, None, 0, ""
    n = len(src)

    def cur_ns() -> list[str]:
        out: list[str] = []
        for k, parts in stack:
            if k == "ns":
                out += parts
        return out

    while i < n:
        if src[i] in " \t\n":
            i += 1
            continue
        line_end = src.find("\n", i)
        line_end = n if line_end < 0 else line_end
        if src.startswith("/-!", i):
            j = _comment_end(src, i)
            items.append(ModDoc(src[i + 3 : j - 2], lineno(i), cur_ns()))
            i = j
            continue
        if src.startswith("/--", i):
            j = _comment_end(src, i)
            doc, doc_line = src[i + 3 : j - 2], lineno(i)
            i = j
            continue
        if src.startswith("/-", i):
            raise RenderError(f"{path}:{lineno(i)}: a plain comment at top level is not rendered")
        if src.startswith("--", i):
            raise RenderError(f"{path}:{lineno(i)}: a line comment at top level is not rendered")
        # A command: this line and every following line that starts no command.
        j = line_end
        while j < n:
            nxt = src.find("\n", j + 1)
            nxt = n if nxt < 0 else nxt
            ln = src[j + 1 : nxt]
            if _starts_command(ln):
                break
            j = nxt
        cmd = src[i:j].rstrip()
        start = lineno(i)
        i = j
        first = cmd.split("\n", 1)[0]
        if re.match(r"open\s.*\sin$", first) and "\n" not in cmd:
            prefix = first + "\n"
            continue
        if first.startswith(("module", "public import", "import", "@[expose] public section", "universe",
                             "set_option")):
            continue
        if first.startswith("namespace "):
            stack.append(("ns", first.split()[1].split(".")))
            continue
        if first.startswith("section"):
            stack.append(("sec", first.split()[1:]))
            continue
        if first.startswith("end"):
            if not stack:
                raise RenderError(f"{path}:{start}: `end` with nothing open")
            stack.pop()
            continue
        if first.startswith(("variable", "open ")):
            continue
        m = re.match(r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(" + "|".join(DECL_KEYWORDS)
                     + r")\s+([^\s({\[:]+)", first)
        if not m:
            raise RenderError(f"{path}:{start}: a command the renderer does not know: {first[:80]!r}")
        kind, name = m.group(1), m.group(2)
        if doc is not None and doc_line and start - doc_line > 40:
            raise RenderError(f"{path}:{doc_line}: a docstring far from its declaration")
        full = ".".join(cur_ns() + [name])
        d = Decl(kind, name, full, anchor_of(full), doc, prefix + cmd, prefix + cmd, start, path, cur_ns())
        if kind in ("structure", "class", "inductive"):
            _members(d, cmd, start)
        items.append(d)
        doc, prefix = None, ""
    if doc is not None:
        raise RenderError(f"{path}:{doc_line}: a docstring with no declaration")
    return Module(path, items)


def _members(d: Decl, cmd: str, start: int) -> None:
    lines = cmd.split("\n")
    # The header: to the line that ends with `where` (or the whole command: a structure that only extends).
    h = 0
    while h < len(lines) and not re.search(r"\bwhere\s*$", lines[h]):
        h += 1
    head_end = h if h < len(lines) else len(lines) - 1
    head = "\n".join(lines[: head_end + 1])
    d.head = (d.code[: len(d.code) - len(cmd)]) + head
    d.is_prop = bool(re.search(r":\s*Prop\b", head))
    em = re.search(r"\bextends\b(.*?)(?:\bwhere\b|$)", head, re.DOTALL)
    if em:
        d.extends = [x.strip() for x in em.group(1).split(",") if x.strip()]
    body = lines[head_end + 1 :]
    k, doc, doc_line = 0, None, 0
    while k < len(body):
        ln = body[k]
        if not ln.strip():
            k += 1
            continue
        ind = len(ln) - len(ln.lstrip())
        s = ln.strip()
        if s.startswith("/--"):
            buf = [s]
            doc_line = start + head_end + 1 + k
            while "-/" not in buf[-1][3 if len(buf) == 1 else 0 :]:
                k += 1
                buf.append(body[k])
            text = "\n".join(buf)
            doc = text[3 : text.rindex("-/")]
            k += 1
            continue
        if s.startswith("deriving"):
            d.tail += _dedent(ln) + "\n"
            k += 1
            continue
        if d.kind == "inductive":
            m = re.match(r"\|\s*([^\s({\[:]+)", s)
        else:
            m = re.match(r"([A-Za-z_][\w'!?]*)\s*(?::|\(|\{|\[|:=)", s)
        if not m:
            raise RenderError(f"{d.path}:{start + head_end + 1 + k}: not a member: {s[:80]!r}")
        name = m.group(1)
        code = [ln]
        k += 1
        while k < len(body) and body[k].strip() and (len(body[k]) - len(body[k].lstrip())) > ind \
                and not body[k].strip().startswith("/--"):
            code.append(body[k])
            k += 1
        mem = Member(name, doc, _dedent("\n".join(code)), start + head_end + 1 + k - len(code))
        mem.anchor = f"{d.anchor}.{name}"
        d.members.append(mem)
        doc = None
    if doc is not None:
        raise RenderError(f"{d.path}:{doc_line}: a member's docstring with no member")


def _dedent(code: str) -> str:
    ls = code.split("\n")
    ind = min((len(x) - len(x.lstrip()) for x in ls if x.strip()), default=0)
    return "\n".join(x[ind:] for x in ls)


# ---------------------------------------------------------------------------------------------------------------
# The index of names, for links


class Index:
    """Every rendered entry by its full Lean name: (page, anchor)."""

    def __init__(self) -> None:
        self.names: dict[str, tuple[str, str]] = {}
        self.decls: dict[str, Decl] = {}

    def add_module(self, mod: Module, page: str) -> None:
        for it in mod.items:
            if isinstance(it, Decl):
                self.names[it.full] = (page, it.anchor)
                self.decls[it.full] = it
                for m in it.members:
                    self.names[f"{it.full}.{m.name}"] = (page, m.anchor)
        # A structure's parents' fields are its fields too (`Host.WF.elapsedMono`).
        for it in mod.items:
            if isinstance(it, Decl) and it.extends:
                for p in it.extends:
                    pname = re.sub(r"^H\.", "Host.", p.split()[0])
                    pd = self.resolve_decl(pname, it.ns)
                    if pd:
                        for m in pd.members:
                            self.names.setdefault(f"{it.full}.{m.name}", (page, m.anchor))

    def resolve_decl(self, name: str, ns: list[str]) -> Decl | None:
        full = self.resolve(name, ns)
        return self.decls.get(full) if full else None

    def resolve(self, name: str, ns: list[str]) -> str | None:
        name = name.strip()
        for k in range(len(ns), -1, -1):
            cand = ".".join(ns[:k] + [name])
            if cand in self.names:
                return cand
        for root in ("Ecma", "Ecma.Machine"):
            cand = f"{root}.{name}"
            if cand in self.names:
                return cand
        return None

    def href(self, name: str, ns: list[str], here: str) -> str | None:
        full = self.resolve(name, ns)
        if not full:
            return None
        page, anchor = self.names[full]
        return ("" if page == here else page) + "#" + anchor


# ---------------------------------------------------------------------------------------------------------------
# spec.html: clause titles and numbers


class SpecText(law_quotes.Spec):
    """law_quotes' spec.html, with each clause's number and title."""

    def __init__(self) -> None:
        super().__init__()
        self.nums: dict[str, str] = {}
        self.titles: dict[str, str] = {}
        self.used: set[str] = set()
        stack: list[str | None] = []
        counts = [0]
        annex = 0
        for m in re.finditer(r"<(/?)(emu-clause|emu-annex|emu-intro)\b([^>]*)>", self.src):
            close, tag, attrs = m.groups()
            if close:
                stack.pop()
                counts.pop()
                continue
            idm = re.search(r'\bid="([^"]+)"', attrs)
            if tag == "emu-intro":
                num = None
            elif not stack and tag == "emu-annex":
                annex += 1
                num = chr(64 + annex)
            else:
                counts[-1] += 1
                num = (stack[-1] + "." if stack and stack[-1] else "") + str(counts[-1])
            stack.append(num)
            counts.append(0)
            if idm and num:
                self.nums[idm.group(1)] = num
                h = re.search(r"<h1>(.*?)</h1>", self.src[m.end() : m.end() + 4000], re.DOTALL)
                if h:
                    t = html.unescape(re.sub(r"<[^>]*>", "", h.group(1)))
                    t = re.sub(r"[_*~|]", "", t)
                    self.titles[idm.group(1)] = re.sub(r"\s+", " ", t).strip()
        # The numbering is computed, so it is checked against clauses whose numbers are known.
        for cid, num in (("sec-ecmascript-language-types-number-type", "6.1.6.1"), ("sec-date.now", "21.4.3.1"),
                         ("sec-jobs", "9.5"), ("sec-conformance", "2"), ("sec-additional-ecmascript-features-for-web-browsers", "B")):
            if self.nums.get(cid) != num:
                raise RenderError(f"spec.html: {cid} numbered {self.nums.get(cid)}, expected {num}")

    def exists(self, cid: str) -> bool:
        return re.search(r'\bid="' + re.escape(cid) + r'"', self.src) is not None

    def need(self, cid: str, where: str) -> None:
        if cid in self.used:
            return
        if not self.exists(cid):
            raise RenderError(f"{where}: no element with id {cid} in spec.html")
        self.used.add(cid)

    def short_title(self, cid: str) -> str:
        """A clause's title without its parameters: `HostEnqueueTimeoutJob`."""
        t = self.titles.get(cid)
        if t is None:
            return cid
        m = re.match(r"([^(]+?)\s*\(", t)
        return m.group(1) if m else t


# ---------------------------------------------------------------------------------------------------------------
# Prose


def esc(s: str) -> str:
    return html.escape(s, quote=True)


class Prose:
    def __init__(self, spec: SpecText, index: Index, page: str) -> None:
        self.spec, self.index, self.page = spec, index, page
        self.where = page
        self.unlinked: list[str] = []

    def code_span(self, text: str, ns: list[str]) -> str:
        t = text.strip()
        name = t.split()[0] if t else t
        href = None
        if re.fullmatch(r"[A-Za-z_][\w'.]*", t):
            href = self.index.href(t, ns, self.page)
        elif t and re.fullmatch(r"[A-Za-z_][\w'.]*", name):
            # `Model.NodeRel M src n t`: the head of an application links.
            href = self.index.href(name, ns, self.page)
        inner = f"<code>{esc(text)}</code>"
        return f'<a class="name" href="{esc(href)}">{inner}</a>' if href else inner

    def clause_link(self, cid: str, label: str | None = None) -> str:
        self.spec.need(cid, self.where)
        return f'<a class="clause" href="{esc(CLAUSE_URL.format(cid))}">{esc(label or cid)}</a>'

    def inline(self, text: str, ns: list[str]) -> str:
        """One paragraph's text as HTML."""
        out: list[str] = []
        parts = re.split(r"(`[^`]+`)", text)
        for p in parts:
            if p.startswith("`") and p.endswith("`") and len(p) > 1:
                out.append(self.code_span(p[1:-1], ns))
                continue
            out.append(self._emph(p))
        return "".join(out)

    def _emph(self, t: str) -> str:
        holes: list[str] = []

        def hole(s: str) -> str:
            holes.append(s)
            return f"\x00{len(holes) - 1}\x00"

        t = ID_RE.sub(lambda m: hole(self._id(m.group(1))), t)
        t = esc(t)
        t = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", t)
        t = re.sub(r"(?<![\w*])\*([^*\s](?:[^*]*?[^*\s])?)\*(?![\w*])", r'<span class="val">\1</span>', t)
        t = re.sub(r"(?<![\w])_([^_\s](?:[^_]*?[^_\s])?)_(?![\w])", r"<var>\1</var>", t)
        t = re.sub(r"(?<![\w~])~([\w-]+)~(?![\w~])", r'<span class="const">\1</span>', t)
        t = re.sub(r"\|([A-Z][A-Za-z]*(?:\[[^\]|]*\])?)\|", r'<span class="nt">\1</span>', t)
        return re.sub(r"\x00(\d+)\x00", lambda m: holes[int(m.group(1))], t)

    def _id(self, cid: str) -> str:
        trail = ""
        while cid and cid[-1] in ".,;:":
            trail = cid[-1] + trail
            cid = cid[:-1]
        if not self.spec.exists(cid):
            # A word of the prose that only looks like an id ("that sec-id"): not linked, and reported.
            self.unlinked.append(f"{self.where}: {cid!r} looks like a clause id and is none; not linked")
            return esc(cid + trail)
        return self.clause_link(cid) + esc(trail)

    def block(self, text: str, ns: list[str], base_heading: int = 2) -> str:
        """A docstring as paragraphs, lists, headings and code blocks."""
        lines = _dedent(text.strip("\n")).split("\n")
        out: list[str] = []
        para: list[str] = []
        items: list[str] = []
        i = 0

        def flush() -> None:
            nonlocal para, items
            if para:
                out.append(f"<p>{self.inline(' '.join(x.strip() for x in para), ns)}</p>")
                para = []
            if items:
                out.append("<ul>" + "".join(f"<li>{self.inline(x, ns)}</li>" for x in items) + "</ul>")
                items = []

        while i < len(lines):
            ln = lines[i]
            s = ln.strip()
            if not s:
                flush()
                i += 1
                continue
            if s.startswith("```"):
                flush()
                j = i + 1
                while j < len(lines) and not lines[j].strip().startswith("```"):
                    j += 1
                out.append(f'<pre class="lean">{highlight(chr(10).join(lines[i + 1 : j]), self, ns)}</pre>')
                i = j + 1
                continue
            hm = re.match(r"(#+)\s+(.*)", s)
            if hm and not para and not items:
                level = min(6, base_heading + len(hm.group(1)) - 1)
                out.append(f"<h{level}>{self.inline(hm.group(2), ns)}</h{level}>")
                i += 1
                continue
            if re.match(r"[-*]\s+", s) and not ln.startswith("    "):
                if para:
                    out.append(f"<p>{self.inline(' '.join(x.strip() for x in para), ns)}</p>")
                    para = []
                items.append(re.sub(r"^[-*]\s+", "", s))
                i += 1
                continue
            if items:
                items[-1] += " " + s
            else:
                para.append(ln)
            i += 1
        flush()
        return "\n".join(out)


# ---------------------------------------------------------------------------------------------------------------
# Lean, lightly highlighted

TOKEN = re.compile(
    r"(?P<com>--[^\n]*|/-.*?-/)"
    r"|(?P<str>\"(?:\\.|[^\"\\])*\")"
    r"|(?P<num>\b\d+\b)"
    r"|(?P<id>[^\W\d][\w'.!?₀-₉]*)"
    r"|(?P<sym>[∀∃→←↔∧∨¬≠≤≥λ⟨⟩×⊕∈∉∅]|:=|=>|\|)",
    re.DOTALL,
)


def highlight(code: str, prose: Prose | None, ns: list[str], own: str | None = None) -> str:
    """The Lean, each source line a block (so a long line wraps under its own indentation). A comment or a
    docstring may span lines: the text is tokenized whole, then cut into lines."""
    pieces: list[tuple[str | None, str]] = []  # (CSS class or "a:<href>", text)
    pos = 0
    for m in TOKEN.finditer(code):
        if m.start() > pos:
            pieces.append((None, code[pos : m.start()]))
        tok, kind = m.group(0), m.lastgroup
        cls: str | None = None
        if kind == "com":
            cls = "c"
        elif kind == "str":
            cls = "s"
        elif kind in ("num", "sym"):
            cls = "n" if kind == "num" else "o"
        elif tok in LEAN_KEYWORDS:
            cls = "k"
        elif own and tok == own:
            cls = "d"
        elif prose and ("." in tok or tok[0].isupper() or len(tok) > 3):
            href = prose.index.href(tok, ns, prose.page)
            cls = f"a:{href}" if href else None
        pieces.append((cls, tok))
        pos = m.end()
    pieces.append((None, code[pos:]))

    def wrap(cls: str | None, text: str) -> str:
        if not text:
            return ""
        if cls is None:
            return esc(text)
        if cls.startswith("a:"):
            return f'<a href="{esc(cls[2:])}">{esc(text)}</a>'
        return f'<span class="{cls}">{esc(text)}</span>'

    raw = code.split("\n")
    lines: list[list[str]] = [[]]
    for cls, text in pieces:
        for k, part in enumerate(text.split("\n")):
            if k:
                lines.append([])
            lines[-1].append(wrap(cls, part))
    out = []
    for k, buf in enumerate(lines):
        ind = len(raw[k]) - len(raw[k].lstrip(" "))
        out.append(f'<span class="l" style="--i:{ind}">{"".join(buf) or " "}</span>')
    return "".join(out)


# ---------------------------------------------------------------------------------------------------------------
# Laws


@dataclass
class Law:
    cid: str | None
    locator: str  # "step 23", "the requirements' first item", …
    quotes: list[tuple[str, str]]  # (clause id, text)
    reading: str
    no_sentence: str | None
    problems: list[str]


def parse_law(doc: str) -> Law | None:
    """A law docstring by the convention, or None where it is not one."""
    if "Reading:" not in doc and "No sentence:" not in doc:
        return None
    problems: list[str] = []
    ns = re.match(r"\s*No sentence:\s*(.*?)\n\s*Reading:\s*(.*)$", doc, re.DOTALL)
    if ns:
        return Law(None, "", [], _join(ns.group(2)), _join(ns.group(1)), problems)
    head, _, reading = _split_reading(doc)
    cid, qs = law_quotes.quotes(doc)
    first = head.strip().split("\n")[0]
    m = re.match(r"(" + law_quotes.ID + r")(.*):\s*$", first)
    locator = ""
    if m:
        locator = m.group(2).strip().lstrip(",").strip()
    else:
        problems.append("the first line is not `<clause id> [where]:`")
    rest = [x.strip() for x in head.strip().split("\n")[1:] if x.strip()]
    for x in rest:
        if not re.match(r"(?:" + law_quotes.ID + r"[^:\"]*:\s*)?\".*\"$", x):
            problems.append(f"a line between the clause and `Reading:` that is no quotation: {x[:60]!r}")
    if not qs:
        problems.append("no quotation")
    return Law(cid, locator, qs, _join(reading), None, problems)


def _split_reading(doc: str) -> tuple[str, str, str]:
    parts = re.split(r"\n\s*Reading:", doc, maxsplit=1)
    if len(parts) == 1:
        return parts[0], "", ""
    return parts[0], "Reading:", parts[1]


def _cap(t: str) -> str:
    """A reading as a sentence: its first letter capitalized, unless it begins with code or a variable."""
    return t[:1].upper() + t[1:] if t[:1].isalpha() and t[:1].islower() else t


def _join(t: str) -> str:
    return " ".join(x.strip() for x in t.strip().split("\n"))


# ---------------------------------------------------------------------------------------------------------------
# Rendering a module


@dataclass
class Options:
    """What a page adds to its modules' entries."""

    status: dict[str, str] = field(default_factory=dict)  # full name → HTML of its status line
    group_quotes: bool = True  # consecutive laws quoting the same sentence share one quotation
    fold_lines: int = 14  # a declaration's Lean longer than this is folded


class Renderer:
    def __init__(self, spec: SpecText, index: Index, page: str, opts: Options | None = None) -> None:
        self.spec, self.index, self.page = spec, index, page
        self.opts = opts or Options()
        self.prose = Prose(spec, index, page)
        self.laws: list[tuple[Decl, Member, Law]] = []  # every law rendered, in order
        self.findings: list[str] = []  # docstrings that break the convention or are missing
        self.rendered: set[str] = set()

    def module(self, mod: Module, heading: int = 2, skip_first_title: bool = False) -> str:
        """A module's prose and entries. The first heading of its first module docstring is the section's title."""
        out = []
        rel = mod.path.relative_to(ROOT) if mod.path.is_relative_to(ROOT) else mod.path
        for k, it in enumerate(mod.items):
            if isinstance(it, ModDoc):
                self.prose.where = f"{rel}:{it.line}"
                text = it.text
                if k == 0 and skip_first_title:
                    text = re.sub(r"^\s*#\s+[^\n]*\n", "", text, count=1)
                out.append(f'<div class="prose moddoc">{self.prose.block(text, it.ns, heading + 1)}</div>')
            else:
                out.append(self.decl(it, rel))
        return "\n".join(out)

    def decl(self, d: Decl, rel: Path) -> str:
        self.rendered.add(d.full)
        self.prose.where = f"{rel}:{d.line}"
        src = f'<a class="src" href="#{esc(d.anchor)}" title="{esc(str(rel))} line {d.line}">{esc(rel.name)}:{d.line}</a>'
        head = (f'<header class="entry-head"><span class="kind">{esc(d.kind)}</span> '
                f'<h4 class="entry-name"><a class="self" href="#{esc(d.anchor)}">{esc(d.anchor)}</a></h4>{src}</header>')
        doc = f'<div class="prose">{self.prose.block(d.doc, d.ns)}</div>' if d.doc else \
            '<p class="nodoc">No docstring.</p>'
        if not d.doc:
            self.findings.append(f"{rel}:{d.line} {d.anchor}: no docstring")
        status = self.opts.status.get(d.full, "")
        status = f'<p class="status">{status}</p>' if status else ""
        laws = [m for m in d.members if d.is_prop and m.doc and parse_law(m.doc)]
        if d.members:
            code_html = self._code(d.head, d.ns, d.name, open_=True)
            members = self._members(d, rel)
            cls = "entry decl lawset" if laws else "entry decl"
            n = f'<p class="count">{len(laws)} laws</p>' if laws else ""
            return (f'<section class="{cls}" id="{esc(d.anchor)}">{head}{doc}{status}{code_html}{n}'
                    f'{members}</section>')
        return f'<section class="entry decl" id="{esc(d.anchor)}">{head}{doc}{status}{self._code(d.code, d.ns, d.name)}</section>'

    def _code(self, code: str, ns: list[str], own: str, open_: bool = False) -> str:
        nlines = code.count("\n") + 1
        pre = f'<pre class="lean">{highlight(code, self.prose, ns, own.split(".")[-1])}</pre>'
        if nlines > self.opts.fold_lines and not open_:
            return f'<details class="lean-fold"><summary>Lean, {nlines} lines</summary>{pre}</details>'
        return pre

    def _members(self, d: Decl, rel: Path) -> str:
        out: list[str] = []
        last_key = None
        group: list[str] = []

        def close_group() -> None:
            nonlocal group
            if group:
                out.append("".join(group) + "</div>")
                group = []

        for m in d.members:
            self.rendered.add(f"{d.full}.{m.name}")
            self.prose.where = f"{rel}:{m.line}"
            law = parse_law(m.doc) if (d.is_prop and m.doc) else None
            if d.is_prop and not law:
                self.findings.append(f"{rel}:{m.line} {m.anchor}: "
                                     + ("no docstring" if not m.doc else "a docstring that is not in the laws' convention"))
            if law is None:
                close_group()
                last_key = None
                out.append(self._plain_member(d, m))
                continue
            for p in law.problems:
                self.findings.append(f"{rel}:{m.line} {m.anchor}: {p}")
            self.laws.append((d, m, law))
            key = (law.cid, law.locator, tuple(law.quotes)) if law.quotes else None
            if self.opts.group_quotes and key is not None and key == last_key:
                group.append(self._law(d, m, law, shared=True))
                continue
            close_group()
            last_key = key
            group.append('<div class="lawgroup">' + self._sentence(law) + self._law(d, m, law, shared=False))
        close_group()
        return f'<div class="members">{"".join(out)}</div>'

    def _plain_member(self, d: Decl, m: Member) -> str:
        doc = f'<div class="prose">{self.prose.block(m.doc, d.ns)}</div>' if m.doc else ""
        return (f'<article class="member" id="{esc(m.anchor)}"><div class="member-head">'
                f'<a class="self name" href="#{esc(m.anchor)}"><code>{esc(m.name)}</code></a></div>{doc}'
                f'<pre class="lean">{highlight(m.code, self.prose, d.ns, m.name)}</pre></article>')

    def clause_label(self, cid: str) -> str:
        num = self.spec.nums.get(cid)
        title = self.spec.short_title(cid)
        if title == cid:
            return cid
        return (f"{num} " if num else "") + title

    def _sentence(self, law: Law) -> str:
        if law.no_sentence is not None:
            return (f'<div class="nosentence"><span class="label">No sentence</span> '
                    f'{self.prose.inline(law.no_sentence, [])}</div>')
        cl = ""
        if law.cid:
            self.spec.need(law.cid, self.prose.where)
            num = self.spec.nums.get(law.cid)
            cl = (f'<div class="clause-line"><a class="clause" href="{esc(CLAUSE_URL.format(law.cid))}">'
                  f'{"<span class=secnum>" + esc(num) + "</span> " if num else ""}'
                  f'<span class="ctitle">{esc(self.spec.short_title(law.cid))}</span></a>'
                  f'{(" <span class=locator>" + self.prose._emph(law.locator) + "</span>") if law.locator else ""}'
                  f' <span class="cid">{esc(law.cid)}</span></div>')
        qs = []
        for c, q in law.quotes:
            self.spec.need(c, self.prose.where)
            why = law_quotes.check(self.spec, c, q)  # the page never shows a quotation spec.html does not have
            if why:
                raise RenderError(f"{self.prose.where}: {why}")
            other = ""
            if c != law.cid:
                other = (f'<cite><a class="clause" href="{esc(CLAUSE_URL.format(c))}">{esc(self.clause_label(c))}'
                         f'</a> <span class="cid">{esc(c)}</span></cite>')
            qs.append(f'<blockquote class="sentence">{other}<p>{self.prose._emph(q)}</p></blockquote>')
        return cl + "".join(qs)

    def _law(self, d: Decl, m: Member, law: Law, shared: bool) -> str:
        st = self.opts.status.get(f"{d.full}.{m.name}", "")
        st = f'<p class="status">{st}</p>' if st else ""
        return (f'<article class="law{" shared" if shared else ""}" id="{esc(m.anchor)}">'
                f'<p class="reading">{self.prose.inline(_cap(law.reading), d.ns)}</p>{st}'
                f'<div class="law-foot"><a class="self name" href="#{esc(m.anchor)}"><code>{esc(m.name)}</code></a>'
                f'<details class="lean-fold"><summary>Lean</summary>'
                f'<pre class="lean">{highlight(m.code, self.prose, d.ns, m.name)}</pre></details></div></article>')

    def check_laws(self) -> None:
        """Every law law_quotes reads in a rendered file was laid out as a law."""
        mine = {(str(d.path), m.name) for d, m, _ in self.laws}
        files = {str(d.path) for d, _, _ in self.laws}
        for f in law_quotes.FILES:
            if str(f) not in files:
                continue
            for line, name, _doc in law_quotes.docstrings(f):
                if (str(f), name) not in mine:
                    raise RenderError(f"{f.relative_to(ROOT)}:{line} {name}: a law not laid out as one")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--spec", type=Path, help="a spec.html (default: the text, scripts/spec_text.py)")
    ap.add_argument("files", nargs="+", type=Path)
    a = ap.parse_args()
    law_quotes.SPEC = a.spec
    spec = SpecText()
    index = Index()
    mods = [parse_file(f.resolve()) for f in a.files]
    for m in mods:
        index.add_module(m, "")
    r = Renderer(spec, index, "")
    for m in mods:
        print(r.module(m))
    r.check_laws()
    for f in r.findings + r.prose.unlinked:
        print(f"note: {f}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
