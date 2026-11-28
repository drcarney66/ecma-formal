#!/usr/bin/env python3
"""The errata as a page: from spec/DECISIONS.md and site/errata.json, each quotation checked against spec.html, each program run.

    python3 scripts/errata_page.py run --ecma-run .lake/build/bin/ecma-run --out build/errata-runs.json [-j 3]
    python3 scripts/errata_page.py check                     # the data and the quotations, no run

The errata are the 56 active decisions in `spec/DECISIONS.md` (§1 Summary Table: resolution, kind, layer, where the
literal text stops, source write-up) paired with `site/errata.json` (the step, rule, grammar and prose anchors in
`external/ecma262/spec.html`, alternative readings, notes, and demonstration programs). SpecTec bakes one resolved
reading directly into `spec/spectec/` for each erratum rather than switching readings at run time.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import law_quotes  # noqa: E402
import spec_text  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
DECISIONS = ROOT / "spec/DECISIONS.md"
DATA = ROOT / "site/errata.json"
ISSUES = ROOT / "docs/spec-issues/README.md"
ECMA262 = ROOT / "external/ecma262"
DIRS = {"demo": ROOT / "tools/dbg/demo", "dbg": ROOT / "tests/dbg", "run": ROOT / "tests/run"}
CLAUSE_URL = "https://tc39.es/ecma262/#{}"
COMMIT_URL = "https://github.com/tc39/ecma262/commit/{}"
PR_URL = "https://github.com/tc39/ecma262/pull/{}"
READING_NAMES = ("literal", "test262", "proposed")
TIMEOUT = 60  # seconds per run


def esc(s: str) -> str:
    return html.escape(s, quote=True)


# ---------------------------------------------------------------------------------------------------------------
# SpecTec's decisions & errata data


@dataclass
class Alt:
    readings: list[str]
    kind: str  # "alg", "p" (a rule's text), "grammar" (a definition)
    text: str


@dataclass
class Anchor:
    tag: str  # emu-reading, emu-rule-reading, emu-orphan-row
    attrs: dict[str, str]
    alts: list[Alt] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


@dataclass
class Erratum:
    name: str
    resolution: str
    kind: str
    switch: str  # layer in spec/DECISIONS.md: "spec", "parser", "none"
    stops: list[str] | None  # None: not given; []: never stops
    default: str  # baked-in reading in SpecTec
    anchors: list[Anchor]
    notes: list[str]
    reports: list[str] = field(default_factory=list)


def read_errata() -> list[Erratum]:
    dec = DECISIONS.read_text()
    m = re.search(r"\*\*Summary Table:\*\*\s*\n+(.*?)(?=\n### |\Z)", dec, re.DOTALL)
    if not m:
        raise SystemExit(f"{DECISIONS}: no Summary Table")
    data = json.loads(DATA.read_text())
    rd_map = data.get("readings", {})
    out: list[Erratum] = []
    for ln in m.group(1).strip().split("\n"):
        ln = ln.strip()
        if not ln.startswith("|"):
            continue
        cells = [c.strip() for c in ln.strip("|").split("|")]
        if len(cells) < 6 or cells[0] in ("Erratum", "---") or set(cells[0]) <= {"-"}:
            continue
        name = cells[0].strip("`")
        kind = cells[1].strip("`")
        res = cells[2].strip("`")
        layer = cells[3].strip("`")
        stops_raw = cells[4].strip("`")
        reports = [r.strip("`") for r in cells[5].split() if r.strip("`") and r.strip("`") != "—"]
        st = None if stops_raw in ("-", "—") else [] if stops_raw == "none" else stops_raw.split()
        baked = "proposed" if res == "pending" else res
        entry = rd_map.get(name)
        if entry is None:
            raise SystemExit(f"{DATA}: no readings entry for {name}")
        anchors = [
            Anchor(
                it["tag"],
                it["attrs"],
                [Alt(a["readings"], a["kind"], a["text"]) for a in it.get("alts", [])],
                it.get("notes", []),
            )
            for it in entry.get("items", [])
        ]
        out.append(Erratum(name, res, kind, layer, st, baked, anchors, entry.get("notes", []), reports))
    if not out:
        raise SystemExit(f"{DECISIONS}: parsed 0 errata rows")
    return out


def other_readings(e: Erratum) -> list[str]:
    """The readings the overlay gives an erratum besides the literal text, in the order test262, proposed."""
    got = {r for an in e.anchors for alt in an.alts for r in alt.readings}
    text = " ".join(e.notes + [n for an in e.anchors for n in an.notes])
    for r in ("test262", "proposed"):
        if re.search(r"\b" + r + r"\b(?: and \w+)? reading", text) or re.search(r"The proposed text", text) and r == "proposed":
            got.add(r)
    if e.resolution in ("test262", "proposed"):
        got.add(e.resolution)
    return [r for r in ("test262", "proposed") if r in got]


# ---------------------------------------------------------------------------------------------------------------
# spec.html


ROMAN = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x", "xi", "xii", "xiii", "xiv", "xv", "xvi",
         "xvii", "xviii", "xix", "xx", "xxi", "xxii", "xxiii", "xxiv", "xxv"]


def step_label(depth: int, k: int) -> str:
    m = depth % 3
    if m == 0:
        return str(k)
    if m == 1:
        s = ""
        while k > 0:
            k -= 1
            s = chr(97 + k % 26) + s
            k //= 26
        return s
    return ROMAN[k - 1]


def alg_steps(alg: str) -> list[tuple[str, str]]:
    """An emu-alg's steps: (path, the step's own text), the text as crates/spec-gen reads it."""
    out, stack = [], []
    for ln in alg.split("\n"):
        m = re.match(r"^(\s*)(?:\d+|\*)\.\s+(.*)$", ln)
        if not m:
            continue
        ind = len(m.group(1))
        while stack and stack[-1][0] > ind:
            stack.pop()
        if stack and stack[-1][0] == ind:
            stack[-1][1] += 1
        else:
            stack.append([ind, 1])
        out.append((".".join(step_label(d, c) for d, (_, c) in enumerate(stack)),
                    re.sub(r"^\[[^\]]*\]\s*", "", m.group(2)).rstrip()))
    return out


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


class Text(law_quotes.Spec):
    """spec.html: clauses' own text (without their subclauses), numbers and titles."""

    def __init__(self) -> None:
        super().__init__()
        self.nums: dict[str, str] = {}
        self.titles: dict[str, str] = {}
        stack: list[str | None] = []
        counts = [0]
        annex = 0
        for m in re.finditer(r"<(/?)(emu-clause|emu-annex|emu-intro)\b([^>]*)>", self.src):
            close, tag, a = m.groups()
            if close:
                stack.pop()
                counts.pop()
                continue
            idm = re.search(r'\bid="([^"]+)"', a)
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
                h = re.search(r"<h1>(.*?)</h1>", self.src[m.end(): m.end() + 4000], re.DOTALL)
                if h:
                    t = re.sub(r"[_*~|]", "", html.unescape(re.sub(r"<[^>]*>", "", h.group(1))))
                    self.titles[idm.group(1)] = re.sub(r"\s+", " ", t).strip()

    def exists(self, cid: str) -> bool:
        return re.search(r'\bid="' + re.escape(cid) + r'"', self.src) is not None

    def own(self, cid: str) -> str:
        raw = self.raw(cid)
        if raw is None:
            raise SystemExit(f"spec.html: no element {cid}")
        body = raw[raw.index(">") + 1:]
        res, pos, d = [], 0, 0
        for m in re.finditer(r"<(/?)(emu-clause|emu-annex)\b[^>]*>", body):
            if not m.group(1):
                if d == 0:
                    res.append(body[pos: m.start()])
                d += 1
            else:
                d -= 1
                if d == 0:
                    pos = m.end()
                if d < 0:
                    res.append(body[pos: m.start()])
                    break
        return "".join(res)

    def clause_of(self, cid: str) -> str:
        """The clause an element (a table, a note) is in."""
        if cid in self.nums:
            return cid
        at = self.src.find(f'id="{cid}"')
        best = None
        for m in re.finditer(r'<(emu-clause|emu-annex)\b[^>]*\bid="([^"]+)"', self.src[:at]):
            best = m.group(2)
        return best or cid

    def short(self, cid: str) -> str:
        t = self.titles.get(cid, cid)
        m = re.match(r"([^(]+?)\s*\(", t)
        return m.group(1) if m else t


@dataclass
class Quote:
    cid: str
    where: str  # "step 6", "an early-error rule", "", …
    text: str  # spec.html's markup
    block: str = "p"  # "p", "grammar"
    checked: str = ""  # how it was checked
    alts: list[Alt] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def grammar_def(block: str, rule: str) -> str | None:
    lines = [l for l in block.split("\n") if l.strip() and l.strip() != "// emu-format ignore"]
    if not lines:
        return None
    base = min(len(l) - len(l.lstrip()) for l in lines)
    lines = [l[base:] for l in lines]
    for k, l in enumerate(lines):
        if re.match(rf"{re.escape(rule)}\b", l):
            end = next((j for j in range(k + 1, len(lines)) if not lines[j].startswith(" ")), len(lines))
            return "\n".join(lines[k:end])
    return None


def quotes_of(e: Erratum, sp: Text, anchors: dict, findings: list[str]) -> list[Quote]:
    out: list[Quote] = []
    for an in e.anchors:
        a = an.attrs
        cid = a["clause"]
        own = sp.own(cid)
        if an.tag == "emu-reading" and "step" in a:
            steps = [(p, t) for alg in re.findall(r"<emu-alg\b[^>]*>(.*?)</emu-alg>", own, re.DOTALL) for p, t in alg_steps(alg)]
            hit = [(p, t) for p, t in steps if p == a["step"] and sha(t) == a["hash"]]
            if not hit:
                hit = [(p, t) for p, t in steps if sha(t) == a["hash"]]
                if not hit:
                    raise SystemExit(f"{e.name}: no step of {cid} has the hash {a['hash'][:12]}… (step {a['step']})")
                findings.append(f"{e.name}: the overlay names step {a['step']} of {cid}; the step with its hash is {hit[0][0]}")
            out.append(Quote(cid, f"step {hit[0][0]}", hit[0][1], checked="hash", alts=an.alts, notes=an.notes))
        elif an.tag == "emu-reading" and "rule" in a:
            m = re.search(r"<emu-grammar>" + re.escape(a["grammar"]) + r"</emu-grammar>\s*<ul>(.*?)</ul>", own, re.DOTALL)
            if not m:
                raise SystemExit(f"{e.name}: {cid} has no early-error rules for {a['grammar']}")
            lis = re.findall(r"<li>(.*?)</li>", m.group(1), re.DOTALL)
            k = int(a["rule"])
            if k >= len(lis) or sha(lis[k]) != a["hash"]:
                raise SystemExit(f"{e.name}: rule {k} of {a['grammar']} in {cid} does not have the hash {a['hash'][:12]}…")
            out.append(Quote(cid, f"the early-error rule of <code>{esc(a['grammar'])}</code>", lis[k].strip(),
                             checked="hash", alts=an.alts, notes=an.notes))
        elif an.tag == "emu-reading":  # a row the text lacks
            if f"<emu-grammar>{a['grammar']}</emu-grammar>" in own:
                raise SystemExit(f"{e.name}: {cid} has a row for {a['grammar']}, which the reading adds")
            out.append(Quote(cid, f"no row for <code>{esc(a['grammar'])}</code>", "", block="none",
                             checked="absent", alts=an.alts, notes=an.notes))
        elif an.tag == "emu-rule-reading":
            defs = [d for b in re.findall(r'<emu-grammar type="definition">(.*?)</emu-grammar>', own, re.DOTALL)
                    if (d := grammar_def(b, a["rule"]))]
            if len(defs) != 1 or sha(defs[0]) != a["hash"]:
                raise SystemExit(f"{e.name}: the definition of {a['rule']} in {cid} does not have the hash {a['hash'][:12]}…")
            out.append(Quote(cid, f"the definition of <span class=\"nt\">{esc(a['rule'])}</span>", defs[0],
                             block="grammar", checked="hash", alts=an.alts, notes=an.notes))
        elif an.tag == "emu-orphan-row":
            m = re.search(r"<li>((?:(?!</li>).)*<emu-grammar>" + re.escape(a["grammar"]) + r"</emu-grammar>.*?)</li>", own, re.DOTALL)
            if not m:
                raise SystemExit(f"{e.name}: {cid} has no row for {a['grammar']}")
            out.append(Quote(cid, "an equation row", m.group(1).strip(), checked="found"))
    for q in anchors.get(e.name, []):
        cid = q["clause"]
        if not sp.exists(cid):
            raise SystemExit(f"site/errata.json: {e.name}: no element {cid} in spec.html")
        for part in re.split(r"\s*(?:…|\.\.\.)\s*", q["quote"]):
            if law_quotes.norm(part) not in law_quotes.norm(sp.raw(cid)):
                raise SystemExit(f"site/errata.json: {e.name}: {cid} does not say {part!r}")
        out.append(Quote(sp.clause_of(cid), q.get("where", ""), q["quote"], checked="quote"))
    if not out:
        raise SystemExit(f"{e.name}: no sentence of the text (a reading's anchor, or site/errata.json's anchors)")
    return out


# ---------------------------------------------------------------------------------------------------------------
# The programs


def program_file(pid: str) -> Path:
    kind, _, name = pid.partition("/")
    if kind not in DIRS:
        raise SystemExit(f"site/errata.json: {pid}: a program is demo/NAME, dbg/NAME or run/NAME")
    f = DIRS[kind] / f"{name}.js"
    if not f.is_file():
        raise SystemExit(f"site/errata.json: {pid}: no {f.relative_to(ROOT)}")
    return f


def header_args(src: str, name: str) -> list[str]:
    """tests/run's `// module:` and `// args:` headers, less the options that set `name`'s reading."""
    a = ["--module"] if re.search(r"(?m)^// module: yes\s*$", src) else []
    m = re.search(r"(?m)^// args:(.*)$", src)
    if m:
        a += m.group(1).split()
    out, i = [], 0
    while i < len(a):
        if a[i] == "--literal" and i + 1 < len(a) and a[i + 1] == name:
            i += 2
            continue
        if a[i] == "--erratum" and i + 1 < len(a) and a[i + 1].startswith(name + "="):
            i += 2
            continue
        out.append(a[i])
        i += 1
    return out


def runs_wanted(errata: list[Erratum], data: dict) -> list[dict]:
    """Every run the page verifies on native ecma-run: SpecTec's baked-in reading for each demonstration program."""
    by = {e.name: e for e in errata}
    want = []
    for name, progs in data["programs"].items():
        if name not in by:
            raise SystemExit(f"site/errata.json: no erratum {name}")
        e = by[name]
        for p in progs:
            f = program_file(p["program"])
            base = header_args(f.read_text(), name)
            for rd in p["outcomes"]:
                if rd not in READING_NAMES:
                    raise SystemExit(f"site/errata.json: {name} {p['program']}: no reading {rd}")
            if e.default not in p["outcomes"]:
                raise SystemExit(f"site/errata.json: {name} {p['program']}: no outcome for baked-in reading {e.default}")
            want.append({"erratum": name, "program": p["program"], "reading": e.default,
                         "args": base, "file": f.relative_to(ROOT).as_posix(),
                         "expect": p["outcomes"][e.default]})
    return want


def norm_line(s: str) -> str:
    return re.sub(r"#\d+\]", "#N]", s)


def run_one(ecma_run: Path, w: dict) -> dict:
    try:
        r = subprocess.run([str(ecma_run), *w["args"], w["file"]], cwd=ROOT, capture_output=True, text=True,
                           timeout=TIMEOUT)
        lines = r.stdout.rstrip("\n").split("\n")
        got = {"end": norm_line(lines[0]), "printed": [norm_line(x) for x in lines[1:]]}
    except subprocess.TimeoutExpired:
        got = {"end": "timeout", "printed": []}
    exp = {"end": w["expect"]["end"], "printed": w["expect"].get("printed", [])}
    return {**w, "got": got, "ok": got == exp}


def check_data(errata: list[Erratum], data: dict, sp: Text) -> list[str]:
    findings: list[str] = []
    for e in errata:
        quotes_of(e, sp, data.get("anchors", {}), findings)
    for name in data.get("anchors", {}):
        if name not in {e.name for e in errata}:
            raise SystemExit(f"site/errata.json: anchors for no erratum {name}")
    return findings


# ---------------------------------------------------------------------------------------------------------------
# The text's notation as HTML


def md(t: str, sp: Text | None = None, refs: bool = False) -> str:
    """spec.html's markup of a sentence as the site's HTML: ecmarkdown's emphasis, the
    inline grammar, cross-references by their clause number; `refs` keeps the notes' references to the
    project's own files, which the page otherwise leaves out."""
    holes: list[str] = []

    def hole(s: str) -> str:
        holes.append(s)
        return f"\x00{len(holes) - 1}\x00"

    if not refs:
        # A reference to a write-up the site publishes is a link to its page; any other reference to the
        # project's own files is left out.
        def writeup(m: re.Match) -> str:
            f = ROOT / "docs/spec-issues" / m.group(1)
            if not f.is_file():
                return ""
            return " (" + hole(f'<a href="spec-issues/{esc(f.stem)}.html">write-up {esc(f.name[:2])}</a>') + ")"

        t = re.sub(r"\s*\(docs/spec-issues/(\d\d-[\w-]+\.md)\)", writeup, t)
        t = re.sub(r"\s*\((?:docs/spec-issues/[^()]*|decisions\.md, <code>[^<]*</code>)\)", "", t)

    def xref(m: re.Match) -> str:
        target, inner = m.group(1), m.group(2)
        if inner.strip():
            return hole(md(inner, sp, refs))
        if sp and target in sp.nums:
            return hole(f"§{sp.nums[target]}")
        if sp:
            cl = sp.clause_of(target)
            if cl in sp.nums:
                return hole(f"a table of §{sp.nums[cl]}")
        return hole(esc(target))

    t = re.sub(r'<emu-xref href="#([^"]+)"[^>]*>(.*?)</emu-xref>', xref, t, flags=re.DOTALL)
    t = re.sub(r"<emu-grammar>(.*?)</emu-grammar>", lambda m: hole(f'<code class="grammar">{esc(html.unescape(m.group(1)))}</code>'), t, flags=re.DOTALL)
    t = re.sub(r"<code>(.*?)</code>", lambda m: hole(f"<code>{esc(html.unescape(m.group(1)))}</code>"), t, flags=re.DOTALL)
    t = re.sub(r"``\s*(.*?)\s*``", lambda m: hole(f"<code>{esc(html.unescape(m.group(1)))}</code>"), t)
    t = re.sub(r"`([^`]+)`", lambda m: hole(f"<code>{esc(html.unescape(m.group(1)))}</code>"), t)
    t = re.sub(r"<(/?)(sub|sup)>", lambda m: hole(f"<{m.group(1)}{m.group(2)}>"), t)
    t = re.sub(r"<[^>]+>", "", t)  # emu-meta, a, and the like: their text
    t = esc(html.unescape(t))
    t = re.sub(r"(?<![\w*])\*([^*\s](?:[^*]*?[^*\s])?)\*(?![\w*])", r'<span class="val">\1</span>', t)
    t = re.sub(r"(?<![\w])_([^_\s](?:[^_]*?[^_\s])?)_(?![\w])", r"<var>\1</var>", t)
    t = re.sub(r"(?<![\w~])~([\w-]+)~(?![\w~])", r'<span class="const">\1</span>', t)
    t = re.sub(r"\|([A-Z][A-Za-z]*(?:\[[^\]|]*\])?\??)\|", r'<span class="nt">\1</span>', t)
    t = re.sub(r"\s+", " ", t).strip()
    while "\x00" in t:
        t = re.sub(r"\x00(\d+)\x00", lambda m: holes[int(m.group(1))], t)
    return t


def alg_html(text: str, sp: Text | None, start: str | None = None) -> str:
    """An emu-alg's steps as nested ordered lists."""
    items: list[tuple[int, str]] = []
    for ln in text.split("\n"):
        m = re.match(r"^(\s*)(?:\d+|\*)\.\s+(.*)$", ln)
        if m:
            items.append((len(m.group(1)), re.sub(r"^\[[^\]]*\]\s*", "", m.group(2))))
    if not items:
        return ""
    out: list[str] = []
    stack: list[int] = []
    for ind, t in items:
        if not stack or ind > stack[-1]:
            depth = len(stack)
            style = ["decimal", "lower-alpha", "lower-roman"][depth % 3]
            out.append(f'<ol class="alg" style="list-style-type:{style}">')
            stack.append(ind)
        else:
            while stack and ind < stack[-1]:
                out.append("</li></ol>")
                stack.pop()
            out.append("</li>")
        out.append(f"<li>{md(t, sp)}")
    while stack:
        out.append("</li></ol>")
        stack.pop()
    return "".join(out)


def grammar_html(text: str) -> str:
    lines = [l for l in text.split("\n") if l.strip()]
    base = min(len(l) - len(l.lstrip()) for l in lines) if lines else 0
    return f'<pre class="grammar">{esc(html.unescape(chr(10).join(l[base:] for l in lines)))}</pre>'


# ---------------------------------------------------------------------------------------------------------------
# The page

READING_LABEL = {"literal": "the literal text", "test262": "the test262 reading", "proposed": "the proposed reading"}
LAYER = {
    "spec": ("Algorithm & early-error SpecTec",
             "Baked directly into the clause or early-error rules of <code>spec/spectec/</code>."),
    "parser": ("Grammar & parser",
               "Baked into the SpecTec grammars (<code>spec/spectec/01..07-grammar-*.spectec</code>) and the parser."),
    "none": ("Prose relations & unused rows",
             "Applies in the SpecTec prose model (<code>spec/spectec/prose/</code>) or an unreachable grammar row."),
}
STOP_KIND = {
    "sortError": "a value of the wrong sort reaches the step",
    "residue": "a step of the text with no reading the machine can run",
    "erratum": "the step this erratum names",
    "assertFailed": "a failed Assert",
    "implLimit": "an implementation limit of the engine",
}


def clause_link(sp: Text, cid: str, label: str | None = None) -> str:
    num = sp.nums.get(cid)
    text = label or (f"§{num} {sp.short(cid)}" if num else cid)
    return f'<a class="clause" href="{esc(CLAUSE_URL.format(cid))}">{esc(text)}</a>'


def site_html(sp: Text, site: str, path: str) -> str:
    """A machine site, `sec-id#k` and a step path, as a clause and a step."""
    cid = site.split("#")[0]
    if path in ("?", "-"):
        step = "" if path == "?" else ", the job loop's check of a Job's completion"
    else:
        own = path.split("..")[0]
        step = f", step {esc(own)}" + (" (inside the reading of that step)" if ".." in path else "")
    if cid in sp.nums:
        return clause_link(sp, cid) + step
    return f"<code>{esc(cid)}</code> (a helper clause of SpecTec){step}"


def outcome_html(sp: Text, end: str) -> str:
    m = re.match(r"stop: (erratum (\w+)|\w+) (\S+) (\S+)$", end)
    if m:
        kind = "erratum" if m.group(2) else m.group(1)
        return (f"<code>{esc(end)}</code>: stops at {site_html(sp, m.group(3), m.group(4))} "
                f"({STOP_KIND.get(kind, esc(kind))})")
    m = re.match(r"stop: (\w+)$", end)
    if m:
        return f"<code>{esc(end)}</code> ({STOP_KIND.get(m.group(1), esc(m.group(1)))})"
    return f"<code>{esc(end)}</code>"


def stops_html(sp: Text, e: Erratum) -> str:
    """What the text gives read as written, as the overlay records it (`stops`), or "" where it records none."""
    if e.stops is None:
        return ""
    if not e.stops:
        return "The text never stops a run."
    parts = []
    for s in e.stops:
        m = re.match(r"([^@]+)@([^\[]+)(?:\[([^\]]+)\])?$", s)
        cid, path, caller = m.group(1), m.group(2), m.group(3)
        where = clause_link(sp, cid) + (", the job loop's check of a Job's abrupt completion (§9.5)" if path == "-"
                                        else f", step {esc(path)}")
        if caller:
            where += f", when called from {clause_link(sp, caller)}"
        parts.append(where)
    return f"A run stops at {'; or at '.join(parts)}."


def quote_html(sp: Text, q: Quote) -> str:
    where = clause_link(sp, q.cid) + (f", {md(q.where, sp)}" if q.where else "")
    body = grammar_html(q.text) if q.block == "grammar" else f"<p>{md(q.text, sp)}</p>"
    return f'<blockquote class="sentence{" gram" if q.block == "grammar" else ""}"><cite>{where}</cite>{body}</blockquote>'


def alts_html(sp: Text, q: Quote) -> str:
    """The other readings of an anchor, one entry per text (two readings with the same text share one)."""
    groups: dict[str, list[str]] = {}
    for alt in q.alts:
        if alt.kind == "alg":
            body = alg_html(alt.text, sp)
        elif alt.kind == "grammar":
            body = grammar_html(alt.text)
        else:
            body = f"<p>{md(alt.text, sp)}</p>"
        groups.setdefault(body, []).extend(alt.readings)
    out = []
    for body, rds in groups.items():
        rds = [r for r in READING_NAMES if r in rds]
        label = ("The " + " and ".join(rds) + (" reading" if len(rds) == 1 else " readings"))
        out.append(f"<dt>{esc(label)}</dt><dd>{body}</dd>")
    return f'<dl class="readings">{"".join(out)}</dl>' if out else ""


def program_html(sp: Text, e: Erratum, p: dict, runs: dict, gallery: dict, builds: list[dict], run_name: str,
                 results_hrefs: list[str] | None = None) -> str:
    pid = p["program"]
    f = program_file(pid)
    rows = []
    for rd, exp in p["outcomes"].items():
        if rd == e.default:
            r = runs[(e.name, pid, rd)]
            end_s = r["got"]["end"]
            printed_lines = r["got"]["printed"]
            tag = "default"
            badge = " (baked into SpecTec · verified)"
        else:
            end_s = exp["end"]
            printed_lines = exp.get("printed", [])
            tag = "other"
            badge = " (alternative reading)"
        printed = "".join(f"<li><code>{esc(x)}</code></li>" for x in printed_lines)
        rows.append(f'<tr class="{tag}"><th scope="row">{READING_LABEL[rd][0].upper() + READING_LABEL[rd][1:]}'
                    f'{badge}</th>'
                    f'<td>{outcome_html(sp, end_s)}'
                    f'{f"<ul class=printed>{printed}</ul>" if printed else ""}</td></tr>')
    links = []
    ex = next((x for x in gallery.get("examples", []) if x["id"] == pid), None) if gallery else None
    by_id = {b["id"]: b for b in builds}
    if ex and builds:
        first = builds[0]["id"]
        for b in ex["builds"]:
            if b not in by_id:
                continue
            q = f"?example={pid}" + ("" if b == first else f"&amp;build={b}")
            links.append(f'<button type="button" class="open" data-dbg-open="debugger/{q}">Open in the debugger</button>')
    for rhref in (results_hrefs or []):
        links.append(f'<a class="open" href="{esc(rhref)}">Cross-engine runs</a>')
    args = header_args(f.read_text(), e.name)
    run_line = " ".join([run_name, *args, f.relative_to(ROOT).as_posix()])
    return (f'<div class="program"><p class="prog-head">The program <code>{esc(f.relative_to(ROOT).as_posix())}</code>'
            f', verified with <code class="cmd">{esc(run_line)}</code>:</p>'
            f'<div class="tablebox"><table class="outcomes"><tbody>{"".join(rows)}</tbody></table></div>'
            f'{"<p class=opens>" + " ".join(links) + "</p>" if links else ""}'
            f'<details class="jssrc"><summary>Source</summary><pre class="js">{esc(f.read_text())}</pre></details></div>')


def issue_example_html(ex: Path, builds: list[dict], unrunnable: dict[str, str], results_href: str, si_dir: Path) -> str:
    """Fallback program block when an erratum's program lives under docs/spec-issues/examples/."""
    files = sorted(p for p in ex.rglob("*") if p.is_file()) if ex.is_dir() else [ex]
    ident = ex.name if ex.is_dir() else ex.stem
    srcs = "".join(f'<details class="jssrc"><summary>Source <code>{esc(f.relative_to(si_dir).as_posix())}</code></summary>'
                   f'<pre class="js">{esc(f.read_text())}</pre></details>' for f in files)
    links = []
    if ident not in unrunnable and builds:
        links.append(f'<button type="button" class="open" data-dbg-open="debugger/?example={esc(ident)}">Open in the debugger</button>')
    links.append(f'<a class="open" href="{esc(results_href)}">Cross-engine runs</a>')
    kind = "Module graph" if ex.is_dir() else "Script"
    note = f' <span class="muted">(not offered in browser debugger: {esc(unrunnable[ident])})</span>' if ident in unrunnable else ""
    return (f'<div class="program"><p class="prog-head">Example ({kind}): '
            f'<code>docs/spec-issues/examples/{esc(ex.name)}</code>{note}</p>'
            f'<p class="opens">{" ".join(links)}</p>{srcs}</div>')


def writeups(e: Erratum) -> list[tuple[str, str]]:
    """The write-ups spec/DECISIONS.md names for an erratum, as (page under the site, its number and title)."""
    out = []
    for p in e.reports:
        w = ROOT / p
        if not w.is_file():
            raise SystemExit(f"{DECISIONS}: {e.name} names {p}, which is not there")
        title = re.sub(r"^#\s*", "", w.read_text().split("\n", 1)[0])
        out.append((f"spec-issues/{w.stem}.html", title))
    return out


def erratum_html(sp: Text, e: Erratum, quotes: list[Quote], data: dict, runs: dict, gallery: dict, builds: list[dict],
                 run_name: str, iss_for_e: list, recs: dict, unrunnable: dict[str, str], sip) -> str:
    wl = " ".join(f'<a class="open" href="spec-issues/{esc(i.slug)}.html">Write-up {i.num}: {sip.inline(i.title)} →</a>'
                  for i in iss_for_e) or "".join(f'<a class="open" href="{esc(href)}">Write-up {md(title)} →</a>'
                                                  for href, title in writeups(e))
    parts = [f'<article class="erratum" id="{esc(e.name)}"><h3><a class="self" href="#{esc(e.name)}">{esc(e.name)}</a></h3>',
             f'<p class="erratum-meta"><span class="badge rd">SpecTec: {esc(e.default)}</span>'
             f'<span class="badge sw-{e.switch}">layer: {esc(e.switch)}</span></p>',
             f'<p class="opens">{wl}</p>' if wl else ""]
    for q in quotes:
        if q.block == "none":
            parts.append(f'<p class="nosentence">{clause_link(sp, q.cid)} has {md(q.where, sp)}.</p>')
        else:
            parts.append(quote_html(sp, q))
        parts.append(alts_html(sp, q))
    notes = [n for q in quotes for n in q.notes] + e.notes
    if notes:
        parts.append('<div class="ov-note"><p class="ov-label">Formalization note</p>'
                     + "".join(f"<p>{md(n, sp)}</p>" for n in notes) + "</div>")
    facts = []
    st = stops_html(sp, e)
    if st:
        facts.append(f"<dt>Read as written</dt><dd>{st}</dd>")
    res = (f" Upstream resolution is <code>pending</code>; SpecTec bakes in {READING_LABEL[e.default]}."
           if e.resolution == "pending" else "")
    facts.append(f"<dt>In SpecTec</dt><dd>{READING_LABEL[e.default][0].upper() + READING_LABEL[e.default][1:]}.{res}</dd>")
    title, sentence = LAYER[e.switch]
    facts.append(f"<dt>Layer</dt><dd>{title}. {sentence}</dd>")
    ups = [re.sub(r'href="(\d\d-[\w-]+)\.md(#[^"]*)?"', r'href="spec-issues/\1.html\2"',
                  sip.upstream_html(i.header["Upstream"], recs.get(i.num, [])))
           for i in iss_for_e if "Upstream" in i.header]
    if ups:
        facts.append(f'<dt>Upstream</dt><dd>{"<br>".join(ups)}</dd>')
    parts.append(f'<dl class="split efacts">{"".join(facts)}</dl>')
    ex_issues = [i for i in iss_for_e if i.example]
    results_hrefs = [f"spec-issues/results.html#{sip.results_anchor(i.example.name)}" for i in ex_issues]
    progs = data["programs"].get(e.name, [])
    if progs:
        parts += [program_html(sp, e, p, runs, gallery, builds, run_name,
                               results_hrefs if idx == 0 else None) for idx, p in enumerate(progs)]
    elif ex_issues:
        parts += [issue_example_html(i.example, builds, unrunnable,
                                     f"spec-issues/results.html#{sip.results_anchor(i.example.name)}", sip.si.DIR)
                  for i in ex_issues]
    else:
        parts.append('<p class="noprog">No JavaScript program on this site shows this erratum (an axiomatic §29 relation).</p>')
    parts.append("</article>")
    return "\n".join(x for x in parts if x)


def page(runs_file: dict, gallery: dict | None, builds: list[dict], run_name: str, sp: Text | None = None) -> dict:
    """errata.html's title, lede, body and table of contents — unified with the spec-issue index and upstream data."""
    import spec_issue_pages as sip
    errata = read_errata()
    data = json.loads(DATA.read_text())
    sp = sp or Text()
    findings: list[str] = []
    want = runs_wanted(errata, data)
    runs = {}
    for r in runs_file["runs"]:
        runs[(r["erratum"], r["program"], r["reading"])] = r
    for w in want:
        r = runs.get((w["erratum"], w["program"], w["reading"]))
        if not r or r["args"] != w["args"] or r["expect"] != w["expect"]:
            raise SystemExit(f"errata runs: {w['erratum']} {w['program']} [{w['reading']}] was not run as the data has it "
                             "(scripts/errata_page.py run)")
        if not r["ok"]:
            raise SystemExit(f"errata runs: {w['erratum']} {w['program']} [{w['reading']}] failed its check")
    gallery = gallery or {}
    defects = [e for e in errata if e.kind == "defect"]
    proposals = [e for e in errata if e.kind == "proposal"]
    if len(defects) + len(proposals) != len(errata):
        raise SystemExit("errata: a kind neither defect nor proposal")

    all_issues = sip.si.issues()
    iss_by_err: dict[str, list] = {}
    for i in all_issues:
        for ename in i.errata:
            iss_by_err.setdefault(ename, []).append(i)
    recs = sip.upstream.by_writeup()
    try:
        import dbg_spec_examples
        unrunnable = dict(dbg_spec_examples.UNRUNNABLE)
    except ImportError:
        unrunnable = {}

    def has_any_prog(e: Erratum) -> bool:
        return bool(data["programs"].get(e.name)) or any(i.example for i in iss_by_err.get(e.name, []))

    def table(es: list[Erratum]) -> str:
        trs = []
        for e in es:
            q = quotes_of(e, sp, data.get("anchors", {}), findings)[0]
            num = sp.nums.get(q.cid, "")
            cl_cell = (f'<a class="clause" href="{esc(CLAUSE_URL.format(q.cid))}"><span class="secnum">{esc(num)}</span> '
                       f'{esc(sp.short(q.cid))}</a>' if num else esc(sp.short(q.cid)))
            iss_e = iss_by_err.get(e.name, [])
            w_cell = "<br>".join(f'<a href="spec-issues/{esc(i.slug)}.html">{i.num}. {sip.inline(i.title)}</a>'
                                 for i in iss_e)
            up_parts = [u for i in iss_e if (u := sip.upstream_summary(i.header.get("Upstream", ""), recs.get(i.num, [])))]
            up_cell = "<br>".join(dict.fromkeys(up_parts))
            prog = "yes" if has_any_prog(e) else ""
            plain_q = " ".join([
                e.name, q.cid, num, sp.short(q.cid), e.default, e.switch,
                *(f"{i.num} {i.title} {i.header.get('Upstream', '')}" for i in iss_e),
            ]).lower()
            trs.append(f'<tr data-q="{esc(plain_q)}">'
                       f'<td class="tname"><a href="#{esc(e.name)}"><code>{esc(e.name)}</code></a></td>'
                       f'<td class="tclause">{cl_cell}</td>'
                       f'<td class="twriteup">{w_cell}</td>'
                       f'<td class="trd"><span class="badge rd">{esc(e.default)}</span> '
                       f'<span class="badge sw-{e.switch}">{esc(e.switch)}</span></td>'
                       f'<td class="up">{up_cell}</td>'
                       f'<td class="num">{prog}</td></tr>')
        return ('<div class="tablebox"><table class="errata-index"><thead><tr><th>Erratum</th><th>Clause</th>'
                '<th>Write-up</th><th>SpecTec</th><th>Upstream</th><th class="num">Program</th>'
                '</tr></thead><tbody>' + "".join(trs) + "</tbody></table></div>")

    def section(sid: str, title: str, es: list[Erratum], intro: str, with_filter: bool = False) -> str:
        flt = (f'<div class="filter"><label for="lawfilter">Filter the {len(errata)} entries</label>'
               f'<input id="lawfilter" type="search" placeholder="a clause, an erratum, a write-up, an upstream PR" '
               f'autocomplete="off"><span class="filter-count" aria-live="polite"></span></div>'
               if with_filter else "")
        arts = [erratum_html(sp, e, quotes_of(e, sp, data.get("anchors", {}), findings), data, runs, gallery, builds,
                             run_name, iss_by_err.get(e.name, []), recs, unrunnable, sip) for e in es]
        return (f'<section class="part" id="{sid}"><h2 class="part-title"><a class="self" href="#{sid}">{esc(title)} '
                f'({len(es)})</a></h2>{intro}{flt}{table(es)}{"".join(arts)}</section>')

    from collections import Counter
    dflt = Counter(e.default for e in errata)
    sw = Counter(e.switch for e in errata)
    with_prog = sum(1 for e in errata if has_any_prog(e))
    nruns = len(want)
    checked = ", ".join(sorted({r.checked_on for v in recs.values() for r in v})) or "no date"
    eng_list = [a for a, _ in sip.engines() if not a.startswith("the formal model")]
    eng_items = "".join(f"<li><strong>{esc(a)}</strong>: {sip.inline(b)}</li>"
                        for a, b in sip.engines() if not a.startswith("the formal model"))
    eng_items += ("<li><strong>The formal model</strong>: <code>ecma-run</code>, built from this repository at the "
                  "commit this site was built from.</li>")
    pin = sip.subprocess_out(["git", "-C", str(ECMA262), "rev-parse", "--short=9", "HEAD"])
    t262 = sip.subprocess_out(["git", "-C", str(ROOT / "external/test262"), "rev-parse", "--short=8", "HEAD"])

    tiles = (f'<ul class="facts" aria-label="Summary">'
             f'<li><b>{len(errata)}</b><span>Specification decisions ({len(defects)} defects, {len(proposals)} proposals)</span></li>'
             f'<li><b>{len(all_issues)}</b><span>Long-form write-ups (<code>docs/spec-issues/</code>)</span></li>'
             f'<li><b>{with_prog}</b><span>Entries with runnable example programs</span></li>'
             f'<li><b>{len(eng_list) + 1}</b><span>Engines compared in <a href="spec-issues/results.html">recorded runs</a></span></li>'
             f'</ul>')

    how = (f'<section class="part" id="reading"><h2 class="part-title"><a class="self" href="#reading">How to read this '
           f'page</a></h2>'
           f'<p>Each entry names the sentences of ECMA-262 (at <code>{esc(pin)}</code>) it concerns, quoted from the '
           f'pinned <code>spec.html</code> (every step, grammar production, or rule checked by SHA-256 hash or '
           f'normalized text when the site builds), alongside its candidate readings: <em>the literal text</em> as '
           f'written; <em>the test262 reading</em> required by <code>test262</code> (at <code>{esc(t262)}</code>); and '
           f'<em>the proposed reading</em> drafted in its place. SpecTec bakes one resolved reading directly into '
           f'<code>spec/spectec/</code> and records every non-literal choice in <code>spec/DECISIONS.md</code>: across '
           f'the {len(errata)} entries, {dflt.get("test262", 0)} follow <code>test262</code>, {dflt.get("proposed", 0)} '
           f'bake in a proposed fix, and {dflt.get("literal", 0)} keep the literal wording ({sw.get("spec", 0)} in '
           f'algorithms and early errors, {sw.get("parser", 0)} in the grammars and parser, and {sw.get("none", 0)} in '
           f'prose relations).</p>'
           f'<p>Every entry links to its long-form committee write-up (<code>docs/spec-issues/NN-*.md</code>), which '
           f'traces the issue step by step from the specification text alone, tracks upstream <code>tc39/ecma262</code> '
           f'and <code>tc39/test262</code> issues and pull requests (checked {esc(checked)} in '
           f'<code>docs/spec-issues/upstream.tsv</code>), and proposes an editorial change.</p>'
           f'<p>{with_prog} of the {len(errata)} entries have a runnable JavaScript example: {len(data["programs"])} '
           f'are verified on native <code>{esc(run_name)}</code> ({nruns} runs checked at build time, with object '
           f'addresses normalized to <code>#N</code>), and the write-ups\' examples are also recorded across '
           f'<a href="spec-issues/results.html">all four engines</a>:</p>'
           f'<ul>{eng_items}</ul></section>')
    body = [tiles, how,
            section("defects", "Defects of the text", defects,
                    "<p>Places where the text, read as written, gives no answer, an answer that contradicts another "
                    "sentence, or an answer test262 does not accept — including every place where SpecTec bakes in a "
                    "non-literal choice so the formal specification and reference engine are well-defined.</p>",
                    with_filter=True),
            section("proposals", "Proposed normative changes", proposals,
                    "<p>Not a defect: the text is consistent, and the change alters what it requires (such as "
                    "finite resource limits for BigInts and Strings or pre-Unicode-15.1 identity escapes).</p>")]
    toc = [("reading", "How to read this page", 1), ("defects", f"Defects of the text ({len(defects)})", 1)]
    toc += [(e.name, esc(e.name), 2) for e in defects]
    toc += [("proposals", f"Proposed normative changes ({len(proposals)})", 1)]
    toc += [(e.name, esc(e.name), 2) for e in proposals]
    lede = (f"<p>All {len(errata)} specification defects, non-literal SpecTec readings, and proposed normative changes "
            f"encountered when formalizing ECMA-262 ({len(defects)} defects of the text and {len(proposals)} "
            f"proposed normative change{'s' if len(proposals) != 1 else ''}, paired with {len(all_issues)} long-form "
            f"write-ups): the sentences quoted from <code>spec.html</code>, the reading baked into "
            f"<code>spec/spectec/</code>, upstream TC39 status, and verified demonstration programs.</p>")
    return {"title": "Spec issues & errata",
            "eyebrow": "Specification issues &amp; decisions · <code>spec/DECISIONS.md</code>, "
                       "<code>docs/spec-issues/</code>",
            "lede": lede, "body": "\n".join(body), "toc": toc,
            "findings": sorted(set(findings)),
            "counts": {"errata": len(errata), "defects": len(defects), "proposals": len(proposals),
                       "runs": nruns, "with_program": with_prog, "writeups": len(all_issues)}}


# ---------------------------------------------------------------------------------------------------------------
# CLI


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="run every program the page states an outcome of")
    r.add_argument("--ecma-run", type=Path, default=ROOT / ".lake/build/bin/ecma-run")
    r.add_argument("--out", type=Path, required=True)
    r.add_argument("-j", "--jobs", type=int, default=3)
    sub.add_parser("check", help="check the data and the quotations")
    a = ap.parse_args()
    errata = read_errata()
    data = json.loads(DATA.read_text())
    sp = Text()
    findings = check_data(errata, data, sp)
    for f in findings:
        print(f"note: {f}")
    if a.cmd == "check":
        print(f"ok   errata: {len(errata)}, the quotations checked")
        return 0
    want = runs_wanted(errata, data)
    with ThreadPoolExecutor(a.jobs) as ex:
        got = list(ex.map(lambda w: run_one(a.ecma_run, w), want))
    bad = [g for g in got if not g["ok"]]
    for g in bad:
        print(f"FAIL {g['erratum']} {g['program']} [{g['reading']}]: {' '.join(g['args'])}\n"
              f"     expected {g['expect']}\n     got      {g['got']}")
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps({"ecma_run": str(a.ecma_run), "runs": got}, indent=1, ensure_ascii=False) + "\n")
    print(f"{'FAIL' if bad else 'ok  '} errata programs: {len(got)} runs, {len(bad)} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
