#!/usr/bin/env python3
"""The errata as a page: from the overlay's own data, each quotation checked against spec.html, each program run.

    python3 scripts/errata_page.py run --ecma-run .lake/build/bin/ecma-run --out build/errata-runs.json [-j 3]
    python3 scripts/errata_page.py check                     # the data and the quotations, no run

The errata are spec/formal/readings.emu's `<emu-erratum>` elements with spec/formal/errata.txt's columns (the
resolution, `kind`, `switch`, where the literal text stops) and the default reading the generated data applies
(`Ecma.Gen.parity` in lean/Ecma/Gen/Decls.lean). For each erratum the page quotes the text it is about from
external/ecma262/spec.html:

- an `emu-reading` of a step: the step's text, found by its path and checked by the hash the overlay gives
  (SHA-256 of the step's text, as crates/spec-gen computes it);
- an `emu-reading` of an early-error rule: the rule's bullet, checked the same way;
- an `emu-rule-reading`: the grammar rule's definition, checked by its hash (scripts/jsgrammar.py's);
- an `emu-orphan-row`: the equation row the grammar has no production for;
- an erratum with none of these (its readings are a note): the sentences `site/errata.json` names under
  `anchors`, each checked to occur in its clause as the laws' quotations are (scripts/law_quotes.py).

`site/errata.json` also names, under `programs`, the programs that show an erratum (tests/run, tests/dbg,
tools/dbg/demo; the debugger's example ids), each with the outcome it must have under each reading it is run
under: the default reading, and the literal one (or, where the default is the literal text, the erratum's other
reading). `run` runs each on the native ecma-run, with the program's header arguments (tests/run's
`// module:` and `// args:`, without the ones that set this erratum's reading) and `--erratum NAME=READING`,
and fails unless every outcome is the one recorded (`[object #N]` stands for any object number). It writes
the runs for `scripts/site_pages.py --errata-runs`, which writes errata.html and checks that the runs are of
the data as it is.

Each erratum links to its write-ups (docs/spec-issues/NN-*.md, errata.txt's last column), which the site publishes
under spec-issues/ (scripts/spec_issue_pages.py); the overlay's notes cite them in parentheses, and those
references become links to the same pages (the notes' references to decisions.md are left out). The list of
errata that earlier reviews removed because the editors fixed the text is docs/spec-issues/README.md's "Fixed
upstream": the names and the upstream commits, each commit checked to be one of external/ecma262 before the
pinned one when the clone has the history, and each name a retired erratum id.
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

ROOT = Path(__file__).resolve().parent.parent
READINGS = ROOT / "spec/formal/readings.emu"
ERRATA = ROOT / "spec/formal/errata.txt"
IDS = ROOT / "spec/formal/erratum-ids.txt"
DECLS = ROOT / "lean/Ecma/Gen/Decls.lean"
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
# The overlay's data


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
    switch: str
    stops: list[str] | None  # None: not given; []: never stops
    default: str
    anchors: list[Anchor]
    notes: list[str]


def attrs_of(s: str) -> dict[str, str]:
    return {k: html.unescape(v) for k, v in re.findall(r'([\w-]+)="([^"]*)"', s)}


def notes_in(body: str) -> list[str]:
    return [p for n in re.findall(r"<emu-note>(.*?)</emu-note>", body, re.DOTALL)
            for p in re.findall(r"<p>(.*?)</p>", n, re.DOTALL)]


def parity() -> dict[str, str]:
    """Each erratum's default reading, as the generated data has it (`Ecma.Gen.errata`, `Ecma.Gen.parity`)."""
    src = DECLS.read_text()

    def array(name: str) -> list[str]:
        m = re.search(r"(?m)^def " + name + r" : Array \w+ :=\n(.*?)(?=\n\n|\n/--)", src, re.DOTALL)
        if not m:
            raise SystemExit(f"{DECLS}: no def {name}")
        return re.findall(r'"([^"]*)"' if name == "errata" else r"\.(\w+)", m.group(1))

    names, rd = array("errata"), array("parity")
    if len(names) != len(rd):
        raise SystemExit(f"{DECLS}: {len(names)} errata, {len(rd)} parities")
    return dict(zip(names, rd))


def read_errata() -> list[Erratum]:
    rows = {}
    for ln in ERRATA.read_text().split("\n"):
        if ln.strip() and not ln.startswith("#"):
            f = ln.split("\t")
            rows[f[0]] = f
    par = parity()
    src = READINGS.read_text()
    out = []
    for m in re.finditer(r"<emu-erratum\b([^>]*)>(.*?)</emu-erratum>", src, re.DOTALL):
        a = attrs_of(m.group(1))
        body = m.group(2)
        name = a["name"]
        anchors = []
        for r in re.finditer(r"<(emu-reading|emu-rule-reading)\b([^>]*)>(.*?)</\1>|<(emu-orphan-row)\b([^>]*)></emu-orphan-row>",
                             body, re.DOTALL):
            if r.group(4):
                anchors.append(Anchor(r.group(4), attrs_of(r.group(5))))
                continue
            an = Anchor(r.group(1), attrs_of(r.group(2)), notes=notes_in(r.group(3)))
            for alt in re.finditer(r'<(emu-alg|p|emu-grammar)\b([^>]*)\breading="([^"]+)"[^>]*>(.*?)</\1>', r.group(3), re.DOTALL):
                kind = {"emu-alg": "alg", "p": "p", "emu-grammar": "grammar"}[alt.group(1)]
                an.alts.append(Alt(alt.group(3).split(), kind, alt.group(4)))
            anchors.append(an)
        rest = re.sub(r"<(emu-reading|emu-rule-reading)\b.*?</\1>", "", body, flags=re.DOTALL)
        row = rows.get(name)
        if not row:
            raise SystemExit(f"{ERRATA}: no row for {name}")
        res, kind, switch, stops = row[1], row[2], row[3], row[4]
        if res != a.get("resolution") or kind != a.get("kind", "defect") or switch != a.get("switch", "spec"):
            raise SystemExit(f"{name}: errata.txt and readings.emu differ (run `spec-gen errata -check`)")
        st = None if stops == "-" else [] if stops == "none" else stops.split()
        if name not in par:
            raise SystemExit(f"{name}: not in Ecma.Gen.errata")
        out.append(Erratum(name, res, kind, switch, st, par[name], anchors, notes_in(rest)))
    if len(out) != len(rows):
        raise SystemExit(f"readings.emu has {len(out)} errata, errata.txt {len(rows)}")
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
    """Every run the page states: (erratum, program, reading, its arguments, the recorded outcome)."""
    by = {e.name: e for e in errata}
    want = []
    for name, progs in data["programs"].items():
        if name not in by:
            raise SystemExit(f"site/errata.json: no erratum {name}")
        for p in progs:
            f = program_file(p["program"])
            base = header_args(f.read_text(), name)
            for rd, exp in p["outcomes"].items():
                if rd not in READING_NAMES:
                    raise SystemExit(f"site/errata.json: {name} {p['program']}: no reading {rd}")
                want.append({"erratum": name, "program": p["program"], "reading": rd,
                             "args": base + ["--erratum", f"{name}={rd}"], "file": f.relative_to(ROOT).as_posix(),
                             "expect": exp})
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
    fixed_upstream()
    return findings


# ---------------------------------------------------------------------------------------------------------------
# What earlier reviews removed


def fixed_upstream() -> list[dict]:
    """docs/spec-issues/README.md's "Fixed upstream": the errata and the commits that fixed their text, each
    commit checked to be of external/ecma262 and before the pinned one, each name a retired erratum id."""
    t = ISSUES.read_text()
    m = re.search(r"(?ms)^## Fixed upstream\n(.*?)(?=^## |\Z)", t)
    if not m:
        raise SystemExit(f"{ISSUES}: no section Fixed upstream")
    pin = re.search(r"Fixed in `([0-9a-f]+)`", m.group(1))
    retired = {ln.split("\t")[1] for ln in IDS.read_text().split("\n") if ln.endswith("\tretired")}
    out = []
    for item in re.findall(r"(?ms)^- (.*?)(?=^- |\Z)", m.group(1)):
        item = re.sub(r"\s+", " ", item).strip()
        im = re.match(r"\[\d+\]\([^)]*\): (.*?), by ([0-9a-f]{7,40}) \((.*?)\)\.?$", item)
        if not im:
            raise SystemExit(f"{ISSUES}: an entry of Fixed upstream not read: {item!r}")
        names = re.split(r",? and |, ", im.group(1))
        for n in names:
            if n not in retired:
                raise SystemExit(f"{ISSUES}: {n} is no retired erratum id ({IDS.name})")
        commit = im.group(2)
        full = subprocess.run(["git", "-C", str(ECMA262), "rev-parse", "--verify", "--quiet", commit + "^{commit}"],
                              capture_output=True, text=True).stdout.strip()
        shallow = subprocess.run(["git", "-C", str(ECMA262), "rev-parse", "--is-shallow-repository"],
                                 capture_output=True, text=True).stdout.strip() == "true"
        if full:
            anc = subprocess.run(["git", "-C", str(ECMA262), "merge-base", "--is-ancestor", full, "HEAD"])
            if anc.returncode != 0:
                raise SystemExit(f"{ISSUES}: {commit} is not before the pinned external/ecma262")
        elif not shallow:
            raise SystemExit(f"{ISSUES}: {commit} is no commit of external/ecma262")
        # A shallow checkout of external/ecma262 has no history to check the commit against: it is linked as given.
        prs = re.findall(r"PR #(\d+)", im.group(3))
        out.append({"names": names, "commit": full or commit, "short": commit, "prs": prs, "checked": bool(full)})
    return out


# ---------------------------------------------------------------------------------------------------------------
# The text's notation as HTML


def md(t: str, sp: Text | None = None, refs: bool = False) -> str:
    """spec.html's (or the overlay's) markup of a sentence as the site's HTML: ecmarkdown's emphasis, the
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
SWITCH = {
    "spec": ("In the specification, at run time",
             "Its readings are a parameter of the specification's machine: <code>{run} --erratum {name}=READING</code> "
             "runs a program under one of them ({readings}), and the engine's theorem holds under every choice."),
    "parser": ("Only in the engine's parser",
               "The specification's grammar (<code>lean/Ecma/Grammar/Gen</code>) has the default reading; the engine's "
               "parser has both, and <code>{run} --erratum {name}=literal</code> parses as the text is written. The "
               "literal reading is the engine's parser's, not the specification layer's."),
    "none": ("Nowhere",
             "The overlay holds one reading, and no option changes it."),
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
    return f"<code>{esc(cid)}</code> (a reading of the overlay){step}"


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


def program_html(sp: Text, e: Erratum, p: dict, runs: dict, gallery: dict, builds: list[dict], run_name: str) -> str:
    pid = p["program"]
    f = program_file(pid)
    rows = []
    for rd in p["outcomes"]:
        r = runs[(e.name, pid, rd)]
        tag = "default" if rd == e.default else "other"
        printed = "".join(f"<li><code>{esc(x)}</code></li>" for x in r["got"]["printed"])
        rows.append(f'<tr class="{tag}"><th scope="row">{READING_LABEL[rd][0].upper() + READING_LABEL[rd][1:]}'
                    f'{" (the default)" if rd == e.default else ""}<br><code class="cmd">--erratum {esc(e.name)}={rd}</code></th>'
                    f'<td>{outcome_html(sp, r["got"]["end"])}'
                    f'{f"<ul class=printed>{printed}</ul>" if printed else ""}</td></tr>')
    other = [rd for rd in p["outcomes"] if rd != e.default]
    links = []
    ex = next((x for x in gallery.get("examples", []) if x["id"] == pid), None) if gallery else None
    by_id = {b["id"]: b for b in builds}
    if ex:
        first = builds[0]["id"]
        for b in ex["builds"]:
            if b not in by_id:
                continue
            q = f"?example={pid}" + ("" if b == first else f"&amp;build={b}")
            links.append(f'<a class="open" href="debugger/{q}">Open in the debugger: {esc(by_id[b]["label"])}</a>')
            if b == first:
                for rd in other:
                    args = f"--erratum {e.name}={rd}".replace(" ", "%20").replace("=", "%3D")
                    links.append(f'<a class="open" href="debugger/{q}&amp;args={args}">Open in the debugger: '
                                 f'{esc(by_id[b]["label"])}, with {esc(READING_LABEL[rd])}</a>')
    args = header_args(f.read_text(), e.name)
    run_line = " ".join([run_name, *args, f.relative_to(ROOT).as_posix()])
    return (f'<div class="program"><p class="prog-head">The program <code>{esc(f.relative_to(ROOT).as_posix())}</code>'
            f', run as <code class="cmd">{esc(run_line)}</code> with the option of each row:</p>'
            f'<div class="tablebox"><table class="outcomes"><tbody>{"".join(rows)}</tbody></table></div>'
            f'{"<p class=opens>" + " ".join(links) + "</p>" if links else ""}'
            f'<details class="jssrc"><summary>Source</summary><pre class="js">{esc(f.read_text())}</pre></details></div>')


def writeups(name: str) -> list[tuple[str, str]]:
    """The write-ups errata.txt names for an erratum, as (page under the site, its number and title)."""
    out = []
    for ln in ERRATA.read_text().split("\n"):
        f = ln.split("\t")
        if ln.startswith("#") or len(f) < 6 or f[0] != name:
            continue
        for p in f[5].split():
            w = ROOT / p
            if not w.is_file():
                raise SystemExit(f"{ERRATA}: {name} names {p}, which is not there")
            title = re.sub(r"^#\s*", "", w.read_text().split("\n", 1)[0])
            out.append((f"spec-issues/{w.stem}.html", title))
    return out


def erratum_html(sp: Text, e: Erratum, quotes: list[Quote], data: dict, runs: dict, gallery: dict, builds: list[dict],
                 run_name: str) -> str:
    wl = "".join(f'<a class="open" href="{esc(href)}">Write-up {md(title)}</a>' for href, title in writeups(e.name))
    parts = [f'<article class="erratum" id="{esc(e.name)}"><h3><a class="self" href="#{esc(e.name)}">{esc(e.name)}</a></h3>',
             f'<p class="erratum-meta"><span class="badge rd">default: {esc(e.default)}</span>'
             f'<span class="badge sw-{e.switch}">switched: {esc(e.switch)}</span></p>',
             f'<p class="opens">{wl}</p>' if wl else ""]
    for q in quotes:
        if q.block == "none":
            parts.append(f'<p class="nosentence">{clause_link(sp, q.cid)} has {md(q.where, sp)}.</p>')
        else:
            parts.append(quote_html(sp, q))
        parts.append(alts_html(sp, q))
    notes = [n for q in quotes for n in q.notes] + e.notes
    if notes:
        parts.append('<div class="ov-note"><p class="ov-label">The overlay\'s note</p>'
                     + "".join(f"<p>{md(n, sp)}</p>" for n in notes) + "</div>")
    facts = []
    st = stops_html(sp, e)
    if st:
        facts.append(f"<dt>Read as written</dt><dd>{st}</dd>")
    res = (f" The overlay's resolution is <code>{esc(e.resolution)}</code>: not yet decided; the machine runs "
           f"{READING_LABEL[e.default]} until it is." if e.resolution == "pending" else "")
    facts.append(f"<dt>Default</dt><dd>{READING_LABEL[e.default][0].upper() + READING_LABEL[e.default][1:]}.{res}</dd>")
    title, sentence = SWITCH[e.switch]
    rds = ", ".join(f"<code>{r}</code>" for r in ["literal", *other_readings(e)])
    facts.append(f"<dt>Switched</dt><dd>{title}. {sentence.format(run=run_name, name=esc(e.name), readings=rds)}</dd>")
    parts.append(f'<dl class="split efacts">{"".join(facts)}</dl>')
    progs = data["programs"].get(e.name, [])
    if progs:
        parts += [program_html(sp, e, p, runs, gallery, builds, run_name) for p in progs]
    else:
        parts.append('<p class="noprog">No program on this site shows this erratum.</p>')
    parts.append("</article>")
    return "\n".join(x for x in parts if x)


def page(runs_file: dict, gallery: dict | None, builds: list[dict], run_name: str, sp: Text | None = None) -> dict:
    """errata.html's title, lede, body and table of contents. `runs_file` is `run`'s output, which must be of
    the data as it is and have passed."""
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

    def table(es: list[Erratum]) -> str:
        trs = []
        for e in es:
            q = quotes_of(e, sp, data.get("anchors", {}), findings)[0]
            num = sp.nums.get(q.cid, "")
            n = len(data["programs"].get(e.name, []))
            trs.append(f'<tr><td><a href="#{esc(e.name)}"><code>{esc(e.name)}</code></a></td>'
                       f'<td><span class="secnum">{esc(num)}</span> {esc(sp.short(q.cid))}</td>'
                       f'<td>{esc(e.default)}</td><td>{esc(e.switch)}</td><td class="num">{"yes" if n else ""}</td></tr>')
        return ('<div class="tablebox"><table class="errata-index"><thead><tr><th>Erratum</th><th>Clause</th>'
                '<th>Default</th><th>Switched</th><th class="num">Program</th></tr></thead><tbody>'
                + "".join(trs) + "</tbody></table></div>")

    def section(sid: str, title: str, es: list[Erratum], intro: str) -> str:
        arts = [erratum_html(sp, e, quotes_of(e, sp, data.get("anchors", {}), findings), data, runs, gallery, builds,
                             run_name) for e in es]
        return (f'<section class="part" id="{sid}"><h2 class="part-title"><a class="self" href="#{sid}">{esc(title)} '
                f'({len(es)})</a></h2>{intro}{table(es)}{"".join(arts)}</section>')

    from collections import Counter
    dflt = Counter(e.default for e in errata)
    sw = Counter(e.switch for e in errata)
    with_prog = sum(1 for e in errata if data["programs"].get(e.name))
    nruns = len(want)
    fixed = fixed_upstream()
    nfixed = sum(len(x["names"]) for x in fixed)
    how = (f'<section class="part" id="reading"><h2 class="part-title"><a class="self" href="#reading">How to read an '
           f'erratum</a></h2>'
           f'<p>Each erratum names the sentences of the text it is about, quoted from the pinned spec.html (a step or a '
           f'rule is found by the hash the overlay records of its text, so a change to the text fails the build), '
           f'and the readings the overlay holds: <em>the literal text</em>, the sentence as written; <em>the test262 '
           f'reading</em>, the one test262\'s tests require; <em>the proposed reading</em>, the text proposed in its '
           f'place. Where two readings have the same text, it is given once. The notes are the overlay\'s own.</p>'
           f'<p>Of the {len(errata)} errata, {dflt.get("test262", 0)} are read by default as test262 requires, '
           f'{dflt.get("literal", 0)} as written and {dflt.get("proposed", 0)} as proposed. {sw.get("spec", 0)} are '
           f'switched in the specification at run time, {sw.get("parser", 0)} only in the engine\'s parser, and '
           f'{sw.get("none", 0)} have one reading.</p>'
           f'<p>{with_prog} errata have a program that shows them. Each program was run when this site was built, '
           f'{nruns} runs in all on the native <code>{esc(run_name)}</code>, under its erratum\'s default reading and '
           f'under its other reading (the literal text, or, where the default is the literal text, the proposed or '
           f'test262 reading), and printed what the page says. An object\'s number in a result line is written '
           f'<code>#N</code>.</p></section>')
    body = [how,
            section("defects", "Defects of the text", defects,
                    "<p>Places where the text, read as written, gives no answer, an answer that contradicts another "
                    "sentence, or an answer test262 does not accept.</p>"),
            section("proposals", "Proposed normative changes", proposals,
                    "<p>Not a defect: the text is consistent, and the change would alter what it requires.</p>")]
    items = []
    for x in fixed:
        prs = ", ".join(f'<a href="{PR_URL.format(n)}">#{n}</a>' for n in x["prs"])
        items.append(f'<li>{" and ".join(f"<code>{esc(n)}</code>" for n in x["names"])}: fixed by '
                     f'<a href="{COMMIT_URL.format(x["commit"])}"><code>{esc(x["short"])}</code></a>'
                     f'{" (" + prs + ")" if prs else ""}.</li>')
    pin = subprocess.run(["git", "-C", str(ECMA262), "rev-parse", "--short=9", "HEAD"], capture_output=True,
                         text=True).stdout.strip()
    body.append(f'<section class="part" id="removed"><h2 class="part-title"><a class="self" href="#removed">Removed '
                f'because the editors fixed the text ({nfixed})</a></h2><p>Errata an earlier review of the overlay '
                f'held, and removed when the text at <code>{esc(pin)}</code> no longer had the defect. Their ids stay '
                f'retired in <code>spec/formal/erratum-ids.txt</code>.</p><ul class="fixed">{"".join(items)}</ul></section>')
    toc = [("reading", "How to read an erratum", 1), ("defects", f"Defects of the text ({len(defects)})", 1)]
    toc += [(e.name, esc(e.name), 2) for e in defects]
    toc += [("proposals", f"Proposed normative changes ({len(proposals)})", 1)]
    toc += [(e.name, esc(e.name), 2) for e in proposals]
    toc += [("removed", f"Removed: fixed upstream ({nfixed})", 1)]
    lede = (f"<p>The places where the overlay reads the text of ECMA-262 in more than one way: {len(defects)} defects "
            f"of the text and {len(proposals)} proposed normative change{'s' if len(proposals) != 1 else ''}, from <code>spec/formal/readings.emu</code>. "
            f"For each, the sentences it is about, what they give read as written, the other readings, which one the "
            f"machine runs by default, where the choice is made, and a program that shows the difference.</p>")
    return {"title": "Errata", "eyebrow": "From the overlay: <code>spec/formal/readings.emu</code>, "
            "<code>spec/formal/errata.txt</code>", "lede": lede, "body": "\n".join(body), "toc": toc,
            "findings": sorted(set(findings)), "counts": {"errata": len(errata), "defects": len(defects),
                                             "proposals": len(proposals), "runs": nruns, "with_program": with_prog}}


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
