#!/usr/bin/env python3
"""The laws' quotations, checked against the specification.

    python3 scripts/law_quotes.py [--show ID] [-v]

Every docstring of a field under lean/Ecma/Host/Laws/ and of lean/Ecma/Model/Laws.lean is read as the
convention has it: the id of a clause (or table, note, …) of the text's spec.html (`scripts/spec_text.py`) with a step or
paragraph, the governing sentence quoted in double quotes, then `Reading:` and one line; or, where no sentence
governs, `No sentence:` and why. A quotation may be several, each on lines of its own, and one may begin with
another id and a colon to be looked for in that clause instead. An ellipsis (… or ...) in a quotation skips
text: the parts around it must occur in that order. The check fails unless every part of every quotation
occurs in the text of its clause, tags stripped, entities decoded, ecmarkdown's emphasis (`_x_`, `*x*`, `~x~`,
`|X|`, backquotes) and white space dropped, on both sides. `--show ID` prints a clause's text so read.
"""

import argparse
import html
import re
import sys
from pathlib import Path

import spec_text

ROOT = Path(__file__).resolve().parent.parent
# the spec.html read: the text (scripts/spec_text.py) unless a caller sets another
SPEC: Path | None = None
FILES = sorted((ROOT / "lean/Ecma/Host/Laws").glob("*.lean")) + [ROOT / "lean/Ecma/Model/Laws.lean"]

ID = r"(?:sec|table|figure|note|prod|eqn|step)-[A-Za-z0-9_.%-]+"


def norm(t: str) -> str:
    """Text as the check compares it."""
    t = re.sub(r"<[^>]*>", " ", t)
    t = html.unescape(t)
    t = t.replace("“", '"').replace("”", '"').replace("’", "'").replace("‘", "'")
    t = re.sub(r"[_*~|`]", "", t)
    # White space is the markup's as often as the text's (`+0<sub>𝔽</sub>`): it is not compared.
    return re.sub(r"\s+", "", t)


class Spec:
    def __init__(self) -> None:
        self.src = (SPEC or spec_text.spec_html()).read_text()
        self.cache: dict[str, str | None] = {}

    def raw(self, cid: str) -> str | None:
        m = re.search(r'<([a-z-]+)\b[^>]*\bid="' + re.escape(cid) + r'"', self.src)
        if not m:
            return None
        tag, start, depth = m.group(1), m.start(), 0
        for t in re.finditer(r"<(/?)" + re.escape(tag) + r"\b[^>]*>", self.src[start:]):
            depth += -1 if t.group(1) else 1
            if depth == 0:
                return self.src[start : start + t.end()]
        return self.src[start:]

    def text(self, cid: str) -> str | None:
        if cid not in self.cache:
            r = self.raw(cid)
            self.cache[cid] = None if r is None else norm(r)
        return self.cache[cid]


def docstrings(path: Path):
    """(line, name, docstring) of each field: a `/-- … -/` followed by `name :`."""
    src = path.read_text()
    for m in re.finditer(r"/--((?:(?!-/).)*?)-/\s*\n\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", src, re.S):
        yield src.count("\n", 0, m.start()) + 1, m.group(2), m.group(1)


def quotes(doc: str):
    """The clause id and the quotations of a docstring; `None` for a `No sentence:` law."""
    body = re.split(r"\n\s*(?:Reading:|No sentence:)", doc, maxsplit=1)
    head = body[0]
    if "No sentence:" in doc and '"' not in head:
        return None, []
    m = re.match(r"\s*(" + ID + r")", head)
    cid = m.group(1) if m else None
    qs = []
    for q in re.finditer(r'(?:^|\n)\s*(?:(' + ID + r'):\s*)?"(.*?)"\s*(?=\n|$)', head, re.S):
        qs.append((q.group(1) or cid, q.group(2)))
    return cid, qs


def check(spec: Spec, cid: str | None, q: str) -> str | None:
    """Why the quotation `q` is not in the clause `cid`, or None."""
    if cid is None:
        return "no clause id"
    t = spec.text(cid)
    if t is None:
        return f"no element with id {cid}"
    pos = 0
    for part in re.split(r"\s*(?:…|\.\.\.)\s*", q):
        p = norm(part)
        if not p:
            continue
        i = t.find(p, pos)
        if i < 0:
            return f"not in {cid}: {p[:90]!r}"
        pos = i + len(p)
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--show")
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    spec = Spec()
    if a.show:
        r = spec.raw(a.show)
        print(r and re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]*>", " ", r))))
        return 0
    bad = laws = nosent = 0
    for f in FILES:
        for line, name, doc in docstrings(f):
            laws += 1
            if "Reading:" not in doc and "No sentence:" not in doc:
                print(f"FAIL {f.relative_to(ROOT)}:{line} {name}: no `Reading:` or `No sentence:`")
                bad += 1
                continue
            cid, qs = quotes(doc)
            if cid is None and not qs:
                nosent += 1
                if a.v:
                    print(f"no sentence {f.relative_to(ROOT)}:{line} {name}")
                continue
            if not qs:
                print(f"FAIL {f.relative_to(ROOT)}:{line} {name}: no quotation")
                bad += 1
            for c, q in qs:
                why = check(spec, c, q)
                if why:
                    print(f"FAIL {f.relative_to(ROOT)}:{line} {name}: {why}")
                    bad += 1
    print(f"{'FAIL' if bad else 'ok  '} law quotations: {laws} laws, {nosent} with no sentence, {bad} failing")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
