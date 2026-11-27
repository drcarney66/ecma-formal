#!/usr/bin/env python3
"""The site's pages: the reading pages generated from the Lean, the hand-written pages, the frame.

    python3 scripts/site_pages.py --out DIR [--spec spec.html] [--test262-record RECORD] [--errata-runs RUNS.json]
        [--examples EXAMPLES.json --builds BUILDS.json [--checked CHECK.json]...] [--debugger]
    python3 scripts/site_pages.py --check DIR

Writes into DIR: `index.html`, `how-it-works.html`, `what-is-proved.html` (site/*.html, their `{{…}}` filled with
numbers computed from the tree), the reading pages `model.html`, `host.html`, `implements.html`,
`parser-laws.html` (scripts/render_lean.py over lean/Ecma), `test262.html` from a test262 run's record
(scripts/test262_report.py), `errata.html` from the errata programs' runs (scripts/errata_page.py),
`examples.html` when examples are given (scripts/dbg_gallery.py's examples.json,
with the table of builds and the results of their check, tools/dbg/ui/gallery_test.mjs --json), the debugger's
page `debugger/index.html` with --debugger (tools/dbg/ui/index.html's body under the site's header; the
debugger's files beside it are scripts/build_site.py's), and `style.css`, `site.js` (site/). Needs no Lean build:
it reads sources only. Every Lean name a hand-written page cites in <code> must be declared under lean/.

`--check DIR` checks a built site, the debugger's directory included: every page well formed, every internal
link and anchor resolves, no page, script or stylesheet loads anything from another origin, and no page uses a
retired name. It runs after every build too.
"""

from __future__ import annotations

import argparse
import html
import json
import html.parser
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import errata_page
import proposal_record
import law_quotes
import render_lean as rl
import spec_text
import spec_issue_pages
import test262_report

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
LEAN = ROOT / "lean"

# The working title, in one place, and the executables by the names they are about to get.
SITE_NAME = "ECMA-262 in Lean"
BASE_PATH = "/ecma-formal/"
RUN = "ecma-run"
DBG = "ecma-dbg"
BUNDLE = "ecma-bundle"

# Retired names no page may use (checked on the built text).
RETIRED = [r"\bESL\b", r"\besl\b", r"\bB0'?\b", r"\bB1'?\b", r"\bb1p\b", r"[Tt]he meaning\b", r"\bthe Sem\b"]

# Source docstrings that still use a retired name: what the page says in their place. Each must still match its
# source (the build fails once the source is fixed, so that the entry is removed).
REWORD: list[tuple[str, str, str]] = [
    ("lean/Ecma/Machine/Run.lean",
     "the program's code, the host and the readings, and nothing else.",
     "the program's code, the host, and whether Asserts are checked."),
]

# The pages, in three dropdown menus next to the site's name. Home is the site's name.
NAV = [
    ("Read", [("how-it-works.html", "How it works"), ("what-is-proved.html", "What is proved"),
              ("errata.html", "Errata"), ("spec-issues/", "Spec issues"),
              ("proposal.html", "Applying a proposal"), ("test262.html", "test262"),
              ("slides.html", "TC39 #117 slides")]),
    ("The Specification", [("model.html", "The model"), ("host.html", "The host"), ("implements.html", "Implements"),
                           ("parser-laws.html", "Parser laws")]),
    ("Try it", [("examples.html", "Examples"), ("debugger/", "Debugger")]),
]
DBG_UI = ROOT / "tools/dbg/ui/index.html"


# ---------------------------------------------------------------------------------------------------------------
# Facts from the tree


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()


def lean_lines(d: Path, *, skip_gen: bool = True, only: str | None = None, exclude: str | None = None) -> tuple[int, int]:
    """(files, lines) of the .lean files under `d`."""
    files = lines = 0
    for f in sorted(d.rglob("*.lean")):
        rel = f.relative_to(d).as_posix()
        if skip_gen and "/Gen/" in "/" + rel:
            continue
        if only and not rel.startswith(only):
            continue
        if exclude and rel.startswith(exclude):
            continue
        files += 1
        lines += f.read_text().count("\n")
    return files, lines


def gen_lines(d: Path) -> tuple[int, int]:
    fs = sorted(d.glob("*.lean"))
    return len(fs), sum(f.read_text().count("\n") for f in fs)


def spectec_counts() -> dict[str, int]:
    """Files and lines of `spec/spectec/` (structured SpecTec vs `prose/` modules) and `spec/html/`."""
    spec_dir = ROOT / "spec/spectec"
    struct_fs = [f for f in sorted(spec_dir.rglob("*.spectec")) if "prose" not in f.parts]
    prose_fs = sorted((spec_dir / "prose").glob("*.spectec"))
    clause_fs = sorted((spec_dir / "clauses").glob("*.spectec"))
    html_fs = sorted((ROOT / "spec/html").glob("*.txt"))
    defs = sum(len(re.findall(r"(?m)^def @", f.read_text())) for f in struct_fs)
    return {
        "struct_files": len(struct_fs),
        "struct_lines": sum(f.read_text().count("\n") for f in struct_fs),
        "prose_files": len(prose_fs),
        "prose_lines": sum(f.read_text().count("\n") for f in prose_fs),
        "total_files": len(struct_fs) + len(prose_fs),
        "total_lines": sum(f.read_text().count("\n") for f in struct_fs + prose_fs),
        "clause_files": len(clause_fs),
        "defs": defs,
        "html_files": len(html_fs),
        "html_lines": sum(f.read_text().count("\n") for f in html_fs),
    }


def errata() -> dict[str, int]:
    """`spec/DECISIONS.md`'s 38 errata counted by baked-in reading (`test262`, …), resolution (`res:pending`, …),
    kind (`kind:defect`, …) and layer (`switch:spec`, …)."""
    out: dict[str, int] = {}
    for e in errata_page.read_errata():
        for k in (e.default, "res:" + e.resolution, "kind:" + e.kind, "switch:" + e.switch):
            out[k] = out.get(k, 0) + 1
    return out


def pins() -> int:
    """The `native_decide` pins: each `pin_alg`, `pin_prog_alg` and `pin_true` declaration (Proofs/Pins/Pin.lean)."""
    n = 0
    for f in (LEAN / "Engine").rglob("*.lean"):
        if f.name == "Pin.lean":
            continue
        n += len(re.findall(r"(?m)^\s*(?:pin_alg|pin_prog_alg|pin_true|pin)\s+[A-Za-z_]", f.read_text()))
    # The axiom check recorded in lean/Engine/Claims.lean counts the same pins; a difference is a stale page.
    rec = re.search(r"(\d+)\s+`native_decide` pins", (LEAN / "Engine/Claims.lean").read_text())
    if not rec or int(rec.group(1)) != n:
        raise SystemExit(f"pins: {n} pin declarations, but lean/Engine/Claims.lean records {rec and rec.group(1)}")
    return n


def axioms() -> list[str]:
    """The standard axioms the headline theorems depend on, as lean/Engine/Claims.lean records the axiom check."""
    t = (LEAN / "Engine/Claims.lean").read_text()
    m = re.search(r"Axioms of `Engine.implements` and of `Engine.run_sound`: (.*?) and \d+\s+`native_decide` pins", t)
    if not m:
        raise SystemExit("lean/Engine/Claims.lean: no recorded axiom check")
    return re.findall(r"`([^`]+)`", m.group(1))


def runtime_pins() -> int:
    """The pinned program equations checked at run time (`class PinsHold` in `lean/Engine/Pins.lean`)."""
    src = (LEAN / "Engine/Pins.lean").read_text()
    m = re.search(r"(?m)^class PinsHold : Prop where\n(.*?)(?=\n\n)", src, re.DOTALL)
    if not m:
        raise SystemExit("lean/Engine/Pins.lean: no class PinsHold")
    n = len(re.findall(r"(?m)^\s+[A-Za-z_]\w*\s*:", m.group(1)))
    if n <= 0:
        raise SystemExit("lean/Engine/Pins.lean: no fields in class PinsHold")
    return n


def statement(path: Path, name: str) -> str:
    """A theorem's statement as written: from `theorem name` to its `:=` or `where`."""
    src = path.read_text()
    m = re.search(r"(?m)^theorem " + re.escape(name) + r"\b", src)
    if not m:
        raise SystemExit(f"{path}: no theorem {name}")
    end = re.search(r":=|\swhere\s*\n", src[m.start():])
    return src[m.start() : m.start() + end.start()].rstrip()


def need_theorem(full: str) -> None:
    """`full` is a theorem of the engine's sources (for a status line that names it)."""
    last = full.split(".")[-1]
    for f in (LEAN / "Engine").rglob("*.lean"):
        if re.search(r"(?m)^theorem " + re.escape(last) + r"\b", f.read_text()):
            return
    raise SystemExit(f"status names {full}, which is no theorem under lean/Engine")


# ---------------------------------------------------------------------------------------------------------------
# The frame


def nav_html(here: str, pages: set[str], prefix: str = "") -> str:
    menus = []
    for title, items in NAV:
        lis = []
        for href, label in items:
            if href not in pages:
                continue
            cur = ' aria-current="page"' if href == here else ""
            lis.append(f'<li><a href="{prefix}{href}"{cur}>{html.escape(label)}</a></li>')
        if lis:
            cur = " here" if any(href == here for href, _ in items) else ""
            menus.append(f'<details class="nav-menu{cur}"><summary>{html.escape(title)}</summary><ul>{"".join(lis)}</ul></details>')
    return "".join(menus)


def bar_html(here: str, pages: set[str], prefix: str = "") -> str:
    """The site's header: the name, the three dropdown menus beside it, and the theme switch on the far right."""
    return f"""<header class="bar">
<div class="bar-in">
<a class="brand" href="{prefix}index.html">{html.escape(SITE_NAME)}</a>
<nav class="site" aria-label="Pages">{nav_html(here, pages, prefix)}</nav>
<button class="theme theme-sm" type="button" id="theme" aria-label="Toggle dark mode" title="Toggle dark mode">
<svg viewBox="0 0 20 20" width="14" height="14" aria-hidden="true"><circle cx="10" cy="10" r="7.25" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M10 2.75a7.25 7.25 0 0 1 0 14.5z" fill="currentColor"/></svg></button>
</div>
</header>"""


ICON = '<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27%3E%3Ctext x=%276%27 y=%2725%27 font-family=%27Georgia,serif%27 font-size=%2726%27 fill=%27%231c5d99%27%3E%C2%A7%3C/text%3E%3C/svg%3E">'
THEME = ('<script>document.documentElement.classList.add("js");try{var t=localStorage.getItem("theme");'
         'document.documentElement.setAttribute("data-theme",t==="dark"?"dark":"light")}catch(e){'
         'document.documentElement.setAttribute("data-theme","light")}</script>')


@dataclass
class Page:
    file: str
    title: str
    eyebrow: str
    lede: str
    body: str
    toc: list[tuple[str, str, int]] = field(default_factory=list)  # (anchor, label, level)
    wide: bool = False
    nav: str | None = None  # the navigation's entry for the page (default: its file)
    prefix: str | None = None  # the path to the site's root (default: from the file's directory; "/" for 404.html)


def frame(p: Page, pages: set[str], facts: dict) -> str:
    toc = ""
    if p.toc:
        items = "".join(f'<li class="t{lvl}"><a href="#{html.escape(a)}">{lab}</a></li>' for a, lab, lvl in p.toc)
        toc = (f'<nav class="toc" aria-label="On this page"><details open id="toc-details"><summary>On this page'
               f'</summary><ol>{items}</ol></details></nav>')
    title = SITE_NAME if p.file == "index.html" else f"{re.sub(r'<[^>]+>', '', html.unescape(p.title))} · {SITE_NAME}"
    pre = p.prefix if p.prefix is not None else "../" * p.file.count("/")
    is_slides = p.file == "slides.html"
    ver_q = f"?v={html.escape(facts['rev'])}" if facts.get("rev") else ""
    coi_tag = f'<script src="{pre}coi-serviceworker.js{ver_q}"></script>\n' if p.file != "404.html" else ""
    head_block = "" if is_slides else f"""<header class="title">
<p class="eyebrow">{p.eyebrow}</p>
<h1>{p.title}</h1>
{f'<div class="lede">{p.lede}</div>' if p.lede else ''}
</header>"""
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<meta name="color-scheme" content="light dark">
{ICON}
{coi_tag}<link rel="stylesheet" href="{pre}style.css{ver_q}">
{THEME}
<script src="{pre}site.js{ver_q}" defer></script>
</head>
<body{' class="slides-body"' if is_slides else ''}>
<a class="skip" href="#main">Skip to the text</a>
{bar_html(p.nav or p.file, pages, pre)}
<div class="page{' wide' if p.wide else ''}{' slides-page' if is_slides else ''}{' has-toc' if p.toc else ''}">
{toc}
<main id="main">
{head_block}
{p.body}
</main>
</div>
<footer class="foot">
<div class="foot-in">
<p>{html.escape(SITE_NAME)} (a working title). Built from this repository at <code>{facts['rev']}</code>{' (with uncommitted changes)' if facts['dirty'] else ''};
the specification at tc39/ecma262 <code>{facts['ecma262'][:9]}</code>, the tests at tc39/test262 <code>{facts['test262'][:9]}</code>.
Clause links go to the living draft at tc39.es, which may differ from the pinned text; clause numbers are the pinned text's.</p>
</div>
</footer>
</body>
</html>
"""


def debugger_frame(pages: set[str], gallery: dict | None, rev: str = "") -> str:
    """The debugger's page, debugger/index.html: tools/dbg/ui/index.html's body under the site's header, the
    debugger's files (ui/, the Worker build, builds.json, examples.json) beside it."""
    src = DBG_UI.read_text()
    m = re.search(r"<body([^>]*)>(.*)</body>", src, re.DOTALL)
    if not m or 'src="app.mjs"' not in m.group(2):
        raise SystemExit(f"{DBG_UI}: no body with app.mjs")
    attrs = m.group(1)
    if 'class="dbg"' not in attrs:
        raise SystemExit(f"{DBG_UI}: the body is not class=\"dbg\"")
    ver_q = f"?v={html.escape(rev)}" if rev else ""
    ver_attr = f' data-version="{html.escape(rev)}"' if rev else ""
    body = m.group(2).replace('src="app.mjs"', f'src="ui/app.mjs{ver_q}"')
    noscript = ('<noscript><p class="dbg-noscript">The debugger is a script. Every example\'s source, and what it '
                'shows, is on the <a href="../examples.html">examples page</a>.</p></noscript>') if gallery else ""
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Debugger · {html.escape(SITE_NAME)}</title>
<meta name="color-scheme" content="light dark">
{ICON}
<!-- Cross-origin isolation from the site-root service worker where the server gives none; a no-op where it does. -->
<script src="../coi-serviceworker.js{ver_q}"></script>
<link rel="stylesheet" href="../style.css{ver_q}">
<link rel="stylesheet" href="ui/style.css{ver_q}">
{THEME}
<script src="../site.js{ver_q}" defer></script>
</head>
<body{attrs} data-root="./" data-engine="worker"{ver_attr}>
{bar_html("debugger/", pages, "../")}
{noscript}
{body.strip()}
</body>
</html>
"""


# ---------------------------------------------------------------------------------------------------------------
# The examples page


def example_anchor(eid: str) -> str:
    return "ex-" + re.sub(r"[^A-Za-z0-9_-]", "-", eid)


def check_line(c: dict) -> str:
    """What an example's check requires under a build (tools/dbg/ui/gallery.mjs `summary`)."""
    at = [f"<code>{html.escape(p['alg'])} {html.escape(p['path'])}</code>" for p in c["pauses"]]
    printed = ""
    if c.get("printed"):
        printed = "; prints " + ", ".join(f"<code>{html.escape(x)}</code>" for x in c["printed"])
    return (f"{'pauses at ' + ', then '.join(at) + '; ' if at else ''}ends <code>{html.escape(c['end'])}</code>{printed}")


def examples_page(gallery: dict, builds: list[dict], checked: list[dict], facts: dict,
                  more: dict[str, str] | None = None) -> tuple[str, str, list]:
    """`more`: HTML after a group's intro, by group id (the proposal group's link to its page)."""
    """The body of examples.html, its lede and its table of contents."""
    by_id = {b["id"]: b for b in builds}
    first = builds[0]["id"]
    ran: dict[tuple[str, str], list[str]] = {}
    for c in checked:
        for r in c["results"]:
            if not r["ok"]:
                raise SystemExit(f"examples: {r['id']} [{r['build']}] failed its check on {c['transport']}: {r['why']}")
            ran.setdefault((r["id"], r["build"]), []).append(c["transport"])
    names = {"native": "the native debugger", "wasm-node": "the WebAssembly build in node"}
    toc, parts = [], []
    for g in gallery["groups"]:
        exs = [e for e in gallery["examples"] if e["group"] == g["id"]]
        exs = [e for e in exs if any(b in by_id for b in e["builds"])]
        if not exs:
            continue
        toc.append((g["id"], html.escape(g["title"]), 1))
        items = []
        for e in exs:
            primary_q = None
            checks = []
            for b, c in e["builds"].items():
                if b not in by_id:
                    continue
                if primary_q is None:
                    primary_q = f"?example={e['id']}" + ("" if b == first else f"&amp;build={b}")
                where = ran.get((e["id"], b))
                if checked and not where:
                    raise SystemExit(f"examples: {e['id']} [{b}] was not checked")
                checks.append(f'<li><span class="build">{html.escape(by_id[b]["label"])}</span>: {check_line(c)}.</li>')
            open_p = (f'<p class="opens"><button type="button" class="open" data-dbg-open="debugger/{primary_q}">'
                      f'Open in the debugger</button></p>') if primary_q else ""
            args = (f'<p class="args">Run with <code>{html.escape(" ".join(e["args"]))}</code>.</p>' if e["args"] else "")
            bps = ", ".join(f"<code>{html.escape(x['alg'])}{(' ' + html.escape(x['path'])) if x.get('path') else ''}</code>"
                            for x in e["breakpoints"])
            setup = []
            if bps:
                setup.append(f"breakpoints at {bps}")
            if e["filters"]:
                setup.append("pauses on " + ", ".join({"stop": "the machine's stops", "throw": "throw completions",
                                                         "debugger": "debugger statements"}[f] for f in e["filters"]))
            setup_p = f'<p class="setup">Opened with {"; ".join(setup)}.</p>' if setup else ""
            items.append(f"""<article class="example" id="{example_anchor(e['id'])}">
<h3><a class="self" href="#{example_anchor(e['id'])}">{html.escape(e['title'])}</a></h3>
<p class="what">{html.escape(e['line'])}</p>
{open_p}
{setup_p}{args}<ul class="checks">{''.join(checks)}</ul>
<details class="jssrc" open><summary>Source <code>{html.escape(e['file'])}</code></summary><pre class="js">{html.escape(e['source'])}</pre></details>
</article>""")
        parts.append(f'<section class="part" id="{g["id"]}"><h2 class="part-title"><a class="self" href="#{g["id"]}">'
                     f'{html.escape(g["title"])}</a></h2><p>{html.escape(g["intro"])}</p>{(more or {}).get(g["id"], "")}'
                     f'{"".join(items)}</section>')
    n = sum(1 for e in gallery["examples"] for b in e["builds"] if b in by_id)
    how = ""
    if checked:
        how = (f" Each was run, under each build it names, on {' and on '.join(names[c['transport']] for c in checked)} "
               f"when this site was built, and reached what its check below says.")
    builds_list = "".join(f'<li><strong>{html.escape(b["label"])}.</strong> {html.escape(b["description"])}</li>' for b in builds)
    lede = (f"<p>{len(gallery['examples'])} programs that open in the <a href=\"debugger/\">debugger</a> with their "
            f"breakpoints set, {n} runs in all.{how}</p>")
    body = (f'<p>The debugger runs one of these builds, chosen in its header:</p><ul class="builds">{builds_list}</ul>'
            + "".join(parts))
    return body, lede, toc


# ---------------------------------------------------------------------------------------------------------------
# The reading pages


@dataclass
class Section:
    anchor: str
    title: str
    files: list[str]
    intro: str = ""  # HTML before the modules
    after: str = ""  # HTML after them


def status_lines() -> dict[str, str]:
    """What is proved of each structure of laws, by the engine's theorem that proves it (checked to exist)."""
    def c(x: str) -> str:
        return f"<code>{x}</code>"

    proved = '<span class="badge proved">Proved</span> '
    owed = '<span class="badge owed">Owed</span> '
    none = '<span class="badge none">No claim</span> '
    st = {
        "Ecma.Model.Laws": (proved + "of the engine's model: " + c("Engine.Impl.laws") + ", the first part of "
                            "<a href=\"implements.html#Implements.model\">" + c("Implements.model") + "</a>.",
                            ["Engine.Impl.laws"]),
        "Ecma.Model.NumLaws": (proved + "as part of " + c("Model.Laws") + " (its field " + c("num") + ").", []),
        "Ecma.Model.ByteLaws": (proved + "as part of " + c("Model.Laws") + " (its field " + c("bytes") + ").", []),
        "Ecma.Model.UnicodeLaws": (proved + "of the engine's model: " + c("Engine.Impl.unicodeLaws") + ", part of "
                                   "<a href=\"implements.html#Implements.model\">" + c("Implements.model")
                                   + "</a>.", ["Engine.Impl.unicodeLaws"]),
        "Ecma.Model.ParentLaws": (proved + "of the engine's model: " + c("Engine.Impl.parentLaws") + ", part of "
                                  "<a href=\"implements.html#Implements.model\">" + c("Implements.model")
                                  + "</a>.", ["Engine.Impl.parentLaws"]),
        "Ecma.Host.WF": (proved + "of the engine's host under every option set: " + c("Engine.SpecHost.wfBy")
                         + ", which is <a href=\"implements.html#Implements.host\">" + c("Implements.host") + "</a>.",
                         ["Engine.SpecHost.wfBy"]),
        "Ecma.Model.ParseLaws": (proved + "of the engine's model, for the specification's grammar under the engine's "
                                 "readings: " + c("Engine.Claims.parseLaws") + ". Not a field of "
                                 + c("Implements") + ".", ["Engine.Claims.parseLaws"]),
        "Ecma.Model.CoverLaws": (proved + "of the engine's model, for the specification's grammar under the engine's "
                                 "readings: " + c("Engine.Claims.coverLaws") + ". Not a field of "
                                 + c("Implements") + ".", ["Engine.Claims.coverLaws"]),
        "Ecma.Model.NodeLaws": (proved + "of the engine's model, for the specification's grammar under the engine's "
                                "readings: " + c("Engine.Claims.nodeLaws") + ". Not a field of "
                                + c("Implements") + ".", ["Engine.Claims.nodeLaws"]),
    }
    for t in ["JobLaws", "TimeLaws", "MemoryLaws", "RegExpLaws", "OrderLaws", "LocaleLaws", "OptionalLaws",
              "ValueLaws", "HookLaws", "ChangeLaws"]:
        st[f"Ecma.Host.{t}"] = (proved + "as part of <a href=\"#Host.WF\">" + c("Host.WF") + "</a>.", [])
    out = {}
    for k, (text, thms) in st.items():
        for t in thms:
            need_theorem(t)
        out[k] = text
    return out


# Laws whose reading is known to differ from their sentence.
DIFFERS = {
    "Ecma.Host.RegExpLaws.escapePattern": ("stricter", ("requires <code>\\/</code> and the line terminators' escapes, "
                                           "where the text also allows <code>/</code>")),
    "Ecma.Host.OptionalLaws.nativeFunctionSource": ("stricter", ("one form, <code>function name() { [native code] }"
                                                    "</code>, where the text allows any NativeFunction")),
    "Ecma.Host.ChangeLaws.collect": ("weaker", "liveness's second condition, about future executions, is left out"),
    "Ecma.Host.JobLaws.agentNextJob": ("weaker", "there is no law about a timeout"),
}


class Site:
    def __init__(self, spec_path: Path) -> None:
        law_quotes.SPEC = spec_path
        self.spec = rl.SpecText()
        self.index = rl.Index()
        self.modules: dict[str, rl.Module] = {}
        self.findings: list[str] = []
        self.reword_used: set[int] = set()
        self.status = status_lines()

    def module(self, rel: str) -> rl.Module:
        if rel not in self.modules:
            m = rl.parse_file(ROOT / rel)
            for k, (f, old, new) in enumerate(REWORD):
                if f != rel:
                    continue
                for it in m.items:
                    for attr in ("text", "doc"):
                        v = getattr(it, attr, None)
                        if v and old in v:
                            setattr(it, attr, v.replace(old, new))
                            self.reword_used.add(k)
            self.modules[rel] = m
        return self.modules[rel]

    def register(self, page: str, sections: list[Section]) -> None:
        for s in sections:
            for f in s.files:
                self.index.add_module(self.module(f), page)

    def render(self, page: str, sections: list[Section], opts: rl.Options) -> tuple[str, list, rl.Renderer]:
        r = rl.Renderer(self.spec, self.index, page, opts)
        body, toc = [], []
        for s in sections:
            toc.append((s.anchor, html.escape(s.title), 1))
            parts = [(f'<section class="part" id="{s.anchor}"><h2 class="part-title"><a class="self" '
                     f'href="#{s.anchor}">{html.escape(s.title)}</a></h2>'), s.intro]
            for f in s.files:
                parts.append(f'<div class="module"><p class="module-src">From <code>{f}</code></p>'
                             f'{r.module(self.module(f), heading=2, skip_first_title=True)}</div>')
            parts.append(s.after + "</section>")
            body.append("\n".join(parts))
        r.check_laws()
        self.findings += r.findings + r.prose.unlinked
        return "\n".join(body), toc, r


def host_sections() -> list[Section]:
    prose_dir = ROOT / "spec/spectec/prose"
    wf_src = (prose_dir / "26-host-laws.spectec").read_text()
    topics = re.findall(r"H\.(\w+)", wf_src.split("extends", 1)[1])
    files = {}
    for f in sorted(prose_dir.glob("*-host-laws-*.spectec")):
        m = re.search(r"(?m)^\s*laws\s+Host\.(\w+)", f.read_text())
        if m:
            files[m.group(1)] = f"spec/spectec/prose/{f.name}"
    secs = [Section("host", "The host", ["spec/spectec/prose/10-host.spectec"]),
            Section("laws", "The laws of a host", ["spec/spectec/prose/26-host-laws.spectec"])]
    for t in topics:
        if t not in files:
            raise SystemExit(f"Host.WF extends {t}, which no *-host-laws-*.spectec file defines")
        title = re.search(r"---!\s*#\s*([^\n]+)", (ROOT / files[t]).read_text()).group(1).strip()
        secs.append(Section(t, title[0].upper() + title[1:], [files[t]]))
    rest = [("basic", "spec/spectec/prose/14-host-laws-basic.spectec"),
            ("dateformat", "spec/spectec/prose/15-date-format.spectec")]
    for anchor, f in rest:  # Basic (what the laws are stated over), DateFormat (definitions only)
        title = re.search(r"---!\s*#\s*([^\n]+)", (ROOT / f).read_text()).group(1).strip()
        secs.append(Section(anchor, title[0].upper() + title[1:], [f]))
    return secs


def law_table(r: rl.Renderer, spec: rl.SpecText) -> str:
    rows = []
    for d, m, law in r.laws:
        if not d.full.startswith("Ecma.Host."):
            continue
        cl = '<span class="muted">No sentence</span>'
        if law.cid:
            num = spec.nums.get(law.cid, "")
            cl = (f'<a class="clause" href="{rl.CLAUSE_URL.format(law.cid)}"><span class="secnum">{num}</span> '
                  f'{html.escape(spec.short_title(law.cid))}</a>')
        diff = DIFFERS.get(f"{d.full}.{m.name}")
        flag = f'<br><span class="badge {diff[0]}">{diff[0]}</span>' if diff else ""
        topic = d.name.split(".")[-1].removesuffix("Laws")
        text = re.sub(r"<[^>]+>", "", r.prose.inline(law.reading, d.ns))
        rows.append(f'<tr data-q="{html.escape((m.name + " " + (law.cid or "") + " " + spec.short_title(law.cid or "") + " " + text).lower())}">'
                    f'<td class="tname"><a href="#{m.anchor}"><code>{m.name}</code></a>{flag}</td>'
                    f'<td class="ttopic">{topic}</td><td class="tclause">{cl}</td>'
                    f'<td class="tread">{r.prose.inline(rl._cap(law.reading), d.ns)}</td></tr>')
    return (f'<div class="lawtable" id="summary"><div class="filter"><label for="lawfilter">Filter the '
            f'{len(rows)} laws</label><input id="lawfilter" type="search" placeholder="a clause, a word, a name" '
            f'autocomplete="off"><span class="filter-count" aria-live="polite"></span></div>'
            f'<div class="tablebox"><table><thead><tr><th>Law</th><th>Topic</th><th>Clause</th><th>Reading</th>'
            f'</tr></thead><tbody>{"".join(rows)}</tbody></table></div></div>'), len(rows)


def differs_list() -> str:
    items = []
    for full, (kind, why) in DIFFERS.items():
        a = rl.anchor_of(full)
        items.append(f'<li><a href="#{a}"><code>{a.split(".")[-1]}</code></a> '
                     f'<span class="badge {kind}">{kind}</span> {why}.</li>')
    return "<ul class=\"differs\">" + "".join(items) + "</ul>"


# ---------------------------------------------------------------------------------------------------------------
# Hand-written pages: site/*.html with `{{name}}` filled


def fill(text: str, values: dict[str, str], where: str) -> str:
    used: set[str] = set()

    def sub(m: re.Match) -> str:
        k = m.group(1)
        if k not in values:
            raise SystemExit(f"{where}: unknown placeholder {{{{{k}}}}}")
        used.add(k)
        return values[k]

    return re.sub(r"\{\{([\w.:'-]+)\}\}", sub, text)


def read_template(name: str) -> tuple[dict[str, str], str]:
    """A hand-written page: `<!-- key: value -->` lines (title, eyebrow, lede), then its body."""
    src = (SITE / name).read_text()
    meta = dict(re.findall(r"<!--\s*(\w+):\s*(.*?)\s*-->", src.split("\n\n", 1)[0], re.DOTALL))
    body = src.split("\n\n", 1)[1]
    return meta, body


def toc_of(body: str) -> list[tuple[str, str, int]]:
    out = []
    for m in re.finditer(r'<h([23])[^>]*\bid="([^"]+)"[^>]*>(.*?)</h\1>', body, re.DOTALL):
        label = re.sub(r"<[^>]+>", "", m.group(3)).strip()
        out.append((m.group(2), html.escape(html.unescape(label)), int(m.group(1)) - 1))
    return out


def fmt(n: int) -> str:
    return f"{n:,}"


# ---------------------------------------------------------------------------------------------------------------
# The build


_LEAN_NAMES: set[str] | None = None
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|public)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[]+)")


def lean_names() -> set[str]:
    """The full names the Lean sources declare, roughly: declarations under their namespaces, a structure's
    fields and an inductive's constructors (for the hand-written pages' check of the names they cite)."""
    global _LEAN_NAMES
    if _LEAN_NAMES is not None:
        return _LEAN_NAMES
    names: set[str] = set()
    for f in LEAN.rglob("*.lean"):
        ns: list[str] = []
        owner: str | None = None
        for ln in f.read_text().split("\n"):
            m = re.match(r"^namespace\s+([\w.«»]+)", ln)
            if m:
                ns.append(m.group(1))
                names.add(".".join(ns))
                continue
            m = re.match(r"^end\s+([\w.«»]+)\s*$", ln)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = DECL.match(ln)
            if m:
                full = ".".join(ns + [m.group(2).strip("«»")])
                names.add(full)
                owner = full if m.group(1) in ("structure", "class", "inductive") else None
                continue
            if owner:
                fm = re.match(r"^\s{2,4}(?:\|\s*)?([a-zA-Z_][\w']*)\s*(?::|\(|\{|$)", ln)
                if fm:
                    names.add(owner + "." + fm.group(1))
                elif ln and not ln.startswith((" ", "/-", "--")):
                    owner = None
    _LEAN_NAMES = names
    return names


def check_lean_names(body: str, where: str) -> None:
    """Every Lean name a hand-written page cites in <code> (a dotted name under one of the libraries'
    namespaces) is declared in lean/."""
    names = lean_names()
    tops = {n.split(".")[0] for n in names} | {n.split(".")[1] for n in names if n.count(".") >= 2 and n.split(".")[0] in ("Ecma", "Engine", "Debugger")}
    for c in re.findall(r"<code>([^<]+)</code>", body):
        c = html.unescape(c).strip()
        if not re.fullmatch(r"[A-Z][\w']*(?:\.[\w'«»]+)+", c) or c.split(".")[0] not in tops:
            continue
        if c in names or any(n.endswith("." + c) for n in names):
            continue
        raise SystemExit(f"{where}: <code>{c}</code> names nothing declared under lean/")


def t262_sentence(tp: dict | None) -> str:
    if not tp:
        return ""
    c = tp["counts"]
    ran = sum(v for k, v in c.items() if k != "skip")
    return (f' In its latest recorded run of test262 (at <code>{html.escape(tp["meta"]["test262"][:9])}</code>, '
            f'{html.escape(tp["meta"]["date"])}), {fmt(c.get("pass", 0))} of the {fmt(ran)} tests run pass'
            f'{" (in either of its two passes, the second with larger limits)" if tp.get("rerun") else ""}; '
            f'<a href="test262.html">test262</a> lists every other.')


def t262_section(tp: dict | None) -> str:
    if not tp:
        return ""
    c = tp["counts"]
    ran = sum(v for k, v in c.items() if k != "skip")
    return ('<h2 id="results">Results</h2>\n<ul class="cards two">\n<li><h3><a href="test262.html">test262</a></h3>'
            f'<p>One run of the conformance suite on the engine: {fmt(c.get("pass", 0))} of {fmt(ran)} tests pass'
            f'{" in one of its two passes" if tp.get("rerun") else ""}. '
            'Every test that does not pass, by cause; what is not run, and why.</p></li>\n</ul>')


def proposals_117_fragments(dbgopt: dict | None) -> dict[str, str]:
    """HTML fragments for site/slides.html computed from site/proposals-117.json."""
    rec_path = SITE / "proposals-117.json"
    has_dbg = bool(dbgopt and dbgopt.get("debugger"))

    if has_dbg:
        step3_after = (
            '<div class="step3-live">'
            '<iframe class="step-dbg-iframe" id="step3-dbg-frame" '
            'data-dbg-src="debugger/?example=dbg/proposal_trim_chars&amp;build=trim-chars" '
            'title="Live spec debugger paused on String.prototype.trim step 2"></iframe>'
            '</div>'
        )
    else:
        step3_after = '<pre class="lean">paused at String.prototype.trim step 2 · characters = "/_"</pre>'

    if not rec_path.is_file():
        return {
            "proposals_117_count": "14",
            "proposals_117_table": '<p class="muted">Run <code>scripts/proposals_summary.py</code>.</p>',
            "slides_step3_after": step3_after,
        }

    data = json.loads(rec_path.read_text())
    props = [p for p in data.get("proposals", []) if p.get("status") == "ready"]

    def pm(b: dict) -> str:
        a, r = b.get("added", 0), b.get("removed", 0)
        if a == 0 and r == 0:
            return '<span class="muted">0</span>'
        return f"+{fmt(a)}" + (f" / −{fmt(r)}" if r else "")

    stage_cls = {"3": "proved", "2.7": "rd", "2": "owed", "1": "none", "0": "none"}
    trows = []
    for p in props:
        d = p["diff"]
        sd = p.get("spec_diff", {"added": 0, "removed": 0})
        st = d.get("spectec", {"added": 0, "removed": 0})
        ln = d.get("lean", {
            "added": d.get("model", {}).get("added", 0) + d.get("proofs", {}).get("added", 0),
            "removed": d.get("model", {}).get("removed", 0) + d.get("proofs", {}).get("removed", 0),
        })
        bcls = stage_cls.get(p["stage"], "none")
        ex, bid = p.get("example", ""), p.get("build", "")
        dbg_url = f"debugger/?example={html.escape(ex)}&amp;build={html.escape(bid)}"
        dbg_cell = (f'<a class="open open-xs" href="{dbg_url}" data-dbg-open="{dbg_url}">Debug →</a>'
                    if (has_dbg and ex and bid) else f'<code>{html.escape(bid)}</code>')
        trows.append(
            f'<tr>'
            f'<td><span class="badge {bcls}">{html.escape(p["stage"])}</span></td>'
            f'<td class="p-title"><a href="{html.escape(p["repo"])}">{html.escape(p["title"])}</a></td>'
            f'<td class="num">{pm(sd)}</td>'
            f'<td class="num">{pm(st)}</td>'
            f'<td class="num">{pm(ln)}</td>'
            f'<td>{dbg_cell}</td>'
            f'</tr>'
        )
    table_html = (
        '<div class="tablebox prop117-box"><table class="prop117-table">'
        '<thead><tr>'
        '<th>Stage</th><th>Proposal</th><th class="num"><code>spec.html</code></th>'
        '<th class="num">SpecTec</th><th class="num">Hand-written Lean</th><th></th>'
        '</tr></thead><tbody>'
        + "".join(trows)
        + '</tbody></table></div>'
    )
    return {
        "proposals_117_count": str(len(props)),
        "proposals_117_table": table_html,
        "slides_step3_after": step3_after,
    }


def worked_example(dbgopt: dict | None) -> dict[str, str]:
    """How it works' worked example, IsCallable: its text from spec.html, its SpecTec definition from
    spec/spectec/clauses/S07.spectec, and its sorted ClauseId index."""
    cid = "sec-iscallable"
    sp = errata_page.Text()
    alg = re.search(r"<emu-alg>(.*?)</emu-alg>", sp.own(cid), re.DOTALL).group(1)
    st_file = ROOT / "spec/spectec/clauses/S07.spectec"
    src = st_file.read_text()
    m = re.search(r"(?ms)^def @sec-iscallable\b.*?^\}\n", src)
    if not m:
        raise SystemExit(f"{st_file}: no def @sec-iscallable")
    code = m.group(0).rstrip()
    clause_names = sorted({m.group(1) or m.group(2) for ln in (ROOT / "spec/spectec/00-decls.spectec").read_text().splitlines()
                           if (m := re.match(r'^clause @(?:"([^"]+)"|(\S+))', ln))})
    if cid not in clause_names:
        raise SystemExit(f"{cid} not in spec/spectec/00-decls.spectec")
    aid = str(clause_names.index(cid))
    tour = bool(dbgopt and dbgopt.get("gallery") and any(e["id"] == "run/iscallable" for e in dbgopt["gallery"]["examples"]))
    num = sp.nums[cid]
    return {
        "ex:num": num,
        "ex:spec": (f'<blockquote class="sentence alg"><cite><a class="clause" href="{rl.CLAUSE_URL.format(cid)}">'
                    f'§{num} IsCallable ( <var>arg</var> )</a></cite>{errata_page.alg_html(alg, sp)}</blockquote>'),
        "ex:spectec": f'<pre class="lean">{rl.highlight("--- " + st_file.relative_to(ROOT).as_posix() + chr(10) + code, None, [], lang="SpecTec")}</pre>',
        "ex:id": aid,
        "ex:debugger": ('<p class="opens"><button type="button" class="open" data-dbg-open="debugger/?example=run/iscallable">Open in the debugger</button></p>'
                        if tour else ""),
    }


def build(out: Path, spec_path: Path, t262: Path | None, dbgopt: dict | None = None,
          errata_runs: dict | None = None, proposal: Path | None = None, base_path: str = BASE_PATH) -> list[str]:
    """`t262`: a test262 run's record (scripts/test262_report.py); `dbgopt`: {gallery, builds, checked, debugger}
    (the examples and the debugger's page), or None; `errata_runs`: scripts/errata_page.py run's output."""
    site = Site(spec_path)
    rev = git("rev-parse", "--short", "HEAD")
    dirty = bool(git("status", "--porcelain", "--untracked-files=no"))
    tree = git("ls-tree", "HEAD", "external/ecma262", "external/test262").split("\n")
    sub = {x.split()[3]: x.split()[2] for x in tree}
    facts = {"rev": rev, "dirty": dirty, "ecma262": sub["external/ecma262"], "test262": sub["external/test262"]}

    model_secs = [Section("model", "The model", ["spec/spectec/prose/01-model.spectec"]),
                  Section("values", "Values, cells and stops", ["spec/spectec/prose/02-value.spectec"]),
                  Section("laws", "The laws of a model", ["spec/spectec/prose/05-model-laws.spectec"])]
    host_secs = host_sections()
    impl_secs = [Section("implements", "What it is to implement the specification", ["lean/Ecma/Implements.lean"]),
                 Section("runs", "Runs", ["lean/Ecma/Machine/Run.lean"])]
    parse_secs = [Section("nodes", "Parse Nodes, derivations and their laws", ["spec/spectec/prose/06-node-rel.spectec"])]
    for page, secs in (("model.html", model_secs), ("host.html", host_secs), ("implements.html", impl_secs),
                       ("parser-laws.html", parse_secs)):
        site.register(page, secs)

    opts = rl.Options(status=site.status)
    pages: list[Page] = []

    # The model.
    body, toc, r_model = site.render("model.html", model_secs, opts)
    model_laws = [x for x in r_model.laws]
    pages.append(Page("model.html", "The model and its laws",
                      "Reading page · generated from <code>spec/spectec/prose/01-model.spectec</code>, <code>02-value.spectec</code>, <code>05-model-laws.spectec</code>",
                      f"<p>A model (<code>syntax Model record</code>) gives each sort of the specification "
                      f"(mathematical values, Numbers, BigInts, Strings, Symbols, Parse Nodes, Lists, Data Blocks, "
                      f"CharSets, Records, the store) a carrier and its operations, over which specification values "
                      f"(<code>syntax Val</code>) and store cells (<code>syntax Cell</code>) are defined. "
                      f"The SpecTec <code>laws</code> blocks state what the prose assumes of them: {fmt(len(model_laws))} laws, "
                      f"each quoting the sentence it reads. Laws that quote the same sentence share one quotation.</p>",
                      body, toc))

    # The host.
    body, toc, r_host = site.render("host.html", host_secs, opts)
    table, nhost = law_table(r_host, site.spec)
    nosent = sum(1 for d, m, law in r_host.laws if d.full.startswith("Ecma.Host.") and law.no_sentence is not None)
    summary = (f'<section class="part" id="all-laws"><h2 class="part-title"><a class="self" href="#all-laws">All '
               f'{nhost} laws</a></h2><p>Each law is a <code>law</code> declaration in the SpecTec <code>laws</code> '
               f'block of its topic, and <a href="#Host.WF"><code>Host.WF</code></a> extends all of them. Two read '
               f'their sentence more strictly than it is written, and are for the list of proposed normative changes; '
               f'two more weakly:</p>{differs_list()}{table}</section>')
    first_part = body.index(f'<section class="part" id="{host_secs[2].anchor}"')
    body = body[:first_part] + summary + body[first_part:]
    toc.insert(2, ("all-laws", f"All {nhost} laws", 1))
    pages.append(Page("host.html", "The host and its laws",
                      "Reading page · generated from <code>spec/spectec/prose/10-host.spectec</code> and <code>spec/spectec/prose/*-host-laws*.spectec</code>",
                      f"<p>What the specification leaves to the host, and the {nhost} SpecTec laws it requires of one, "
                      f"by topic. Each law names its clause, quotes the sentence that governs it, and says how "
                      f"SpecTec reads it ({nosent} have no single sentence and say why). "
                      f"<code>scripts/law_quotes.py</code> checks every quotation against the pinned <code>spec.html</code>.</p>",
                      body, toc, wide=False))

    # Implements and runs.
    body, toc, _ = site.render("implements.html", impl_secs, opts)
    pages.append(Page("implements.html", "What it is to implement the specification",
                      "Reading page · generated from <code>lean/Ecma/Implements.lean</code>, <code>lean/Ecma/Machine/Run.lean</code>",
                      "<p>The downstream Lean conformance contract that bridges the compiled SpecTec specification "
                      "to the concrete engine, in full, with the definitions of a run it uses. "
                      "<a href=\"what-is-proved.html\">What is proved</a> reads it field by field.</p>", body, toc))

    # The parser's laws.
    body, toc, _ = site.render("parser-laws.html", parse_secs, opts)
    pages.append(Page("parser-laws.html", "The parser's laws",
                      "Reading page · generated from <code>spec/spectec/prose/06-node-rel.spectec</code>",
                      "<p>What a model's parser must give, stated in SpecTec: a Parse Node related to a derivation of "
                      "the source text under the grammar (<code>relation Model.NodeRel</code>, <code>laws Model.ParseLaws</code>), "
                      "a covered node that is a parse of its cover's text (<code>laws Model.CoverLaws</code>), and "
                      "the laws of a Parse Node's children and descendants (<code>laws Model.NodeLaws</code>). All three "
                      "are proved of the engine (<code>Engine.Claims.parseLaws</code>, <code>Engine.Claims.coverLaws</code>, "
                      "<code>Engine.Claims.nodeLaws</code>).</p>", body, toc))

    # The results page and the errata page, whose numbers the hand-written pages give.
    gallery = dbgopt and dbgopt.get("gallery")
    tp = test262_report.page(t262) if t262 else None
    ep = errata_page.page(errata_runs, gallery, (dbgopt or {}).get("builds", []), RUN) if errata_runs else None
    if ep:
        site.findings += ep["findings"]
    pp = proposal_record.page(proposal_record.read(proposal), gallery, (dbgopt or {}).get("builds", [])) if proposal else None

    # Numbers for the hand-written pages.
    e = errata()
    st = spectec_counts()
    ecma = lean_lines(LEAN / "Ecma")
    gen = gen_lines(LEAN / "Ecma/Gen")
    ggen = gen_lines(LEAN / "Ecma/Grammar/Gen")
    eng = lean_lines(LEAN / "Engine", exclude="Proofs")
    proofs = lean_lines(LEAN / "Engine/Proofs")
    dbg = lean_lines(LEAN / "Debugger")
    host_laws = r_host.laws
    model_counts = {}
    for d, _m, _l in model_laws:
        model_counts[d.anchor] = model_counts.get(d.anchor, 0) + 1
    impl_rel = ROOT / "lean/Engine/Proofs/Model.lean"
    total_errata = sum(v for k, v in e.items() if ":" not in k)

    def code(s: str) -> str:
        return f'<pre class="lean">{rl.highlight(s, None, [])}</pre>'

    values = {
        "SITE_NAME": html.escape(SITE_NAME), "RUN": RUN, "DBG": DBG, "BUNDLE": BUNDLE,
        "rev": rev, "ecma262": facts["ecma262"][:9], "test262": facts["test262"][:9],
        "spectec_struct_files": fmt(st["struct_files"]), "spectec_struct_lines": fmt(st["struct_lines"]),
        "spectec_prose_files": fmt(st["prose_files"]), "spectec_prose_lines": fmt(st["prose_lines"]),
        "spectec_total_files": fmt(st["total_files"]), "spectec_total_lines": fmt(st["total_lines"]),
        "spectec_clause_files": fmt(st["clause_files"]), "spectec_defs": fmt(st["defs"]),
        "spectec_html_files": fmt(st["html_files"]), "spectec_html_lines": fmt(st["html_lines"]),
        "gen_modules": fmt(gen[0]), "gen_lines": fmt(gen[1]),
        "grammar_gen_modules": fmt(ggen[0]), "grammar_gen_lines": fmt(ggen[1]),
        "ecma_lines": fmt(ecma[1]), "ecma_files": fmt(ecma[0]),
        "engine_lines": fmt(eng[1]), "proof_lines": fmt(proofs[1]), "debugger_lines": fmt(dbg[1]),
        "engine_files": fmt(eng[0]), "proof_files": fmt(proofs[0]), "debugger_files": fmt(dbg[0]),
        "errata": fmt(total_errata),
        "errata_defects": fmt(e.get("kind:defect", 0)), "errata_proposals": fmt(e.get("kind:proposal", 0)),
        "errata_proposals_noun": "change" if e.get("kind:proposal", 0) == 1 else "changes",
        "errata_switch_spec": fmt(e.get("switch:spec", 0)), "errata_switch_parser": fmt(e.get("switch:parser", 0)),
        "errata_switch_none": fmt(e.get("switch:none", 0)),
        "errata_test262": fmt(e.get("test262", 0)), "errata_literal": fmt(e.get("literal", 0)),
        "errata_proposed": fmt(e.get("proposed", 0)), "errata_pending": fmt(e.get("res:pending", 0)),
        "host_laws": fmt(len(host_laws)), "host_topics": fmt(len([s for s in host_secs if s.anchor[0].isupper()])),
        "model_laws": fmt(model_counts.get("Model.Laws", 0)), "num_laws": fmt(model_counts.get("Model.NumLaws", 0)),
        "byte_laws": fmt(model_counts.get("Model.ByteLaws", 0)),
        "parent_laws": fmt(model_counts.get("Model.ParentLaws", 0)),
        "unicode_laws": fmt(model_counts.get("Model.UnicodeLaws", 0)),
        "all_model_laws": fmt(len(model_laws)),
        "total_laws": fmt(len(model_laws) + len(host_laws)),
        "pins": fmt(pins()),
        "runtime_pins": fmt(runtime_pins()),
        "stmt:implements": code("-- lean/Engine/Proofs/Model.lean, in namespace Engine\n"
                                + statement(impl_rel, "implements")),
        "stmt:run_sound": code("-- lean/Engine/Proofs/Model.lean, in namespace Engine\n"
                               + statement(impl_rel, "run_sound")),
        "implements_struct": code("-- lean/Ecma/Implements.lean, in namespace Ecma\n" + implements_struct()),
        "stmt:implementation": code("-- lean/Engine/Claims.lean, in namespace Engine\n"
                                    + definition(LEAN / "Engine/Claims.lean", "implementation")),
        "t262_link": '<a href="test262.html">test262</a>' if tp else "test262",
        "read_cols": "three" if 2 + bool(ep) + bool(pp) == 3 else "two",
        "proposal_card": ('<li><h3><a href="proposal.html">Applying a proposal</a></h3><p>A TC39 proposal applied in a '
                          'branch: ' + fmt(pp["summary"]["hand_lines"]) + ' lines written by hand, '
                          + fmt(pp["summary"]["lean_hand"]) + ' files of hand-written Lean changed.</p></li>') if pp else "",
        "proposal_link": (' (<a href="proposal.html">Applying a proposal</a> shows one applied)') if pp else "",
        "errata_card": ('<li><h3><a href="errata.html">Errata</a></h3><p>The ' + fmt(ep["counts"]["errata"]) + ' specification '
                        'defects and proposed changes recorded in <code>spec/DECISIONS.md</code>: the quoted sentences, '
                        'the reading baked into SpecTec, and ' + fmt(ep["counts"]["with_program"]) + ' verified programs.'
                        '</p></li>') if ep else "",
        "t262_section": t262_section(tp),
        "errata_sentence": (' <a href="errata.html">The errata page</a> quotes each entry\'s sentences and alternative '
                            'readings, and verifies a demonstration program for each one that has one.') if ep else "",
        "t262_sentence": t262_sentence(tp),
        "axioms": ", ".join(f"<code>{x}</code>" for x in axioms()), "axiom_count": fmt(len(axioms())),
        "dbg_section": "", "dbg_revision": (" and the step debugger as <code>" + DBG + "</code>"
                                            + ("." if pp else "; the application of a proposal is not on this site yet.")),
        "slides_errata_link": '<a href="errata.html">Errata</a>' if ep else "Errata",
        "slides_errata_count_link": f'<a href="errata.html">{fmt(total_errata)} documented errata</a>' if ep else f'{fmt(total_errata)} documented errata',
        "slides_examples_link": '<a href="examples.html">All debugger examples</a>' if gallery else "All debugger examples",
        "slides_proposal_link": '<a href="proposal.html">Deep dive: applying <code>import defer</code></a>' if pp else "Applying <code>import defer</code>",
        **worked_example(dbgopt),
        **proposals_117_fragments(dbgopt),
    }
    if dbgopt and dbgopt.get("debugger"):
        values["dbg_section"] = (
            '<h2 id="run">Run it</h2>\n<ul class="cards two">\n'
            '<li><h3><a href="debugger/">The debugger</a></h3><p>A JavaScript program run by the specification\'s '
            'machine, paused at its steps: the spec stack beside the JS stack, the step\'s text, its slots and the '
            'store. In a browser with 64-bit WebAssembly.</p></li>\n'
            + ('<li><h3><a href="examples.html">Examples</a></h3><p>Programs that each open in the debugger with '
               'their breakpoints set, from a property get to the errata read as written.</p></li>\n' if gallery else "")
            + "</ul>")
        values["dbg_revision"] = ("; the step debugger, <code>" + DBG + "</code>, runs in the browser as WebAssembly."
                                  + ("" if pp else " The application of a proposal is not on this site yet."))

    for name in ("index.html", "how-it-works.html", "what-is-proved.html", "slides.html"):
        meta, body = read_template(name)
        body = fill(body, values, f"site/{name}")
        check_lean_names(body + meta.get("lede", ""), f"site/{name}")
        lede = fill(meta.get("lede", ""), values, f"site/{name}")
        is_slides = name == "slides.html"
        pages.append(Page(name, fill(meta["title"], values, name), fill(meta.get("eyebrow", ""), values, name),
                          lede, body, toc_of(body) if name not in ("index.html", "slides.html") else [],
                          wide=is_slides))

    if gallery:
        more = {"proposal": '<p>What it took to apply the proposal: <a href="proposal.html">Applying a proposal</a>.</p>'} if pp else {}
        body, lede, toc = examples_page(gallery, dbgopt["builds"], dbgopt.get("checked", []), facts, more)
        pages.append(Page("examples.html", "Examples", "Programs for the debugger · <code>tools/dbg/gallery.json</code>",
                          lede, body, toc))

    if tp:
        pages.append(Page("test262.html", tp["title"], tp["eyebrow"], tp["lede"], tp["body"], tp["toc"], wide=True))
    if ep:
        pages.append(Page("errata.html", ep["title"], ep["eyebrow"], ep["lede"], ep["body"], ep["toc"]))
    if pp:
        pages.append(Page("proposal.html", pp["title"], pp["eyebrow"], pp["lede"], pp["body"], pp["toc"], wide=True))

    # The spec-issue write-ups (scripts/spec_issue_pages.py), under spec-issues/.
    for o in spec_issue_pages.pages((dbgopt or {}).get("builds", []), errata_page.Text()):
        check_lean_names(o.body, o.file)
        pages.append(Page(o.file, o.title, o.eyebrow, o.lede, o.body, o.toc, nav="spec-issues/",
                          wide=o.file.endswith("results.html")))

    # The page GitHub Pages serves for an address with no page: its links are from the site's root, since it is
    # served at any depth.
    pages.append(Page("404.html", "No page here", "", "<p>There is no page at this address.</p>",
                      f'<p>The site\'s pages are in its navigation above; <a href="{base_path}index.html">the home page</a> '
                      'says what is here.</p>', prefix=base_path))

    names = ({p.file for p in pages} | ({"debugger/"} if dbgopt and dbgopt.get("debugger") else set())
             | {"spec-issues/"})
    for k, (f, old, _new) in enumerate(REWORD):
        if k not in site.reword_used:
            raise SystemExit(f"REWORD: {f} no longer has {old!r}: remove the entry")
    out.mkdir(parents=True, exist_ok=True)
    for old in [*out.glob("*.html"), *out.glob("spec-issues/*.html")]:  # a page an earlier build wrote, not this one
        if old.relative_to(out).as_posix() not in names:
            old.unlink()
    for p in pages:
        (out / p.file).parent.mkdir(parents=True, exist_ok=True)
        (out / p.file).write_text(frame(p, names, facts))
    if dbgopt and dbgopt.get("debugger"):
        (out / "debugger").mkdir(exist_ok=True)
        (out / "debugger/index.html").write_text(debugger_frame(names, gallery, facts["rev"]))
    for a in ("style.css", "site.js", "robots-lean.svg"):
        if (SITE / a).is_file():
            shutil.copy(SITE / a, out / a)
    for c in ("coi-serviceworker.js", "coi-serviceworker.LICENSE"):
        if (ROOT / "tools/dbg" / c).is_file():
            shutil.copy(ROOT / "tools/dbg" / c, out / c)
    return site.findings


def definition(path: Path, name: str) -> str:
    """A definition as written, without its docstring: from `def name` to the blank line after it."""
    src = path.read_text()
    m = re.search(r"(?m)^def " + re.escape(name) + r"\b.*?(?=\n\s*\n)", src, re.DOTALL)
    if not m:
        raise SystemExit(f"{path}: no def {name}")
    return m.group(0)


def implements_struct() -> str:
    src = (LEAN / "Ecma/Implements.lean").read_text()
    m = re.search(r"(?m)^structure Implements\b.*?(?=\n\nend|\Z)", src, re.DOTALL)
    return m.group(0)


# ---------------------------------------------------------------------------------------------------------------
# The check

VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}


class Checker(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.stack: list[tuple[str, int, bool]] = []
        self.errors: list[str] = []
        self.ids: list[str] = []
        self.links: list[str] = []
        self.loads: list[str] = []
        self.text: list[str] = []
        self.skip = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a:
            self.ids.append(a["id"])
        if tag == "a" and "href" in a:
            self.links.append(a["href"])
        for k in ("src", "srcset", "poster", "data"):
            if k in a:
                self.loads.append(a[k])
        if tag == "link" and "href" in a:
            self.loads.append(a["href"])
        if "style" in a and "url(" in a["style"]:
            self.loads.append(a["style"])
        # Text in scripts and styles, and in an element marked `data-verbatim` (a record quoted as it is, such
        # as a command line), is not checked for retired names.
        flag = tag in ("script", "style") or "data-verbatim" in a
        if tag not in VOID:
            self.stack.append((tag, self.getpos()[0], flag))
            self.skip += flag

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.stack.pop()

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        if not self.stack:
            self.errors.append(f"line {self.getpos()[0]}: </{tag}> with nothing open")
            return
        if self.stack[-1][0] != tag:
            self.errors.append(f"line {self.getpos()[0]}: </{tag}> closes <{self.stack[-1][0]}> of line {self.stack[-1][1]}")
            # Recover: pop to the matching tag, if any.
            for k in range(len(self.stack) - 1, -1, -1):
                if self.stack[k][0] == tag:
                    self.skip -= sum(f for _, _, f in self.stack[k:])
                    del self.stack[k:]
                    break
            return
        self.skip -= self.stack.pop()[2]

    def handle_data(self, data):
        if not self.skip:
            self.text.append(data)


def site_pages(out: Path) -> dict[str, Path]:
    """Every page of a built site by its path under it (`debugger/index.html`)."""
    return {p.relative_to(out).as_posix(): p for p in sorted(out.rglob("*.html"))}


def resolve(name: str, href: str, base_path: str = BASE_PATH) -> tuple[str, str]:
    """A relative or site-root link of page `name` as (the page's path under the site, the fragment); a directory
    is its index.html."""
    page, _, frag = href.partition("#")
    page = page.split("?", 1)[0]
    if not page:
        return name, frag
    if page.startswith("/"):
        rel = page[len(base_path):] if page.startswith(base_path) else page.lstrip("/")
        parts = rel.split("/")
    else:
        parts = (name.rsplit("/", 1)[0].split("/") if "/" in name else []) + page.split("/")
    outp: list[str] = []
    for x in parts:
        if x == "..":
            if outp:
                outp.pop()
        elif x not in ("", "."):
            outp.append(x)
    target = "/".join(outp)
    if page.endswith("/") or not outp:
        target = (target + "/" if target else "") + "index.html"
    return target, frag


# What a stylesheet or a script may not contain: a load from another origin (a URL as data, such as a link to
# tc39.es that a script writes into a page, is not a load).
CSS_EXTERNAL = re.compile(r"url\(\s*['\"]?(?:https?:)?//|@import")
JS_EXTERNAL = re.compile(r"""(?:\bfrom\s*|\bimport\s*\(\s*|\bfetch\s*\(\s*|\bWorker\s*\(\s*|importScripts\s*\(\s*|"""
                         r"""\.src\s*=\s*|\bnew\s+URL\s*\(\s*)['"`](?:https?:)?//""")


def check(out: Path, base_path: str = BASE_PATH) -> list[str]:
    errs: list[str] = []
    pages = site_pages(out)
    parsed: dict[str, Checker] = {}
    for name, p in pages.items():
        c = Checker()
        src = p.read_text()
        if not src.startswith("<!doctype html>"):
            errs.append(f"{name}: no doctype")
        c.feed(src)
        c.close()
        if c.stack:
            errs.append(f"{name}: unclosed " + ", ".join(f"<{t}> of line {ln}" for t, ln, _ in c.stack[:5]))
        errs += [f"{name}: {e}" for e in c.errors[:10]]
        dup = {i for i in c.ids if c.ids.count(i) > 1}
        if dup:
            errs.append(f"{name}: duplicate ids {sorted(dup)[:5]}")
        for ld in c.loads:
            if re.match(r"\s*(?:[a-z]+:)?//", ld) or "url(http" in ld or "url(//" in ld:
                errs.append(f"{name}: loads {ld}")
            elif not re.match(r"[a-z]+:", ld):
                target, _ = resolve(name, ld, base_path)
                if not (out / target).is_file():
                    errs.append(f"{name}: loads {ld}: no such file")
        text = re.sub(r"\s+", " ", " ".join(c.text))
        for pat in RETIRED:
            for m in re.finditer(pat, text):
                errs.append(f"{name}: a retired name: …{text[max(0, m.start() - 40) : m.end() + 40]}…")
        parsed[name] = c
    for f in sorted([*out.rglob("*.css"), *out.rglob("*.js"), *out.rglob("*.mjs")]):
        t = f.read_text(errors="replace")
        m = (CSS_EXTERNAL if f.suffix == ".css" else JS_EXTERNAL).search(t)
        if m:
            line = t[t.rfind("\n", 0, m.start()) + 1 : t.find("\n", m.end())][:160]
            errs.append(f"{f.relative_to(out)}: loads from another origin: {line.strip()}")
    for name, c in parsed.items():
        for href in c.links:
            if re.match(r"[a-z]+:", href):
                if not href.startswith(("https://tc39.es/", "https://github.com/")):
                    errs.append(f"{name}: an external link {href}")
                continue
            target, frag = resolve(name, href, base_path)
            if target not in parsed:
                if not (out / target).exists():
                    errs.append(f"{name}: a link to {href}: no such page")
                continue
            if frag and html.unescape(frag) not in set(parsed[target].ids):
                errs.append(f"{name}: a link to {href}: no such anchor")
    return errs


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--check", type=Path, metavar="DIR")
    ap.add_argument("--spec", type=Path, help="a spec.html (default: the text, scripts/spec_text.py)")
    ap.add_argument("--test262-record", type=Path,
                    help="a test262 run's record (scripts/test262_report.py record): test262.html")
    ap.add_argument("--proposal-record", type=Path, default=proposal_record.RECORD,
                    help="a proposal branch's record (scripts/proposal_record.py): proposal.html, when it is there")
    ap.add_argument("--errata-runs", type=Path,
                    help="the errata programs' runs (scripts/errata_page.py run --out): errata.html")
    ap.add_argument("--findings", type=Path, help="write the docstrings the renderer flagged to this file")
    ap.add_argument("--examples", type=Path, help="the compiled examples (scripts/dbg_gallery.py): examples.html")
    ap.add_argument("--builds", type=Path, help="the debugger's table of builds (builds.json), for the examples page")
    ap.add_argument("--checked", type=Path, action="append", default=[],
                    help="a result of the examples' check (tools/dbg/ui/gallery_test.mjs --json); every example must pass")
    ap.add_argument("--debugger", action="store_true", help="write the debugger's page, debugger/index.html")
    ap.add_argument("--no-check", action="store_true",
                    help="do not check what was written (the caller adds files and checks the whole site)")
    ap.add_argument("--base-path", default=BASE_PATH,
                    help=f"URL prefix where the site is hosted (default: {BASE_PATH})")
    a = ap.parse_args()
    base = "/" + a.base_path.strip("/") + "/" if a.base_path.strip("/") else "/"
    if a.check:
        errs = check(a.check, base)
        for e in errs:
            print(f"FAIL {e}")
        print(f"{'FAIL' if errs else 'ok  '} site check: {len(site_pages(a.check))} pages, {len(errs)} problems")
        return 1 if errs else 0
    if not a.out:
        ap.error("--out or --check")
    a.spec = a.spec or spec_text.spec_html()
    if not a.spec.is_file() or a.spec.stat().st_size == 0:
        ap.error(f"{a.spec}: no spec.html (git submodule update --init external/ecma262, or --spec)")
    t262 = a.test262_record
    if t262 and not t262.is_file():
        ap.error(f"--test262-record {t262}: no such file")
    runs = json.loads(a.errata_runs.read_text()) if a.errata_runs else None
    dbg = None
    if a.examples or a.debugger:
        if a.examples and not a.builds:
            ap.error("--examples needs --builds")
        dbg = {"debugger": a.debugger, "checked": [json.loads(f.read_text()) for f in a.checked]}
        if a.examples:
            dbg["gallery"] = json.loads(a.examples.read_text())
            dbg["builds"] = json.loads(a.builds.read_text())["builds"]
    try:
        findings = build(a.out, a.spec, t262, dbg, runs,
                         a.proposal_record if a.proposal_record and a.proposal_record.is_file() else None, base)
    except rl.RenderError as e:
        print(f"FAIL render: {e}")
        return 1
    if a.findings:
        a.findings.write_text("".join(f + "\n" for f in findings))
    errs = [] if a.no_check else check(a.out, base)
    for e in errs:
        print(f"FAIL {e}")
    print(f"{'FAIL' if errs else 'ok  '} site: {a.out}, {len(site_pages(a.out))} pages, "
          f"{len(findings)} docstring notes, {len(errs)} problems")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
