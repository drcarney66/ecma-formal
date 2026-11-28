#!/usr/bin/env python3
"""The spec-issue write-ups as pages of the site (scripts/site_pages.py calls `pages`).

Writes, under `spec-issues/` of the site: `index.html`, the index made from the data (scripts/spec_issues.py:
each write-up's number, title, first clause, errata, kind, program), one page per write-up (`NN-name.html`, its
Markdown rendered: the header items as a list of facts, each block quotation of the text as the text's steps
with their own labels, the links to other write-ups and to the examples resolved), and `results.html`
(docs/spec-issues/examples/RESULTS.md, the recorded runs of every example on the three engines and the model).

docs/spec-issues/README.md is not published as it is: its account of how the examples were run is the index
page's (the engines' versions read from RESULTS.md), its summary table is the index, and its "Fixed upstream"
list is the Errata page's. SHORTLIST.md (an order for filing them, with notes for the person filing) is not
published.
"""

from __future__ import annotations

import html
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import markdown

sys.path.insert(0, str(Path(__file__).resolve().parent))
import errata_page  # noqa: E402
import spec_issues as si  # noqa: E402
import spec_issues_upstream as upstream  # noqa: E402

ROOT = si.ROOT
DIR = "spec-issues"  # the pages' directory in the site
CLAUSE_URL = "https://tc39.es/ecma262/#{}"
# The examples the debugger's Worker build cannot run (scripts/dbg_spec_examples.py UNRUNNABLE): no link.
sys.path.insert(0, str(ROOT / "scripts"))


def esc(s: str) -> str:
    return html.escape(s, quote=True)


@dataclass
class Out:
    file: str  # under the site: spec-issues/01-….html
    title: str
    eyebrow: str
    lede: str
    body: str
    toc: list[tuple[str, str, int]]


def inline(t: str) -> str:
    """A line of Markdown as inline HTML."""
    t = re.sub(r"(?<![\w~`])~([\w-]+)~(?![\w~])", r'<span class="const">\1</span>', t)
    h = markdown.markdown(t, extensions=["tables"])
    return re.sub(r"^<p>(.*)</p>$", r"\1", h.strip(), flags=re.DOTALL)


def kind_of(iss: si.Issue, kinds: dict[str, str]) -> str:
    """defect, proposal, fixed, or none (no erratum: an editorial item or a question)."""
    if iss.errata:
        ks = {kinds[e] for e in iss.errata}
        return "proposal" if ks == {"proposal"} else "defect"
    if iss.retired:
        return "fixed"
    return "none"


KIND_LABEL = {"defect": "defect of the text", "proposal": "proposed normative change",
              "fixed": "fixed in the pinned text", "none": "no erratum"}


def first_clause(iss: si.Issue) -> str | None:
    loc = iss.header.get("Location", "") or iss.text
    m = si.ID_RE.search(loc) or si.ID_RE.search(iss.text)
    return m.group(1) if m else None


# ---------------------------------------------------------------------------------------------------------------
# A write-up's Markdown as HTML


def qmd(t: str, sp: errata_page.Text) -> str:
    """A quotation's text as the Errata page renders the text's (errata_page.md): the write-ups write a value's
    subscript (`*+0*𝔽`) without spec.html's `<sub>`."""
    return errata_page.md(re.sub(r"\*([^*\s]+)\*([𝔽ℤ])", r"*\1*<sub>\2</sub>", t), sp)


def quote_html(b: si.Block, sp: errata_page.Text) -> str:
    """A block quotation: its paragraphs; a step with its own label, indented under its parents."""
    parts = []
    for para in b.paras:
        rows = []
        for it in para:
            if it.kind == "gap":
                rows.append('<p class="q-gap">…</p>')
            elif it.kind == "prose":
                rows.append(f"<p>{qmd(it.text, sp)}</p>")
            else:
                depth = len(it.labels) - 1
                rows.append(f'<p class="q-step" style="--d:{depth}"><span class="q-num">{esc(it.labels[-1])}.</span> '
                            f'{qmd(it.text, sp)}</p>')
        parts.append("".join(rows))
    cls = "sentence q-other" if b.mark else "sentence q-text"
    return f'<blockquote class="{cls}">{"".join(parts)}</blockquote>'


def split_quotes(text: str, sp: errata_page.Text) -> tuple[str, dict[str, str]]:
    """The Markdown with each block quotation (and its `<!-- quote: -->` mark) replaced by a placeholder."""
    bl = {b.line: b for b in si.blocks(text)}
    lines = text.split("\n")
    out, holes = [], {}
    k = 0
    while k < len(lines):
        ln = lines[k]
        if si.MARK_RE.match(ln):
            k += 1
            continue
        if (k + 1) in bl:
            b = bl[k + 1]
            key = f"QUOTEHOLE{len(holes)}X"
            holes[key] = quote_html(b, sp)
            out += ["", key, ""]
            while k < len(lines) and lines[k].startswith(">"):
                k += 1
            continue
        out.append(ln)
        k += 1
    return "\n".join(out), holes


def body_html(iss: si.Issue, sp: errata_page.Text, names: dict[str, str], errata: set[str],
              example_anchor: str | None) -> str:
    """The write-up's sections (its title and header items are the page's own)."""
    text = iss.text.split("\n", 1)[1]
    # The header items are the page's facts list; the body starts at the first section.
    m = re.search(r"(?m)^## ", text)
    pre, text = (text[: m.start()], text[m.start():]) if m else ("", text)
    lead = "\n".join(ln for ln in pre.split("\n") if not re.match(r"^(- \*\*|  \S)", ln)).strip()
    text = (lead + "\n\n" + text) if lead else text
    text, holes = split_quotes(text, sp)
    text = re.sub(r"(?<![\w~`])~([\w-]+)~(?![\w~])", r'<span class="const">\1</span>', text)
    h = markdown.markdown(text, extensions=["tables", "fenced_code"])
    for k, v in holes.items():
        h = h.replace(f"<p>{k}</p>", v)
    h = re.sub(r'<pre><code class="language-(\w+)">', r'<pre class="\1"><code>', h)
    h = re.sub(r"<pre><code>", r'<pre class="plain"><code>', h)
    h = h.replace("<table>", '<div class="tablebox"><table class="wt">').replace("</table>", "</table></div>")
    h = re.sub(r"<h2>(.*?)</h2>", lambda m: f'<h2 id="{slug(m.group(1))}">{m.group(1)}</h2>', h)

    def link(m: re.Match) -> str:
        href = html.unescape(m.group(1))
        page, _, frag = href.partition("#")
        if re.fullmatch(r"\d\d-[\w-]+\.md", page) and page[:-3] in names:
            href = f"{page[:-3]}.html" + (f"#{frag}" if frag else "")
        elif page == "examples/RESULTS.md":
            href = "results.html" + (f"#{frag}" if frag else "")
        elif page.startswith("examples/"):
            href = f"#{example_anchor}" if example_anchor else "results.html"
        elif page in ("README.md", "./"):
            href = "../errata.html"
        return f'href="{esc(href)}"'

    h = re.sub(r'href="([^"]*)"', link, h)
    h = h.replace('">RESULTS.md</a>', '">the recorded runs</a>')
    h = re.sub(r"<code>#((?:sec|prod|table|figure|eqn|await|step)[A-Za-z0-9_.%@-]*)</code>",
               lambda m: f'<a class="clause" href="{esc(CLAUSE_URL.format(m.group(1)))}"><code>#{m.group(1)}</code></a>', h)
    h = re.sub(r"<code>(\w+)</code>", lambda m: (f'<a href="../errata.html#{m.group(1)}"><code>{m.group(1)}</code></a>'
                                                  if m.group(1) in errata else m.group(0)), h)
    return h


def results_anchor(heading: str) -> str:
    """The id results.html gives an example's heading (Markdown's toc extension, as GitHub's)."""
    from markdown.extensions.toc import slugify
    return slugify(heading, "-")


def slug(t: str) -> str:
    t = re.sub(r"<[^>]+>", "", html.unescape(t)).lower()
    return re.sub(r"[^a-z0-9]+", "-", t).strip("-") or "s"


# ---------------------------------------------------------------------------------------------------------------
# The pages


def engines() -> list[tuple[str, str]]:
    """RESULTS.md's table of the engines and their versions."""
    t = (si.EXAMPLES / "RESULTS.md").read_text()
    rows = re.findall(r"(?m)^\| ([^|]+?) \| ([^|]+?) \|$", t)
    return [(a, b) for a, b in rows if a not in ("Engine", "---")]


def results_page(sp: errata_page.Text) -> Out:
    t = (si.EXAMPLES / "RESULTS.md").read_text()
    t = t.split("\n", 1)[1]  # its own title
    t = re.sub(r"(?m)^Generated by `scripts/spec_issues_run.py` \(do not edit; run it again\)\. ", "", t)
    h = markdown.markdown(t, extensions=["tables", "fenced_code", "toc"])
    h = re.sub(r"<pre><code>", r'<pre class="plain"><code>', h)
    h = h.replace("<table>", '<div class="tablebox"><table>').replace("</table>", "</table></div>")
    # Each example's heading links to its write-up.
    toc = []

    def head(m: re.Match) -> str:
        hid, name = m.group(1), m.group(2)
        toc.append((hid, esc(html.unescape(name)), 1))
        return m.group(0)

    re.sub(r'<h2 id="([^"]+)">(.*?)</h2>', head, h)
    lede = ("<p>Every example of the write-ups, run on the three engines and on the model: each run's exit status, "
            "standard output and standard error, exactly as recorded by <code>scripts/spec_issues_run.py</code>. "
            "The model's runs were made from this repository's build; the engines' runs are the record of the "
            "versions below.</p>")
    return Out(f"{DIR}/results.html", "The examples' runs",
               '<a href="../errata.html">Spec issues &amp; errata</a> · <code>docs/spec-issues/examples/RESULTS.md</code>',
               lede, h, toc)


def program_html(iss: si.Issue, builds: list[dict], errata: dict, unrunnable: dict[str, str]) -> str:
    ex = iss.example
    files = sorted(p for p in ex.rglob("*") if p.is_file()) if ex.is_dir() else [ex]
    ident = ex.name if ex.is_dir() else ex.stem
    srcs = "".join(f'<details class="jssrc"><summary>Source <code>{esc(f.relative_to(si.DIR).as_posix())}</code></summary>'
                   f'<pre class="js">{esc(f.read_text())}</pre></details>' for f in files)
    links = []
    if ident in unrunnable:
        links.append(f'<p class="muted">Not offered in the debugger: {esc(unrunnable[ident])}.</p>')
    elif builds:
        first = builds[0]
        q = f"../debugger/?example={esc(ident)}"
        opens = [f'<button type="button" class="open" data-dbg-open="{q}">Open in the debugger</button>']
        links.append(f'<p class="opens">{" ".join(opens)}</p>')
    kind = "a Module graph (its <code>main.mjs</code> runs as a Module)" if ex.is_dir() else "a Script"
    return (f'<section id="program"><h2>The program</h2>'
            f'<p>The example is {kind}. Its runs on the engines and on the model: '
            f'<a href="results.html#{results_anchor(ex.name)}">the examples\' runs</a>.</p>{"".join(links)}{srcs}</section>')


STATE_LABEL = {"open": "open", "draft": "open, a draft", "closed": "closed", "closed-unmerged": "closed unmerged",
               "merged": "merged"}
REF_RE = re.compile(r"test262\s+PR\s+#(\d+)|(?<![\w/&])#(\d+)\b|\b([0-9a-f]{9})\b")


def upstream_link(m: re.Match, by: dict[tuple[str, str], upstream.Row]) -> str:
    if m.group(1):
        r = by.get(("test262-pull", m.group(1)))
        return f'test262 <a class="ext" href="{esc(r.url)}">PR #{m.group(1)}</a>' if r else m.group(0)
    if m.group(2):
        r = by.get(("issue", m.group(2))) or by.get(("pull", m.group(2)))
        return f'<a class="ext" href="{esc(r.url)}">#{m.group(2)}</a>' if r else m.group(0)
    r = by.get(("commit", m.group(3)))
    return f'<a class="ext" href="{esc(r.url)}"><code>{m.group(3)}</code></a>' if r else m.group(0)


def upstream_html(item: str, rows: list[upstream.Row]) -> str:
    """The Upstream item, each issue, pull request and commit the record has for it linked to GitHub."""
    by = {(r.kind, r.ref): r for r in rows}
    return REF_RE.sub(lambda m: upstream_link(m, by), inline(item))


def upstream_summary(item: str, rows: list[upstream.Row]) -> str:
    """The index's cell: what the item's first sentence names, with its state (a fix: the merged pull request)."""
    body = upstream.CHECKED_RE.sub("", item)
    if not body:
        return ""
    by = {(r.kind, r.ref): r for r in rows}
    low = body.lower()
    if low.startswith("fixed"):
        named = [by[k] for k in (("pull", n) for _, n in upstream.refs(body) if _ == "num") if k in by
                 and by[k].state == "merged"][:1]
        lead = "fixed: "
    elif low.startswith(("none found", "no fix found")):
        return '<span class="muted">none found</span>'
    else:
        first = re.split(r"\.\s+(?=[A-Z`])", body, maxsplit=1)[0]
        named = []
        for kind, n in upstream.refs(first):
            r = (by.get(("test262-pull", n)) if kind == "t262" else by.get(("issue", n)) or by.get(("pull", n)))
            if r:
                named.append(r)
        lead = "related: " if low.startswith("related") else ""
    parts = []
    for r in named:
        what = {"issue": "issue", "pull": "PR", "test262-pull": "test262 PR"}[r.kind]
        parts.append(f'{what} <a class="ext" href="{esc(r.url)}">#{r.ref}</a> '
                     f'<span class="muted">{esc(STATE_LABEL[r.state])}</span>')
    return esc(lead) + ", ".join(parts)


def facts_html(iss: si.Issue, sp: errata_page.Text, names: dict[str, str], errata: dict, kinds: dict[str, str],
               recs: dict[str, list[upstream.Row]]) -> str:
    rows = []
    for k in ("Location", "Kind", "Model erratum", "Model errata", "Model reading"):
        if k in iss.header:
            v = inline(iss.header[k])
            v = re.sub(r'href="(\d\d-[\w-]+)\.md(#[^"]*)?"',
                       lambda m: f'href="{m.group(1)}.html{m.group(2) or ""}"' if m.group(1) in names else m.group(0), v)
            v = re.sub(r"<code>#((?:sec|prod|table|figure|eqn|await|step)[A-Za-z0-9_.%@-]*)</code>",
                       lambda m: f'<a class="clause" href="{esc(CLAUSE_URL.format(m.group(1)))}"><code>#{m.group(1)}</code></a>', v)
            rows.append(f"<dt>{esc(k)}</dt><dd>{v}</dd>")
    if "Upstream" in iss.header:
        rows.append(f"<dt>Upstream</dt><dd>{upstream_html(iss.header['Upstream'], recs.get(iss.num, []))}</dd>")
    ers = []
    for e in iss.errata:
        er = errata[e]
        ers.append(f'<a href="../errata.html#{esc(e)}"><code>{esc(e)}</code></a> on Spec issues &amp; errata '
                   f'({esc(KIND_LABEL[er.kind])}; SpecTec bakes in {esc(errata_page.READING_LABEL[er.default])})')
    for e in iss.retired:
        ers.append(f'<code>{esc(e)}</code>, retired: <a href="../errata.html#removed">removed because the editors fixed the text</a>')
    if ers:
        rows.append(f'<dt>On this site</dt><dd>{"<br>".join(ers)}</dd>')
    dl = f'<dl class="split efacts">{"".join(rows)}</dl>'
    return re.sub(r'href="(\d\d-[\w-]+)\.md(#[^"]*)?"',
                  lambda m: f'href="{m.group(1)}.html{m.group(2) or ""}"' if m.group(1) in names else m.group(0), dl)


def pages(builds: list[dict] | None = None, sp: errata_page.Text | None = None, strict: bool = True) -> list[Out]:
    """Every page under spec-issues/; `strict`: stop at a quotation of the text that spec.html does not have."""
    sp = sp or errata_page.Text()
    builds = builds or []
    all_errata = {e.name: e for e in errata_page.read_errata()}
    kinds = {n: e.kind for n, e in all_errata.items()}
    iss = si.issues()
    names = {i.slug: i for i in iss}
    try:
        import dbg_spec_examples
        unrunnable = dict(dbg_spec_examples.UNRUNNABLE)
    except ImportError:
        unrunnable = {}
    ck = si.Checker()
    recs = upstream.by_writeup()
    out: list[Out] = []
    for i in iss:
        fails, _notes, _n = ck.check(i)
        if fails and strict:
            raise SystemExit("spec issues: a quotation of the text does not match spec.html (scripts/spec_issues.py "
                             "check):\n  " + "\n  ".join(fails))
        anchor = "program" if i.example else None
        body = facts_html(i, sp, names, all_errata, kinds, recs) + body_html(i, sp, names, set(all_errata), anchor)
        if i.example:
            body += program_html(i, builds, all_errata, unrunnable)
        toc = [(m.group(1), m.group(2), 1) for m in re.finditer(r'<h2 id="([^"]+)">(.*?)</h2>', body)]
        if i.example:
            toc.append(("program", "The program", 1))
        out.append(Out(f"{DIR}/{i.slug}.html", f"{i.num}. {inline(i.title)}",
                       f'<a href="../errata.html">Spec issues &amp; errata</a> · {esc(KIND_LABEL[kind_of(i, kinds)])} · '
                       f'<code>docs/spec-issues/{esc(i.path.name)}</code>', "", body, toc))
    out.append(results_page(sp))
    return out


GROUPS = [
    ("defects", "Defects of the text", "defect",
     "The text, read as written, gives no answer, an answer that contradicts another sentence, or an answer "
     "test262 does not accept. Each is an erratum recorded in SpecTec, with its readings on the Errata page."),
    ("proposals", "Proposed normative changes", "proposal",
     "Not a defect: the text is consistent, and the change would alter what it requires."),
    ("other", "Editorial items and questions", "none",
     "Irregular notation, a missing case nothing observable depends on, or a sentence that needs clarifying."),
]


def index_page(iss: list[si.Issue], sp: errata_page.Text, errata: dict, kinds: dict[str, str],
               recs: dict[str, list[upstream.Row]]) -> Out:
    secs, toc = [], []
    counts = {}
    for gid, title, kind, intro in GROUPS:
        rows = []
        for i in iss:
            if kind_of(i, kinds) != kind:
                continue
            cid = first_clause(i)
            num = sp.nums.get(cid or "", "")
            clause = (f'<a class="clause" href="{esc(CLAUSE_URL.format(cid))}"><span class="secnum">{esc(num)}</span> '
                      f'{esc(sp.short(cid))}</a>' if cid and num else "")
            more = len(set(si.ID_RE.findall(i.header.get("Location", "")))) - 1
            if more > 0:
                clause += f' <span class="muted">and {more} more</span>'
            ers = ", ".join(f'<a href="../errata.html#{esc(e)}"><code>{esc(e)}</code></a>' for e in i.errata)
            ers = ers or ", ".join(f'<code>{esc(e)}</code> (retired)' for e in i.retired) or '<span class="muted">none</span>'
            up = upstream_summary(i.header.get("Upstream", ""), recs.get(i.num, []))
            rows.append(f'<tr><td class="num">{i.num}</td><td><a href="{esc(i.slug)}.html">{inline(i.title)}</a></td>'
                        f'<td>{clause}</td><td>{ers}</td><td class="up">{up}</td>'
                        f'<td class="num">{"yes" if i.example else ""}</td></tr>')
        counts[kind] = len(rows)
        if not rows:
            continue
        toc.append((gid, f"{esc(title)} ({len(rows)})", 1))
        secs.append(f'<section class="part" id="{gid}"><h2 class="part-title"><a class="self" href="#{gid}">{esc(title)} '
                    f'({len(rows)})</a></h2><p>{esc(intro)}</p><div class="tablebox"><table class="issues"><thead><tr>'
                    f'<th class="num">No.</th><th>Write-up</th><th>Clause</th><th>Erratum</th><th>Upstream</th>'
                    f'<th class="num">Program</th>'
                    f'</tr></thead><tbody>{"".join(rows)}</tbody></table></div></section>')
    checked = ", ".join(sorted({r.checked_on for v in recs.values() for r in v})) or "no date"
    eng = "".join(f"<li><strong>{esc(a)}</strong>: {inline(b)}</li>" for a, b in engines() if not a.startswith("the formal model"))
    eng += ("<li><strong>The formal model</strong>: <code>ecma-run</code>, built from this repository at the commit this "
            "site was built from.</li>")
    pin = subprocess_out(["git", "-C", str(ROOT / "external/ecma262"), "rev-parse", "--short=9", "HEAD"])
    t262 = subprocess_out(["git", "-C", str(ROOT / "external/test262"), "rev-parse", "--short=8", "HEAD"])
    how = (f'<section class="part" id="how"><h2 class="part-title"><a class="self" href="#how">How to read them</a></h2>'
           f'<p>Each write-up names its clause and step in ECMA-262 at <code>{esc(pin)}</code> (the pinned text; clause '
           f'numbers and steps are its own, and links go to the living draft, which may differ), quotes the text, says '
           f'what goes wrong, gives a small program where one shows it, proposes a change, and says what test262 '
           f'(at <code>{esc(t262)}</code>) tests. Every quotation of the text is checked against the pinned spec.html '
           f'when this site is built, step numbers included. Where a write-up is about an erratum of the model, the '
           f'<a href="../errata.html">Errata page</a> has that erratum\'s readings and the program that shows it.</p>'
           f'<p>The examples are Scripts unless they are a directory, whose <code>main.mjs</code> is a Module. They were '
           f'run on:</p><ul>{eng}</ul>'
           f'<p>The SpiderMonkey shell runs a Script file as it is; Node.js and Bun run it through a three-line shim that '
           f'evaluates it with <code>vm.runInThisContext</code>, as a Script in the main realm. <a href="results.html">The '
           f'examples\' runs</a> has every run\'s output. The proposed changes are proposals of this project, not of TC39: '
           f'none of these write-ups has been filed with TC39.</p>'
           f'<p>Each write-up\'s Upstream item says what a check of tc39/ecma262 found on {esc(checked)}: the issues and pull '
           f'requests that report, fix or relate to the defect, with their state on that day, and the commits that '
           f'changed the text. The Upstream column gives the first of them, or the fix. The record of the check is '
           f'<code>docs/spec-issues/upstream.tsv</code>; the site\'s build does not use the network.</p></section>')
    toc.insert(0, ("how", "How to read them", 1))
    n = len(iss)
    nd, np, no = counts.get("defect", 0), counts.get("proposal", 0), counts.get("none", 0)
    parts_lede = [f"{nd} defect{'s' if nd != 1 else ''} of the text",
                  f"{np} proposed normative change{'s' if np != 1 else ''}"]
    if no:
        parts_lede.append(f"{no} editorial item{'s' if no != 1 else ''} and question{'s' if no != 1 else ''}")
    summary_str = ", ".join(parts_lede[:-1]) + (f" and {parts_lede[-1]}" if len(parts_lede) > 1 else parts_lede[0])
    lede = (f"<p>{n} write-ups of places where the text of ECMA-262 cannot be followed as written, or where SpecTec "
            f"bakes in a non-literal reading or proposed change: {summary_str}. Each argues from the text alone.</p>")
    return Out(f"{DIR}/index.html", "Spec issues", "From <code>docs/spec-issues/</code>", lede, how + "".join(secs), toc)


def subprocess_out(cmd: list[str]) -> str:
    import subprocess
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip()


def writeup_links() -> dict[str, list[tuple[str, str]]]:
    """Each erratum's write-ups as (page under the site, label), for the Errata page."""
    out: dict[str, list[tuple[str, str]]] = {}
    for i in si.issues():
        for e in i.errata:
            out.setdefault(e, []).append((f"{DIR}/{i.slug}.html", f"{i.num}. {inline(i.title)}"))
    return out
