#!/usr/bin/env python3
"""test262's results: a run's record in the repository, and the page made from it.

    python3 scripts/test262_report.py record --results TSV --engine COMMIT --command 'CMD' [--date YYYY-MM-DD] \\
        [--jobs N] [--max-heap MB] [--note TEXT] [--out tests/test262/results/STAGE.tsv] \\
        [--rerun TSV --rerun-command 'CMD' --rerun-max-heap MB [--rerun-timeout S] [--rerun-rss-cap MB] \\
         [--rerun-jobs N] [--rerun-date YYYY-MM-DD]]
    python3 scripts/test262_report.py page [--record tests/test262/results/suite.tsv] --out DIR

`record` turns a results file of crates/test262-runner (`--results`: a first line `# build <id> stage <name>
test262 <revision> timeout <s> rss-cap <mb>`, then a row per test `<test>\\t<bucket>\\t<ms>\\t<detail>\\t<cost
ms>`, a resumed run appending, so that a test's last row counts) into the run's record:
tests/test262/results/<stage>.tsv. The record is what the site's test262 page is made from, so that the page
can be made again from the repository alone. It holds, in `# key value` lines: the engine's commit (the
commit of this repository the ecma-run that ran was built from), test262's revision, the stage (its
configuration, tests/test262/<stage>.conf), the date of the run, the command that ran it, the limits per test
(the wall clock in seconds, the memory cap in MB), the jobs and the runner's build id; then one row per test,
sorted by path: `<test>\\t<bucket>\\t<detail>`. It leaves out the times, which differ from run to run and
machine to machine and say nothing about the specification, so that a later run's record differs from this
one only where a test's result does. `--date` defaults to the day the results file was last written;
`--max-heap` (the ceiling of ecma-run's store, `--max-heap`) to ecma-run's default (`defaultMaxHeap`,
lean/Engine/Cli/Run.lean); `--note` is a line about the run (`resumed once`).

A second pass (`--rerun`, a results file of the same form) runs again, with larger limits, tests the first
did not pass. Its limits and command go into the header (`rerun-timeout`, `rerun-rss-cap`, `rerun-max-heap`,
`rerun-command`, `rerun-jobs`, `rerun-date`, `rerun-runner-build`; the timeout and the memory cap default to
its results file's), and each of its tests' rows has two more columns, the second pass's bucket and detail:
`<test>\t<bucket>\t<detail>\t<bucket2>\t<detail2>`, the first pass's result kept. A record without a second
pass has only three-column rows and no `rerun-` keys.

`page` (or `scripts/site_pages.py --test262-record`, which scripts/build_site.py passes when the record is
there) makes test262.html: the totals, as counts and shares of the tests run, and what a pass is; what is not
run and why, from the stage's configuration; every test that does not pass, by cause; the results by
directory; the revisions, the date and the command.
"""

from __future__ import annotations

import argparse
import datetime
import html
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORDS = ROOT / "tests/test262/results"
CONFS = ROOT / "tests/test262"
TEST262 = ROOT / "external/test262"
TESTS_URL = "https://github.com/tc39/test262/blob/{rev}/test/{path}"
BUCKETS = ["pass", "fail", "assertFailed", "stop", "timeout", "timeout(fuel)", "unsupported", "skip"]
KEYS = ["engine", "test262", "stage", "date", "command", "timeout", "rss-cap", "jobs", "runner-build"]
# Keys a record may have: the first pass's store ceiling, a note, and the second pass's (all of them, or none).
OPTIONAL = ["max-heap", "note"]
RERUN_KEYS = ["rerun-date", "rerun-command", "rerun-timeout", "rerun-rss-cap", "rerun-max-heap", "rerun-jobs",
              "rerun-runner-build"]
RUN_LEAN = ROOT / "lean/Engine/Cli/Run.lean"


def default_max_heap() -> str:
    m = re.search(r"(?m)^def defaultMaxHeap : Nat := (\d+)", RUN_LEAN.read_text())
    if not m:
        raise SystemExit(f"{RUN_LEAN}: no defaultMaxHeap")
    return m.group(1)


def size(mb: str) -> str:
    """Megabytes as the page says them: `3 GB`, `512 MB`."""
    if not mb.isdigit():
        return f"{mb} MB"
    n = int(mb)
    return f"{n // 1024} GB" if n >= 1024 and n % 1024 == 0 else f"{n:,} MB"


def esc(s: str) -> str:
    return html.escape(s, quote=True)


# ---------------------------------------------------------------------------------------------------------------
# The record


def read_runner(path: Path) -> tuple[dict[str, str], dict[str, tuple[str, str]]]:
    """A runner's results file: its header and each test's last row (bucket, detail)."""
    head: dict[str, str] = {}
    rows: dict[str, tuple[str, str]] = {}
    for ln in path.read_text().split("\n"):
        if not ln.strip():
            continue
        if ln.startswith("#"):
            for m in re.finditer(r"\b(build|stage|test262|timeout|rss-cap)\s+(\S+)", ln[1:]):
                head[m.group(1)] = m.group(2)
            continue
        f = ln.split("\t")
        if len(f) < 4 or f[1] not in BUCKETS:
            raise SystemExit(f"{path}: not a results row: {ln[:100]!r}")
        rows[f[0]] = (f[1], f[3])
    return head, rows


def write_record(results: Path, engine: str, command: str, date: str | None, jobs: str | None, out: Path | None,
                 max_heap: str | None = None, note: str | None = None, rerun: dict | None = None) -> Path:
    """The record of `results`, and of a second pass when `rerun` is {path, command, max_heap, timeout, rss_cap,
    jobs, date} (the last four may be None)."""
    head, rows = read_runner(results)
    stage = head.get("stage")
    if not stage or not head.get("test262"):
        raise SystemExit(f"{results}: no `# build … stage … test262 …` line")
    if not (CONFS / f"{stage}.conf").is_file():
        raise SystemExit(f"{results}: no tests/test262/{stage}.conf")
    date = date or datetime.date.fromtimestamp(results.stat().st_mtime).isoformat()
    meta = {"engine": engine, "test262": head["test262"], "stage": stage, "date": date, "command": command,
            "timeout": head.get("timeout", "?"), "rss-cap": head.get("rss-cap", "?"), "jobs": jobs or "?",
            "runner-build": head.get("build", "?"), "max-heap": max_heap or default_max_heap()}
    if note:
        meta["note"] = note
    second: dict[str, tuple[str, str]] = {}
    if rerun:
        rp = Path(rerun["path"])
        h2, second = read_runner(rp)
        if h2.get("test262") != head["test262"] or h2.get("stage") != stage:
            raise SystemExit(f"{rp}: test262 {h2.get('test262')} stage {h2.get('stage')}, but the first pass's "
                             f"are {head['test262']} {stage}")
        extra = sorted(set(second) - set(rows))
        if extra:
            raise SystemExit(f"{rp}: {len(extra)} tests the first pass did not run ({extra[0]}, …)")
        passed = sorted(t for t in second if rows[t][0] == "pass")
        if passed:
            raise SystemExit(f"{rp}: {len(passed)} tests the first pass passed ({passed[0]}, …)")
        meta.update({"rerun-date": rerun.get("date") or datetime.date.fromtimestamp(rp.stat().st_mtime).isoformat(),
                     "rerun-command": rerun["command"], "rerun-timeout": rerun.get("timeout") or h2.get("timeout", "?"),
                     "rerun-rss-cap": rerun.get("rss_cap") or h2.get("rss-cap", "?"),
                     "rerun-max-heap": rerun["max_heap"], "rerun-jobs": rerun.get("jobs") or "?",
                     "rerun-runner-build": h2.get("build", "?")})
    out = out or RECORDS / f"{stage}.tsv"
    out.parent.mkdir(parents=True, exist_ok=True)
    lines = ["# test262 on ecma-run: one run's record (scripts/test262_report.py record). The times are left out.",
             *(f"# {k} {meta[k]}" for k in KEYS + OPTIONAL + RERUN_KEYS if k in meta)]
    for t, (b, d) in sorted(rows.items()):
        lines.append(f"{t}\t{b}\t{d}" + (f"\t{second[t][0]}\t{second[t][1]}" if t in second else ""))
    out.write_text("\n".join(lines) + "\n")
    by = Counter(b for b, _ in rows.values())
    print(f"{out.relative_to(ROOT) if out.is_relative_to(ROOT) else out}: {len(rows)} tests, "
          + ", ".join(f"{b} {by[b]}" for b in BUCKETS if by[b]))
    if second:
        by2 = Counter(b for b, _ in second.values())
        print(f"  the second pass: {len(second)} tests, " + ", ".join(f"{b} {by2[b]}" for b in BUCKETS if by2[b]))
    return out


def read_record(path: Path) -> tuple[dict[str, str], dict[str, tuple[str, str, str | None, str | None]]]:
    """A record's header and each test's (bucket, detail, second pass's bucket or None, its detail or None)."""
    meta: dict[str, str] = {}
    rows: dict[str, tuple[str, str, str | None, str | None]] = {}
    for ln in path.read_text().split("\n"):
        if not ln:
            continue
        if ln.startswith("# "):
            k, _, v = ln[2:].partition(" ")
            if k in KEYS or k in OPTIONAL or k in RERUN_KEYS:
                meta[k] = v
            continue
        f = ln.split("\t")
        if len(f) not in (3, 5) or f[1] not in BUCKETS or (len(f) == 5 and f[3] not in BUCKETS):
            raise SystemExit(f"{path}: not a record row: {ln[:100]!r}")
        rows[f[0]] = (f[1], f[2], f[3], f[4]) if len(f) == 5 else (f[1], f[2], None, None)
    missing = [k for k in KEYS if k not in meta]
    if missing:
        raise SystemExit(f"{path}: the record has no {', '.join(missing)}")
    has2 = any(r[2] is not None for r in rows.values())
    got2 = [k for k in RERUN_KEYS if k in meta]
    if has2 and len(got2) != len(RERUN_KEYS):
        raise SystemExit(f"{path}: second-pass rows without the header's {', '.join(k for k in RERUN_KEYS if k not in meta)}")
    if got2 and not has2:
        raise SystemExit(f"{path}: a second pass in the header and no row of it")
    return meta, rows


# ---------------------------------------------------------------------------------------------------------------
# The configuration


def conf_sections(conf: Path) -> dict[str, list[tuple[str, str]]]:
    """Each section's entries, each with the comment block above it (the reason the file gives, or "")."""
    out: dict[str, list[tuple[str, str]]] = {}
    sec, reason, last_comment = None, "", False
    for ln in conf.read_text().split("\n"):
        s = ln.strip()
        m = re.fullmatch(r"\[([\w-]+)\]", s)
        if m:
            sec, reason, last_comment = m.group(1), "", False
            out[sec] = []
            continue
        if not s:
            continue
        if s.startswith("#"):
            reason = (reason + " " if last_comment else "") + s[1:].strip()
            last_comment = True
            continue
        last_comment = False
        if sec:
            out[sec].append((s.split("#")[0].strip(), reason))
    return out


def conf_header(conf: Path) -> list[str]:
    head = []
    for ln in conf.read_text().split("\n"):
        if not ln.startswith("#"):
            break
        head.append(ln[1:].strip())
    return head


# ---------------------------------------------------------------------------------------------------------------
# The page


def mode_and(detail: str) -> tuple[str, str]:
    m = re.match(r"(non-strict|strict|module): (.*)$", detail)
    return (m.group(1), m.group(2)) if m else ("", detail)


def cause(bucket: str, detail: str, second: bool = False) -> tuple[str, str, str]:
    """A test that did not pass: (group, cause, layer). The layer is `engine` (a limit of the engine: its
    store, its numbers, the time or memory a test may take, the native stack) or `specification` (the
    specification's machine gives no answer, or a wrong one: a step with no reading, a value of the wrong
    sort, a failed Assert, a wrong result). `second`: the result is the second pass's."""
    _, d = mode_and(detail)
    d = re.sub(r"\b[\w.-]*-run: ", "", d)
    run = "the second pass" if second else "the run"
    if bucket == "stop":
        kind, _, site = d.partition(":")
        if kind == "implLimit":
            if site in ("? ?", ""):
                return ("limit", f"an implementation limit; {run} recorded <code>implLimit</code> at no step", "engine")
            return ("limit", f"an implementation limit at <code>{esc(site)}</code>", "engine")
        if kind == "crash":
            return ("limit", f"the process ended by {esc(site)} (the native stack)", "engine")
        return ("spec", f"a stop of the machine, <code>{esc(kind)}</code> at <code>{esc(site)}</code>", "specification")
    if bucket == "timeout":
        return ("timeout", f"over the {esc(d)}", "engine")
    if bucket == "timeout(fuel)":
        return ("timeout", "out of fuel (call depth or a loop's rounds)", "engine")
    if bucket == "unsupported":
        return ("unsupported", f"needs <code>{esc(d)}</code>, which the test host does not have", "engine")
    return ("fail", f"<code>{esc(d)}</code>", "specification")


GROUPS = [
    ("fail", "Failures", "A wrong answer: an uncaught exception, a missing expected error, a valid program "
     "rejected, or a failed Assert of the specification."),
    ("spec", "Stops of the specification's machine", "The machine reached a step it has no reading for, or a value "
     "of the wrong sort: a gap of the specification layer."),
    ("limit", "Stops at an implementation limit", "The engine stopped where the specification would go on: a limit "
     "the claim allows (What is proved)."),
    ("timeout", "Time-outs", "The test took longer than the wall-clock limit or more memory than the cap."),
    ("unsupported", "Unsupported", "The test needs a host feature the test host does not provide."),
]


def pct(a: int, b: int) -> str:
    return f"{100 * a / b:.2f}%" if b else "–"


def limits(timeout: str, store: str, rss: str) -> str:
    return f"{esc(timeout)} s of wall clock, a store of {esc(size(store))} and {esc(size(rss))} of memory per test"


def page(record: Path, test262: Path = TEST262, conf_dir: Path = CONFS) -> dict:
    meta, rows = read_record(record)
    rev, stage = meta["test262"], meta["stage"]
    conf = conf_dir / f"{stage}.conf"
    secs = conf_sections(conf)
    n = len(rows)
    by = Counter(r[0] for r in rows.values())  # the first pass
    ran = n - by.get("skip", 0)
    first_pass = by.get("pass", 0)
    rerun = {t: r for t, r in rows.items() if r[2] is not None}
    final = {t: ((r[2], r[3]) if r[2] is not None else (r[0], r[1])) for t, r in rows.items()}
    by_final = Counter(b for b, _ in final.values())
    passed = by_final.get("pass", 0)
    nonpass = {t: bd for t, bd in final.items() if bd[0] not in ("pass", "skip")}
    causes: dict[str, dict[str, list[tuple[str, str]]]] = defaultdict(lambda: defaultdict(list))
    layer_n: Counter = Counter()
    for t, (b, d) in sorted(nonpass.items()):
        g, c, layer = cause(b, d, t in rerun)
        causes[g][c].append((t, mode_and(d)[0]))
        layer_n[layer] += 1
    store1 = meta.get("max-heap", "?")
    lim1 = limits(meta["timeout"], store1, meta["rss-cap"])

    def link(t: str) -> str:
        return f'<a href="{esc(TESTS_URL.format(rev=rev, path=t))}"><code>{esc(t)}</code></a>'

    body = []
    # The totals.
    tiles = [("Tests run", ran), ("Pass", passed), ("Do not pass", len(nonpass)), ("Not run", by.get("skip", 0))]
    body.append('<h2 id="totals">Totals</h2><ul class="facts">' + "".join(
        f"<li><b>{v:,}</b><span>{esc(k)}</span></li>" for k, v in tiles) + "</ul>")
    spec_n = layer_n.get("specification", 0)
    verdict = ("No test fails, or stops, for a reason of the specification layer: every test that does not pass "
               "stopped at a limit of the engine or ran out of time or memory." if spec_n == 0 else
               f"{spec_n:,} tests do not pass for a reason of the specification layer (a wrong answer, or a stop "
               f"of the specification's machine): they are listed first below.")
    if rerun:
        p2 = sum(1 for r in rerun.values() if r[2] == "pass")
        head = (f"{passed:,} of the {ran:,} tests run pass ({pct(passed, ran)}), counting a test as passing if it "
                f"passes in either of the two passes below.")
    else:
        head = f"{passed:,} of the {ran:,} tests run pass ({pct(passed, ran)})."
    body.append(f'<p class="verdict"><strong>{esc(head)}</strong> {esc(verdict)}</p>')
    trs = []
    for b in BUCKETS:
        if b == "skip" or not by.get(b):
            continue
        trs.append(f'<tr><td>{esc(b)}</td><td class="num">{by[b]:,}</td><td class="num">{pct(by[b], ran)}</td></tr>')
    body.append(f'<h3 id="first">The first pass</h3><p>Every test, under {lim1}: {first_pass:,} pass '
                f'({pct(first_pass, ran)} of the tests run).</p>'
                '<div class="tablebox"><table class="t262 totals"><thead><tr><th>Result</th><th class="num">Tests</th>'
                '<th class="num">Share of the tests run</th></tr></thead><tbody>' + "".join(trs) + "</tbody></table></div>")
    if rerun:
        k2 = len(rerun) - p2
        by2 = Counter(r[2] for r in rerun.values())
        rest = ", ".join(f"{by2[b]:,} {b}" for b in BUCKETS if b != "pass" and by2.get(b))
        lim2 = limits(meta["rerun-timeout"], meta["rerun-max-heap"], meta["rerun-rss-cap"])
        gc2 = " and mark-and-sweep store collection (<code>--gc</code>)" if "--gc" in meta.get("rerun-command", "") else ""
        hit = all(r[0] in ("stop", "timeout", "timeout(fuel)") for r in rerun.values())
        which = "hit one of those limits" if hit else "did not pass in the first pass"
        body.append(f'<h3 id="second">The second pass</h3><p>The {len(rerun):,} tests that {which} '
                    f'were run again with {lim2}{gc2}: {p2:,} pass; {k2:,} still do not pass'
                    + (f" ({rest})" if rest else "") + ".</p>")
    body.append(
        '<p><strong>Why the store has a ceiling.</strong> By default the engine\'s store only grows: every value the '
        'machine makes stays in it, and no cell is freed, so the memory a run uses grows with the steps it takes. '
        '<code>ecma-run</code> therefore stops a run whose store reaches a ceiling (<code>--max-heap</code>, a stop '
        'at an implementation limit) rather than let it take the machine\'s memory. An optional flag, '
        '<code>--gc</code> (outside <a href="what-is-proved.html#outside"><code>Engine.implements</code></a>), '
        'sweeps unreachable cells in place while keeping live addresses monotonic, so <code>--max-heap</code> bounds '
        'live cells rather than total allocations.</p>')
    body.append(
        '<h3 id="pass">What a pass is</h3><p>The runner (<code>crates/test262-runner</code>) runs each test on '
        '<code>ecma-run</code>, the engine\'s whole-program driver, after its harness (<code>assert.js</code>, '
        '<code>sta.js</code>, <code>doneprintHandle.js</code> for an <code>async</code> test, then the test\'s '
        '<code>includes</code>) run as Scripts in the same realm. A test runs twice, in non-strict code and in strict '
        'code (<code>"use strict";</code> before the test alone), unless its flags say otherwise: once for '
        '<code>onlyStrict</code>, <code>noStrict</code> or <code>raw</code> (<code>raw</code> without the harness), '
        'and once, as a module, for <code>module</code>. A run passes when it completes normally, or, for a negative '
        'test, throws an error of the expected constructor (a <code>parse</code> negative test is only parsed); an '
        '<code>async</code> test passes when its <code>$DONE</code> prints <code>Test262:AsyncTestComplete</code>. '
        'The test passes when every run passes, and counts once, under the worse of its runs; when the first run '
        'does not pass for want of an answer (a stop, a time-out, or the test host lacking something), the second '
        'is not run. Every run executes the test\'s own assertions, the harness\'s functions that throw a '
        '<code>Test262Error</code>. A test over the wall clock or the memory cap is a time-out.</p>')

    # Not run.
    top = sorted(p.name for p in (test262 / "test").iterdir() if p.is_dir())
    paths = [p for p, _ in secs.get("paths", [])]
    not_in = [d for d in top if d not in paths]
    skip_by: Counter = Counter(r[1] for r in rows.values() if r[0] == "skip")
    feat_reason = {f: r for f, r in secs.get("skip-features", [])}
    flag_reason = {f: r for f, r in secs.get("skip-flags", [])}
    feat_n: Counter = Counter()
    for d, k in skip_by.items():
        m = re.match(r"feature (.*)$", d)
        if m:
            for f in m.group(1).split(", "):
                feat_n[f] += k
    by_reason: dict[str, list[str]] = defaultdict(list)
    for f, r in secs.get("skip-features", []):
        by_reason[r].append(f)
    missing: list[str] = []
    items = []
    for r, fs in by_reason.items():
        if not r:
            missing += fs
        cnt = sum(feat_n.get(f, 0) for f in fs)
        feats = ", ".join(f"<code>{esc(f)}</code>{f' ({feat_n[f]:,})' if feat_n.get(f) else ''}" for f in fs)
        items.append(f"<li><p>{esc(r) if r else '<em>No reason given.</em>'} <span class=muted>{cnt:,} tests.</span>"
                     f"</p><p class=featlist>{feats}</p></li>")
    flags = [(f, r) for f, r in secs.get("skip-flags", [])]
    for f, r in flags:
        if not r:
            missing.append(f"flag {f}")
        items.append(f"<li><p>The flag <code>{esc(f)}</code>: {esc(r) if r else '<em>no reason given</em>'}.</p></li>")
    head_text = " ".join(conf_header(conf))
    head_sents = re.split(r"(?<=[.;)])\s+", head_text)

    def said(name: str) -> str:
        """The configuration header's sentence that names `name`, if any."""
        hit = next((x for x in head_sents if name in x), "")
        return f' <span class="muted">(the configuration\'s header: <q>{esc(hit)}</q>)</span>' if hit else ""
    excl = secs.get("exclude", [])
    ex_items = "".join(f"<li><code>{esc(p)}</code>: {esc(r) if r else '<em>no reason given beside it</em>' + said(p)}</li>"
                       for p, r in excl)
    missing += [p for p, r in excl if not r]
    multi = sum(k for d, k in skip_by.items() if "," in d)
    body.append(
        f'<h2 id="not-run">What is not run, and why</h2>'
        f'<p>The run is the stage <code>{esc(stage)}</code> of <code data-verbatim>tests/test262/{esc(stage)}.conf</code>. '
        f'It runs the directories {", ".join(f"<code>{esc(p)}</code>" for p in paths)}; not '
        f'{", ".join(f"<code>{esc(d)}</code>{said(d)}" for d in not_in) or "none"}.</p>'
        f'<p>Left out of those directories (<code>[exclude]</code>):</p><ul>{ex_items}</ul>'
        f'<p>{by.get("skip", 0):,} tests are not run because they need a feature the configuration leaves out '
        f'(<code>[skip-features]</code>; a test that needs several counts under each, {multi:,} do), by the '
        f'reason the configuration gives:</p><ul class="skips">{"".join(items)}</ul>'
        + (f'<p>The configuration gives no reason for {", ".join(f"<code>{esc(x)}</code>" for x in missing)}.</p>'
           if missing else '<p>The configuration gives a reason for every feature it leaves out.</p>'))

    # Every test that does not pass, by cause.
    after = " after the second pass" if rerun else ""
    sections = [f'<h2 id="not-passing">Every test that does not pass{after}, by cause ({len(nonpass):,})</h2>']
    if rerun:
        sections.append("<p>A test's result here is the second pass's where it was run again, else the first's.</p>")
    rows_c = []
    for g, title, _ in GROUPS:
        k = sum(len(v) for v in causes.get(g, {}).values())
        layer = "specification" if g in ("fail", "spec") else "engine"
        rows_c.append(f'<tr class="{"bad" if layer == "specification" and k else ""}"><td><a href="#c-{g}">{esc(title)}'
                      f'</a></td><td>{"the specification layer" if layer == "specification" else "the engine"}</td>'
                      f'<td class="num">{k:,}</td></tr>')
    sections.append('<div class="tablebox"><table class="t262 causes"><thead><tr><th>Cause</th><th>Where it lies</th>'
                    '<th class="num">Tests</th></tr></thead><tbody>' + "".join(rows_c) + "</tbody></table></div>")
    for g, title, what in GROUPS:
        cs = causes.get(g, {})
        k = sum(len(v) for v in cs.values())
        if not k:
            sections.append(f'<h3 id="c-{g}">{esc(title)}</h3><p>None.</p>')
            continue
        lis = []
        for c, ts in sorted(cs.items(), key=lambda x: (-len(x[1]), x[0])):
            dirs = Counter("/".join(t.split("/")[:2]) for t, _ in ts)
            where = ", ".join(f"{esc(d)} ({v})" for d, v in dirs.most_common(6)) + (" …" if len(dirs) > 6 else "")
            tl = "".join(f"<li>{link(t)} <span class=muted>{esc(m)}</span></li>" for t, m in ts)
            lis.append(f'<li><details><summary><b class="num">{len(ts):,}</b> {c} <span class="muted">· {where}'
                       f'</span></summary><ul class="results">{tl}</ul></details></li>')
        sections.append(f'<h3 id="c-{g}">{esc(title)} ({k:,})</h3><p>{esc(what)}</p><ul class="sites">{"".join(lis)}</ul>')
    body.append("".join(sections))

    # What passed only in the second pass, by what stopped it in the first, then by directory (folded).
    toc_more = []
    if rerun:
        later = {t: r for t, r in rerun.items() if r[2] == "pass"}
        kinds: dict[str, list[str]] = defaultdict(list)
        for t, r in sorted(later.items()):
            _, d = mode_and(r[1])
            d = re.sub(r"\b[\w.-]*-run: ", "", d)
            if r[0] == "stop" and d.startswith("implLimit"):
                with_gc = " and --gc" if "--gc" in meta.get("rerun-command", "") else ""
                kinds[f"stopped at the store's ceiling of {size(store1)}: they pass with a store of "
                      f"{size(meta['rerun-max-heap'])}{with_gc}"].append(t)
            elif r[0] == "timeout":
                kinds[f"over the {d} in the first pass"].append(t)
            else:
                kinds[f"{r[0]} in the first pass ({d})"].append(t)
        lis = []
        for kind, ts in sorted(kinds.items(), key=lambda x: -len(x[1])):
            dirs: dict[str, list[str]] = defaultdict(list)
            for t in ts:
                dirs["/".join(t.split("/")[:2])].append(t)
            dl = "".join(f'<li><details><summary><b class="num">{len(v):,}</b> <code>{esc(d)}</code></summary>'
                         f'<ul class="results">{"".join(f"<li>{link(t)}</li>" for t in v)}</ul></details></li>'
                         for d, v in sorted(dirs.items(), key=lambda x: (-len(x[1]), x[0])))
            lis.append(f'<li><p><b class="num">{len(ts):,}</b> {esc(kind)}.</p><ul class="sites">{dl}</ul></li>')
        body.append(f'<h2 id="second-only">Passing only in the second pass ({len(later):,})</h2>'
                    f'<p>Tests that did not pass under the first pass\'s limits and pass under the second\'s, by what '
                    f'the first pass recorded, then by directory.</p><ul class="later">{"".join(lis)}</ul>')
        toc_more = [("second-only", "Passing only in the second pass", 1)]

    # By directory.
    dirs: dict[str, Counter] = defaultdict(Counter)
    for t, (b, _) in final.items():
        parts = t.split("/")
        dirs["/".join(parts[:2]) if len(parts) > 2 else parts[0]][b] += 1
    trs = []
    for d in sorted(dirs):
        c = dirs[d]
        r = sum(c.values()) - c.get("skip", 0)
        np_ = r - c.get("pass", 0)
        trs.append(f'<tr{" class=bad" if np_ else ""}><td><code>{esc(d)}</code></td><td class="num">{r:,}</td>'
                   f'<td class="num">{c.get("pass", 0):,}</td><td class="num">{np_ or ""}</td>'
                   f'<td class="num">{c.get("skip", 0) or ""}</td><td class="num">{pct(c.get("pass", 0), r) if r else "–"}</td></tr>')
    body.append('<h2 id="directories">By directory</h2><p>Two levels of test262\'s <code>test/</code>'
                + (", a test passing if it passes in either pass" if rerun else "")
                + '; a row is marked where a test does not pass.</p><div class="tablebox tall"><table class="t262 dirs"><thead><tr>'
                '<th>Directory</th><th class="num">Run</th><th class="num">Pass</th><th class="num">Not passing</th>'
                '<th class="num">Not run</th><th class="num">Pass rate</th></tr></thead><tbody>' + "".join(trs)
                + "</tbody></table></div>")

    # The run.
    run = ('<h2 id="run">The run</h2><dl class="split">'
           f'<dt>engine</dt><dd><code>ecma-run</code> built from commit <code>{esc(meta["engine"])}</code> of this repository</dd>'
           f'<dt>test262</dt><dd><code>{esc(rev)}</code></dd>'
           f'<dt>selection</dt><dd><code data-verbatim>tests/test262/{esc(stage)}.conf</code>, {n:,} tests</dd>'
           f'<dt>first pass</dt><dd>{esc(meta["date"])}; {lim1}; {esc(meta["jobs"])} jobs at a time'
           + (f'; {esc(meta["note"])}' if meta.get("note") else "") + "</dd>"
           f'<dt>command</dt><dd><pre class="cmd" data-verbatim>{esc(meta["command"])}</pre></dd>'
           f'<dt>runner build</dt><dd><code>{esc(meta["runner-build"])}</code> (the hash of the tools and the run\'s '
           f'configuration, as <code>crates/test262-runner</code> records it)</dd>')
    if rerun:
        run += (f'<dt>second pass</dt><dd>{esc(meta["rerun-date"])}; the {len(rerun):,} tests the first pass did not '
                f'pass; {limits(meta["rerun-timeout"], meta["rerun-max-heap"], meta["rerun-rss-cap"])}; '
                f'{esc(meta["rerun-jobs"])} jobs at a time; runner build <code>{esc(meta["rerun-runner-build"])}</code></dd>'
                f'<dt>command</dt><dd><pre class="cmd" data-verbatim>{esc(meta["rerun-command"])}</pre></dd>')
    run += (f'<dt>record</dt><dd><code data-verbatim>{esc(record.relative_to(ROOT).as_posix() if record.is_relative_to(ROOT) else record.name)}</code>: '
            f'this page is made from it (<code>scripts/test262_report.py</code>)</dd></dl>')
    body.append(run)

    toc = [("totals", "Totals", 1), ("first", "The first pass", 2)] + ([("second", "The second pass", 2)] if rerun else []) \
        + [("pass", "What a pass is", 2), ("not-run", "What is not run", 1), ("not-passing", "Not passing, by cause", 1)] \
        + [(f"c-{g}", t, 2) for g, t, _ in GROUPS] + toc_more + [("directories", "By directory", 1), ("run", "The run", 1)]
    either = ", counting a test that passes in either of two passes" if rerun else ""
    return {
        "title": "test262",
        "eyebrow": f"One run of test262 on the engine · <code>{esc(record.name)}</code>",
        "lede": (f"<p>test262 is TC39's conformance suite. This page reports one run of it on the engine, "
                 f"<code>ecma-run</code> at commit <code>{esc(meta['engine'])}</code>, test262 at "
                 f"<code>{esc(rev[:9])}</code>, on {esc(meta['date'])}: {passed:,} of the {ran:,} tests run pass "
                 f"({pct(passed, ran)}){either}.</p>"),
        "body": "\n".join(body),
        "toc": toc,
        "counts": dict(by_final),
        "first_counts": dict(by),
        "rerun": len(rerun),
        "meta": meta,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record", help="a runner's results file as the run's record")
    r.add_argument("--results", type=Path, required=True)
    r.add_argument("--engine", required=True, help="the commit the ecma-run that ran was built from")
    r.add_argument("--command", required=True, help="the command line that ran it")
    r.add_argument("--date", help="the day of the run (default: the day the results file was last written)")
    r.add_argument("--jobs", help="the jobs the run ran at a time")
    r.add_argument("--max-heap", help="the store's ceiling in MB, ecma-run's --max-heap (default: ecma-run's default)")
    r.add_argument("--note", help="a line about the run, such as `resumed once`")
    r.add_argument("--rerun", type=Path, help="a second pass's results file: tests the first did not pass, run again")
    r.add_argument("--rerun-command", help="the command line of the second pass")
    r.add_argument("--rerun-max-heap", help="the second pass's store ceiling in MB (its --run-arg --max-heap)")
    r.add_argument("--rerun-timeout", help="the second pass's wall clock in s (default: its results file's)")
    r.add_argument("--rerun-rss-cap", help="the second pass's memory cap in MB (default: its results file's)")
    r.add_argument("--rerun-jobs", help="the jobs the second pass ran at a time")
    r.add_argument("--rerun-date", help="the day of the second pass (default: the day its file was last written)")
    r.add_argument("--out", type=Path)
    p = sub.add_parser("page", help="test262.html from a record")
    p.add_argument("--record", type=Path, default=RECORDS / "suite.tsv")
    p.add_argument("--test262", type=Path, default=TEST262)
    p.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    if a.cmd == "record":
        rerun = None
        if a.rerun:
            if not (a.rerun_command and a.rerun_max_heap):
                ap.error("--rerun needs --rerun-command and --rerun-max-heap")
            rerun = {"path": a.rerun, "command": a.rerun_command, "max_heap": a.rerun_max_heap,
                     "timeout": a.rerun_timeout, "rss_cap": a.rerun_rss_cap, "jobs": a.rerun_jobs, "date": a.rerun_date}
        write_record(a.results, a.engine, a.command, a.date, a.jobs, a.out, a.max_heap, a.note, rerun)
        return 0
    pg = page(a.record, a.test262)
    import site_pages
    a.out.mkdir(parents=True, exist_ok=True)
    facts = {"rev": site_pages.git("rev-parse", "--short", "HEAD"), "dirty": False, "ecma262": "",
             "test262": pg["meta"]["test262"]}
    page_ = site_pages.Page("test262.html", pg["title"], pg["eyebrow"], pg["lede"], pg["body"], pg["toc"], wide=True)
    (a.out / "test262.html").write_text(site_pages.frame(page_, {"test262.html"}, facts))
    print(" ".join(f"{k} {v}" for k, v in sorted(pg["counts"].items())))
    return 0


if __name__ == "__main__":
    sys.exit(main())
