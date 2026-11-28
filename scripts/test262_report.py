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
    skip_n = by.get("skip", 0)
    spec_n = layer_n.get("specification", 0)
    stop_n = sum(1 for b, _ in final.values() if b == "stop")
    fail_stop_n = spec_n + stop_n
    t1 = meta["timeout"]
    t2 = meta.get("rerun-timeout", "")

    if rerun:
        tiles = [
            ("Tests run", f"{ran:,}", f"{skip_n:,} skipped by {stage}.conf"),
            (f"Pass ({t1} s pass)", f"{first_pass:,}", f"{pct(first_pass, ran)} · {size(store1)} store, proved"),
            (f"Pass ({t2} s pass)", f"{passed:,}", f"{pct(passed, ran)} · +{passed - first_pass:,} with {size(meta['rerun-max-heap'])} & --gc"),
            ("Failures / stops", f"{fail_stop_n:,}", f"{len(nonpass):,} wall-clock time-outs"),
        ]
    else:
        tiles = [
            ("Tests run", f"{ran:,}", f"{skip_n:,} skipped by {stage}.conf"),
            ("Pass", f"{passed:,}", pct(passed, ran)),
            ("Failures / stops", f"{fail_stop_n:,}", f"{len(nonpass):,} time-outs"),
        ]
    body.append('<ul class="facts" aria-label="Totals">' + "".join(
        f"<li><b>{esc(v)}</b><span>{esc(k)} — {esc(sub)}</span></li>" for k, v, sub in tiles) + "</ul>")

    # Single unified table by two-level directory, with Pass (first pass) and Pass (long-timeout pass) columns.
    dirs1: dict[str, Counter] = defaultdict(Counter)
    dirs2: dict[str, Counter] = defaultdict(Counter)
    for t, r in rows.items():
        parts = t.split("/")
        d = "/".join(parts[:2]) if len(parts) > 2 else parts[0]
        dirs1[d][r[0]] += 1
        b_fin = r[2] if r[2] is not None else r[0]
        dirs2[d][b_fin] += 1

    has_other = fail_stop_n > 0 or by_final.get("unsupported", 0) > 0

    def row_html(label_html: str, c1: Counter, c2: Counter, is_total: bool = False) -> str:
        r_cnt = sum(c2.values()) - c2.get("skip", 0)
        p1_cnt = c1.get("pass", 0)
        p2_cnt = c2.get("pass", 0)
        to_cnt = c2.get("timeout", 0) + c2.get("timeout(fuel)", 0)
        oth_cnt = r_cnt - p2_cnt - to_cnt
        sk_cnt = c2.get("skip", 0)
        np_cnt = r_cnt - p2_cnt
        cls = ' class="total-row"' if is_total else (' class="bad"' if np_cnt else "")
        cols = [f"<td>{label_html}</td>", f'<td class="num">{r_cnt:,}</td>', f'<td class="num">{p1_cnt:,}</td>']
        if rerun:
            delta = f' <span class="muted">(+{p2_cnt - p1_cnt:,})</span>' if p2_cnt > p1_cnt else ""
            cols.append(f'<td class="num">{p2_cnt:,}{delta}</td>')
        if has_other:
            cols.append(f'<td class="num">{oth_cnt:,}</td>' if (oth_cnt or is_total) else '<td class="num"></td>')
        cols.append(f'<td class="num">{to_cnt:,}</td>' if (to_cnt or is_total) else '<td class="num"></td>')
        cols.append(f'<td class="num">{sk_cnt:,}</td>' if (sk_cnt or is_total) else '<td class="num"></td>')
        cols.append(f'<td class="num">{pct(p2_cnt, r_cnt) if r_cnt else "–"}</td>')
        return f"<tr{cls}>{''.join(cols)}</tr>"

    ths = [
        "<th>Directory</th>",
        '<th class="num">Run</th>',
        f'<th class="num">Pass ({esc(t1)} s)</th>' if rerun else '<th class="num">Pass</th>',
    ]
    if rerun:
        gc_lbl = ", --gc" if "--gc" in meta.get("rerun-command", "") else ""
        ths.append(f'<th class="num">Pass ({esc(t2)} s{esc(gc_lbl)})</th>')
    if has_other:
        ths.append('<th class="num">Fail / stop</th>')
    ths += ['<th class="num">Time-out</th>', '<th class="num">Skipped</th>', '<th class="num">Pass rate</th>']

    total_row = row_html("<strong>Total</strong>", by, by_final, is_total=True)
    dir_rows = "".join(row_html(f"<code>{esc(d)}</code>", dirs1[d], dirs2[d]) for d in sorted(dirs2))
    body.append(
        '<h2 id="results">Results by directory</h2>'
        '<p>Two levels of <code>test262/test/</code>; rows with remaining time-outs are highlighted.</p>'
        '<div class="tablebox"><table class="t262 dirs"><thead><tr>' + "".join(ths) + "</tr></thead>"
        "<tbody>" + total_row + dir_rows + "</tbody></table></div>"
    )

    if nonpass:
        tl = "".join(f"<li>{link(t)} <span class=muted>{esc(mode_and(d)[0])}</span></li>"
                     for t, (_, d) in sorted(nonpass.items()))
        top_dirs = Counter("/".join(t.split("/")[:2]) for t in nonpass)
        where = ", ".join(f"{esc(d)} ({v})" for d, v in top_dirs.most_common(5)) + (" …" if len(top_dirs) > 5 else "")
        body.append(
            f'<details class="jssrc"><summary>Show all {len(nonpass):,} non-passing tests '
            f'({where})</summary><ul class="results">{tl}</ul></details>'
        )

    # Compact setup & skipped summary.
    top = sorted(p.name for p in (test262 / "test").iterdir() if p.is_dir())
    paths = [p for p, _ in secs.get("paths", [])]
    not_in = [d for d in top if d not in paths]
    lim2_txt = ""
    if rerun:
        lim2 = limits(meta["rerun-timeout"], meta["rerun-max-heap"], meta["rerun-rss-cap"])
        gc2 = (" and mark-and-sweep store collection (<code>--gc</code>, outside "
               '<a href="what-is-proved.html#outside"><code>Engine.implements</code></a>)'
               if "--gc" in meta.get("rerun-command", "") else "")
        lim2_txt = (f" The <strong>{esc(t2)} s pass</strong> reruns the {len(rerun):,} non-passing tests with "
                    f"{lim2}{gc2}, adding {passed - first_pass:,} passes.")

    body.append(
        f'<h2 id="setup">How the suite was run</h2>'
        f'<p><code>crates/test262-runner</code> runs each test on <code>ecma-run</code> after its harness in both '
        f'non-strict and strict mode (once for <code>onlyStrict</code>, <code>noStrict</code>, <code>raw</code>, or '
        f'<code>module</code>), executing the test\'s own assertions. The <strong>{esc(t1)} s pass</strong> runs '
        f'default proved <code>ecma-run</code> under {lim1}.{lim2_txt}</p>'
        f'<p><strong>Skipped ({skip_n:,} tests, <code data-verbatim>tests/test262/{esc(stage)}.conf</code>):</strong> '
        f'runs {", ".join(f"<code>{esc(p)}</code>" for p in paths)} (leaving out '
        f'{", ".join(f"<code>{esc(d)}</code>" for d in not_in) or "none"} and <code>staging/sm</code>), and skips '
        f'tests gated on features outside the pinned ECMA-262 specification (<code>Temporal</code>, unmerged '
        f'proposals, ECMA-402, and non-standard <code>caller</code>).</p>'
    )

    run = ('<dl class="split">'
           f'<dt>engine</dt><dd><code>ecma-run</code> at commit <code>{esc(meta["engine"])}</code> · '
           f'test262 at <code>{esc(rev[:12])}</code> ({esc(meta["date"])})</dd>'
           f'<dt>{esc(t1)} s command</dt><dd><pre class="cmd" data-verbatim>{esc(meta["command"])}</pre></dd>')
    if rerun:
        run += f'<dt>{esc(t2)} s command</dt><dd><pre class="cmd" data-verbatim>{esc(meta["rerun-command"])}</pre></dd>'
    run += (f'<dt>record</dt><dd><code data-verbatim>{esc(record.relative_to(ROOT).as_posix() if record.is_relative_to(ROOT) else record.name)}</code></dd>'
            '</dl>')
    body.append(run)

    toc = [("results", "Results by directory", 1), ("setup", "How the suite was run", 1)]
    lede = (
        f"<p>TC39's conformance suite (<code>{esc(rev[:9])}</code>) on <code>ecma-run</code> "
        f"(commit <code>{esc(meta['engine'])}</code>): <strong>{first_pass:,}</strong> of "
        f"<strong>{ran:,}</strong> tests pass in the default {esc(t1)} s pass ({pct(first_pass, ran)}), "
        + (f"rising to <strong>{passed:,}</strong> ({pct(passed, ran)}) with the {esc(t2)} s pass — "
           if rerun else "— ")
        + f"with <strong>{fail_stop_n}</strong> failures or stops.</p>"
    )
    return {
        "title": "test262 results",
        "eyebrow": f"Conformance suite on <code>ecma-run</code> · <code>{esc(record.name)}</code>",
        "lede": lede,
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
