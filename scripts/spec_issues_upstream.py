#!/usr/bin/env python3
"""The record of what the write-ups' Upstream items name in tc39/ecma262 (docs/spec-issues/upstream.tsv).

    python3 scripts/spec_issues_upstream.py write --cache DIR --clone DIR [--checked-on DATE]

Each write-up's `- **Upstream:**` item says what a check of tc39/ecma262 found: the issues and pull requests that
report, fix or relate to the defect, with their state, and the commits that changed the text. The record has one
row per issue, pull request or commit an item names (and one row for an item's search), with its state, its date
and its title as they were on the day of the check. The site's build reads the record and never the network:
the pages link each number and hash to GitHub and the index shows each write-up's state, and
`scripts/spec_issues.py check` fails when an item names anything the record does not have for that write-up, or
gives it another state or month.

`write` makes the record from the items and from what the check fetched, offline: DIR of `--cache` holds the
GitHub API's responses as they were fetched (each response in a file whose name is a hash of its URL, with the
URL and the HTTP status in the file of the same name plus `.url`: issue lists, single issues, searches), and
DIR of `--clone` is a clone of tc39/ecma262 (for the commits, and for a merged pull request the API responses do
not have: its commits' subjects end with `(#N)`).

Columns: write-up (its number), kind (issue, pull, commit, test262-pull, search), ref (the number, the hash, or
the search's terms), state (open, draft, closed, closed-unmerged, merged; a commit: exists; a search: searched),
date (opened, for an open issue or pull request; closed or merged; a commit's date; a search's day), title,
checked-on.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "docs/spec-issues/upstream.tsv"
COLUMNS = ["writeup", "kind", "ref", "state", "date", "title", "checked_on"]
REPO = "https://github.com/tc39/ecma262"
URLS = {"issue": REPO + "/issues/{}", "pull": REPO + "/pull/{}", "commit": REPO + "/commit/{}",
        "test262-pull": "https://github.com/tc39/test262/pull/{}"}

T262_RE = re.compile(r"test262\s+PR\s+#(\d+)")
NUM_RE = re.compile(r"(?<![\w/])#(\d+)\b")
COMMIT_RE = re.compile(r"\bcommits?\s+([0-9a-f]{9})(?:\s+and\s+([0-9a-f]{9}))?")
CHECKED_RE = re.compile(r"^Checked (\d{4}-\d\d-\d\d): ")
SEARCH_RE = re.compile(r"\(searched for ([^()]*(?:\([^()]*\)[^()]*)*)\)|searched tc39/ecma262's issues and pull "
                       r"requests for ([^)]*)\)")


@dataclass
class Row:
    writeup: str
    kind: str
    ref: str
    state: str
    date: str
    title: str
    checked_on: str

    @property
    def url(self) -> str | None:
        return URLS[self.kind].format(self.ref) if self.kind in URLS else None


def refs(item: str) -> list[tuple[str, str]]:
    """What an Upstream item names: ("t262", N), ("num", N) and ("commit", hash), in order."""
    out: list[tuple[str, str]] = []
    t262 = {m.start(1) - 1 for m in T262_RE.finditer(item)}
    for m in T262_RE.finditer(item):
        out.append((m.start(), ("t262", m.group(1))))
    for m in NUM_RE.finditer(item):
        if m.start() not in t262:
            out.append((m.start(), ("num", m.group(1))))
    for m in COMMIT_RE.finditer(item):
        out.append((m.start(1), ("commit", m.group(1))))
        if m.group(2):
            out.append((m.start(2), ("commit", m.group(2))))
    seen, res = set(), []
    for _, r in sorted(out):
        if r not in seen:
            seen.add(r)
            res.append(r)
    return res


def read() -> list[Row]:
    if not RECORD.exists():
        return []
    lines = RECORD.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [Row(**dict(zip(head, ln.split("\t")))) for ln in lines[1:]]


def by_writeup() -> dict[str, list[Row]]:
    out: dict[str, list[Row]] = {}
    for r in read():
        out.setdefault(r.writeup, []).append(r)
    return out


STATE_WORDS = {"open": {"open", "draft"}, "closed": {"closed"}, "closed without merging": {"closed-unmerged"},
               "merged": {"merged"}}


def check(num: str, item: str | None, rows: list[Row]) -> list[str]:
    """An Upstream item against the record's rows for its write-up."""
    if item is None:
        return ["no Upstream item"]
    fails = []
    m = CHECKED_RE.match(item)
    if not m:
        fails.append("the Upstream item does not begin `Checked YYYY-MM-DD: `")
    have = {(("t262" if r.kind == "test262-pull" else "commit" if r.kind == "commit" else "num"), r.ref): r
            for r in rows if r.kind != "search"}
    named = refs(item)
    for r in named:
        if r not in have:
            fails.append(f"the Upstream item names {r[1]}, which the record does not have for this write-up")
    for k in have:
        if k not in named:
            fails.append(f"the record has {k[1]} for this write-up, which its Upstream item does not name")
    for r in rows:
        if m and r.checked_on != m.group(1):
            fails.append(f"{r.ref}: checked on {r.checked_on} in the record, {m.group(1)} in the item")
    # "#N (state, YYYY-MM…)": the state and the month must be the record's.
    for mm in re.finditer(r"(?<![\w/])#(\d+) \(((?:open|closed without merging|closed|merged))[ ,]([^)]*)\)", item):
        key = ("t262" if re.search(r"test262\s+PR\s+$", item[:mm.start()]) else "num", mm.group(1))
        r = have.get(key)
        if not r:
            continue
        if r.state not in STATE_WORDS[mm.group(2)]:
            fails.append(f"#{mm.group(1)}: the item says {mm.group(2)}, the record {r.state}")
        if r.date[:7] not in mm.group(3):
            fails.append(f"#{mm.group(1)}: the item does not give the record's month {r.date[:7]}")
    return fails


# ---------------------------------------------------------------------------------------------------------------
# write: the record from the items, the cached responses and the clone


def cached(cache: Path) -> dict[tuple[str, int], dict]:
    """Every issue object the cached API responses hold, by (repository, number)."""
    out: dict[tuple[str, int], dict] = {}
    for u in sorted(cache.glob("*.url")):
        url, status = u.read_text().split("\n")[:2]
        m = re.match(r"https://api\.github\.com/(?:repos/tc39/([\w-]+)/issues|search/issues)", url)
        if status != "200" or not m:
            continue
        data = json.loads(u.with_suffix("").read_text())
        repo = m.group(1)
        if isinstance(data, dict) and "items" in data:
            items, repo = data["items"], None
        elif isinstance(data, list):
            items = data
        elif isinstance(data, dict) and "number" in data:
            items = [data]
        else:
            continue
        for it in items:
            if not isinstance(it, dict) or "number" not in it or "html_url" not in it:
                continue
            r = repo or it["html_url"].split("/")[4]
            key = (r, it["number"])
            # a single issue's response wins over a list's or a search's (they are the same object)
            if key not in out or url.rstrip("/").endswith(f"/issues/{it['number']}"):
                out[key] = it
    return out


def git(clone: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(clone), *args], capture_output=True, text=True, check=True).stdout


def issue_row(num: str, kind_repo: str, it: dict, checked: str) -> Row:
    pr = it.get("pull_request")
    if pr:
        kind = "pull" if kind_repo == "ecma262" else "test262-pull"
        if pr.get("merged_at"):
            state, date = "merged", pr["merged_at"]
        elif it["state"] == "closed":
            state, date = "closed-unmerged", it["closed_at"]
        else:
            state, date = ("draft" if it.get("draft") else "open"), it["created_at"]
    else:
        kind = "issue"
        state = it["state"]
        date = it["closed_at"] if state == "closed" else it["created_at"]
    return Row(num, kind, str(it["number"]), state, date[:10], it["title"], checked)


def write(cache: Path, clone: Path, default_checked: str) -> list[Row]:
    sys.path.insert(0, str(ROOT / "scripts"))
    import spec_issues as si
    objs = cached(cache)
    rows: list[Row] = []
    for iss in si.issues():
        item = iss.header.get("Upstream")
        if item is None:
            continue
        m = CHECKED_RE.match(item)
        checked = m.group(1) if m else default_checked
        for kind, ref in refs(item):
            if kind == "commit":
                full = git(clone, "rev-parse", "--verify", f"{ref}^{{commit}}").strip()
                date, subject = git(clone, "log", "-1", "--format=%cs%x09%s", full).strip().split("\t", 1)
                rows.append(Row(iss.num, "commit", ref, "exists", date, subject, checked))
                continue
            repo = "test262" if kind == "t262" else "ecma262"
            it = objs.get((repo, int(ref)))
            if it is not None:
                rows.append(issue_row(iss.num, repo, it, checked))
                continue
            # A merged pull request the responses lack: its commits in the clone.
            log = git(clone, "log", "main", "--format=%cs%x09%s", "--grep", f"(#{ref})", "--fixed-strings")
            lines = [ln.split("\t", 1) for ln in log.strip().split("\n") if ln.strip()]
            if repo != "ecma262" or not lines:
                raise SystemExit(f"{iss.num}: #{ref} is neither in the cached responses nor merged in the clone")
            date = max(d for d, _ in lines)
            title = re.sub(rf"\s*\(#{ref}\)$", "", lines[-1][1])
            rows.append(Row(iss.num, "pull", ref, "merged", date, title, checked))
        for sm in SEARCH_RE.finditer(item):
            terms = (sm.group(1) or sm.group(2)).strip()
            rows.append(Row(iss.num, "search", terms, "searched", checked, "tc39/ecma262 issues and pull requests",
                            checked))
    for r in rows:
        if any("\t" in getattr(r, c) or "\n" in getattr(r, c) for c in COLUMNS):
            raise SystemExit(f"{r.writeup} {r.ref}: a tab or a line break in a field")
    RECORD.write_text("\n".join("\t".join(x) for x in [COLUMNS, *([getattr(r, c) for c in COLUMNS] for r in rows)])
                      + "\n")
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("write")
    w.add_argument("--cache", type=Path, required=True)
    w.add_argument("--clone", type=Path, required=True)
    w.add_argument("--checked-on", default="")
    a = ap.parse_args()
    rows = write(a.cache, a.clone, a.checked_on)
    print(f"{RECORD.relative_to(ROOT)}: {len(rows)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
