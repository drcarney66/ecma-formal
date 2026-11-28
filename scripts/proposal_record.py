#!/usr/bin/env python3
"""What it took to apply a TC39 proposal: the record of a proposal's branch, and the site's page made from it.

    python3 scripts/proposal_record.py record --tree PATH [--branch proposal-defer-import-eval] \\
        [--base main] --test262 TSV [--test262-command 'CMD'] [--out site/proposal-defer-import-eval.json]
    python3 scripts/proposal_record.py check [--record site/proposal-defer-import-eval.json]

`record` reads two branches with git: the base branch (`main`) and the proposal's branch, which is the base
at some commit plus the proposal's own commits, and the proposal branch's working tree (`--tree`, read only: the
proposal's submodule is checked out only there). It writes one JSON file under `site/`: the site's own data, the
way `site/errata.json` is, so that the site's build needs only that file and not the branch, its submodule or its
Lean build (none of which a CI machine has). It records:

- the proposal's repository and pinned commit, ECMA-262's pinned commit, the branch's commit and its merge base;
- the branch's diff against the merge base, every file in one group (the pin, the answers, the SpecTec definitions,
  list files, the tests, hand-written Lean, any regenerated modules, and what the site does not publish),
  with its lines from `git diff --numstat`; a file in no group stops the command;
- the answers file, line by line, each with the README's reason and the question the merge asked;
- the readings: each `emu-reading` the branch adds or changes, with its clause, its step, the proposal's sentence as
  the merged text has it (found by the hash the overlay records), the reading's text and note from the `.emu`
  file, and the report's (`docs/spec-issues/{name}/README.md` on the branch) "why the generator could not read it unaided";
- the errata of the proposal's text, with the overlay's notes (the page shows them among the readings, without
  their notes: the site does not present the proposal's errata);
- the regenerated modules by directory;
- the merge tool (this tree's `scripts/apply_proposal.py`) run on the proposal with no answers, and with them,
  each output written to a temporary directory: the refusals and warnings, and what the merge did;
- the results: the proposal's test262 feature from a runner's results file (`--test262`), and the axioms the
  claims rest on, from the branch's report and this tree's `lean/Engine/Claims.lean`.

The notes and reasons cite the unfiled write-ups under docs/spec-issues/ in parentheses; the record leaves those
references out, and nothing from the write-ups is recorded.

`check` reads a record and fails unless it has everything the page states (`read()`); `scripts/site_pages.py`
makes `proposal.html` from it (`page()`).
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "site/proposal-defer-import-eval.json"
FORMAT = 1
# The list files the branch changes: written by hand, or regenerated (the branch's report, "Done by hand": "list
# files"). A file of spec/formal or tests the branch changes that is in neither stops the record.
HAND_LISTS = {"spec/formal/readings-restating.txt", "spec/formal/phrase-unreviewed.txt", "spec/formal/decisions.md"}
REGEN_LISTS = {"spec/formal/residue.txt", "spec/formal/asserts-open.txt", "spec/formal/assert-sites.txt",
               "spec/formal/permanent-sentences.txt", "spec/formal/type-dyn-sites.txt", "spec/formal/errata.txt",
               "tests/parser/grammar_index.txt"}
GROUPS = [
    ("pin", "The pin"),
    ("answers", "The merge's answers"),
    ("readings", "SpecTec definitions & HTML metadata"),
    ("lists", "List files, by hand"),
    ("tests", "Tests"),
    ("lean-hand", "Hand-written Lean"),
    ("regenerated", "Regenerated: Lean modules"),
    ("lists-regen", "Regenerated: list files"),
    ("unpublished", "Not on the site: files under docs/, counted only"),
]
HAND = ("pin", "answers", "readings", "lists", "tests", "lean-hand")
REF = re.compile(r"\s*\((?:write-up \d+|docs/spec-issues/[^()]*|decisions\.md[^()]*)\)|\s*Write-up: docs/spec-issues/\S+?\.md\.?"
                 r"|\s*A defect of the proposal's \w+: `docs/spec-issues/[^`]*`\.?")


def esc(s: str) -> str:
    return html.escape(s, quote=True)


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout


def cap(t: str) -> str:
    return t[:1].upper() + t[1:]


def xrefs(t: str, sp) -> str:
    """An overlay note's empty cross-references as the merged text numbers them."""
    def one(m: re.Match) -> str:
        cid = m.group(1)
        if cid in sp.nums:
            return f"§{sp.nums[cid]}"
        cl = sp.clause_of(cid)
        return f"a table of §{sp.nums[cl]}" if cl in sp.nums else cid
    return re.sub(r'<emu-xref href="#([^"]+)"></emu-xref>', one, t)


def unref(t: str) -> str:
    """A note or a reason without its references to the project's own unpublished files."""
    return re.sub(r"\s{2,}", " ", REF.sub("", t)).strip()


# ---------------------------------------------------------------------------------------------------------------
# Reading the branch


def group_of(path: str) -> str:
    if path == ".gitmodules" or path.startswith("external/") or path == "spec/proposals.txt":
        return "pin"
    if path.startswith("spec/proposals/"):
        return "answers"
    if path.startswith("spec/spectec/") or path.startswith("spec/html/") or (path.startswith("spec/formal/") and path.endswith(".emu")):
        return "readings"
    if path in HAND_LISTS:
        return "lists"
    if path in REGEN_LISTS:
        return "lists-regen"
    if path.startswith("lean/"):
        return "regenerated" if "/Gen/" in path else "lean-hand"
    if path.startswith("tests/"):
        return "tests"
    if path.startswith("docs/"):
        return "unpublished"
    raise SystemExit(f"{path}: in no group of the record (scripts/proposal_record.py GROUPS)")


def emu_readings(text: str) -> list[dict]:
    """Every emu-reading of an overlay file: its attributes, its readings' steps, its notes, its erratum (or None)."""
    out = []
    errs = [(m.start(), m.end(), re.search(r'name="([^"]+)"', m.group(1)).group(1))
            for m in re.finditer(r"<emu-erratum\b([^>]*)>.*?</emu-erratum>", text, re.DOTALL)]
    for m in re.finditer(r"<emu-reading\b([^>]*)>(.*?)</emu-reading>", text, re.DOTALL):
        a = dict(re.findall(r'([\w-]+)="([^"]*)"', m.group(1)))
        alts = [(x.group(1), x.group(2)) for x in re.finditer(r'<emu-alg reading="([^"]+)">(.*?)</emu-alg>', m.group(2), re.DOTALL)]
        notes = re.findall(r"<p>(.*?)</p>", "".join(re.findall(r"<emu-note>(.*?)</emu-note>", m.group(2), re.DOTALL)), re.DOTALL)
        err = next((n for s, e, n in errs if s <= m.start() < e), None)
        out.append({"attrs": a, "alts": alts, "notes": notes, "erratum": err})
    return out


def dedent(alg: str) -> str:
    lines = [l for l in alg.split("\n") if l.strip()]
    base = min(len(l) - len(l.lstrip()) for l in lines)
    return "\n".join(l[base:] for l in lines)


def report_table(report: str, heading: str) -> list[list[str]]:
    """The rows of the first table under `heading` in the branch's report, cells stripped."""
    i = report.index(heading)
    rows = []
    for ln in report[i:].split("\n")[1:]:
        if ln.startswith("|"):
            cells = [c.strip() for c in ln.strip().strip("|").split(" | ")]
            if not set(cells[0]) <= {"-", " "}:
                rows.append(cells)
        elif rows:
            break
    return rows[1:]  # without the header row


def record(tree: Path, branch: str, base: str, t262: Path, t262_cmd: str | None, out: Path) -> dict:
    import errata_page
    import law_quotes

    head = git("rev-parse", branch).strip()
    mb = git("merge-base", base, branch).strip()
    base_head = git("rev-parse", base).strip()
    if git("rev-parse", "HEAD", cwd=tree).strip() != head:
        raise SystemExit(f"{tree}: its HEAD is not {branch} ({head[:9]})")
    if git("status", "--porcelain", "--untracked-files=no", cwd=tree).strip():
        raise SystemExit(f"{tree}: has uncommitted changes")

    def at(rev: str, path: str) -> str:
        return git("show", f"{rev}:{path}")

    # The pins.
    plist = [l.split() for l in at(head, "spec/proposals.txt").split("\n") if l.split() and not l.startswith("#")]
    if len(plist) != 1:
        raise SystemExit(f"{branch}: spec/proposals.txt names {len(plist)} proposals; the record is of one")
    name, ppath, answers = plist[0]
    gm = at(head, ".gitmodules")
    url = re.search(r'\[submodule "' + re.escape(ppath) + r'"\][^\[]*?url = (\S+)', gm).group(1)
    pcommit = git("ls-tree", head, ppath).split()[2]
    ecma = git("ls-tree", head, "external/ecma262").split()[2]
    if ecma != git("ls-tree", base_head, "external/ecma262").split()[2]:
        raise SystemExit("the branch pins another ECMA-262 than the base branch")

    # The diff, by group.
    files = []
    for ln in git("diff", "--numstat", mb, head).strip().split("\n"):
        a, r, p = ln.split("\t")
        files.append({"path": p, "added": int(a) if a != "-" else 0, "removed": int(r) if r != "-" else 0,
                      "group": group_of(p)})
    old_paths = set(git("ls-tree", "-r", "--name-only", mb).split("\n"))
    for f in files:
        f["new"] = f["path"] not in old_paths

    # The merge: the text with and without the answers, written to a temporary directory.
    proposal = tree / ppath
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        (t / "none").mkdir()
        (t / "ans").mkdir()
        subprocess.run([sys.executable, ROOT / "scripts/apply_proposal.py", ROOT / "external/ecma262/spec.html", proposal,
                        t / "none/spec.html", "--report", t / "none/report.json", "--force"], capture_output=True)
        ans_file = t / "answers.txt"
        ans_file.write_text(at(head, answers))
        r = subprocess.run([sys.executable, ROOT / "scripts/apply_proposal.py", ROOT / "external/ecma262/spec.html",
                            proposal, t / "ans/spec.html", "--resolutions", ans_file, "--report", t / "ans/report.json"],
                           capture_output=True, text=True)
        if r.returncode:
            raise SystemExit(f"the merge with the branch's answers refuses:\n{r.stdout}{r.stderr}")
        none = json.loads((t / "none/report.json").read_text())
        ans = json.loads((t / "ans/report.json").read_text())
        law_quotes.SPEC = ROOT / "external/ecma262/spec.html"
        spb = errata_page.Text()
        law_quotes.SPEC = t / "ans/spec.html"
        sp = errata_page.Text()
        base_src = (ROOT / "external/ecma262/spec.html").read_text()
        emu_src = (proposal / "spec.emu").read_text() if proposal.is_dir() else proposal.read_text()

        # The answers, each with the README's reason and the question the merge asked.
        readme = at(head, str(Path(answers).parent / "README.md"))
        reasons = {}
        for cells in report_table(readme, "| answer |"):
            for code in re.findall(r"`([^`]+)`", cells[0]):
                reasons[code] = (cells[1], cells[2])
        refusals = {(x["clause"], x["block"]): x for x in none["refusals"]}
        alist = []
        for ln in at(head, answers).split("\n"):
            w = ln.split("#")[0].split()
            if not w:
                continue
            verb = w[0]
            code = " ".join(w[:5] if verb == "place" else w[:3])
            key = next((k for k in reasons if k == code or code.startswith(k)), None)
            if key is None:
                raise SystemExit(f"{answers}: no reason in the README for `{code}`")
            q, why = reasons[key]
            ref = refusals.get((w[1], int(w[2]))) if verb not in ("rename",) else None
            if verb != "rename" and ref is None:
                raise SystemExit(f"{answers}: `{code}` answers no refusal of the merge")
            cl = w[1] if verb != "rename" else None
            alist.append({"answer": code, "verb": verb, "question": unref(q), "reason": unref(why),
                          "tool": ref["message"] if ref else None, "clause": cl,
                          "num": sp.nums.get(cl, "") if cl else "", "title": sp.short(cl) if cl else ""})
        answered = {(a["answer"].split()[1], int(a["answer"].split()[2])) for a in alist if a["verb"] != "rename"}
        if answered != set(refusals):
            raise SystemExit(f"the answers file answers {sorted(answered)}; the merge refused {sorted(refusals)}")

        # The rename: the old name's calls in the base, the new name's in the proposal's text.
        old_new = next(((a["answer"].split()[1], a["answer"].split()[2]) for a in alist if a["verb"] == "rename"), None)
        rename = None
        if old_new:
            o, n = old_new
            # shown: the uses the proposal renames in the text it shows (`<ins>NEW</ins>` where the old name is
            # deleted); left: the old name's uses in the merge without answers, in the clauses it does not show.
            none_text = (t / "none/spec.html").read_text()
            rename = {"old": o, "new": n, "shown": len(re.findall(r"<ins>" + re.escape(n) + r"</ins>", emu_src)),
                      "left": len(re.findall(r"\b" + re.escape(o) + r"\b", none_text)),
                      "old_clause": f"sec-{o}", "old_num": spb.nums.get(f"sec-{o}", ""),
                      "clauses": [c for c in re.findall(r"in \d+ clause\(s\): (.*?);", " ".join(none["warnings"]))]}

        # The readings.
        report = at(head, f"docs/spec-issues/{name}/README.md")
        why_rows = report_table(report, "| clause, step | the proposal's sentence |")
        readings, errata = [], []
        for f in files:
            if f["group"] != "readings" or not f["path"].endswith(".emu"):
                continue
            new_rs = emu_readings(at(head, f["path"]))
            old_rs = [] if f["new"] else emu_readings(at(mb, f["path"]))
            old_keys = {json.dumps(r["attrs"], sort_keys=True) for r in old_rs}
            for rd in new_rs:
                a = rd["attrs"]
                if json.dumps(a, sort_keys=True) in old_keys:
                    continue
                cid = a["clause"]
                steps = (a.get("steps") or a.get("step") or "").split()
                hashes = (a.get("hashes") or a.get("hash") or "").split()
                sentence = []
                for s, h in zip(steps, hashes):
                    own = sp.own(cid)
                    hit = [t for alg in re.findall(r"<emu-alg\b[^>]*>(.*?)</emu-alg>", own, re.DOTALL)
                           for p, t in errata_page.alg_steps(alg) if errata_page.sha(t) == h]
                    if not hit:
                        raise SystemExit(f"{f['path']}: no step of {cid} in the merged text has the hash {h[:12]}…")
                    sentence.append({"step": s, "text": hit[0]})
                before = [o for o in old_rs if o["attrs"]["clause"] == cid]
                if not before:
                    status = "new"
                else:
                    ob = dedent(before[0]["alts"][0][1]) if before[0]["alts"] else ""
                    nb = dedent(rd["alts"][0][1]) if rd["alts"] else ""
                    if old_new:
                        ob = ob.replace(old_new[0], old_new[1])
                    status = "re-anchored" if ob == nb else "replaced"
                title = sp.titles.get(cid, cid)
                short = re.sub(r"^(?:Static|Runtime) Semantics: ", "", re.match(r"([^(]+?)\s*(?:\(|$)", title).group(1))
                pat = re.compile(r"(?:^|[ ,`(])" + re.escape(short) + (r" " + re.escape(steps[0]) + r"\b" if steps else r"\b"))
                k = next((n for n, cells in enumerate(why_rows) if pat.search(cells[0])), None)
                # "the same": the report's row above says it
                while k is not None and k > 0 and why_rows[k][3].strip().rstrip(".") == "the same":
                    k -= 1
                why = why_rows[k][3] if k is not None else None
                if why is None:
                    raise SystemExit(f"docs/spec-issues/{name}/README.md: no row of the readings' table for {short} {steps[:1]}")
                item = {"file": f["path"], "clause": cid, "num": sp.nums.get(cid, ""), "title": title,
                        "steps": steps, "grammar": a.get("grammar"), "sentence": sentence, "status": status,
                        "reading": [{"readings": r.split(), "text": dedent(t)} for r, t in rd["alts"]],
                        "note": [xrefs(unref(p), sp) for p in rd["notes"]], "why": unref(why)}
                if rd["erratum"]:
                    errata.append(item)
                else:
                    readings.append(item)
        # The errata's own notes (outside their readings).
        dsrc = "".join(at(head, f["path"]) for f in files if f["path"].endswith(".emu") and f["group"] == "readings")
        for m in re.finditer(r'<emu-erratum\b[^>]*name="([^"]+)"[^>]*>(.*?)</emu-erratum>', dsrc, re.DOTALL):
            body = re.sub(r"<emu-reading\b.*?</emu-reading>", "", m.group(2), flags=re.DOTALL)
            notes = [xrefs(unref(p), sp) for p in re.findall(r"<p>(.*?)</p>", body, re.DOTALL)]
            attrs = dict(re.findall(r'([\w-]+)="([^"]*)"', dsrc[m.start(): dsrc.index(">", m.start())]))
            for e in errata:
                if e["clause"] in m.group(2):
                    e["erratum"] = m.group(1)
                    e["note"] = e["note"] + notes
                    e["resolution"] = attrs.get("resolution")
                    e["switch"] = attrs.get("switch", "spec")

        # Other overlay changes: the lines of .emu files outside the readings recorded above.
        other = []
        for f in files:
            if f["group"] == "readings" and not f["new"]:
                d = git("diff", "-U0", mb, head, "--", f["path"])
                rem = [l[1:].strip() for l in d.split("\n") if l.startswith("-") and not l.startswith("---")]
                add = [l[1:].strip() for l in d.split("\n") if l.startswith("+") and not l.startswith("+++")]
                rem = [l for l in rem if not l.startswith(("<emu-reading", "1.", "<emu-alg", "</emu-alg"))]
                add = [l for l in add if not l.startswith(("<emu-reading", "1.", "<emu-alg", "</emu-alg"))]
                if rem or add:
                    other.append({"file": f["path"], "removed": rem, "added": add})

    # test262.
    rows: dict[str, str] = {}
    details: dict[str, str] = {}
    head_t = ""
    for ln in t262.read_text().split("\n"):
        if ln.startswith("#"):
            head_t = ln
        elif ln.strip():
            c = ln.split("\t")
            rows[c[0]] = c[1]
            details[c[0]] = c[3] if len(c) > 3 else ""
    by = Counter(rows.values())
    dirs: dict[str, Counter] = defaultdict(Counter)
    for t, b in rows.items():
        p = t.split("/")
        dirs["/".join(p[:3]) if p[1] != "import" else "/".join(p[:3])][b] += 1
    rev = re.search(r"test262 (\w+)", head_t)
    test262 = {"feature": "import-defer", "counts": dict(by), "dirs": {d: dict(c) for d, c in sorted(dirs.items())},
               "test262": rev.group(1) if rev else "?", "skipped": [[t, details[t]] for t, b in sorted(rows.items()) if b == "skip"],
               "command": t262_cmd or ""}

    # The axioms: the branch's report and this tree's record of the axiom check.
    ax = re.search(r"depend on (.*?) and (\d+) `native_decide` pins", report)
    base_ax = re.search(r"Axioms of `Engine.implements` and of `Engine.run_sound`: (.*?) and (\d+)\s+`native_decide` pins",
                        (ROOT / "lean/Engine/Claims.lean").read_text())
    axioms = {"branch": re.findall(r"`([^`]+)`", ax.group(1)), "branch_pins": int(ax.group(2)),
              "base": re.findall(r"`([^`]+)`", base_ax.group(1)), "base_pins": int(base_ax.group(2))}

    rec = {
        "format": FORMAT, "name": name, "title": f"tc39/proposal-{name}",
        "proposal": {"repository": url, "commit": pcommit, "path": ppath},
        "ecma262": ecma,
        "branch": {"name": branch, "commit": head, "merge_base": mb, "base": base, "base_commit": base_head},
        "groups": [{"id": g, "title": t, "files": [f for f in files if f["group"] == g]} if g != "unpublished" else
                   {"id": g, "title": t, "files": [], "count": sum(1 for f in files if f["group"] == g)}
                   for g, t in GROUPS],
        "answers": alist, "answers_file": answers,
        "readings": readings, "errata": errata, "other_overlay": other,
        "merge": {"no_answers": {"refusals": none["refusals"], "warnings": none["warnings"]},
                  "with_answers": {"changed": len(dict(ans["log"]).get("replaced", [])),
                                   "inserted": len(dict(ans["log"]).get("inserted", [])),
                                   "removed": len(dict(ans["log"]).get("removed", [])),
                                   "figures": len(ans["images"]), "ins": ans["checks"]["ins_total"],
                                   "del": ans["checks"]["del_total"], "tree_ok": ans["checks"]["tree_ok"],
                                   "warnings": ans["warnings"]}},
        "rename": rename,
        "test262": test262,
        "axioms": axioms,
    }
    read(rec)
    out.write_text(json.dumps(rec, indent=1, ensure_ascii=False) + "\n")
    s = summary(rec)
    print(f"{out.relative_to(ROOT) if out.is_relative_to(ROOT) else out}: {s['hand_lines']} lines by hand in "
          f"{s['hand_files']} files, {s['lean_hand']} hand-written Lean files, {len(readings)} readings, "
          f"{len(errata)} errata, test262 {by.get('pass', 0)} pass of {sum(by.values())}")
    return rec


# ---------------------------------------------------------------------------------------------------------------
# Reading the record


NEED = ["format", "name", "proposal", "ecma262", "branch", "groups", "answers", "readings", "errata", "merge",
        "test262", "axioms"]


def read(rec: dict | Path) -> dict:
    """The record, checked to hold everything the page states."""
    if isinstance(rec, Path):
        rec = json.loads(rec.read_text())
    miss = [k for k in NEED if k not in rec]
    if miss:
        raise SystemExit(f"the proposal's record has no {', '.join(miss)}")
    if rec["format"] != FORMAT:
        raise SystemExit(f"the proposal's record is of format {rec['format']}, not {FORMAT}")
    for k in ("repository", "commit"):
        if not rec["proposal"].get(k):
            raise SystemExit(f"the proposal's record has no proposal {k}")
    for k in ("name",):
        if not rec["branch"].get(k):
            raise SystemExit(f"the proposal's record has no branch {k}")
    if [g["id"] for g in rec["groups"]] != [g for g, _ in GROUPS]:
        raise SystemExit("the proposal's record's groups are not the page's")
    if not rec["answers"] or any(not a.get("reason") for a in rec["answers"]):
        raise SystemExit("the proposal's record has an answer without its reason")
    for r in rec["readings"] + rec["errata"]:
        if not r.get("reading") or not r.get("why") or not (r.get("sentence") or r.get("grammar")):
            raise SystemExit(f"the proposal's record: the reading of {r.get('clause')} lacks its sentence, text or why")
    for e in rec["errata"]:
        if not e.get("erratum") or not e.get("note"):
            raise SystemExit(f"the proposal's record: the erratum at {e.get('clause')} has no name or note")
    if "refusals" not in rec["merge"].get("no_answers", {}) or "changed" not in rec["merge"].get("with_answers", {}):
        raise SystemExit("the proposal's record has no merge report")
    t = rec["test262"]
    if not t.get("counts") or not t.get("dirs"):
        raise SystemExit("the proposal's record has no test262 results")
    if not rec["axioms"].get("branch") or not rec["axioms"].get("base"):
        raise SystemExit("the proposal's record has no axioms")
    return rec


def summary(rec: dict) -> dict:
    g = {x["id"]: x["files"] for x in rec["groups"]}
    hand = [f for k in HAND for f in g[k] if not f["path"].startswith("external/")]
    return {"hand_lines": sum(f["added"] for f in hand), "hand_removed": sum(f["removed"] for f in hand),
            "hand_files": len(hand), "lean_hand": len(g["lean-hand"]),
            "regen_files": len(g["regenerated"]), "regen_added": sum(f["added"] for f in g["regenerated"]),
            "regen_removed": sum(f["removed"] for f in g["regenerated"])}


# ---------------------------------------------------------------------------------------------------------------
# The page


def page(rec: dict, gallery: dict | None, builds: list[dict]) -> dict:
    import errata_page

    rec = read(rec)
    s = summary(rec)
    g = {x["id"]: x for x in rec["groups"]}
    p = rec["proposal"]
    t = rec["test262"]
    tc = t["counts"]
    t_run = sum(v for k, v in tc.items() if k != "skip")
    md = lambda x: errata_page.md(x)  # noqa: E731
    title = rec["title"]
    purl = p["repository"].removesuffix(".git")
    plink = f'<a href="{esc(purl)}"><code>{esc(title)}</code></a>' if purl.startswith("https://github.com/tc39/") else f"<code>{esc(title)}</code>"
    ax = rec["axioms"]
    same_ax = ax["branch"] == ax["base"] and ax["branch_pins"] == ax["base_pins"]
    body = []

    def files_table(ids: list[str]) -> str:
        trs = []
        for k in ids:
            for f in g[k]["files"]:
                trs.append(f'<tr><td><code>{esc(f["path"])}</code>{" <span class=muted>(new)</span>" if f["new"] else ""}</td>'
                           f'<td class="num">+{f["added"]}</td><td class="num">−{f["removed"]}</td></tr>')
        return ('<div class="tablebox"><table class="t262"><thead><tr><th>File</th><th class="num">Added</th>'
                '<th class="num">Removed</th></tr></thead><tbody>' + "".join(trs) + "</tbody></table></div>")

    # 1. What was done.
    nread = len(rec["readings"]) + len(rec["errata"])
    bref = (f'<code>{esc(rec["branch"]["commit"][:7])}</code>, from <code>{esc(rec["branch"]["merge_base"][:7])}</code>'
            if rec["branch"].get("commit") and rec["branch"].get("merge_base")
            else f'from <code>{esc(rec["branch"].get("base") or "main")}</code>')
    body.append(
        f'<h2 id="summary">What was done</h2><p>The proposal {plink}, at its commit <code>{esc(p["commit"][:7])}</code>, '
        f'was applied to ECMA-262 at <code>{esc(rec["ecma262"][:9])}</code> in a branch of this repository, '
        f'<code>{esc(rec["branch"]["name"])}</code> ({bref}): the proposal\'s text merged into the specification\'s, the '
        f'Lean specification regenerated from the result, the engine built and its claims checked, and the proposal\'s '
        f'test262 tests run.</p>'
        f'<ul class="facts"><li><b>{s["hand_lines"]:,}</b><span>lines added by hand (−{s["hand_removed"]:,} removed) across '
        f'{s["hand_files"]} files: the pin, {len(rec["answers"])} merge answers, SpecTec definitions &amp; HTML metadata '
        f'(including {nread} step readings), and tests</span></li>'
        f'<li><b>{s["lean_hand"]}</b><span>files of hand-written Lean changed</span></li>'
        f'<li><b>{tc.get("pass", 0):,}</b><span>of the proposal\'s {sum(tc.values()):,} test262 tests '
        f'(<code>{esc(t["feature"])}</code>) pass; {tc.get("skip", 0)} not run, none fails</span></li></ul>')

    # 2. How a proposal is applied.
    body.append(
        '<h2 id="how">How a proposal is applied</h2><ol class="steps">'
        f'<li><strong>Pin it.</strong> The proposal\'s repository is a submodule, <code>{esc(p["path"])}</code>, at '
        f'<code>{esc(p["commit"][:7])}</code>, and one line of <code>spec/proposals.txt</code> names it with its answers '
        'file.</li>'
        '<li><strong>Merge it.</strong> <code>scripts/apply_proposal.py</code> reads the proposal\'s <code>spec.emu</code> as a '
        'diff against ECMA-262: it matches each clause by its <code>id</code> and each block of the clause by its old '
        'text (the block with its <code>&lt;ins&gt;</code> dropped and its <code>&lt;del&gt;</code> kept), which must be '
        'the base\'s; it inserts the proposal\'s new clauses and removes the ones it deletes. Where the old text is not '
        'the base\'s, or an inserted block\'s place is not shown, it refuses and asks: the answers file '
        f'(<code>{esc(rec["answers_file"])}</code>) answers each question, one line each.</li>'
        '<li><strong>The text.</strong> <code>scripts/spec_text.py</code> makes the text every generator, check and page '
        'reads: ECMA-262 with the proposals of <code>spec/proposals.txt</code> applied, remade whenever an input '
        'changes.</li>'
        '<li><strong>SpecTec.</strong> <code>crates/spectec-html</code> translates new or changed algorithms, '
        'grammar rules, tables and early errors into <code>spec/spectec/</code> and checks the round-trip back to '
        'the merged <code>spec.html</code>.</li>'
        '<li><strong>Regenerate.</strong> <code>python3 scripts/generate.py</code> runs <code>spectec emit</code> '
        'over <code>spec/spectec/</code> to write <code>lean/Ecma/Gen</code> and '
        '<code>lean/Ecma/Grammar/Gen</code> (<code>python3 scripts/spec_text.py --report</code> says what the merge did).</li>'
        '<li><strong>Build and check.</strong> <code>lake build</code>, the axiom check of the claims, '
        '<code>python3 scripts/quick_check.py</code>, and test262 with the proposal\'s feature no longer in '
        '<code>[skip-features]</code>.</li></ol>')

    # 3. What was written by hand.
    atr = "".join(f'<tr><td><code>{esc(a["answer"])}</code></td><td>{md(a["question"])}</td><td>{md(a["reason"])}</td></tr>'
                  for a in rec["answers"])
    body.append(
        f'<h2 id="by-hand">What was written by hand</h2>{files_table(["pin", "answers", "readings", "lists", "tests"])}'
        f'<p>Hand-written Lean: {s["lean_hand"]} files changed under <code>lean/</code> outside its generated directories.</p>'
        f'<h3 id="answers">The answers to the merge ({len(rec["answers"])})</h3>'
        f'<div class="tablebox"><table class="answers"><thead><tr><th>Answer</th><th>The question the merge asked</th>'
        f'<th>Why this answer</th></tr></thead><tbody>{atr}</tbody></table></div>')
    # The two readings the record holds as errata of the proposal's text are shown as readings: the site does not
    # present the proposal's errata (they stay on its branch).
    by_status = Counter(r["status"] for r in rec["readings"] + rec["errata"])
    rlis = []
    for r in rec["readings"] + rec["errata"]:
        short = re.sub(r"^(?:Static|Runtime) Semantics: ", "", re.match(r"([^(]+?)\s*(?:\(|$)", r["title"]).group(1))
        where = (f'<a class="clause" href="https://tc39.es/ecma262/#{esc(r["clause"])}"><span class="secnum">'
                 f'{esc(r["num"])}</span> {esc(short)}</a>')
        if r["steps"]:
            where += f', step{"s" if len(r["steps"]) > 1 else ""} {esc(", ".join(r["steps"]))}'
        tag = esc(r["status"])
        why = (r["why"] if not r.get("erratum") else
               "the proposal's text does not give it; the reading gives what test262's tests of the proposal require")
        sent = "".join(f'<p>{md(x["text"])}</p>' for x in r["sentence"]) if r["sentence"] else \
            f'<p class="muted">No row for <code>{esc(r["grammar"])}</code>.</p>'
        rd = "".join(errata_page.alg_html(x["text"], None) for x in r["reading"])
        rlis.append(f'<tbody><tr><td>{where}<br><span class="muted">{tag}</span></td><td class="spec">{sent}</td>'
                    f'<td class="spec">{rd}</td></tr><tr class="why"><td colspan="3"><span class="muted">Why '
                    f'SpecTec records an explicit step reading:</span> {md(why)}</td></tr></tbody>')
    rtable = ('<div class="tablebox"><table class="readings-t"><thead><tr><th>Clause, step</th><th>The proposal\'s '
              'sentence, as the merged text has it</th><th>The reading</th></tr></thead>' + "".join(rlis) + "</table></div>")
    counts = ", ".join(f"{v} {k}" for k, v in sorted(by_status.items(), key=lambda x: -x[1]))
    oth = "".join(f'<li><code>{esc(o["file"])}</code>: ' + "; ".join(
        [f"removed <code>{esc(x)}</code>" for x in o["removed"]] + [f"added <code>{esc(x)}</code>" for x in o["added"]]) + "</li>"
        for o in rec["other_overlay"])
    body.append(f'<h3 id="readings">The readings ({nread})</h3><p>Each reading says what a sentence of the proposal means '
                f'where the merged prose is informal or incomplete: {counts}. The proposal\'s sentence is quoted from the '
                f'merged text (matched via <code>spec/html/step-patches.txt</code>); '
                f'the reasons are the branch\'s report\'s.</p>{rtable}'
                + (f'<p>Other SpecTec changes:</p><ul>{oth}</ul>' if oth else ""))

    # 4. What regenerating changed.
    regen = g["regenerated"]["files"]
    bydir: dict[str, list] = defaultdict(list)
    for f in regen:
        bydir[str(Path(f["path"]).parent)].append(f)
    rtr = "".join(f'<tr><td><code>{esc(d)}</code></td><td class="num">{len(fs)}</td>'
                  f'<td class="num">+{sum(f["added"] for f in fs):,}</td><td class="num">−{sum(f["removed"] for f in fs):,}</td>'
                  f'<td>{", ".join(esc(Path(f["path"]).stem) + (" (new)" if f["new"] else "") for f in fs)}</td></tr>'
                  for d, fs in sorted(bydir.items()))
    regen_tbl = (
        f'<p>{len(regen)} generated modules, +{s["regen_added"]:,} −{s["regen_removed"]:,} lines, nobody edited:</p>'
        f'<div class="tablebox"><table class="t262"><thead><tr><th>Directory</th><th class="num">Modules</th>'
        f'<th class="num">Added</th><th class="num">Removed</th><th>Modules</th></tr></thead><tbody>{rtr}</tbody></table></div>'
        if regen else
        '<p>Generated Lean modules (<code>lean/Ecma/Gen</code> and <code>lean/Ecma/Grammar/Gen</code>) are gitignored '
        'and emitted directly from <code>spec/spectec/</code> by <code>scripts/generate.py</code>.</p>'
    )
    body.append(
        f'<h2 id="regenerated">What regenerating changed</h2>{regen_tbl}'
        '<p>Every identifier in SpecTec is symbolic (<a href="how-it-works.html#ids">How it works</a>); '
        '<code>crates/spectec</code> derives sorted numeric indices and <code>Ecma.Known</code> constants automatically '
        'when emitting Lean, so diffs stay confined to the changed SpecTec definitions and downstream proofs continue to '
        'name the same declarations.</p>')

    # 5. What the merge found.
    kinds = Counter()
    for a in rec["answers"]:
        if a["verb"] != "rename":
            kinds[{"ignore": "a context block that is not the base's (an abbreviated header)",
                   "place": "an inserted block whose place is not shown",
                   "rebase": "old text that is not the base's: the base changed after the proposal was written",
                   "rebase-take": "old text that is not the base's: the proposal changed it without marking it"}.get(a["verb"], a["verb"])] += 1
    ktr = "".join(f"<tr><td>{esc(k)}</td><td class=num>{v}</td></tr>" for k, v in kinds.most_common())
    m = rec["merge"]
    w = m["with_answers"]
    body.append(
        f'<h2 id="merge">What the merge found in the proposal\'s text</h2><p>Run with no answers, the merge refuses '
        f'{len(m["no_answers"]["refusals"])} times and warns {len(m["no_answers"]["warnings"])} '
        f'time{"s" if len(m["no_answers"]["warnings"]) != 1 else ""}. The refusals, by what the answer found them to be:</p>'
        f'<div class="tablebox"><table class="t262"><thead><tr><th>Refusal</th><th class="num">Count</th></tr></thead>'
        f'<tbody>{ktr}</tbody></table></div>'
        + "".join(f"<p>The warning: {esc(x)}.</p>" for x in m["no_answers"]["warnings"])
        + f'<p>With the answers, it changes {w["changed"]} clauses, inserts {w["inserted"]}, removes {w["removed"]} and copies '
        f'{w["figures"]} figures; every one of the proposal\'s {w["ins"]} <code>&lt;ins&gt;</code> texts is in the result, '
        f'none of its {w["del"]} <code>&lt;del&gt;</code> texts is left, and the clause tree is the base\'s less the removed '
        f'clauses plus the inserted ones.</p>'
        '<p>For the merge to ask nothing, a proposal\'s text would reproduce whole blocks (no abbreviated headers; an '
        'inserted note shown with the algorithm before it), be written against the current ECMA-262, mark every change '
        'with <code>&lt;ins&gt;</code> and <code>&lt;del&gt;</code>, and rename a removed operation at every call or say '
        'that the rest are renamed with it.</p>')

    # 6. The results.
    dtr = "".join(f'<tr><td><code>{esc(d)}</code></td><td class="num">{c.get("pass", 0)}</td>'
                  f'<td class="num">{sum(v for k, v in c.items() if k not in ("pass", "skip")) or ""}</td>'
                  f'<td class="num">{c.get("skip", 0) or ""}</td></tr>' for d, c in t["dirs"].items())
    progs = []
    if gallery:
        for e in gallery["examples"]:
            if e["group"] != "proposal":
                continue
            cells = []
            for b in ("defer", "spec"):
                c = e["builds"].get(b)
                cells.append(f'<td>{"<code>" + esc(c["end"]) + "</code>" + "".join(f"<br><code>{esc(x)}</code>" for x in c.get("printed", [])) if c else "—"}</td>')
            progs.append(f'<tr><td><code>{esc(e["file"])}</code></td>{"".join(cells)}</tr>')
    def ax_text(names: list[str], npins: int) -> str:
        s = ", ".join(f"<code>{esc(x)}</code>" for x in names)
        return f"{s} alone (no <code>native_decide</code> pins)" if npins == 0 else f"{s} and {npins} <code>native_decide</code> pins"

    body.append(
        f'<h2 id="results">The results</h2><p><strong>test262.</strong> The {sum(tc.values()):,} tests of the feature '
        f'<code>{esc(t["feature"])}</code> at test262 <code>{esc(t["test262"][:9])}</code>: '
        + ", ".join(f"{v:,} {k}" for k, v in sorted(tc.items(), key=lambda x: -x[1]))
        + (" (not run: " + "; ".join(f"<code>{esc(x)}</code>, {esc(d)}" for x, d in t["skipped"]) + ")" if t["skipped"] else "")
        + '.</p>'
        f'<div class="tablebox"><table class="t262"><thead><tr><th>Directory</th><th class="num">Pass</th>'
        f'<th class="num">Not passing</th><th class="num">Skipped</th></tr></thead><tbody>{dtr}</tbody></table></div>'
        f'<p><strong>The claims.</strong> On the branch, <code>Engine.implements</code> and <code>Engine.run_sound</code> '
        f'rest on {ax_text(ax["branch"], ax["branch_pins"])}'
        + ("; the same list as without the proposal." if same_ax else f'; without the proposal, on {ax_text(ax["base"], ax["base_pins"])}.')
        + "</p>"
        + (f'<p><strong>The programs.</strong> Each of the proposal\'s three example programs, under the proposal\'s build '
           f'and under the specification\'s (both checked when this site was built):</p><div class="tablebox"><table '
           f'class="t262"><thead><tr><th>Program</th><th>With the proposal</th><th>The specification</th></tr></thead>'
           f'<tbody>{"".join(progs)}</tbody></table></div>' if progs else ""))

    # 7. Try it.
    has = any(b["id"] == "defer" for b in builds)
    if has and gallery:
        lab = {b["id"]: b["label"] for b in builds}
        lis = []
        for e in gallery["examples"]:
            if e["group"] != "proposal":
                continue
            links = [f'<button type="button" class="open" data-dbg-open="debugger/?example={esc(e["id"])}&amp;build=defer">Open in the debugger</button>']
            lis.append(f'<li><p><strong>{esc(e["title"])}</strong></p><p class="opens">{" ".join(links)}</p></li>')
        body.append(f'<h2 id="try">Try it</h2><p>The debugger has the proposal\'s build: under it each program runs and '
                    f'pauses in the proposal\'s algorithms.</p>'
                    f'<ul class="try">{"".join(lis)}</ul>')
    else:
        body.append('<h2 id="try">Try it</h2><p>This site was built without the proposal\'s debugger build; '
                    '<code>scripts/build_site.py --build defer=PATH</code> adds it, PATH being the WebAssembly build made '
                    'from the proposal\'s branch.</p>')

    toc = [("summary", "What was done", 1), ("how", "How a proposal is applied", 1), ("by-hand", "Written by hand", 1),
           ("answers", "The answers", 2), ("readings", "The readings", 2), ("regenerated", "Regenerated", 1),
           ("merge", "What the merge found", 1), ("results", "The results", 1),
           ("try", "Try it", 1)]
    return {"title": "Applying a proposal", "eyebrow": f"A record of the branch <code>{esc(rec['branch']['name'])}</code> · "
            f"<code>{esc(RECORD.relative_to(ROOT).as_posix())}</code>",
            "lede": (f"<p>What it takes to apply a TC39 proposal to this specification, shown on {plink}: the text merged, "
                     f"what was written by hand, what was regenerated, what the merge found, and the results.</p>"),
            "body": "\n".join(body), "toc": toc, "summary": s}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record")
    r.add_argument("--tree", type=Path, required=True, help="the proposal branch's working tree (read only)")
    r.add_argument("--branch", default="proposal-defer-import-eval")
    r.add_argument("--base", default="main")
    r.add_argument("--test262", type=Path, required=True, help="a runner's results file of the proposal's feature")
    r.add_argument("--test262-command", help="the command line that ran it")
    r.add_argument("--out", type=Path, default=RECORD)
    c = sub.add_parser("check")
    c.add_argument("--record", type=Path, default=RECORD)
    a = ap.parse_args()
    if a.cmd == "record":
        record(a.tree.expanduser(), a.branch, a.base, a.test262, a.test262_command, a.out)
    else:
        rec = read(a.record)
        print(f"ok   {a.record}: {summary(rec)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
