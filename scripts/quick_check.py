#!/usr/bin/env python3
"""The quick check: a handful of programs on ecma-run, each within a time and a memory limit.

    python3 scripts/quick_check.py [--run .lake/build/bin/ecma-run] [--update] [-- ECMA-RUN-OPTIONS]

Each tests/quick/NAME.js runs with JS_TRACE_STEPS=1. Its result line, printed lines, exit status, the digest
of the steps it entered (each trace line's section and step number, not its text) and the cells its store
ends with (the store only grows, so this is what it allocated) must be tests/quick/NAME.expected; `--update` rewrites those. A run over SECONDS of wall clock or MEGABYTES of resident
memory is killed and fails. Then lean/Ecma (outside Gen/) is checked to hold no theorem, tactic, or partial or
unsafe definition: the specification is definitions and stated laws only. Then the kept id tables
(spec/formal/{clause,sdo,method,erratum,reason,note}-ids.txt) are checked against lean/Ecma/Gen/Decls.lean: each
number names there what its table says, and each name there has a number; the grammar's (prod-, nt-,
param-ids.txt) against lean/Ecma/Grammar/Gen (`NT`'s and `Param`'s constructors, `Gen.prodIds`), Decls.lean and
tests/parser/grammar_index.txt, and table-ids.txt against the order of lean/Ecma/Gen/Tables_N.lean; and, with a
current target/release/spec-gen and jsgrammar, regenerating from the checked-in inputs writes the same tables (no
number changes) and the same lean/Ecma/Gen and lean/Ecma/Grammar/Gen, byte for byte, and `spec-gen roundtrip`
passes (every step prints back from its parse and its data): the text's half of the bijection; the specification
read is the text (`scripts/spec_text.py`). Then the data's half: every item of lean/Ecma/Gen and
lean/Ecma/Grammar/Gen as ecma-print prints it is spec.html's or the overlay's text, each exactly once
(`scripts/bijection.py`; it fails if ecma-print is not built). Then every law's quotation is checked against the
specification (`scripts/law_quotes.py`).
Last, the end-to-end cases of tests/run that use the driver's options (a `// module:` or `// args:` header,
about 90 of them) are run against their own expectations (`scripts/js_run_test.py --driver-cases --jobs 3`,
about 15 s); `--all-run-tests` runs all of tests/run instead (about a minute at `--jobs 3`). A case with a
`// needs:` header is reported as not run and does not fail the check.
"""

import argparse
import hashlib
import re
import subprocess
import sys
import threading
import time
from pathlib import Path

import spec_text

ROOT = Path(__file__).resolve().parent.parent
SECONDS = 5.0
MEGABYTES = 1024


def rss_mb(pid: int) -> float:
    r = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True)
    return int(r.stdout.strip() or 0) / 1024


def run(cmd: list[str]) -> tuple[str, float, float, str | None]:
    """The record of a run, its seconds, its peak megabytes, and why it was killed (if it was)."""
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env={"JS_TRACE_STEPS": "1"})
    peak, killed = 0.0, None

    def watch() -> None:
        nonlocal peak, killed
        while p.poll() is None:
            peak = max(peak, rss_mb(p.pid))
            if peak > MEGABYTES:
                killed = f"over {MEGABYTES} MB"
            elif time.monotonic() - t0 > SECONDS:
                killed = f"over {SECONDS:g} s"
            if killed:
                p.kill()
                return
            time.sleep(0.05)

    w = threading.Thread(target=watch)
    w.start()
    out, err = p.communicate()
    w.join()
    steps = hashlib.md5()
    n = 0
    cells = "-"
    for line in err.decode(errors="replace").splitlines():
        if line.startswith("cells\t"):
            cells = line.split("\t")[1]
            continue
        f = line.split(" ")
        if len(f) >= 2 and f[1].endswith("."):
            steps.update(f"{f[0]} {f[1]}\n".encode())
            n += 1
    rec = f"{out.decode(errors='replace')}exit {p.returncode}\nsteps {n} {steps.hexdigest()}\ncells {cells}\n"
    return rec, time.monotonic() - t0, peak, killed


# What the specification's library must not contain: it is definitions and stated laws only.
FORBIDDEN = re.compile(
    r":= by\b|\bby (simp|omega|decide|exact|rfl|cases|intro|intros|induction|unfold|constructor|funext|rw|apply|"
    r"native_decide|grind|all_goals)\b|^\s*(theorem|lemma|decreasing_by|termination_by|initialize)\b|"
    r"^\s*(private |protected )?(partial|unsafe) def|@\[(csimp|implemented_by)|\bsorry\b|\bdbgTrace\b|\boutOfFuel\b"
)


def spec_is_plain() -> list[str]:
    """The lines of lean/Ecma (outside Gen/) with a theorem, a tactic, or a partial or unsafe definition."""
    bad = []
    for f in sorted((ROOT / "lean/Ecma").rglob("*.lean")):
        if "Gen" in f.parts:
            continue
        for n, line in enumerate(f.read_text().splitlines(), 1):
            if FORBIDDEN.search(line) and not line.lstrip().startswith(("--", "/--")):
                bad.append(f"{f.relative_to(ROOT)}:{n}: {line.strip()[:100]}")
    return bad


def no_native_decide() -> list[str]:
    """No Lean file under lean/ uses `native_decide`."""
    pat = re.compile(r"\bnative_decide\b")
    bad = []
    for f in sorted((ROOT / "lean").rglob("*.lean")):
        text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), f.read_text(), flags=re.S)
        for n, line in enumerate(text.splitlines(), 1):
            code = line.split("--", 1)[0]
            if pat.search(code):
                bad.append(f"{f.relative_to(ROOT)}:{n}: {line.strip()[:100]}")
    return bad


# The kept id tables (crates/spec-gen ids.rs) and the generated arrays they number.
KEPT = {"clause": "clauses", "sdo": "sdos", "method": "methods", "erratum": "errata", "reason": "reasons", "note": "notes"}


def kept_table(path: Path) -> list[tuple[int, str]]:
    """A kept table's entries: number and name."""
    out = []
    for line in path.read_text().splitlines():
        if line and not line.startswith("#"):
            f = line.split("\t")
            out.append((int(f[0]), f[1]))
    return out


def ids_consistent() -> list[str]:
    """Every kept number names in lean/Ecma/Gen/Decls.lean what its table says, and every name there has a number:
    regenerating from the checked-in inputs keeps every number (the generator reads these tables)."""
    decls = (ROOT / "lean/Ecma/Gen/Decls.lean").read_text()
    ids_dir = spec_text.ids_dir()
    bad = []
    for kind, arr in KEPT.items():
        path = ids_dir / f"{kind}-ids.txt"
        if not path.exists():
            bad.append(f"{path.relative_to(ROOT)}: missing (scripts/generate.py writes it)")
            continue
        m = re.search(rf"def {arr} : Array String :=\s*(.*?)\n\n", decls, re.S)
        names = [re.sub(r"\\(.)", lambda e: {"n": "\n", "t": "\t"}.get(e.group(1), e.group(1)), x) for x in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))] if m else []
        table = kept_table(path)
        for i, n in table:
            if i >= len(names) or names[i] != n:
                bad.append(f"{path.relative_to(ROOT)}: {i} is {n}, but Ecma.Gen.{arr} has {names[i] if i < len(names) else 'nothing'} there")
        numbered = {i for i, _ in table}
        for i, n in enumerate(names):
            if i not in numbered and n:
                bad.append(f"Ecma.Gen.{arr}[{i}] = {n} has no number in {path.relative_to(ROOT)}")
    return bad[:20]


def lean_names(text: str, arr: str) -> list[str]:
    """The strings of `def ARR : … := [ … ]` (an Array or a List) in `text`."""
    m = re.search(rf"def {arr} : [^\n]*:=\s*(.*?)\n\n", text, re.S)
    return [re.sub(r"\\(.)", lambda e: {"n": "\n", "t": "\t"}.get(e.group(1), e.group(1)), x) for x in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))] if m else []


def grammar_ids_consistent() -> list[str]:
    """The grammar's kept ids (jsgrammar ids.rs) number what lean/ has: `NT`'s and `Param`'s constructors in order
    (`retired_Name` for a retired one) and their `names`, Decls.lean's nts, params and prods (spec-gen's grammar, up to
    its last), tests/parser/grammar_index.txt's `prod` lines, and `Gen.prodIds` (the index's ids in its order); and
    table-ids.txt numbers the tables of lean/Ecma/Gen/Tables_N.lean in their order."""
    bad = []
    ids_dir = spec_text.ids_dir()
    sym = (ROOT / "lean/Ecma/Grammar/Gen/Symbols.lean").read_text()
    decls = (ROOT / "lean/Ecma/Gen/Decls.lean").read_text()
    for kind, ind, arr in (("nt", "NT", "nts"), ("param", "Param", "params")):
        path = ids_dir / f"{kind}-ids.txt"
        if not path.exists():
            bad.append(f"{path.relative_to(ROOT)}: missing (scripts/generate.py writes it)")
            continue
        rows = [l.split("\t") for l in path.read_text().splitlines() if l and not l.startswith("#")]
        m = re.search(rf"inductive {ind} where\n(.*?)\n  deriving", sym, re.S)
        ctors = [l.strip()[2:] for l in m.group(1).splitlines()] if m else []
        want = [("retired_" + r[1]) if r[2:] == ["retired"] else r[1] for r in rows]
        if [int(r[0]) for r in rows] != list(range(len(rows))) or ctors != want:
            bad.append(f"{path.relative_to(ROOT)}: Ecma.Grammar.{ind}'s constructors are not its names in its order")
        if lean_names(sym, f"{ind}.names") != [r[1] for r in rows]:
            bad.append(f"{path.relative_to(ROOT)}: Ecma.Grammar.{ind}.names is not its names in its order")
        names = lean_names(decls, arr)
        if names != [r[1] for r in rows][:len(names)]:
            bad.append(f"{path.relative_to(ROOT)}: Ecma.Gen.{arr} is not its names in its order")
    path = ids_dir / "prod-ids.txt"
    if path.exists():
        table = dict(kept_table(path))
        names = lean_names(decls, "prods")
        bad += [f"{path.relative_to(ROOT)}: {i} is {table.get(i)}, but Ecma.Gen.prods has {n} there" for i, n in enumerate(names) if table.get(i, "") != n][:5]
        index = [l.split(" ", 2)[1:] for l in (ROOT / "tests/parser/grammar_index.txt").read_text().splitlines() if l.startswith("prod ")]
        bad += [f"tests/parser/grammar_index.txt: prod {i} {k}, but {path.relative_to(ROOT)} has {table.get(int(i))}" for i, k in index if table.get(int(i)) != k][:5]
        idx = (ROOT / "lean/Ecma/Grammar/Gen/Index.lean").read_text()
        m = re.search(r"def Gen\.prodIds : List \(Nat × Nat\) :=\s*\[(.*?)\]\n", idx, re.S)
        runs = [int(a) + k for a, n in re.findall(r"\((\d+), (\d+)\)", m.group(1)) for k in range(int(n))] if m else []
        if runs != [int(i) for i, _ in index]:
            bad.append("lean/Ecma/Grammar/Gen/Index.lean: Gen.prodIds is not tests/parser/grammar_index.txt's ids in its order")
    else:
        bad.append(f"{path.relative_to(ROOT)}: missing (scripts/generate.py writes it)")
    path = ids_dir / "table-ids.txt"
    if path.exists():
        mods = sorted((ROOT / "lean/Ecma/Gen").glob("Tables_*.lean"), key=lambda f: int(f.stem.split("_")[1]))
        order = [x for f in mods for x in re.findall(r"«([^»]*)»", re.search(r"def tables : List Table := \[(.*?)\]\n", f.read_text(), re.S).group(1))]
        table = kept_table(path)
        if [i for i, _ in table] != list(range(len(table))) or [n for _, n in table] != order:
            bad.append(f"{path.relative_to(ROOT)}: Ecma.Gen.tables (Tables_N.lean, in order) is not its names in id order")
    else:
        bad.append(f"{path.relative_to(ROOT)}: missing (scripts/generate.py writes it)")
    return bad[:20]


def ids_regenerated() -> tuple[list[str], str]:
    """Regenerating (target/release/spec-gen and jsgrammar, if they are newer than their sources) keeps every kept
    number (each table's lines are the regenerated table's) and writes lean/Ecma/Gen and lean/Ecma/Grammar/Gen as they
    are, and `spec-gen roundtrip` passes. The problems, and what was checked."""
    gen = ROOT / "target/release/spec-gen"
    jsg = ROOT / "target/release/jsgrammar"
    ids_dir = spec_text.ids_dir()
    jsrc = list((ROOT / "crates/jsgrammar/src").rglob("*.rs"))
    # spec-gen links the jsgrammar crate; each binary is current if it is newer than the sources it is built from
    srcs = {gen: list((ROOT / "crates/spec-gen/src").rglob("*.rs")) + jsrc, jsg: jsrc}
    if any(not g.exists() or any(f.stat().st_mtime > g.stat().st_mtime for f in srcs[g]) for g in (gen, jsg)):
        return [], "skipped: target/release/spec-gen or jsgrammar is missing or older than its sources (cargo build --release)"
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        ov = ROOT / "spec/formal"
        r = subprocess.run([str(jsg), "--spec", str(spec_text.spec_html()), "--out", str(Path(tmp) / "jsg"), "--readings", str(ov / "readings.emu"),
                            "--readings", str(ov / "syntax.emu"), "--json", str(ov / "json.emu"), "--ids", str(ids_dir)], capture_output=True, text=True)
        if r.returncode != 0:
            return [f"jsgrammar failed: {r.stderr.strip()[-300:]}"], "regenerated"
        r = subprocess.run([str(gen), f"--spec={spec_text.spec_html()}", f"--overlay={ov}", f"--ids={ids_dir}", "emit", f"--out={tmp}"],
                           capture_output=True, text=True)
        if r.returncode != 0:
            return [f"spec-gen emit failed: {r.stderr.strip()[-300:]}"], "regenerated"
        for t in ("prod", "nt", "param"):
            (Path(tmp) / "jsg" / f"{t}-ids.txt").replace(Path(tmp) / f"{t}-ids.txt")
        bad = []
        # the modules, byte for byte (gen_spec.py and jsgrammar.py --write keep these of what the generators write)
        for d, out, keep in ((ROOT / "lean/Ecma/Gen", Path(tmp), lambda n: not n.startswith(("Examples", "Host", "Memory"))),
                             (ROOT / "lean/Ecma/Grammar/Gen", Path(tmp) / "jsg", lambda n: n != "Keys.lean")):
            new = {f.name for f in out.glob("*.lean") if keep(f.name)}
            old = {f.name for f in d.glob("*.lean")}
            bad += [f"{d.relative_to(ROOT)}/{n}: not what regenerating writes" for n in sorted(new ^ old)]
            bad += [f"{d.relative_to(ROOT)}/{n}: not what regenerating writes" for n in sorted(new & old)
                    if (out / n).read_bytes() != (d / n).read_bytes()]
        r = subprocess.run([str(gen), f"--spec={spec_text.spec_html()}", f"--overlay={ov}", f"--ids={ids_dir}", "roundtrip"],
                           capture_output=True, text=True)
        if r.returncode != 0:
            bad.append("spec-gen roundtrip failed: " + " | ".join((r.stderr.strip() or r.stdout.strip()).splitlines()[-3:]))
        for kind in [*KEPT, "table", "prod", "nt", "param"]:
            path = ids_dir / f"{kind}-ids.txt"
            new = dict(kept_table(Path(tmp) / path.name))
            for i, n in kept_table(path) if path.exists() else []:
                if new.get(i) != n:
                    bad.append(f"{path.relative_to(ROOT)}: regenerating gives {i} to {new.get(i)}, not {n}")
            if path.exists() and (Path(tmp) / path.name).read_text() != path.read_text():
                bad.append(f"{path.relative_to(ROOT)} is not what regenerating writes (scripts/generate.py)")
        return bad[:20], "regenerated, and spec-gen roundtrip"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", default=str(ROOT / ".lake/build/bin/ecma-run"))
    ap.add_argument("--print", default=str(ROOT / ".lake/build/bin/ecma-print"), help="ecma-print, for scripts/bijection.py")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--all-run-tests", action="store_true", help="run all of tests/run, not only the driver's cases")
    ap.add_argument("rest", nargs="*", help="options passed to ecma-run")
    a = ap.parse_args()
    bad = 0
    for js in sorted((ROOT / "tests/quick").glob("*.js")):
        rec, secs, peak, killed = run([a.run, "--stats", *a.rest, str(js)])
        exp = js.with_suffix(".expected")
        if a.update and not killed:
            exp.write_text(rec)
        ok = not killed and exp.exists() and exp.read_text() == rec
        why = killed or ("" if ok else "differs from " + exp.name)
        print(f"{'ok  ' if ok else 'FAIL'} {js.name:14} {secs:5.2f} s {peak:6.0f} MB  {why}")
        bad += not ok
    plain = spec_is_plain()
    for line in plain:
        print("FAIL not plain:", line)
    print(f"{'FAIL' if plain else 'ok  '} lean/Ecma has no theorems, tactics, partial or unsafe definitions")
    no_nd = no_native_decide()
    for line in no_nd:
        print("FAIL native_decide:", line)
    print(f"{'FAIL' if no_nd else 'ok  '} lean/ has no native_decide")
    pc = subprocess.run([a.run, "--check-pins"], capture_output=True, text=True)
    for line in (pc.stdout + pc.stderr).splitlines():
        print(line)
    if pc.returncode != 0 and not any(l.startswith("FAIL") for l in (pc.stdout + pc.stderr).splitlines()):
        print(f"FAIL pins check exited {pc.returncode}")
    ids = ids_consistent() + grammar_ids_consistent()
    for line in ids:
        print("FAIL ids:", line)
    print(f"{'FAIL' if ids else 'ok  '} the kept ids (spec/formal/*-ids.txt) number what lean/Ecma/Gen and lean/Ecma/Grammar/Gen have at them")
    regen, how = ids_regenerated()
    for line in regen:
        print("FAIL ids:", line)
    print(f"{'FAIL' if regen else 'ok  '} regenerating keeps every kept id and writes the generated modules as they are ({how})")
    ids += regen
    t0 = time.monotonic()
    b = subprocess.run([sys.executable, str(ROOT / "scripts/bijection.py"), "--print", a.print], capture_output=True, text=True)
    for line in (b.stdout + b.stderr).splitlines():
        if line.startswith(("FAIL", "  ", "...")) and not line.startswith(("  not data", "  printed", "  held", "  data")):
            print(line)
    tail = (b.stdout.strip() or b.stderr.strip() or "no output").splitlines()[-1]
    print(f"{'' if tail.startswith(('ok', 'FAIL')) else 'FAIL '}{tail} ({time.monotonic() - t0:.1f} s)")
    q = subprocess.run([sys.executable, str(ROOT / "scripts/law_quotes.py")], capture_output=True, text=True)
    print(q.stdout.rstrip())
    rt = subprocess.run([sys.executable, str(ROOT / "scripts/js_run_test.py"), "--run", a.run, "--jobs", "3",
                         *([] if a.all_run_tests else ["--driver-cases"])], cwd=ROOT, capture_output=True, text=True)
    for line in rt.stdout.splitlines():
        if line.startswith(("FAIL", "not ")):
            print(line)
    tail = rt.stdout.rstrip().splitlines()[-1:] or ["no output"]
    print(f"{'FAIL' if rt.returncode else 'ok  '} tests/run{'' if a.all_run_tests else ' (the driver cases)'}: {tail[0]}")
    return 1 if bad or plain or no_nd or pc.returncode or ids or b.returncode or q.returncode or rt.returncode else 0


if __name__ == "__main__":
    sys.exit(main())
