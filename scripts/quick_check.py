#!/usr/bin/env python3
"""The quick check: a handful of programs on ecma-run, each within a time and a memory limit.

    python3 scripts/quick_check.py [--run .lake/build/bin/ecma-run] [--update] [-- ECMA-RUN-OPTIONS]

Each tests/quick/NAME.js runs with JS_TRACE_STEPS=1. Its result line, printed lines, exit status, the digest
of the steps it entered (each trace line's section and step number, not its text) and the cells its store
ends with (the store only grows, so this is what it allocated) must be tests/quick/NAME.expected; `--update` rewrites those. A run over SECONDS of wall clock or MEGABYTES of resident
memory is killed and fails. Then lean/Ecma (outside Gen/) is checked to hold no theorem, tactic, or partial or
unsafe definition: the specification is definitions and stated laws only. Then the kept id tables
(spec/ids/{clause,sdo,method,field,enum,prim,sort}-ids.txt) are checked against lean/Ecma/Gen/Decls.lean: each
number names there what its table says, and each name there has a number; the grammar's (nt-, param-,
prod-ids.txt) against lean/Ecma/Grammar/Gen (`NT`'s and `Param`'s constructors, `Gen.prodIds`), Decls.lean and
tests/parser/grammar_index.txt, and table-ids.txt against `Ecma.Gen.tableNames` in lean/Ecma/Gen/Tables.lean;
and, with a current target/release/spectec, regenerating from `spec/spectec/` and `spec/ids/` writes the same
lean/Ecma/Gen, lean/Ecma/Grammar/Gen, and tests/parser/grammar_index.txt byte for byte, and `spectec roundtrip`
passes (every `.spectec` file parses and prints back byte for byte): the text's half of the bijection.
Then the data's half: every `.spectec` file in `spec/spectec/` is printed back byte for byte from `lean/Ecma/Gen`
and `lean/Ecma/Grammar/Gen` by `ecma-print` (`scripts/bijection.py`). Then every law's quotation is checked against
the specification (`scripts/law_quotes.py`).
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


# The kept id tables (`spec/ids`) and the generated arrays in `Ecma.Gen.Decls`.
NUMBERED_KEPT = {"clause": "clauses", "sdo": "sdos", "method": "methods"}
PLAIN_KEPT = {"field": "fields", "enum": "enums", "prim": "prims", "sort": "sorts"}
KEPT = {**NUMBERED_KEPT, **PLAIN_KEPT}


def kept_table(path: Path, numbered: bool = True) -> list[tuple[int, str]]:
    """A kept table's entries: number and name."""
    out = []
    idx = 0
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        if numbered:
            f = line.split("\t")
            out.append((int(f[0]), f[1]))
        else:
            out.append((idx, line))
            idx += 1
    return out


def lean_names(text: str, arr: str) -> list[str]:
    """The strings of `def ARR : … := #[ … ]` or `[ … ]` in `text`."""
    m = re.search(rf"def {arr} : [^\n]*:=\s*(.*?)(?:\n\n|\Z)", text, re.S)
    return [re.sub(r"\\(.)", lambda e: {"n": "\n", "t": "\t"}.get(e.group(1), e.group(1)), x) for x in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))] if m else []


def ids_consistent() -> list[str]:
    """Every kept number names in lean/Ecma/Gen/Decls.lean what its table says, and every name there has a number:
    regenerating from `spec/ids` keeps every number."""
    decls = (ROOT / "lean/Ecma/Gen/Decls.lean").read_text()
    ids_dir = spec_text.ids_dir()
    bad = []
    for kind, arr in KEPT.items():
        path = ids_dir / f"{kind}-ids.txt"
        if not path.exists():
            bad.append(f"{path.relative_to(ROOT)}: missing")
            continue
        names = lean_names(decls, arr)
        table = kept_table(path, numbered=(kind in NUMBERED_KEPT))
        for i, n in table:
            if i >= len(names) or names[i] != n:
                bad.append(f"{path.relative_to(ROOT)}: {i} is {n}, but Ecma.Gen.{arr} has {names[i] if i < len(names) else 'nothing'} there")
        numbered = {i for i, _ in table}
        for i, n in enumerate(names):
            if i not in numbered and n:
                bad.append(f"Ecma.Gen.{arr}[{i}] = {n} has no number in {path.relative_to(ROOT)}")
    return bad[:20]


def grammar_ids_consistent() -> list[str]:
    """The grammar's kept ids (`spec/ids/{nt,param,prod,table}-ids.txt`) match `Ecma.Grammar.NT`, `Param`,
    `Ecma.Gen`, `tests/parser/grammar_index.txt`, `Gen.prodIds`, and `Ecma.Gen.tableNames`."""
    bad = []
    ids_dir = spec_text.ids_dir()
    sym = (ROOT / "lean/Ecma/Grammar/Gen/Symbols.lean").read_text()
    decls = (ROOT / "lean/Ecma/Gen/Decls.lean").read_text()
    tbls = (ROOT / "lean/Ecma/Gen/Tables.lean").read_text()
    for kind, ind, arr in (("nt", "NT", "nts"), ("param", "Param", "params")):
        path = ids_dir / f"{kind}-ids.txt"
        if not path.exists():
            bad.append(f"{path.relative_to(ROOT)}: missing")
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
        bad.append(f"{path.relative_to(ROOT)}: missing")
    path = ids_dir / "table-ids.txt"
    if path.exists():
        order = lean_names(tbls, "tableNames")
        table = kept_table(path)
        if [i for i, _ in table] != list(range(len(table))) or [n for _, n in table] != order:
            bad.append(f"{path.relative_to(ROOT)}: Ecma.Gen.tableNames is not its names in id order")
    else:
        bad.append(f"{path.relative_to(ROOT)}: missing")
    return bad[:20]


def ids_regenerated() -> tuple[list[str], str]:
    """Regenerating (`target/release/spectec`, if current) writes `lean/Ecma/Gen`, `lean/Ecma/Grammar/Gen`,
    and `tests/parser/grammar_index.txt` byte-for-byte as they are, and `spectec roundtrip` passes."""
    spectec = ROOT / "target/release/spectec"
    spec_dir = ROOT / "spec/spectec"
    ids_dir = spec_text.ids_dir()
    srcs = list((ROOT / "crates/spectec/src").rglob("*.rs")) + [ROOT / "crates/spectec/Cargo.toml"]
    if not spectec.exists() or any(f.stat().st_mtime > spectec.stat().st_mtime for f in srcs):
        return [], "skipped: target/release/spectec is missing or older than its sources (cargo build --release)"
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        tdir = Path(tmp)
        lean_out = tdir / "lean"
        gi_out = tdir / "grammar_index.txt"
        r = subprocess.run(
            [str(spectec), f"--spec-dir={spec_dir}", f"--ids-dir={ids_dir}", "emit", f"--lean-dir={lean_out}", f"--grammar-index={gi_out}"],
            capture_output=True,
            text=True,
        )
        if r.returncode != 0:
            return [f"spectec emit failed: {r.stderr.strip()[-300:]}"], "regenerated"
        bad = []
        for d, out, keep in (
            (ROOT / "lean/Ecma/Gen", lean_out / "Ecma/Gen", lambda _n: True),
            (ROOT / "lean/Ecma/Grammar/Gen", lean_out / "Ecma/Grammar/Gen", lambda n: n != "Keys.lean"),
        ):
            new = {f.name for f in out.glob("*.lean") if keep(f.name)}
            old = {f.name for f in d.glob("*.lean")}
            bad += [f"{d.relative_to(ROOT)}/{n}: not what regenerating writes" for n in sorted(new ^ old)]
            bad += [
                f"{d.relative_to(ROOT)}/{n}: not what regenerating writes"
                for n in sorted(new & old)
                if (out / n).read_bytes() != (d / n).read_bytes()
            ]
        if gi_out.read_bytes() != (ROOT / "tests/parser/grammar_index.txt").read_bytes():
            bad.append("tests/parser/grammar_index.txt: not what regenerating writes")
        r = subprocess.run([str(spectec), f"--spec-dir={spec_dir}", "roundtrip"], capture_output=True, text=True)
        if r.returncode != 0:
            bad.append("spectec roundtrip failed: " + " | ".join((r.stderr.strip() or r.stdout.strip()).splitlines()[-3:]))
        return bad[:20], "regenerated, and spectec roundtrip"


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
    print(f"{'FAIL' if ids else 'ok  '} the kept ids (spec/ids/*-ids.txt) number what lean/Ecma/Gen and lean/Ecma/Grammar/Gen have at them")
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
