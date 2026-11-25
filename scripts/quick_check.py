#!/usr/bin/env python3
"""The quick check: a handful of programs on ecma-run, each within a time and a memory limit.

    python3 scripts/quick_check.py [--run .lake/build/bin/ecma-run] [--update] [-- ECMA-RUN-OPTIONS]

Each tests/quick/NAME.js runs with JS_TRACE_STEPS=1. Its result line, printed lines, exit status, the digest
of the steps it entered (each trace line's section and step number, not its text) and the cells its store
ends with (the store only grows, so this is what it allocated) must be tests/quick/NAME.expected; `--update` rewrites those. A run over SECONDS of wall clock or MEGABYTES of resident
memory is killed and fails. Then lean/Ecma (outside Gen/) is checked to hold no theorem, tactic, or partial or
unsafe definition: the specification is definitions and stated laws only. Then every generated id namespace
in lean/Ecma/Gen/Decls.lean, lean/Ecma/Grammar/Gen (NT, Param, Gen.prodIds), lean/Ecma/Gen/Tables.lean, and
tests/parser/grammar_index.txt is checked to be sorted alphabetically and unique;
and, with a current target/release/spectec, regenerating from `spec/spectec/` writes the same
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


DECL_ARRS = ("clauses", "sdos", "methods", "fields", "enums", "prims", "sorts", "nts", "params", "prods")


def lean_names(text: str, arr: str) -> list[str]:
    """The strings of `def ARR : … := #[ … ]` or `[ … ]` in `text`."""
    m = re.search(rf"def {arr} : [^\n]*:=\s*(.*?)(?:\n\n|\Z)", text, re.S)
    return [re.sub(r"\\(.)", lambda e: {"n": "\n", "t": "\t"}.get(e.group(1), e.group(1)), x) for x in re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))] if m else []


def check_sorted_unique(label: str, names: list[str]) -> list[str]:
    if not names:
        return [f"{label}: empty"]
    for i in range(len(names) - 1):
        if not (names[i] < names[i + 1]):
            return [f"{label}[{i}..{i+1}] not strictly sorted: {names[i]!r}, {names[i+1]!r}"]
    return []


def ids_consistent() -> list[str]:
    """Every generated id table in `Ecma.Gen.Decls`, `Ecma.Gen.Tables`, `Ecma.Grammar.NT`, `Param`,
    `tests/parser/grammar_index.txt`, and `Gen.prodIds` is sorted alphabetically, unique, and mutually consistent."""
    decls = (ROOT / "lean/Ecma/Gen/Decls.lean").read_text()
    sym = (ROOT / "lean/Ecma/Grammar/Gen/Symbols.lean").read_text()
    tbls = (ROOT / "lean/Ecma/Gen/Tables.lean").read_text()
    bad = []
    arrs: dict[str, list[str]] = {}
    for arr in DECL_ARRS:
        names = lean_names(decls, arr)
        arrs[arr] = names
        bad += check_sorted_unique(f"Ecma.Gen.{arr}", names)
    for ind, arr in (("NT", "nts"), ("Param", "params")):
        m = re.search(rf"inductive {ind} where\n(.*?)\n  deriving", sym, re.S)
        ctors = [l.strip()[2:] for l in m.group(1).splitlines()] if m else []
        if ctors != arrs[arr]:
            bad.append(f"Ecma.Grammar.{ind}'s constructors do not match Ecma.Gen.{arr}")
        if lean_names(sym, f"{ind}.names") != arrs[arr]:
            bad.append(f"Ecma.Grammar.{ind}.names does not match Ecma.Gen.{arr}")
    prods = arrs["prods"]
    index = [l.split(" ", 2)[1:] for l in (ROOT / "tests/parser/grammar_index.txt").read_text().splitlines() if l.startswith("prod ")]
    for i_s, k in index:
        i = int(i_s)
        if i < 0 or i >= len(prods) or prods[i] != k:
            bad.append(f"tests/parser/grammar_index.txt: prod {i} {k}, but Ecma.Gen.prods has {prods[i] if 0 <= i < len(prods) else 'OOB'}")
            break
    idx = (ROOT / "lean/Ecma/Grammar/Gen/Index.lean").read_text()
    m = re.search(r"def Gen\.prodIds : List \(Nat × Nat\) :=\s*\[(.*?)\]\n", idx, re.S)
    runs = [int(a) + k for a, n in re.findall(r"\((\d+), (\d+)\)", m.group(1)) for k in range(int(n))] if m else []
    if runs != [int(i) for i, _ in index]:
        bad.append("lean/Ecma/Grammar/Gen/Index.lean: Gen.prodIds is not tests/parser/grammar_index.txt's ids in its order")
    bad += check_sorted_unique("Ecma.Gen.tableNames", lean_names(tbls, "tableNames"))
    return bad[:20]


def ids_regenerated() -> tuple[list[str], str]:
    """Regenerating (`target/release/spectec`, if current) writes `lean/Ecma/Gen`, `lean/Ecma/Grammar/Gen`,
    and `tests/parser/grammar_index.txt` byte-for-byte as they are, and `spectec roundtrip` passes."""
    spectec = ROOT / "target/release/spectec"
    spec_dir = ROOT / "spec/spectec"
    srcs = list((ROOT / "crates/spectec/src").rglob("*.rs")) + [ROOT / "crates/spectec/Cargo.toml"]
    if not spectec.exists() or any(f.stat().st_mtime > spectec.stat().st_mtime for f in srcs):
        return [], "skipped: target/release/spectec is missing or older than its sources (cargo build --release)"
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        tdir = Path(tmp)
        lean_out = tdir / "lean"
        gi_out = tdir / "grammar_index.txt"
        r = subprocess.run(
            [str(spectec), f"--spec-dir={spec_dir}", "emit", f"--lean-dir={lean_out}", f"--grammar-index={gi_out}"],
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


def html_bijection() -> tuple[list[str], str]:
    """If target/release/spectec-html is built and current, verify spec/spectec + spec/html <-> spec.html."""
    bin_path = ROOT / "target/release/spectec-html"
    srcs = (
        list((ROOT / "crates/spectec-html/src").rglob("*.rs"))
        + list((ROOT / "crates/spectec/src").rglob("*.rs"))
        + [ROOT / "crates/spectec-html/Cargo.toml"]
    )
    if not bin_path.exists() or any(f.stat().st_mtime > bin_path.stat().st_mtime for f in srcs):
        return [], "skipped: target/release/spectec-html is missing or older than its sources (cargo build --release)"
    r = subprocess.run([sys.executable, str(ROOT / "scripts/html_bijection.py"), "--bin", str(bin_path)], capture_output=True, text=True)
    if r.returncode != 0:
        detail = " | ".join((r.stderr.strip() or r.stdout.strip()).splitlines()[-3:])
        return [f"html bijection failed: {detail}"], "spec/html"
    tail = (r.stdout.strip().splitlines() or ["ok"])[-1]
    return [], tail


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
    ids = ids_consistent()
    for line in ids:
        print("FAIL ids:", line)
    print(f"{'FAIL' if ids else 'ok  '} lean/Ecma/Gen and lean/Ecma/Grammar/Gen have sorted unique ids matching grammar_index.txt")
    regen, how = ids_regenerated()
    for line in regen:
        print("FAIL ids:", line)
    print(f"{'FAIL' if regen else 'ok  '} regenerating writes the generated modules as they are ({how})")
    ids += regen
    t0 = time.monotonic()
    b = subprocess.run([sys.executable, str(ROOT / "scripts/bijection.py"), "--print", a.print], capture_output=True, text=True)
    for line in (b.stdout + b.stderr).splitlines():
        if line.startswith(("FAIL", "  ", "...")) and not line.startswith(("  not data", "  printed", "  held", "  data")):
            print(line)
    tail = (b.stdout.strip() or b.stderr.strip() or "no output").splitlines()[-1]
    print(f"{'' if tail.startswith(('ok', 'FAIL')) else 'FAIL '}{tail} ({time.monotonic() - t0:.1f} s)")
    hb_bad, hb_msg = html_bijection()
    for line in hb_bad:
        print("FAIL html bijection:", line)
    print(f"{'FAIL' if hb_bad else 'ok  '} html bijection ({hb_msg})")
    q = subprocess.run([sys.executable, str(ROOT / "scripts/law_quotes.py")], capture_output=True, text=True)
    print(q.stdout.rstrip())
    rt = subprocess.run([sys.executable, str(ROOT / "scripts/js_run_test.py"), "--run", a.run, "--jobs", "3",
                         *([] if a.all_run_tests else ["--driver-cases"])], cwd=ROOT, capture_output=True, text=True)
    for line in rt.stdout.splitlines():
        if line.startswith(("FAIL", "not ")):
            print(line)
    tail = rt.stdout.rstrip().splitlines()[-1:] or ["no output"]
    print(f"{'FAIL' if rt.returncode else 'ok  '} tests/run{'' if a.all_run_tests else ' (the driver cases)'}: {tail[0]}")
    return 1 if bad or plain or no_nd or pc.returncode or ids or b.returncode or hb_bad or q.returncode or rt.returncode else 0


if __name__ == "__main__":
    sys.exit(main())
