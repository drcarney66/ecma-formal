#!/usr/bin/env python3
"""End-to-end tests of the JS driver: ecma-run on tests/run/*.js.

Every tests/run/*.js is run as `ecma-run FILE`.
Header comments in the file give the expectation:

    // expect: <the line the run prints>
    // print: <a line the host's `print` writes>   (any number, in order)
    // exit: <status>          (default: from the `expect` line)
    // module: yes             (run the file as a Module: `--module`)
    // args: <driver options>
    // needs: <what>           (not run: the driver lacks <what>; reported apart)

In the expected lines `#N` stands for any object number (`[object #N]`), which
changes whenever the realm's intrinsics do.

A Module's imports are other files under `tests/run/modules/`, which are not
cases themselves: the driver's loader is flat (`--module-dir DIR` serves
`DIR/NAME` as `./NAME`), so a case that loads one has the header
`// args: --module-dir tests/run/modules` and imports `./NAME`.

A case with a `// needs:` header asks for something the driver does not have
(an option, a host hook): it is not run, and is reported as `not run: needs
<what>` and counted apart from the passes and the failures. `--case NAME` runs
it all the same (to see whether the driver has it now).

Every case runs on the driver's fixed host, which defines `print`. The driver
prints the result line, then the lines `print` wrote. `--arg A` adds `A` to
every run (`--checked`).

    python3 scripts/js_run_test.py --run .lake/build/bin/ecma-run \\
        --expect-file tests/expected/ecma-run.txt [--update]

With `--same-as OTHER`, every case is run by the driver and by OTHER instead,
and the two must print the same (stdout, stderr and the exit status), whatever
the headers say; `--other-arg A` adds `A` to the other program's runs
(`--no-accel`); `--ignore-stderr P` leaves the stderr lines starting with `P`
out of the comparison (`unchecked `).

With `--expect-file F`, F's rows (`name<TAB>line`, `\\n` and `\\\\` escaped) override
the headers of the cases they name with the line the program is allowed to
print instead (ecma-run's stops). `--update` writes F from this run: a row for
each case that does not print what its header expects. F only shrinks: a case
without a row that fails is an error, and the file is not written.

`--case NAME` (any number) runs only the cases named; the other cases' rows are kept. `--driver-cases`
runs only the cases with a `// module:` or `// args:` header, those that use the driver's options (the
quick check runs these; scripts/quick_check.py --all-run-tests all of them).

The runs go `--jobs` at a time (default min(8, CPUs)); a run past `--timeout`
seconds (default 60) prints `timeout`, a status a row may name.
"""

import argparse
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SUITE = Path("tests/run")

# The exit status a header's result line implies (`exit`'s default): ecma-run's (Engine.Host.outcome and
# Engine.Cli.main): a command line it refuses (`stop: unsupported OPTION`) or a bundle it refuses 2, every
# stop of a run 3, an abrupt completion other than a throw 4.
STATUS = [
    ("normal:", 0),
    ("throw:", 1),
    ("stop: unsupported", 2),
    ("stop: bundle:", 2),
    ("stop:", 3),
    ("abrupt:", 4),
    ("timeout", -1),
]

# One run's time limit (`--timeout`), and the status a run past it is given.
TIMEOUT_S = 60
TIMEOUT_STATUS = -1

HEADER = re.compile(r"^//\s*(expect|print|exit|module|args|needs):\s?(.*)$")


def expectations(path: Path) -> dict[str, str]:
    """The headers; the `print` lines are joined after the `expect` line."""
    out: dict[str, str] = {}
    printed: list[str] = []
    for line in path.read_text().splitlines():
        m = HEADER.match(line)
        if m and m.group(1) == "print":
            printed.append(m.group(2).rstrip())
        elif m:
            out[m.group(1)] = m.group(2).rstrip()
    if printed and "expect" in out:
        out["expect"] = "\n".join([out["expect"], *printed])
    return out


def matches(got: str, want: str) -> bool:
    """`got` is `want`, where `#N` in `want` stands for any object number."""
    return re.fullmatch(re.escape(want).replace("\\#N", r"#\d+"), got) is not None


def expected_status(exp: dict[str, str]) -> int:
    if "exit" in exp:
        return int(exp["exit"])
    for prefix, status in STATUS:
        if exp.get("expect", "").startswith(prefix):
            return status
    raise ValueError("no `expect` or `exit` header")


def read_rows(path: Path) -> dict[str, str]:
    """The expect file's rows: case name to the line it may print."""
    rows: dict[str, str] = {}
    if path.exists():
        for line in path.read_text().splitlines():
            if line and not line.startswith("#"):
                name, _, got = line.partition("\t")
                rows[name] = re.sub(r"\\(.)", lambda m: "\n" if m.group(1) == "n" else m.group(1), got)
    return rows


def write_rows(path: Path, rows: dict[str, str]) -> None:
    esc = lambda t: t.replace("\\", "\\\\").replace("\n", "\\n")
    head = "# What ecma-run prints instead of a case's `expect` header; written by js_run_test.py --update, only shrinks.\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(head + "".join(f"{n}\t{esc(rows[n])}\n" for n in sorted(rows)))


def command(driver: str, extra: list[str], exp: dict[str, str], case: Path) -> list[str]:
    """The run of `case` its headers ask for."""
    cmd = [driver, *extra]
    if exp.get("module") == "yes":
        cmd.append("--module")
    if "args" in exp:
        cmd += exp["args"].split()
    return cmd + [str(case)]


def kept(stderr: str, prefixes: list[str]) -> str:
    """`stderr` without its lines that start with one of `prefixes`."""
    return "".join(l for l in stderr.splitlines(keepends=True) if not l.startswith(tuple(prefixes)))


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    """`cmd`'s result; a run past TIMEOUT_S prints `timeout`."""
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, TIMEOUT_STATUS, "timeout\n", "")


def main() -> int:
    global TIMEOUT_S
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="the driver (ecma-run)")
    ap.add_argument("--suite", default=str(SUITE))
    ap.add_argument("--same-as", help="compare the driver's output with this binary's instead of the headers")
    ap.add_argument("--arg", action="append", default=[], help="an argument added to every run (e.g. --checked)")
    ap.add_argument("--other-arg", action="append", default=[], help="with --same-as: an argument added to the other's runs")
    ap.add_argument("--ignore-stderr", action="append", default=[], help="with --same-as: stderr lines starting with this not compared")
    ap.add_argument("--expect-file", help="rows `name<TAB>line` overriding the headers")
    ap.add_argument("--update", action="store_true", help="write --expect-file from this run (only shrinks)")
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1), help="runs at a time")
    ap.add_argument("--timeout", type=int, default=TIMEOUT_S, help="one run's time limit (s)")
    ap.add_argument("--skip", action="append", default=[], help="a case not run (its --expect-file row is kept)")
    ap.add_argument("--case", action="append", default=[], help="run only this case (its --expect-file rows are the only ones changed)")
    ap.add_argument("--driver-cases", action="store_true", help="run only the cases with a `module` or `args` header")
    args = ap.parse_args()
    TIMEOUT_S = args.timeout
    driver = str(Path(args.run).resolve())
    expect_file = Path(args.expect_file) if args.expect_file else None
    if args.update and not expect_file:
        print("--update needs --expect-file")
        return 1
    rows = read_rows(expect_file) if expect_file else {}
    fresh = expect_file is not None and not expect_file.exists()
    new_rows: dict[str, str] = {}
    fixed: list[str] = []
    cases = sorted(c for c in Path(args.suite).glob("*.js") if c.name not in args.skip)
    new_rows.update({n: rows[n] for n in args.skip if n in rows})
    if args.case:
        missing = sorted(set(args.case) - {c.name for c in cases})
        if missing:
            print(f"no such case in {args.suite}: {', '.join(missing)}")
            return 1
        cases = [c for c in cases if c.name in args.case]
        new_rows.update({n: g for n, g in rows.items() if n not in args.case})
    if args.driver_cases:
        kept_rows = {c.name for c in cases if not ({"module", "args"} & expectations(c).keys())}
        new_rows.update({n: rows[n] for n in kept_rows if n in rows})
        cases = [c for c in cases if c.name not in kept_rows]
    if not cases:
        print(f"no test cases in {args.suite}")
        return 1
    failures = 0
    # Cases that need what the driver lacks: not run, unless named by --case.
    needs = {c: n for c in cases if (n := expectations(c).get("needs")) and c.name not in args.case}
    for case, what in needs.items():
        print(f"not  {case.name}: not run: needs {what}")
    cases = [c for c in cases if c not in needs]
    new_rows.update({c.name: rows[c.name] for c in needs if c.name in rows})
    other = str(Path(args.same_as).resolve()) if args.same_as else None
    cmds = {case: command(driver, args.arg, expectations(case), case) for case in cases}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        runs = {case: pool.submit(run, cmd) for case, cmd in cmds.items()}
        others = {case: pool.submit(run, [other, *args.other_arg, *cmd[1:]]) for case, cmd in cmds.items()} if other else {}
    for case in cases:
        exp = expectations(case)
        cmd = cmds[case]
        r = runs[case].result()
        if other:
            r2 = others[case].result()
            ign = args.ignore_stderr
            same = (r.returncode, r.stdout, kept(r.stderr, ign)) == (r2.returncode, r2.stdout, kept(r2.stderr, ign))
            if not same:
                failures += 1
                print(f"FAIL {case.name}: {Path(driver).name} exit {r.returncode}, {Path(other).name} exit {r2.returncode}")
                for name, x in ((Path(driver).name, r), (Path(other).name, r2)):
                    print(f"  {name}: {(x.stdout + x.stderr).strip()[:400]!r}")
            else:
                print(f"same {case.name}: {r.stdout.strip()[:80] or '(exit ' + str(r.returncode) + ')'}")
            continue
        got = r.stdout.strip()

        def check(exp: dict[str, str]) -> list[str]:
            problems = []
            want_status = expected_status(exp)
            if r.returncode != want_status:
                problems.append(f"exit {r.returncode}, expected {want_status}")
            if "expect" in exp and not matches(got, exp["expect"]):
                problems.append(f"printed {got!r}, expected {exp['expect']!r}")
            return problems

        problems = check(exp)
        if problems and expect_file:
            if args.update:
                if case.name in rows or fresh:
                    new_rows[case.name] = got
                    problems = []
                else:
                    problems.append(f"not in {expect_file} (it only shrinks)")
            elif case.name in rows:
                problems = check({"expect": rows[case.name]})
        elif not problems and case.name in rows:
            fixed.append(case.name)
        if problems:
            failures += 1
            print(f"FAIL {case.name}: " + "; ".join(problems))
            if r.stderr.strip():
                print("  stderr: " + r.stderr.strip().replace("\n", "\n          "))
        else:
            print(f"ok   {case.name}: {got or '(exit ' + str(r.returncode) + ')'}")
    if args.update and expect_file:
        if failures:
            print(f"{expect_file} not written: {failures} new failures")
        else:
            write_rows(expect_file, new_rows)
            print(f"wrote {expect_file}: {len(new_rows)} rows (was {len(rows)})")
    elif fixed:
        print(f"{len(fixed)} cases now print their header ({', '.join(fixed[:5])}...): run with --update to drop their rows")
    not_run = f", {len(needs)} not run ({', '.join(sorted({f'needs {w}' for w in needs.values()}))})" if needs else ""
    print(f"{len(cases) + len(needs)} cases: {len(cases) - failures} passed, {failures} failed{not_run}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
