#!/usr/bin/env python3
"""test262 through ecma-run: the sample, its per-mode runs, the ratchet and the census.

    python3 scripts/test262.py sample                 # write tests/test262/sample.conf (seed 262)
    python3 scripts/test262.py expand --batch 300     # append 300 tests never sampled (stratified; new, so pending)
    python3 scripts/test262.py expand --status        # the sample's coverage of test262, per top directory
    python3 scripts/test262.py run                    # the sample's pending tests on ecma-run (mode default)
    python3 scripts/test262.py run --full             # every test of the sample (over FULL_MAX: --scheduled)
    python3 scripts/test262.py plan                   # the chunks of ~10 minutes the pending tests make
    python3 scripts/test262.py run --chunk 3/8        # one of them (chunks may run concurrently)
    python3 scripts/test262.py round --batch 300 --update  # expand, then each chunk's command
    python3 scripts/test262.py run --mode plain --update   # record the run (the ratchet's floor rises with it)
    python3 scripts/test262.py run --stage suite --scheduled --update  # the whole suite (user-scheduled)
    python3 scripts/test262.py merge --mode default --against plain OTHER/default.tsv  # another machine's rows, recorded here
    python3 scripts/test262.py census                 # board/test262.md from the runs' results
    python3 scripts/test262.py ratchet                # the expected files against their floor

The modes (crates/test262-runner's): `default` (the machine, accelerated), `checked` (`--checked`), `plain`
(`--no-accel`) and `plain-checked`.

`run` builds ecma-run (`lake build ecma-run`) and the runner (`cargo build --release -p test262-runner`), then runs
crates/test262-runner with `--run`, `--mode MODE` and
`--serve` on the stage's pending tests (`--stage`, default sample): those whose expected bucket is
`stop`, `fail` or `unsupported`, and those the expected file does not list; known-good passes are kept by
the ratchet, not re-run, and `timeout` and `timeout(fuel)` rows are
parked (`--timeouts` re-runs them), as are the tests of a feature in
LIMITS (`# limit <test>: <reason>` in the expected file; `--limits` runs them alone, but the excluded ones: a reason in
EXCLUDED, which no run runs and the census counts apart from `tests`).
`--full` runs every test of the stage (`suite`, the whole suite, only with `--scheduled`: the user
schedules full runs; on any stage of over FULL_MAX (3000) runnable tests, such as a grown sample, too). `--update` merges the re-run tests' rows into the expected file (a test not re-run
keeps its row) and raises the floor. `--chunk I/M` runs the I-th of M chunks of those, by a hash of the test's path, so
that chunks run at once or one after another, before or after another chunk's `--update`, split the same
tests; `plan` picks M from the recorded times so that a chunk takes about `--minutes` (10). A run on
suite is a chunk, once it has an expected file (without one every test is new), or a scheduled run.
Each test's bucket, milliseconds and detail are merged into OUT/<stage>/<mode>.tsv (`--out`, default
$TMPDIR/test262: the latest row per test), which `plan` and `census` read. A run's wall-clock timeouts (a test's or
its harness run's, not the rss cap's) run
again once it ends, at the same limit and `--retry-jobs` (8; 0: none) jobs, and the second rows are recorded in
place of the first: on a loaded machine a test near the limit times out by contention. `--tests-from FILE` keeps only the
tests FILE lists. Every other argument after `--` goes to the runner. Every `fail` (a
wrong answer) is printed at the end: report each as a finding. A stop's site is the machine's own record of the step
that stopped.

The ratchet (`tests/expected/<stage>/floor.txt`): per mode, every test that passed at the last update still
passes, and the passes are never fewer; no expected file has a `fail` row (a wrong answer is fixed, never
recorded); across modes, no test passes in one and fails in another. `run --update` raises the floor when it holds.
"""

import argparse
import contextlib
import datetime
import fcntl
import math
import os
import random
import re
import signal
import statistics
import subprocess
import sys
import time
import zlib
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODES = ["default", "checked", "plain", "plain-checked"]
# The program the tests run on and the runner, as `run` builds them.
RUN = ROOT / ".lake/build/bin/ecma-run"
RUNNER = ROOT / "target/release/test262-runner"
BUCKETS = ["pass", "fail", "stop", "unsupported", "timeout", "timeout(fuel)"]
# The timeouts: over the wall clock (or the rss cap), and out of fuel, kept apart.
TIMEOUTS = ("timeout", "timeout(fuel)")
SEED = 262
SIZE = 1500
# The top-level directories the stages run (intl402 is ECMA-402, not ECMA-262); not staging/sm (SpiderMonkey's tests: many test its extensions).
TOP = ["annexB", "built-ins", "harness", "language", "staging"]
EXCLUDE = ["staging/sm"]
# The stages a full run of is the user's to schedule, and the most runnable tests an unscheduled --full run runs.
SCHEDULED = {"suite"}
FULL_MAX = 3000
# A chunk's estimate: a new test's with nothing measured, and a chunk's servers' harness runs.
DEFAULT_MS = 30_000
WARM_MS = 120_000
# A new test is estimated by its deepest directory (of at most DIR_DEPTH) with DIR_MIN measured tests.
DIR_DEPTH = 3
DIR_MIN = 5
# A test's wall-clock limit (s): a pending run's (over it, a test is recorded `timeout`), a full run's.
PENDING_TIMEOUT = 120
# An invocation's budget (the box's rule: no job much over 10 minutes).
MINUTES = 10.0
# A run over this times its estimate warns, with its measured rate.
OVERRUN = 1.5
# A stopped runner's time (s) to kill its children and end, after SIGTERM, before SIGKILL.
GRACE = 10.0
FULL_TIMEOUT = 600
# The quiet re-run's jobs: a run's wall-clock timeouts again at the same limit, few at once (a run's own load is most of
# the contention that times a test out).
RETRY_JOBS = 3
# A job's resident memory cap, MB (over it, the test is `timeout`, `rss cap`): a few jobs at 2 GB each leave a 36 GB
# machine that is also building room to work; raise it with --rss-cap-mb on a larger one.
RSS_CAP_MB = 2048
# A server's harness run's limit: WARM_FACTOR times a test's, at most WARM_CAP s (the runner's default; over it, every
# test of that harness in the run is `timeout`, so that a chunk ends within that limit of its last row).
WARM_FACTOR = 2
WARM_CAP = 600
# The features whose tests no executor answers within a run's limit, each with the reason: parked as limits (not run
# without `--limits`), the reason on the board and in the expected files (`# limit <test>: <reason>`).
LIMITS = {"tail-call-optimization": "executor depth (execution-resources)"}
# The limits excluded from execution, by reason: not run, `--limits` included; outside the census's `tests` and rates,
# listed apart.
BUILDSTRING = "harness buildString: no JS acceleration, user 2026-10-21"
EXCLUDED = {BUILDSTRING}
# The same by path (a test, or a directory ending in `/`; the longest match decides, None: not a limit, whatever its
# features), each with its cause (`workload`: the test's own computation; `warm-up`: its harness run).
LIMIT_PATHS = {
    "built-ins/Proxy/revocable/tco-fn-realm.js": None,
    "built-ins/RegExp/property-escapes/generated/": BUILDSTRING,
    "built-ins/RegExp/property-escapes/generated/strings/": None,
    **{f"built-ins/RegExp/CharacterClassEscapes/character-class-{c}-class-escape-{s}-cases.js": BUILDSTRING
       for c, s in [("digit", "negative"), ("non-digit", "positive"),
                    ("non-whitespace", "positive"), ("non-word", "positive"),
                    ("whitespace", "negative"), ("word", "negative")]},
    "harness/nativeFunctionMatcher.js": "warm-up: nativeFunctionMatcher.js's harness run takes over 80 s",
    **{f"built-ins/Function/prototype/toString/{t}.js":
       "workload: validateNativeFunctionSource's regex literals, parsed and compiled at each evaluation"
       for t in ["bound-function", "built-in-function-object", "proxy-arrow-function", "proxy-async-function",
                 "proxy-async-generator-function", "proxy-async-generator-method-definition",
                 "proxy-async-method-definition", "proxy-bound-function", "proxy-class", "proxy-function-expression",
                 "proxy-generator-function", "proxy-method-definition", "symbol-named-builtins"]},
}
LIMIT_RE = re.compile(r"^# limit (\S+): (.*)$")


# --- the sample -------------------------------------------------------------------------------------------


def frontmatter(text: str) -> dict[str, list[str]]:
    """The lists `flags`, `features` and `includes` of a test's frontmatter (inline or block lists)."""
    m = re.search(r"/\*---(.*?)---\*/", text, re.S)
    out: dict[str, list[str]] = {"flags": [], "features": [], "includes": []}
    if not m:
        return out
    key = None
    for line in re.split(r"\r\n|\r|\n", m.group(1)):
        k = re.match(r"^(\w+):\s*(.*)$", line)
        if k:
            key = k.group(1) if k.group(1) in out else None
            v = k.group(2).strip()
            if key and v.startswith("["):
                out[key] += [x.strip() for x in v.strip("[]").split(",") if x.strip()]
                key = None
        elif key and line.strip().startswith("- "):
            out[key].append(line.strip()[2:].strip())
    return out


def conf_section(path: Path, name: str) -> list[str]:
    lines, cur = [], None
    for raw in path.read_text().splitlines():
        line = raw.split("#")[0].strip()
        if line.startswith("[") and line.endswith("]"):
            cur = line[1:-1]
        elif line and cur == name:
            lines.append(line)
    return lines


def candidates(test_dir: Path, skip_features: set[str]) -> list[str]:
    """The tests under TOP the full stage would run (no skipped feature), as paths under test/."""
    out = []
    for top in TOP:
        for p in sorted((test_dir / top).rglob("*.js")):
            rel = p.relative_to(test_dir).as_posix()
            if "_FIXTURE" in rel or any(rel.startswith(x + "/") for x in EXCLUDE):
                continue
            if skip_features & set(frontmatter(p.read_text(errors="replace"))["features"]):
                continue
            out.append(rel)
    return out


def stratum(test: str) -> str:
    """The test's stratum: its first two directories (`built-ins/Array`, `language/expressions`)."""
    return "/".join(test.split("/")[:-1][:2])


def stratified(tests: list[str], size: int, seed: int) -> list[str]:
    """About `size` tests: from each stratum its share by size, at least two (or all it has), drawn by `seed`."""
    groups: dict[str, list[str]] = defaultdict(list)
    for t in tests:
        groups[stratum(t)].append(t)
    rng = random.Random(seed)
    out = []
    for name in sorted(groups):
        g = sorted(groups[name])
        n = min(len(g), max(2, round(size * len(g) / len(tests))))
        out += rng.sample(g, n)
    return sorted(out)


def cmd_sample(args) -> int:
    conf = ROOT / "tests/test262/sample.conf"
    if conf.exists() and len(conf_batches(conf)) > 1 and not args.force:
        raise SystemExit(f"{conf.relative_to(ROOT)} has batches from `expand`: a new sample drops them (--force)")
    test_dir = test262_dir(args) / "test"
    full = ROOT / "tests/test262/full.conf"
    skip = set(conf_section(full, "skip-features"))
    tests = stratified(candidates(test_dir, skip), args.size, args.seed)
    strata = Counter(stratum(t) for t in tests)
    head = f"""# test262 on ecma-run: a stratified sample. Generated; do not edit:
#   python3 scripts/test262.py sample --seed {args.seed} --size {args.size}
# {len(tests)} tests from {len(strata)} strata (the first two directories under {', '.join(TOP)}; not
# {', '.join(EXCLUDE)}): each stratum's share by size, at least two; the features full.conf skips left out.
"""
    web = conf_section(ROOT / "tests/test262/suite.conf", "web-browser-paths")
    body = ["[paths]", *tests, "", "[web-browser-paths]", *web, "", "[features]", "*", "", "[skip-features]", *sorted(skip)]
    conf.write_text(head + "\n" + "\n".join(body) + "\n")
    print(f"wrote tests/test262/sample.conf: {len(tests)} tests, {len(strata)} strata")
    return 0


# --- expanding the sample ---------------------------------------------------------------------------------


BATCH_RE = re.compile(r"^# batch (\d+): (\S+), seed (-?\d+), (\d+) tests, runnable sampled (\d+) of (\d+)")


def conf_batches(path: Path) -> list[tuple[str, list[str]]]:
    """The conf's [paths] by batch: ("sample", the tests before any batch line), then ("batch K: ...", its tests)."""
    out: list[tuple[str, list[str]]] = [("sample", [])]
    cur = None
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if line.startswith("[") and line.endswith("]"):
            cur = line[1:-1]
        elif cur == "paths" and BATCH_RE.match(line):
            out.append((line[2:], []))
        elif cur == "paths" and line.split("#")[0].strip():
            out[-1][1].append(line.split("#")[0].strip())
    return out


def conf_coverage(path: Path) -> tuple[int, int] | None:
    """(runnable sampled, runnable in test262) as the conf's last batch line records them; None before any batch."""
    ms = [m for b, _ in conf_batches(path)[1:] if (m := BATCH_RE.match("# " + b))]
    return (int(ms[-1].group(5)), int(ms[-1].group(6))) if ms else None


# The `$262` members the test host has; `$262` itself is the empty one (run.rs's HOST_MEMBERS).
HOST_MEMBERS = {"", "global", "detachArrayBuffer", "createRealm", "evalScript", "agent", "IsHTMLDDA"}


def host_hook(text: str) -> str | None:
    """The first `$262` member `text` uses that the test host lacks (`$262.agent`; run.rs's host_hook)."""
    for at in re.finditer(re.escape("$262"), text):
        m = re.match(r"\.(\w+)", text[at.end() :])
        member = m.group(1) if m else ""
        if member not in HOST_MEMBERS:
            return f"$262.{member}"
    return None


# The `$262` members of the test262 host interface that the test host lacks (run.rs's HOST_LACKS).
HOST_LACKS = {"gc", "AbstractModuleSource"}


def realm_hook(text: str) -> str | None:
    """The first lacking member `text` uses through a created realm's `$262` (`other.agent`; run.rs's realm_hook)."""
    return next((f"$262.{m.group(1)}" for m in re.finditer(r"\.(\w+)", text) if m.group(1) in HOST_LACKS), None)


def unsupported_reason(test: str, fm: dict[str, list[str]], source: str, harness) -> str | None:
    """Why ecma-run's test host cannot run `test` (run.rs's unsupported_reason); `harness` gives an include's text."""
    texts = [source] + [h for i in fm["includes"] if (h := harness(i)) is not None]
    if hook := next((h for t in texts if (h := host_hook(t))), None):
        return hook
    if any("$262.createRealm" in t for t in texts):
        return next((h for t in texts if (h := realm_hook(t))), None)
    return None


def limit_reason(fm: dict[str, list[str]]) -> str | None:
    """Why a test of frontmatter `fm` is parked as a limit (its first feature in LIMITS), None if it is not."""
    return next((LIMITS[f] for f in fm["features"] if f in LIMITS), None)


def path_entry(test: str) -> str | None:
    """LIMIT_PATHS' longest key matching `test`, None if none does."""
    hits = [p for p in LIMIT_PATHS if test == p or (p.endswith("/") and test.startswith(p))]
    return max(hits, key=len) if hits else None


def path_limit(test: str) -> str | None:
    """Why `test` is parked as a limit by its path (LIMIT_PATHS' longest match), None if it is not."""
    return LIMIT_PATHS[k] if (k := path_entry(test)) else None


def excluded(limits: dict[str, str]) -> set[str]:
    """The tests of `limits` (test: reason) excluded from execution: their reason in EXCLUDED."""
    return {t for t, why in limits.items() if why in EXCLUDED}


def limits_of(test262: Path, tests: list[str]) -> dict[str, str]:
    """The tests parked as limits, each with its reason, from their path if LIMIT_PATHS lists it, else their
    frontmatter."""
    out = {}
    for t in tests:
        p = test262 / "test" / t
        if not p.is_file():
            continue
        why = path_limit(t) if path_entry(t) else limit_reason(frontmatter(p.read_text(errors="replace")))
        if why:
            out[t] = why
    return out


def includes_of(test262: Path):
    """An include's text from test262/harness (None: no such file), each read once."""
    cache: dict[str, str | None] = {}

    def get(name: str) -> str | None:
        if name not in cache:
            p = test262 / "harness" / name
            cache[name] = p.read_text(errors="replace") if p.is_file() else None
        return cache[name]
    return get


def predicted_unsupported(test262: Path, tests: list[str]) -> set[str]:
    """The tests the runner will find unsupported, from their frontmatter and source."""
    harness, out = includes_of(test262), set()
    for t in tests:
        p = test262 / "test" / t
        src = p.read_text(errors="replace") if p.is_file() else ""
        if unsupported_reason(t, frontmatter(src), src, harness):
            out.add(t)
    return out


def suite(test262: Path, skip_features: set[str]) -> dict[str, str | None]:
    """suite's tests (TOP less EXCLUDE, no skipped feature), each with why ecma-run cannot run it (None: runnable)."""
    test_dir, harness, out = test262 / "test", includes_of(test262), {}
    for top in TOP:
        for p in sorted((test_dir / top).rglob("*.js")):
            rel = p.relative_to(test_dir).as_posix()
            if "_FIXTURE" in rel or any(rel.startswith(x + "/") for x in EXCLUDE):
                continue
            src = p.read_text(errors="replace")
            fm = frontmatter(src)
            if skip_features & set(fm["features"]):
                continue
            out[rel] = unsupported_reason(rel, fm, src, harness)
    return out


def allocate(sizes: dict[str, int], n: int) -> dict[str, int]:
    """`n` tests split across strata by their share of `sizes`: at least one where any remain, at most all it has."""
    live = sorted(s for s, k in sizes.items() if k)
    total = sum(sizes[s] for s in live)
    n = min(n, total)
    if n < len(live):
        return {s: 1 for s in sorted(live, key=lambda s: (-sizes[s], s))[:n]}
    fixed: dict[str, int] = {}
    while True:
        rest = [s for s in live if s not in fixed]
        budget, left = n - sum(fixed.values()), sum(sizes[s] for s in rest)
        quota = {s: budget * sizes[s] / left for s in rest} | fixed
        small = [s for s in rest if quota[s] < 1]
        if not small:
            break
        fixed |= {s: 1 for s in small}
    out = {s: min(sizes[s], max(1, math.floor(quota[s]))) for s in live}
    while sum(out.values()) < n:
        out[min((s for s in live if out[s] < sizes[s]), key=lambda s: (out[s] - quota[s], s))] += 1
    while sum(out.values()) > n:
        out[min((s for s in live if out[s] > 1), key=lambda s: (quota[s] - out[s], s))] -= 1
    return out


def expansion(cands: dict[str, str | None], sampled: list[str], n: int, seed: int) -> list[str]:
    """`n` runnable candidates not in `sampled`, stratified by their share of the runnable ones remaining, drawn by `seed`."""
    groups: dict[str, list[str]] = defaultdict(list)
    have = set(sampled)
    for t in sorted(t for t, why in cands.items() if why is None and t not in have):
        groups[stratum(t)].append(t)
    rng = random.Random(seed)
    out = []
    for name, k in sorted(allocate({s: len(g) for s, g in groups.items()}, n).items()):
        out += rng.sample(groups[name], k)
    return sorted(out)


def batch_line(k: int, date: str, seed: int, n: int, sampled: int, total: int) -> str:
    return f"# batch {k}: {date}, seed {seed}, {n} tests, runnable sampled {sampled} of {total}"


def append_batch(conf: Path, head: str, tests: list[str]) -> None:
    """Append `tests` to the conf's [paths] under the batch line `head`."""
    lines = conf.read_text().splitlines()
    start = lines.index("[paths]")
    end = next((i for i in range(start + 1, len(lines)) if lines[i].strip().startswith("[")), len(lines))
    while end > start + 1 and not lines[end - 1].strip():
        end -= 1
    conf.write_text("\n".join(lines[:end] + [head, *tests] + lines[end:]) + "\n")


def coverage(cands: dict[str, str | None], sampled: list[str]) -> list[tuple[str, int, int, int, int]]:
    """(top directory, runnable sampled, runnable, unsupported sampled, unsupported) per TOP directory, then the total."""
    have = set(sampled)
    rows = []
    for top in TOP:
        run = [t for t, why in cands.items() if t.startswith(top + "/") and why is None]
        uns = [t for t, why in cands.items() if t.startswith(top + "/") and why is not None]
        rows.append((top, sum(t in have for t in run), len(run), sum(t in have for t in uns), len(uns)))
    return rows + [("total", *(sum(r[i] for r in rows) for i in range(1, 5)))]


def mispredicted(expected_dir: Path, cands: dict[str, str | None]) -> list[tuple[str, tuple[str, str, str | None]]]:
    """The expected files' tests whose recorded `unsupported` (or not) the prediction contradicts."""
    out = []
    for m in MODES:
        if (expected_dir / f"{m}.txt").exists():
            out += [(m, (t, b, cands[t])) for t, b in sorted(read_expected(expected_dir / f"{m}.txt").items())
                    if t in cands and (b == "unsupported") != (cands[t] is not None)]
    return out


def stage_conf(args) -> Path:
    if args.stage in SCHEDULED:
        raise SystemExit(f"{args.stage} is the whole suite: it has nothing to expand")
    return ROOT / "tests/test262" / f"{args.stage}.conf"


def full_suite(args) -> dict[str, str | None]:
    """suite's tests, its skipped features left out, each with why ecma-run cannot run it (None: runnable)."""
    full = ROOT / "tests/test262/suite.conf"
    return suite(test262_dir(args), set(conf_section(full, "skip-features")))


def pct_of(n: int, total: int) -> str:
    return f"{100 * n / total:.1f}" if total else "-"


def cmd_expand(args) -> int:
    conf = stage_conf(args)
    batches = conf_batches(conf)
    sampled = [t for _, ts in batches for t in ts]
    cands = full_suite(args)
    if args.status:
        print(f"{args.stage}: {len(batches) - 1} batch(es) after the sample")
        for name, ts in batches:
            print(f"  {name}: {len(ts)} tests" if name == "sample" else f"  {name}")
        print("\n| directory | runnable sampled | runnable | % | unsupported sampled | unsupported |")
        print("|---|---:|---:|---:|---:|---:|")
        for top, n, total, un, utotal in coverage(cands, sampled):
            print(f"| {top} | {n} | {total} | {pct_of(n, total)} | {un} | {utotal} |")
        print("\n(unsupported: what ecma-run's test host lacks, predicted from the frontmatter as the runner does)")
        held = parked_per_mode(ROOT / "tests/expected" / args.stage, sampled)
        if held:
            print("parked timeouts (not re-run without --timeouts): " + ", ".join(f"{m} {n}" for m, n in held.items()))
        lims = limits_per_mode(ROOT / "tests/expected" / args.stage, sampled)
        if lims:
            print("parked limits (not run without --limits): " + ", ".join(f"{m} {len(n) - len(excluded(n))}"
                                                                            for m, n in lims.items()))
        if any(excluded(n) for n in lims.values()):
            print("excluded limits (not run): " + ", ".join(f"{m} {len(excluded(n))}" for m, n in lims.items()))
        for m, (t, b, why) in mispredicted(ROOT / "tests/expected" / args.stage, cands):
            print(f"{m}: {t} recorded {b}, predicted {why or 'runnable'} (unsupported_reason no longer mirrors the runner's)")
        outside = len(set(sampled) - set(cands))
        if outside:
            print(f"{outside} sampled test(s) are no longer candidates (a skipped feature, or gone from test262)")
        return 0
    add_batch(args, conf, batches, cands)
    return 0


def add_batch(args, conf: Path, batches: list[tuple[str, list[str]]], cands: dict[str, str | None]) -> list[str]:
    """Append a batch of `args.batch` runnable tests never sampled to `conf`; return them."""
    sampled = [t for _, ts in batches for t in ts]
    seed = args.seed if args.seed is not None else SEED + len(batches)
    tests = expansion(cands, sampled, args.batch, seed)
    if not tests:
        print(f"{args.stage}: every runnable test is sampled: nothing to add")
        return []
    done = sum(cands[t] is None for t in set(sampled) | set(tests) if t in cands)
    head = batch_line(len(batches), datetime.date.today().isoformat(), seed, len(tests), done,
                      sum(why is None for why in cands.values()))
    append_batch(conf, head, tests)
    print(f"{conf.relative_to(ROOT)}: {head[2:]} ({len(Counter(stratum(t) for t in tests))} strata); "
          "its tests are new, so pending for the next run")
    return tests


# --- running ----------------------------------------------------------------------------------------------


def sh(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    print("+", " ".join(cmd), file=sys.stderr)
    return subprocess.run(cmd, cwd=ROOT, **kw)


def test262_dir(args) -> Path:
    """The pinned checkout: --test262, else external/test262."""
    d = Path(getattr(args, "test262", None) or ROOT / "external/test262")
    if not (d / "test").is_dir():
        raise SystemExit(f"{d}/test not found (git submodule update --init --depth 1 external/test262)")
    args.test262 = str(d.resolve())
    return Path(args.test262)


def out_dir(args) -> Path:
    d = Path(args.out or Path(os.environ.get("TMPDIR", "/tmp")) / "test262") / args.stage
    d.mkdir(parents=True, exist_ok=True)
    return d


def default_jobs() -> int:
    """The runner's default: $TEST262_JOBS, else half the CPUs."""
    v = os.environ.get("TEST262_JOBS", "")
    return max(1, int(v) if v.isdigit() else (os.cpu_count() or 8) // 2)


def limit_args(timeout: int) -> list[str]:
    """The runner's limits for a test's limit `timeout` (s): the test's and its server's harness run's."""
    return ["--timeout", str(timeout), "--warm-timeout", str(min(WARM_FACTOR * timeout, WARM_CAP))]


def stage_tests(test262: Path, conf: Path) -> list[str]:
    """The stage's tests as the runner collects them: its [paths] less [exclude] (skipped ones included)."""
    root = test262 / "test"
    exclude = [x.rstrip("/") for x in conf_section(conf, "exclude")]
    out = set()
    for p in conf_section(conf, "paths"):
        full = root / p
        if full.is_file():
            out.add(p)
        elif full.is_dir():
            out.update(q.relative_to(root).as_posix() for q in full.rglob("*.js"))
        else:
            raise SystemExit(f"{conf}: {full}: no such test file or directory")
    return sorted(t for t in out if t.endswith(".js") and "_FIXTURE" not in t
                  and not any(t == x or t.startswith(x + "/") for x in exclude))


def pending(tests: list[str], expected: dict[str, str], timeouts: bool = False, limits=()) -> list[str]:
    """The tests not known good: `stop`, `fail`, `unsupported` or not listed (new); the TIMEOUTS (parked) with
    `timeouts`; never those in `limits` (parked limits)."""
    held = {"pass"} if timeouts else {"pass", *TIMEOUTS}
    return [t for t in tests if t not in limits and expected.get(t) not in held]


def parked(tests: list[str], expected: dict[str, str], limits=()) -> int:
    """The tests recorded `timeout` or `timeout(fuel)`, not in `limits`: not re-run without --timeouts."""
    return sum(expected.get(t) in TIMEOUTS and t not in limits for t in tests)


def parked_per_mode(expected_dir: Path, tests: list[str] | None) -> dict[str, int]:
    """Each mode's parked timeouts among `tests` (None: every test it lists; its limits left out), per its expected
    file (modes with none left out)."""
    files = {m: expected_dir / f"{m}.txt" for m in MODES}
    held = {m: parked(list(e) if tests is None else tests, e, read_limits(p))
            for m, p in files.items() if p.exists() for e in [read_expected(p)]}
    return {m: n for m, n in held.items() if n}


def limits_per_mode(expected_dir: Path, tests: list[str] | None) -> dict[str, dict[str, str]]:
    """Each mode's parked limits among `tests` (None: all) with their reasons, per its expected file (modes with none
    left out)."""
    files = {m: expected_dir / f"{m}.txt" for m in MODES}
    held = {m: {t: why for t, why in read_limits(p).items() if tests is None or t in tests}
            for m, p in files.items() if p.exists()}
    return {m: d for m, d in held.items() if d}


def tests_of(args, tests: list[str]) -> list[str]:
    """The stage's tests, only those another mode's expected file lists with `--tests-of MODE` (as `--bucket B`), and
    those `--tests-from FILE` lists."""
    if getattr(args, "tests_from", None):
        listed = {t.strip() for t in Path(args.tests_from).read_text().splitlines() if t.strip() and not t.startswith("#")}
        tests = [t for t in tests if t in listed]
    if not getattr(args, "tests_of", None):
        if getattr(args, "bucket", None):
            raise SystemExit("--bucket needs --tests-of MODE")
        return tests
    listed = read_expected(ROOT / "tests/expected" / args.stage / f"{args.tests_of}.txt")
    return [t for t in tests if t in listed and getattr(args, "bucket", None) in (None, listed[t])]


def selection(tests: list[str], expected: dict[str, str], full: bool, timeouts: bool = False, limits=(),
              only_limits: bool = False) -> list[str]:
    """A run's tests: the parked limits alone but the excluded ones (`--limits`), else every test of the stage but the
    limits (`--full`), else the pending ones."""
    if only_limits:
        return [t for t in tests if t in limits and limits[t] not in EXCLUDED]
    return [t for t in tests if t not in limits] if full else pending(tests, expected, timeouts, limits)


def parse_chunk(v: str) -> tuple[int, int]:
    i, _, m = v.partition("/")
    if not (i.isdigit() and m.isdigit() and int(i) < int(m)):
        raise argparse.ArgumentTypeError(f"{v}: expected I/M with 0 <= I < M")
    return int(i), int(m)


def chunk_of(test: str, m: int) -> int:
    """The test's chunk of `m`: by its path alone, whatever else is pending."""
    return zlib.crc32(test.encode()) % m


def estimates(tests: list[str], times: dict[str, int | None], cap_ms: int | None = None,
              zero: set[str] = frozenset(), costs: dict[str, int] | None = None) -> dict[str, int]:
    """Each test's milliseconds: 0 in `zero` (unsupported), else recorded (a skip's or unsupported's 0), else (none or
    `-`) new_estimate's from `costs` (default: the recorded times); at most `cap_ms`."""
    new = new_estimate({t: ms for t, ms in times.items() if ms} if costs is None else costs)
    est = {t: 0 if t in zero else new(t) if times.get(t) is None else times[t] for t in tests}
    return {t: min(ms, cap_ms) for t, ms in est.items()} if cap_ms else est


def new_estimate(costs: dict[str, int]):
    """A new test's milliseconds: the median cost of its deepest directory (at most DIR_DEPTH down) with DIR_MIN measured
    tests, else of all, else (nothing measured) DEFAULT_MS."""
    by_dir: dict[str, list[int]] = defaultdict(list)
    for t, ms in costs.items():
        dirs = t.split("/")[:-1]
        for k in range(1, min(DIR_DEPTH, len(dirs)) + 1):
            by_dir["/".join(dirs[:k])].append(ms)
    medians = {k: int(statistics.median(v)) for k, v in by_dir.items() if len(v) >= DIR_MIN}
    overall = int(statistics.median(costs.values())) if costs else DEFAULT_MS

    def est(test: str) -> int:
        dirs = test.split("/")[:-1]
        for k in range(min(DIR_DEPTH, len(dirs)), 0, -1):
            if "/".join(dirs[:k]) in medians:
                return medians["/".join(dirs[:k])]
        return overall
    return est


def cost_of(rows: list[tuple[str, str, int | None, str, int | None]]) -> dict[str, int]:
    """The rows' measured milliseconds per test: the cost, else (an older row) the jobs' ms; skips and unsupported left
    out."""
    out = {}
    for t, b, ms, _, cost in rows:
        if b not in ("skip", "unsupported") and (v := ms if cost is None else cost) is not None:
            out[t] = v
    return out


def measured(d: Path, mode: str) -> dict[str, int]:
    """The costs new tests are estimated from: the mode's latest run's (OUT/<stage>/<mode>.last.tsv), else the mode's
    results, else another mode's."""
    for p in [d / f"{mode}.last.tsv", d / f"{mode}.tsv", *(d / f"{m}.tsv" for m in MODES if m != mode)]:
        if p.exists() and (costs := cost_of(read_rows(p))):
            return costs
    return {}


def slowest_first(est: dict[str, int]) -> list[str]:
    """The runner's work queue: the slowest first, so that each starts on a server of its own and the rest fill in."""
    return sorted(est, key=lambda t: (-est[t], t))


def chunk_minutes(est: dict[str, int], m: int, jobs: int) -> float:
    """The slowest of `m` chunks' estimated minutes at `jobs` jobs (a chunk takes at least its slowest test)."""
    total, longest = [0] * m, [0] * m
    for t, ms in est.items():
        c = chunk_of(t, m)
        total[c] += ms
        longest[c] = max(longest[c], ms)
    return (max(max(s / jobs, x) for s, x in zip(total, longest)) + WARM_MS) / 60_000


def plan_chunks(est: dict[str, int], jobs: int, minutes: float) -> int:
    """The fewest chunks whose slowest takes at most `minutes`, or than the slowest test, if that is longer."""
    if not est:
        return 0
    goal = max(minutes, (max(est.values()) + WARM_MS) / 60_000)
    budget = max(goal * 60_000 - WARM_MS, 1)
    m = min(len(est), max(1, math.ceil(sum(est.values()) / jobs / budget)))
    while m < len(est) and chunk_minutes(est, m, jobs) > goal:
        m += 1
    return m


def recorded_times(d: Path, mode: str) -> dict[str, int | None]:
    """The tests' recorded milliseconds in OUT/<stage> (the cost, else the jobs' ms): the mode's results, else another
    mode's."""
    times: dict[str, int | None] = {}
    for m in [x for x in MODES if x != mode] + [mode]:
        if (d / f"{m}.tsv").exists():
            times.update({t: (0 if b in ("skip", "unsupported") else ms if c is None else c)
                          for t, b, ms, _, c in read_rows(d / f"{m}.tsv")})
    return times


@contextlib.contextmanager
def locked(d: Path):
    """An exclusive lock on the directory `d`, for concurrent runs merging into its files."""
    fd = os.open(d, os.O_RDONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        os.close(fd)


def merge_results(path: Path, rows: list[tuple]) -> None:
    """The results file with `rows` (read_rows's, or without the cost) replacing their tests' rows (the latest row per
    test)."""
    merged = {r[0]: r for r in (read_rows(path) if path.exists() else [])}
    merged.update({r[0]: r for r in rows})
    write_rows(path, sorted(merged.values()))


def write_rows(path: Path, rows: list[tuple], header: str | None = None) -> None:
    """A results file of `rows` (read_rows's, or without the cost), under `header` if any."""
    path.write_text(("" if header is None else header + "\n")
                    + "".join(f"{t}\t{b}\t{'-' if ms is None else ms}\t{d}" + ("" if c is None else f"\t{c}") + "\n"
                              for t, b, ms, d, c in ((tuple(r) + (None,))[:5] for r in rows)))


def build_line(path: Path) -> str | None:
    """A results file's `# build ...` line (the runner's build and configuration), None without one."""
    if not path.exists():
        return None
    with path.open() as f:
        first = f.readline().rstrip("\n")
    return first if first.startswith("# build ") else None


def update_last(path: Path, build: str | None, rows: list[tuple]) -> None:
    """The latest build's rows (OUT/<stage>/<mode>.last.tsv): `rows` of build `build` merge into the file's rows of the
    same build (concurrent chunks), and replace another build's."""
    same = build is not None and build_line(path) == build
    merged = {r[0]: r for r in (read_rows(path) if same else [])} | {r[0]: r for r in rows}
    write_rows(path, [merged[t] for t in sorted(merged)], build)


def check_run(args, expected_path: Path, chosen: int) -> None:
    """Refuse a run on a SCHEDULED stage that is a full run (or unbounded) and not --scheduled; a run without an expected
    file is bounded by --tests-of to `chosen` tests, at most FULL_MAX."""
    if args.stage not in SCHEDULED or args.scheduled:
        return
    if args.full:
        raise SystemExit(f"run --full on {args.stage} is a full run: the user schedules those (--scheduled)")
    if not expected_path.exists() and not (args.tests_of and chosen <= FULL_MAX):
        raise SystemExit(f"no expected file for {args.stage} (tests/expected/{args.stage}/{args.mode}.txt): every test is new, "
                         "so its chunks make a full run, which must be scheduled by the user (--scheduled), unless "
                         f"--tests-of bounds it to at most {FULL_MAX} tests")
    if not args.chunk:
        raise SystemExit(f"run on {args.stage} runs a chunk (`plan --stage {args.stage}`, then --chunk I/M) "
                         "or a scheduled run (--scheduled)")


def check_full(args, runnable: int) -> None:
    """Refuse an unscheduled --full run of more than FULL_MAX runnable tests (a grown sample's is a full run)."""
    if args.full and not args.scheduled and runnable > FULL_MAX:
        raise SystemExit(f"run --full on {args.stage} runs {runnable} runnable tests (over {FULL_MAX}): a full run, "
                         "which the user schedules (--scheduled); pending runs and chunks need none")


def cmd_run(args, rest: list[str]) -> int:
    expected_path = ROOT / "tests/expected" / args.stage / f"{args.mode}.txt"
    test262 = test262_dir(args)
    expected = read_expected(expected_path) if expected_path.exists() else {}
    tests = tests_of(args, stage_tests(test262, ROOT / "tests/test262" / f"{args.stage}.conf"))
    limits = limits_of(test262, tests)
    chosen = selection(tests, expected, args.full, args.timeouts, limits, args.limits)
    check_run(args, expected_path, len(chosen))
    if args.full and not args.scheduled:
        stage_run = [t for t in tests if t not in limits]
        check_full(args, len(stage_run) - len(unsupported_of(args, test262, stage_run, expected)))
    if args.build:
        sh(["lake", "build", "ecma-run"], check=True)
        sh(["cargo", "build", "--release", "-p", "test262-runner"], check=True)
    held = 0 if args.full or args.timeouts or args.limits else parked(tests, expected, limits)
    exc = len(excluded(limits))
    lim = 0 if args.limits else len(limits) - exc
    note = ((f", {held} parked timeouts (--timeouts)" if held else "") + (f", {lim} parked limits (--limits)" if lim else "")
            + (f", {exc} excluded limits (not run)" if exc else ""))
    print(f"{args.stage} {args.mode}: {len(chosen)} of {len(tests)} tests"
          + (f" (the parked limits{note})" if args.limits else f" ({note[2:]})" if args.full and note
             else "" if args.full else
             f" pending ({len(tests) - len(chosen) - held - lim - exc} known-good passes not re-run{note})"),
          file=sys.stderr)
    tag, scope = "run", tests
    if args.chunk:
        i, m = args.chunk
        chosen, tag = [t for t in chosen if chunk_of(t, m) == i], f"chunk-{i}-of-{m}"
        scope = [t for t in tests if chunk_of(t, m) == i]
        print(f"chunk {i}/{m}: {len(chosen)} tests", file=sys.stderr)
    # The `# limit` lines of the run's tests: each limit's reason, none for the rest.
    reasons = {t: limits.get(t) for t in scope}
    if not chosen:
        if args.update and (expected_path.exists() or limits):
            with locked(expected_path.parent):
                merge_expected(expected_path, [], expected_header(args, test262), reasons)
        return 0
    d = out_dir(args)
    timeout = args.timeout or (FULL_TIMEOUT if args.full else PENDING_TIMEOUT)
    est = estimates(chosen, recorded_times(d, args.mode), timeout * 1000, unsupported_of(args, test262, chosen, expected),
                    measured(d, args.mode))
    jobs = args.jobs or default_jobs()
    minutes = chunk_minutes(est, 1, jobs)
    print(f"about {minutes:.0f} minutes at -j {jobs}, timeout {timeout}s"
          + (f" (over {MINUTES} minutes: `plan`, then --chunk I/M)" if minutes > MINUTES else ""), file=sys.stderr)
    listing, part = d / f"{args.mode}.{tag}.tests", d / f"{args.mode}.{tag}.tsv"
    listing.write_text("".join(t + "\n" for t in slowest_first(est)))

    def runner(listing: Path, part: Path, j: int | None, compare: bool) -> list[str]:
        return [str(RUNNER), "--stage", args.stage, "--test262", str(test262),
                "--run", str(RUN), "--mode", args.mode, "--serve",
                *limit_args(timeout), "--serve-max-rss-mb", str(args.max_rss_mb), "--rss-cap-mb", str(args.rss_cap_mb),
                "--no-retry", "--stop-on-eof",
                *(["-j", str(j)] if j else []), "--tests-from", str(listing), "--results", str(part),
                *([] if compare else ["--no-compare"]), *rest]
    compare = not args.update and expected_path.exists()
    # A resumed chunk runs only the tests its part records nothing of yet.
    code = watched(runner(listing, part, args.jobs, compare), part,
                   lambda done: chunk_minutes({t: ms for t, ms in est.items() if t not in done}, 1, jobs) * 60, jobs)
    rows = latest(read_rows(part)) if part.exists() else []
    files = [part, listing]
    again = wall_clock_timeouts(rows) if code in (0, 1) and args.retry_jobs else []
    if again:
        rlisting, rpart = d / f"{args.mode}.{tag}.retry.tests", d / f"{args.mode}.{tag}.retry.tsv"
        rlisting.write_text("".join(t + "\n" for t in again))
        files += [rpart, rlisting]
        rj = min(args.retry_jobs, len(again))
        print(f"quiet re-run: the {len(again)} wall-clock timeout(s) again at -j {rj}, timeout {timeout}s", file=sys.stderr)
        rcode = watched(runner(rlisting, rpart, rj, False), rpart,
                        lambda done: chunk_minutes({t: timeout * 1000 for t in again if t not in done}, 1, rj) * 60, rj)
        second = latest(read_rows(rpart)) if rpart.exists() else []
        rows = replaced(rows, second)
        print(retry_note(second), file=sys.stderr)
        if rcode != 0:
            code = rcode
        elif code == 1 and compare and second:
            code = int(mismatched(expected, rows))
    with locked(d):
        merge_results(d / f"{args.mode}.tsv", rows)
        if rows:
            update_last(d / f"{args.mode}.last.tsv", build_line(part), rows)
    if code < 0:
        print(f"the runner was stopped (signal {-code}): {part} kept, the same command resumes", file=sys.stderr)
    else:
        for f in files:
            f.unlink(missing_ok=True)
    fails = [r for r in rows if r[1] == "fail"]
    if fails:
        print(f"\n{len(fails)} wrong answer(s) (report each to the coordinator as a finding):")
        for t, _, _, detail, _ in fails:
            print(f"  {t}  {detail}")
    if args.tests_of and args.tests_of != args.mode:
        diffs = against_expected(read_expected(expected_path.parent / f"{args.tests_of}.txt"), rows)
        if diffs:
            print(f"\n{len(diffs)} test(s) where {args.mode} differs from {args.tests_of}'s expected file (report each"
                  " as a finding unless one side timed out):")
            for t, a, b in diffs:
                print(f"  {t}  {args.tests_of} {a}, {args.mode} {b[0]} {b[1]!r}" + ("  (a limit)" if {a, b[0]} & set(TIMEOUTS) else ""))
    if args.update and code == 0:
        with locked(expected_path.parent):
            merge_expected(expected_path, [(t, b) for t, b, *_ in rows], expected_header(args, test262), reasons)
            print(f"merged {len(rows)} row(s) into {expected_path.relative_to(ROOT)}", file=sys.stderr)
            problems = ratchet(expected_path.parent, update=True)
        for p in problems:
            print("ratchet:", p)
        code = 1 if problems else 0
    return code


def latest(rows: list[tuple]) -> list[tuple]:
    """A results file's rows, the latest per test, in test order."""
    return sorted({r[0]: r for r in rows}.values())


def wall_clock_timeouts(rows: list[tuple]) -> list[str]:
    """The tests the rows record over the wall-clock limit (the test's or its harness run's), not over the rss cap: the
    quiet re-run's."""
    return sorted(t for t, b, _, detail, *_ in rows if b == "timeout" and detail.endswith("wall clock"))


def replaced(rows: list[tuple], second: list[tuple]) -> list[tuple]:
    """The run's rows with the re-run's in place of their tests'."""
    return sorted(({r[0]: r for r in rows} | {r[0]: r for r in second}).values())


def retry_note(second: list[tuple]) -> str:
    """The quiet re-run's buckets, recorded in place of the timeouts."""
    n = Counter(r[1] for r in second)
    return "quiet re-run: " + (", ".join(f"{n[b]} {b}" for b in sorted(n)) or "no row") + " (recorded in their place)"


def mismatched(expected: dict[str, str], rows: list[tuple]) -> bool:
    """The runner's comparison fails on the rows: an assertFailed, an expected pass lost, or an unexpected pass."""
    return any(b == "assertFailed" or (b != "skip" and t in expected and (expected[t] == "pass") != (b == "pass"))
               for t, b, *_ in rows)


def expected_header(args, test262: Path) -> list[str]:
    """A new expected file's header; makes its directory."""
    (ROOT / "tests/expected" / args.stage).mkdir(parents=True, exist_ok=True)
    return [f"test262 expected results on ecma-run, stage {args.stage}, mode {args.mode}.",
            f"Update: python3 scripts/test262.py run --stage {args.stage} --mode {args.mode} --update",
            f"test262 {test262_revision(test262)}",
            "<bucket> <test under external/test262/test>; skipped tests are not listed; `# limit <test>: <reason>`: "
            "a parked limit."]


def cmd_merge(args) -> int:
    """Merge results files (a run's on another machine, fetched) into OUT's results and the mode's expected file, with the stage's
    `# limit` lines; raise the floor."""
    expected_path = ROOT / "tests/expected" / args.stage / f"{args.mode}.txt"
    test262 = test262_dir(args)
    tests = stage_tests(test262, ROOT / "tests/test262" / f"{args.stage}.conf")
    limits = limits_of(test262, tests)
    d = out_dir(args)
    rows = [r for f in args.results for r in read_rows(Path(f))]
    with locked(d):
        merge_results(d / f"{args.mode}.tsv", rows)
    against = read_expected(expected_path.parent / f"{args.against}.txt") if args.against else {}
    for t, a, b in against_expected(against, rows):
        print(f"  {t}  {args.against} {a}, {args.mode} {b[0]} {b[1]!r}" + ("  (a limit)" if {a, b[0]} & set(TIMEOUTS) else ""))
    with locked(expected_path.parent):
        merge_expected(expected_path, [(t, b) for t, b, *_ in rows], expected_header(args, test262),
                       {t: limits.get(t) for t in tests})
        print(f"merged {len(rows)} row(s) into {expected_path.relative_to(ROOT)}", file=sys.stderr)
        problems = ratchet(expected_path.parent, update=True)
    for p in problems:
        print("ratchet:", p)
    return 1 if problems else 0


def overrun(elapsed_s: float, est_s: float, done: int, jobs: int) -> str:
    """The warning of a run over OVERRUN times its estimate, with the rate it has measured."""
    rate = (f"{done} tests done, {done / elapsed_s:.2f} tests/s, about {elapsed_s * jobs / done:.0f} job-seconds per "
            f"test at -j {jobs}" if done else "no test done yet")
    return (f"warning: running {elapsed_s / 60:.1f} minutes, over {OVERRUN}x its estimate of {est_s / 60:.1f}: {rate} "
            "(a stopped chunk resumes: the same command again)")


@contextlib.contextmanager
def signals_raise():
    """Within: SIGTERM and SIGHUP raise SystemExit (128 + the signal), as SIGINT raises KeyboardInterrupt."""
    def stop(sig, _frame):
        raise SystemExit(128 + sig)
    old = {sig: signal.signal(sig, stop) for sig in (signal.SIGTERM, signal.SIGHUP)}
    try:
        yield
    finally:
        for sig, handler in old.items():
            signal.signal(sig, handler)


def stop_group(proc: subprocess.Popen) -> None:
    """SIGTERM `proc`'s process group (its pid), SIGKILL it after GRACE seconds, and wait for `proc`."""
    for sig in (signal.SIGTERM, signal.SIGKILL):
        with contextlib.suppress(ProcessLookupError):
            os.killpg(proc.pid, sig)
        try:
            proc.wait(timeout=GRACE)
            return
        except subprocess.TimeoutExpired:
            pass
    proc.wait()


def part_state(part: Path) -> tuple[str | None, set[str]]:
    """A results file's build line and the tests it records."""
    return build_line(part), ({r[0] for r in read_rows(part)} if part.exists() else set())


def watched(cmd: list[str], part: Path, est_of, jobs: int) -> int:
    """Run `cmd` (the runner, appending to `part`); once over OVERRUN x its estimate, warn with the rate of `part`'s new
    rows. `est_of(done)`: the estimate (s) of the run without the tests `done`, those `part` records for the runner's
    build (a resume; assumed its own until `part`'s build line says otherwise).

    The runner runs in a session of its own with stdin a pipe from here (its --stop-on-eof lifeline); any exit from here
    before it ends (a signal, an exception) stops its group and waits for it."""
    print("+", " ".join(cmd), file=sys.stderr)
    build, resumed = part_state(part)
    est_s = est_of(resumed)
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=ROOT, stdin=subprocess.PIPE, start_new_session=True)
    try:
        with signals_raise():
            while True:
                try:
                    proc.wait(timeout=max(OVERRUN * est_s - (time.monotonic() - t0), 0.1))
                    break
                except subprocess.TimeoutExpired:
                    now, recorded = part_state(part)
                    if resumed and now is not None and now != build:  # another build: the runner resumed nothing
                        resumed, est_s = set(), est_of(set())
                        continue
                    print(overrun(time.monotonic() - t0, est_s, len(recorded - resumed), jobs), file=sys.stderr)
                    proc.wait()
                    break
    finally:
        if proc.poll() is None:
            stop_group(proc)
        proc.stdin.close()
    print(f"took {(time.monotonic() - t0) / 60:.1f} minutes (estimate {est_s / 60:.1f})", file=sys.stderr)
    return proc.returncode


def merge_expected(path: Path, rows: list[tuple[str, str]], header: list[str],
                   limits: dict[str, str | None] | None = None) -> None:
    """The expected file with the re-run `rows` replacing their tests' (a skip's dropped), the rest unchanged; `limits`
    sets (a reason) or drops (None) its tests' `# limit` lines, written after their rows, the others kept.

    An existing file keeps its header; a new one gets `header`."""
    text = path.read_text() if path.exists() else ""
    head = [line for line in text.splitlines() if line.startswith("#") and not LIMIT_RE.match(line)] \
        or [f"# {h}" for h in header]
    res = read_expected(path) if path.exists() else {}
    notes = read_limits(path)
    for t, b in rows:
        if b == "skip":
            res.pop(t, None)
        else:
            res[t] = b
    for t, why in (limits or {}).items():
        if why is None:
            notes.pop(t, None)
        else:
            notes[t] = why
    path.write_text("".join(h + "\n" for h in head)
                    + "".join((f"{res[t]} {t}\n" if t in res else "") + (f"# limit {t}: {notes[t]}\n" if t in notes else "")
                              for t in sorted(set(res) | set(notes))))


def test262_revision(test262: Path) -> str:
    """The checkout's commit, else the submodule's pin."""
    for cmd in (["git", "-C", str(test262), "rev-parse", "HEAD"], ["git", "-C", str(ROOT), "ls-tree", "HEAD", "external/test262"]):
        try:
            out = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
        except FileNotFoundError:
            return "(unknown revision)"
        if out.returncode == 0 and (rev := out.stdout.split("\t")[0].split()[-1:]):
            return rev[0]
    return "(unknown revision)"


def unsupported_of(args, test262: Path, chosen: list[str], expected: dict[str, str]) -> set[str]:
    """The selection's unsupported tests (about 0 ms): recorded so, or predicted for the rest."""
    rest = [t for t in chosen if expected.get(t) != "unsupported"]
    return {t for t in chosen if expected.get(t) == "unsupported"} | predicted_unsupported(test262, rest)


def chunked(chosen: list[str], m: int) -> list[list[str]]:
    """The selection's `m` chunks, as `run --chunk I/m` takes them."""
    out: list[list[str]] = [[] for _ in range(m)]
    for t in chosen:
        out[chunk_of(t, m)].append(t)
    return out


def stage_plan(args) -> tuple[list[str], list[str], dict[str, str], dict[str, int], int]:
    """The stage's tests, its pending ones, the expected file, their estimates and the chunks they make."""
    expected_path = ROOT / "tests/expected" / args.stage / f"{args.mode}.txt"
    expected = read_expected(expected_path) if expected_path.exists() else {}
    test262 = test262_dir(args)
    tests = tests_of(args, stage_tests(test262, ROOT / "tests/test262" / f"{args.stage}.conf"))
    limits = limits_of(test262, tests)
    chosen = selection(tests, expected, False, args.timeouts, limits, args.limits)
    d = out_dir(args)
    est = estimates(chosen, recorded_times(d, args.mode), args.timeout * 1000,
                    unsupported_of(args, test262, chosen, expected), measured(d, args.mode))
    return tests, chosen, expected, est, plan_chunks(est, args.jobs, args.minutes), limits


def held_note(args, tests: list[str], expected: dict[str, str], limits: dict[str, str]) -> list[tuple[str, str]]:
    """What a plan leaves out, each with the flag that adds it: the parked timeouts, the parked limits and the excluded
    ones (no flag)."""
    held = 0 if args.timeouts or args.limits else parked(tests, expected, limits)
    exc = len(excluded(limits))
    lim = 0 if args.limits else len(limits) - exc
    return (([(f"{held} parked timeouts", "--timeouts")] if held else []) + ([(f"{lim} parked limits", "--limits")] if lim else [])
            + ([(f"{exc} excluded limits", "not run")] if exc else []))


def chunk_command(args, i: int, m: int, update: bool = False) -> str:
    return (f"python3 scripts/test262.py run --stage {args.stage} --mode {args.mode} -j {args.jobs} "
            f"--timeout {args.timeout}{' --timeouts' if args.timeouts else ''}{' --limits' if args.limits else ''}"
            f"{f' --tests-of {args.tests_of}' if args.tests_of else ''}{f' --bucket {args.bucket}' if args.bucket else ''} --chunk {i}/{m}{' --update' if update else ''}")


def unrun_batch(batches: list[tuple[str, list[str]]], expected: dict[str, str]) -> str | None:
    """The last batch's line if none of its tests has a row yet (its round not run), else None."""
    if len(batches) > 1 and batches[-1][1] and not any(t in expected for t in batches[-1][1]):
        return batches[-1][0]
    return None


def cmd_round(args) -> int:
    conf = stage_conf(args)
    batches = conf_batches(conf)
    if args.batch and not args.force:
        expected_path = ROOT / "tests/expected" / args.stage / f"{args.mode}.txt"
        last = unrun_batch(batches, read_expected(expected_path) if expected_path.exists() else {})
        if last:
            raise SystemExit(f"{conf.relative_to(ROOT)}: the last batch ({last}) has no {args.mode} row yet: "
                             "run its chunks (`round --batch 0`), or revert it, before adding another (--force)")
    added = add_batch(args, conf, batches, full_suite(args)) if args.batch else []
    tests, chosen, expected, est, m, limits = stage_plan(args)
    held = "".join(", " + h for h, _ in held_note(args, tests, expected, limits))
    print(f"{args.stage} {args.mode}: {len(chosen)} pending of {len(tests)} tests ({len(added)} new in this batch"
          f"{held}), about {sum(est.values()) / args.jobs / 60_000:.0f} minutes at -j {args.jobs}")
    if not m:
        return 0
    if added:
        print(f"commit {conf.relative_to(ROOT)} first: the chunks run the sample with this batch")
    print(f"{m} chunk(s) of about {args.minutes:.0f} minutes, each its own command (they may run concurrently):")
    for i, part in enumerate(chunked(chosen, m)):
        mins = chunk_minutes({t: est[t] for t in part}, 1, args.jobs)
        print(f"  {chunk_command(args, i, m, args.update)}   # {len(part)} tests, about {mins:.0f} minutes")
    return 0


def cmd_plan(args) -> int:
    tests, chosen, expected, est, m, limits = stage_plan(args)
    held = ", ".join(f"{h}: {flag}" for h, flag in held_note(args, tests, expected, limits))
    print(f"{args.stage} {args.mode}: {len(chosen)} pending of {len(tests)} tests"
          f"{f' ({held})' if held else ''}, about "
          f"{sum(est.values()) / args.jobs / 60_000:.0f} minutes at -j {args.jobs}")
    if m:
        print(f"{m} chunk(s), the slowest about {chunk_minutes(est, m, args.jobs):.0f} minutes; each one of:")
        print(f"  {chunk_command(args, 0, m).replace(f'--chunk 0/{m}', f'--chunk I/{m}')}   # I = 0..{m - 1}")
    return 0


# --- results and the ratchet ------------------------------------------------------------------------------


def read_rows(path: Path) -> list[tuple[str, str, int | None, str, int | None]]:
    """The runner's `--results`: (test, bucket, ms, detail, cost ms), a time None where there is none; `#` lines are
    comments, and a torn last line (a run stopped mid-write) is left out."""
    out = []
    text = path.read_text()
    for line in text.splitlines()[: None if text.endswith("\n") else -1]:
        if not line or line.startswith("#"):
            continue
        t, b, ms, d, c = (line.split("\t") + ["", "", "", ""])[:5]
        out.append((t, b, None if ms in ("", "-") else int(ms), d, None if c in ("", "-") else int(c)))
    return out


def read_results(path: Path) -> list[tuple[str, str, int | None, str]]:
    """The runner's `--results`: (test, bucket, ms or None, detail)."""
    return [r[:4] for r in read_rows(path)]


def read_expected(path: Path) -> dict[str, str]:
    out = {}
    for line in path.read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            b, t = line.split(" ", 1)
            out[t.strip()] = b
    return out


def read_limits(path: Path) -> dict[str, str]:
    """An expected file's parked limits: `# limit <test>: <reason>` lines (none without the file)."""
    if not path.exists():
        return {}
    return {m.group(1): m.group(2) for line in path.read_text().splitlines() if (m := LIMIT_RE.match(line))}


def read_floor(path: Path) -> tuple[dict[str, int], dict[str, set[str]]]:
    """floor.txt: `<mode> passes N` and `<mode> pass <test>` lines."""
    covered: dict[str, int] = {}
    passes: dict[str, set[str]] = defaultdict(set)
    if path.exists():
        for line in path.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            mode, kind, value = line.split(" ", 2)
            if kind == "passes":
                covered[mode] = int(value)
            elif kind == "pass":
                passes[mode].add(value.strip())
    return covered, passes


def ratchet(expected_dir: Path, update: bool = False) -> list[str]:
    """The ratchet's problems (none: it holds); with `update`, when it holds, the floor raised to the files."""
    files = {m: read_expected(expected_dir / f"{m}.txt") for m in MODES if (expected_dir / f"{m}.txt").exists()}
    floor_path = expected_dir / "floor.txt"
    covered, passes = read_floor(floor_path)
    problems = []
    for mode in sorted(set(covered) | set(passes)):
        if mode not in files:
            problems.append(f"{mode}: the floor names it, but {mode}.txt is missing")
    for mode, res in files.items():
        lost = sorted(t for t in passes.get(mode, ()) if res.get(t) != "pass")
        for t in lost:
            problems.append(f"{mode}: {t} passed at the floor, now {res.get(t, 'not listed')}")
        for t in sorted(t for t, b in res.items() if b == "fail"):
            problems.append(f"{mode}: {t} is a wrong answer (fail): fix it; the expected files record none")
        cov = sum(1 for b in res.values() if b == "pass")
        if cov < covered.get(mode, 0):
            problems.append(f"{mode}: {cov} tests pass, fewer than the floor's {covered[mode]}")
    for a in files:
        for b in files:
            if a < b:
                for t in sorted(set(files[a]) & set(files[b])):
                    if {files[a][t], files[b][t]} == {"pass", "fail"}:
                        problems.append(f"{t}: {files[a][t]} in {a}, {files[b][t]} in {b} (the engines disagree)")
    if update and not problems:
        lines = [f"# The ratchet's floor of {expected_dir.name}'s expected files (scripts/test262.py ratchet).",
                 "# Written by `test262.py run --update` when the ratchet holds; it only rises."]
        for mode, res in sorted(files.items()):
            cov = sum(1 for b in res.values() if b == "pass")
            lines.append(f"{mode} passes {max(cov, covered.get(mode, 0))}")
            lines += [f"{mode} pass {t}" for t in sorted(t for t, b in res.items() if b == "pass")]
        floor_path.write_text("\n".join(lines) + "\n")
    return problems


def cmd_ratchet(args) -> int:
    d = Path(args.dir) if args.dir else ROOT / "tests/expected" / args.stage
    problems = ratchet(d, update=args.update)
    for p in problems:
        print(p)
    files = [m for m in MODES if (d / f"{m}.txt").exists()]
    print(f"ratchet {d.name}: {len(files)} mode(s), {'ok' if not problems else f'{len(problems)} problem(s)'}")
    return 1 if problems else 0


# --- the census -------------------------------------------------------------------------------------------


def phrase_names() -> list[str]:
    """Deprecated phrase id map (no longer kept)."""
    return []


def site_note(stop: str, phrases: list[str]) -> str:
    """What a stop's site names where the site does not say it: a phrase's name."""
    m = re.search(r"phrase:(\d+)", stop)
    return f" ({phrases[int(m.group(1))]})" if m and int(m.group(1)) < len(phrases) else ""


def first_stop(detail: str) -> str:
    """The stop a detail names, without the strictness label: `residue:sdo:MV ?`."""
    return re.sub(r"^(non-strict|strict): ", "", detail)


def pct(xs: list[int], q: float) -> str:
    if not xs:
        return "-"
    s = sorted(xs)
    return f"{s[min(len(s) - 1, int(q * len(s)))] / 1000:.2f}"


Row = tuple[str, str, int | None, str]




def against_expected(expected: dict[str, str], rows: list[tuple]) -> list[tuple[str, str, tuple[str, str]]]:
    """The run's tests whose bucket differs from `expected`'s (skips and unlisted left out): test, expected bucket,
    (bucket, detail)."""
    return [(r[0], expected[r[0]], (r[1], r[3])) for r in rows
            if r[1] != "skip" and r[0] in expected and expected[r[0]] != r[1]]




UNTIMED = ("skip", "unsupported", "timeout", "timeout(fuel)")










def batch_table(results: dict[str, list[tuple[str, str, int | None, str]]], batches: list[tuple[str, list[str]]],
                cover: tuple[int, int] | None) -> list[str]:
    """The census's coverage line and each batch's outcomes per mode."""
    n = sum(len(ts) for _, ts in batches)
    out = ["## Coverage and batches\n"]
    out.append(f"The sample: {n} tests in {len(batches)} batch(es)"
               + (f"; runnable tests of test262 sampled: {cover[0]} of {cover[1]} ({100 * cover[0] / cover[1]:.1f}%)."
                  if cover else " (`test262.py expand --status` for its coverage of test262).") + "\n")
    out.append("| batch | tests | mode | " + " | ".join(BUCKETS) + " | not run |")
    out.append("|---|---:|---|" + "---:|" * len(BUCKETS) + "---:|")
    modes = [m for m in MODES if m in results]
    got = {m: {t: b for t, b, _, _ in results[m] if b != "skip"} for m in modes}
    for name, ts in batches:
        b = BATCH_RE.match("# " + name)
        label = f"batch {b.group(1)} ({b.group(2)}, seed {b.group(3)})" if b else name
        for m in modes:
            c = Counter(got[m][t] for t in ts if t in got[m])
            cells = " | ".join(str(c.get(k, 0)) for k in BUCKETS)
            out.append(f"| {label} | {len(ts)} | {m} | {cells} | {len(ts) - sum(c.values())} |")
    out.append("")
    return out




def census(results: dict[str, list[tuple[str, str, int | None, str]]], top: int = 25,
           held: dict[str, int] | None = None, batches: list[tuple[str, list[str]]] | None = None,
           cover: tuple[int, int] | None = None, limits: dict[str, dict[str, str]] | None = None) -> str:
    """The census report's body from each mode's results, `held` the parked
    timeouts, `batches` the sample's (with `cover`, its runnable coverage of test262), `limits` each mode's parked
    limits with their reasons (counted `limit`, whatever their rows; the excluded ones `excluded`, outside `tests`)."""
    limits = limits or {}
    reasons = {t: why for d in limits.values() for t, why in d.items()}
    exc = {m: excluded(d) for m, d in limits.items()}
    xcol = any(exc.values())
    out = batch_table(results, batches, cover) if batches else []
    phrases = phrase_names()
    modes = [m for m in MODES if m in results]
    out.append("## Outcomes per mode\n")
    out.append("| mode | tests | " + " | ".join(BUCKETS) + " | limit |" + " excluded |" * xcol + " pass % | stop % |")
    out.append("|---|---:|" + "---:|" * (len(BUCKETS) + 1 + xcol) + "---:|---:|")
    for m in modes:
        lim, x = set(limits.get(m, {})), exc.get(m, set())
        rows = [r for r in results[m] if r[1] != "skip" and r[0] not in lim]
        c = Counter("stop" if r[1] == "assertFailed" else r[1] for r in rows)
        ran = len(rows) + len(lim - x)
        cells = " | ".join(str(c.get(b, 0)) for b in BUCKETS)
        p = f"{100 * c['pass'] / ran:.1f}" if ran else "-"
        cov = f"{100 * c['stop'] / ran:.1f}" if ran else "-"
        out.append(f"| {m} | {ran} | {cells} | {len(lim - x)} |"
                   + f" {len(x)} |" * xcol + f" {p} | {cov} |")
    if limits:
        out.append("\n(`limit`: a parked limit, whatever its row; `tests` counts them.)")
    if xcol:
        out.append("\n(`excluded`: a limit excluded from execution, whatever its row; `tests` and the rates leave them"
                   " out; listed below.)")
    out.append("")
    if held:
        out.append("Parked timeouts (expected `timeout` or `timeout(fuel)`, not re-run without `--timeouts`): "
                   + ", ".join(f"{m} {n}" for m, n in held.items()) + ".\n")
    if limits:
        out.append("Parked limits (tests no executor answers within a run's limit, not run without `--limits`; the reason"
                   " in the expected files' `# limit` lines): "
                   + ", ".join(f"{m} {len(d) - len(exc[m])}" for m, d in limits.items()) + ".\n")
    if xcol:
        out.append("Excluded limits (not run, `--limits` included; out of `tests`): "
                   + ", ".join(f"{m} {len(x)}" for m, x in exc.items() if x) + ".\n")
    for m in modes:
        stops = Counter(first_stop(r[3]) for r in results[m] if r[1] == "stop" and r[0] not in limits.get(m, {}))
        if not stops:
            continue
        out.append(f"## First stops, {m}: ranked by tests blocked\n")
        out.append("| tests | stop |")
        out.append("|---:|---|")
        for s, n in stops.most_common(top):
            out.append(f"| {n} | `{s}`{site_note(s, phrases)} |")
        if len(stops) > top:
            out.append(f"| {sum(n for _, n in stops.most_common()[top:])} | ({len(stops) - top} more stops) |")
        out.append("")
    unsup = Counter()
    for m in modes[:1]:
        unsup = Counter(first_stop(r[3]) for r in results[m] if r[1] == "unsupported")
    if unsup:
        out.append(f"## Unsupported ({modes[0]}): what the ecma-run test host lacks\n")
        out.append("| tests | flag or host hook |")
        out.append("|---:|---|")
        out += [f"| {n} | `{u}` |" for u, n in unsup.most_common()]
        out.append("")
    for m in modes:
        for kind, title in (("timeout", "Timeouts"), ("timeout(fuel)", "Timeouts (fuel)")):
            slow = [(t, d) for t, b, _, d in results[m] if b == kind and t not in reasons]
            if slow:
                out.append(f"## {title}, {m}\n")
                out += [f"- `{t}`: {d}" for t, d in slow]
                out.append("")
    for title, part in [("parked", {t: w for t, w in reasons.items() if w not in EXCLUDED}),
                        ("excluded from execution", {t: w for t, w in reasons.items() if w in EXCLUDED})]:
        if not part:
            continue
        out.append(f"## Limits: {title}, by reason\n")
        out.append("| tests | reason |")
        out.append("|---:|---|")
        out += [f"| {n} | {why} |" for why, n in Counter(part.values()).most_common()]
        out.append("")
        out += [f"- `{t}`: {why}" for t, why in sorted(part.items())]
        out.append("")
    out.append("## Wrong answers\n")
    wrong = [(m, t, d) for m in modes for t, b, _, d in results[m] if b == "fail"]
    if wrong:
        out += [f"- {m}: `{t}`: {d}" for m, t, d in wrong]
    else:
        out.append("None.")
    out.append("\n## Time per test (seconds: the test's jobs, without a server's harness run)\n")
    out.append("| mode | tests timed | median | p95 |")
    out.append("|---|---:|---:|---:|")
    for m in modes:
        # A harness's timeout ends before the test's job: no time of the test's own.
        timed = {t: ms for t, b, ms, _ in results[m] if ms and b not in ("skip", "unsupported")}
        out.append(f"| {m} | {len(timed)} | {pct(list(timed.values()), 0.5)} | {pct(list(timed.values()), 0.95)} |")
    out.append("")
    out.append("ecma-run counts no steps, so steps are not reported (wall time only).")
    return "\n".join(out) + "\n"


RECORDED = "(recorded in the expected file, not in the results)"


def with_recorded(results: dict[str, list[Row]], expected_dir: Path) -> dict[str, list[Row]]:
    """Each mode's results, with a row per test its expected file records and the results lack (no time, detail
    RECORDED)."""
    out = dict(results)
    for m in MODES:
        p = expected_dir / f"{m}.txt"
        if p.exists():
            have = {r[0] for r in results.get(m, [])}
            extra = [(t, b, None, RECORDED) for t, b in read_expected(p).items() if t not in have]
            if extra or m in results:
                out[m] = results.get(m, []) + extra
    return out


def cmd_census(args) -> int:
    d = out_dir(args)
    expected_dir = ROOT / "tests/expected" / args.stage
    results = with_recorded({m: read_results(d / f"{m}.tsv") for m in MODES if (d / f"{m}.tsv").exists()},
                            expected_dir)
    if not results:
        print(f"no results in {d} and no expected file in {expected_dir} (run `test262.py run --mode M` first)")
        return 1
    n = len({t for rs in results.values() for t, *_ in rs})
    notes = "".join(x + "\n" for x in args.note)
    head = f"""# test262 on ecma-run: the census ({args.stage})

Generated by `python3 scripts/test262.py census` from the runs' results, and the
expected files for the tests the results lack: {n} tests of the stage `{args.stage}`
(tests/test262/{args.stage}.conf), per mode of ecma-run.""" + f""" `stop` is the model's coverage gap
(`<kind>:<site> <step>`), `fail` a wrong answer (a finding).
{notes}"""
    (ROOT / args.report).parent.mkdir(parents=True, exist_ok=True)
    conf = ROOT / "tests/test262" / f"{args.stage}.conf"
    paths = conf_section(conf, "paths") if conf.exists() else []
    # A sample lists its tests; a stage of directories (suite) has no batches and counts every listed test.
    sampled = bool(paths) and all(t.endswith(".js") for t in paths)
    tests = paths if sampled else None
    held = parked_per_mode(expected_dir, tests)
    limits = limits_per_mode(expected_dir, tests)
    batches = conf_batches(conf) if sampled else None
    cover = conf_coverage(conf) if sampled else None
    (ROOT / args.report).write_text(head + "\n" + census(results, held=held, batches=batches, cover=cover, limits=limits))
    print(f"wrote {args.report}")
    return 0


LIMITS_HELP = ("only the parked limits (tests with a feature in LIMITS or a path in LIMIT_PATHS), whatever is recorded,"
               " but the excluded ones (a reason in EXCLUDED)")


def parser() -> argparse.ArgumentParser:
    """The command line: sample, expand, run, plan, round, merge, census, ratchet."""
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--stage", default="sample")
    common.add_argument("--test262", help="the test262 checkout (default external/test262)")
    common.add_argument("--out", help="the results directory (default $TMPDIR/test262)")
    s = sub.add_parser("sample", parents=[common])
    s.add_argument("--seed", type=int, default=SEED)
    s.add_argument("--size", type=int, default=SIZE)
    s.add_argument("--force", action="store_true", help="replace a sample that has batches")
    e = sub.add_parser("expand", parents=[common])
    eg = e.add_mutually_exclusive_group(required=True)
    eg.add_argument("--batch", type=int, help="add N tests never in the sample, stratified by what remains")
    eg.add_argument("--status", action="store_true", help="the sample's coverage of test262, per top directory")
    e.add_argument("--seed", type=int, help=f"the batch's seed (default {SEED} + the batch's number)")
    r = sub.add_parser("run", parents=[common])
    r.add_argument("--mode", choices=MODES, default="default")
    r.add_argument("--update", action="store_true")
    sel = r.add_mutually_exclusive_group()
    sel.add_argument("--pending", action="store_false", dest="full",
                     help="the tests not known good: not `pass`, or new (the default)")
    sel.add_argument("--full", action="store_true", help="every test of the stage, known-good passes too (not the limits)")
    sel.add_argument("--limits", action="store_true", help=LIMITS_HELP)
    r.set_defaults(full=False)
    r.add_argument("--scheduled", action="store_true", help="a full run the user scheduled (suite, or --full of over FULL_MAX runnable tests)")
    r.add_argument("--timeouts", action="store_true", help="the pending tests and those recorded `timeout` or `timeout(fuel)` (parked)")
    r.add_argument("--chunk", type=parse_chunk, help="I/M: the I-th of M chunks of the selection")
    r.add_argument("--tests-of", choices=MODES, help="only the tests MODE's expected file lists")
    r.add_argument("--bucket", choices=BUCKETS, help="with --tests-of: only those it lists as BUCKET")
    r.add_argument("--tests-from", metavar="FILE", help="only the tests FILE lists (one per line, `#` comments)")
    r.add_argument("-j", "--jobs", type=int, help="the runner's parallel jobs (default its own)")
    r.add_argument("--retry-jobs", type=int, default=RETRY_JOBS,
                   help=f"re-run the run's wall-clock timeouts at the same limit at this -j (default {RETRY_JOBS}; 0: not)")
    r.add_argument("--timeout", type=int, help=f"a test's limit, s (default {PENDING_TIMEOUT}; --full {FULL_TIMEOUT})")
    r.add_argument("--max-rss-mb", type=int, default=1024, help="replace a server over it after a job, MB")
    r.add_argument("--rss-cap-mb", type=int, default=RSS_CAP_MB, help="a job's resident memory cap, MB (0: none)")
    r.add_argument("--no-build", dest="build", action="store_false")
    pl = sub.add_parser("plan", parents=[common])
    rd = sub.add_parser("round", parents=[common])
    rd.add_argument("--batch", type=int, default=0, help="first add N runnable tests never sampled (expand)")
    rd.add_argument("--seed", type=int, help=f"the batch's seed (default {SEED} + the batch's number)")
    rd.add_argument("--update", action="store_true", help="the chunks merge their rows and raise the floor")
    rd.add_argument("--force", action="store_true", help="add a batch while the last one has no row yet")
    for x in [pl, rd]:
        x.add_argument("--mode", choices=MODES, default="default")
        x.add_argument("-j", "--jobs", type=int, default=default_jobs())
        x.add_argument("--minutes", type=float, default=MINUTES)
        x.add_argument("--timeout", type=int, default=PENDING_TIMEOUT, help="the runs' limit per test, s")
        x.add_argument("--timeouts", action="store_true", help="the pending tests and those recorded `timeout` or `timeout(fuel)` (parked)")
        x.add_argument("--limits", action="store_true", help=LIMITS_HELP)
        x.add_argument("--tests-of", choices=MODES, help="only the tests MODE's expected file lists")
        x.add_argument("--bucket", choices=BUCKETS, help="with --tests-of: only those it lists as BUCKET")
    mg = sub.add_parser("merge", parents=[common])
    mg.add_argument("--mode", choices=MODES, required=True)
    mg.add_argument("--against", choices=MODES, help="print the rows whose bucket differs from MODE's expected file")
    mg.add_argument("results", nargs="+", help="results files (OUT/<stage>/<mode>.tsv of a run elsewhere)")
    c = sub.add_parser("census", parents=[common])
    c.add_argument("--report", default="board/test262.md")
    c.add_argument("--note", action="append", default=[], help="a line for the report's head (repeatable)")
    k = sub.add_parser("ratchet", parents=[common])
    k.add_argument("--dir", help="the expected files' directory (default tests/expected/STAGE)")
    k.add_argument("--update", action="store_true")
    return ap


def main(argv: list[str]) -> int:
    rest: list[str] = []
    if "--" in argv:
        i = argv.index("--")
        argv, rest = argv[:i], argv[i + 1 :]
    args = parser().parse_args(argv)
    if args.cmd == "sample":
        return cmd_sample(args)
    if args.cmd == "expand":
        return cmd_expand(args)
    if args.cmd == "run":
        return cmd_run(args, rest)
    if args.cmd == "plan":
        return cmd_plan(args)
    if args.cmd == "round":
        return cmd_round(args)
    if args.cmd == "merge":
        return cmd_merge(args)
    if args.cmd == "census":
        return cmd_census(args)
    return cmd_ratchet(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
