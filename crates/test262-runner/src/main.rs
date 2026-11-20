//! `test262-runner`: run test262 on ecma-run (scripts/test262.py drives it).
//!
//! ```text
//! test262-runner --run PATH [--mode MODE] [--stage s2] [--update] [TESTS…]
//! ```
//!
//! Run from the repository root. The stage's configuration is
//! `tests/test262/<stage>.conf` (directories, allowed features, skipped
//! flags). `--run PATH --mode MODE` runs the tests on ecma-run (the
//! specification's driver; `test262_runner::run`): MODE is `default`,
//! `checked`, `plain` (`--no-accel`) or `plain-checked`, the expected file
//! `tests/expected/<stage>/<MODE>.txt`. `TESTS` (files or directories under
//! `external/test262/test`) and `--tests-from FILE`'s lines replace the
//! stage's directories (a file named so runs even under `[exclude]`). Every test runs in non-strict and strict mode unless
//! its flags say otherwise (`onlyStrict`, `noStrict`, `raw`), its harness
//! (`assert.js`, `sta.js` and its `includes`, not for `raw`) as preludes, and
//! lands in one bucket: pass, fail, unsupported, stop (a model stop),
//! assertFailed, timeout, or skip (not run: a feature outside the allow-list or
//! a skipped flag).
//!
//! Exit status: 0 when the run matches the expected results (no expected
//! pass lost, no unexpected pass, no assertFailed); 1 otherwise; 2 on a usage
//! or setup error. `--update` rewrites the expected file from the run.
//!
//! A test that ends over the wall-clock limit, unless it is expected to time
//! out (with `--update`: any test), is run again, alone, once the others are
//! done, under a longer limit (`--retry-timeout`, 3x `--timeout`;
//! `--no-retry`: not), since such a timeout is the machine's load as often
//! as the test's. `--shard I/N` runs every
//! N-th test from the I-th; `--allow-timeout FILE` lists tests that may end in
//! `timeout`. `--expected-timeout SECS` runs the tests the expected file
//! records as `timeout` under that limit, the one the file was recorded under,
//! where `--timeout` is longer: such a test then answers the question its
//! expected bucket answers (does it end within the recorded limit?), not
//! whether the machine was quiet enough to finish it within the longer one.
//!
//! `--serve` runs the jobs on `--serve` servers, one per worker, replaced after a
//! timeout, a crash, every `--serve-jobs` jobs or over `--serve-max-rss-mb`. `--rss-cap-mb`
//! stops a job whose program goes over it (`timeout`, `rss cap`). The work
//! queue is grouped by harness (`test262_runner::plan`), so that a server warms each
//! prelude list for a run of tests, not for one.
//! `--results FILE` gets each test's row as it completes (bucket, milliseconds, detail
//! and cost: the test's work with its servers' starts and harness runs), under a line
//! naming the build (the hash of the program and the stage's configuration, and the run's
//! configuration); a run again with the same file and build runs only the tests it does
//! not record yet (a resume).
//!
//! SIGINT, SIGTERM and SIGHUP (and with `--stop-on-eof` stdin's end, a parent's
//! lifeline) kill every child's process group, write no further row, and end the run
//! by that signal (SIGTERM).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant};

use test262_runner::plan::{Next, Plan};
use test262_runner::results::{build_id, ResultsLog};
use test262_runner::run::{
    default_warm_timeout, mode_args, prelude_names, run_args, run_test, ColdHarness, RunConfig, RunServers, PROGRAM,
};
use test262_runner::{
    collect_tests, compare, parse_test_list, read_frontmatter, shard, stop_on_signals, summary, Bucket, Expected,
    Harness, Outcome, Stage,
};

const USAGE: &str = "usage: test262-runner --run PATH [options] [TESTS...]

  --run PATH          run the tests on this ecma-run (the specification's driver)
  --mode MODE         default, checked, plain (--no-accel) or plain-checked
                      (default default); expected file tests/expected/STAGE/MODE.txt
  --run-arg ARG       pass ARG to every ecma-run too (repeatable: --no-blame,
                      --max-heap MB)

options:
  --stage NAME        stage configuration tests/test262/NAME.conf (default s2)
  --test262 DIR       the test262 checkout (default external/test262)
  --timeout SECS      wall-clock limit per process (default 30)
  --expected-timeout SECS  wall-clock limit of the tests expected to time out
                      (the limit the expected file was recorded under; default --timeout)
  -j N                parallel jobs (default: half the CPUs, or $TEST262_JOBS)
  --nice N            run at this scheduling niceness, inherited by every
                      child (default 10; 0 keeps the current)
  --expected FILE     expected results (default tests/expected/NAME/MODE.txt)
  --allow-timeout FILE  tests (one per line) that may end in timeout whatever is expected
  --shard I/N         run every N-th test from the I-th (0 <= I < N)
  --tests-from FILE   run the tests FILE lists (one per line, `#` comments) in place of
                      the stage's directories, in its order; an empty list runs nothing
  --no-retry          do not rerun, alone, the wall-clock timeouts of tests not expected to time out
  --retry-timeout SECS  wall-clock limit of such a rerun (default 3x --timeout)
  --update            rewrite the expected file from this run
  --no-compare        do not compare with the expected file
  --depth N           directory depth of the summary (default 3)
  --log FILE          write `<bucket> <test> <detail>` for every test
  -v                  print every test that is not pass or skip
  --serve             run the jobs on servers (--serve): batch mode, the same outcomes
  --serve-jobs N      replace a server after N jobs (default 500; 0: never)
  --serve-max-rss-mb N  replace a server whose resident memory is over N MB
                      after a job (default 512; 0: never)
  --rss-cap-mb N      stop a job whose program's resident memory goes over N MB:
                      a timeout (`rss cap`) (default 768; 0: never)
  --results FILE      append `<test>\t<bucket>\t<ms>\t<detail>\t<cost ms>` as each test
                      completes; a run again with FILE of the same build resumes
  --stop-on-eof       stop as on SIGTERM when stdin ends (the caller's lifeline)
  --warm-timeout SECS wall-clock limit of a server's harness run (default 2x --timeout, at most 600);
                      over it, every test of that harness is a timeout
";

struct Options {
    stage: String,
    test262: PathBuf,
    timeout: u64,
    expected_timeout: Option<u64>,
    retry_timeout: Option<u64>,
    jobs: usize,
    nice: i32,
    expected: Option<PathBuf>,
    allow_timeout: Option<PathBuf>,
    shard: Option<(usize, usize)>,
    retry: bool,
    update: bool,
    no_compare: bool,
    depth: usize,
    log: Option<PathBuf>,
    verbose: bool,
    tests: Vec<String>,
    tests_from: Option<PathBuf>,
    serve: bool,
    serve_jobs: usize,
    serve_max_rss_mb: u64,
    rss_cap_mb: u64,
    results: Option<PathBuf>,
    stop_on_eof: bool,
    run: Option<PathBuf>,
    mode: String,
    run_args: Vec<String>,
    warm_timeout: Option<u64>,
}

fn parse_args() -> Result<Options, String> {
    let mut o = Options {
        stage: "s2".into(),
        test262: "external/test262".into(),
        timeout: 30,
        expected_timeout: None,
        retry_timeout: None,
        jobs: default_jobs(),
        nice: 10,
        expected: None,
        allow_timeout: None,
        shard: None,
        retry: true,
        update: false,
        no_compare: false,
        depth: 3,
        log: None,
        verbose: false,
        tests: Vec::new(),
        tests_from: None,
        serve: false,
        serve_jobs: 500,
        serve_max_rss_mb: 512,
        rss_cap_mb: 768,
        results: None,
        stop_on_eof: false,
        run: None,
        mode: "default".into(),
        run_args: Vec::new(),
        warm_timeout: None,
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut value = |name: &str| args.next().ok_or_else(|| format!("{name} needs a value"));
        match a.as_str() {
            "--stage" => o.stage = value("--stage")?,
            "--test262" => o.test262 = value("--test262")?.into(),
            "--timeout" => o.timeout = value("--timeout")?.parse().map_err(|e| format!("--timeout: {e}"))?,
            "--expected-timeout" => {
                o.expected_timeout = Some(
                    value("--expected-timeout")?
                        .parse()
                        .map_err(|e| format!("--expected-timeout: {e}"))?,
                )
            }
            "-j" => o.jobs = value("-j")?.parse().map_err(|e| format!("-j: {e}"))?,
            "--nice" => o.nice = value("--nice")?.parse().map_err(|e| format!("--nice: {e}"))?,
            "--expected" => o.expected = Some(value("--expected")?.into()),
            "--allow-timeout" => o.allow_timeout = Some(value("--allow-timeout")?.into()),
            "--shard" => o.shard = Some(parse_shard(&value("--shard")?)?),
            "--tests-from" => o.tests_from = Some(value("--tests-from")?.into()),
            "--no-retry" => o.retry = false,
            "--retry-timeout" => {
                o.retry_timeout = Some(
                    value("--retry-timeout")?
                        .parse()
                        .map_err(|e| format!("--retry-timeout: {e}"))?,
                )
            }
            "--update" => o.update = true,
            "--no-compare" => o.no_compare = true,
            "--depth" => o.depth = value("--depth")?.parse().map_err(|e| format!("--depth: {e}"))?,
            "--log" => o.log = Some(value("--log")?.into()),
            "-v" => o.verbose = true,
            "--serve" => o.serve = true,
            "--serve-jobs" => {
                o.serve_jobs = value("--serve-jobs")?
                    .parse()
                    .map_err(|e| format!("--serve-jobs: {e}"))?
            }
            "--serve-max-rss-mb" => {
                o.serve_max_rss_mb = value("--serve-max-rss-mb")?
                    .parse()
                    .map_err(|e| format!("--serve-max-rss-mb: {e}"))?
            }
            "--rss-cap-mb" => {
                o.rss_cap_mb = value("--rss-cap-mb")?
                    .parse()
                    .map_err(|e| format!("--rss-cap-mb: {e}"))?
            }
            "--results" => o.results = Some(value("--results")?.into()),
            "--stop-on-eof" => o.stop_on_eof = true,
            "--run" => o.run = Some(value("--run")?.into()),
            "--mode" => o.mode = value("--mode")?,
            "--run-arg" => o.run_args.push(value("--run-arg")?),
            "--warm-timeout" => {
                o.warm_timeout = Some(
                    value("--warm-timeout")?
                        .parse()
                        .map_err(|e| format!("--warm-timeout: {e}"))?,
                )
            }
            "-h" | "--help" => {
                print!("{USAGE}");
                std::process::exit(0);
            }
            _ if a.starts_with('-') => return Err(format!("unknown option {a}")),
            _ => o.tests.push(a),
        }
    }
    o.jobs = o.jobs.max(1);
    Ok(o)
}

/// The path of the program the tests run on, once the mode is known.
fn driver_of(o: &Options) -> Result<PathBuf, String> {
    mode_args(&o.mode).ok_or_else(|| format!("--mode {}: unknown mode", o.mode))?;
    o.run.clone().ok_or_else(|| format!("give --run (the path of {PROGRAM})"))
}

/// `I/N`, with `I < N`.
fn parse_shard(v: &str) -> Result<(usize, usize), String> {
    let bad = || format!("--shard {v}: expected I/N with 0 <= I < N");
    let (i, n) = v.split_once('/').ok_or_else(bad)?;
    let (i, n): (usize, usize) = (i.parse().map_err(|_| bad())?, n.parse().map_err(|_| bad())?);
    if i >= n {
        return Err(bad());
    }
    Ok((i, n))
}

/// `$TEST262_JOBS`, else half the CPUs: a full run is long, and it shares the
/// machine with builds and other work.
fn default_jobs() -> usize {
    if let Some(n) = std::env::var("TEST262_JOBS").ok().and_then(|v| v.parse().ok()) {
        return n;
    }
    std::thread::available_parallelism().map_or(4, |n| n.get() / 2)
}

/// Lower this process's scheduling priority by `inc`; the children inherit it.
#[cfg(unix)]
fn lower_priority(inc: i32) {
    extern "C" {
        fn nice(inc: i32) -> i32;
    }
    if inc > 0 {
        // SAFETY: nice(3) only adjusts this process's scheduling priority.
        unsafe { nice(inc) };
    }
}

#[cfg(not(unix))]
fn lower_priority(_inc: i32) {}

/// A test path as given on the command line, relative to `test262/test`.
fn test_path(arg: &str, test262: &std::path::Path) -> String {
    let arg = arg.trim_end_matches('/');
    let root = test262.join("test");
    let root = root.to_string_lossy();
    for prefix in [
        format!("{root}/"),
        "external/test262/test/".to_string(),
        "test/".to_string(),
    ] {
        if let Some(rest) = arg.strip_prefix(prefix.as_str()) {
            return rest.to_string();
        }
    }
    arg.to_string()
}

fn main() -> ExitCode {
    let o = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("test262-runner: {e}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    lower_priority(o.nice);
    match run(o) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("test262-runner: {e}");
            ExitCode::from(2)
        }
    }
}

fn run(o: Options) -> Result<bool, String> {
    let conf = PathBuf::from(format!("tests/test262/{}.conf", o.stage));
    let stage = Stage::parse(&std::fs::read_to_string(&conf).map_err(|e| format!("{}: {e}", conf.display()))?)
        .map_err(|e| format!("{}: {e}", conf.display()))?;
    if !o.test262.join("test").is_dir() {
        return Err(format!(
            "{}/test not found (git submodule update --init --depth 1 external/test262)",
            o.test262.display()
        ));
    }
    let program_path = driver_of(&o)?;
    if !program_path.is_file() {
        return Err(format!("{PROGRAM} not found at {}", program_path.display()));
    }
    let mode_args = run_args(&o.mode, &o.run_args).ok_or_else(|| format!("--mode {}: unknown mode", o.mode))?;
    let mut given = o.tests.clone();
    if let Some(p) = &o.tests_from {
        let text = std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?;
        given.extend(
            text.lines()
                .map(|l| l.split('#').next().unwrap_or("").trim())
                .filter(|l| !l.is_empty())
                .map(String::from),
        );
    }
    let paths: Vec<String> = if given.is_empty() && o.tests_from.is_none() {
        stage.paths.clone()
    } else {
        given.iter().map(|t| test_path(t, &o.test262)).collect()
    };
    let mut tests = collect_tests(&o.test262, &paths)?;
    // A test named by itself runs even under `[exclude]`.
    tests.retain(|t| paths.contains(t) || !stage.excludes(t));
    if let Some((i, n)) = o.shard {
        tests = shard(tests, i, n);
    }
    if o.tests_from.is_some() {
        // The listed order is the work queue's within each harness group (a caller lists the slowest first).
        let rank: std::collections::HashMap<&str, usize> =
            paths.iter().enumerate().rev().map(|(i, p)| (p.as_str(), i)).collect();
        tests.sort_by_key(|t| rank.get(t.as_str()).copied().unwrap_or(usize::MAX));
    }
    let allow_timeout = match &o.allow_timeout {
        Some(p) => parse_test_list(&std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?),
        None => BTreeSet::new(),
    };
    let expected_path = o
        .expected
        .clone()
        .unwrap_or_else(|| PathBuf::from(format!("tests/expected/{}/{}.txt", o.stage, o.mode)));
    let mut expected = match std::fs::read_to_string(&expected_path) {
        Ok(text) => Expected::parse(&text).map_err(|e| format!("{}: {e}", expected_path.display()))?,
        Err(_) if o.update || o.no_compare => Expected::default(),
        Err(e) => {
            return Err(format!(
                "{}: {e} (run with --update to create it)",
                expected_path.display()
            ))
        }
    };

    // The harness files every test needs, read once, and each test's preludes (the work queue's groups).
    let mut includes = Vec::new();
    let mut harness_of: HashMap<String, Vec<String>> = HashMap::new();
    for t in &tests {
        if let Ok((_, fm)) = read_frontmatter(&o.test262, t) {
            harness_of.insert(t.clone(), prelude_names(&fm));
            includes.extend(fm.includes);
        }
    }
    let key_of = |t: &str| harness_of.get(t).cloned().unwrap_or_default();
    let harness = Harness::load(&o.test262, includes)?;

    let scratch = std::env::temp_dir().join(format!("test262-runner-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).map_err(|e| format!("{}: {e}", scratch.display()))?;
    stop_on_signals(o.stop_on_eof, scratch.clone());
    let cfg = RunConfig {
        test262: std::fs::canonicalize(&o.test262).map_err(|e| e.to_string())?,
        program: std::fs::canonicalize(&program_path).map_err(|e| e.to_string())?,
        args: mode_args,
        timeout: Duration::from_secs(o.timeout),
        warm_timeout: o
            .warm_timeout
            .map_or_else(|| default_warm_timeout(Duration::from_secs(o.timeout)), Duration::from_secs),
        cold: ColdHarness::default(),
        scratch: scratch.clone(),
        stage,
        serve: o.serve,
        serve_jobs: o.serve_jobs,
        max_rss: o.serve_max_rss_mb << 20,
        rss_cap: o.rss_cap_mb << 20,
    };

    eprintln!(
        "test262-runner: {} tests, stage {} on {} {}{}, {} jobs, timeout {}{}",
        tests.len(),
        o.stage,
        PROGRAM,
        cfg.args.join(" "),
        o.shard.map_or(String::new(), |(i, n)| format!(" (shard {i}/{n})")),
        o.jobs,
        match o.expected_timeout {
            Some(e) => format!("{}s (expected timeouts {e}s)", o.timeout),
            None => format!("{}s", o.timeout),
        },
        if o.serve { ", batch mode" } else { "" }
    );
    // The tests expected to time out, under the limit they were recorded
    // under (--expected-timeout).
    let recorded = o.expected_timeout.map(|secs| RunConfig {
        timeout: Duration::from_secs(secs),
        ..cfg.clone()
    });
    let cfg_of = |test: &str| match &recorded {
        Some(r) if expected.results.get(test) == Some(&Bucket::Timeout) => r,
        _ => &cfg,
    };
    // One test, timed (its jobs time themselves, without a server's harness run).
    let run_one = |cfg: &RunConfig, test: &str, worker: usize, servers: &mut RunServers| {
        let t0 = Instant::now();
        let mut outcome = run_test(cfg, &harness, test, worker, servers);
        if outcome.bucket != Bucket::Skip {
            let took = t0.elapsed().as_millis() as u64;
            outcome.ms.get_or_insert(took);
            outcome.cost_ms = Some(took);
        }
        outcome
    };
    // The rows the results file has for this build: those tests are done.
    let (log, mut resumed) = match &o.results {
        Some(path) => {
            let mut config = format!(
                "stage {} test262 {} timeout {} {}",
                o.stage,
                test262_revision(&o.test262),
                o.timeout,
                cfg.args.join(" ")
            );
            if o.rss_cap_mb > 0 {
                config.push_str(&format!(" rss-cap {}", o.rss_cap_mb));
            }
            let tools = [program_path.clone(), conf.clone()];
            let id = build_id(&tools.iter().map(PathBuf::as_path).collect::<Vec<_>>(), &config)?;
            let (log, rows) = ResultsLog::open(path, &id)?;
            (Some(log), rows)
        }
        None => (None, BTreeMap::new()),
    };
    let listed: BTreeSet<&String> = tests.iter().collect();
    resumed.retain(|t, _| listed.contains(t));
    if !resumed.is_empty() {
        eprintln!(
            "test262-runner: resuming {}: {} of {} tests recorded for this build",
            o.results.as_ref().map_or(String::new(), |p| p.display().to_string()),
            resumed.len(),
            tests.len()
        );
    }
    let all = tests.len();
    let tests: Vec<String> = tests.into_iter().filter(|t| !resumed.contains_key(t)).collect();
    let start = Instant::now();
    let keys: Vec<Vec<String>> = tests.iter().map(|t| key_of(t)).collect();
    let plan = (Mutex::new(Plan::new(&keys, o.jobs)), Condvar::new());
    let done = AtomicUsize::new(0);
    let results: Mutex<BTreeMap<String, Outcome>> = Mutex::new(resumed);
    let log_error: Mutex<Option<String>> = Mutex::new(None);
    let large = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for worker in 0..o.jobs {
            let (cfg_of, run_one, tests, plan, done, results, large, log, log_error) =
                (&cfg_of, &run_one, &tests, &plan, &done, &results, &large, &log, &log_error);
            s.spawn(move || {
                let mut servers = RunServers::default();
                loop {
                    let (queue, changed) = plan;
                    let mut q = queue.lock().expect("plan");
                    let i = loop {
                        match q.next(worker) {
                            Next::Test(i) => break Some(i),
                            Next::Done => break None,
                            Next::Wait if log_error.lock().expect("log error").is_some() => break None,
                            Next::Wait => q = changed.wait_timeout(q, Duration::from_secs(1)).expect("plan").0,
                        }
                    };
                    drop(q);
                    let Some(test) = i.map(|i| &tests[i]) else { break };
                    let outcome = run_one(cfg_of(test), test, worker, &mut servers);
                    if !matches!(outcome.bucket, Bucket::Skip | Bucket::Unsupported) {
                        let (ms, cost) = (outcome.ms.unwrap_or(0), outcome.cost_ms.unwrap_or(0));
                        queue.lock().expect("plan").record(worker, ms, cost);
                        changed.notify_all();
                    }
                    if log_error.lock().expect("log error").is_some() {
                        break;
                    }
                    if let Some(Err(e)) = log.as_ref().map(|l| l.append(test, &outcome)) {
                        log_error.lock().expect("log error").get_or_insert(e);
                    }
                    results.lock().expect("results").insert(test.clone(), outcome);
                    let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                    if n % 500 == 0 {
                        let secs = start.elapsed().as_secs_f64();
                        eprintln!("  {n}/{} ({secs:.0}s, {:.2} tests/s)", tests.len(), n as f64 / secs);
                    }
                }
                servers.stop();
                large.fetch_add(servers.large, Ordering::Relaxed);
            });
        }
    });
    let large = large.into_inner();
    if let Some(e) = log_error.into_inner().expect("log error") {
        return Err(e);
    }
    if large > 0 {
        eprintln!(
            "test262-runner: {large} server(s) replaced for their resident memory (over {} MB)",
            o.serve_max_rss_mb
        );
    }
    let mut results = results.into_inner().expect("results");
    // Wall-clock timeouts of tests not expected to time out (with --update,
    // of every test, before they are recorded): again, one at a time.
    if o.retry && !o.no_compare {
        let again: Vec<String> = results
            .iter()
            .filter(|(t, r)| {
                r.is_wall_clock_timeout()
                    && !allow_timeout.contains(*t)
                    && (o.update || expected.results.get(*t).is_some_and(|b| *b != Bucket::Timeout))
            })
            .map(|(t, _)| t.clone())
            .collect();
        // By harness, so that the one server warms each once.
        let mut again = again;
        again.sort_by_cached_key(|t| key_of(t));
        if !again.is_empty() {
            let t0 = Instant::now();
            let limit = o.retry_timeout.unwrap_or(3 * o.timeout);
            // A longer harness limit too, so that a harness over the first is warmed again.
            let slow = RunConfig {
                timeout: Duration::from_secs(limit),
                warm_timeout: cfg.warm_timeout.max(default_warm_timeout(Duration::from_secs(limit))),
                ..cfg.clone()
            };
            let mut passed = 0;
            let mut servers = RunServers::default();
            for t in &again {
                let outcome = run_one(&slow, t, 0, &mut servers);
                if let Some(l) = &log {
                    l.append(t, &outcome)?;
                }
                passed += usize::from(outcome.bucket == Bucket::Pass);
                results.insert(t.clone(), outcome);
            }
            servers.stop();
            eprintln!(
                "test262-runner: {} wall-clock timeout(s), run again alone under {limit}s: {passed} passed ({:.1}s)",
                again.len(),
                t0.elapsed().as_secs_f64()
            );
        }
    }
    let _ = std::fs::remove_dir_all(&scratch);
    eprintln!(
        "test262-runner: done in {:.1}s ({} run, {} resumed)",
        start.elapsed().as_secs_f64(),
        tests.len(),
        all - tests.len()
    );

    if let Some(log) = &o.log {
        let mut text = String::new();
        for (t, r) in &results {
            text.push_str(&format!("{} {} {}\n", r.bucket.name(), t, r.detail));
        }
        std::fs::write(log, text).map_err(|e| format!("{}: {e}", log.display()))?;
    }
    if let Some(l) = &log {
        l.finish(&results)?;
    }
    if o.verbose {
        for (t, r) in &results {
            if !matches!(r.bucket, Bucket::Pass | Bucket::Skip) {
                println!("{:12} {t}  {}", r.bucket.name(), r.detail);
            }
        }
    }
    print!("{}", summary(&results, o.depth));

    let mut ok = true;
    let assert_failed: Vec<_> = results
        .iter()
        .filter(|(_, r)| r.bucket == Bucket::AssertFailed)
        .collect();
    if !assert_failed.is_empty() {
        ok = false;
        println!(
            "\n{} test(s) stopped at a failed Assert (always a bug):",
            assert_failed.len()
        );
        for (t, r) in assert_failed {
            println!("  {t}  {}", r.detail);
        }
    }

    if !o.no_compare && !o.update {
        let c = compare(&expected, &results, &allow_timeout);
        if !c.allowed_timeouts.is_empty() {
            println!(
                "\n{} allowed timeout(s) (--allow-timeout {}):",
                c.allowed_timeouts.len(),
                o.allow_timeout
                    .as_ref()
                    .map_or(String::new(), |p| p.display().to_string())
            );
            for (t, was) in &c.allowed_timeouts {
                println!("  {t}  (expected {})", was.name());
            }
        }
        if !c.regressions.is_empty() {
            println!("\n{} regression(s) (expected pass):", c.regressions.len());
            for (t, _, r) in &c.regressions {
                println!("  {:12} {t}  {}", r.bucket.name(), r.detail);
            }
        }
        if !c.unexpected_passes.is_empty() {
            println!(
                "\n{} unexpected pass(es) (rerun with --update to record them):",
                c.unexpected_passes.len()
            );
            for (t, was) in &c.unexpected_passes {
                println!("  {t}  (expected {})", was.name());
            }
        }
        if !c.changes.is_empty() {
            println!("\n{} other change(s) of bucket:", c.changes.len());
            for (t, was, now) in c.changes.iter().take(50) {
                println!("  {t}: {} -> {}", was.map_or("(new)", |b| b.name()), now.name());
            }
            if c.changes.len() > 50 {
                println!("  … and {} more", c.changes.len() - 50);
            }
        }
        ok &= c.is_ok();
    }
    if o.update {
        expected.update(&results);
        let header = format!(
            "test262 expected results on {}, stage {}, mode {}.\n\
             Regenerate: python3 scripts/test262.py run --mode {} --update\n\
             test262 {}\n<bucket> <test under external/test262/test>; skipped tests are not listed.",
            PROGRAM,
            o.stage,
            o.mode,
            o.mode,
            test262_revision(&o.test262)
        );
        if let Some(dir) = expected_path.parent() {
            std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        std::fs::write(&expected_path, expected.render(&header))
            .map_err(|e| format!("{}: {e}", expected_path.display()))?;
        println!("\nwrote {}", expected_path.display());
    }
    Ok(ok)
}

/// The test262 commit (Bazel's checkout's REVISION, else the checkout's HEAD), for the expected file's header and the
/// build id.
fn test262_revision(test262: &std::path::Path) -> String {
    std::fs::read_to_string(test262.join("REVISION"))
        .ok()
        .filter(|r| !r.starts_with("unavailable"))
        .map(|r| r.trim().to_string())
        .or_else(|| {
            std::process::Command::new("git")
                .arg("-C")
                .arg(test262)
                .args(["rev-parse", "HEAD"])
                .output()
                .ok()
                .filter(|o| o.status.success())
                .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        })
        .unwrap_or_else(|| "(unknown revision)".into())
}
