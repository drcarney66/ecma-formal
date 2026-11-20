//! test262 through `ecma-run` (lean/Engine/Cli/Run.lean), the specification's own
//! whole-program driver: the machine accelerated (`default`) or at its own steps (`plain`,
//! `--no-accel`), each optionally `--checked` ([`MODES`]).
//!
//! ecma-run parses the code itself (ParseScript). A test's
//! harness (`assert.js`, `sta.js`, `doneprintHandle.js` for an `async` test, then its
//! `includes`) runs as `--prelude` Scripts in the realm before the test, as
//! INTERPRETING.md lets `includes` be evaluated; a strict-mode run prepends `"use
//! strict";` to the test alone; a `CanBlockIsTrue` test runs on a host whose agent can block
//! (`--can-block`). The test's directory is its `--module-dir` (the modules
//! its specifiers `./NAME` load). A `module` test runs once, from its own file, as the root of a
//! module graph (`--module`, so that it imports itself by its name); a `parse` negative one is only
//! parsed (`--parse-only`), without the harness. A test the stage runs on the web-browser host
//! ([`Stage::web_browser_for`]) runs with `--web-browser`. On a server (`ecma-run --serve`) the state after each
//! prefix of the preludes is cached, so a worker parses the harness once: before a
//! job whose preludes its server has not run yet, the worker sends them alone (a
//! warm-up job, under [`RunConfig::warm_timeout`]), so that a job's limit and time are
//! the test's. A prelude list whose warm-up went over that limit is not warmed again in
//! the run: each of its tests is a `timeout` ([`ColdHarness`]).
//!
//! The outcomes ([`outcome_of`]): `pass`; `fail`, a wrong answer (always a finding);
//! `stop` (`stop:<kind>:<site>`, the model's coverage gap: a residue step, out of fuel,
//! a failed Assert; `crash:<signal>`, the program killed by a signal without a result,
//! such as a native stack overflow's SIGABRT); `unsupported` (`unsupported:<what>`: a
//! feature or host hook the ecma-run test host does not have, [`unsupported_reason`]); `timeout`
//! (`wall clock`, a job or its harness over its limit; `rss cap`, the program's resident memory
//! over [`RunConfig::rss_cap`]).

use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::frontmatter::{Frontmatter, Phase};
use crate::{
    async_outcome, kill_group, killed_by, over_rss, read_frontmatter, reap, run_with_timeout, signal_name,
    skip_reason, spawn_group, throws, Bucket, Harness, Outcome, Run, Stage, RSS_POLL,
};

/// The program the tests run on, as outcomes name it.
pub const PROGRAM: &str = "ecma-run";

/// The modes: a name and ecma-run's arguments for it.
pub const MODES: [(&str, &[&str]); 4] = [
    ("default", &[]),
    ("checked", &["--checked"]),
    ("plain", &["--no-accel"]),
    ("plain-checked", &["--no-accel", "--checked"]),
];

/// The longest default warm-up limit, half the build box's job limit.
pub const WARM_CAP: Duration = Duration::from_secs(600);

/// The warm-up limit when none is given: twice a job's `timeout`, at most [`WARM_CAP`].
pub fn default_warm_timeout(timeout: Duration) -> Duration {
    (timeout * 2).min(WARM_CAP)
}

/// The program's arguments for the mode `name`.
pub fn mode_args(name: &str) -> Option<Vec<String>> {
    MODES
        .iter()
        .find(|(n, ..)| *n == name)
        .map(|(_, a)| a.iter().map(|s| s.to_string()).collect())
}

/// The program's arguments for the mode `name`: the mode's, then `extra`.
pub fn run_args(name: &str, extra: &[String]) -> Option<Vec<String>> {
    let mut args = mode_args(name)?;
    args.extend(extra.iter().cloned());
    Some(args)
}

/// How to run the tests on ecma-run.
#[derive(Debug, Clone)]
pub struct RunConfig {
    pub test262: PathBuf,
    /// ecma-run's path.
    pub program: PathBuf,
    /// The mode's arguments and any others (`--no-blame`, `--max-heap MB`).
    pub args: Vec<String>,
    /// Wall-clock limit of a job.
    pub timeout: Duration,
    /// Wall-clock limit of a warm-up job (the harness alone).
    pub warm_timeout: Duration,
    /// The prelude lists whose warm-up went over its limit, shared by the run's workers.
    pub cold: ColdHarness,
    pub scratch: PathBuf,
    pub stage: Stage,
    /// Run the jobs on `--serve` servers.
    pub serve: bool,
    /// Replace a server after this many jobs (0: never).
    pub serve_jobs: usize,
    /// Replace a server whose resident memory is over this many bytes after a job (0: never).
    pub max_rss: u64,
    /// Stop a job whose program's resident memory goes over this many bytes (0: never).
    pub rss_cap: u64,
}

/// The prelude lists whose warm-up went over a limit, each with the longest such limit.
#[derive(Debug, Clone, Default)]
pub struct ColdHarness(Arc<Mutex<HashMap<Vec<PathBuf>, Duration>>>);

impl ColdHarness {
    /// Whether `pre`'s warm-up went over `limit` or a longer limit.
    pub fn over(&self, pre: &[PathBuf], limit: Duration) -> bool {
        self.0.lock().expect("cold").get(pre).is_some_and(|l| *l >= limit)
    }

    /// `pre`'s warm-up went over `limit`.
    pub fn record(&self, pre: &[PathBuf], limit: Duration) {
        let mut m = self.0.lock().expect("cold");
        let l = m.entry(pre.to_vec()).or_default();
        *l = (*l).max(limit);
    }
}

/// Why ecma-run cannot run a test (with frontmatter `fm` and source `source`; `harness`
/// gives an include's text): a host hook its test host does not have.
pub fn unsupported_reason(
    fm: &Frontmatter,
    source: &str,
    harness: impl Fn(&str) -> Option<String>,
) -> Option<String> {
    let texts: Vec<String> = std::iter::once(source.to_string())
        .chain(fm.includes.iter().filter_map(|i| harness(i)))
        .collect();
    if let Some(m) = texts.iter().find_map(|t| host_hook(t)) {
        return Some(m);
    }
    if texts.iter().any(|t| t.contains("$262.createRealm")) {
        return texts.iter().find_map(|t| realm_hook(t));
    }
    None
}

/// The `$262` members the test host has; `$262` itself is the empty one.
const HOST_MEMBERS: [&str; 7] = [
    "", "global", "detachArrayBuffer", "createRealm", "evalScript", "agent", "IsHTMLDDA",
];

/// The first `$262` member `text` uses that the test host lacks (`$262.gc`).
fn host_hook(text: &str) -> Option<String> {
    text.match_indices("$262").find_map(|(at, _)| {
        let member: String = text[at + 4..]
            .strip_prefix('.')
            .map(|r| r.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect())
            .unwrap_or_default();
        (!HOST_MEMBERS.contains(&member.as_str())).then(|| format!("$262.{member}"))
    })
}

/// The `$262` members of the test262 host interface that the test host lacks.
const HOST_LACKS: [&str; 2] = ["gc", "AbstractModuleSource"];

/// The first lacking member `text` uses through a created realm's `$262` (`other.gc`).
fn realm_hook(text: &str) -> Option<String> {
    text.match_indices('.').find_map(|(at, _)| {
        let member: String = text[at + 1..]
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        HOST_LACKS.contains(&member.as_str()).then(|| format!("$262.{member}"))
    })
}

/// The outcome of a test's run in one mode, from ecma-run's result line and the lines
/// `print` wrote.
pub fn outcome_of(fm: &Frontmatter, line: &str, printed: &[String]) -> Outcome {
    let negative = fm.negative.as_ref();
    if let Some(rest) = line.strip_prefix("stop: ") {
        if let Some(what) = rest.strip_prefix("unsupported ") {
            return Outcome::new(Bucket::Unsupported, what);
        }
        if rest.starts_with("cannot read ") {
            return Outcome::new(Bucket::Fail, format!("ecma-run: {rest}"));
        }
        let (kind, site) = rest.split_once(' ').unwrap_or((rest, ""));
        // Out of fuel (call depth or a loop's rounds) is a timeout of its own kind.
        let bucket = if kind == "outOfFuel" { Bucket::FuelTimeout } else { Bucket::Stop };
        return Outcome::new(
            bucket,
            if site.is_empty() {
                kind.to_string()
            } else {
                format!("{kind}:{site}")
            },
        );
    }
    if line.starts_with("normal: ") {
        if let Some(n) = negative {
            return Outcome::new(Bucket::Fail, format!("{line}, but a {} was expected", n.error_type));
        }
        if fm.has_flag("async") {
            let text: String = std::iter::once(line)
                .chain(printed.iter().map(String::as_str))
                .map(|l| format!("{l}\n"))
                .collect();
            return async_outcome(&text);
        }
        return Outcome::new(Bucket::Pass, "");
    }
    if line.starts_with("throw: ") {
        return match negative {
            Some(n) if throws(line, &n.error_type) => Outcome::new(Bucket::Pass, ""),
            Some(n) => Outcome::new(Bucket::Fail, format!("{line}, but a {} was expected", n.error_type)),
            None => Outcome::new(Bucket::Fail, line),
        };
    }
    if line.is_empty() {
        return Outcome::new(Bucket::Fail, "ecma-run: no result line");
    }
    Outcome::new(Bucket::Fail, line)
}

/// The outcome of a run that ended by the signal `sig` without a result line: a limit, not an answer.
pub fn crash_outcome(sig: i32) -> Outcome {
    Outcome::new(Bucket::Stop, format!("crash:{}", signal_name(sig)))
}

/// Run one test (`test` relative to `test262/test`) on ecma-run in every mode its flags
/// ask for (non-strict and strict, but not the second after
/// a first that [`stops_coverage`]): the worse outcome, the time of its jobs in `ms`.
pub fn run_test(cfg: &RunConfig, harness: &Harness, test: &str, slot: usize, servers: &mut RunServers) -> Outcome {
    let (source, fm) = match read_frontmatter(&cfg.test262, test) {
        Ok(x) => x,
        Err(e) => return Outcome::new(Bucket::Fail, format!("frontmatter: {e}")),
    };
    if let Some(reason) = skip_reason(&cfg.stage, &fm) {
        return Outcome::new(Bucket::Skip, reason);
    }
    if let Some(what) = unsupported_reason(&fm, &source, |i| harness.get(i).map(String::from)) {
        return Outcome::new(Bucket::Unsupported, what);
    }
    let modes: &[bool] = if fm.has_flag("module") {
        &[true]
    } else if fm.has_flag("raw") || fm.has_flag("noStrict") {
        &[false]
    } else if fm.has_flag("onlyStrict") {
        &[true]
    } else {
        &[false, true]
    };
    let mut worst = Outcome::new(Bucket::Pass, "");
    let mut total = Duration::ZERO;
    for &strict in modes {
        // A test whose first run stopped or timed out is not covered whatever the other
        // gives, and the other would almost always stop at the same site: not run.
        if stops_coverage(worst.bucket) {
            break;
        }
        let (o, took) = run_mode(cfg, &fm, &source, &cfg.test262.join("test").join(test), strict, slot, servers);
        total += took;
        if o.bucket > worst.bucket {
            let label = match (fm.has_flag("module"), strict) {
                (true, _) => "module",
                (_, true) => "strict",
                _ => "non-strict",
            };
            worst = Outcome::new(o.bucket, format!("{label}: {}", o.detail));
        }
    }
    worst.ms = Some(total.as_millis() as u64);
    worst
}

/// Whether a run's `bucket` leaves the test uncovered, so that its other strictness is not
/// run (a wrong answer there shows once the stop is gone).
pub fn stops_coverage(bucket: Bucket) -> bool {
    matches!(bucket, Bucket::Stop | Bucket::Unsupported) || bucket.is_timeout()
}

/// One `ecma-run --serve`.
struct Server {
    child: Child,
    stdin: ChildStdin,
    answers: Receiver<String>,
    jobs: usize,
    /// The prelude lists it has run (and so cached), each with the host options it ran them on.
    warmed: HashSet<(Vec<PathBuf>, Vec<&'static str>)>,
}

impl Server {
    fn start(program: &Path, args: &[String]) -> Result<Server, String> {
        let mut child = spawn_group(
            Command::new(program)
                .args(args)
                .arg("--serve")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null()),
        )
        .map_err(|e| format!("{}: {e}", program.display()))?;
        let stdin = child.stdin.take().ok_or("no stdin")?;
        let stdout = child.stdout.take().ok_or("no stdout")?;
        let (tx, answers) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                let Ok(line) = line else { break };
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        Ok(Server {
            child,
            stdin,
            answers,
            jobs: 0,
            warmed: HashSet::new(),
        })
    }

    /// Send `PATH<TAB>OPTIONS` and read the records up to `.`, within `timeout` and, its resident
    /// memory read every [`RSS_POLL`], under `rss_cap` bytes (0: no cap).
    fn ask(&mut self, request: &str, timeout: Duration, rss_cap: u64) -> Result<Vec<String>, Ended> {
        if writeln!(self.stdin, "{request}").and_then(|()| self.stdin.flush()).is_err() {
            return Err(Ended::Unwritten);
        }
        let deadline = Instant::now() + timeout;
        let mut polled = Instant::now();
        let mut records = Vec::new();
        loop {
            let now = Instant::now();
            if now >= deadline {
                return Err(Ended::TimedOut);
            }
            let left = deadline - now;
            let wait = if rss_cap > 0 { left.min(RSS_POLL) } else { left };
            match self.answers.recv_timeout(wait) {
                Ok(l) if l == "." => return Ok(records),
                Ok(l) => records.push(l),
                Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => return Err(Ended::Died),
            }
            if rss_cap > 0 && polled.elapsed() >= RSS_POLL {
                polled = Instant::now();
                if over_rss(self.child.id(), rss_cap) {
                    return Err(Ended::RssCap);
                }
            }
        }
    }

    /// Whether it has run nothing but the prelude list `pre` on the host `host`: its memory is then the job's own.
    fn fresh(&self, pre: &[PathBuf], host: &[&str]) -> bool {
        self.jobs == 0 && self.warmed.iter().all(|(w, h)| w == pre && h == host)
    }
}

/// How a request to a server ended without its answer.
enum Ended {
    /// The request could not be written: the server was gone before it.
    Unwritten,
    /// The server closed its output before the answer's end.
    Died,
    TimedOut,
    /// The server's resident memory went over the cap.
    RssCap,
}

/// How long a server whose output or input ended has to exit before it is killed.
const DEATH_GRACE: Duration = Duration::from_secs(2);

/// A worker's ecma-run server, started when first needed.
#[derive(Default)]
pub struct RunServers {
    server: Option<Server>,
    /// Servers replaced for their resident memory.
    pub large: usize,
}

impl RunServers {
    /// Close the server's input and reap it, killed if it has not exited within [`DEATH_GRACE`].
    pub fn stop(&mut self) {
        if let Some(Server { mut child, stdin, .. }) = self.server.take() {
            drop(stdin);
            if exit_within(&mut child, DEATH_GRACE).is_none() {
                kill_group(&mut child);
            }
        }
    }

    /// Kill the server.
    fn kill(&mut self) {
        if let Some(mut s) = self.server.take() {
            kill_group(&mut s.child);
        }
    }

    /// The server whose output ended: the signal it died of within [`DEATH_GRACE`] (SIGKILL
    /// included: not the runner's), else none and it is killed.
    fn died(&mut self) -> Option<i32> {
        let mut s = self.server.take()?;
        match exit_within(&mut s.child, DEATH_GRACE) {
            Some(status) => killed_by(status),
            None => {
                kill_group(&mut s.child);
                None
            }
        }
    }
}

/// The status of `child` once it exits within `grace` (reaped), else none (still running).
fn exit_within(child: &mut Child, grace: Duration) -> Option<ExitStatus> {
    let t0 = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                reap(child);
                return Some(status);
            }
            Ok(None) if t0.elapsed() < grace => std::thread::sleep(Duration::from_millis(10)),
            _ => return None,
        }
    }
}

/// A record's text: `\\`, `\t`, `\n` unescaped.
fn unescape(t: &str) -> String {
    let mut out = String::new();
    let mut chars = t.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('t') => out.push('\t'),
            Some('n') => out.push('\n'),
            Some(o) => out.push(o),
            None => out.push('\\'),
        }
    }
    out
}

/// A server's answer as (result line, printed lines).
pub fn parse_records(records: &[String]) -> (String, Vec<String>) {
    let mut line = String::new();
    let mut printed = Vec::new();
    for r in records {
        let (k, v) = r.split_once('\t').unwrap_or((r.as_str(), ""));
        match k {
            "outcome" => line = unescape(v),
            "print" => printed.push(unescape(v)),
            _ => {}
        }
    }
    (line, printed)
}

/// The harness files of a run, in order: `assert.js`, `sta.js`, `doneprintHandle.js` for an
/// `async` test, then the includes; none for a `raw` test or a module test only parsed.
pub fn prelude_names(fm: &Frontmatter) -> Vec<String> {
    if fm.has_flag("raw") || parse_only(fm) {
        return Vec::new();
    }
    let mut names = vec!["assert.js", "sta.js"];
    if fm.has_flag("async") {
        names.push("doneprintHandle.js");
    }
    names.extend(fm.includes.iter().map(String::as_str));
    let mut seen = HashSet::new();
    names
        .into_iter()
        .filter(|n| seen.insert(*n))
        .map(String::from)
        .collect()
}

/// The harness of a run as paths ([`prelude_names`]).
fn preludes(cfg: &RunConfig, fm: &Frontmatter) -> Vec<PathBuf> {
    let dir = cfg.test262.join("harness");
    prelude_names(fm).iter().map(|n| dir.join(n)).collect()
}

/// A module test whose expected error is a `parse` one: only parsed.
fn parse_only(fm: &Frontmatter) -> bool {
    fm.has_flag("module") && fm.negative.as_ref().is_some_and(|n| n.phase == Phase::Parse)
}

/// The host's options for the test at `test` (its source `source`, its preludes `pre`):
/// `--web-browser` where the stage runs it on the web-browser host, and its agent's ([`agent_args`]).
fn host_args(cfg: &RunConfig, test: &Path, fm: &Frontmatter, source: &str, pre: &[PathBuf]) -> Vec<&'static str> {
    let rel = test.strip_prefix(cfg.test262.join("test")).unwrap_or(test);
    let web = cfg.stage.web_browser_for(&rel.to_string_lossy()).then_some("--web-browser");
    let agents = source.contains("$262.agent")
        || pre.iter().any(|p| std::fs::read_to_string(p).is_ok_and(|t| t.contains("$262.agent")));
    web.into_iter().chain(agent_args(fm, agents)).collect()
}

/// ecma-run's agent options for a test: `--can-block` for a `CanBlockIsTrue` one or one that
/// uses `$262.agent` (`agents`; its surrounding agent can block, INTERPRETING.md).
fn agent_args(fm: &Frontmatter, agents: bool) -> Vec<&'static str> {
    if agents || fm.has_flag("CanBlockIsTrue") {
        vec!["--can-block"]
    } else {
        vec![]
    }
}

/// ecma-run's options for how a test's file runs: `--module` for a module test, with
/// `--parse-only` for one only parsed.
fn source_args(fm: &Frontmatter) -> Vec<&'static str> {
    match (fm.has_flag("module"), parse_only(fm)) {
        (true, true) => vec!["--module", "--parse-only"],
        (true, false) => vec!["--module"],
        _ => vec![],
    }
}

/// Run a test (the file `test`) in one mode (`strict`) on ecma-run, its modules those of its
/// directory: its outcome and the time of the test's job (without a warm-up). A module test
/// runs from `test` itself, any other from a scratch copy (`"use strict";` first when `strict`).
pub fn run_mode(
    cfg: &RunConfig,
    fm: &Frontmatter,
    source: &str,
    test: &Path,
    strict: bool,
    slot: usize,
    servers: &mut RunServers,
) -> (Outcome, Duration) {
    let dir = test.parent().unwrap_or(test);
    let file = if fm.has_flag("module") {
        test.to_path_buf()
    } else {
        let file = cfg.scratch.join(format!("{slot}.js"));
        let text = if strict {
            format!("\"use strict\";\n{source}")
        } else {
            source.to_string()
        };
        if let Err(e) = std::fs::write(&file, text) {
            return (Outcome::new(Bucket::Fail, format!("scratch: {e}")), Duration::ZERO);
        }
        file
    };
    let pre = preludes(cfg, fm);
    let host = host_args(cfg, test, fm, source, &pre);
    if cfg.serve {
        if let Some(r) = serve_job(cfg, fm, &file, &pre, dir, &host, slot, servers) {
            return r;
        }
    }
    let mut args: Vec<OsString> = cfg.args.iter().map(OsString::from).collect();
    args.extend(host.iter().map(OsString::from));
    for p in &pre {
        args.push("--prelude".into());
        args.push(p.into());
    }
    args.push("--module-dir".into());
    args.push(dir.into());
    args.extend(source_args(fm).into_iter().map(OsString::from));
    args.push(file.into());
    let (out, err) = (
        cfg.scratch.join(format!("{slot}.out")),
        cfg.scratch.join(format!("{slot}.err")),
    );
    let t0 = Instant::now();
    // Under a memory cap, ecma-run writes no snapshot (ECMA_SNAPSHOT) whose writing would pass it: about 1.5 KB a cell.
    let mut command = Command::new(&cfg.program);
    command.args(&args);
    if cfg.rss_cap > 0 && std::env::var_os("ECMA_SNAPSHOT_MAX_CELLS").is_none() {
        command.env("ECMA_SNAPSHOT_MAX_CELLS", (cfg.rss_cap / 1500).max(1).to_string());
    }
    let ran = run_with_timeout(&mut command, &out, &err, cfg.timeout, cfg.rss_cap);
    let took = t0.elapsed();
    let o = match ran {
        Run::TimedOut => Outcome::new(Bucket::Timeout, format!("{}: wall clock", PROGRAM)),
        Run::RssCap => Outcome::new(Bucket::Timeout, format!("{}: rss cap", PROGRAM)),
        Run::Error(e) => Outcome::new(Bucket::Fail, format!("{}: {e}", PROGRAM)),
        Run::Exited(sig) => {
            let stdout = std::fs::read_to_string(&out).unwrap_or_default();
            let mut lines = stdout.lines().map(String::from);
            let line = lines.next().unwrap_or_default();
            let printed: Vec<String> = lines.collect();
            match sig {
                Some(sig) if line.trim().is_empty() => crash_outcome(sig),
                _ => outcome_of(fm, line.trim(), &printed),
            }
        }
    };
    (o, took)
}

/// The job on the worker's server; `None` when the server cannot answer it (it died but not
/// of a signal, or went over the RSS cap with other tests' state: the job then runs as a process).
fn serve_job(
    cfg: &RunConfig,
    fm: &Frontmatter,
    file: &Path,
    pre: &[PathBuf],
    dir: &Path,
    host: &[&'static str],
    slot: usize,
    servers: &mut RunServers,
) -> Option<(Outcome, Duration)> {
    // The host options set up the realm the preludes run in: the warm-up has them too.
    let opts: String = host
        .iter()
        .map(|a| format!("{a} "))
        .chain(pre.iter().map(|p| format!("--prelude {} ", p.display())))
        .collect();
    let warm = format!("{opts}--module-dir {}", dir.display());
    let job: String = source_args(fm).iter().map(|a| format!(" {a}")).collect();
    let fields = [file.display().to_string(), format!("{warm}{job}")];
    // OPTIONS split at spaces: a path with one runs as a process.
    let spaced = pre.iter().map(PathBuf::as_path).chain([dir]).any(|p| p.to_string_lossy().contains(' '));
    if spaced || fields.iter().any(|f| f.contains(['\t', '\n'])) {
        return None;
    }
    let limit = |what: &str, took| {
        let what = format!("{}: {what}", PROGRAM);
        Some((Outcome::new(Bucket::Timeout, what), took))
    };
    let warmed = servers.server.as_ref().is_some_and(|s| s.warmed.contains(&(pre.to_vec(), host.to_vec())));
    if !pre.is_empty() && !warmed && cfg.cold.over(pre, cfg.warm_timeout) {
        return limit("harness: wall clock", Duration::ZERO);
    }
    if servers.server.is_none() {
        servers.server = Some(Server::start(&cfg.program, &cfg.args).ok()?);
    }
    let server = servers.server.as_mut().expect("started");
    if !pre.is_empty() && !warmed {
        // The harness alone, so that the job's limit and time are the test's.
        let empty = cfg.scratch.join(format!("{slot}.warm.js"));
        std::fs::write(&empty, "").ok()?;
        let fresh = server.fresh(pre, host);
        match server.ask(&format!("{}\t{warm}", empty.display()), cfg.warm_timeout, cfg.rss_cap) {
            Ok(_) => {
                server.warmed.insert((pre.to_vec(), host.to_vec()));
            }
            Err(Ended::TimedOut) => {
                servers.kill();
                cfg.cold.record(pre, cfg.warm_timeout);
                return limit("harness: wall clock", Duration::ZERO);
            }
            Err(Ended::RssCap) if fresh => {
                servers.kill();
                return limit("harness: rss cap", Duration::ZERO);
            }
            Err(_) => {
                servers.kill();
                return None;
            }
        }
    }
    let server = servers.server.as_mut().expect("started");
    let fresh = server.fresh(pre, host);
    let t0 = Instant::now();
    let answer = server.ask(&fields.join("\t"), cfg.timeout, cfg.rss_cap);
    let took = t0.elapsed();
    let o = match answer {
        Ok(records) => {
            let (line, printed) = parse_records(&records);
            outcome_of(fm, &line, &printed)
        }
        Err(Ended::TimedOut) => {
            servers.kill();
            return limit("wall clock", took);
        }
        // Over the cap with only this test's harness cached: the test's; else as a process, alone.
        Err(Ended::RssCap) if fresh => {
            servers.kill();
            return limit("rss cap", took);
        }
        // A server that died of a signal crashed on this job; otherwise it runs as a process.
        Err(Ended::Died) => return servers.died().map(|sig| (crash_outcome(sig), took)),
        Err(Ended::RssCap | Ended::Unwritten) => {
            servers.kill();
            return None;
        }
    };
    let server = servers.server.as_mut().expect("started");
    server.jobs += 1;
    let large = over_rss(server.child.id(), cfg.max_rss);
    servers.large += usize::from(large);
    if (cfg.serve_jobs > 0 && server.jobs >= cfg.serve_jobs) || large {
        servers.stop();
    }
    Some((o, took))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontmatter;

    fn fm(yaml: &str) -> Frontmatter {
        frontmatter::parse(&format!("/*---\n{yaml}\n---*/")).unwrap()
    }

    #[test]
    fn outcomes() {
        let plain = fm("description: x");
        let o = |f: &Frontmatter, l: &str| {
            let o = outcome_of(f, l, &[]);
            (o.bucket, o.detail)
        };
        assert_eq!(o(&plain, "normal: undefined"), (Bucket::Pass, "".into()));
        assert_eq!(
            o(&plain, "throw: [object #9] (constructor Test262Error)"),
            (Bucket::Fail, "throw: [object #9] (constructor Test262Error)".into())
        );
        assert_eq!(
            o(&plain, "stop: residue sdo:MV ?"),
            (Bucket::Stop, "residue:sdo:MV ?".into())
        );
        assert_eq!(
            o(&plain, "stop: residue sec-x#0 2.d.i"),
            (Bucket::Stop, "residue:sec-x#0 2.d.i".into())
        );
        assert_eq!(o(&plain, "stop: outOfFuel"), (Bucket::FuelTimeout, "outOfFuel".into()));
        assert_eq!(
            o(&plain, "stop: outOfFuel sec-runtime-semantics-canonicalize-ch#0 1"),
            (Bucket::FuelTimeout, "outOfFuel:sec-runtime-semantics-canonicalize-ch#0 1".into())
        );
        assert_eq!(
            o(&plain, "stop: outOfFuel ph-copies-appended#0 2.a"),
            (Bucket::FuelTimeout, "outOfFuel:ph-copies-appended#0 2.a".into())
        );
        assert_eq!(o(&plain, "stop: residue ? ?"), (Bucket::Stop, "residue:? ?".into()));
        assert_eq!(
            o(&plain, "stop: unsupported --web-browser"),
            (Bucket::Unsupported, "--web-browser".into())
        );
        assert_eq!(o(&plain, "abrupt: break").0, Bucket::Fail);
        assert_eq!(o(&plain, "").0, Bucket::Fail);
        assert_eq!(o(&plain, "stop: cannot read x: e").0, Bucket::Fail);
    }

    #[test]
    fn negative_outcomes() {
        let parse = fm("negative:\n  phase: parse\n  type: SyntaxError");
        let runtime = fm("negative:\n  phase: runtime\n  type: Test262Error");
        let b = |f: &Frontmatter, l: &str| outcome_of(f, l, &[]).bucket;
        assert_eq!(b(&parse, "throw: SyntaxError: x"), Bucket::Pass);
        assert_eq!(b(&parse, "throw: SyntaxError"), Bucket::Pass);
        assert_eq!(b(&parse, "throw: ReferenceError: $DONOTEVALUATE"), Bucket::Fail);
        assert_eq!(b(&parse, "normal: undefined"), Bucket::Fail);
        assert_eq!(b(&parse, "stop: residue sdo:MV ?"), Bucket::Stop);
        assert_eq!(b(&runtime, "throw: [object #3] (constructor Test262Error)"), Bucket::Pass);
        assert_eq!(b(&runtime, "throw: TypeError"), Bucket::Fail);
        let resolution = fm("flags: [module]\nnegative:\n  phase: resolution\n  type: SyntaxError");
        assert_eq!(b(&resolution, "throw: SyntaxError: x"), Bucket::Pass);
        assert_eq!(b(&resolution, "normal: undefined"), Bucket::Fail);
    }

    #[test]
    fn module_runs() {
        let parse = fm("flags: [module]\nnegative:\n  phase: parse\n  type: SyntaxError");
        let resolution = fm("flags: [module]\nnegative:\n  phase: resolution\n  type: SyntaxError");
        let script = fm("negative:\n  phase: parse\n  type: SyntaxError");
        assert_eq!(source_args(&parse), vec!["--module", "--parse-only"]);
        assert_eq!(source_args(&resolution), vec!["--module"]);
        assert!(source_args(&script).is_empty());
        assert_eq!(agent_args(&fm("flags: [CanBlockIsTrue]"), false), vec!["--can-block"]);
        assert_eq!(agent_args(&fm(""), true), vec!["--can-block"]);
        assert!(agent_args(&fm("flags: [CanBlockIsFalse]"), false).is_empty());
        assert!(prelude_names(&parse).is_empty());
        assert_eq!(prelude_names(&resolution), vec!["assert.js", "sta.js"]);
        assert_eq!(prelude_names(&script), vec!["assert.js", "sta.js"]);
    }

    #[test]
    fn async_and_records() {
        let a = fm("flags: [async]");
        let recs: Vec<String> = ["outcome\tnormal: undefined", "print\tTest262:AsyncTestComplete", "site\t-", "cpu\t5"]
            .map(String::from)
            .to_vec();
        let (line, printed) = parse_records(&recs);
        assert_eq!(outcome_of(&a, &line, &printed).bucket, Bucket::Pass);
        assert_eq!(outcome_of(&a, &line, &[]).bucket, Bucket::Fail);
        let recs = vec!["outcome\tthrow: Error: a\\tb\\\\c\\nd".to_string()];
        assert_eq!(parse_records(&recs).0, "throw: Error: a\tb\\c\nd");
    }

    #[test]
    fn unsupported_reasons() {
        let none = |_: &str| None;
        let r = |_: &str, f: &Frontmatter, src: &str| unsupported_reason(f, src, none);
        assert_eq!(r("language/a.js", &fm("flags: [module]"), ""), None);
        assert_eq!(r("language/a.js", &fm("flags: [module]\nfeatures: [import-attributes, json-modules]"), ""), None);
        assert_eq!(r("language/a.js", &fm("flags: [CanBlockIsTrue]"), ""), None);
        assert_eq!(r("annexB/a.js", &fm("description: x"), ""), None);
        assert_eq!(r("language/a.js", &fm("description: x"), "var o = $262.createRealm();"), None);
        assert_eq!(
            r("language/a.js", &fm("description: x"), "$262.createRealm(); $262.gc()"),
            Some("$262.gc".into())
        );
        assert_eq!(
            r("language/a.js", &fm("description: x"), "var o = $262.createRealm(); o.gc()"),
            Some("$262.gc".into())
        );
        assert_eq!(r("language/a.js", &fm("description: x"), "o.gc()"), None);
        assert_eq!(r("language/a.js", &fm("description: x"), "var o = $262.createRealm(); o.gcs"), None);
        assert_eq!(r("language/a.js", &fm("description: x"), "$262.evalScript(s)"), None);
        assert_eq!(r("language/a.js", &fm("description: x"), "var o = $262.createRealm(); o.evalScript(s)"), None);
        assert_eq!(r("language/a.js", &fm("description: x"), "x($262, $262.global)"), None);
        assert_eq!(
            r("language/a.js", &fm("description: x"), "$262.detachArrayBuffer(b); $262.gc()"),
            Some("$262.gc".into())
        );
        assert_eq!(r("language/a.js", &fm("flags: [async, raw]"), "print(1)"), None);
        assert_eq!(r("annexB/a.js", &fm("features: [IsHTMLDDA]"), "var d = $262.IsHTMLDDA;"), None);
        assert_eq!(r("annexB/a.js", &fm("description: x"), "var o = $262.createRealm(); o.IsHTMLDDA"), None);
        let inc = fm("includes: [detachArrayBuffer.js]");
        let h = |n: &str| (n == "detachArrayBuffer.js").then(|| "$262.detachArrayBuffer(b)".to_string());
        assert_eq!(unsupported_reason(&inc, "", h), None);
        let h = |n: &str| (n == "detachArrayBuffer.js").then(|| "$262.gc()".to_string());
        assert_eq!(
            unsupported_reason(&inc, "", h),
            Some("$262.gc".into())
        );
    }

    #[test]
    fn modes() {
        assert!(mode_args("default").unwrap().is_empty());
        assert_eq!(mode_args("checked").unwrap(), vec!["--checked"]);
        assert_eq!(mode_args("plain").unwrap(), vec!["--no-accel"]);
        assert_eq!(mode_args("plain-checked").unwrap(), vec!["--no-accel", "--checked"]);
        assert!(mode_args("other").is_none());
        let extra = ["--max-heap".to_string(), "7".to_string()];
        assert_eq!(
            run_args("default", &extra).unwrap(),
            vec!["--max-heap", "7"]
        );
        assert_eq!(
            run_args("plain", &extra).unwrap(),
            vec!["--no-accel", "--max-heap", "7"]
        );
        assert!(run_args("other", &[]).is_none());
    }

    #[test]
    fn coverage_stops() {
        assert!(stops_coverage(Bucket::Stop) && stops_coverage(Bucket::Timeout) && stops_coverage(Bucket::FuelTimeout));
        assert!(!stops_coverage(Bucket::Pass) && !stops_coverage(Bucket::Fail));
    }

    #[test]
    fn warm_limits() {
        assert_eq!(default_warm_timeout(Duration::from_secs(120)), Duration::from_secs(240));
        assert_eq!(default_warm_timeout(Duration::from_secs(600)), WARM_CAP);
        let cold = ColdHarness::default();
        let pre = vec![PathBuf::from("a.js")];
        cold.record(&pre, Duration::from_secs(240));
        assert!(cold.over(&pre, Duration::from_secs(240)) && cold.over(&pre, Duration::from_secs(60)));
        assert!(!cold.over(&pre, Duration::from_secs(480)) && !cold.over(&[], Duration::from_secs(1)));
    }

    /// A scratch directory with the program `script` (a shell script) and a config to run it.
    #[cfg(unix)]
    fn fake(name: &str, script: &str, serve: bool, warm_timeout: Duration) -> RunConfig {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("test262-runner-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let program = dir.join("ecma-run");
        std::fs::write(&program, format!("#!/bin/sh\n{script}")).unwrap();
        std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o755)).unwrap();
        RunConfig {
            test262: dir.clone(),
            program,
            args: vec![],
            timeout: Duration::from_secs(20),
            warm_timeout,
            cold: ColdHarness::default(),
            scratch: dir,
            stage: Stage::default(),
            serve,
            serve_jobs: 0,
            max_rss: 0,
            rss_cap: 0,
        }
    }

    #[cfg(unix)]
    #[test]
    fn warm_up_over_its_limit() {
        // A server whose warm-up job never ends.
        let script = "while IFS= read -r l; do case \"$l\" in *.warm.js*) sleep 60;; esac\n\
                      printf 'outcome\\tnormal: undefined\\n.\\n'; done\n";
        let warm = Duration::from_millis(500);
        let cfg = fake("warm", script, true, warm);
        let test = cfg.scratch.join("t.js");
        let inc = fm("includes: [slow.js]");
        let mut servers = RunServers::default();
        let t0 = Instant::now();
        let (o, _) = run_mode(&cfg, &inc, "", &test, false, 0, &mut servers);
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Timeout, "ecma-run: harness: wall clock"));
        assert!(o.is_wall_clock_timeout() && t0.elapsed() >= warm && servers.server.is_none());
        // The same harness again, on another worker: a timeout at once, no server started.
        let mut other = RunServers::default();
        let t1 = Instant::now();
        let (o, _) = run_mode(&cfg, &inc, "", &test, true, 1, &mut other);
        assert_eq!(o.bucket, Bucket::Timeout);
        assert!(t1.elapsed() < warm && other.server.is_none());
        // A test without a harness runs.
        let (o, _) = run_mode(&cfg, &fm("flags: [raw]"), "", &test, false, 1, &mut other);
        assert_eq!(o.bucket, Bucket::Pass);
        // A longer limit warms it again.
        let longer = RunConfig {
            warm_timeout: 2 * warm,
            ..cfg.clone()
        };
        let t2 = Instant::now();
        let (o, _) = run_mode(&longer, &inc, "", &test, false, 1, &mut other);
        assert_eq!(o.bucket, Bucket::Timeout);
        assert!(t2.elapsed() >= 2 * warm);
        servers.stop();
        other.stop();
        let _ = std::fs::remove_dir_all(&cfg.scratch);
    }

    #[cfg(unix)]
    #[test]
    fn killed_by_sigabrt() {
        for serve in [true, false] {
            let cfg = fake(&format!("abrt-{serve}"), "kill -ABRT $$\n", serve, Duration::from_secs(5));
            let test = cfg.scratch.join("t.js");
            for f in [fm("flags: [raw]"), fm("description: x")] {
                let mut servers = RunServers::default();
                let (o, _) = run_mode(&cfg, &f, "", &test, false, 0, &mut servers);
                assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Stop, "crash:SIGABRT"), "serve {serve}");
                servers.stop();
            }
            let _ = std::fs::remove_dir_all(&cfg.scratch);
        }
        // A server that crashes on its job: the crash, not a process run's answer.
        let served = "case \" $* \" in *\" --serve \"*) read l; kill -ABRT $$;; *) echo 'normal: undefined';; esac\n";
        let cfg = fake("abrt-served", served, true, Duration::from_secs(5));
        let mut servers = RunServers::default();
        let (o, _) = run_mode(&cfg, &fm("flags: [raw]"), "", &cfg.scratch.join("t.js"), false, 0, &mut servers);
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Stop, "crash:SIGABRT"));
        let process = RunConfig {
            serve: false,
            ..cfg.clone()
        };
        let (o, _) = run_mode(&process, &fm("flags: [raw]"), "", &cfg.scratch.join("t.js"), false, 0, &mut servers);
        assert_eq!(o.bucket, Bucket::Pass);
        let _ = std::fs::remove_dir_all(&cfg.scratch);
        assert_eq!(crash_outcome(11).detail, "crash:SIGSEGV");
        assert_eq!(crash_outcome(64).detail, "crash:signal 64");
    }

    /// A server that answers a warm-up at once and runs `job` (shell) for any other request.
    #[cfg(unix)]
    fn served(job: &str) -> String {
        format!(
            "case \" $* \" in *\" --serve \"*) while IFS= read -r l; do case \"$l\" in \
             *.warm.js*) printf 'outcome\\tnormal: undefined\\n.\\n';; *) {job};; esac; done;; \
             *) echo 'normal: undefined';; esac\n"
        )
    }

    #[cfg(unix)]
    #[test]
    fn job_over_its_limit() {
        // A job that never answers, and one whose records never end: each a timeout at its limit.
        let flood = "while :; do printf 'print\\tx\\n'; done";
        for (name, job) in [("silent", "sleep 60"), ("flood", flood)] {
            let cfg = RunConfig {
                timeout: Duration::from_secs(1),
                ..fake(&format!("limit-{name}"), &served(job), true, Duration::from_secs(5))
            };
            let mut servers = RunServers::default();
            let t0 = Instant::now();
            let (o, took) = run_mode(&cfg, &fm("flags: [async]"), "", &cfg.scratch.join("t.js"), false, 0, &mut servers);
            assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Timeout, "ecma-run: wall clock"), "{name}");
            assert!(took >= cfg.timeout && t0.elapsed() < Duration::from_secs(10), "{name}");
            assert!(servers.server.is_none());
            let _ = std::fs::remove_dir_all(&cfg.scratch);
        }
    }

    #[cfg(unix)]
    #[test]
    fn async_tests_end_at_their_limit() {
        // A server that answers by the source: an async test that never calls $DONE waits, one whose job queue
        // never drains prints forever, any other completes; at its input's end it does not exit.
        let script = "case \" $* \" in *\" --serve \"*) while IFS= read -r l; do f=$(printf '%s' \"$l\" | cut -f1); \
                      if grep -q NEVER_DONE \"$f\"; then sleep 60; \
                      elif grep -q JOBS_FOREVER \"$f\"; then while :; do printf 'print\\tjob\\n'; done; \
                      else printf 'outcome\\tnormal: undefined\\nprint\\tTest262:AsyncTestComplete\\n.\\n'; fi; done; \
                      sleep 60;; esac\n";
        let cfg = RunConfig {
            timeout: Duration::from_secs(1),
            ..fake("async", script, true, Duration::from_secs(5))
        };
        let (harness, tests) = (cfg.test262.join("harness"), cfg.test262.join("test"));
        std::fs::create_dir_all(&harness).unwrap();
        std::fs::create_dir_all(&tests).unwrap();
        for h in ["assert.js", "sta.js", "doneprintHandle.js", "asyncHelpers.js"] {
            std::fs::write(harness.join(h), "").unwrap();
        }
        let head = "/*---\nflags: [async]\nincludes: [asyncHelpers.js]\n---*/\n";
        for (t, body) in [("never-done.js", "NEVER_DONE"), ("jobs-forever.js", "JOBS_FOREVER"), ("done.js", "$DONE();")] {
            std::fs::write(tests.join(t), format!("{head}{body}\n")).unwrap();
        }
        let h = Harness::load(&cfg.test262, ["asyncHelpers.js".to_string()]).unwrap();
        let mut servers = RunServers::default();
        for t in ["never-done.js", "jobs-forever.js"] {
            let t0 = Instant::now();
            let o = run_test(&cfg, &h, t, 0, &mut servers);
            let took = t0.elapsed();
            assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Timeout, "non-strict: ecma-run: wall clock"), "{t}");
            // Its limit plus a margin: the strict run is not tried after a timeout.
            assert!(took >= cfg.timeout && took < cfg.timeout + Duration::from_secs(3), "{t}: {took:?}");
            assert!(servers.server.is_none(), "{t}");
            // The next test runs, on a new server.
            assert_eq!(run_test(&cfg, &h, "done.js", 0, &mut servers).bucket, Bucket::Pass, "{t}");
            assert!(servers.server.is_some(), "{t}");
        }
        // A server that does not exit at its input's end is killed after the grace.
        let t0 = Instant::now();
        servers.stop();
        assert!(t0.elapsed() < DEATH_GRACE + Duration::from_secs(3) && servers.server.is_none());
        let _ = std::fs::remove_dir_all(&cfg.scratch);
    }

    #[cfg(unix)]
    #[test]
    fn over_the_rss_cap() {
        // About 200 MB in the shell's memory, against a 64 MB cap.
        let grow = "x=$(head -c 200000000 /dev/zero | tr '\\0' a); sleep 60";
        let cap = 64 << 20;
        let process = RunConfig {
            rss_cap: cap,
            ..fake("rss-process", &format!("{grow}\n"), false, Duration::from_secs(5))
        };
        let mut servers = RunServers::default();
        let t0 = Instant::now();
        let (o, _) = run_mode(&process, &fm("flags: [raw]"), "", &process.scratch.join("t.js"), false, 0, &mut servers);
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Timeout, "ecma-run: rss cap"));
        assert!(t0.elapsed() < Duration::from_secs(15) && !o.is_wall_clock_timeout());
        let _ = std::fs::remove_dir_all(&process.scratch);
        // On a server that ran only this test's harness: the test's.
        let job = format!("case \"$l\" in */7.js*) {grow};; *) printf 'outcome\\tnormal: undefined\\n.\\n';; esac");
        let cfg = RunConfig {
            rss_cap: cap,
            ..fake("rss-served", &served(&job), true, Duration::from_secs(5))
        };
        let t = cfg.scratch.join("t.js");
        let mut servers = RunServers::default();
        let (o, _) = run_mode(&cfg, &fm("description: x"), "", &t, false, 7, &mut servers);
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Timeout, "ecma-run: rss cap"));
        assert!(servers.server.is_none());
        // After another test's job: run again as a process, alone (here it passes).
        let (o, _) = run_mode(&cfg, &fm("description: x"), "", &t, false, 0, &mut servers);
        assert_eq!(o.bucket, Bucket::Pass);
        let (o, _) = run_mode(&cfg, &fm("description: x"), "", &t, false, 7, &mut servers);
        assert_eq!(o.bucket, Bucket::Pass);
        assert!(servers.server.is_none());
        let _ = std::fs::remove_dir_all(&cfg.scratch);
    }

    #[cfg(unix)]
    #[test]
    fn server_killed_from_outside() {
        // SIGKILL not sent by the runner (an OOM killer's): the job's crash, not a process run's answer.
        let cfg = fake("sigkill", &served("kill -KILL $$"), true, Duration::from_secs(5));
        let mut servers = RunServers::default();
        let (o, _) = run_mode(&cfg, &fm("description: x"), "", &cfg.scratch.join("t.js"), false, 0, &mut servers);
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Stop, "crash:SIGKILL"));
        assert!(servers.server.is_none());
        let _ = std::fs::remove_dir_all(&cfg.scratch);
    }

    #[cfg(unix)]
    #[test]
    fn web_browser_paths_run_with_web_browser() {
        // Passes only when its options say `--web-browser`, as a process and on a server.
        let process = "case \" $* \" in *\" --web-browser \"*) echo 'normal: undefined';; *) echo 'throw: x';; esac\n";
        let job = "case \"$l\" in *--web-browser*) printf 'outcome\\tnormal: undefined\\n.\\n';; \
                   *) printf 'outcome\\tthrow: x\\n.\\n';; esac";
        let stage = Stage::parse("[paths]\nannexB\nlanguage\n[web-browser-paths]\nannexB\n").unwrap();
        for (name, script, serve) in [("web-process", process.to_string(), false), ("web-served", served(job), true)] {
            let cfg = RunConfig {
                stage: stage.clone(),
                ..fake(name, &script, serve, Duration::from_secs(5))
            };
            let root = cfg.test262.join("test");
            let mut servers = RunServers::default();
            for (t, want) in [("annexB/t.js", Bucket::Pass), ("language/t.js", Bucket::Fail)] {
                for f in [fm("flags: [raw]"), fm("description: x")] {
                    let (o, _) = run_mode(&cfg, &f, "", &root.join(t), false, 0, &mut servers);
                    assert_eq!(o.bucket, want, "{name} {t}");
                }
            }
            servers.stop();
            let _ = std::fs::remove_dir_all(&cfg.scratch);
        }
    }
}
