//! Run tc39/test262 (`external/test262`) on `ecma-run` (the specification's driver: the
//! machine).
//!
//! * [`frontmatter`] reads a test's metadata.
//! * [`Stage`] is a stage's configuration (`tests/test262/<stage>.conf`):
//!   the directories it runs, the test262 features it allows, and the flags
//!   it skips.
//! * [`run`] runs one test in each mode its flags ask for and puts it in one
//!   [`Bucket`]; a model stop is the bucket `stop`, out of fuel `timeout(fuel)`.
//! * [`Expected`] is the expected-results file
//!   (`tests/expected/<stage>/<mode>.txt`) and [`compare`] checks a run against it.
//! * [`plan`] is the work queue, grouped by harness.
//! * [`results`] is the results file a run appends to and resumes from.

pub mod frontmatter;
pub mod plan;
pub mod results;
pub mod run;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Mutex, MutexGuard};
use std::time::{Duration, Instant};

use frontmatter::{Frontmatter, Phase};

/// Where a test ends up. Ordered by how bad it is: two runs of one test
/// (non-strict and strict) combine to the worse bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bucket {
    /// The test ran and passed.
    Pass,
    /// Not run: a feature outside the stage's allow-list, or a skipped flag.
    Skip,
    /// The program stopped with `unsupported`, or the test needs a flag or
    /// host hook the test host does not have.
    Unsupported,
    /// ecma-run's model stopped (a residue step, a failed Assert): the detail
    /// is `<kind>:<site>`.
    Stop,
    /// Over the wall-clock limit or the resident memory cap.
    Timeout,
    /// Out of fuel (call depth or a loop's rounds), `timeout(fuel)`: a
    /// timeout kept apart from the wall clock's; the detail is `outOfFuel:<site>`.
    FuelTimeout,
    /// The test failed: an uncaught exception, a missing expected error, or
    /// a valid program rejected.
    Fail,
    /// The program stopped at a failed `Assert` (always a bug).
    AssertFailed,
}

impl Bucket {
    pub const ALL: [Bucket; 8] = [
        Bucket::Pass,
        Bucket::Fail,
        Bucket::Unsupported,
        Bucket::Stop,
        Bucket::AssertFailed,
        Bucket::Timeout,
        Bucket::FuelTimeout,
        Bucket::Skip,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Bucket::Pass => "pass",
            Bucket::Skip => "skip",
            Bucket::Unsupported => "unsupported",
            Bucket::Stop => "stop",
            Bucket::Timeout => "timeout",
            Bucket::FuelTimeout => "timeout(fuel)",
            Bucket::Fail => "fail",
            Bucket::AssertFailed => "assertFailed",
        }
    }

    pub fn from_name(s: &str) -> Option<Bucket> {
        Bucket::ALL.into_iter().find(|b| b.name() == s)
    }

    /// A timeout of either kind, wall clock or fuel.
    pub fn is_timeout(self) -> bool {
        matches!(self, Bucket::Timeout | Bucket::FuelTimeout)
    }
}

/// A test's result: its bucket, a one-line reason, and the milliseconds its
/// runs took (set by the caller that timed them).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub bucket: Bucket,
    pub detail: String,
    pub ms: Option<u64>,
    /// The milliseconds of the test's work, its servers' starts and harness runs included.
    pub cost_ms: Option<u64>,
}

impl Outcome {
    fn new(bucket: Bucket, detail: impl Into<String>) -> Self {
        Outcome {
            bucket,
            detail: detail.into(),
            ms: None,
            cost_ms: None,
        }
    }

    /// A `timeout` by the wall-clock limit (not the rss cap, not
    /// `timeout(fuel)`): one that depends on the machine's load.
    pub fn is_wall_clock_timeout(&self) -> bool {
        self.bucket == Bucket::Timeout && self.detail.ends_with("wall clock")
    }
}

/// A stage's configuration file: `[paths]`, `[exclude]`, `[features]`,
/// `[skip-features]`, `[skip-flags]`, `[host]` and `[web-browser-paths]`
/// sections, one entry per line, `#` comments.
#[derive(Debug, Clone, Default)]
pub struct Stage {
    /// Directories or files under `test262/test` that the stage runs.
    pub paths: Vec<String>,
    /// Directories or files under `paths` that the stage does not run, unless
    /// a test is named by itself (`TESTS`, `--tests-from`).
    pub exclude: Vec<String>,
    /// The test262 features a test may use (`*`: every feature not in
    /// `skip_features`).
    pub features: HashSet<String>,
    /// With `*` in `features`: the features a test may not use.
    pub skip_features: HashSet<String>,
    /// Tests with any of these flags are skipped (`async`, `module`, …).
    pub skip_flags: HashSet<String>,
    /// `[host]` `web-browser`: the tests run on the web-browser host (Annex B,
    /// ecma-run's `--web-browser`).
    pub web_browser: bool,
    /// `[web-browser-paths]`: directories or files under `paths` whose tests
    /// run on the web-browser host even when `[host]` does not say
    /// `web-browser` (the `annexB` tests of a full-suite stage).
    pub web_browser_paths: Vec<String>,
}

impl Stage {
    pub fn parse(text: &str) -> Result<Stage, String> {
        let mut stage = Stage::default();
        let mut section = String::new();
        for (n, raw) in text.lines().enumerate() {
            let line = raw.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                section = name.to_string();
                continue;
            }
            match section.as_str() {
                "paths" => stage.paths.push(line.to_string()),
                "exclude" => stage.exclude.push(line.trim_end_matches('/').to_string()),
                "skip-features" => {
                    stage.skip_features.insert(line.to_string());
                }
                "host" if line == "web-browser" => stage.web_browser = true,
                "web-browser-paths" => stage.web_browser_paths.push(line.trim_end_matches('/').to_string()),
                "features" => {
                    stage.features.insert(line.to_string());
                }
                "skip-flags" => {
                    stage.skip_flags.insert(line.to_string());
                }
                _ => return Err(format!("line {}: entry outside a known section", n + 1)),
            }
        }
        Ok(stage)
    }

    /// Whether `test` (relative to `test262/test`) lies under `[exclude]`.
    pub fn excludes(&self, test: &str) -> bool {
        self.exclude.iter().any(|x| test == x || test.strip_prefix(x.as_str()).is_some_and(|r| r.starts_with('/')))
    }

    /// Whether `test` (relative to `test262/test`) runs on the web-browser
    /// host: every test of a `[host] web-browser` stage, and the tests under
    /// `[web-browser-paths]`.
    pub fn web_browser_for(&self, test: &str) -> bool {
        self.web_browser
            || self
                .web_browser_paths
                .iter()
                .any(|p| test == p || test.strip_prefix(p.as_str()).is_some_and(|r| r.starts_with('/')))
    }
}

/// The harness files, read once.
#[derive(Debug, Default)]
pub struct Harness {
    files: HashMap<String, String>,
}

impl Harness {
    /// Read `assert.js`, `sta.js`, `doneprintHandle.js` (for `async` tests)
    /// and every file a test includes.
    pub fn load(test262: &Path, names: impl IntoIterator<Item = String>) -> Result<Harness, String> {
        let mut files = HashMap::new();
        let always = ["assert.js", "sta.js", "doneprintHandle.js"].map(String::from);
        for name in always.into_iter().chain(names) {
            if files.contains_key(&name) {
                continue;
            }
            let path = test262.join("harness").join(&name);
            let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            files.insert(name, text);
        }
        Ok(Harness { files })
    }

    fn get(&self, name: &str) -> Option<&str> {
        self.files.get(name).map(String::as_str)
    }
}

/// Every test file under `paths` (relative to `test262/test`), sorted, as
/// paths relative to `test262/test`. `_FIXTURE` files are not tests.
pub fn collect_tests(test262: &Path, paths: &[String]) -> Result<Vec<String>, String> {
    let root = test262.join("test");
    let mut out = Vec::new();
    for p in paths {
        let full = root.join(p);
        if full.is_file() {
            out.push(p.clone());
        } else if full.is_dir() {
            walk(&root, &full, &mut out)?;
        } else {
            return Err(format!("{}: no such test file or directory", full.display()));
        }
    }
    out.retain(|p| p.ends_with(".js") && !p.contains("_FIXTURE"));
    out.sort();
    out.dedup();
    Ok(out)
}

/// Shard `index` of `count` (`0 <= index < count`) of the sorted `tests`:
/// every `count`-th test, from the `index`-th. Interleaving spreads a slow
/// directory (RegExp's property escapes, say) over every shard.
pub fn shard(tests: Vec<String>, index: usize, count: usize) -> Vec<String> {
    tests
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % count == index)
        .map(|(_, t)| t)
        .collect()
}

/// A list of tests, one per line (paths under `test262/test`), `#` comments:
/// the tests a `--allow-timeout` file lets end in `timeout`.
pub fn parse_test_list(text: &str) -> BTreeSet<String> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .map(String::from)
        .collect()
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.is_dir() {
            walk(root, &path, out)?;
        } else if let Ok(rel) = path.strip_prefix(root) {
            out.push(rel.to_string_lossy().replace('\\', "/"));
        }
    }
    Ok(())
}

/// Read a test's frontmatter (for collecting includes before the run).
pub fn read_frontmatter(test262: &Path, test: &str) -> Result<(String, Frontmatter), String> {
    let path = test262.join("test").join(test);
    let source = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let fm = frontmatter::parse(&source)?;
    Ok((source, fm))
}

/// Why a test is skipped, if it is.
pub fn skip_reason(stage: &Stage, fm: &Frontmatter) -> Option<String> {
    if let Some(flag) = fm.flags.iter().find(|f| stage.skip_flags.contains(*f)) {
        return Some(format!("flag {flag}"));
    }
    if let Some(n) = &fm.negative {
        if n.phase == Phase::Resolution && stage.skip_flags.contains("module") {
            return Some("negative phase resolution (modules)".into());
        }
    }
    let mut missing: Vec<&str> = fm
        .features
        .iter()
        .filter(|f| {
            if stage.features.contains("*") {
                stage.skip_features.contains(*f)
            } else {
                !stage.features.contains(*f)
            }
        })
        .map(String::as_str)
        .collect();
    if !missing.is_empty() {
        missing.sort();
        return Some(format!("feature {}", missing.join(", ")));
    }
    None
}

/// The outcome of an `async` test whose Script completed normally, from the
/// lines `print` wrote after the result line (INTERPRETING.md): it
/// passes when `$DONE` printed `Test262:AsyncTestComplete`, and fails when it
/// printed `Test262:AsyncTestFailure:…` or was never called.
fn async_outcome(stdout: &str) -> Outcome {
    for printed in stdout.lines().skip(1) {
        let printed = printed.trim_end();
        if printed == "Test262:AsyncTestComplete" {
            return Outcome::new(Bucket::Pass, "");
        }
        if let Some(failure) = printed.strip_prefix("Test262:AsyncTestFailure:") {
            return Outcome::new(Bucket::Fail, format!("async: {failure}"));
        }
    }
    Outcome::new(Bucket::Fail, "async: $DONE was not called")
}

/// Whether the `throw: <value>` line shows an error of `error_type`.
/// An uncaught error object prints as `<name>` or `<name>: <message>`, its
/// "name" being the native error type (`throw: TypeError: …`). Any other
/// expected type (such as Test262Error, an ordinary object made by the
/// harness) must be an object that is not an error object and whose
/// constructor has that name, which prints as `[object #n] (constructor
/// <name>)`: a thrown TypeError, plain object or primitive does not count.
/// The check reads the "name" the program prints (of an error object, or of its
/// constructor), not the constructor's identity: an error whose "name" was
/// changed counts as the type it names.
fn throws(line: &str, error_type: &str) -> bool {
    const NATIVE: [&str; 8] = [
        "Error",
        "EvalError",
        "RangeError",
        "ReferenceError",
        "SyntaxError",
        "TypeError",
        "URIError",
        "AggregateError",
    ];
    let Some(value) = line.strip_prefix("throw: ") else {
        return false;
    };
    if NATIVE.contains(&error_type) {
        value == error_type || value.starts_with(&format!("{error_type}: "))
    } else {
        value.starts_with("[object #") && value.ends_with(&format!(" (constructor {error_type})"))
    }
}

/// How a job ended.
pub(crate) enum Run {
    /// Ended by itself (its result line, not its status, says how), or by the signal it holds.
    Exited(Option<i32>),
    TimedOut,
    /// Killed when its resident memory went over the cap.
    RssCap,
    Error(String),
}

/// Start `cmd` in a process group of its own (its pid), so that
/// [`kill_group`] reaches the processes it starts too, which would otherwise
/// outlive it and escape the runner's resource accounting.
pub(crate) fn own_group(cmd: &mut Command) -> &mut Command {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }
    cmd
}

/// Kill `child` and its process group (started by [`own_group`]), and reap it.
pub(crate) fn kill_group(child: &mut std::process::Child) {
    #[cfg(unix)]
    {
        if let Ok(pid) = i32::try_from(child.id()) {
            // SAFETY: kill(2) on the group whose id is the child's pid (SIGKILL = 9);
            // the child is not reaped yet, so the id is still its own.
            unsafe { kill(-pid, 9) };
        }
    }
    let _ = child.kill();
    reap(child);
}

/// The process groups of the children [`spawn_group`] started and nobody reaped yet.
static GROUPS: Mutex<BTreeSet<u32>> = Mutex::new(BTreeSet::new());

/// The signal that stops the run (0: none yet).
static STOP: AtomicI32 = AtomicI32::new(0);

fn groups() -> MutexGuard<'static, BTreeSet<u32>> {
    GROUPS.lock().unwrap_or_else(|e| e.into_inner())
}

/// Spawn `cmd` in a process group of its own ([`own_group`]), recorded until [`reap`]ed.
pub(crate) fn spawn_group(cmd: &mut Command) -> std::io::Result<std::process::Child> {
    let mut groups = groups();
    let child = own_group(cmd).spawn()?;
    groups.insert(child.id());
    Ok(child)
}

/// Wait for `child` (from [`spawn_group`]) and forget its group.
pub(crate) fn reap(child: &mut std::process::Child) {
    let _ = child.wait();
    groups().remove(&child.id());
}

/// Whether a signal (or stdin's end, [`stop_on_signals`]) is stopping the run.
pub fn stopping() -> bool {
    STOP.load(Ordering::SeqCst) != 0
}

#[cfg(unix)]
extern "C" {
    fn signal(sig: i32, handler: usize) -> usize;
    fn kill(pid: i32, sig: i32) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn raise(sig: i32) -> i32;
}

#[cfg(unix)]
extern "C" fn on_signal(sig: i32) {
    STOP.store(sig, Ordering::SeqCst);
}

/// Kill the process groups of `children` (each its leader's pid) and wait for the leaders.
#[cfg(unix)]
fn kill_groups(children: &BTreeSet<u32>) {
    for &pid in children {
        if let Ok(pid) = i32::try_from(pid) {
            // SAFETY: kill(2) on a child's group (SIGKILL = 9), waitpid(2) on that child.
            unsafe {
                kill(-pid, 9);
                waitpid(pid, std::ptr::null_mut(), 0);
            }
        }
    }
}

/// On SIGINT, SIGTERM or SIGHUP (and, with `stdin`, at stdin's end: a parent's lifeline),
/// kill the children's process groups, remove `scratch` and die of that signal (SIGTERM).
#[cfg(unix)]
pub fn stop_on_signals(stdin: bool, scratch: PathBuf) {
    const SIGHUP: i32 = 1;
    const SIGINT: i32 = 2;
    const SIGTERM: i32 = 15;
    for sig in [SIGHUP, SIGINT, SIGTERM] {
        // SAFETY: the handler only stores to an atomic.
        unsafe { signal(sig, on_signal as extern "C" fn(i32) as usize) };
    }
    if stdin {
        std::thread::spawn(|| {
            let _ = std::io::copy(&mut std::io::stdin().lock(), &mut std::io::sink());
            let _ = STOP.compare_exchange(0, SIGTERM, Ordering::SeqCst, Ordering::SeqCst);
        });
    }
    std::thread::spawn(move || loop {
        let sig = STOP.load(Ordering::SeqCst);
        if sig != 0 {
            // Held to the end: no child starts after the kill.
            let held = groups();
            kill_groups(&held);
            let _ = std::fs::remove_dir_all(&scratch);
            let n = held.len();
            eprintln!("test262-runner: stopped (signal {sig}): {n} child process group(s) killed");
            // SAFETY: back to the default action, then that signal to this thread.
            unsafe {
                signal(sig, 0);
                raise(sig);
            }
            std::process::exit(128 + sig);
        }
        std::thread::sleep(Duration::from_millis(50));
    });
}

#[cfg(not(unix))]
pub fn stop_on_signals(_stdin: bool, _scratch: PathBuf) {}

/// The signal that ended a process with `status`, if one did.
pub(crate) fn killed_by(status: std::process::ExitStatus) -> Option<i32> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        status.signal()
    }
    #[cfg(not(unix))]
    {
        let _ = status;
        None
    }
}

/// A signal's name (`SIGABRT`), or `signal N`.
pub fn signal_name(sig: i32) -> String {
    let name = match sig {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        5 => "SIGTRAP",
        6 => "SIGABRT",
        8 => "SIGFPE",
        9 => "SIGKILL",
        11 => "SIGSEGV",
        13 => "SIGPIPE",
        15 => "SIGTERM",
        #[cfg(target_os = "linux")]
        7 => "SIGBUS",
        #[cfg(target_os = "macos")]
        10 => "SIGBUS",
        _ => return format!("signal {sig}"),
    };
    name.to_string()
}

/// How often a run's resident memory is read against its cap.
pub(crate) const RSS_POLL: Duration = Duration::from_millis(250);

/// Whether the process `pid`'s resident memory is over `cap` bytes (0: no cap).
pub(crate) fn over_rss(pid: u32, cap: u64) -> bool {
    cap > 0 && rss_bytes(pid).is_some_and(|b| b > cap)
}

/// The resident memory of the process `pid`, in bytes, where the system says
/// (macOS: `proc_pidinfo`; Linux: `/proc/PID/statm`).
#[cfg(target_os = "macos")]
pub(crate) fn rss_bytes(pid: u32) -> Option<u64> {
    extern "C" {
        fn proc_pidinfo(pid: i32, flavor: i32, arg: u64, buffer: *mut u8, size: i32) -> i32;
    }
    // `struct proc_taskinfo` (<sys/proc_info.h>): 96 bytes, its second field
    // `pti_resident_size`; flavor PROC_PIDTASKINFO = 4.
    let mut info = [0u64; 12];
    let size = std::mem::size_of_val(&info) as i32;
    // SAFETY: proc_pidinfo writes at most `size` bytes into `info`.
    let n = unsafe { proc_pidinfo(pid as i32, 4, 0, info.as_mut_ptr().cast(), size) };
    (n == size).then_some(info[1])
}

#[cfg(target_os = "linux")]
pub(crate) fn rss_bytes(pid: u32) -> Option<u64> {
    let statm = std::fs::read_to_string(format!("/proc/{pid}/statm")).ok()?;
    let pages: u64 = statm.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages * 4096)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn rss_bytes(_pid: u32) -> Option<u64> {
    None
}

/// Run `cmd` with stdout to `out` and stderr to `err`, killing it (and its
/// process group) after `timeout` or once its resident memory is over `rss_cap` bytes (0: no cap).
pub(crate) fn run_with_timeout(cmd: &mut Command, out: &Path, err: &Path, timeout: Duration, rss_cap: u64) -> Run {
    let (Ok(o), Ok(e)) = (File::create(out), File::create(err)) else {
        return Run::Error("cannot create scratch files".into());
    };
    let mut child = match spawn_group(cmd.stdin(Stdio::null()).stdout(o).stderr(e)) {
        Ok(c) => c,
        Err(e) => return Run::Error(e.to_string()),
    };
    let start = Instant::now();
    let mut pause = Duration::from_millis(1);
    let mut polled = start;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                groups().remove(&child.id());
                return Run::Exited(killed_by(status));
            }
            Ok(None) if start.elapsed() >= timeout => {
                kill_group(&mut child);
                return Run::TimedOut;
            }
            Ok(None) => {
                if rss_cap > 0 && polled.elapsed() >= RSS_POLL {
                    polled = Instant::now();
                    if over_rss(child.id(), rss_cap) {
                        kill_group(&mut child);
                        return Run::RssCap;
                    }
                }
                std::thread::sleep(pause);
                pause = (pause * 2).min(Duration::from_millis(20));
            }
            Err(e) => {
                groups().remove(&child.id());
                return Run::Error(e.to_string());
            }
        }
    }
}

/// The expected-results file: `<bucket> <test>` per line, `#` comments.
/// Skipped tests are not listed.
#[derive(Debug, Clone, Default)]
pub struct Expected {
    pub results: BTreeMap<String, Bucket>,
}

impl Expected {
    pub fn parse(text: &str) -> Result<Expected, String> {
        let mut results = BTreeMap::new();
        for (n, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (b, test) = line
                .split_once(' ')
                .ok_or_else(|| format!("line {}: expected `<bucket> <test>`", n + 1))?;
            let bucket = Bucket::from_name(b).ok_or_else(|| format!("line {}: unknown bucket {b:?}", n + 1))?;
            results.insert(test.trim().to_string(), bucket);
        }
        Ok(Expected { results })
    }

    /// Record the results of a run: tests that ran replace their entries,
    /// skipped tests are dropped, and tests that did not run are kept.
    pub fn update(&mut self, run: &BTreeMap<String, Outcome>) {
        for (test, o) in run {
            if o.bucket == Bucket::Skip {
                self.results.remove(test);
            } else {
                self.results.insert(test.clone(), o.bucket);
            }
        }
    }

    pub fn render(&self, header: &str) -> String {
        let mut s = String::new();
        for l in header.lines() {
            s.push_str("# ");
            s.push_str(l);
            s.push('\n');
        }
        for (test, b) in &self.results {
            s.push_str(b.name());
            s.push(' ');
            s.push_str(test);
            s.push('\n');
        }
        s
    }
}

/// How a run differs from the expected results.
#[derive(Debug, Default)]
pub struct Comparison {
    /// Expected to pass, and did not.
    pub regressions: Vec<(String, Bucket, Outcome)>,
    /// Passed, but expected not to: update the expected file.
    pub unexpected_passes: Vec<(String, Bucket)>,
    /// Other changes of bucket, and tests the file does not list (`None`).
    pub changes: Vec<(String, Option<Bucket>, Bucket)>,
    /// Ended in `timeout`, which the allow-list permits, though expected
    /// otherwise (not a regression).
    pub allowed_timeouts: Vec<(String, Bucket)>,
}

impl Comparison {
    pub fn is_ok(&self) -> bool {
        self.regressions.is_empty() && self.unexpected_passes.is_empty()
    }
}

/// Compare the tests that ran with the expected results. A test in
/// `allow_timeout` may end in `timeout` whatever its expected bucket.
pub fn compare(expected: &Expected, run: &BTreeMap<String, Outcome>, allow_timeout: &BTreeSet<String>) -> Comparison {
    let mut c = Comparison::default();
    for (test, o) in run {
        let was = expected.results.get(test).copied();
        match (was, o.bucket) {
            (_, Bucket::Skip) => {}
            (Some(w), now) if w == now => {}
            (Some(w), Bucket::Timeout) if allow_timeout.contains(test) => c.allowed_timeouts.push((test.clone(), w)),
            (Some(Bucket::Pass), _) => c.regressions.push((test.clone(), Bucket::Pass, o.clone())),
            (Some(w), Bucket::Pass) => c.unexpected_passes.push((test.clone(), w)),
            (w, now) => c.changes.push((test.clone(), w, now)),
        }
    }
    c
}

/// Counts per bucket, for a directory or the whole run.
#[derive(Debug, Clone, Default)]
pub struct Counts {
    pub by_bucket: [usize; 8],
}

impl Counts {
    pub fn add(&mut self, b: Bucket) {
        self.by_bucket[Bucket::ALL.iter().position(|x| *x == b).unwrap_or(0)] += 1;
    }

    pub fn get(&self, b: Bucket) -> usize {
        self.by_bucket[Bucket::ALL.iter().position(|x| *x == b).unwrap_or(0)]
    }

    /// Tests that ran (everything but `skip`).
    pub fn ran(&self) -> usize {
        self.by_bucket.iter().sum::<usize>() - self.get(Bucket::Skip)
    }
}

/// The directory of `test` cut to `depth` components (`language/expressions/addition`).
pub fn directory(test: &str, depth: usize) -> String {
    let parts: Vec<&str> = test.split('/').collect();
    let dirs = &parts[..parts.len().saturating_sub(1)];
    dirs[..dirs.len().min(depth)].join("/")
}

/// The per-directory summary table.
pub fn summary(run: &BTreeMap<String, Outcome>, depth: usize) -> String {
    let mut dirs: BTreeMap<String, Counts> = BTreeMap::new();
    let mut total = Counts::default();
    for (test, o) in run {
        dirs.entry(directory(test, depth)).or_default().add(o.bucket);
        total.add(o.bucket);
    }
    let width = dirs.keys().map(String::len).max().unwrap_or(0).max(9);
    let mut s = format!(
        "{:width$}  {:>6} {:>6} {:>11} {:>6} {:>12} {:>7} {:>13} {:>6}  {:>6}\n",
        "directory", "pass", "fail", "unsupported", "stop", "assertFailed", "timeout", "timeout(fuel)", "skip", "pass%"
    );
    let mut row = |name: &str, c: &Counts| {
        let pct = if c.ran() == 0 {
            "-".to_string()
        } else {
            format!("{:.1}", 100.0 * c.get(Bucket::Pass) as f64 / c.ran() as f64)
        };
        s.push_str(&format!(
            "{:width$}  {:>6} {:>6} {:>11} {:>6} {:>12} {:>7} {:>13} {:>6}  {:>6}\n",
            name,
            c.get(Bucket::Pass),
            c.get(Bucket::Fail),
            c.get(Bucket::Unsupported),
            c.get(Bucket::Stop),
            c.get(Bucket::AssertFailed),
            c.get(Bucket::Timeout),
            c.get(Bucket::FuelTimeout),
            c.get(Bucket::Skip),
            pct
        ));
    };
    for (d, c) in &dirs {
        row(d, c);
    }
    row("total", &total);
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn stop_kills_child_groups() {
        let mut child = spawn_group(
            Command::new("sh")
                .args(["-c", "sleep 60 & echo $!; wait"])
                .stdout(Stdio::piped()),
        )
        .unwrap();
        let mut line = String::new();
        std::io::BufRead::read_line(&mut std::io::BufReader::new(child.stdout.take().unwrap()), &mut line).unwrap();
        let grandchild: i32 = line.trim().parse().unwrap();
        assert!(groups().contains(&child.id()));
        kill_groups(&BTreeSet::from([child.id()]));
        // The leader is reaped already; its child, killed with the group, is gone once its new parent reaps it.
        assert!(child.try_wait().is_err());
        let deadline = Instant::now() + Duration::from_secs(5);
        // SAFETY: kill(2) with signal 0 only checks that the process exists.
        while unsafe { kill(grandchild, 0) } == 0 {
            assert!(Instant::now() < deadline, "grandchild {grandchild} survived");
            std::thread::sleep(Duration::from_millis(20));
        }
        groups().remove(&child.id());
    }

    #[test]
    fn stage_config() {
        let s = Stage::parse("# c\n[paths]\nlanguage/expressions\n[features]\nlet # ES2015\n[skip-flags]\nasync\n")
            .unwrap();
        assert_eq!(s.paths, vec!["language/expressions"]);
        assert!(s.features.contains("let"));
        assert!(s.skip_flags.contains("async"));
        assert!(Stage::parse("stray\n").is_err());
    }

    #[test]
    fn web_browser_paths() {
        let s = Stage::parse("[paths]\nannexB\nlanguage\n[web-browser-paths]\nannexB/\n").unwrap();
        assert!(!s.web_browser);
        assert!(s.web_browser_for("annexB/language/x.js"));
        assert!(!s.web_browser_for("annexBx/y.js"));
        assert!(!s.web_browser_for("language/annexB/z.js"));
        let all = Stage::parse("[host]\nweb-browser\n").unwrap();
        assert!(all.web_browser_for("language/z.js"));
    }

    #[test]
    fn excludes() {
        let s = Stage::parse("[paths]\nstaging\n[exclude]\nstaging/sm/\n").unwrap();
        assert!(s.excludes("staging/sm/x.js"));
        assert!(s.excludes("staging/sm"));
        assert!(!s.excludes("staging/smx/y.js"));
        assert!(!s.excludes("staging/z.js"));
    }

    #[test]
    fn skipping() {
        let stage = Stage::parse("[features]\nlet\n[skip-flags]\nmodule\n").unwrap();
        let fm = frontmatter::parse("/*---\nfeatures: [let, Symbol]\n---*/").unwrap();
        assert_eq!(skip_reason(&stage, &fm), Some("feature Symbol".into()));
        let fm = frontmatter::parse("/*---\nflags: [module]\n---*/").unwrap();
        assert_eq!(skip_reason(&stage, &fm), Some("flag module".into()));
        let fm = frontmatter::parse("/*---\nfeatures: [let]\nflags: [onlyStrict]\n---*/").unwrap();
        assert_eq!(skip_reason(&stage, &fm), None);
    }

    #[test]
    fn expected_file_round_trip_and_compare() {
        let e = Expected::parse("# h\npass a/x.js\nunsupported a/y.js\nfail a/z.js\n").unwrap();
        let mut run = BTreeMap::new();
        run.insert("a/x.js".to_string(), Outcome::new(Bucket::Fail, "throw: 1"));
        run.insert("a/y.js".to_string(), Outcome::new(Bucket::Pass, ""));
        run.insert("a/z.js".to_string(), Outcome::new(Bucket::Unsupported, "sec-x"));
        run.insert("a/w.js".to_string(), Outcome::new(Bucket::Skip, "feature Symbol"));
        let c = compare(&e, &run, &BTreeSet::new());
        assert_eq!(c.regressions.len(), 1);
        assert_eq!(c.unexpected_passes, vec![("a/y.js".to_string(), Bucket::Unsupported)]);
        assert_eq!(
            c.changes,
            vec![("a/z.js".to_string(), Some(Bucket::Fail), Bucket::Unsupported)]
        );
        assert!(!c.is_ok());
        let mut e2 = e.clone();
        e2.update(&run);
        let text = e2.render("h");
        assert_eq!(text, "# h\nfail a/x.js\npass a/y.js\nunsupported a/z.js\n");
        assert_eq!(Expected::parse(&text).unwrap().results.len(), 3);
    }

    #[test]
    fn allowed_timeouts() {
        let e = Expected::parse("pass a/x.js\npass a/y.js\n").unwrap();
        let mut run = BTreeMap::new();
        run.insert(
            "a/x.js".to_string(),
            Outcome::new(Bucket::Timeout, "ecma-run: wall clock"),
        );
        run.insert("a/y.js".to_string(), Outcome::new(Bucket::FuelTimeout, "outOfFuel:sec-x#0 1"));
        let allow = parse_test_list("# the slow one\na/x.js  # wall clock\na/y.js\n\n");
        assert_eq!(allow.len(), 2);
        let c = compare(&e, &run, &allow);
        assert_eq!(c.allowed_timeouts, vec![("a/x.js".to_string(), Bucket::Pass)]);
        assert_eq!(c.regressions.len(), 1);
        assert!(!c.is_ok());
        assert!(run["a/x.js"].is_wall_clock_timeout());
        assert!(!run["a/y.js"].is_wall_clock_timeout());
        assert!(Bucket::FuelTimeout.is_timeout() && Bucket::Timeout.is_timeout() && !Bucket::Stop.is_timeout());
    }

    #[test]
    fn fuel_timeout_kept_apart() {
        let e = Expected::parse("timeout(fuel) a/x.js\ntimeout a/y.js\n").unwrap();
        assert_eq!(e.results["a/x.js"], Bucket::FuelTimeout);
        assert_eq!(e.render(""), "timeout(fuel) a/x.js\ntimeout a/y.js\n");
        let mut run = BTreeMap::new();
        run.insert("a/x.js".to_string(), Outcome::new(Bucket::Timeout, "ecma-run: wall clock"));
        run.insert("a/y.js".to_string(), Outcome::new(Bucket::FuelTimeout, "outOfFuel:sec-x#0 1"));
        let c = compare(&e, &run, &BTreeSet::new());
        assert_eq!(c.changes.len(), 2);
        let s = summary(&run, 1);
        let head: Vec<&str> = s.lines().next().unwrap().split_whitespace().collect();
        let total: Vec<&str> = s.lines().last().unwrap().split_whitespace().collect();
        assert_eq!(head[6..8], ["timeout", "timeout(fuel)"]);
        assert_eq!(total[6..8], ["1", "1"]);
    }

    #[test]
    fn shards() {
        let tests: Vec<String> = (0..7).map(|i| format!("t{i}.js")).collect();
        let parts: Vec<Vec<String>> = (0..3).map(|i| shard(tests.clone(), i, 3)).collect();
        assert_eq!(parts[0], vec!["t0.js", "t3.js", "t6.js"]);
        assert_eq!(parts[2], vec!["t2.js", "t5.js"]);
        let mut all: Vec<String> = parts.concat();
        all.sort();
        assert_eq!(all, tests);
    }

    #[test]
    fn throw_lines() {
        assert!(throws("throw: TypeError", "TypeError"));
        assert!(throws("throw: TypeError: not a function", "TypeError"));
        assert!(!throws("throw: TypeErrorX", "TypeError"));
        assert!(!throws("throw: RangeError", "TypeError"));
        assert!(!throws("throw: Error", "TypeError"));
        assert!(throws("throw: [object #3] (constructor Test262Error)", "Test262Error"));
        assert!(!throws("throw: [object #3]", "Test262Error"));
        assert!(!throws("throw: [object #3] (constructor Object)", "Test262Error"));
        assert!(!throws("throw: TypeError", "Test262Error"));
        assert!(!throws("throw: Error: m", "Test262Error"));
        assert!(!throws("throw: 1", "Test262Error"));
        assert!(!throws("normal: 1", "Test262Error"));
    }

    #[test]
    fn async_results() {
        assert_eq!(
            async_outcome("normal: undefined\nTest262:AsyncTestComplete\n").bucket,
            Bucket::Pass
        );
        let o = async_outcome("normal: undefined\nx\nTest262:AsyncTestFailure:Test262Error: m\n");
        assert_eq!((o.bucket, o.detail.as_str()), (Bucket::Fail, "async: Test262Error: m"));
        assert_eq!(async_outcome("normal: undefined\n").bucket, Bucket::Fail);
        // The result line itself is not printed output.
        assert_eq!(async_outcome("Test262:AsyncTestComplete\n").bucket, Bucket::Fail);
    }

    #[test]
    fn directories() {
        assert_eq!(
            directory("language/expressions/addition/S1.js", 3),
            "language/expressions/addition"
        );
        assert_eq!(directory("language/expressions/a/b/c.js", 2), "language/expressions");
        assert_eq!(directory("x.js", 3), "");
    }
}
