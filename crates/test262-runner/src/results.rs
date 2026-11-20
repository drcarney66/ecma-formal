//! The results file (`--results`): `# build <id>`, then a row per test as it completes
//! ([`result_row`]), so that a stopped run keeps what it finished and a restarted one
//! with the same file and build runs only the rest ([`ResultsLog::open`]).

use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use crate::{Bucket, Outcome};

/// The build a run's rows are of: an FNV-1a hash of the tools' bytes, then `config`.
pub fn build_id(tools: &[&Path], config: &str) -> Result<String, String> {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut buf = vec![0u8; 1 << 20];
    for t in tools {
        let mut f = File::open(t).map_err(|e| format!("{}: {e}", t.display()))?;
        loop {
            let n = f.read(&mut buf).map_err(|e| format!("{}: {e}", t.display()))?;
            if n == 0 {
                break;
            }
            for &b in &buf[..n] {
                h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
            }
        }
    }
    Ok(format!("{h:016x} {config}").trim_end().to_string())
}

/// A test's row: `<test>\t<bucket>\t<ms>\t<detail>\t<cost>` (`-`: no time).
pub fn result_row(test: &str, o: &Outcome) -> String {
    let time = |v: Option<u64>| v.map_or("-".to_string(), |m| m.to_string());
    format!(
        "{test}\t{}\t{}\t{}\t{}\n",
        o.bucket.name(),
        time(o.ms),
        o.detail.replace(['\t', '\n'], " "),
        time(o.cost_ms)
    )
}

/// The rows of a results file of build `id` (later rows win; a torn last line is
/// dropped); `None` when the file is of no build or another.
pub fn parse_results(text: &str, id: &str) -> Option<BTreeMap<String, Outcome>> {
    let mut lines = text.split_inclusive('\n').filter(|l| l.ends_with('\n'));
    if lines.next()?.trim_end() != format!("# build {id}") {
        return None;
    }
    let mut out = BTreeMap::new();
    for line in lines {
        let line = line.trim_end_matches('\n');
        if line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        let Some(bucket) = f.get(1).and_then(|b| Bucket::from_name(b)) else {
            continue;
        };
        let time = |i: usize| f.get(i).and_then(|v| v.parse().ok());
        out.insert(
            f[0].to_string(),
            Outcome {
                bucket,
                detail: f.get(3).unwrap_or(&"").to_string(),
                ms: time(2),
                cost_ms: time(4),
            },
        );
    }
    Some(out)
}

/// The results file a run appends its rows to.
pub struct ResultsLog {
    path: PathBuf,
    id: String,
    file: Mutex<File>,
}

impl ResultsLog {
    /// Open `path` for build `id`: the rows it already has for that build (a resume),
    /// rewritten without a torn last line; any other file's rows are dropped.
    pub fn open(path: &Path, id: &str) -> Result<(ResultsLog, BTreeMap<String, Outcome>), String> {
        let err = |e: std::io::Error| format!("{}: {e}", path.display());
        let kept = match std::fs::read_to_string(path) {
            Ok(text) => parse_results(&text, id).unwrap_or_default(),
            Err(_) => BTreeMap::new(),
        };
        let log = ResultsLog {
            path: path.to_path_buf(),
            id: id.to_string(),
            file: Mutex::new(OpenOptions::new().create(true).append(true).open(path).map_err(err)?),
        };
        log.finish(&kept)?;
        Ok((log, kept))
    }

    /// Append a completed test's row (one write, unbuffered); none once the run is stopping.
    pub fn append(&self, test: &str, o: &Outcome) -> Result<(), String> {
        if crate::stopping() {
            return Ok(());
        }
        self.write(&result_row(test, o))
    }

    /// Replace the file by `results`, one row per test, sorted.
    pub fn finish(&self, results: &BTreeMap<String, Outcome>) -> Result<(), String> {
        let tmp = self.path.with_extension("tmp");
        let err = |p: &Path, e: std::io::Error| format!("{}: {e}", p.display());
        std::fs::write(&tmp, self.render(results)).map_err(|e| err(&tmp, e))?;
        std::fs::rename(&tmp, &self.path).map_err(|e| err(self.path.as_path(), e))?;
        let file = OpenOptions::new()
            .append(true)
            .open(&self.path)
            .map_err(|e| err(self.path.as_path(), e))?;
        *self.file.lock().expect("results file") = file;
        Ok(())
    }

    fn render(&self, results: &BTreeMap<String, Outcome>) -> String {
        let mut s = format!("# build {}\n", self.id);
        for (t, o) in results {
            s.push_str(&result_row(t, o));
        }
        s
    }

    fn write(&self, text: &str) -> Result<(), String> {
        let mut f = self.file.lock().expect("results file");
        f.write_all(text.as_bytes())
            .and_then(|()| f.flush())
            .map_err(|e| format!("{}: {e}", self.path.display()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn outcome(bucket: Bucket, detail: &str, ms: u64) -> Outcome {
        Outcome {
            bucket,
            detail: detail.into(),
            ms: Some(ms),
            cost_ms: Some(ms + 40),
        }
    }

    #[test]
    fn rows_round_trip() {
        let o = outcome(Bucket::Stop, "strict: residue:x\ty", 7);
        let text = format!("# build id1 default\n{}", result_row("a.js", &o));
        let got = parse_results(&text, "id1 default").expect("same build");
        assert_eq!(got["a.js"].detail, "strict: residue:x y");
        assert_eq!((got["a.js"].ms, got["a.js"].cost_ms), (Some(7), Some(47)));
        assert!(parse_results(&text, "id2 default").is_none());
        assert!(parse_results("a.js\tpass\t5\t\n", "id1 default").is_none());
        // Four columns (no cost), later rows win, a torn last line is dropped.
        let got = parse_results("# build b\na.js\tpass\t5\t\na.js\tfail\t6\tz\nb.js\tpa", "b").expect("same build");
        assert_eq!(got.len(), 1);
        assert_eq!((got["a.js"].bucket, got["a.js"].cost_ms), (Bucket::Fail, None));
    }

    #[test]
    fn append_and_resume() {
        let dir = std::env::temp_dir().join(format!("test262-results-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("r.tsv");
        let (log, kept) = ResultsLog::open(&path, "id1").unwrap();
        assert!(kept.is_empty());
        log.append("a.js", &outcome(Bucket::Pass, "", 5)).unwrap();
        log.append("b.js", &outcome(Bucket::Stop, "s", 6)).unwrap();
        // Stopped mid-row: the rows so far are on disk.
        std::fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(b"c.js\tpa")
            .unwrap();
        drop(log);
        let (log, kept) = ResultsLog::open(&path, "id1").unwrap();
        assert_eq!(kept.keys().collect::<Vec<_>>(), ["a.js", "b.js"]);
        log.append("c.js", &outcome(Bucket::Pass, "", 1)).unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        assert!(
            text.starts_with("# build id1\n") && text.ends_with("c.js\tpass\t1\t\t41\n"),
            "{text}"
        );
        let mut all = parse_results(&text, "id1").unwrap();
        all.insert("a.js".into(), outcome(Bucket::Fail, "again", 9));
        log.finish(&all).unwrap();
        log.append("d.js", &outcome(Bucket::Pass, "", 2)).unwrap();
        let got = parse_results(&std::fs::read_to_string(&path).unwrap(), "id1").unwrap();
        assert_eq!(got.len(), 4);
        assert_eq!(got["a.js"].bucket, Bucket::Fail);
        // Another build: the rows are dropped.
        let (_, kept) = ResultsLog::open(&path, "id2").unwrap();
        assert!(kept.is_empty());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "# build id2\n");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn build_ids() {
        let dir = std::env::temp_dir().join(format!("test262-build-id-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let (a, b) = (dir.join("a"), dir.join("b"));
        std::fs::write(&a, "one").unwrap();
        std::fs::write(&b, "two").unwrap();
        let id = build_id(&[&a], "--checked").unwrap();
        assert_eq!(id, build_id(&[&a], "--checked").unwrap());
        assert_ne!(id, build_id(&[&b], "--checked").unwrap());
        assert_ne!(id, build_id(&[&a], "--no-accel").unwrap());
        assert!(build_id(&[&dir.join("none")], "").is_err());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
