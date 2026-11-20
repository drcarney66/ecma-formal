//! The work queue of a run, by harness: a server's warm-up (ecma-run's preludes) is paid once
//! per worker and prelude list, so the tests are grouped by that list and a worker keeps to
//! one group while it has tests. A group of `n` of the run's `N` tests at `J` jobs takes at
//! most `ceil(n J / N)` workers (its share), and more only once a measured backlog per
//! worker is longer than the group's measured warm-up. Groups start in the listed order of
//! their first tests, and each group's tests run in the listed order.

use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

/// What a worker does next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Next {
    /// The test of this index.
    Test(usize),
    /// Nothing yet: tests are left, but none is worth a warm-up now ([`Plan::record`] may change that).
    Wait,
    /// No test is left.
    Done,
}

/// One harness's tests.
#[derive(Debug)]
struct Group {
    tests: VecDeque<usize>,
    /// The workers it may take before its backlog is measured.
    slots: usize,
    /// The workers that have joined it.
    joined: usize,
    /// The workers in it now.
    members: usize,
    /// Tests measured and their milliseconds (the jobs', without a warm-up).
    measured: u64,
    ms: u64,
    /// The latest warm-up measured: a joining worker's first test's cost over its time.
    warm_ms: Option<u64>,
}

impl Group {
    /// The group's measured backlog per worker, if it has tests, members and measurements.
    fn backlog_ms(&self) -> Option<u64> {
        if self.tests.is_empty() || self.members == 0 || self.measured == 0 {
            return None;
        }
        Some(self.tests.len() as u64 * (self.ms / self.measured) / self.members as u64)
    }
}

/// A worker's place.
#[derive(Debug, Clone, Copy, Default)]
struct Seat {
    group: Option<usize>,
    /// Its next recorded test is its first in the group (it paid the warm-up).
    fresh: bool,
}

/// The work queue ([module docs](self)).
#[derive(Debug)]
pub struct Plan {
    groups: Vec<Group>,
    seats: Vec<Seat>,
}

impl Plan {
    /// The plan for tests `0..keys.len()` in that (the listed) order, `keys[i]` test `i`'s harness, at `jobs` workers.
    pub fn new<K: Hash + Eq>(keys: &[K], jobs: usize) -> Plan {
        let jobs = jobs.max(1);
        let mut index: HashMap<&K, usize> = HashMap::new();
        let mut tests: Vec<VecDeque<usize>> = Vec::new();
        for (i, k) in keys.iter().enumerate() {
            let g = *index.entry(k).or_insert_with(|| {
                tests.push(VecDeque::new());
                tests.len() - 1
            });
            tests[g].push_back(i);
        }
        let n = keys.len().max(1);
        let groups = tests
            .into_iter()
            .map(|t| Group {
                slots: (t.len() * jobs).div_ceil(n),
                tests: t,
                joined: 0,
                members: 0,
                measured: 0,
                ms: 0,
                warm_ms: None,
            })
            .collect();
        Plan {
            groups,
            seats: vec![Seat::default(); jobs],
        }
    }

    /// Worker `w`'s next test: its group's next, else the first-listed group with a free share, else the group with the
    /// longest measured backlog per worker if that is over its warm-up.
    pub fn next(&mut self, w: usize) -> Next {
        if let Some(g) = self.seats[w].group {
            if let Some(t) = self.groups[g].tests.pop_front() {
                return Next::Test(t);
            }
            self.groups[g].members -= 1;
            self.seats[w].group = None;
        }
        let open = |g: &Group| !g.tests.is_empty() && (g.joined < g.slots || g.members == 0);
        let pick = self
            .groups
            .iter()
            .enumerate()
            .filter(|(_, g)| open(g))
            .min_by_key(|(_, g)| g.tests[0])
            .map(|(i, _)| i)
            .or_else(|| {
                self.groups
                    .iter()
                    .enumerate()
                    .filter_map(|(i, g)| Some((i, g.backlog_ms()?, g.warm_ms?)))
                    .filter(|&(_, backlog, warm)| backlog > warm)
                    .max_by_key(|&(i, backlog, _)| (backlog, std::cmp::Reverse(i)))
                    .map(|(i, _, _)| i)
            });
        let Some(g) = pick else {
            return if self.groups.iter().any(|g| !g.tests.is_empty()) {
                Next::Wait
            } else {
                Next::Done
            };
        };
        let group = &mut self.groups[g];
        group.joined += 1;
        group.members += 1;
        self.seats[w] = Seat {
            group: Some(g),
            fresh: true,
        };
        Next::Test(group.tests.pop_front().expect("open group"))
    }

    /// Worker `w`'s latest test took `ms` of jobs and `cost_ms` in all (its server's start and warm-up included).
    pub fn record(&mut self, w: usize, ms: u64, cost_ms: u64) {
        let seat = &mut self.seats[w];
        let Some(g) = seat.group else { return };
        let group = &mut self.groups[g];
        group.measured += 1;
        group.ms += ms;
        if std::mem::take(&mut seat.fresh) {
            group.warm_ms = Some(cost_ms.saturating_sub(ms));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Run `keys` at `jobs` workers taking turns, each test `ms(i)` long and each warm-up `warm(key)`: every worker's
    /// sequence of (test, key).
    fn simulate(keys: &[&str], jobs: usize, ms: impl Fn(usize) -> u64, warm: impl Fn(&str) -> u64) -> Vec<Vec<usize>> {
        let mut plan = Plan::new(keys, jobs);
        let mut seqs = vec![Vec::new(); jobs];
        let mut done = vec![false; jobs];
        while done.iter().any(|d| !d) {
            for w in 0..jobs {
                if done[w] {
                    continue;
                }
                match plan.next(w) {
                    Next::Test(t) => {
                        let first = seqs[w].last().is_none_or(|&p: &usize| keys[p] != keys[t]);
                        let cost = ms(t) + if first { warm(keys[t]) } else { 0 };
                        plan.record(w, ms(t), cost);
                        seqs[w].push(t);
                    }
                    Next::Wait => {}
                    Next::Done => done[w] = true,
                }
            }
        }
        seqs
    }

    /// The keys a worker met, each once per run of it.
    fn runs<'a>(keys: &[&'a str], seq: &[usize]) -> Vec<&'a str> {
        let mut out: Vec<&str> = seq.iter().map(|&t| keys[t]).collect();
        out.dedup();
        out
    }

    fn mixed() -> Vec<&'static str> {
        (0..500)
            .map(|i| match i % 10 {
                0 => "propertyHelper",
                1 if i % 20 == 1 => "testTypedArray",
                2 | 3 => "compareArray",
                _ => "plain",
            })
            .collect()
    }

    #[test]
    fn every_test_once() {
        for (keys, jobs) in [
            (mixed(), 84),
            (mixed(), 1),
            (mixed(), 7),
            (vec!["a"; 3], 84),
            (vec![], 4),
        ] {
            let seqs = simulate(&keys, jobs, |i| 1 + (i as u64 % 7), |_| 50);
            let mut all: Vec<usize> = seqs.concat();
            all.sort();
            assert_eq!(all, (0..keys.len()).collect::<Vec<_>>(), "{jobs} jobs");
        }
    }

    #[test]
    fn sets_grouped() {
        let keys = mixed();
        let seqs = simulate(&keys, 84, |_| 10, |_| 180_000);
        for seq in &seqs {
            let r = runs(&keys, seq);
            let mut uniq = r.clone();
            uniq.sort();
            uniq.dedup();
            assert_eq!(r.len(), uniq.len(), "a worker came back to a set: {r:?}");
        }
        let workers = |k: &str| seqs.iter().filter(|s| s.iter().any(|&t| keys[t] == k)).count();
        // 50 propertyHelper tests in 500 at 84 jobs: its share is 9 workers, not one each.
        assert_eq!(workers("propertyHelper"), 9);
        assert_eq!(workers("testTypedArray"), 5);
        // Each set's tests in the listed order.
        for seq in &seqs {
            for k in ["propertyHelper", "plain"] {
                let mine: Vec<usize> = seq.iter().copied().filter(|&t| keys[t] == k).collect();
                assert!(mine.is_sorted());
            }
        }
    }

    #[test]
    fn listed_order_starts_groups() {
        let keys = ["b", "a", "b", "a", "c"];
        let mut plan = Plan::new(&keys, 2);
        assert_eq!(plan.next(0), Next::Test(0));
        assert_eq!(plan.next(1), Next::Test(1));
        assert_eq!(plan.next(1), Next::Test(3));
        assert_eq!(plan.next(1), Next::Test(4));
        assert_eq!(plan.next(0), Next::Test(2));
        assert_eq!(plan.next(0), Next::Done);
    }

    #[test]
    fn backlog_over_warm_up_takes_more() {
        // One worker's share; a second waits until the backlog is measured, then joins if it is over the warm-up.
        let keys = ["h"; 3];
        for (ms, warm, joins) in [(1000, 100, true), (10, 100_000, false)] {
            let mut plan = Plan::new(&keys, 2);
            plan.groups[0].slots = 1;
            assert_eq!(plan.next(0), Next::Test(0));
            assert_eq!(plan.next(1), Next::Wait);
            plan.record(0, ms, ms + warm);
            let n = plan.next(1);
            assert_eq!(n == Next::Test(1), joins, "{ms} ms, warm-up {warm}");
            if !joins {
                assert_eq!(n, Next::Wait);
            }
        }
    }
}
