//! The Assert ledger: every `Assert:` step and `!` of the algorithms, the overlay's algorithms and
//! its readings' steps, classed as checked mode treats it. Paths are numbered as `spec-gen steps`
//! numbers them (a closure's steps under the step that defines it); a reading's steps are numbered
//! from 1 under `<erratum id>/<clause>@<path>/<reading>`.

use crate::ast::{Arm, Body, Channel, CloLit, Cond, Expr, Hole, Node, Part, Pred, Reading, Stmt, TyExpr};
use crate::data::Data;
use crate::grammar::Grammar;
use crate::spec::{Spec, Step};
use std::collections::{BTreeMap, HashMap, HashSet};

/// The classes, in the header's order.
pub const CLASSES: &[&str] = &["formal", "definition", "open", "permanent-future", "permanent-provenance", "bang"];

/// A site: class, algorithm key (`sec-x#n` or an overlay id), path (`!k` for a step's k-th `!`,
/// k ≥ 2), and the step's text from the site on.
#[derive(Clone, Debug, PartialEq)]
pub struct Site {
    pub class: &'static str,
    pub key: String,
    pub path: String,
    pub text: String,
}

impl Site {
    pub fn line(&self) -> String {
        let t: String = self.text.chars().map(|c| if c.is_whitespace() { ' ' } else { c }).take(60).collect();
        format!("{}\t{}\t{}\t{}\n", self.class, self.key, self.path, t)
    }
}

/// Whether a channel gives its prose a meaning (a primitive applied to the holes).
fn meant(c: &Channel) -> bool {
    matches!(c, Channel::Prim(_, true) | Channel::Upstream(_, Some(_)) | Channel::Annotated(_, Some(_)))
}

/// Whether a condition has prose without a meaning anywhere in it.
fn open_cond(c: &Cond) -> bool {
    let mut open = false;
    Walk::default().cond(c, &mut |x| open |= matches!(x, Visit::Prose(ch) if !meant(ch)));
    open
}

enum Visit<'a> {
    Prose(&'a Channel),
    Bang,
}

/// A visitor over one step's expressions and conditions, not its nested steps.
#[derive(Default)]
struct Walk;

impl Walk {
    fn expr(&self, e: &Expr, f: &mut dyn FnMut(Visit)) {
        match e {
            Expr::Call(_, xs) | Expr::List(xs) => xs.iter().for_each(|x| self.expr(x, f)),
            Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
                self.expr(x, f);
                xs.iter().for_each(|x| self.expr(x, f));
            }
            Expr::Bang(x) | Expr::BangAt(_, x) => {
                f(Visit::Bang);
                self.expr(x, f);
            }
            Expr::Component(_, _, x) | Expr::Field(x, _) | Expr::Erratum(_, _, x) | Expr::Q(x) | Expr::Neg(x) | Expr::Paren(x) | Expr::Annot(_, x) | Expr::ResumedWith(x) | Expr::ChildOf(x, _, _) => self.expr(x, f),
            Expr::Index(x, y) | Expr::Bin(_, x, y) | Expr::TableStep(_, x, y) => {
                self.expr(x, f);
                self.expr(y, f);
            }
            Expr::Record(_, _, fs) => fs.iter().for_each(|(_, x)| self.expr(x, f)),
            Expr::Extreme(_, _, t, c) => {
                self.ty(t, f);
                self.cond(c, f);
            }
            Expr::Phrase(_, hs) => self.holes(hs, f),
            Expr::Prose(ch, ps) => {
                f(Visit::Prose(ch));
                self.parts(ps, f);
            }
            _ => {}
        }
    }

    fn pred(&self, p: &Pred, f: &mut dyn FnMut(Visit)) {
        match p {
            Pred::IsVal(_, _, xs) => xs.iter().for_each(|x| self.expr(x, f)),
            Pred::IsTy(_, _, ts) => ts.iter().for_each(|t| self.ty(t, f)),
            Pred::Phrase(_, hs) => self.holes(hs, f),
        }
    }

    fn cond(&self, c: &Cond, f: &mut dyn FnMut(Visit)) {
        match c {
            Cond::Preds(e, p, r) => {
                self.expr(e, f);
                self.pred(p, f);
                r.iter().for_each(|(_, p)| self.pred(p, f));
            }
            Cond::Rel(_, x, y) => {
                self.expr(x, f);
                self.expr(y, f);
            }
            Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().for_each(|c| self.cond(c, f)),
            Cond::Paren(c) => self.cond(c, f),
            Cond::Alg(..) => {}
            Cond::Phrase(_, hs) => self.holes(hs, f),
            Cond::Prose(ch, ps) => {
                f(Visit::Prose(ch));
                self.parts(ps, f);
            }
        }
    }

    fn ty(&self, t: &TyExpr, f: &mut dyn FnMut(Visit)) {
        match t {
            TyExpr::ListOf(_, x) => self.ty(x, f),
            TyExpr::Union(_, _, ts) => ts.iter().for_each(|t| self.ty(t, f)),
            TyExpr::Completion(x) => x.iter().for_each(|t| self.ty(t, f)),
            TyExpr::Interval(x, lo, hi) => {
                self.ty(x, f);
                self.expr(lo, f);
                self.expr(hi, f);
            }
            TyExpr::Value(e) => self.expr(e, f),
            TyExpr::Record(fs) => fs.iter().for_each(|(_, t)| self.ty(t, f)),
            TyExpr::That(x, p, r) => {
                self.ty(x, f);
                self.pred(p, f);
                r.iter().for_each(|(_, p)| self.pred(p, f));
            }
            TyExpr::Phrase(_, hs) => self.holes(hs, f),
            TyExpr::Prose(ps) => self.parts(ps, f),
            _ => {}
        }
    }

    /// Holes.
    fn holes(&self, hs: &[Hole], f: &mut dyn FnMut(Visit)) {
        for h in hs {
            match h {
                Hole::E(e) => self.expr(e, f),
                Hole::C(c) | Hole::Bc(_, c) => self.cond(c, f),
                Hole::T(t) => self.ty(t, f),
                Hole::L(_, xs) => xs.iter().for_each(|x| self.expr(x, f)),
                _ => {}
            }
        }
    }

    fn parts(&self, ps: &[Part], f: &mut dyn FnMut(Visit)) {
        for p in ps {
            if let Part::Hole(h) = p {
                self.holes(std::slice::from_ref(h), f);
            }
        }
    }
}

/// The label of the n-th step (from 1) at depth d: `1`, `a`, `i`.
pub(crate) fn label(d: usize, n: usize) -> String {
    match d % 3 {
        0 => n.to_string(),
        1 => {
            let (mut s, mut n) = (String::new(), n);
            while n > 0 {
                s.insert(0, char::from(b'a' + ((n - 1) % 26) as u8));
                n = (n - 1) / 26;
            }
            s
        }
        _ => crate::text::roman(n),
    }
}

/// The steps a node stands for: an If and its Else arms are one node.
pub(crate) fn width(n: &Node) -> usize {
    match &n.stmt {
        Stmt::If(_, _, arms, els) => 1 + arms.len() + els.iter().count(),
        Stmt::Readings(_, s, _) => match &**s {
            Stmt::If(_, _, arms, els) => 1 + arms.len() + els.iter().count(),
            _ => 1,
        },
        _ => 1,
    }
}

/// One algorithm's walk: its key, its clause, the texts of its steps by path, its closures.
struct Alg<'a> {
    key: String,
    clause: String,
    texts: HashMap<String, &'a str>,
    closures: &'a [CloLit],
    errata: &'a [crate::overlay::Erratum],
}

/// A raw site: key, path, what (`None`: a bang; `Some(open, definition)`: an Assert).
type Raw = (String, String, Option<(bool, bool)>, String);

impl Alg<'_> {
    fn text(&self, path: &str) -> &str {
        self.texts.get(path).copied().unwrap_or("")
    }

    fn nodes(&self, ns: &[Node], d: usize, pre: &str, out: &mut Vec<Raw>) {
        let mut i = 1;
        for n in ns {
            self.node(n, d, pre, i, out);
            i += width(n);
        }
    }

    fn node(&self, n: &Node, d: usize, pre: &str, i: usize, out: &mut Vec<Raw>) {
        let at = |k: usize| format!("{pre}{}", label(d, k));
        let (st, rd) = match &n.stmt {
            Stmt::Readings(e, s, alts) => (&**s, Some((*e, alts))),
            s => (s, None),
        };
        let definition = rd.is_some_and(|(_, alts)| alts.iter().any(|(r, _)| *r == Reading::Definition));
        if let Stmt::If(c, b, arms, els) = st {
            let mut bangs = 0;
            self.step_cond(c, &at(i), &mut bangs, out);
            self.body(b, d, &at(i), &mut bangs, false, out);
            for (k, a) in arms.iter().chain(els.iter()).enumerate() {
                self.arm(a, d, &at(i + 1 + k), out);
            }
        } else {
            self.stmt(st, d, &at(i), &mut 0, definition, out);
        }
        if let Some((e, alts)) = rd {
            self.alts(e, &at(i), alts, out);
        }
    }

    fn arm(&self, a: &Arm, d: usize, path: &str, out: &mut Vec<Raw>) {
        let mut bangs = 0;
        if let Some(c) = &a.cond {
            self.step_cond(c, path, &mut bangs, out);
        }
        self.body(&a.body, d, path, &mut bangs, false, out);
    }

    fn body(&self, b: &Body, d: usize, path: &str, bangs: &mut usize, definition: bool, out: &mut Vec<Raw>) {
        match b {
            Body::Inline(s) => self.stmt(s, d, path, bangs, definition, out),
            Body::Block(ns) => self.nodes(ns, d + 1, &format!("{path}."), out),
        }
    }

    /// An erratum's readings at `path`: each its own steps, under its overlay id.
    fn alts(&self, e: usize, path: &str, alts: &[(Reading, Vec<Node>)], out: &mut Vec<Raw>) {
        let Some(er) = self.errata.get(e) else { return };
        let Some(an) = er.readings.iter().find(|r| r.clause == self.clause && r.step == path) else { return };
        for alt in &an.alts {
            let first = crate::data::reading_of(alt.readings().next().unwrap_or_default());
            let Some((_, ns)) = alts.iter().find(|(r, _)| *r == first) else { continue };
            let sub = Alg {
                key: format!("{}/{}@{}/{}", er.id, an.clause, an.step, alt.key()),
                clause: self.clause.clone(),
                texts: crate::spec::labelled(&alt.steps).into_iter().map(|(p, s)| (p, s.text.as_str())).collect(),
                closures: self.closures,
                errata: self.errata,
            };
            sub.nodes(ns, 0, "", out);
        }
    }

    /// The `!`s and closures of a step's condition.
    fn step_cond(&self, c: &Cond, path: &str, bangs: &mut usize, out: &mut Vec<Raw>) {
        let mut n = 0;
        Walk.cond(c, &mut |x| n += matches!(x, Visit::Bang) as usize);
        self.push_bangs(n, path, bangs, out);
    }

    fn push_bangs(&self, n: usize, path: &str, bangs: &mut usize, out: &mut Vec<Raw>) {
        for _ in 0..n {
            *bangs += 1;
            let p = if *bangs == 1 { path.to_string() } else { format!("{path}!{bangs}") };
            out.push((self.key.clone(), p, None, bang_text(self.text(path), *bangs)));
        }
    }

    /// The closures an expression defines, walked as nested steps of `path`.
    fn closures_in(&self, st: &Stmt, d: usize, path: &str, out: &mut Vec<Raw>) {
        let mut ks = Vec::new();
        expr_closures(st, &mut ks);
        for k in ks {
            if let Some(c) = self.closures.get(k) {
                self.nodes(&c.body, d + 1, &format!("{path}."), out);
            }
        }
    }

    fn stmt(&self, st: &Stmt, d: usize, path: &str, bangs: &mut usize, definition: bool, out: &mut Vec<Raw>) {
        if let Stmt::WithSteps(s, ns) = st {
            self.stmt(s, d, path, bangs, definition, out);
            return self.nodes(ns, d + 1, &format!("{path}."), out);
        }
        let text = self.text(path).to_string();
        match st {
            Stmt::Assert(c) | Stmt::AssertAt(_, c) => {
                out.push((self.key.clone(), path.to_string(), Some((open_cond(c), definition)), text));
                self.step_cond(c, path, bangs, out);
                return;
            }
            Stmt::AssertIf(c, e) => {
                out.push((self.key.clone(), path.to_string(), Some((open_cond(c) || open_cond(e), definition)), text));
                self.step_cond(c, path, bangs, out);
                self.step_cond(e, path, bangs, out);
                return;
            }
            // `Assert: This step is never reached.`: it stops in every mode
            Stmt::Unreachable(_) => out.push((self.key.clone(), path.to_string(), Some((false, definition)), text.clone())),
            // an Assert step that a phrase means (its meaning's own Asserts are sites of its algorithm)
            Stmt::Phrase(..) | Stmt::Prose(..) if text.starts_with("Assert:") => {
                let mut open = false;
                own(st, &mut |x| open |= matches!(x, Visit::Prose(ch) if !meant(ch)));
                out.push((self.key.clone(), path.to_string(), Some((open, definition)), text.clone()));
            }
            _ => {}
        }
        // this step's own `!`s, then the steps nested in it
        let mut n = 0;
        own(st, &mut |x| n += matches!(x, Visit::Bang) as usize);
        self.push_bangs(n, path, bangs, out);
        self.closures_in(st, d, path, out);
        match st {
            Stmt::If(_, b, arms, els) => {
                self.body(b, d, path, bangs, false, out);
                for a in arms.iter().chain(els.iter()) {
                    self.body(&a.body, d, path, bangs, false, out);
                }
            }
            Stmt::IfElse(_, x, y) => {
                self.stmt(x, d, path, bangs, false, out);
                self.stmt(y, d, path, bangs, false, out);
            }
            Stmt::FindSuchThat(.., s) => self.stmt(s, d, path, bangs, false, out),
            Stmt::Repeat(ns) | Stmt::RepeatWhile(_, ns) | Stmt::RepeatUntil(_, ns) | Stmt::RepeatN(_, ns) => self.nodes(ns, d + 1, &format!("{path}."), out),
            Stmt::ForEach(.., b) | Stmt::ForEachRec(.., b) | Stmt::ForSuchThat(.., b) | Stmt::ForKeys(.., b) | Stmt::ForIndex(_, _, b) | Stmt::ForChildren(_, b) | Stmt::ForChildrenOf(_, _, b) | Stmt::ForRange(.., b) => {
                self.body(b, d, path, bangs, false, out)
            }
            Stmt::Readings(e, s, alts) => {
                self.stmt(s, d, path, bangs, alts.iter().any(|(r, _)| *r == Reading::Definition), out);
                self.alts(*e, path, alts, out);
            }
            _ => {}
        }
    }
}

/// The text of a step from its k-th `!` on, or the whole text when it has fewer.
fn bang_text(text: &str, k: usize) -> String {
    let at: Vec<usize> = text.match_indices("! ").map(|x| x.0).filter(|&i| i == 0 || matches!(text.as_bytes()[i - 1], b' ' | b'(' | b'[')).collect();
    at.get(k - 1).map_or(text, |&i| &text[i..]).to_string()
}

/// A statement's own expressions and conditions, not its nested steps' (inline bodies are walked
/// as statements of the same step).
fn own(st: &Stmt, f: &mut dyn FnMut(Visit)) {
    let w = Walk;
    match st {
        Stmt::Let(_, e) | Stmt::Perform(e) | Stmt::ThrowVal(e) | Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) => w.expr(e, f),
        Stmt::Set(p, e) => {
            if let crate::ast::Place::Field(x, _) | crate::ast::Place::Expr(x) = p {
                w.expr(x, f);
            }
            w.expr(e, f);
        }
        Stmt::Ret(e) => e.iter().for_each(|e| w.expr(e, f)),
        Stmt::RetSee(e, _) => w.expr(e, f),
        Stmt::If(c, ..) | Stmt::IfElse(c, ..) | Stmt::RepeatWhile(c, _) | Stmt::RepeatUntil(c, _) => w.cond(c, f),
        Stmt::ForEach(_, t, l, _, _) => {
            t.iter().for_each(|t| w.ty(t, f));
            w.expr(l, f);
        }
        Stmt::ForEachRec(_, _, l, _) | Stmt::ForIndex(_, l, _) | Stmt::ForChildrenOf(_, l, _) | Stmt::RepeatN(l, _) => w.expr(l, f),
        Stmt::ForSuchThat(_, t, c, _, _) | Stmt::FindSuchThat(_, t, c, _, _) => {
            w.ty(t, f);
            w.cond(c, f);
        }
        Stmt::ForKeys(_, o, c, _, _) => {
            w.expr(o, f);
            w.cond(c, f);
        }
        Stmt::ForRange(_, lo, _, hi, _, _, _) => {
            w.expr(lo, f);
            w.expr(hi, f);
        }
        Stmt::Macro(_, xs) => xs.iter().for_each(|x| w.expr(x, f)),
        Stmt::RemoveRestore(x, y) | Stmt::Resume(x, y) | Stmt::SetCodeState(x, y) | Stmt::ResumeLet(x, y, _, _) => {
            w.expr(x, f);
            w.expr(y, f);
        }
        Stmt::LetSuchThat(_, c, os) => {
            w.cond(c, f);
            os.iter().for_each(|(_, e)| w.expr(e, f));
        }
        Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => w.holes(hs, f),
        Stmt::Prose(ch, ps) => {
            f(Visit::Prose(ch));
            w.parts(ps, f);
        }
        _ => {}
    }
}

/// The closures a statement's own expressions define, by index in the closure table.
fn expr_closures(st: &Stmt, ks: &mut Vec<usize>) {
    fn e(x: &Expr, ks: &mut Vec<usize>) {
        if let Expr::Closure(k) = x {
            ks.push(*k);
        }
    }
    match st {
        Stmt::Let(_, x) | Stmt::Perform(x) | Stmt::Set(_, x) | Stmt::Ret(Some(x)) => e(x, ks),
        Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => hs.iter().for_each(|h| if let Hole::E(x) = h { e(x, ks) }),
        _ => {}
    }
}

/// The sites, in the spec's order, then the overlay algorithms', each reading's after its step.
pub fn sites(sp: &Spec, g: &Grammar, dt: &Data) -> Vec<Site> {
    let mut raw: Vec<Raw> = Vec::new();
    for a in &dt.algs {
        let al = &sp.algs[a.alg];
        let cid = sp.clauses[sp.home(a.clause)].id.as_str();
        let key = format!("{cid}#{}", al.idx);
        let w = Alg {
            key,
            clause: cid.to_string(),
            texts: crate::spec::labelled(&al.steps).into_iter().map(|(p, s)| (p, s.text.as_str())).collect(),
            closures: &a.closures,
            errata: &g.overlay.errata,
        };
        w.nodes(&a.body, 0, "", &mut raw);
    }
    let texts = |steps: &[Step]| crate::spec::labelled(steps).into_iter().map(|(p, s)| (p, s.text.clone())).collect::<HashMap<String, String>>();
    let mut overlay: Vec<(String, HashMap<String, String>, &[CloLit], &[Node])> = Vec::new();
    for p in &dt.phrase_algs {
        overlay.push((p.id.clone(), texts(&p.alg.steps), &p.closures, &p.body));
    }
    for r in &dt.reading_rows {
        overlay.push((r.id.clone(), texts(&r.alg.steps), &r.closures, r.steps()));
    }
    for (id, ts, closures, body) in &overlay {
        let w = Alg { key: id.clone(), clause: String::new(), texts: ts.iter().map(|(p, t)| (p.clone(), t.as_str())).collect(), closures, errata: &g.overlay.errata };
        w.nodes(body, 0, "", &mut raw);
    }
    let perm = &g.overlay.permanent;
    // a parameterized clause's site once, however many instances share it
    let mut seen = HashSet::new();
    raw.retain(|r| seen.insert(r.clone()));
    raw.into_iter()
        .map(|(key, path, what, text)| {
            let class = match what {
                None => "bang",
                Some((_, true)) => "definition",
                Some((open, false)) => match perm.iter().find(|p| p.step == path && (p.clause == key || key.split_once('#').is_some_and(|(c, _)| c == p.clause))) {
                    Some(p) => match p.class {
                        crate::overlay::StepClass::AssertFuture => "permanent-future",
                        crate::overlay::StepClass::AssertProvenance => "permanent-provenance",
                        crate::overlay::StepClass::Informative | crate::overlay::StepClass::History => if open { "open" } else { "formal" },
                    },
                    None if open => "open",
                    None => "formal",
                },
            };
            Site { class, key, path, text }
        })
        .collect()
}

/// The header: what the file is, and the count of each class.
pub fn header(sites: &[Site], what: &str) -> Vec<String> {
    let mut by: BTreeMap<&str, usize> = BTreeMap::new();
    for s in sites {
        *by.entry(s.class).or_default() += 1;
    }
    vec![
        format!("# {what}\n"),
        format!("# sites: {}; {}\n", sites.len(), CLASSES.iter().map(|c| format!("{c} {}", by.get(c).unwrap_or(&0))).collect::<Vec<_>>().join(", ")),
    ]
}
