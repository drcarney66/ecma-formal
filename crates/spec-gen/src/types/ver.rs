//! Slot versions: each read's reaching bindings, and a slot's bindings grouped by the reads they share.

use super::{binds_at, hole_vars, Bind};
use crate::ast::{Body, CloLit, Cond, Expr, Hole, Id, Node, Part, Place, Pred, Reading, Stmt, TyExpr};
use std::collections::{BTreeSet, HashMap, HashSet};

/// The key of a slot's value on entry: a parameter's, an outer variable's, or none.
pub(super) const ENTRY: usize = 0;

/// An expression's address: a read's key, and a binding's.
pub(super) fn addr(e: &Expr) -> usize {
    e as *const Expr as usize
}

/// A binding's key (its expression's or type's address); none for a binder no step defines here.
pub(super) fn key(b: &Bind) -> Option<usize> {
    match b {
        Bind::E(e) | Bind::Unwrap(e) | Bind::El(e) => Some(addr(e)),
        Bind::H(t) => Some(*t as *const TyExpr as usize),
        Bind::T(_) => None,
    }
}

/// The bindings reaching each slot on a path (a slot absent: its entry value only); none past a step that never falls through.
type Defs = Option<HashMap<Id, BTreeSet<usize>>>;

/// Each slot's binding groups: the keys of each group (`ENTRY` in the first, if any read sees it), and each read's group.
#[derive(Debug, Default)]
pub(super) struct Groups {
    pub of: HashMap<Id, Vec<Vec<usize>>>,
    pub read: HashMap<usize, (Id, usize)>,
    /// the slots that keep one version: bound by a form no step defines here, by a phrase or prose step, or in a closure
    pub whole: HashSet<Id>,
}

struct Walk<'a> {
    closures: &'a [CloLit],
    reads: Vec<(usize, Id, BTreeSet<usize>)>,
    defined: HashSet<usize>,
    /// also the reads past a step that never falls through
    all: bool,
}

fn join(a: Defs, b: Defs) -> Defs {
    let (Some(a), Some(b)) = (&a, &b) else { return a.or(b) };
    let entry = || BTreeSet::from([ENTRY]);
    let mut out = a.clone();
    for (x, s) in out.iter_mut() {
        s.extend(b.get(x).cloned().unwrap_or_else(entry));
    }
    for (x, s) in b {
        out.entry(*x).or_insert_with(|| entry().union(s).copied().collect());
    }
    Some(out)
}

impl Walk<'_> {
    /// Records every variable read in `e` (closure bodies aside) with the bindings reaching it.
    fn expr(&mut self, st: &Defs, e: &Expr) {
        let mut vs = Vec::new();
        vars(e, &mut vs);
        self.record(st, vs);
    }

    fn cond(&mut self, st: &Defs, c: &Cond) {
        let mut vs = Vec::new();
        cond_vars(c, &mut vs);
        self.record(st, vs);
    }

    fn holes(&mut self, st: &Defs, hs: &[Hole]) {
        let mut vs = Vec::new();
        hs.iter().for_each(|h| hole_vars_in(h, &mut vs));
        self.record(st, vs);
    }

    fn record(&mut self, st: &Defs, vs: Vec<(usize, Id)>) {
        for (a, x) in vs {
            match st {
                Some(m) => self.reads.push((a, x, m.get(&x).cloned().unwrap_or_else(|| BTreeSet::from([ENTRY])))),
                None if self.all => self.reads.push((a, x, BTreeSet::new())),
                None => {}
            }
        }
    }

    fn def(&mut self, st: &mut Defs, x: Id, k: usize) {
        self.defined.insert(k);
        if let Some(m) = st {
            m.insert(x, BTreeSet::from([k]));
        }
    }

    /// A loop's head: the bindings before it and every one in it, which a later round may see.
    fn head(&self, s: &Stmt, st: &Defs) -> Defs {
        let mut st = st.clone();
        let mut bs = Vec::new();
        binds_at(Some(s), &[], self.closures, &mut bs, &mut HashSet::new());
        if let Some(m) = &mut st {
            for (x, b) in &bs {
                if let Some(k) = key(b) {
                    m.entry(*x).or_insert_with(|| BTreeSet::from([ENTRY])).insert(k);
                }
            }
        }
        st
    }

    fn nodes(&mut self, ns: &[Node], st: Defs) -> Defs {
        ns.iter().fold(st, |st, n| self.stmt(&n.stmt, st))
    }

    fn body(&mut self, b: &Body, st: Defs) -> Defs {
        match b {
            Body::Inline(s) => self.stmt(s, st),
            Body::Block(ns) => self.nodes(ns, st),
        }
    }

    fn stmt(&mut self, s: &Stmt, mut st: Defs) -> Defs {
        match s {
            Stmt::Let(x, e) | Stmt::Set(Place::Var(x), e) => {
                self.expr(&st, e);
                self.def(&mut st, *x, addr(e));
                st
            }
            Stmt::Set(Place::Field(b, _), e) | Stmt::Set(Place::Expr(b), e) => {
                self.expr(&st, b);
                self.expr(&st, e);
                st
            }
            Stmt::Macro(_, xs) => {
                xs.iter().for_each(|e| self.expr(&st, e));
                if let Some(e @ Expr::Var(x)) = xs.first() {
                    self.def(&mut st, *x, addr(e));
                }
                st
            }
            Stmt::Ret(e) => {
                e.iter().for_each(|e| self.expr(&st, e));
                None
            }
            Stmt::RetSee(e, x) => {
                self.expr(&st, e);
                self.expr(&st, x);
                None
            }
            Stmt::ThrowVal(e) => {
                self.expr(&st, e);
                None
            }
            Stmt::ThrowErr(_) | Stmt::Unreachable(_) => None,
            Stmt::If(c, b, arms, els) => {
                self.cond(&st, c);
                let mut ends = vec![self.body(b, st.clone())];
                for a in arms.iter().chain(els.iter()) {
                    if let Some(c) = &a.cond {
                        self.cond(&st, c);
                    }
                    ends.push(self.body(&a.body, st.clone()));
                }
                if !els.as_ref().is_some_and(|a| a.cond.is_none()) {
                    ends.push(st);
                }
                ends.into_iter().reduce(join).unwrap_or(None)
            }
            Stmt::IfElse(c, x, y) => {
                self.cond(&st, c);
                let a = self.stmt(x, st.clone());
                let b = self.stmt(y, st);
                join(a, b)
            }
            Stmt::Readings(_, x, alts) => {
                let mut ends = Vec::new();
                if !alts.iter().any(|(r, _)| *r == Reading::Definition) {
                    ends.push(self.stmt(x, st.clone()));
                }
                for (_, ns) in alts {
                    ends.push(self.nodes(ns, st.clone()));
                }
                ends.into_iter().reduce(join).unwrap_or(st)
            }
            Stmt::FindSuchThat(_, t, c, _, x) => {
                let h = self.head(s, &st);
                self.ty(&h, t);
                self.cond(&h, c);
                let e = self.stmt(x, h.clone());
                join(h, e)
            }
            Stmt::Repeat(ns) | Stmt::RepeatN(_, ns) | Stmt::RepeatWhile(_, ns) | Stmt::RepeatUntil(_, ns) => {
                let h = self.head(s, &st);
                match s {
                    Stmt::RepeatN(e, _) => self.expr(&st, e),
                    Stmt::RepeatWhile(c, _) | Stmt::RepeatUntil(c, _) => self.cond(&h, c),
                    _ => {}
                }
                self.nodes(ns, h.clone());
                h
            }
            Stmt::ForEach(x, t, l, _, b) => {
                self.expr(&st, l);
                let mut h = self.head(s, &st);
                if let Some(t) = t {
                    self.ty(&st, t);
                }
                let k = t.as_ref().map_or(addr(l), |t| t as *const TyExpr as usize);
                let mut inner = h.clone();
                self.def(&mut inner, *x, k);
                self.body(b, inner);
                if let Some(m) = &mut h {
                    m.entry(*x).or_insert_with(|| BTreeSet::from([ENTRY])).insert(k);
                }
                h
            }
            Stmt::ForEachRec(_, _, e, b) | Stmt::ForIndex(_, e, b) | Stmt::ForChildrenOf(_, e, b) => {
                self.expr(&st, e);
                let h = self.head(s, &st);
                self.body(b, h.clone());
                h
            }
            Stmt::ForKeys(_, o, c, _, b) => {
                self.expr(&st, o);
                let h = self.head(s, &st);
                self.cond(&h, c);
                self.body(b, h.clone());
                h
            }
            Stmt::ForSuchThat(_, t, c, _, b) => {
                let h = self.head(s, &st);
                self.ty(&h, t);
                self.cond(&h, c);
                self.body(b, h.clone());
                h
            }
            Stmt::ForRange(_, lo, _, hi, _, _, b) => {
                self.expr(&st, lo);
                self.expr(&st, hi);
                let h = self.head(s, &st);
                self.body(b, h.clone());
                h
            }
            Stmt::ForChildren(_, b) => {
                let h = self.head(s, &st);
                self.body(b, h.clone());
                h
            }
            Stmt::WithSteps(x, ns) => {
                let h = self.head(s, &st);
                let e = self.stmt(x, h.clone());
                self.nodes(ns, e);
                h
            }
            Stmt::Perform(e) | Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) => {
                self.expr(&st, e);
                st
            }
            Stmt::RemoveRestore(x, y) | Stmt::Resume(x, y) | Stmt::SetCodeState(x, y) | Stmt::ResumeLet(x, y, _, _) => {
                self.expr(&st, x);
                self.expr(&st, y);
                st
            }
            Stmt::Assert(c) | Stmt::AssertAt(_, c) => {
                self.cond(&st, c);
                st
            }
            Stmt::AssertIf(c, d) => {
                self.cond(&st, c);
                self.cond(&st, d);
                st
            }
            Stmt::LetSuchThat(_, c, os) => {
                self.cond(&st, c);
                os.iter().for_each(|(_, e)| self.expr(&st, e));
                st
            }
            Stmt::SyntaxError(_, c, u) => {
                self.cond(&st, c);
                if let Some((_, u)) = u {
                    self.cond(&st, u);
                }
                st
            }
            Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => {
                self.holes(&st, hs);
                st
            }
            Stmt::Prose(_, ps) | Stmt::Note(ps) => {
                let mut vs = Vec::new();
                ps.iter().for_each(|p| if let Part::Hole(h) = p { hole_vars_in(h, &mut vs) });
                self.record(&st, vs);
                st
            }
            Stmt::ResumeTop => st,
        }
    }

    fn ty(&mut self, st: &Defs, t: &TyExpr) {
        let mut vs = Vec::new();
        ty_vars(t, &mut vs);
        self.record(st, vs);
    }
}

/// The variables an expression reads (address and slot), closure bodies aside.
fn vars(e: &Expr, out: &mut Vec<(usize, Id)>) {
    match e {
        Expr::Var(x) => out.push((addr(e), *x)),
        Expr::Call(_, xs) | Expr::List(xs) => xs.iter().for_each(|x| vars(x, out)),
        Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
            vars(x, out);
            xs.iter().for_each(|x| vars(x, out));
        }
        Expr::Component(_, _, x) | Expr::Field(x, _) | Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) | Expr::Erratum(_, _, x) | Expr::Neg(x) | Expr::Paren(x) | Expr::Annot(_, x) | Expr::Table(_, x) | Expr::Definition(x, _) | Expr::ResumedWith(x) | Expr::ChildOf(x, _, _) => vars(x, out),
        Expr::Index(x, y) | Expr::Bin(_, x, y) | Expr::TableStep(_, x, y) => {
            vars(x, out);
            vars(y, out);
        }
        Expr::Record(_, _, fs) => fs.iter().for_each(|(_, x)| vars(x, out)),
        Expr::Extreme(_, _, t, c) => {
            ty_vars(t, out);
            cond_vars(c, out);
        }
        Expr::Phrase(_, hs) => hs.iter().for_each(|h| hole_vars_in(h, out)),
        Expr::Prose(_, ps) => ps.iter().for_each(|p| if let Part::Hole(h) = p { hole_vars_in(h, out) }),
        _ => {}
    }
}

fn hole_vars_in(h: &Hole, out: &mut Vec<(usize, Id)>) {
    match h {
        Hole::E(e) => vars(e, out),
        Hole::C(c) | Hole::Bc(_, c) => cond_vars(c, out),
        Hole::T(t) => ty_vars(t, out),
        Hole::L(_, xs) => xs.iter().for_each(|x| vars(x, out)),
        _ => {}
    }
}

fn pred_vars(p: &Pred, out: &mut Vec<(usize, Id)>) {
    match p {
        Pred::IsVal(_, _, xs) => xs.iter().for_each(|x| vars(x, out)),
        Pred::IsTy(_, _, ts) => ts.iter().for_each(|t| ty_vars(t, out)),
        Pred::Phrase(_, hs) => hs.iter().for_each(|h| hole_vars_in(h, out)),
    }
}

fn cond_vars(c: &Cond, out: &mut Vec<(usize, Id)>) {
    match c {
        Cond::Preds(e, p, r) => {
            vars(e, out);
            pred_vars(p, out);
            r.iter().for_each(|(_, p)| pred_vars(p, out));
        }
        Cond::Rel(_, x, y) => {
            vars(x, out);
            vars(y, out);
        }
        Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().for_each(|c| cond_vars(c, out)),
        Cond::Paren(c) => cond_vars(c, out),
        Cond::Phrase(_, hs) => hs.iter().for_each(|h| hole_vars_in(h, out)),
        Cond::Prose(_, ps) => ps.iter().for_each(|p| if let Part::Hole(h) = p { hole_vars_in(h, out) }),
        Cond::Alg(..) => {}
    }
}

fn ty_vars(t: &TyExpr, out: &mut Vec<(usize, Id)>) {
    match t {
        TyExpr::ListOf(_, x) => ty_vars(x, out),
        TyExpr::Union(_, _, ts) => ts.iter().for_each(|t| ty_vars(t, out)),
        TyExpr::Completion(Some(x)) => ty_vars(x, out),
        TyExpr::Interval(x, a, b) => {
            ty_vars(x, out);
            vars(a, out);
            vars(b, out);
        }
        TyExpr::Value(e) => vars(e, out),
        TyExpr::Record(fs) => fs.iter().for_each(|(_, t)| ty_vars(t, out)),
        TyExpr::That(x, p, r) => {
            ty_vars(x, out);
            pred_vars(p, out);
            r.iter().for_each(|(_, p)| pred_vars(p, out));
        }
        TyExpr::Phrase(_, hs) => hs.iter().for_each(|h| hole_vars_in(h, out)),
        TyExpr::Prose(ps) => ps.iter().for_each(|p| if let Part::Hole(h) = p { hole_vars_in(h, out) }),
        _ => {}
    }
}

/// The binding groups of a unit's slots: bindings that reach a common read share a group.
pub(super) fn groups(body: &[Node], closures: &[CloLit], bs: &[(Id, Bind)]) -> Groups {
    let mut w = Walk { closures, reads: Vec::new(), defined: HashSet::new(), all: false };
    w.nodes(body, Some(HashMap::new()));
    let mut whole: HashSet<Id> = HashSet::new();
    for (x, b) in bs {
        if key(b).is_none_or(|k| !w.defined.contains(&k)) {
            whole.insert(*x);
        }
    }
    body.iter().for_each(|n| hole_vars(&n.stmt, &mut whole));
    for c in closures {
        whole.extend(c.params.iter().flatten().chain(c.caps.iter()));
        if let Some((a, b, c)) = c.frame {
            whole.extend([a, b, c]);
        }
        let mut cb = Vec::new();
        binds_at(None, &c.body, closures, &mut cb, &mut HashSet::new());
        whole.extend(cb.iter().map(|b| b.0));
        let mut cw = Walk { closures, reads: Vec::new(), defined: HashSet::new(), all: true };
        cw.nodes(&c.body, Some(HashMap::new()));
        whole.extend(cw.reads.iter().map(|r| r.1));
    }
    // union-find over each slot's keys
    let mut parent: HashMap<(Id, usize), (Id, usize)> = HashMap::new();
    fn find(p: &mut HashMap<(Id, usize), (Id, usize)>, a: (Id, usize)) -> (Id, usize) {
        let mut r = a;
        while let Some(&q) = p.get(&r).filter(|q| **q != r) {
            r = q;
        }
        p.insert(a, r);
        r
    }
    for (x, b) in bs.iter().filter(|b| !whole.contains(&b.0)) {
        if let Some(k) = key(b) {
            parent.entry((*x, k)).or_insert((*x, k));
        }
    }
    for (_, x, ks) in w.reads.iter().filter(|r| !whole.contains(&r.1)) {
        let mut it = ks.iter();
        let Some(&k0) = it.next() else { continue };
        parent.entry((*x, k0)).or_insert((*x, k0));
        let r0 = find(&mut parent, (*x, k0));
        for &k in it {
            parent.entry((*x, k)).or_insert((*x, k));
            let r = find(&mut parent, (*x, k));
            if r != r0 {
                // the entry value's group is its root
                let (a, b) = if r.1 == ENTRY { (r0, r) } else { (r, r0) };
                parent.insert(a, b);
            }
        }
    }
    let keys: Vec<(Id, usize)> = parent.keys().copied().collect();
    let mut idx: HashMap<(Id, usize), usize> = HashMap::new();
    let mut of: HashMap<Id, Vec<Vec<usize>>> = HashMap::new();
    // groups in binding order, not address order
    let mut ord: HashMap<usize, usize> = HashMap::new();
    for k in bs.iter().filter_map(|b| key(&b.1)) {
        let n = ord.len() + 1;
        ord.entry(k).or_insert(n);
    }
    let rank = |k: usize| if k == ENTRY { 0 } else { ord[&k] };
    let mut sorted = keys;
    sorted.sort_by_key(|&(x, k)| (x, rank(k)));
    for a in sorted {
        let r = find(&mut parent, a);
        let gs = of.entry(a.0).or_default();
        let i = *idx.entry(r).or_insert_with(|| {
            gs.push(Vec::new());
            gs.len() - 1
        });
        gs[i].push(a.1);
    }
    let mut read = HashMap::new();
    for (a, x, ks) in &w.reads {
        if let (false, Some(&k)) = (whole.contains(x), ks.iter().next()) {
            let r = find(&mut parent, (*x, k));
            read.insert(*a, (*x, idx[&r]));
        }
    }
    Groups { of, read, whole }
}
