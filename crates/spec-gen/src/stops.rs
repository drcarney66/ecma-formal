//! The literal errata's stop sites (readings.emu `stops=`) as erratum-labelled checks: at a site's
//! step its Asserts, `!`s and field reads of a field's value; under a caller condition, the step's
//! Asserts as checks in every mode and the caller's calls of the site's clause, whose failed checks
//! and sort errors stop as the erratum. A site whose step has none of these (sec-enqueueatomicswaitasynctimeoutjob@4:
//! the host takes any delay) labels nothing, nor does a site outside any step other than the job loop's
//! (sec-reads-bytes-from@-: the memory model, which no run evaluates); the job loop's site (`sec-jobs@-`)
//! is `Decls.jobErrata`.

use crate::ast::*;
use crate::spec::Step;
use std::cell::RefCell;
use std::collections::HashMap;

/// The sites the converter labels.
#[derive(Default)]
pub struct StopSites {
    /// a site's step: its erratum, `None` under a caller condition only
    pub steps: HashMap<*const Step, Option<usize>>,
    /// per caller clause id: the site clauses (clause index) it calls, with their errata
    pub calls: HashMap<String, Vec<(Id, usize)>>,
    /// the caller sites labelled: caller clause id, site clause, erratum
    pub called: RefCell<Vec<(String, Id, usize)>>,
}

impl StopSites {
    /// A step's own statement labelled: at a site, its checks; in a caller, its calls of a site's clause.
    pub fn label(&self, s: &Step, clause: &str, st: &mut Stmt) {
        self.with(s, clause, |at, f| stmt(st, at, f));
    }

    /// An `Else` arm's own condition and inline statement labelled (as `label`).
    pub fn label_arm(&self, s: &Step, clause: &str, a: &mut Arm) {
        self.with(s, clause, |at, f| {
            a.cond.iter_mut().for_each(|c| cond(c, f));
            body(&mut a.body, at, f);
        });
    }

    fn with(&self, s: &Step, clause: &str, g: impl FnOnce(Option<Option<usize>>, &mut F)) {
        let at = self.steps.get(&(s as *const Step)).copied();
        let calls = self.calls.get(clause).map(Vec::as_slice).unwrap_or_default();
        if at.is_none() && calls.is_empty() {
            return;
        }
        g(at, &mut |x: &mut Expr| {
            if let Some(Some(e)) = at {
                site(e, x);
            }
            if let Expr::Call(Callee::Alg(c), _) = x {
                if let Some(&(_, e)) = calls.iter().find(|(k, _)| k == c) {
                    self.called.borrow_mut().push((clause.to_string(), *c, e));
                    *x = Expr::Erratum(e, true, Box::new(std::mem::replace(x, Expr::ThisNode)));
                }
            }
        });
    }
}

/// At a site of erratum `e`: a `!` and a maximal field read of a field's value labelled.
fn site(e: usize, x: &mut Expr) {
    match x {
        Expr::Bang(y) => *x = Expr::BangAt(e, std::mem::replace(y, Box::new(Expr::ThisNode))),
        Expr::Field(y, f) => {
            let f = *f;
            let inner = match std::mem::replace(&mut **y, Expr::ThisNode) {
                Expr::Erratum(k, true, z) if k == e && matches!(*z, Expr::Field(..)) => Some(*z),
                z @ Expr::Field(..) => Some(z),
                z => {
                    **y = z;
                    None
                }
            };
            if let Some(z) = inner {
                *x = Expr::Erratum(e, true, Box::new(Expr::Field(Box::new(z), f)));
            }
        }
        _ => {}
    }
}

type F<'a> = dyn FnMut(&mut Expr) + 'a;

/// A statement's own expressions, children first, and at a site `at` (of erratum `e`, or `None` under a
/// caller condition) its Asserts; inline bodies are statements of the same step, nested steps and closure
/// bodies are not.
fn stmt(st: &mut Stmt, at: Option<Option<usize>>, f: &mut F) {
    if let (Some(e), Stmt::Assert(c)) = (at, &mut *st) {
        *st = Stmt::AssertAt(e, std::mem::replace(c, Cond::Alg(0, 0, String::new())));
    }
    match st {
        Stmt::Let(_, e) | Stmt::Perform(e) | Stmt::ThrowVal(e) | Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) | Stmt::RetSee(e, _) => expr(e, f),
        Stmt::Set(p, e) => {
            if let Place::Field(x, _) | Place::Expr(x) = p {
                expr(x, f);
            }
            expr(e, f);
        }
        Stmt::Ret(e) => e.iter_mut().for_each(|e| expr(e, f)),
        Stmt::If(c, b, arms, els) => {
            cond(c, f);
            body(b, at, f);
            for a in arms.iter_mut().chain(els.iter_mut()) {
                a.cond.iter_mut().for_each(|c| cond(c, f));
                body(&mut a.body, at, f);
            }
        }
        Stmt::IfElse(c, x, y) => {
            cond(c, f);
            stmt(x, at, f);
            stmt(y, at, f);
        }
        Stmt::Assert(c) | Stmt::AssertAt(_, c) | Stmt::RepeatWhile(c, _) | Stmt::RepeatUntil(c, _) => cond(c, f),
        Stmt::AssertIf(c, d) => {
            cond(c, f);
            cond(d, f);
        }
        Stmt::ForEach(_, t, l, _, _) => {
            t.iter_mut().for_each(|t| ty(t, f));
            expr(l, f);
        }
        Stmt::ForEachRec(_, _, l, _) | Stmt::ForIndex(_, l, _) | Stmt::ForChildrenOf(_, l, _) | Stmt::RepeatN(l, _) => expr(l, f),
        Stmt::ForSuchThat(_, t, c, _, _) => {
            ty(t, f);
            cond(c, f);
        }
        Stmt::FindSuchThat(_, t, c, _, s) => {
            ty(t, f);
            cond(c, f);
            stmt(s, at, f);
        }
        Stmt::ForKeys(_, o, c, _, _) => {
            expr(o, f);
            cond(c, f);
        }
        Stmt::ForRange(_, lo, _, hi, _, _, _) => {
            expr(lo, f);
            expr(hi, f);
        }
        Stmt::Macro(_, xs) => xs.iter_mut().for_each(|x| expr(x, f)),
        Stmt::RemoveRestore(x, y) | Stmt::Resume(x, y) | Stmt::SetCodeState(x, y) | Stmt::ResumeLet(x, y, _, _) => {
            expr(x, f);
            expr(y, f);
        }
        Stmt::LetSuchThat(_, c, os) => {
            cond(c, f);
            os.iter_mut().for_each(|(_, e)| expr(e, f));
        }
        Stmt::SyntaxError(_, c, u) => {
            cond(c, f);
            u.iter_mut().for_each(|(_, c)| cond(c, f));
        }
        Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => holes(hs, f),
        Stmt::Prose(_, ps) | Stmt::Note(ps) => parts(ps, f),
        Stmt::WithSteps(s, _) | Stmt::Readings(_, s, _) => stmt(s, at, f),
        Stmt::Unreachable(_) | Stmt::ThrowErr(_) | Stmt::Repeat(_) | Stmt::ForChildren(..) | Stmt::ResumeTop => {}
    }
}

fn body(b: &mut Body, at: Option<Option<usize>>, f: &mut F) {
    if let Body::Inline(s) = b {
        stmt(s, at, f);
    }
}

fn expr(e: &mut Expr, f: &mut F) {
    match e {
        Expr::Call(_, xs) | Expr::List(xs) => xs.iter_mut().for_each(|x| expr(x, f)),
        Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
            expr(x, f);
            xs.iter_mut().for_each(|x| expr(x, f));
        }
        Expr::Component(_, _, x)
        | Expr::Field(x, _)
        | Expr::Q(x)
        | Expr::Bang(x)
        | Expr::BangAt(_, x)
        | Expr::Erratum(_, _, x)
        | Expr::Neg(x)
        | Expr::Paren(x)
        | Expr::Annot(_, x)
        | Expr::ResumedWith(x)
        | Expr::ChildOf(x, _, _)
        | Expr::Table(_, x)
        | Expr::Definition(x, _) => expr(x, f),
        Expr::Index(x, y) | Expr::Bin(_, x, y) | Expr::TableStep(_, x, y) => {
            expr(x, f);
            expr(y, f);
        }
        Expr::Record(_, _, fs) => fs.iter_mut().for_each(|(_, x)| expr(x, f)),
        Expr::Extreme(_, _, t, c) => {
            ty(t, f);
            cond(c, f);
        }
        Expr::Phrase(_, hs) => holes(hs, f),
        Expr::Prose(_, ps) => parts(ps, f),
        _ => {}
    }
    f(e);
}

fn pred(p: &mut Pred, f: &mut F) {
    match p {
        Pred::IsVal(_, _, xs) => xs.iter_mut().for_each(|x| expr(x, f)),
        Pred::IsTy(_, _, ts) => ts.iter_mut().for_each(|t| ty(t, f)),
        Pred::Phrase(_, hs) => holes(hs, f),
    }
}

fn cond(c: &mut Cond, f: &mut F) {
    match c {
        Cond::Preds(e, p, r) => {
            expr(e, f);
            pred(p, f);
            r.iter_mut().for_each(|(_, p)| pred(p, f));
        }
        Cond::Rel(_, x, y) => {
            expr(x, f);
            expr(y, f);
        }
        Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter_mut().for_each(|c| cond(c, f)),
        Cond::Paren(c) => cond(c, f),
        Cond::Phrase(_, hs) => holes(hs, f),
        Cond::Prose(_, ps) => parts(ps, f),
        Cond::Alg(..) => {}
    }
}

fn ty(t: &mut TyExpr, f: &mut F) {
    match t {
        TyExpr::ListOf(_, x) => ty(x, f),
        TyExpr::Union(_, _, ts) => ts.iter_mut().for_each(|t| ty(t, f)),
        TyExpr::Completion(x) => x.iter_mut().for_each(|t| ty(t, f)),
        TyExpr::Interval(x, lo, hi) => {
            ty(x, f);
            expr(lo, f);
            expr(hi, f);
        }
        TyExpr::Value(e) => expr(e, f),
        TyExpr::Record(fs) => fs.iter_mut().for_each(|(_, t)| ty(t, f)),
        TyExpr::That(x, p, r) => {
            ty(x, f);
            pred(p, f);
            r.iter_mut().for_each(|(_, p)| pred(p, f));
        }
        TyExpr::Phrase(_, hs) => holes(hs, f),
        TyExpr::Prose(ps) => parts(ps, f),
        _ => {}
    }
}

fn holes(hs: &mut [Hole], f: &mut F) {
    for h in hs {
        match h {
            Hole::E(e) => expr(e, f),
            Hole::C(c) | Hole::Bc(_, c) => cond(c, f),
            Hole::T(t) => ty(t, f),
            Hole::L(_, xs) => xs.iter_mut().for_each(|x| expr(x, f)),
            _ => {}
        }
    }
}

fn parts(ps: &mut [Part], f: &mut F) {
    for p in ps {
        if let Part::Hole(h) = p {
            holes(std::slice::from_mut(h), f);
        }
    }
}
