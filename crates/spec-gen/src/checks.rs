//! Phrase meanings against their sites: each parameter's declared sort against the values
//! sites pass there, and every literal against its algorithm's text; every intrinsic default
//! prototype's literal against the realm table; every reading's binders against the variables
//! bound on every path to the step it replaces. A mismatch fails emission.

use crate::ast::*;
use crate::data::Data;
use crate::decls::{Decls, Meaning, PArg};
use crate::grammar::Grammar;
use crate::spec::Spec;

/// A value's sort, as far as the checks tell sorts apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum S {
    Str,
    CodePoint,
    CodeUnit,
    List,
    Number,
    BigInt,
    Math,
    Bool,
    Field,
    Selector,
    Table,
    Nt,
    Node,
    /// an element of a List or a Data Block, by index
    Elem,
}

/// The sorts a declared parameter type admits; none when any alternative is unknown.
fn admits(t: &str) -> Option<Vec<S>> {
    let t = t.trim().trim_start_matches("optional ");
    let mut out = Vec::new();
    for alt in t.split(", ").flat_map(|x| x.split(" or ")) {
        let a = alt.trim().trim_start_matches("either ");
        let a = a.strip_prefix("a ").or_else(|| a.strip_prefix("an ")).unwrap_or(a).trim();
        let s = if a.starts_with("List") || a.starts_with("Set") || a.ends_with("Data Block") {
            vec![S::List]
        } else if a == "String" || a == "source text" {
            vec![S::Str]
        } else if a == "code point" {
            vec![S::CodePoint]
        } else if a == "code unit" {
            vec![S::CodeUnit]
        } else if a == "character" {
            vec![S::CodePoint, S::CodeUnit]
        } else if ["integer", "non-negative integer", "mathematical value", "extended mathematical value", "byte"].contains(&a) {
            vec![S::Math]
        } else if a == "Number" {
            vec![S::Number]
        } else if a == "BigInt" {
            vec![S::BigInt]
        } else if a == "Boolean" {
            vec![S::Bool]
        } else if ["field", "field name", "internal slot name", "attribute name", "internal method name"].contains(&a) {
            vec![S::Field]
        } else if a == "choice" {
            vec![S::Selector]
        } else if a == "table" {
            vec![S::Table]
        } else if a == "nonterminal" || a.starts_with("nonterminal in ") || a == "grammar symbol" {
            vec![S::Nt]
        } else if a == "Parse Node" {
            vec![S::Node]
        } else {
            return None;
        };
        out.extend(s);
    }
    Some(out)
}

/// What the sorts of a unit's expressions depend on: its variables' sorts (header parameters
/// and single bindings), and the operations' result sorts by clause.
struct Cx<'a> {
    g: &'a Grammar,
    d: &'a Decls,
    vars: std::collections::HashMap<Id, S>,
    rets: &'a std::collections::HashMap<Id, S>,
}

/// The sort a header type names, if it names exactly one.
fn ty_sort(d: &Decls, t: &TyExpr) -> Option<S> {
    match t {
        TyExpr::Sort(_, _, s, _) => match admits(d.sorts.name(*s))?.as_slice() {
            [x] => Some(*x),
            _ => None,
        },
        TyExpr::ListOf(..) => Some(S::List),
        TyExpr::That(x, p, rest) if d.is_context(x, p, rest) => ty_sort(d, x),
        _ => None,
    }
}

/// The sort a primitive's result has, if its signature names exactly one.
fn result_sort(g: &Grammar, d: &Decls, p: Id) -> Option<S> {
    match admits(&crate::sig::of(g, d.prims.name(p))?.res)?.as_slice() {
        [s] => Some(*s),
        _ => None,
    }
}

/// An expression's sort where it is statically plain.
fn expr_sort(cx: &Cx, e: &Expr) -> Option<S> {
    let (g, d) = (cx.g, cx.d);
    Some(match e {
        Expr::Var(x) => return cx.vars.get(x).copied(),
        Expr::Call(Callee::Alg(c), _) => return cx.rets.get(c).copied(),
        Expr::Val(ValLit::Str(..)) => S::Str,
        Expr::Val(ValLit::True | ValLit::False) => S::Bool,
        Expr::Val(ValLit::Num(_, _, Sub::F) | ValLit::NaN(Sub::F)) => S::Number,
        Expr::Val(ValLit::Num(_, _, Sub::Z) | ValLit::BigN(_)) => S::BigInt,
        Expr::Math(..) => S::Math,
        Expr::CodeUnit(..) => S::CodeUnit,
        Expr::CodePoint(..) => S::CodePoint,
        Expr::List(_) => S::List,
        Expr::FieldName(_) => S::Field,
        Expr::Table(..) => S::Table,
        Expr::Nt(..) => S::Nt,
        Expr::Child(..) | Expr::ThisNode => S::Node,
        Expr::Index(..) => S::Elem,
        Expr::Paren(x) | Expr::Erratum(_, _, x) => return expr_sort(cx, x),
        Expr::Call(Callee::Prim(p), _) => return result_sort(g, d, *p),
        Expr::Phrase(p, _) => match &d.phrases[*p].meaning {
            Some(Meaning::Prim { prim, neg: false, .. }) => return result_sort(g, d, *prim),
            _ => return None,
        },
        _ => return None,
    })
}

/// The sort of the value a hole passes, where it is plain.
fn hole_sort(cx: &Cx, h: &Hole) -> Option<S> {
    match h {
        Hole::W(_) => Some(S::Selector),
        Hole::Field(_) => Some(S::Field),
        Hole::Text(_) => Some(S::Str),
        Hole::E(e) => expr_sort(cx, e),
        Hole::L(..) => Some(S::List),
        Hole::C(_) => Some(S::Bool),
        _ => None,
    }
}

/// A hole's sort, and its expression if it is one.
fn hole_arg<'a>(cx: &Cx, h: &'a Hole) -> (Option<S>, Option<&'a Expr>) {
    (hole_sort(cx, h), if let Hole::E(e) = h { Some(e) } else { None })
}

/// Whether a value of sort `s` is definitely not one of `want`: code points and code units
/// are mathematical values, so a number written where a code unit or code point is meant passes.
fn mismatch(s: S, want: &[S]) -> bool {
    match s {
        S::Elem => want == [S::List],
        S::CodePoint | S::CodeUnit if want.contains(&S::Math) => false,
        S::Math if want.contains(&S::CodePoint) || want.contains(&S::CodeUnit) => false,
        _ => !want.contains(&s),
    }
}

/// A phrase site: the phrase, its holes, a predicate's subject.
struct Site<'a> {
    id: Id,
    holes: &'a [Hole],
    subject: Option<&'a Expr>,
}

/// What a walk meets: phrase sites, and literals (outside an erratum's other readings).
#[derive(Default)]
struct Found<'a> {
    sites: Vec<Site<'a>>,
    lits: Vec<&'a str>,
    /// `Let x be e` steps, and the variables a step sets or binds otherwise
    lets: Vec<(Id, &'a Expr)>,
    rebound: Vec<Id>,
    /// the tables `Expr.tableStep`s refer to
    tables: Vec<usize>,
    /// reads of the call's *this* value, NewTarget or arguments List
    frame: usize,
    /// spec-named callees and execution-context forms, in text order, outside an erratum's other readings
    calls: Vec<Called<'a>>,
    /// operation calls (callee clause, arguments), outside an erratum's other readings
    alg_args: Vec<(Id, &'a [Expr])>,
    /// every call's callee and arguments, an erratum's readings included
    call_args: Vec<(&'a Callee, &'a [Expr])>,
    /// macro uses (macro clause, arguments)
    macros: Vec<(Id, &'a [Expr])>,
    /// inside an erratum's other readings
    alt: usize,
    /// prose steps that start with "Else" (an Else that did not join its If)
    else_prose: usize,
    /// the right-hand-side children `Expr.child` names, by position kind and nonterminal
    children: Vec<(usize, Id)>,
}

/// What a step calls: an operation (by clause), an SDO, a method, an overlay phrase, or an execution-context form.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Called<'a> {
    Alg(Id),
    Sdo(Id),
    /// an internal method (FieldId), a concrete method (MethodId)
    IMethod(Id),
    CMethod(Id),
    Phrase(Id),
    /// an emu-table, by its index among the scanned tables: the operations its cells name
    Table(usize),
    /// a phrase's verbatim text hole (an inline table)
    Text(&'a str),
    Ctx(&'static str),
}

impl<'a> Found<'a> {
    fn call(&mut self, c: Called<'a>) {
        if self.alt == 0 {
            self.calls.push(c);
        }
    }

    fn ctx(&mut self, form: &'static str) {
        self.call(Called::Ctx(form));
    }

    fn site(&mut self, s: Site<'a>) {
        self.call(Called::Phrase(s.id));
        self.sites.push(s);
    }

    fn nodes(&mut self, ns: &'a [Node], lits: bool) {
        for n in ns {
            self.stmt(&n.stmt, lits);
        }
    }

    fn body(&mut self, b: &'a Body, lits: bool) {
        match b {
            Body::Inline(s) => self.stmt(s, lits),
            Body::Block(ns) => self.nodes(ns, lits),
        }
    }

    fn holes(&mut self, hs: &'a [Hole], lits: bool) {
        for h in hs {
            match h {
                Hole::E(e) => self.expr(e, lits),
                Hole::C(c) | Hole::Bc(_, c) => self.cond(c, lits),
                Hole::T(t) => self.ty(t, lits),
                Hole::L(_, xs) => xs.iter().for_each(|x| self.expr(x, lits)),
                Hole::Text(t) => self.call(Called::Text(t)),
                Hole::B(_) | Hole::W(_) | Hole::Field(_) => {}
            }
        }
    }

    fn parts(&mut self, ps: &'a [Part], lits: bool) {
        for p in ps {
            if let Part::Hole(h) = p {
                self.holes(std::slice::from_ref(h), lits);
            }
        }
    }

    fn stmt(&mut self, st: &'a Stmt, lits: bool) {
        match st {
            Stmt::Let(x, e) => {
                self.lets.push((*x, e));
                self.expr(e, lits);
            }
            Stmt::Perform(e) | Stmt::ThrowVal(e) => self.expr(e, lits),
            Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) => {
                self.ctx(match st {
                    Stmt::Suspend(..) => "suspend",
                    Stmt::Push(..) => "push",
                    _ => "remove",
                });
                self.expr(e, lits)
            }
            Stmt::Set(p, e) => {
                match p {
                    Place::Var(x) => self.rebound.push(*x),
                    Place::Field(x, _) | Place::Expr(x) => self.expr(x, lits),
                }
                self.expr(e, lits);
            }
            Stmt::Ret(e) => e.iter().for_each(|e| self.expr(e, lits)),
            Stmt::If(c, b, arms, els) => {
                self.cond(c, lits);
                self.body(b, lits);
                for a in arms.iter().chain(els) {
                    a.cond.iter().for_each(|c| self.cond(c, lits));
                    self.body(&a.body, lits);
                }
            }
            Stmt::IfElse(c, a, b) => {
                self.cond(c, lits);
                self.stmt(a, lits);
                self.stmt(b, lits);
            }
            Stmt::Assert(c) | Stmt::AssertAt(_, c) => self.cond(c, lits),
            Stmt::AssertIf(c, k) | Stmt::SyntaxError(_, c, Some((_, k))) => {
                self.cond(c, lits);
                self.cond(k, lits);
            }
            Stmt::SyntaxError(_, c, None) => self.cond(c, lits),
            Stmt::Unreachable(_) | Stmt::ThrowErr(_) => {}
            Stmt::ResumeTop => self.ctx("resumeTop"),
            Stmt::Note(ps) | Stmt::Prose(_, ps) => {
                if matches!((st, ps.first()), (Stmt::Prose(..), Some(Part::Text(t))) if t.trim_start().starts_with("Else")) {
                    self.else_prose += 1;
                }
                self.parts(ps, lits)
            }
            Stmt::Repeat(ns) => self.nodes(ns, lits),
            Stmt::RepeatWhile(c, ns) | Stmt::RepeatUntil(c, ns) => {
                self.cond(c, lits);
                self.nodes(ns, lits);
            }
            Stmt::ForEach(_, t, e, _, b) => {
                t.iter().for_each(|t| self.ty(t, lits));
                self.expr(e, lits);
                self.body(b, lits);
            }
            Stmt::ForEachRec(_, _, e, b) | Stmt::ForIndex(_, e, b) | Stmt::ForChildrenOf(_, e, b) => {
                self.expr(e, lits);
                self.body(b, lits);
            }
            Stmt::ForChildren(_, b) => self.body(b, lits),
            Stmt::Mutate(p, hs) | Stmt::Phrase(p, hs) => {
                self.site(Site { id: *p, holes: hs, subject: None });
                self.holes(hs, lits);
            }
            Stmt::WithSteps(s, ns) => {
                self.stmt(s, lits);
                self.nodes(ns, lits);
            }
            Stmt::ForSuchThat(_, t, c, _, b) => {
                self.ty(t, lits);
                self.cond(c, lits);
                self.body(b, lits);
            }
            Stmt::ForKeys(_, e, c, _, b) => {
                self.expr(e, lits);
                self.cond(c, lits);
                self.body(b, lits);
            }
            Stmt::RepeatN(e, ns) => {
                self.expr(e, lits);
                self.nodes(ns, lits);
            }
            Stmt::ForRange(_, lo, _, hi, _, _, b) => {
                self.expr(lo, lits);
                self.expr(hi, lits);
                self.body(b, lits);
            }
            Stmt::RetSee(a, b) | Stmt::RemoveRestore(a, b) | Stmt::Resume(a, b) | Stmt::SetCodeState(a, b) | Stmt::ResumeLet(a, b, _, _) => {
                match st {
                    Stmt::RemoveRestore(..) => self.ctx("remove"),
                    Stmt::Resume(..) | Stmt::ResumeLet(..) => self.ctx("resume"),
                    Stmt::SetCodeState(..) => self.ctx("setCodeState"),
                    _ => {}
                }
                self.expr(a, lits);
                self.expr(b, lits);
            }
            Stmt::Macro(c, xs) => {
                self.call(Called::Alg(*c));
                self.macros.push((*c, xs));
                xs.iter().for_each(|x| self.expr(x, lits))
            }
            Stmt::Readings(_, lit, alts) => {
                self.stmt(lit, lits);
                self.alt += 1;
                for (_, ns) in alts {
                    self.nodes(ns, false);
                }
                self.alt -= 1;
            }
            Stmt::LetSuchThat(_, c, os) => {
                self.cond(c, lits);
                os.iter().for_each(|(_, e)| self.expr(e, lits));
            }
            Stmt::FindSuchThat(_, t, c, _, f) => {
                self.ty(t, lits);
                self.cond(c, lits);
                self.stmt(f, lits);
            }
        }
    }

    fn expr(&mut self, e: &'a Expr, lits: bool) {
        match e {
            Expr::Val(ValLit::Str(s, _)) | Expr::Code(s, _) | Expr::Term(s) => {
                if lits {
                    self.lits.push(s);
                }
            }
            Expr::Var(_)
            | Expr::Val(_)
            | Expr::Math(..)
            | Expr::Enum(_)
            | Expr::Intrinsic(_)
            | Expr::FieldName(_)
            | Expr::Nt(..)
            | Expr::Param(_)
            | Expr::Prod(..)
            | Expr::CodeUnit(..)
            | Expr::CodePoint(..)
            | Expr::Xref(..)
            | Expr::Closure(_)
            | Expr::Definition(..)
            | Expr::ThisNode => {}
            Expr::Child(k, nt, _) => self.children.push((*k, *nt)),
            Expr::Call(_, xs) | Expr::List(xs) => {
                if let Expr::Call(f, _) = e {
                    self.call_args.push((f, xs));
                }
                if let Expr::Call(Callee::Alg(c), _) = e {
                    self.call(Called::Alg(*c));
                    if self.alt == 0 {
                        self.alg_args.push((*c, xs));
                    }
                }
                xs.iter().for_each(|x| self.expr(x, lits))
            }
            Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
                match e {
                    Expr::Sdo(s, ..) => self.call(Called::Sdo(*s)),
                    Expr::IMethod(_, m, _) => self.call(Called::IMethod(*m)),
                    Expr::CMethod(_, m, _) => self.call(Called::CMethod(*m)),
                    _ => {}
                }
                self.expr(x, lits);
                xs.iter().for_each(|x| self.expr(x, lits));
            }
            Expr::Component(_, _, x) | Expr::Field(x, _) | Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) | Expr::Erratum(_, _, x) | Expr::Neg(x) | Expr::Paren(x) | Expr::Annot(_, x) | Expr::ResumedWith(x) | Expr::ChildOf(x, _, _) => {
                self.expr(x, lits)
            }
            Expr::TableStep(t, a, b) => {
                self.call(Called::Table(*t));
                self.tables.push(*t);
                self.expr(a, lits);
                self.expr(b, lits);
            }
            Expr::Index(a, b) | Expr::Bin(_, a, b) => {
                self.expr(a, lits);
                self.expr(b, lits);
            }
            Expr::Record(_, _, fs) => fs.iter().for_each(|(_, x)| self.expr(x, lits)),
            Expr::Extreme(_, _, t, c) => {
                self.ty(t, lits);
                self.cond(c, lits);
            }
            Expr::Phrase(p, hs) => {
                self.site(Site { id: *p, holes: hs, subject: None });
                self.holes(hs, lits);
            }
            Expr::Table(t, x) => {
                self.call(Called::Table(*t));
                self.expr(x, lits)
            }
            Expr::ThisValue(_) | Expr::NewTarget => self.frame += 1,
            Expr::Prose(_, ps) => {
                if matches!(&ps[..], [Part::Text(t)] if t == crate::conv::ARGUMENTS) {
                    self.frame += 1;
                }
                self.parts(ps, lits)
            }
        }
    }

    fn pred(&mut self, subject: &'a Expr, p: &'a Pred, lits: bool) {
        match p {
            Pred::IsVal(_, _, xs) => xs.iter().for_each(|x| self.expr(x, lits)),
            Pred::IsTy(_, _, ts) => ts.iter().for_each(|t| self.ty(t, lits)),
            Pred::Phrase(id, hs) => {
                self.site(Site { id: *id, holes: hs, subject: Some(subject) });
                self.holes(hs, lits);
            }
        }
    }

    fn cond(&mut self, c: &'a Cond, lits: bool) {
        match c {
            Cond::Preds(e, p, rest) => {
                self.expr(e, lits);
                self.pred(e, p, lits);
                rest.iter().for_each(|(_, p)| self.pred(e, p, lits));
            }
            Cond::Rel(_, a, b) => {
                self.expr(a, lits);
                self.expr(b, lits);
            }
            Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().for_each(|c| self.cond(c, lits)),
            Cond::Paren(c) => self.cond(c, lits),
            Cond::Alg(..) => {}
            Cond::Phrase(p, hs) => {
                self.site(Site { id: *p, holes: hs, subject: None });
                self.holes(hs, lits);
            }
            Cond::Prose(_, ps) => self.parts(ps, lits),
        }
    }

    fn ty(&mut self, t: &'a TyExpr, lits: bool) {
        match t {
            TyExpr::Sort(..) | TyExpr::Nt(..) | TyExpr::Var(..) => {}
            TyExpr::ListOf(_, t) => self.ty(t, lits),
            TyExpr::Union(_, _, ts) => ts.iter().for_each(|t| self.ty(t, lits)),
            TyExpr::Completion(t) => t.iter().for_each(|t| self.ty(t, lits)),
            TyExpr::Interval(t, lo, hi) => {
                self.ty(t, lits);
                self.expr(lo, lits);
                self.expr(hi, lits);
            }
            TyExpr::Value(e) => self.expr(e, lits),
            TyExpr::Record(fs) => fs.iter().for_each(|(_, t)| self.ty(t, lits)),
            TyExpr::That(t, p, rest) => {
                self.ty(t, lits);
                for p in std::iter::once(p).chain(rest.iter().map(|x| &x.1)) {
                    match p {
                        Pred::IsVal(_, _, xs) => xs.iter().for_each(|x| self.expr(x, lits)),
                        Pred::IsTy(_, _, ts) => ts.iter().for_each(|t| self.ty(t, lits)),
                        Pred::Phrase(id, hs) => {
                            self.site(Site { id: *id, holes: hs, subject: None });
                            self.holes(hs, lits);
                        }
                    }
                }
            }
            TyExpr::Phrase(p, hs) => {
                self.site(Site { id: *p, holes: hs, subject: None });
                self.holes(hs, lits);
            }
            TyExpr::Prose(ps) => self.parts(ps, lits),
        }
    }
}

/// The overlay phrases whose literals spell out what the spec states in prose (`literals="spelled"`).
const SPELLED: &[&str] = &["ph-ascii-word-characters", "ph-intrinsic-assoc", "ph-not-in-base64-alphabet", "ph-representation-radix", "ph-upper-hex"];

/// The tables the steps refer to by `the value that … corresponds to in <table>`.
pub fn table_steps(ns: &[Node]) -> Vec<usize> {
    let mut f = Found::default();
    f.nodes(ns, false);
    f.tables
}

/// The reads of the call's *this* value, NewTarget or arguments List, closures' bodies excluded.
pub fn frame_reads(ns: &[Node]) -> usize {
    let mut f = Found::default();
    f.nodes(ns, false);
    f.frame
}

/// The callees and execution-context forms of steps, in text order, an erratum's other readings excluded.
pub fn callees(ns: &[Node]) -> Vec<Called<'_>> {
    let mut f = Found::default();
    f.nodes(ns, false);
    f.calls
}

/// The variables a step binds on every path through it: a branch's when every branch binds them, a loop's never.
fn definite(st: &Stmt) -> Vec<Id> {
    let block = |b: &Body| match b {
        Body::Inline(s) => definite(s),
        Body::Block(ns) => ns.iter().flat_map(|n| definite(&n.stmt)).collect(),
    };
    let all = |bs: Vec<Vec<Id>>| bs.split_first().map(|(a, rest)| a.iter().copied().filter(|x| rest.iter().all(|b| b.contains(x))).collect()).unwrap_or_default();
    match st {
        Stmt::Let(x, _) | Stmt::FindSuchThat(x, ..) | Stmt::ResumeLet(_, _, x, _) => vec![*x],
        Stmt::LetSuchThat(xs, ..) => xs.clone(),
        Stmt::IfElse(_, a, b) => all(vec![definite(a), definite(b)]),
        Stmt::If(_, b, arms, Some(els)) => all(std::iter::once(b).chain(arms.iter().map(|a| &a.body)).chain([&els.body]).map(block).collect()),
        Stmt::Readings(_, lit, _) => definite(lit),
        _ => vec![],
    }
}

/// Every variable steps, their readings included, bind, at any depth.
fn binders(ns: &[Node], out: &mut Vec<Id>) {
    fn stmt(st: &Stmt, out: &mut Vec<Id>) {
        match st {
            Stmt::Let(x, _)
            | Stmt::FindSuchThat(x, ..)
            | Stmt::ResumeLet(_, _, x, _)
            | Stmt::ForEach(x, ..)
            | Stmt::ForEachRec(_, x, ..)
            | Stmt::ForSuchThat(x, ..)
            | Stmt::ForKeys(x, ..)
            | Stmt::ForIndex(x, ..)
            | Stmt::ForChildren(x, _)
            | Stmt::ForChildrenOf(x, ..)
            | Stmt::ForRange(x, ..) => out.push(*x),
            Stmt::LetSuchThat(xs, ..) => out.extend(xs),
            _ => {}
        }
        for i in nested(st) {
            match i {
                Inner::Block(ns) => binders(ns, out),
                Inner::Stmt(s) => stmt(s, out),
            }
        }
        if let Stmt::Readings(_, _, alts) = st {
            alts.iter().for_each(|(_, ns)| binders(ns, out));
        }
    }
    ns.iter().for_each(|n| stmt(&n.stmt, out));
}

/// A step nested in another, or a block of them.
enum Inner<'a> {
    Block(&'a [Node]),
    Stmt(&'a Stmt),
}

/// A step's nested steps, its readings' excepted.
fn nested(st: &Stmt) -> Vec<Inner<'_>> {
    fn body(b: &Body) -> Inner<'_> {
        match b {
            Body::Inline(s) => Inner::Stmt(s),
            Body::Block(ns) => Inner::Block(ns),
        }
    }
    match st {
        Stmt::If(_, b, arms, els) => std::iter::once(b).chain(arms.iter().chain(els).map(|a| &a.body)).map(body).collect(),
        Stmt::IfElse(_, a, b) => vec![Inner::Stmt(a), Inner::Stmt(b)],
        Stmt::FindSuchThat(.., f) | Stmt::Readings(_, f, _) => vec![Inner::Stmt(f)],
        Stmt::Repeat(ns) | Stmt::RepeatWhile(_, ns) | Stmt::RepeatUntil(_, ns) | Stmt::RepeatN(_, ns) => vec![Inner::Block(ns)],
        Stmt::ForEach(.., b)
        | Stmt::ForEachRec(.., b)
        | Stmt::ForSuchThat(.., b)
        | Stmt::ForKeys(.., b)
        | Stmt::ForIndex(_, _, b)
        | Stmt::ForChildren(_, b)
        | Stmt::ForChildrenOf(_, _, b)
        | Stmt::ForRange(.., b) => vec![body(b)],
        Stmt::WithSteps(_, ns) => vec![Inner::Block(ns)],
        _ => vec![],
    }
}

/// The readings' binders already bound on every path to their step (`bound` from the start), not by the step: readings share the frame.
pub fn reading_clashes(bound: &[Id], ns: &[Node]) -> Vec<Id> {
    fn block(ns: &[Node], live: &mut Vec<Id>, out: &mut Vec<Id>) {
        for n in ns {
            stmt(&n.stmt, live, out);
            live.extend(definite(&n.stmt));
        }
    }
    fn stmt(st: &Stmt, live: &[Id], out: &mut Vec<Id>) {
        if let Stmt::Readings(_, lit, alts) = st {
            let own = definite(lit);
            let mut read = Vec::new();
            alts.iter().for_each(|(_, ns)| binders(ns, &mut read));
            for x in read {
                if live.contains(&x) && !own.contains(&x) && !out.contains(&x) {
                    out.push(x);
                }
            }
        }
        for i in nested(st) {
            match i {
                Inner::Block(ns) => block(ns, &mut live.to_vec(), out),
                Inner::Stmt(s) => stmt(s, live, out),
            }
        }
    }
    let mut out = Vec::new();
    block(ns, &mut bound.to_vec(), &mut out);
    out
}

/// A literal's form as a reader of spec.html sees it: entities and backslash escapes undone.
fn decoded(raw: &str) -> String {
    crate::text::unescape(&crate::text::unbackslash(raw))
}

/// Every phrase site whose values do not fit its meaning's declared parameters, and every
/// literal its algorithm's text does not contain, and every Else step kept as prose.
pub fn check(sp: &Spec, g: &Grammar, dt: &Data) -> Vec<String> {
    let d = &dt.decls;
    let mut out = Vec::new();
    let mut spelled: Vec<&str> = g.overlay.phrases.iter().filter(|p| p.spelled).map(|p| p.id.as_str()).collect();
    spelled.sort();
    if spelled != SPELLED {
        out.push(format!("the phrases marked literals=\"spelled\" are {spelled:?}, not checks::SPELLED"));
    }
    // each algorithm's sites and literals, with its decoded text and its name
    let mut units: Vec<(String, String, Found, &crate::data::Hdr)> = Vec::new();
    let mut rets = std::collections::HashMap::new();
    for a in &dt.algs {
        if let Some(s) = a.hdr.ret.as_ref().and_then(|t| ty_sort(d, t)) {
            rets.entry(d.cid(a.clause)).or_insert(s);
        }
    }
    for a in &dt.algs {
        let mut f = Found::default();
        f.nodes(&a.body, true);
        for c in &a.closures {
            f.nodes(&c.body, true);
        }
        let name = format!("{} #{}", sp.clauses[a.clause].id, a.idx);
        units.push((name, decoded(&sp.algs[a.alg].raw), f, &a.hdr));
    }
    let mut phrase_lits: Vec<(Id, String, Vec<&str>)> = Vec::new();
    for pa in &dt.phrase_algs {
        let mut f = Found::default();
        f.nodes(&pa.body, true);
        for c in &pa.closures {
            f.nodes(&c.body, true);
        }
        phrase_lits.push((pa.clause, pa.id.clone(), std::mem::take(&mut f.lits)));
        units.push((pa.id.clone(), String::new(), f, &pa.hdr));
    }
    // 1, 2: each site's values against its meaning's parameters
    for (name, _, f, hdr) in &units {
        let mut cx = Cx { g, d, vars: Default::default(), rets: &rets };
        for (x, t, _, _) in &hdr.params {
            if let Some(s) = t.as_ref().and_then(|t| ty_sort(d, t)) {
                cx.vars.insert(*x, s);
            }
        }
        for x in &f.rebound {
            cx.vars.remove(x);
        }
        let mut seen = std::collections::HashSet::new();
        for (x, e) in &f.lets {
            let s = expr_sort(&cx, e);
            if !seen.insert(*x) || f.rebound.contains(x) || s.is_none() {
                cx.vars.remove(x);
                seen.insert(*x);
                continue;
            }
            cx.vars.insert(*x, s.unwrap());
        }
        for s in &f.sites {
            let p = &d.phrases[s.id];
            let params: Vec<(String, (Option<S>, Option<&Expr>))>;
            let mut subject: Option<String> = None;
            match &p.meaning {
                Some(Meaning::Prim { prim, args, .. }) => {
                    let Some(sig) = crate::sig::all(g, d.prims.name(*prim)).into_iter().find(|s| s.params.len() == args.len() || s.variadic) else { continue };
                    let mut ps = Vec::new();
                    for (k, a) in args.iter().enumerate() {
                        let Some(t) = sig.params.get(k).or(if sig.variadic { sig.params.last() } else { None }) else { continue };
                        match a {
                            PArg::Hole(i) => {
                                if let Some(h) = s.holes.get(*i) {
                                    ps.push((t.clone(), hole_arg(&cx, h)));
                                }
                            }
                            PArg::Spread(i) => {
                                if let Some(Hole::L(_, es)) = s.holes.get(*i) {
                                    ps.extend(es.iter().map(|e| (t.clone(), (expr_sort(&cx, e), Some(e)))));
                                }
                            }
                            PArg::Subject => subject = Some(t.clone()),
                            _ => {}
                        }
                    }
                    params = ps;
                }
                Some(Meaning::Alg(c)) => {
                    let Some(pa) = dt.phrase_algs.iter().find(|x| x.clause == *c) else { continue };
                    let Some(op) = g.overlay.phrases.iter().find(|x| x.id == pa.id) else { continue };
                    let Some(alg) = &op.alg else { continue };
                    let layout = g.phrase_layout(op);
                    let values: Vec<&Hole> = s.holes.iter().enumerate().filter(|(i, _)| !layout.get(*i).copied().unwrap_or(false)).map(|x| x.1).collect();
                    let nvars = op.vars().len();
                    params = alg.params.iter().take(nvars).zip(values).map(|((_, t), h)| (t.clone(), hole_arg(&cx, h))).collect();
                    if op.subject.is_some() {
                        subject = alg.params.get(nvars).map(|x| x.1.clone());
                    }
                }
                None => continue,
            }
            let who = format!("{name}: phrase {} ({} {})", s.id, p.cat, p.name);
            if matches!(p.meaning, Some(Meaning::Prim { .. })) {
                for (_, (_, h)) in &params {
                    if let Some(Expr::Index(base, _)) = h {
                        if params.iter().any(|(_, (_, k))| matches!(k, Some(e) if *e == base.as_ref())) {
                            out.push(format!("{who}: an element of an argument passed beside it"));
                        }
                    }
                }
            }
            for (t, (got, _)) in params {
                if let (Some(want), Some(got)) = (admits(&t), got) {
                    if mismatch(got, &want) {
                        out.push(format!("{who}: a {got:?} for a parameter of type {t}"));
                    }
                }
            }
            if let (Some(t), Some(e)) = (subject, s.subject) {
                if let (Some(want), Some(got)) = (admits(&t), expr_sort(&cx, e)) {
                    if mismatch(got, &want) {
                        out.push(format!("{who}: a {got:?} subject for a parameter of type {t}"));
                    }
                }
            }
        }
    }
    // 3: a Parse Node passed where the callee's parameter is a nonterminal
    for (name, _, f, _) in &units {
        for (callee, xs) in &f.call_args {
            let (who, nts) = match callee {
                Callee::Alg(c) => {
                    let Some(cl) = d.pos(*c).map(|k| &sp.clauses[k]) else { continue };
                    let ts: Vec<String> = crate::header::parse(cl).params.into_iter().map(|p| p.ty.unwrap_or_default()).collect();
                    (cl.id.clone(), crate::sig::nt_params(&ts))
                }
                Callee::Prim(p) => {
                    let Some(sig) = crate::sig::of(g, d.prims.name(*p)) else { continue };
                    (d.prims.name(*p).to_string(), crate::sig::nt_params(&sig.params))
                }
            };
            for k in nts {
                if matches!(xs.get(k), Some(Expr::Child(..) | Expr::ChildOf(..) | Expr::ThisNode)) {
                    out.push(format!("{name}: {who}: a Parse Node for nonterminal parameter {k}"));
                }
            }
        }
    }
    // 4: literals against their algorithm's text; a phrase algorithm's, against its sites'
    for (name, text, f, _) in &units {
        if text.is_empty() {
            continue;
        }
        for l in &f.lits {
            if !text.contains(*l) {
                out.push(format!("{name}: the literal {l:?} is not in its algorithm's text"));
            }
        }
    }
    for (c, id, lits) in phrase_lits.iter().filter(|x| !SPELLED.contains(&x.1.as_str())) {
        let texts: Vec<&str> = units
            .iter()
            .filter(|(_, t, f, _)| !t.is_empty() && f.sites.iter().any(|s| matches!(d.phrases[s.id].meaning, Some(Meaning::Alg(k)) if k == *c)))
            .map(|(_, t, _, _)| t.as_str())
            .collect();
        if texts.is_empty() {
            continue;
        }
        for l in lits {
            if !texts.iter().any(|t| t.contains(*l)) {
                out.push(format!("{id}: the literal {l:?} is in none of its sites' algorithms"));
            }
        }
    }
    // 4: a reading's binders against the live variables of its algorithm
    for a in &dt.algs {
        let name = format!("{} #{}", sp.clauses[a.clause].id, a.idx);
        let params: Vec<Id> = a.hdr.params.iter().map(|p| p.0).chain(a.hdr.recv.as_ref().map(|r| r.0)).collect();
        let mut bodies = vec![(params, &a.body)];
        for c in &a.closures {
            bodies.push((c.params.iter().flatten().chain(&c.caps).copied().collect(), &c.body));
        }
        for (bound, body) in bodies {
            for x in reading_clashes(&bound, body) {
                out.push(format!("{name}: a reading binds _{}_, which is bound on every path to the step it replaces", a.vars.names[x]));
            }
        }
    }
    // 5: every Else step joined its If
    for (name, _, f, _) in &units {
        if f.else_prose > 0 {
            out.push(format!("{name}: {} Else step(s) kept as prose", f.else_prose));
        }
    }
    out
}

/// Every macro use the machine cannot expand: an argument that is not a variable, or no expansion
/// (the clause's second algorithm) over exactly its parameters, without closures and macro uses.
pub fn macro_uses(sp: &Spec, dt: &Data) -> Vec<String> {
    let mut out = Vec::new();
    let mut units: Vec<(String, Found)> = Vec::new();
    for a in &dt.algs {
        let mut f = Found::default();
        f.nodes(&a.body, false);
        for c in &a.closures {
            f.nodes(&c.body, false);
        }
        units.push((format!("{} #{}", sp.clauses[a.clause].id, a.idx), f));
    }
    for pa in &dt.phrase_algs {
        let mut f = Found::default();
        f.nodes(&pa.body, false);
        for c in &pa.closures {
            f.nodes(&c.body, false);
        }
        units.push((pa.id.clone(), f));
    }
    for (name, f) in &units {
        for (c, xs) in &f.macros {
            let who = format!("{name}: macro {}", dt.decls.clauses.name(*c));
            if !xs.iter().all(|x| matches!(x, Expr::Var(_))) {
                out.push(format!("{who}: an argument that is not a variable"));
            }
            match dt.algs.iter().find(|g| dt.decls.cid(g.clause) == *c && g.idx == 1) {
                None => out.push(format!("{who}: no expansion")),
                Some(g) => {
                    let mut e = Found::default();
                    e.nodes(&g.body, false);
                    if g.vars.names.len() != xs.len() || g.hdr.params.len() != xs.len() || !g.closures.is_empty() || !e.macros.is_empty() {
                        out.push(format!("{who}: its expansion is not over exactly its {} parameters, or has closures or macro uses", xs.len()));
                    }
                }
            }
        }
    }
    out
}

/// Every right-hand-side child a row names (`|X|`, `the |X|`, `the first |X|` …) that no production
/// of the row has: a production without it reads it as not present, so a wrong symbol would be absent.
/// A phrase algorithm runs on its caller's node and has no productions: any such child there.
pub fn row_children(sp: &Spec, dt: &Data) -> Vec<String> {
    let d = &dt.decls;
    let mut rows: Vec<(String, &[usize], Found)> = Vec::new();
    for a in dt.algs.iter().filter(|a| !a.prods.is_empty()) {
        let mut f = Found::default();
        f.nodes(&a.body, false);
        a.closures.iter().for_each(|c| f.nodes(&c.body, false));
        a.readings.iter().for_each(|r| f.nodes(&r.3, false));
        rows.push((format!("{} #{}", sp.clauses[a.clause].id, a.idx), &a.prods, f));
    }
    for e in &dt.eqs {
        let mut f = Found::default();
        f.nodes(&e.body, false);
        rows.push((format!("{} #{}", sp.clauses[e.clause].id, e.idx), &e.prods, f));
    }
    for e in &dt.early {
        let mut f = Found::default();
        f.nodes(&e.body, false);
        if let Some((_, rs)) = &e.readings {
            rs.iter().for_each(|r| f.nodes(&r.1, false));
        }
        rows.push((format!("{} early #{}", sp.clauses[e.clause].id, e.idx), &e.prods, f));
    }
    for r in &dt.reading_rows {
        let mut f = Found::default();
        f.nodes(&r.body, false);
        r.closures.iter().for_each(|c| f.nodes(&c.body, false));
        rows.push((r.id.clone(), &r.prods, f));
    }
    let mut out = Vec::new();
    for (name, prods, f) in rows {
        let rhs = crate::conv::prod_rhs(&dt.env.gl, prods);
        for (k, nt) in f.children {
            let x = d.nts.name(nt);
            if k != 3 && k != 6 && !rhs.contains(x) {
                out.push(format!("{name}: |{x}| is on no right-hand side of the row's productions"));
            }
        }
    }
    for pa in &dt.phrase_algs {
        let mut f = Found::default();
        f.nodes(&pa.body, false);
        pa.closures.iter().for_each(|c| f.nodes(&c.body, false));
        for (k, nt) in f.children {
            if k != 3 && k != 6 {
                out.push(format!("{}: |{}| in a phrase algorithm, which has no productions", pa.id, d.nts.name(nt)));
            }
        }
    }
    out
}

/// The operations whose second parameter, _intrinsicDefaultProto_, is an intrinsic object's name.
const INTRINSIC_DEFAULT: &[&str] = &["sec-getprototypefromconstructor", "sec-ordinarycreatefromconstructor"];

/// Every String literal passed as _intrinsicDefaultProto_ that names no intrinsic object of the
/// realm table `r` (`%name%` for one of its objects' intrinsic names).
pub fn intrinsic_defaults(sp: &Spec, dt: &Data, r: &crate::realm::Realm) -> Vec<String> {
    let mut out = Vec::new();
    let mut units: Vec<(String, Found)> = Vec::new();
    for a in &dt.algs {
        let mut f = Found::default();
        f.nodes(&a.body, false);
        a.closures.iter().for_each(|c| f.nodes(&c.body, false));
        units.push((format!("{} #{}", sp.clauses[a.clause].id, a.idx), f));
    }
    for pa in &dt.phrase_algs {
        let mut f = Found::default();
        f.nodes(&pa.body, false);
        pa.closures.iter().for_each(|c| f.nodes(&c.body, false));
        units.push((pa.id.clone(), f));
    }
    for (name, f) in &units {
        for (c, xs) in &f.alg_args {
            let callee = dt.decls.clauses.name(*c);
            if !INTRINSIC_DEFAULT.contains(&callee) {
                continue;
            }
            if let Some(Expr::Val(ValLit::Str(s, _))) = xs.get(1) {
                let named = s.strip_prefix('%').and_then(|x| x.strip_suffix('%')).is_some_and(|n| r.by_name(n).is_some());
                if !named {
                    out.push(format!("{name}: {callee}'s _intrinsicDefaultProto_ {s:?} names no intrinsic object of the realm table"));
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_types_admit_their_sorts() {
        assert_eq!(admits("a List of code points"), Some(vec![S::List]));
        assert_eq!(admits("a code point, a character or a String"), Some(vec![S::CodePoint, S::CodePoint, S::CodeUnit, S::Str]));
        assert_eq!(admits("a non-negative integer or a BigInt"), Some(vec![S::Math, S::BigInt]));
        assert_eq!(admits("an ECMAScript language value"), None);
        assert_eq!(admits("a nonterminal in one of the ECMAScript grammars"), Some(vec![S::Nt]));
    }

    #[test]
    fn nonterminal_parameters() {
        assert_eq!(crate::sig::nt_params(&["a sequence of Unicode code points", "a nonterminal in one of the ECMAScript grammars", "a Boolean"]), vec![1]);
        assert_eq!(crate::sig::nt_params(&["a nonterminal", "a List of nonterminals", "a Parse Node"]), vec![0]);
    }

    #[test]
    fn mismatches_are_definite() {
        assert!(mismatch(S::Selector, &[S::List]));
        assert!(mismatch(S::Str, &[S::Field]));
        assert!(mismatch(S::BigInt, &[S::Math]));
        assert!(!mismatch(S::CodePoint, &[S::Math]));
        assert!(!mismatch(S::Math, &[S::CodeUnit]));
        assert!(mismatch(S::Elem, &[S::List]));
        assert!(!mismatch(S::Elem, &[S::Math]));
    }
}
