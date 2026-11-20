//! The data printed back as spec.html's text (`Ecma.Notation.Print` mirrors it):
//! each constructor emits words and sub-terms as parts, joined by the
//! canonical spacing rules of `token::join`; layout comes from step depth.

use crate::ast::*;
use crate::decls::{Decls, Piece};
use crate::token::Part;

pub fn xref_text(e: &Expr) -> String {
    match e {
        Expr::Xref(h, XrefForm::Plain, _) => format!("<emu-xref href=\"#{h}\"></emu-xref>"),
        Expr::Xref(h, XrefForm::Title, _) => format!("<emu-xref href=\"#{h}\" title></emu-xref>"),
        Expr::Xref(h, XrefForm::Content(c), _) => format!("<emu-xref href=\"#{h}\">{c}</emu-xref>"),
        _ => String::new(),
    }
}

/// An English list node of `len` items holding `k` expressions is written
/// canonically: `a or b`, `a, b, or c`.
pub fn english_ok(len: usize, k: usize) -> bool {
    (k == 2 && len == 3) || (k >= 3 && len == 2 * k)
}

/// The article before an error name.
pub fn article_for(name: &str) -> &'static str {
    if name.starts_with(['A', 'E', 'I', 'O']) {
        "an"
    } else {
        "a"
    }
}

/// Deferred lines after a step's own line.
enum After<'a> {
    Kids(&'a [Node]),
    Bullets(&'a [Expr]),
    Raw(&'a str),
}

pub struct Printer<'a> {
    pub d: &'a Decls,
    pub vars: &'a [String],
    pub clos: &'a [CloLit],
    parts: Vec<Part>,
    glue: bool,
    after: Vec<After<'a>>,
}

fn conj_word(c: Conj) -> &'static str {
    match c {
        Conj::And => "and",
        Conj::Or => "or",
    }
}

impl<'a> Printer<'a> {
    pub fn new(d: &'a Decls, vars: &'a [String], clos: &'a [CloLit]) -> Printer<'a> {
        Printer { d, vars, clos, parts: Vec::new(), glue: false, after: Vec::new() }
    }

    pub(crate) fn w(&mut self, s: &str) {
        let g = std::mem::take(&mut self.glue);
        self.parts.push(Part::Text(s.to_string(), g));
    }

    pub(crate) fn g(&mut self) -> &mut Self {
        self.glue = true;
        self
    }

    pub(crate) fn gw(&mut self, s: &str) {
        self.glue = true;
        self.w(s);
    }

    pub(crate) fn words(&mut self, s: &str) {
        for x in s.split(' ') {
            self.w(x);
        }
    }

    fn raw(&mut self, s: String) {
        let g = std::mem::take(&mut self.glue);
        self.parts.push(Part::Raw(s, g));
    }

    fn sep_list<T>(&mut self, xs: &'a [T], sep: &str, f: fn(&mut Self, &'a T)) {
        for (i, x) in xs.iter().enumerate() {
            if i > 0 {
                self.w(sep);
            }
            f(self, x);
        }
    }

    pub(crate) fn english<T>(&mut self, xs: &'a [T], conj: &str, f: fn(&mut Self, &'a T)) {
        let n = xs.len();
        for (i, x) in xs.iter().enumerate() {
            if i > 0 {
                if n > 2 {
                    self.w(",");
                }
                if i == n - 1 {
                    self.w(conj);
                }
            }
            f(self, x);
        }
    }

    /// A variable; a call frame slot prints as its words.
    pub fn var(&mut self, x: &Id) {
        match self.vars[*x].strip_prefix(crate::conv::FRAME) {
            Some(words) => self.words(words),
            None => {
                let s = format!("_{}_", self.vars[*x]);
                self.w(&s);
            }
        }
    }

    fn prose(&mut self, parts: &'a [Part2]) {
        let mut s = String::new();
        for p in parts {
            match p {
                crate::ast::Part::Text(t) => s.push_str(t),
                crate::ast::Part::Hole(Hole::E(Expr::Var(x))) => match self.vars[*x].strip_prefix(crate::conv::FRAME) {
                    Some(words) => s.push_str(words),
                    None => s.push_str(&format!("_{}_", self.vars[*x])),
                },
                crate::ast::Part::Hole(h) => self.trailing(h),
            }
        }
        if !s.is_empty() {
            self.raw(s);
        }
    }

    fn numeral(n: &Numeral) -> String {
        match n {
            Numeral::Dec(n) => n.to_string(),
            Numeral::Hex(_, d) => format!("0x{d}"),
            Numeral::Frac(w, f, places) => format!("{w}.{f:0>places$}"),
        }
    }

    fn mag(m: &Mag) -> String {
        match m {
            Mag::Num(n) => Self::numeral(n),
            Mag::Inf => "∞".into(),
        }
    }

    fn sign(s: Sign) -> &'static str {
        match s {
            Sign::None => "",
            Sign::Plus => "+",
            Sign::Minus => "-",
        }
    }

    pub fn val_text(&self, v: &ValLit) -> String {
        let sub = |s: &Sub| match s {
            Sub::None => "",
            Sub::F => "<sub>𝔽</sub>",
            Sub::Z => "<sub>ℤ</sub>",
        };
        match v {
            ValLit::Undefined => "*undefined*".into(),
            ValLit::Null => "*null*".into(),
            ValLit::True => "*true*".into(),
            ValLit::False => "*false*".into(),
            ValLit::This => "*this*".into(),
            ValLit::Str(s, w) => format!("*\"{}\"*", written(s, w)),
            ValLit::NaN(s) => format!("*NaN*{}", sub(s)),
            ValLit::Num(sg, m, s) => format!("*{}{}*{}", Self::sign(*sg), Self::mag(m), sub(s)),
            ValLit::Err(i) => format!("*{}*", self.d.fields.name(*i)),
            ValLit::BigN(n) => format!("`{}n`", Self::numeral(n)),
        }
    }

    pub fn expr(&mut self, e: &'a Expr) {
        match e {
            Expr::Var(x) => self.var(x),
            Expr::Val(v) => {
                let s = self.val_text(v);
                self.w(&s)
            }
            Expr::Math(sg, m) => {
                if *sg != Sign::None {
                    self.w(Self::sign(*sg));
                    self.g();
                }
                self.w(&Self::mag(m));
            }
            Expr::Enum(i) => self.w(&format!("~{}~", self.d.enums.name(*i))),
            Expr::Intrinsic(i) => self.w(&format!("%{}%", self.d.fields.name(*i))),
            Expr::FieldName(i) => self.w(&format!("[[{}]]", self.d.fields.name(*i))),
            Expr::Nt(i, xs) => self.w(&format!("|{}{}|", self.d.nts.name(*i), goal_text(self.d, xs))),
            Expr::Param(p) => self.w(&format!("<sub>[{}]</sub>", self.d.params.name(*p))),
            Expr::Prod(_, raw) => self.w(raw),
            Expr::CodeUnit(_, d, name) | Expr::CodePoint(_, d, name) => {
                let pre = if matches!(e, Expr::CodeUnit(..)) { "0x" } else { "U+" };
                self.w(&format!("{pre}{d}"));
                if let Some(n) = name {
                    self.w("(");
                    self.words(n);
                    self.w(")");
                }
            }
            Expr::Code(s, w) => self.w(&format!("`{}`", written(s, w))),
            Expr::Term(t) => self.w(&format!("`{t}`")),
            Expr::Call(Callee::Prim(p), args) if self.d.prims.name(*p) == "WellKnownSymbol" && matches!(args.as_slice(), [Expr::Val(ValLit::Str(_, w))] if w.is_empty()) => {
                let [Expr::Val(ValLit::Str(s, _))] = args.as_slice() else { unreachable!() };
                self.w(&format!("%{s}%"));
            }
            Expr::Call(f, args) => {
                let name = match f {
                    Callee::Alg(c) => self.d.ops[*c].clone(),
                    Callee::Prim(p) => self.d.prims.name(*p).to_string(),
                };
                self.w(&name);
                self.g().args(args);
            }
            Expr::Sdo(s, a, subj, args) => {
                if *a == Article::The {
                    self.w("the");
                }
                self.w(self.d.sdos.name(*s));
                self.w("of");
                self.expr(subj);
                if args.len() == 1 {
                    self.w("with");
                    self.w("argument");
                    self.expr(&args[0]);
                } else if args.len() > 1 {
                    self.w("with");
                    self.w("arguments");
                    self.english(args, "and", Self::expr);
                }
            }
            Expr::Component(c, a, subj) => {
                if *a == Article::The {
                    self.w("the");
                }
                self.w(self.d.fields.name(*c));
                self.w("of");
                self.expr(subj);
            }
            Expr::Field(b, f) => {
                self.expr(b);
                self.gw(".");
                self.gw(&format!("[[{}]]", self.d.fields.name(*f)));
            }
            Expr::IMethod(b, m, args) => {
                self.expr(b);
                self.gw(".");
                self.gw(&format!("[[{}]]", self.d.fields.name(*m)));
                self.g().args(args);
            }
            Expr::CMethod(b, m, args) => {
                self.expr(b);
                self.gw(".");
                self.gw(self.d.methods.name(*m));
                self.g().args(args);
            }
            Expr::Apply(f, args) => {
                self.expr(f);
                self.g().args(args);
            }
            Expr::Index(b, i) => {
                self.expr(b);
                self.gw("[");
                self.g().expr(i);
                self.gw("]");
            }
            Expr::Q(x) => {
                self.w("?");
                self.expr(x);
            }
            Expr::Bang(x) | Expr::BangAt(_, x) => {
                self.w("!");
                self.expr(x);
            }
            Expr::Neg(x) => {
                self.w("-");
                self.g().expr(x);
            }
            Expr::Bin(BinOp::Pow, a, b) => {
                self.expr(a);
                self.gw("<sup>");
                self.g().expr(b);
                self.gw("</sup>");
            }
            Expr::Bin(op, a, b) => {
                self.expr(a);
                self.w(match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "×",
                    BinOp::Div => "/",
                    BinOp::Modulo => "modulo",
                    BinOp::Plus => "plus",
                    BinOp::Times => "times",
                    BinOp::Pow => unreachable!(),
                });
                self.expr(b);
            }
            Expr::Paren(x) => {
                self.w("(");
                self.expr(x);
                self.w(")");
            }
            Expr::List(xs) => {
                self.w("«");
                self.sep_list(xs, ",", Self::expr);
                self.w("»");
            }
            Expr::Record(a, k, fs) => {
                if *a == Article::The {
                    self.w("the");
                }
                if let Some(k) = k {
                    self.words(self.d.sorts.name(*k));
                }
                self.w("{");
                for (i, (f, x)) in fs.iter().enumerate() {
                    if i > 0 {
                        self.w(",");
                    }
                    self.w(&format!("[[{}]]", self.d.fields.name(*f)));
                    self.gw(":");
                    self.expr(x);
                }
                self.w("}");
            }
            Expr::Annot(attrs, x) => {
                self.w(&meta_tag(attrs));
                self.g().expr(x);
                self.gw("</emu-meta>");
            }
            Expr::Xref(..) => self.w(&xref_text(e)),
            Expr::Table(_, x) | Expr::Erratum(_, _, x) => self.expr(x),
            Expr::Definition(x, _) => {
                self.words("the definition specified in");
                self.expr(x);
            }
            Expr::TableStep(_, k, x) => {
                self.words("the value that");
                self.expr(k);
                self.words("corresponds to in");
                self.expr(x);
            }
            Expr::Extreme(mx, x, t, c) => {
                self.w("the");
                self.w(if *mx { "largest" } else { "smallest" });
                self.ty(t);
                self.var(x);
                self.words(if *mx { "( closest to +∞ )" } else { "( closest to -∞ )" });
                self.words("such that");
                self.cond(c);
            }
            Expr::Closure(site) => {
                let CloLit { kind: k, atomic, params, caps, body, .. } = &self.clos[*site];
                self.w("a");
                self.w("new");
                self.words(match k {
                    CloKind::Abstract => "Abstract Closure",
                    CloKind::Job => "Job Abstract Closure",
                    CloKind::Matcher => "Matcher",
                    CloKind::MatcherContinuation => "MatcherContinuation",
                    CloKind::ReadModifyWrite => "read-modify-write modification function",
                });
                self.w("with");
                match params {
                    None => {
                        self.w("no");
                        self.w("parameters");
                    }
                    Some(ps) => {
                        self.w("parameters");
                        self.w("(");
                        self.sep_list(ps, ",", Self::var);
                        self.w(")");
                    }
                }
                self.w("that");
                self.w("captures");
                if caps.is_empty() {
                    self.w("nothing");
                } else {
                    self.english(caps, "and", Self::var);
                }
                self.words("and performs the following steps");
                if *atomic {
                    self.w("atomically");
                }
                self.words("when called");
                self.w(":");
                self.after.push(After::Kids(body));
            }
            Expr::ThisValue(bare) => self.words(if *bare { "*this* value" } else { "the *this* value" }),
            Expr::NewTarget => self.w("NewTarget"),
            Expr::ThisNode => self.words("this Parse Node"),
            Expr::Child(k, n, suf) => {
                if *k < 5 || *k == 7 {
                    self.w("the");
                }
                if let Some(o) = ["first", "second", "third", "derived", "", "", "", "fourth"].get(*k).filter(|o| !o.is_empty()) {
                    self.w(o);
                }
                self.w(&format!("|{}{}|", self.d.nts.name(*n), suf));
            }
            Expr::ChildOf(_, n, suf) => self.w(&format!("|{}{}|", self.d.nts.name(*n), suf)),
            Expr::ResumedWith(x) => {
                self.words("the Completion Record with which");
                self.expr(x);
                self.words("was just resumed");
            }
            Expr::Phrase(p, hs) => self.phrase(*p, hs),
            Expr::Prose(_, ps) => self.prose(ps),
        }
    }

    fn args(&mut self, args: &'a [Expr]) {
        self.w("(");
        self.sep_list(args, ",", Self::expr);
        self.w(")");
    }

    pub fn cond(&mut self, c: &'a Cond) {
        match c {
            Cond::Preds(e, p, rest) => {
                self.expr(e);
                self.preds(p, rest);
            }
            Cond::Rel(op, a, b) => {
                self.expr(a);
                self.w(match op {
                    RelOp::Lt => "&lt;",
                    RelOp::Le => "≤",
                    RelOp::Gt => ">",
                    RelOp::Ge => "≥",
                    RelOp::Eq => "=",
                    RelOp::Ne => "≠",
                });
                self.expr(b);
            }
            Cond::And(ConnForm::Following, cs) | Cond::Or(ConnForm::Following, cs) => {
                let (conj, q) = match (c, cs.len()) {
                    (Cond::And(..), 2) => ("and", "both"),
                    (Cond::And(..), _) => ("and", "all"),
                    _ => ("or", "any"),
                };
                self.words(&format!("{q} of the following conditions are true :"));
                let n = cs.len();
                for (i, x) in cs.iter().enumerate() {
                    if i > 0 {
                        if n > 2 {
                            self.w(",");
                        }
                        if i == n - 1 {
                            self.w(conj);
                        }
                    }
                    self.cond(x);
                }
            }
            Cond::And(f, cs) | Cond::Or(f, cs) => {
                let conj = if matches!(c, Cond::And(..)) { "and" } else { "or" };
                let n = cs.len();
                for (i, x) in cs.iter().enumerate() {
                    if i > 0 {
                        if *f != ConnForm::Plain {
                            self.w(",");
                        }
                        if *f != ConnForm::Comma || i == n - 1 {
                            self.w(conj);
                        }
                        if *f == ConnForm::OrIf {
                            self.w("if");
                        }
                    }
                    self.cond(x);
                }
            }
            Cond::Paren(x) => {
                self.w("(");
                self.cond(x);
                self.w(")");
            }
            Cond::Alg(_, _, raw) => {
                self.words("the following algorithm returns *true* :");
                self.raw(raw.clone());
            }
            Cond::Phrase(p, hs) => self.phrase(*p, hs),
            Cond::Prose(_, ps) => self.prose(ps),
        }
    }

    fn preds(&mut self, p: &'a Pred, rest: &'a [(Conj, Pred)]) {
        self.pred(p);
        for (c, q) in rest {
            self.w(conj_word(*c));
            self.pred(q);
        }
    }

    fn pred(&mut self, p: &'a Pred) {
        match p {
            Pred::IsVal(neg, f, vs) => {
                self.is_head(*neg, *f);
                self.alts(*f, vs, Self::expr);
            }
            Pred::IsTy(neg, f, ts) => {
                self.is_head(*neg, *f);
                self.alts(*f, ts, Self::ty);
            }
            Pred::Phrase(id, hs) => self.phrase(*id, hs),
        }
    }

    fn is_head(&mut self, neg: bool, f: AltForm) {
        self.w("is");
        if neg {
            self.w("not");
        }
        match f {
            AltForm::Either => self.w("either"),
            AltForm::OneOf => {
                self.w("one");
                self.w("of");
            }
            AltForm::Neither => self.w("neither"),
            AltForm::Or => {}
        }
    }

    fn alts<T>(&mut self, f: AltForm, xs: &'a [T], g: fn(&mut Self, &'a T)) {
        if f == AltForm::Neither {
            g(self, &xs[0]);
            self.w("nor");
            g(self, &xs[1]);
        } else {
            self.english(xs, "or", g);
        }
    }

    /// A Record type's words, then its fields: `[[F]] (T), and [[G]] (U)`.
    fn record_ty(&mut self, head: &str, fs: &'a [(Id, TyExpr)]) {
        self.words(head);
        let n = fs.len();
        for (i, (f, x)) in fs.iter().enumerate() {
            if i > 0 {
                if n > 2 {
                    self.w(",");
                }
                if i == n - 1 {
                    self.w("and");
                }
            }
            self.w(&format!("[[{}]]", self.d.fields.name(*f)));
            self.w("(");
            self.ty(x);
            self.w(")");
        }
    }

    pub fn ty(&mut self, t: &'a TyExpr) {
        match t {
            TyExpr::Sort(a, mods, s, written) => {
                if !a.is_empty() {
                    self.w(a);
                }
                for m in mods {
                    self.w(self.d.sorts.name(*m));
                }
                self.words(if written.is_empty() { self.d.sorts.name(*s) } else { written });
            }
            TyExpr::ListOf(a, x) => {
                if !a.is_empty() {
                    self.w(a);
                }
                self.w("List");
                self.w("of");
                match &**x {
                    TyExpr::Record(fs) => self.record_ty("Records with fields", fs),
                    _ => self.ty(x),
                }
            }
            TyExpr::Nt(a, n, suf) => {
                if !a.is_empty() {
                    self.w(a);
                }
                self.w(&format!("|{}{}|", self.d.nts.name(*n), suf));
            }
            TyExpr::That(x, p, rest) if self.d.is_context(x, p, rest) => self.ty(x),
            TyExpr::That(x, p, rest) => {
                self.ty(x);
                self.w("that");
                self.preds(p, rest);
            }
            TyExpr::Union(f, c, ts) => {
                match f {
                    AltForm::Either => self.w("either"),
                    AltForm::OneOf => {
                        self.w("one");
                        self.w("of");
                    }
                    _ => {}
                }
                if *c == ConnForm::Comma && ts.len() == 2 {
                    self.ty(&ts[0]);
                    self.w(",");
                    self.w("or");
                    self.ty(&ts[1]);
                } else {
                    self.english(ts, "or", Self::ty);
                }
            }
            TyExpr::Completion(t) => {
                self.words("a normal completion containing");
                if let Some(t) = t {
                    self.ty(t);
                }
            }
            TyExpr::Interval(x, lo, hi) => {
                self.ty(x);
                self.words("in the inclusive interval from");
                self.expr(lo);
                self.w("to");
                self.expr(hi);
            }
            TyExpr::Value(e) => self.expr(e),
            TyExpr::Var(a, x) => {
                self.w(a);
                self.var(x);
            }
            TyExpr::Record(fs) => self.record_ty("a Record with fields", fs),
            TyExpr::Phrase(p, hs) => self.phrase(*p, hs),
            TyExpr::Prose(ps) => self.prose(ps),
        }
    }

    fn list(&mut self, f: ListForm, xs: &'a [Expr]) {
        match f {
            ListForm::Paren => self.args(xs),
            ListForm::Comma => self.sep_list(xs, ",", Self::expr),
            ListForm::English(c) => self.english(xs, conj_word(c), Self::expr),
            ListForm::Bullets => self.after.push(After::Bullets(xs)),
        }
    }

    pub(crate) fn hole(&mut self, h: &'a Hole) {
        match h {
            Hole::E(e) => self.expr(e),
            Hole::C(c) | Hole::Bc(_, c) => self.cond(c),
            Hole::T(t) => self.ty(t),
            Hole::B(x) => self.var(x),
            Hole::L(f, xs) => self.list(*f, xs),
            Hole::Text(s) => self.words(s),
            Hole::Field(f) => {
                let n = self.d.fields.name(*f);
                self.words(n)
            }
            Hole::W(_) => panic!("a choice index outside a choice"),
        }
    }

    /// A hole after a template's own: bullets, or verbatim continuation lines.
    fn trailing(&mut self, h: &'a Hole) {
        match h {
            Hole::L(ListForm::Bullets, xs) => self.after.push(After::Bullets(xs)),
            Hole::Text(s) => self.after.push(After::Raw(s)),
            // a step's own table: the continuation lines after it print it
            Hole::E(Expr::Table(..)) => {}
            // a closure step's nested steps
            Hole::E(Expr::Closure(site)) => self.after.push(After::Kids(&self.clos[*site].body)),
            _ => panic!("a trailing hole {h:?}"),
        }
    }

    fn pieces(&mut self, ps: &'a [Piece], hs: &mut std::slice::Iter<'a, Hole>) {
        for p in ps {
            match p {
                Piece::Word(w) => self.w(w),
                Piece::Glue => {
                    self.g();
                }
                Piece::Hole(_) => {
                    let h = hs.next().expect("a phrase with too few holes");
                    self.hole(h);
                }
                Piece::Choice(alts) => {
                    let Some(Hole::W(k)) = hs.next() else { panic!("a choice without its index") };
                    self.pieces(&alts[*k], hs);
                }
            }
        }
    }

    fn phrase(&mut self, p: Id, hs: &'a [Hole]) {
        let mut it = hs.iter();
        let t = &self.d.phrases[p].template;
        self.pieces(t, &mut it);
        for h in it {
            self.trailing(h);
        }
    }

    /// An inline statement: printed as a step, first letter lower-cased, and
    /// (before `; else`) without its full stop.
    fn inline(&mut self, s: &'a Stmt, stop: bool) {
        let start = self.parts.len();
        self.stmt(s);
        if let Some(Part::Text(t, _)) = self.parts.get_mut(start) {
            let mut cs = t.chars();
            if let Some(c) = cs.next() {
                *t = c.to_lowercase().chain(cs).collect();
            }
        }
        if !stop {
            match self.parts.last() {
                Some(Part::Text(t, _)) if t == "." => {
                    self.parts.pop();
                }
                _ => panic!("an inline statement before `; else` without a full stop"),
            }
        }
    }

    fn body(&mut self, b: &'a Body) {
        match b {
            Body::Inline(s) => self.inline(s, true),
            Body::Block(ns) => {
                self.w("then");
                self.after.push(After::Kids(ns));
            }
        }
    }

    pub fn stmt(&mut self, s: &'a Stmt) {
        match s {
            Stmt::Let(x, e) => {
                self.w("Let");
                self.var(x);
                self.w("be");
                self.expr(e);
                if !open_ended(e) {
                    self.w(".");
                }
            }
            Stmt::Set(p, e) => {
                self.w("Set");
                match p {
                    Place::Var(x) => self.var(x),
                    Place::Field(b, f) => self.expr_field(b, *f),
                    Place::Expr(b) => self.expr(b),
                }
                if let Expr::Definition(x, true) = e {
                    self.words("as specified in");
                    self.expr(x);
                    self.w(".");
                } else {
                    self.w("to");
                    self.expr(e);
                    if !open_ended(e) {
                        self.w(".");
                    }
                }
            }
            Stmt::Ret(e) => {
                self.w("Return");
                match e {
                    Some(e) => {
                        self.expr(e);
                        if !open_ended(e) {
                            self.w(".");
                        }
                    }
                    None => self.w("."),
                }
            }
            Stmt::Perform(e) => {
                self.w("Perform");
                self.expr(e);
                self.w(".");
            }
            Stmt::If(c, b, _, _) => {
                self.w("If");
                self.cond(c);
                self.w(",");
                self.body(b);
            }
            Stmt::IfElse(c, a, b) => {
                self.w("If");
                self.cond(c);
                self.w(",");
                self.inline(a, false);
                self.w(";");
                self.w("else");
                self.inline(b, true);
            }
            Stmt::Assert(c) | Stmt::AssertAt(_, c) => {
                self.w("Assert");
                self.w(":");
                self.cond(c);
                self.w(".");
            }
            Stmt::AssertIf(c, d) => {
                self.w("Assert");
                self.w(":");
                self.w("If");
                self.cond(c);
                self.w(",");
                self.w("then");
                self.cond(d);
                self.w(".");
            }
            Stmt::Unreachable(_) => self.words("Assert : This step is never reached ."),
            Stmt::ThrowErr(i) => {
                let n = self.d.fields.name(*i);
                self.w("Throw");
                self.w(article_for(n));
                self.w(&format!("*{n}*"));
                self.w("exception");
                self.w(".");
            }
            Stmt::ThrowVal(e) => {
                self.w("Throw");
                self.expr(e);
                self.w(".");
            }
            Stmt::Note(ps) => {
                self.w("NOTE");
                self.w(":");
                self.prose(ps);
            }
            Stmt::Repeat(ns) => {
                self.w("Repeat");
                self.w(",");
                self.after.push(After::Kids(ns));
            }
            Stmt::RepeatWhile(c, ns) | Stmt::RepeatUntil(c, ns) => {
                self.w("Repeat");
                self.w(",");
                self.w(if matches!(s, Stmt::RepeatWhile(..)) { "while" } else { "until" });
                self.cond(c);
                self.w(",");
                self.after.push(After::Kids(ns));
            }
            Stmt::ForEach(_, None, Expr::Phrase(p, hs), false, b) if self.d.phrases[*p].cat == "Step" => {
                self.phrase(*p, hs);
                self.block_after(b);
            }
            Stmt::ForEach(x, t, l, rev, b) => {
                self.w("For");
                self.w("each");
                match t {
                    Some(t) => self.ty(t),
                    None => self.w("element"),
                }
                self.var(x);
                self.w("of");
                self.expr(l);
                self.w(",");
                if *rev {
                    self.words("in reverse List order ,");
                }
                self.w("do");
                if let Body::Block(ns) = b {
                    self.after.push(After::Kids(ns));
                }
            }
            Stmt::ForEachRec(fs, x, l, b) => {
                self.words("For each Record {");
                for (i, f) in fs.iter().enumerate() {
                    if i > 0 {
                        self.w(",");
                    }
                    self.w(&format!("[[{}]]", self.d.fields.name(*f)));
                }
                self.w("}");
                self.var(x);
                self.w("of");
                self.expr(l);
                self.w(",");
                self.w("do");
                if let Body::Block(ns) = b {
                    self.after.push(After::Kids(ns));
                }
            }
            Stmt::Macro(c, args) => {
                let n = self.d.ops[*c].clone();
                self.w(&n);
                self.g().args(args);
                self.w(".");
            }
            Stmt::Suspend(e, v) => {
                self.w("Suspend");
                self.expr(e);
                if *v == 1 {
                    self.words("and remove it from the execution context stack");
                }
                self.w(".");
            }
            Stmt::Push(e, _) => {
                self.w("Push");
                self.expr(e);
                self.words("onto the execution context stack ;");
                self.expr(e);
                self.words("is now the running execution context .");
            }
            Stmt::Remove(e, v) => {
                self.w("Remove");
                self.expr(e);
                self.words("from the execution context stack");
                if *v == 0 {
                    self.words("and restore the execution context that is at the top of the execution context stack as the running execution context");
                }
                self.w(".");
            }
            Stmt::RemoveRestore(e, r) => {
                self.w("Remove");
                self.expr(e);
                self.words("from the execution context stack and restore");
                self.expr(r);
                self.words("as the running execution context .");
            }
            Stmt::ResumeTop => self.words("Resume the context that is now on the top of the execution context stack as the running execution context ."),
            Stmt::ResumeLet(ctx, c, x, attrs) => {
                if !attrs.is_empty() {
                    self.w(&meta_tag(attrs));
                    self.g();
                }
                self.w("Resume");
                self.words("the suspended evaluation of");
                self.expr(ctx);
                if !attrs.is_empty() {
                    self.gw("</emu-meta>");
                }
                self.w("passing");
                self.expr(c);
                self.words("as the result of the operation that suspended it . Let");
                self.var(x);
                self.words("be the Completion Record passed by the resumed computation .");
            }
            Stmt::Resume(ctx, c) => {
                self.w("Resume");
                self.expr(ctx);
                self.w(",");
                self.w("passing");
                self.expr(c);
                self.w(".");
            }
            Stmt::SetCodeState(ctx, clo) => {
                self.words("Set the code evaluation state of");
                self.expr(ctx);
                self.words("such that when evaluation is resumed for that execution context ,");
                self.expr(clo);
                self.words("will be called with no arguments .");
            }
            Stmt::Readings(_, lit, _) => self.stmt(lit),
            Stmt::LetSuchThat(xs, c, os) => {
                self.w("Let");
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        if xs.len() > 2 {
                            self.w(",");
                        }
                        if i == xs.len() - 1 {
                            self.w("and");
                        }
                    }
                    self.var(x);
                }
                self.words("be integers such that");
                self.cond(c);
                for (i, (large, e)) in os.iter().enumerate() {
                    self.w(",");
                    self.words(if i == 0 { "choosing them so that" } else { "then so that" });
                    self.expr(e);
                    self.words(if *large { "is as large as possible" } else { "is as small as possible" });
                }
                self.w(".");
            }
            Stmt::FindSuchThat(x, t, c, r, f) => {
                self.w("Find");
                self.ty(t);
                self.var(x);
                self.words("such that");
                self.cond(c);
                self.w(";");
                self.words("but if this is not possible (");
                self.words(r);
                self.w(")");
                self.w(",");
                self.inline(f, true);
            }
            Stmt::ForSuchThat(x, t, c, o, b) => {
                self.w("For");
                self.w("each");
                self.ty(t);
                self.var(x);
                self.words("such that");
                self.cond(c);
                self.w(",");
                match o {
                    Some(1) => self.words("in descending order ,"),
                    Some(_) => self.words("in ascending order ,"),
                    None => {}
                }
                self.w("do");
                self.block_after(b);
            }
            Stmt::ForKeys(x, o, c, k, b) => {
                self.words("For each own property key");
                self.var(x);
                self.w("of");
                self.expr(o);
                self.words("such that");
                self.cond(c);
                self.w(",");
                self.words(match k {
                    0 => "in ascending numeric index order",
                    1 => "in ascending chronological order of property creation",
                    _ => "in descending numeric index order",
                });
                self.w(",");
                self.w("do");
                self.block_after(b);
            }
            Stmt::ForIndex(x, l, b) => {
                self.words("For each index");
                self.var(x);
                self.w("of");
                self.expr(l);
                self.w(",");
                self.w("do");
                self.block_after(b);
            }
            Stmt::ForChildren(x, b) => {
                self.words("For each child node");
                self.var(x);
                self.words("of this Parse Node ,");
                self.w("do");
                self.block_after(b);
            }
            Stmt::ForChildrenOf(x, e, b) => {
                self.words("For each child node");
                self.var(x);
                self.w("of");
                self.expr(e);
                self.w(",");
                self.w("do");
                self.block_after(b);
            }
            Stmt::RepeatN(e, ns) => {
                self.w("Repeat");
                self.expr(e);
                self.w("times");
                self.w(":");
                self.after.push(After::Kids(ns));
            }
            Stmt::ForRange(x, lo, li, hi, hii, d, b) => {
                self.words("For each integer");
                self.var(x);
                self.words("such that");
                self.expr(lo);
                self.w(if *li { "≤" } else { "&lt;" });
                self.var(x);
                self.w(if *hii { "≤" } else { "&lt;" });
                self.expr(hi);
                self.w(",");
                self.words(if *d { "in descending order ," } else { "in ascending order ," });
                self.w("do");
                self.block_after(b);
            }
            Stmt::RetSee(e, x) => {
                self.w("Return");
                self.expr(e);
                self.w("(");
                self.w("see");
                self.expr(x);
                self.w(")");
                self.w(".");
            }
            Stmt::SyntaxError(early, c, unless) => {
                self.words(if *early { "It is an early Syntax Error if" } else { "It is a Syntax Error if" });
                self.cond(c);
                match unless {
                    Some((UnlessForm::Plain, u)) => {
                        self.w("unless");
                        self.cond(u);
                    }
                    Some((UnlessForm::Comma, u)) => {
                        self.words(", unless");
                        self.cond(u);
                    }
                    Some((UnlessForm::Optional, u)) => {
                        self.gw(OPT_OPEN);
                        self.words(", unless");
                        self.cond(u);
                        self.gw("</span>");
                    }
                    None => {}
                }
                self.w(".");
            }
            Stmt::Mutate(p, hs) | Stmt::Phrase(p, hs) => self.phrase(*p, hs),
            Stmt::Prose(_, ps) => self.prose(ps),
            Stmt::WithSteps(s, ns) => {
                self.stmt(s);
                self.after.push(After::Kids(ns));
            }
        }
    }

    fn block_after(&mut self, b: &'a Body) {
        if let Body::Block(ns) = b {
            self.after.push(After::Kids(ns));
        }
    }

    fn expr_field(&mut self, b: &'a Expr, f: Id) {
        self.expr(b);
        self.gw(".");
        self.gw(&format!("[[{}]]", self.d.fields.name(f)));
    }

    /// The words so far as one line of text (nothing deferred).
    pub(crate) fn take_text(&mut self) -> String {
        let (t, after) = self.take_line();
        assert!(after.is_empty(), "deferred lines in a one-line text");
        t
    }

    fn take_line(&mut self) -> (String, Vec<After<'a>>) {
        let parts = std::mem::take(&mut self.parts);
        let text = crate::token::join(&parts, &[], "");
        (text, std::mem::take(&mut self.after))
    }

    /// One step line (and its arms, kids and continuation lines) at a depth.
    pub fn node(&mut self, n: &'a Node, base: usize, depth: usize, out: &mut String) {
        self.stmt(&n.stmt);
        let (text, after) = self.take_line();
        self.line(base, depth, &n.attrs, &text, out);
        self.afters(after, base, depth, out);
        let st = match &n.stmt {
            Stmt::Readings(_, lit, _) => lit.as_ref(),
            s => s,
        };
        if let Stmt::If(_, _, arms, els) = st {
            for a in arms.iter().chain(els.iter()) {
                match &a.cond {
                    Some(c) => {
                        self.w("Else");
                        self.w("if");
                        self.cond(c);
                    }
                    None => self.w("Else"),
                }
                self.w(",");
                match &a.body {
                    Body::Inline(s) => self.inline(s, true),
                    Body::Block(ns) => {
                        if a.cond.is_some() {
                            self.w("then");
                        }
                        self.after.push(After::Kids(ns));
                    }
                }
                let (text, after) = self.take_line();
                self.line(base, depth, &a.attrs, &text, out);
                self.afters(after, base, depth, out);
            }
        }
    }

    fn afters(&mut self, after: Vec<After<'a>>, base: usize, depth: usize, out: &mut String) {
        for a in after {
            match a {
                After::Kids(ns) => {
                    for k in ns {
                        self.node(k, base, depth + 1, out);
                    }
                }
                After::Bullets(xs) => {
                    for x in xs {
                        self.expr(x);
                        let (t, more) = self.take_line();
                        assert!(more.is_empty());
                        out.push('\n');
                        out.push_str(&" ".repeat(base + 2 * depth + 2));
                        out.push_str("* ");
                        out.push_str(&t);
                    }
                }
                After::Raw(s) => {
                    for l in s.split('\n') {
                        out.push('\n');
                        out.push_str(&" ".repeat(base + 2 * depth));
                        out.push_str(l);
                    }
                }
            }
        }
    }

    fn line(&mut self, base: usize, depth: usize, attrs: &[Attr], text: &str, out: &mut String) {
        out.push('\n');
        out.push_str(&" ".repeat(base + 2 * depth));
        out.push_str("1. ");
        if !attrs.is_empty() {
            out.push('[');
            for (i, a) in attrs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&a.key);
                if let Some(v) = &a.value {
                    out.push_str(&format!("=\"{v}\""));
                }
            }
            out.push_str("] ");
        }
        out.push_str(text);
    }
}

type Part2 = crate::ast::Part;

/// The tag that opens a normative-optional span.
pub const OPT_OPEN: &str = "<span normative-optional>";

/// An expression whose lines follow the step: a closure literal, or bullets.
fn open_ended(e: &Expr) -> bool {
    matches!(e, Expr::Closure(..))
        || matches!(e, Expr::Phrase(_, hs) if matches!(hs.as_slice(), [Hole::L(ListForm::Bullets, _)] | [.., Hole::E(Expr::Table(..)), Hole::Text(_)]))
}

/// `<emu-meta k="v">`.
pub fn meta_tag(attrs: &[Attr]) -> String {
    let mut t = String::from("<emu-meta");
    for a in attrs {
        t.push(' ');
        t.push_str(&a.key);
        if let Some(v) = &a.value {
            t.push_str(&format!("=\"{v}\""));
        }
    }
    t.push('>');
    t
}

/// A type phrase on one line.
pub fn ty_text(d: &Decls, vars: &[String], t: &TyExpr) -> String {
    let mut p = Printer::new(d, vars, &[]);
    p.ty(t);
    p.take_line().0
}

/// An expression on one line.
pub fn expr_text(d: &Decls, vars: &[String], e: &Expr) -> String {
    let mut p = Printer::new(d, vars, &[]);
    p.expr(e);
    p.take_line().0
}

/// A statement on one line, if it has no lines after it.
pub fn stmt_text(d: &Decls, vars: &[String], s: &Stmt) -> Option<String> {
    let mut p = Printer::new(d, vars, &[]);
    p.stmt(s);
    let (t, after) = p.take_line();
    after.is_empty().then_some(t)
}

/// A host requirement sentence from its data.
pub fn requirement(d: &Decls, vars: &[String], s: &crate::host::Sentence) -> String {
    use crate::host::{Duty, Post, Premise, Req, MODALS};
    let mut p = Printer::new(d, vars, &[]);
    match &s.req {
        Req::Must(m) => {
            match &m.premise {
                Some(Premise::If(c, then)) => {
                    p.w("if");
                    p.cond(c);
                    p.w(",");
                    if *then {
                        p.w("then");
                    }
                }
                Some(Premise::Unless(c)) => {
                    p.w("unless");
                    p.cond(c);
                    p.w(",");
                }
                Some(Premise::EachTime(e, comma)) => {
                    p.words("each time");
                    p.expr(e);
                    if *comma {
                        p.w(",");
                    }
                }
                Some(Premise::When(c)) => {
                    p.w("when");
                    p.cond(c);
                    p.w(",");
                }
                Some(Premise::Otherwise) => p.words("otherwise ,"),
                None => {}
            }
            p.expr(&m.subject);
            if let Some((_, w)) = MODALS.iter().find(|x| x.0 == m.modal) {
                p.words(w);
            }
            match &m.duty {
                Duty::Return(t) => {
                    p.w("return");
                    p.ty(t);
                }
                Duty::Be(t) => {
                    p.w("be");
                    p.ty(t);
                }
                Duty::Phrase(id, hs) => p.phrase(*id, hs),
            }
            if let Some((f, c)) = &m.post {
                match f {
                    Post::CommaUnless => p.words(", unless"),
                    Post::Unless => p.w("unless"),
                    Post::If => p.w("if"),
                }
                p.cond(c);
            }
            if m.either {
                p.words(", unless either");
            }
            p.w(if m.colon { ":" } else { "." });
        }
        Req::Holds(pre, c) => {
            if let Some(x) = pre {
                p.w("if");
                p.cond(x);
                p.w(",");
            }
            p.cond(c);
            p.w(".");
        }
        Req::Step(st) => p.stmt(st),
        Req::Default(c, e) => {
            p.words("the default implementation of");
            p.w(&d.ops[*c]);
            p.words("is to return");
            p.expr(e);
            p.w(".");
        }
        Req::Phrase(id, hs) => p.phrase(*id, hs),
        Req::Prose(_, ps) => p.prose(ps),
    }
    let (t, _) = p.take_line();
    let mut cs = t.chars();
    match cs.next() {
        Some(c) if s.cap => c.to_uppercase().chain(cs).collect(),
        _ => t,
    }
}

/// A whole `emu-alg` body from its steps.
pub fn body(d: &Decls, vars: &[String], clos: &[CloLit], steps: &[Node], base: usize, close: usize) -> String {
    let mut p = Printer::new(d, vars, clos);
    let mut out = String::new();
    for n in steps {
        p.node(n, base, 0, &mut out);
    }
    out.push('\n');
    out.push_str(&" ".repeat(close));
    out
}

/// An equation bullet's content: `The SV of <emu-grammar>…</emu-grammar> is ….` on
/// its own line, two columns in from the `<li>`.
pub fn equation(d: &Decls, vars: &[String], sdo: Id, keys: &[String], body: &[Node], indent: usize) -> String {
    let mut p = Printer::new(d, vars, &[]);
    p.w("The");
    p.w(d.sdos.name(sdo));
    p.w("of");
    for (i, x) in keys.iter().enumerate() {
        if i > 0 {
            p.w("or");
            p.w("of");
        }
        p.w(&format!("<emu-grammar>{x}</emu-grammar>"));
    }
    p.w("is");
    match body {
        [Node { stmt: Stmt::If(c, Body::Inline(a), arms, Some(Arm { cond: None, body: Body::Inline(b), .. })), .. }] if arms.is_empty() => {
            let (Stmt::Ret(Some(e1)), Stmt::Ret(Some(e2))) = (a.as_ref(), b.as_ref()) else { panic!("an equation's cases") };
            p.expr(e1);
            p.w("if");
            p.cond(c);
            p.words(". Otherwise , it is");
            p.expr(e2);
        }
        [lets @ .., Node { stmt: Stmt::Ret(Some(e)), .. }] => {
            p.expr(e);
            for (i, l) in lets.iter().enumerate() {
                let Stmt::Let(x, v) = &l.stmt else { panic!("an equation's where") };
                if !l.attrs.iter().any(|a| a.key == "and-bare") {
                    p.w(",");
                }
                p.w(if i == 0 { "where" } else { "and" });
                p.var(x);
                p.w("is");
                p.expr(v);
            }
        }
        _ => panic!("an equation's body"),
    }
    p.w(".");
    let (t, _) = p.take_line();
    format!("\n{}{t}\n{}", " ".repeat(indent + 2), " ".repeat(indent))
}

/// An Early Errors bullet's content (between `<li>` and `</li>`): its sentences on one line, laid out.
pub fn early(d: &Decls, vars: &[String], body: &[Node], layout: LiLayout, indent: usize) -> String {
    let mut p = Printer::new(d, vars, &[]);
    for n in body {
        p.stmt(&n.stmt);
    }
    let (t, after) = p.take_line();
    assert!(after.is_empty(), "an early-error sentence with nested lines");
    match layout {
        LiLayout::Block => format!("\n{}{t}\n{}", " ".repeat(indent + 2), " ".repeat(indent)),
        _ => t,
    }
}

/// A grammar symbol's parameters as written: `[+P, ~Q]`, or nothing.
pub fn goal_text(d: &Decls, xs: &[(usize, bool)]) -> String {
    if xs.is_empty() {
        return String::new();
    }
    let ps: Vec<String> = xs.iter().map(|(p, b)| format!("{}{}", if *b { "+" } else { "~" }, d.params.name(*p))).collect();
    format!("[{}]", ps.join(", "))
}

/// A literal as written: its text re-escaped, or the written form it keeps.
fn written(s: &str, w: &str) -> String {
    if w.is_empty() {
        s.replace('&', "&amp;").replace('<', "&lt;")
    } else {
        w.to_string()
    }
}
