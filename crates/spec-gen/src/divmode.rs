//! The mode M: a deterministic pushdown classifier over token texts that says, before each token, whether a
//! `/` or `/=` (div) or a |RegularExpressionLiteral| (re) may come; and its check over every instance of
//! lr1's expansion (`spec-gen divmode`).
//!
//! M's frames: the goal's statement list, block, function body (closing to a statement, an operand or a class
//! element), static block, function and class headers, class body, object literal, header paren, parameters
//! paren, other paren, bracket, template substitution and ternary; a concise arrow body is a flag on the frame
//! it sits in. Each frame carries the Yield and Await flags in force inside it; the last
//! token's class gives the mode. The check is a summary analysis: for each instance and entry context (the
//! top frame and the last class) the effects its yields can have on the stack (frames popped, frames pushed)
//! and the last class after them, every right-hand side simulated over its children's effects.

use crate::lr1::{Cfg, Src, S};
use jsgrammar::gl::Gl;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// The Yield and Await flags.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Fl {
    pub y: bool,
    pub a: bool,
}

/// Where a function body's `}` leaves: a statement start, an operand end, a class element or property.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Close {
    Stmt,
    Oper,
    Elem,
}

/// An element's phase in an object literal or class body: at its key (the modifiers seen), or in its value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Ph {
    Key { star: bool, asy: bool, prev_async: bool },
    Value,
}

const KEY: Ph = Ph::Key { star: false, asy: false, prev_async: false };

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Fr {
    Top,
    Block,
    Fn(Close),
    Static,
    FnHdr { decl: bool, star: bool, asy: bool },
    ClassHdr { decl: bool },
    Class { decl: bool, ph: Ph },
    Obj(Ph),
    Header { for_: bool, seg0: bool },
    Params,
    Paren { asy: bool },
    Brack { key: bool },
    Tpl,
    Tern,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Frame {
    pub k: Fr,
    pub f: Fl,
    /// In a concise arrow body directly in this frame: the frame's own flags (`f` is the body's).
    pub ar: Option<Fl>,
}

/// The last token's class.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Cls {
    Stmt,
    Expr,
    /// Just after a statement header's `(`.
    Open,
    Default,
    Oper,
    HdrKw(bool),
    /// After `with`: a statement header before `(`, an import attributes clause before `{`.
    With,
    /// After `export *` or `export * as`: a word next is a name.
    ExportStar,
    Dot,
    Decl,
    /// After `let`, `using` or `await using` where a declaration may start: a word next is its binding (true: `using` after a header `(`, where `of` is the keyword).
    Let(bool),
    /// After `await` (an operator) where a statement or a for header's declaration may start.
    AwaitAt,
    AsyncId(bool),
    AsyncParam,
    OfAsync,
    Arrow,
    FnKw,
    ClassKw,
    Params(Fl),
    AsyncClose,
    Name(bool),
    Elem,
}

/// The mode after a class: true for div.
pub fn div(c: Cls) -> bool {
    !matches!(c, Cls::Stmt | Cls::Expr | Cls::Open | Cls::AwaitAt | Cls::Default | Cls::HdrKw(_) | Cls::With | Cls::Decl | Cls::OfAsync | Cls::Arrow)
}

/// A token as M reads its text.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tk<'a> {
    P(&'a str),
    W(&'a str),
    Lit,
    Re,
    Head,
    Mid,
    Tail,
    Priv,
}

/// The stack M reads: a frame at a depth (none if unknown), pop, push.
pub trait Stk {
    fn peek(&self, d: usize) -> Option<Frame>;
    fn pop(&mut self);
    fn push(&mut self, f: Frame);
}

impl Stk for Vec<Frame> {
    fn peek(&self, d: usize) -> Option<Frame> {
        self.len().checked_sub(d + 1).map(|i| self[i])
    }
    fn pop(&mut self) {
        Vec::pop(self);
    }
    fn push(&mut self, f: Frame) {
        Vec::push(self, f)
    }
}

/// A stack relative to an entry: its top frame (if known), the frames popped below the entry, those pushed.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Abs {
    pub top0: Option<Frame>,
    pub popped: u8,
    pub st: Vec<Frame>,
}

impl Stk for Abs {
    fn peek(&self, d: usize) -> Option<Frame> {
        if d < self.st.len() {
            Some(self.st[self.st.len() - 1 - d])
        } else {
            self.top0.filter(|_| d == self.st.len() && self.popped == 0)
        }
    }
    fn pop(&mut self) {
        if self.st.pop().is_none() {
            self.popped += 1;
        }
    }
    fn push(&mut self, f: Frame) {
        if self.st.is_empty() && self.popped == 1 && self.top0 == Some(f) {
            self.popped = 0;
        } else {
            self.st.push(f)
        }
    }
}

fn top<T: Stk>(s: &T) -> Result<Frame, String> {
    s.peek(0).ok_or_else(|| "an unknown frame".to_string())
}

fn set_top<T: Stk>(s: &mut T, f: Frame) {
    s.pop();
    s.push(f);
}

/// Pops an arrow body on top, if any.
fn end_arrow<T: Stk>(s: &mut T) -> Result<Frame, String> {
    let t = top(s)?;
    if let Some(f) = t.ar {
        let u = Frame { f, ar: None, ..t };
        set_top(s, u);
        return Ok(u);
    }
    Ok(t)
}

const RESERVED: &[&str] = &[
    "await", "break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do", "else",
    "enum", "export", "extends", "false", "finally", "for", "function", "if", "import", "in", "instanceof", "new",
    "null", "return", "super", "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with",
    "yield",
];

/// In a key phase: the phase after a name, `*` or computed key.
fn key_named(ph: Ph, w: Option<&str>) -> Ph {
    match ph {
        Ph::Key { star, asy, prev_async } => Ph::Key { star, asy: asy || prev_async, prev_async: w == Some("async") },
        v => v,
    }
}

/// An object literal or class body on top in its key phase.
fn in_key(t: Frame) -> Option<Ph> {
    match t.k {
        Fr::Obj(ph @ Ph::Key { .. }) | Fr::Class { ph: ph @ Ph::Key { .. }, .. } => Some(ph),
        _ => None,
    }
}

fn with_ph(t: Frame, ph: Ph) -> Frame {
    let k = match t.k {
        Fr::Obj(_) => Fr::Obj(ph),
        Fr::Class { decl, .. } => Fr::Class { decl, ph },
        k => k,
    };
    Frame { k, ..t }
}

/// A for header's first segment ends at its `of`.
fn past_of<T: Stk>(s: &mut T, t: Frame) {
    if t.k == (Fr::Header { for_: true, seg0: true }) {
        set_top(s, Frame { k: Fr::Header { for_: true, seg0: false }, ..t });
    }
}

/// M's step: the class after `tk`, the stack updated.
pub fn step<T: Stk>(s: &mut T, last: Cls, tk: Tk) -> Result<Cls, String> {
    let mut t = top(s)?;
    if last == Cls::OfAsync && tk != Tk::P("=>") {
        past_of(s, t);
        t = top(s)?;
    }
    let stmt_at = matches!(last, Cls::Stmt | Cls::Default);
    match tk {
        Tk::W(w) => {
            if last == Cls::Dot {
                return Ok(Cls::Oper);
            }
            if last == Cls::ExportStar {
                return Ok(if w == "as" { Cls::ExportStar } else { Cls::Oper });
            }
            if let Some(ph) = in_key(t) {
                set_top(s, with_ph(t, key_named(ph, Some(w))));
                return Ok(Cls::Name(w == "static"));
            }
            if last == Cls::FnKw {
                return Ok(Cls::FnKw);
            }
            if last == Cls::ClassKw && w != "extends" {
                return Ok(Cls::ClassKw);
            }
            if last == Cls::Decl || matches!(last, Cls::Let(_)) && !matches!(w, "in" | "instanceof") && !(last == Cls::Let(true) && w == "of") {
                return Ok(Cls::Oper);
            }
            if let Cls::AsyncId(st) = last {
                match w {
                    "function" => {
                        s.push(Frame { k: Fr::FnHdr { decl: st, star: false, asy: true }, f: t.f, ar: None });
                        return Ok(Cls::FnKw);
                    }
                    "of" => return Ok(Cls::OfAsync),
                    "yield" | "await" => return Ok(Cls::AsyncParam),
                    _ if !RESERVED.contains(&w) => return Ok(Cls::AsyncParam),
                    _ => {}
                }
            }
            if matches!(w, "yield" | "await") && div(last) {
                return Ok(Cls::Oper);
            }
            Ok(match w {
                "break" | "continue" | "this" | "super" | "null" | "true" | "false" | "debugger" | "enum" => Cls::Oper,
                "case" | "delete" | "typeof" | "void" | "throw" | "new" | "instanceof" | "return" | "extends"
                | "import" => Cls::Expr,
                "in" => {
                    if matches!(t.k, Fr::Header { for_: true, seg0: true }) {
                        let u = end_arrow(s)?;
                        past_of(s, u);
                    }
                    Cls::Expr
                }
                "do" | "else" | "try" | "finally" => Cls::Stmt,
                "with" => Cls::With,
                "if" | "while" | "switch" | "catch" => Cls::HdrKw(false),
                "for" => Cls::HdrKw(true),
                "class" => {
                    s.push(Frame { k: Fr::ClassHdr { decl: stmt_at }, f: t.f, ar: None });
                    Cls::ClassKw
                }
                "function" => {
                    s.push(Frame { k: Fr::FnHdr { decl: stmt_at, star: false, asy: false }, f: t.f, ar: None });
                    Cls::FnKw
                }
                "var" | "const" => Cls::Decl,
                "let" if stmt_at || last == Cls::Open => Cls::Let(false),
                "using" if stmt_at || last == Cls::AwaitAt => Cls::Let(false),
                "using" if last == Cls::Open => Cls::Let(true),
                "let" => Cls::Oper,
                "export" | "default" => Cls::Default,
                "yield" => {
                    if t.f.y {
                        Cls::Expr
                    } else {
                        Cls::Oper
                    }
                }
                "await" => {
                    if last == Cls::HdrKw(true) {
                        Cls::HdrKw(true)
                    } else if t.f.a {
                        if stmt_at || last == Cls::Open {
                            Cls::AwaitAt
                        } else {
                            Cls::Expr
                        }
                    } else {
                        Cls::Oper
                    }
                }
                "async" => Cls::AsyncId(stmt_at),
                "of" => {
                    if last == Cls::Let(false) || !div(last) {
                        Cls::Oper
                    } else {
                        past_of(s, t);
                        Cls::Expr
                    }
                }
                _ => Cls::Oper,
            })
        }
        Tk::Lit | Tk::Re => {
            if let Some(ph) = in_key(t) {
                set_top(s, with_ph(t, key_named(ph, None)));
                return Ok(Cls::Name(false));
            }
            Ok(Cls::Oper)
        }
        Tk::Priv => {
            if let Some(ph) = in_key(t) {
                set_top(s, with_ph(t, key_named(ph, None)));
                return Ok(Cls::Name(false));
            }
            Ok(Cls::Oper)
        }
        Tk::Head => {
            s.push(Frame { k: Fr::Tpl, f: t.f, ar: None });
            Ok(Cls::Expr)
        }
        Tk::Mid | Tk::Tail => {
            let t = end_arrow(s)?;
            if t.k != Fr::Tpl {
                return Err(format!("a template continuation at {t:?}"));
            }
            if tk == Tk::Mid {
                Ok(Cls::Expr)
            } else {
                s.pop();
                Ok(Cls::Oper)
            }
        }
        Tk::P(p) => punct(s, t, last, p),
    }
}

fn punct<T: Stk>(s: &mut T, t: Frame, last: Cls, p: &str) -> Result<Cls, String> {
    match p {
        "{" => {
            if last == Cls::Arrow && t.ar.is_some() {
                end_arrow(s)?;
                s.push(Frame { k: Fr::Fn(Close::Oper), f: t.f, ar: None });
                return Ok(Cls::Stmt);
            }
            if let Fr::FnHdr { decl, star, asy } = t.k {
                set_top(s, Frame { k: Fr::Fn(if decl { Close::Stmt } else { Close::Oper }), f: Fl { y: star, a: asy }, ar: None });
                return Ok(Cls::Stmt);
            }
            if let Fr::ClassHdr { decl } = t.k {
                if div(last) {
                    set_top(s, Frame { k: Fr::Class { decl, ph: KEY }, f: t.f, ar: None });
                    return Ok(Cls::Elem);
                }
                s.push(Frame { k: Fr::Obj(KEY), f: t.f, ar: None });
                return Ok(Cls::Expr);
            }
            if let Cls::Params(f) = last {
                if in_key(t).is_some() {
                    s.push(Frame { k: Fr::Fn(Close::Elem), f, ar: None });
                    return Ok(Cls::Stmt);
                }
            }
            if last == Cls::Name(true) && matches!(t.k, Fr::Class { .. }) {
                s.push(Frame { k: Fr::Static, f: Fl { y: false, a: true }, ar: None });
                return Ok(Cls::Stmt);
            }
            match last {
                Cls::Stmt | Cls::HdrKw(_) => {
                    s.push(Frame { k: Fr::Block, f: t.f, ar: None });
                    Ok(Cls::Stmt)
                }
                Cls::Expr | Cls::Open | Cls::AwaitAt | Cls::Default | Cls::Decl | Cls::Let(_) | Cls::Arrow | Cls::OfAsync | Cls::With => {
                    s.push(Frame { k: Fr::Obj(KEY), f: t.f, ar: None });
                    Ok(Cls::Expr)
                }
                _ => Err(format!("`{{` after {last:?} at {t:?}")),
            }
        }
        "}" => {
            let t = end_arrow(s)?;
            s.pop();
            match t.k {
                Fr::Block => Ok(Cls::Stmt),
                Fr::Fn(Close::Stmt) => Ok(Cls::Stmt),
                Fr::Fn(Close::Oper) => Ok(Cls::Oper),
                Fr::Fn(Close::Elem) | Fr::Static => {
                    let u = top(s)?;
                    set_top(s, with_ph(u, KEY));
                    Ok(Cls::Elem)
                }
                Fr::Class { decl, .. } => Ok(if decl { Cls::Stmt } else { Cls::Oper }),
                Fr::Obj(_) => Ok(Cls::Oper),
                k => Err(format!("`}}` at {k:?}")),
            }
        }
        "(" => {
            let k = if let Cls::HdrKw(for_) = last {
                Frame { k: Fr::Header { for_, seg0: true }, f: t.f, ar: None }
            } else if last == Cls::With {
                Frame { k: Fr::Header { for_: false, seg0: true }, f: t.f, ar: None }
            } else if let Fr::FnHdr { star, asy, .. } = t.k {
                Frame { k: Fr::Params, f: Fl { y: star, a: asy }, ar: None }
            } else if let Some(Ph::Key { star, asy, .. }) = in_key(t) {
                Frame { k: Fr::Params, f: Fl { y: star, a: asy }, ar: None }
            } else {
                Frame { k: Fr::Paren { asy: matches!(last, Cls::AsyncId(_)) || div(last) }, f: t.f, ar: None }
            };
            s.push(k);
            Ok(if matches!(k.k, Fr::Header { .. }) { Cls::Open } else { Cls::Expr })
        }
        ")" => {
            let t = end_arrow(s)?;
            s.pop();
            match t.k {
                Fr::Header { .. } => Ok(Cls::Stmt),
                Fr::Params => Ok(Cls::Params(t.f)),
                Fr::Paren { asy: true } => Ok(Cls::AsyncClose),
                Fr::Paren { asy: false } => Ok(Cls::Oper),
                k => Err(format!("`)` at {k:?}")),
            }
        }
        "[" => {
            let key = in_key(t);
            if let Some(ph) = key {
                set_top(s, with_ph(t, key_named(ph, None)));
            }
            s.push(Frame { k: Fr::Brack { key: key.is_some() }, f: t.f, ar: None });
            Ok(Cls::Expr)
        }
        "]" => {
            let t = end_arrow(s)?;
            s.pop();
            match t.k {
                Fr::Brack { key } => Ok(if key { Cls::Name(false) } else { Cls::Oper }),
                k => Err(format!("`]` at {k:?}")),
            }
        }
        "?" => {
            s.push(Frame { k: Fr::Tern, f: t.f, ar: None });
            Ok(Cls::Expr)
        }
        ":" => {
            let t = end_arrow(s)?;
            match t.k {
                Fr::Tern => {
                    s.pop();
                    Ok(Cls::Expr)
                }
                Fr::Obj(Ph::Key { .. }) => {
                    set_top(s, with_ph(t, Ph::Value));
                    Ok(Cls::Expr)
                }
                Fr::Top | Fr::Block | Fr::Fn(_) | Fr::Static => Ok(Cls::Stmt),
                k => Err(format!("`:` at {k:?}")),
            }
        }
        "," => {
            let t = end_arrow(s)?;
            if matches!(t.k, Fr::Obj(_)) {
                set_top(s, with_ph(t, KEY));
            }
            Ok(Cls::Expr)
        }
        ";" => {
            let t = end_arrow(s)?;
            match t.k {
                Fr::Header { for_: true, .. } => {
                    set_top(s, Frame { k: Fr::Header { for_: true, seg0: false }, f: t.f, ar: None });
                    Ok(Cls::Expr)
                }
                Fr::Class { .. } => {
                    set_top(s, with_ph(t, KEY));
                    Ok(Cls::Elem)
                }
                Fr::Top | Fr::Block | Fr::Fn(_) | Fr::Static => Ok(Cls::Stmt),
                k => Err(format!("`;` at {k:?}")),
            }
        }
        "=" | "..." if in_key(t).is_some() => {
            set_top(s, with_ph(t, Ph::Value));
            Ok(Cls::Expr)
        }
        "*" => {
            if let Some(ph) = in_key(t) {
                let ph = match key_named(ph, None) {
                    Ph::Key { asy, .. } => Ph::Key { star: true, asy, prev_async: false },
                    v => v,
                };
                set_top(s, with_ph(t, ph));
                return Ok(Cls::Name(false));
            }
            if last == Cls::Default {
                return Ok(Cls::ExportStar);
            }
            if last == Cls::FnKw {
                if let Fr::FnHdr { decl, asy, .. } = t.k {
                    set_top(s, Frame { k: Fr::FnHdr { decl, star: true, asy }, f: t.f, ar: None });
                    return Ok(Cls::FnKw);
                }
            }
            Ok(Cls::Expr)
        }
        "=>" => {
            let asy = matches!(last, Cls::AsyncParam | Cls::AsyncClose | Cls::OfAsync);
            set_top(s, Frame { f: Fl { y: false, a: asy }, ar: Some(t.ar.unwrap_or(t.f)), ..t });
            Ok(Cls::Arrow)
        }
        "." | "?." => Ok(Cls::Dot),
        "++" | "--" => Ok(if div(last) { Cls::Oper } else { Cls::Expr }),
        _ => Ok(Cls::Expr),
    }
}

/// The bottom frame of a goal.
pub fn bottom(module: bool) -> Frame {
    Frame { k: Fr::Top, f: Fl { y: false, a: module }, ar: None }
}

/// An instance's entry context: its top frame (if known) and the last class.
pub type Ctx = (Option<Frame>, Cls);

/// An effect: frames popped, frames pushed, the last class after.
pub type Eff = (u8, Vec<Frame>, Cls);

/// A failure: the instance, its production, the position, the context, what failed.
pub struct Fail {
    pub inst: u32,
    pub prod: usize,
    pub pos: usize,
    pub ctx: Ctx,
    pub what: String,
}

/// A token of the expansion as M reads it, none for the end.
fn tk_of(t: &str) -> Option<Tk<'_>> {
    Some(match t {
        "$" => return None,
        "ID" => Tk::W("x"),
        "RegularExpressionLiteral" => Tk::Re,
        "NumericLiteral" | "StringLiteral" | "NoSubstitutionTemplate" => Tk::Lit,
        "TemplateHead" => Tk::Head,
        "TemplateMiddle" => Tk::Mid,
        "TemplateTail" => Tk::Tail,
        "PrivateIdentifier" => Tk::Priv,
        _ if t.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '$') => Tk::W(t),
        _ => Tk::P(t),
    })
}

/// The summaries of every instance reached from the goals' bottoms, and the failures.
pub struct Check {
    pub sums: BTreeMap<(u32, Ctx), BTreeSet<Eff>>,
    pub fails: Vec<Fail>,
    /// Where each instance context was first reached: the parent's key, production and position.
    pub from: HashMap<(u32, Ctx), ((u32, Ctx), usize, usize)>,
}

const MAX: usize = 16;

/// The summary analysis from `roots` (instance, context).
pub fn check(g: &Cfg, roots: &[(u32, Ctx)], limit: usize, first: bool) -> Check {
    let mut by_lhs: HashMap<u32, Vec<usize>> = HashMap::new();
    for (i, p) in g.prods.iter().enumerate() {
        by_lhs.entry(p.lhs).or_default().push(i);
    }
    for t in &g.toks {
        if t.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && t.len() > 1 && tk_of(t) == Some(Tk::W(t)) {
            panic!("divmode: a lexical token M does not read: {t}");
        }
    }
    let mut sums: BTreeMap<(u32, Ctx), BTreeSet<Eff>> = BTreeMap::new();
    let mut deps: HashMap<(u32, Ctx), BTreeSet<(u32, Ctx)>> = HashMap::new();
    let mut from: HashMap<(u32, Ctx), ((u32, Ctx), usize, usize)> = HashMap::new();
    let mut work: Vec<(u32, Ctx)> = roots.to_vec();
    let mut queued: BTreeSet<(u32, Ctx)> = roots.iter().cloned().collect();
    for r in roots {
        sums.insert(r.clone(), BTreeSet::new());
    }
    let mut fails: BTreeMap<(u32, usize, usize, Ctx), String> = BTreeMap::new();
    let mut iters = 0usize;
    while let Some(key) = work.pop() {
        iters += 1;
        if iters % 50000 == 0 {
            eprintln!("divmode: {iters} steps, {} contexts, {} queued", sums.len(), work.len());
        }
        if iters > limit {
            eprintln!("divmode: stopped after {limit} steps");
            break;
        }
        queued.remove(&key);
        let (inst, ctx) = key.clone();
        let mut out: BTreeSet<Eff> = BTreeSet::new();
        for &pi in by_lhs.get(&inst).map(|v| v.as_slice()).unwrap_or(&[]) {
            let p = &g.prods[pi];
            let mut states: BTreeSet<(Abs, Cls)> = BTreeSet::new();
            states.insert((Abs { top0: ctx.0, popped: 0, st: Vec::new() }, ctx.1));
            for (pos, x) in p.rhs.iter().enumerate() {
                let mut next = BTreeSet::new();
                for (a, last) in &states {
                    match *x {
                        S::T(t) => {
                            let name = &g.toks[t as usize];
                            let Some(tk) = tk_of(name) else {
                                next.insert((a.clone(), *last));
                                continue;
                            };
                            let need = match tk {
                                Tk::P("/") | Tk::P("/=") => Some(true),
                                Tk::Re => Some(false),
                                _ => None,
                            };
                            if let Some(d) = need {
                                if div(*last) != d {
                                    fails.entry((inst, pi, pos, ctx)).or_insert(format!("`{name}` after {last:?} at {:?}", a.peek(0)));
                                }
                            }
                            let mut b = a.clone();
                            match step(&mut b, *last, tk) {
                                Ok(c) if b.st.len() <= MAX && (b.popped as usize) <= MAX => {
                                    next.insert((b, c));
                                }
                                Ok(_) => {
                                    fails.entry((inst, pi, pos, ctx)).or_insert("the stack grows past the bound".into());
                                }
                                Err(e) => {
                                    fails.entry((inst, pi, pos, ctx)).or_insert(format!("`{name}` after {last:?}: {e}"));
                                }
                            }
                        }
                        S::N(b) => {
                            let t0 = a.peek(0);
                            let cctx: Ctx = (t0, *last);
                            let ck = (b, cctx);
                            deps.entry(ck.clone()).or_default().insert(key.clone());
                            if !sums.contains_key(&ck) {
                                sums.insert(ck.clone(), BTreeSet::new());
                                from.insert(ck.clone(), (key.clone(), pi, pos));
                                if queued.insert(ck.clone()) {
                                    work.push(ck.clone());
                                }
                            }
                            for (pops, push, c) in &sums[&ck] {
                                let mut a2 = a.clone();
                                for _ in 0..*pops {
                                    a2.pop();
                                }
                                for f in push {
                                    a2.push(*f);
                                }
                                if a2.st.len() <= MAX && (a2.popped as usize) <= MAX {
                                    next.insert((a2, *c));
                                } else {
                                    fails.entry((inst, pi, pos, ctx)).or_insert("the stack grows past the bound".into());
                                }
                            }
                        }
                    }
                }
                states = next;
            }
            for (a, c) in states {
                out.insert((a.popped, a.st, c));
            }
        }
        let cur = sums.entry(key.clone()).or_default();
        let before = cur.len();
        cur.extend(out);
        if cur.len() != before {
            for d in deps.get(&key).into_iter().flatten() {
                if queued.insert(d.clone()) {
                    work.push(d.clone());
                }
            }
        }
        if first && !fails.is_empty() {
            break;
        }
    }
    let fails = fails.into_iter().map(|((inst, prod, pos, ctx), what)| Fail { inst, prod, pos, ctx, what }).collect();
    Check { sums, fails, from }
}

/// The goal's start instance for `nt` (Script or Module).
fn goal(g: &Cfg, nt: &str) -> Option<u32> {
    g.starts.iter().map(|&(k, _)| k).find(|&k| g.keys[k as usize].nt == nt && g.keys[k as usize].on.is_empty())
}

/// `spec-gen divmode [-annexb] [-goal Script|Module] [-v]`: M's check over the goal's instances.
pub fn run(html: &str, rest: &[String]) -> Result<bool, String> {
    let gl = Gl::load(html, None)?;
    let mut src = Src::from_gl(&gl, rest.iter().any(|a| a == "-annexb"));
    let g = Cfg::expand(&mut src);
    let nt = rest.iter().position(|a| a == "-goal").and_then(|i| rest.get(i + 1)).map(String::as_str).unwrap_or("Script");
    let k = goal(&g, nt).ok_or(format!("no goal {nt}"))?;
    let module = nt == "Module";
    let root: Ctx = (Some(bottom(module)), Cls::Stmt);
    let arg = |f: &str| rest.iter().position(|a| a == f).and_then(|i| rest.get(i + 1));
    let limit = arg("-limit").and_then(|v| v.parse().ok()).unwrap_or(usize::MAX);
    let c = check(&g, &[(k, root)], limit, rest.iter().any(|a| a == "-first"));
    let ends = &c.sums[&(k, root)];
    let reached: BTreeSet<u32> = c.sums.keys().map(|k| k.0).collect();
    println!(
        "divmode {nt}{}: {} instances reached, {} instance contexts, {} failures; the goal's effects: {:?}",
        if rest.iter().any(|a| a == "-annexb") { " (Annex B)" } else { "" },
        reached.len(),
        c.sums.len(),
        c.fails.len(),
        ends
    );
    if rest.iter().any(|a| a == "-stats") {
        let mut big: Vec<_> = c.sums.iter().map(|(k, e)| (e.len(), k)).collect();
        big.sort_by(|a, b| b.0.cmp(&a.0));
        for (n, (i, x)) in big.iter().take(12) {
            let e = c.sums[&(*i, *x)].iter().next_back();
            println!("  big {n}: {} [ctx {x:?}] e.g. {e:?}", crate::lr1::key_name(&g.keys[*i as usize], &g.toks));
        }
    }
    if let Some(i) = rest.iter().position(|a| a == "-sum") {
        let (n, x) = (&rest[i + 1], &rest[i + 2]);
        for ((k, ctx), e) in c.sums.iter().filter(|((k, ctx), _)| crate::lr1::key_name(&g.keys[*k as usize], &g.toks).starts_with(n.as_str()) && format!("{ctx:?}").contains(x.as_str())) {
            println!("  sum {} [ctx {ctx:?}]: {e:?}", crate::lr1::key_name(&g.keys[*k as usize], &g.toks));
        }
    }
    if let Some(i) = rest.iter().position(|a| a == "-why") {
        let (n, x) = (&rest[i + 1], &rest[i + 2]);
        let found = c.sums.keys().find(|(k, ctx)| crate::lr1::key_name(&g.keys[*k as usize], &g.toks).starts_with(n.as_str()) && format!("{ctx:?}").contains(x.as_str()));
        let mut k = found.cloned();
        while let Some(key) = k {
            println!("  why {} [ctx {:?}]", crate::lr1::key_name(&g.keys[key.0 as usize], &g.toks), key.1);
            k = c.from.get(&key).map(|(pk, pi, pos)| {
                println!("    by {} @{pos}", g.prods[*pi].name);
                pk.clone()
            });
        }
    }
    let v = rest.iter().any(|a| a == "-v");
    for f in c.fails.iter().take(if v { usize::MAX } else { 40 }) {
        let p = &g.prods[f.prod];
        println!("  {} @{}: {} [ctx {:?}] {}", p.name, f.pos, crate::lr1::key_name(&g.keys[f.inst as usize], &g.toks), f.ctx, f.what);
        if v {
            let mut k = (f.inst, f.ctx);
            let mut prev = f.ctx;
            for _ in 0..400 {
                let Some((pk, pi, pos)) = c.from.get(&k) else { break };
                if pk.1 != prev {
                    println!("    <- {} @{} [ctx {:?}]", g.prods[*pi].name, pos, pk.1);
                    prev = pk.1;
                }
                k = pk.clone();
            }
        }
    }
    let ok = c.fails.is_empty() && ends.iter().all(|(p, s, _)| *p == 0 && s.is_empty());
    Ok(ok && g.errors.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// M's modes before each token of a sentence, its texts given as M reads them.
    fn modes(toks: &[Tk]) -> Result<Vec<bool>, String> {
        run(false, toks).map(|r| r.0)
    }

    /// M's modes over a sentence of the goal, and its stack and class at the end.
    fn run(module: bool, toks: &[Tk]) -> Result<(Vec<bool>, Vec<Frame>, Cls), String> {
        let mut s = vec![bottom(module)];
        let mut last = Cls::Stmt;
        let mut out = Vec::new();
        for t in toks {
            out.push(div(last));
            last = step(&mut s, last, *t)?;
        }
        Ok((out, s, last))
    }

    #[test]
    fn using_after_a_for_paren_is_the_left_side_of_of() {
        use Tk::*;
        let (m, s, c) = run(false, &[W("for"), P("("), W("using"), W("of"), Re, P(")"), P(";")]).unwrap();
        assert!(!m[4] && s == vec![bottom(false)] && c == Cls::Stmt);
    }

    #[test]
    fn async_of_arrow_in_a_var_initializer_ends_at_in() {
        use Tk::*;
        let f = [W("for"), P("("), W("var"), W("a"), P("="), W("async"), W("of"), P("=>"), W("b"), W("in"), Re, P(")"), P(";")];
        let (m, s, c) = run(false, &f).unwrap();
        assert!(!m[10] && s == vec![bottom(false)] && c == Cls::Stmt);
    }

    #[test]
    fn export_star_as_takes_a_reserved_name() {
        use Tk::*;
        let (m, s, _) = run(true, &[W("export"), P("*"), W("as"), W("class"), W("from"), Lit, P(";"), Re]).unwrap();
        assert!(!m[7] && s == vec![bottom(true)]);
    }

    #[test]
    fn with_braces_are_import_attributes() {
        use Tk::*;
        let f = [W("import"), W("x"), W("from"), Lit, W("with"), P("{"), W("function"), P(":"), Lit, P("}"), P(";"), Re];
        let (m, s, _) = run(true, &f).unwrap();
        assert!(!m[11] && s == vec![bottom(true)]);
    }

    #[test]
    fn a_block_ends_in_a_statement_start_and_an_object_in_an_operand() {
        use Tk::*;
        let m = modes(&[P("{"), P("}"), Re, P(";"), W("x"), P("="), P("{"), P("}"), P("/"), Lit]).unwrap();
        assert_eq!(m, vec![false, false, false, true, false, true, false, false, true, false]);
    }

    #[test]
    fn yield_in_an_arrow_body_is_an_identifier() {
        use Tk::*;
        let f = [W("function"), P("*"), W("g"), P("("), P(")"), P("{"), W("x"), P("=>"), W("yield"), P("/"), Lit, P(","), W("yield"), Re, P("}")];
        let m = modes(&f).unwrap();
        assert!(m[9] && !m[13]);
    }
}
