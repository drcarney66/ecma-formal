//! Structural renderer from `spectec::ast` to `spec.html` ecmarkdown step trees,
//! SDO equations, and Early Errors rules.

use crate::call_templates::{render_ph_call, render_prim_call};
use crate::meta::CallTemplates;
use spectec::ast::*;
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug)]
pub struct Out {
    pub inline: String,
    pub trailing: String,
}

impl Out {
    pub fn raw(s: impl Into<String>) -> Self {
        Self { inline: s.into(), trailing: String::new() }
    }
}

pub struct DeclsCtx<'a> {
    pub ops: HashMap<String, String>,
    pub templates: &'a CallTemplates,
}

impl<'a> DeclsCtx<'a> {
    pub fn from_spec(spec: &Spec, templates: &'a CallTemplates) -> Self {
        let mut ops = HashMap::new();
        for f in &spec.files {
            for item in &f.items {
                match item {
                    TopItem::Decl(Decl::Clause { id, op: Some(op) }) => {
                        ops.insert(id.clone(), op.clone());
                    }
                    TopItem::Def(a) => {
                        ops.entry(a.id.clause.clone()).or_insert_with(|| a.name.clone());
                    }
                    _ => {}
                }
            }
        }
        Self { ops, templates }
    }

    pub fn op_name<'b>(&'b self, clause: &'b str) -> &'b str {
        self.ops.get(clause).map(|s| s.as_str()).unwrap_or(clause)
    }
}

pub struct Ctx<'a> {
    pub d: &'a DeclsCtx<'a>,
    pub closures: &'a [CloLit],
    pub depth: usize,
}

impl<'a> Ctx<'a> {
    pub fn deeper(&self) -> Self {
        Self { d: self.d, closures: self.closures, depth: self.depth + 1 }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockKind {
    Root,
    Closure(usize),
    Then(usize),
    Elif(usize, usize),
    Else(usize),
    Do(usize),
}

#[derive(Clone, Debug)]
pub enum UnitBody {
    None,
    Stmts(String, Vec<RenderUnit>),
    Closure(usize, Vec<RenderUnit>),
}

#[derive(Clone, Debug)]
pub struct RenderUnit {
    /// Original statement index within current slice.
    pub stmt_idx: usize,
    /// Sub-part within that statement (0 normally; for `If`, 0=then, 1..=arms, else).
    pub arm_idx: usize,
    /// Exact canonical SpecTec slice string (e.g. `print_stmt` or one arm).
    pub spectec_src: String,
    /// Structurally rendered ecmarkdown line (after `1. `).
    pub text: String,
    /// Nested children when compound block or closure literal.
    pub kids: UnitBody,
}

// --- Expressions, Predicates, Conditions, Types ---

pub fn render_numeral(n: &Numeral) -> String {
    match n {
        Numeral::Dec(v) => v.to_string(),
        Numeral::Hex(_, d) => format!("0x{d}"),
        Numeral::Frac(w, f, p) => format!("{w}.{:0>width$}", f, width = *p as usize),
    }
}

fn render_mag(m: &Mag) -> String {
    match m {
        Mag::Num(n) => render_numeral(n),
        Mag::Inf => "∞".into(),
    }
}

fn render_sign(s: Sign) -> &'static str {
    match s {
        Sign::None => "",
        Sign::Plus => "+",
        Sign::Minus => "-",
    }
}

fn render_sub(s: Sub) -> &'static str {
    match s {
        Sub::None => "",
        Sub::F => "<sub>𝔽</sub>",
        Sub::Z => "<sub>ℤ</sub>",
    }
}

fn written_text(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;")
}

pub fn render_val(v: &ValLit) -> String {
    match v {
        ValLit::Undefined => "*undefined*".into(),
        ValLit::Null => "*null*".into(),
        ValLit::Bool(true) => "*true*".into(),
        ValLit::Bool(false) => "*false*".into(),
        ValLit::This => "*this*".into(),
        ValLit::Str(s) => format!("*\"{}\"*", written_text(s)),
        ValLit::Nan(sb) => format!("*NaN*{}", render_sub(*sb)),
        ValLit::Num(sg, m, sb) => format!("*{}{}*{}", render_sign(*sg), render_mag(m), render_sub(*sb)),
        ValLit::Err(f) => format!("*{f}*"),
        ValLit::BigN(n) => format!("`{}n`", render_numeral(n)),
    }
}

fn var_text(x: &str) -> String {
    if let Some(rest) = x.strip_prefix('#') {
        rest.to_string()
    } else {
        format!("_{x}_")
    }
}

fn english_strs(conj: &str, xs: &[String]) -> String {
    match xs.len() {
        0 => String::new(),
        1 => xs[0].clone(),
        2 => format!("{} {conj} {}", xs[0], xs[1]),
        n => {
            let mut out = xs[..n - 1].join(", ");
            out.push_str(&format!(", {conj} {}", xs[n - 1]));
            out
        }
    }
}

fn clo_words(k: CloKind) -> &'static str {
    match k {
        CloKind::Abstract => "Abstract Closure",
        CloKind::Job => "Job Abstract Closure",
        CloKind::Matcher => "Matcher",
        CloKind::MatcherContinuation => "MatcherContinuation",
        CloKind::ReadModifyWrite => "read-modify-write modification function",
    }
}

fn render_call_arg(cx: &Ctx, e: &Expr) -> String {
    match e {
        Expr::ThisValue => "*this* value".into(),
        _ => render_expr(cx, e).inline,
    }
}

pub fn render_expr(cx: &Ctx, e: &Expr) -> Out {
    match e {
        Expr::Var(x) | Expr::Bnd(x) => Out::raw(var_text(x)),
        Expr::Val(v) => Out::raw(render_val(v)),
        Expr::Math(sg, m) => Out::raw(format!("{}{}", render_sign(*sg), render_mag(m))),
        Expr::Enum(en) => Out::raw(format!("~{en}~")),
        Expr::Param(p) => Out::raw(format!("<sub>[{p}]</sub>")),
        Expr::Intrinsic(f) => Out::raw(format!("%{f}%")),
        Expr::FieldName(f) => Out::raw(format!("[[{f}]]")),
        Expr::Nt(n, args) => {
            if args.is_empty() {
                Out::raw(format!("|{n}|"))
            } else {
                let xs: Vec<_> = args
                    .iter()
                    .map(|a| format!("{}{}", if a.plus { "+" } else { "~" }, a.param))
                    .collect();
                Out::raw(format!("|{n}[{}]|", xs.join(", ")))
            }
        }
        Expr::Prod(ps) => {
            let xs: Vec<_> = ps.iter().map(|p| {
                // Convert `Grammar - Lhs : rhs` or `Grammar 10 Lhs : rhs` -> `<emu-grammar>Lhs : rhs</emu-grammar>`
                if let Some((_, rest)) = p.split_once(' ') {
                    if let Some((_, rhs)) = rest.split_once(' ') {
                        return format!("<emu-grammar>{rhs}</emu-grammar>");
                    }
                }
                p.clone()
            }).collect();
            Out::raw(english_strs("or", &xs))
        }
        Expr::CodeUnit(_, d, nm) => {
            let mut s = format!("0x{d}");
            if let Some(n) = nm {
                s.push_str(&format!(" ({n})"));
            }
            Out::raw(s)
        }
        Expr::CodePoint(_, d, nm) => {
            let mut s = format!("U+{d}");
            if let Some(n) = nm {
                s.push_str(&format!(" ({n})"));
            }
            Out::raw(s)
        }
        Expr::Code(s) => Out::raw(format!("`{}`", written_text(s))),
        Expr::Term(s) => Out::raw(format!("`{s}`")),
        Expr::Call(Callee::Alg(a), args) => {
            if a.clause == "ph-new-error" {
                if let [Expr::FieldName(err)] = args.as_slice() {
                    let art = if err.starts_with(['A', 'E', 'I', 'O']) { "an" } else { "a" };
                    return Out::raw(format!("{art} newly created *{err}* exception"));
                }
            }
            if a.clause.starts_with("ph-") {
                if let Some(t) = cx.d.templates.phs.get(&a.clause) {
                    if let Some(out) = render_ph_call(cx, t, args) {
                        return out;
                    }
                }
            }
            let xs: Vec<_> = args.iter().map(|x| render_call_arg(cx, x)).collect();
            Out::raw(format!("{}({})", cx.d.op_name(&a.clause), xs.join(", ")))
        }
        Expr::Call(Callee::Prim(p), args) => {
            if let Some(out) = render_prim_call(cx, cx.d.templates, p, args, false) {
                return out;
            }
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            Out::raw(format!("{p}({})", xs.join(", ")))
        }
        Expr::CallAt(a, args) => {
            if a.clause.starts_with("ph-") {
                if let Some(t) = cx.d.templates.phs.get(&a.clause) {
                    if let Some(out) = render_ph_call(cx, t, args) {
                        return out;
                    }
                }
            }
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            Out::raw(format!("{}({})", cx.d.op_name(&a.clause), xs.join(", ")))
        }
        Expr::Sdo(s, sub, args) => {
            let mut out = format!("the {s} of {}", render_expr(cx, sub).inline);
            match args.len() {
                0 => {}
                1 => out.push_str(&format!(" with argument {}", render_expr(cx, &args[0]).inline)),
                _ => {
                    let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
                    out.push_str(&format!(" with arguments {}", english_strs("and", &xs)));
                }
            }
            Out::raw(out)
        }
        Expr::Component(c, sub) => Out::raw(format!("the {c} of {}", render_expr(cx, sub).inline)),
        Expr::Field(o, f) => Out::raw(format!("{}.[[{f}]]", render_expr(cx, o).inline)),
        Expr::IMethod(o, m, args) => {
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            Out::raw(format!("{}.[[{m}]]({})", render_expr(cx, o).inline, xs.join(", ")))
        }
        Expr::CMethod(o, m, args) => {
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            Out::raw(format!("{}.{m}({})", render_expr(cx, o).inline, xs.join(", ")))
        }
        Expr::Apply(f, args) => {
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            Out::raw(format!("{}({})", render_expr(cx, f).inline, xs.join(", ")))
        }
        Expr::Index(o, i) => Out::raw(format!("{}[{}]", render_expr(cx, o).inline, render_expr(cx, i).inline)),
        Expr::Q(x) => Out::raw(format!("? {}", render_expr(cx, x).inline)),
        Expr::Bang(x) => Out::raw(format!("! {}", render_expr(cx, x).inline)),
        Expr::Un(UnOp::Neg, x) => Out::raw(format!("-{}", render_expr(cx, x).inline)),
        Expr::Un(UnOp::Not, x) => Out::raw(format!("not {}", render_expr(cx, x).inline)),
        Expr::Bin(BinOp::Pow, a, b) => {
            Out::raw(format!("{}<sup>{}</sup>", render_expr(cx, a).inline, render_expr(cx, b).inline))
        }
        Expr::Bin(op, a, b) => {
            let os = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "×",
                BinOp::Div => "/",
                BinOp::Modulo => "modulo",
                BinOp::Plus => "plus",
                BinOp::Times => "times",
                BinOp::Pow => unreachable!(),
            };
            Out::raw(format!("{} {os} {}", render_expr(cx, a).inline, render_expr(cx, b).inline))
        }
        Expr::Paren(x) => Out::raw(format!("({})", render_expr(cx, x).inline)),
        Expr::List(es) => {
            if es.is_empty() {
                Out::raw("« »")
            } else {
                let xs: Vec<_> = es.iter().map(|x| render_expr(cx, x).inline).collect();
                Out::raw(format!("« {} »", xs.join(", ")))
            }
        }
        Expr::Record(sort, fs) => {
            let hd = match sort {
                Some(s) => format!("the {s} "),
                None => String::new(),
            };
            if fs.is_empty() {
                Out::raw(format!("{hd}{{ }}"))
            } else {
                let xs: Vec<_> = fs
                    .iter()
                    .map(|(f, v)| format!("[[{f}]]: {}", render_expr(cx, v).inline))
                    .collect();
                Out::raw(format!("{hd}{{ {} }}", xs.join(", ")))
            }
        }
        Expr::ResumedWith(x) => {
            Out::raw(format!("the Completion Record with which {} was just resumed", render_expr(cx, x).inline))
        }
        Expr::ThisNode => Out::raw("this Parse Node"),
        Expr::Child(k, n) => {
            let ord = match k {
                0 => "the first ",
                1 => "the second ",
                2 => "the third ",
                3 => "the derived ",
                7 => "the fourth ",
                5 | 6 => "",
                _ => "the ",
            };
            Out::raw(format!("{ord}|{n}|"))
        }
        Expr::ChildOf(_, n) => Out::raw(format!("|{n}|")),
        Expr::ThisValue => Out::raw("the *this* value"),
        Expr::NewTarget => Out::raw("NewTarget"),
        Expr::Xref(c) => Out::raw(format!("<emu-xref href=\"#{c}\"></emu-xref>")),
        Expr::Closure(site) => {
            let l = cx.closures.get(*site);
            match l {
                None => Out::raw(format!("<closure {site}>")),
                Some(l) => {
                    let params = match &l.params {
                        None => "no parameters".to_string(),
                        Some(ps) => format!(
                            "parameters ({})",
                            ps.iter().map(|p| var_text(p)).collect::<Vec<_>>().join(", ")
                        ),
                    };
                    let caps = if l.captures.is_empty() {
                        "nothing".to_string()
                    } else {
                        let cs: Vec<_> = l.captures.iter().map(|c| var_text(c)).collect();
                        english_strs("and", &cs)
                    };
                    let atom = if l.atomic { " atomically" } else { "" };
                    Out::raw(format!(
                        "a new {} with {params} that captures {caps} and performs the following steps{atom} when called:",
                        clo_words(l.kind)
                    ))
                }
            }
        }
        Expr::Table(t) => Out::raw(format!("<emu-xref href=\"#{t}\"></emu-xref>")),
        Expr::Definition(c) => Out::raw(format!("the definition specified in <emu-xref href=\"#{c}\"></emu-xref>")),
        Expr::TableStep(t, k) => Out::raw(format!(
            "the value that {} corresponds to in <emu-xref href=\"#{t}\"></emu-xref>",
            render_expr(cx, k).inline
        )),
        Expr::Data(DataLit::Sort(s)) => Out::raw(s.clone()),
        Expr::Data(DataLit::Choice(i)) => Out::raw(format!("choice {i}")),
        Expr::Data(DataLit::Absent) => Out::raw("absent"),
        Expr::OfCond(c) => render_cond(cx, c),
    }
}

fn render_pred(cx: &Ctx, p: &Pred) -> String {
    match p {
        Pred::IsVal { neg, neither, vals } => {
            let vs: Vec<_> = vals.iter().map(|v| render_expr(cx, v).inline).collect();
            if *neither {
                format!("is neither {}", english_strs("nor", &vs))
            } else {
                let not = if *neg { "not " } else { "" };
                let hd = if vs.len() > 2 { "one of " } else { "" };
                format!("is {not}{hd}{}", english_strs("or", &vs))
            }
        }
        Pred::IsTy { neg, neither, tys } => {
            let ts: Vec<_> = tys.iter().map(|t| render_ty(cx, t)).collect();
            if *neither {
                format!("is neither {}", english_strs("nor", &ts))
            } else {
                let not = if *neg { "not " } else { "" };
                let hd = if ts.len() > 2 { "one of " } else { "" };
                format!("is {not}{hd}{}", english_strs("or", &ts))
            }
        }
        Pred::Call { callee: Callee::Alg(a), args, neg } => {
            if a.clause.starts_with("ph-") {
                if let Some(t) = cx.d.templates.phs.get(&a.clause) {
                    if let Some(out) = render_ph_call(cx, t, args) {
                        return out.inline;
                    }
                }
            }
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            let kw = if *neg { "fails" } else { "satisfies" };
            format!("{kw} {}({})", cx.d.op_name(&a.clause), xs.join(", "))
        }
        Pred::Call { callee: Callee::Prim(pr), args, neg } => {
            if !neg {
                if let Some(out) = render_prim_call(cx, cx.d.templates, pr, args, false) {
                    return out.inline;
                }
            } else if pr == "HasSlot" && args.len() == 1 {
                return format!("does not have a {} internal slot", render_expr(cx, &args[0]).inline);
            } else if pr == "HasField" && args.len() == 1 {
                return format!("does not have a {} field", render_expr(cx, &args[0]).inline);
            } else if pr == "Contains" && args.len() == 1 {
                return format!("does not contain {}", render_expr(cx, &args[0]).inline);
            } else if pr == "IsEmpty" && args.is_empty() {
                return "is not empty".into();
            } else if pr == "Present" && args.is_empty() {
                return "is not present".into();
            } else if pr == "IsFinite" && args.is_empty() {
                return "is not finite".into();
            }
            let xs: Vec<_> = args.iter().map(|x| render_expr(cx, x).inline).collect();
            let kw = if *neg { "fails" } else { "satisfies" };
            format!("{kw} {pr}({})", xs.join(", "))
        }
    }
}

pub fn render_cond(cx: &Ctx, c: &Cond) -> Out {
    match c {
        Cond::Preds(e, p, rest) => {
            let mut s = format!("{} {}", render_expr(cx, e).inline, render_pred(cx, p));
            for (j, pr) in rest {
                let js = match j { Conj::And => "and", Conj::Or => "or" };
                s.push_str(&format!(" {js} {}", render_pred(cx, pr)));
            }
            Out::raw(s)
        }
        Cond::Rel(op, a, b) => {
            let os = match op {
                RelOp::Lt => "&lt;",
                RelOp::Le => "≤",
                RelOp::Gt => ">",
                RelOp::Ge => "≥",
                RelOp::Eq => "=",
                RelOp::Ne => "≠",
            };
            Out::raw(format!("{} {os} {}", render_expr(cx, a).inline, render_expr(cx, b).inline))
        }
        Cond::And(cs) => {
            let xs: Vec<_> = cs.iter().map(|x| render_cond(cx, x).inline).collect();
            Out::raw(xs.join(" and "))
        }
        Cond::Or(cs) => {
            let xs: Vec<_> = cs.iter().map(|x| render_cond(cx, x).inline).collect();
            Out::raw(xs.join(" or "))
        }
        Cond::Paren(x) => Out::raw(format!("({})", render_cond(cx, x).inline)),
        Cond::Alg(_) => Out::raw("the following algorithm returns *true*:"),
        Cond::Expr(e) => render_expr(cx, e),
        Cond::Pass(k) => Out::raw(k.clone()),
    }
}

pub fn render_ty(cx: &Ctx, t: &TyExpr) -> String {
    match t {
        TyExpr::Sort { mods, sort } => {
            let base = if mods.is_empty() {
                sort.clone()
            } else {
                format!("{} {sort}", mods.join(" "))
            };
            let article = if base.starts_with(['A', 'E', 'I', 'O', 'U', 'a', 'e', 'i', 'o']) {
                "an"
            } else {
                "a"
            };
            if sort == "anything" { base } else { format!("{article} {base}") }
        }
        TyExpr::ListOf(inner) => format!("a List of {}", render_ty(cx, inner)),
        TyExpr::SeqOf(inner) => format!("a sequence of {}", render_ty(cx, inner)),
        TyExpr::Union(ts) => {
            let xs: Vec<_> = ts.iter().map(|x| render_ty(cx, x)).collect();
            english_strs("or", &xs)
        }
        TyExpr::Completion(None) => "a Completion Record".into(),
        TyExpr::Completion(Some(inner)) => format!("a normal completion containing {}", render_ty(cx, inner)),
        TyExpr::Interval(base, lo, hi) => format!(
            "{} in the inclusive interval from {} to {}",
            render_ty(cx, base),
            render_expr(cx, lo).inline,
            render_expr(cx, hi).inline
        ),
        TyExpr::Value(e) => render_expr(cx, e).inline,
        TyExpr::Var(x) => var_text(x),
        TyExpr::Nt(n) => format!("|{n}|"),
        TyExpr::Record(fs) => {
            let xs: Vec<_> = fs
                .iter()
                .map(|(f, ty)| format!("[[{f}]] ({})", render_ty(cx, ty)))
                .collect();
            format!("a Record with fields {}", english_strs("and", &xs))
        }
        TyExpr::That(base, p, rest) => {
            let mut s = format!("{} that {}", render_ty(cx, base), render_pred(cx, p));
            for (j, pr) in rest {
                let js = match j { Conj::And => "and", Conj::Or => "or" };
                s.push_str(&format!(" {js} {}", render_pred(cx, pr)));
            }
            s
        }
        TyExpr::Pred(p) => render_pred(cx, p),
        TyExpr::ButNot(a, b) => format!("{}, but not {}", render_ty(cx, a), render_ty(cx, b)),
        TyExpr::Doc(s) => s.clone(),
    }
}

fn find_closure_in_expr(e: &Expr) -> Option<usize> {
    match e {
        Expr::Closure(k) => Some(*k),
        Expr::Call(_, args) | Expr::CallAt(_, args) | Expr::List(args) => args.iter().find_map(find_closure_in_expr),
        Expr::Sdo(_, sub, args) | Expr::IMethod(sub, _, args) | Expr::CMethod(sub, _, args) | Expr::Apply(sub, args) => {
            find_closure_in_expr(sub).or_else(|| args.iter().find_map(find_closure_in_expr))
        }
        Expr::Component(_, x) | Expr::Field(x, _) | Expr::Q(x) | Expr::Bang(x) | Expr::Un(_, x) | Expr::Paren(x) | Expr::ResumedWith(x) | Expr::ChildOf(x, _) | Expr::TableStep(_, x) => {
            find_closure_in_expr(x)
        }
        Expr::Index(a, b) | Expr::Bin(_, a, b) => find_closure_in_expr(a).or_else(|| find_closure_in_expr(b)),
        Expr::Record(_, fs) => fs.iter().find_map(|(_, v)| find_closure_in_expr(v)),
        _ => None,
    }
}

fn lower_first(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) => c.to_lowercase().chain(cs).collect(),
        None => String::new(),
    }
}

fn render_leaf_stmt_line(cx: &Ctx, s: &Stmt) -> String {
    match s {
        Stmt::Let(x, e) => {
            let ex = render_expr(cx, e).inline;
            let stop = if matches!(e, Expr::Closure(_)) { "" } else { "." };
            format!("Let {} be {ex}{stop}", var_text(x))
        }
        Stmt::Set(p, e) => {
            let ps = match p {
                Place::Var(x) => var_text(x),
                Place::Field(o, f) => format!("{}.[[{f}]]", render_expr(cx, o).inline),
                Place::Expr(x) => render_expr(cx, x).inline,
            };
            if let Expr::Definition(c) = e {
                format!("Set {ps} as specified in <emu-xref href=\"#{c}\"></emu-xref>.")
            } else {
                let stop = if matches!(e, Expr::Closure(_)) { "" } else { "." };
                format!("Set {ps} to {}{stop}", render_expr(cx, e).inline)
            }
        }
        Stmt::Ret(None) => "Return.".into(),
        Stmt::Ret(Some(e)) => {
            let stop = if matches!(e, Expr::Closure(_)) { "" } else { "." };
            format!("Return {}{stop}", render_expr(cx, e).inline)
        }
        Stmt::Perform(Expr::Call(Callee::Alg(a), args)) if a.clause.starts_with("ph-") => {
            if let Some(t) = cx.d.templates.phs.get(&a.clause) {
                if t.kind == "step" {
                    if let Some(o) = render_ph_call(cx, t, args) {
                        return o.inline;
                    }
                }
            }
            let xs: Vec<_> = args.iter().map(|x| render_call_arg(cx, x)).collect();
            format!("Perform {}({}).", cx.d.op_name(&a.clause), xs.join(", "))
        }
        Stmt::Perform(Expr::Call(Callee::Prim(p), args)) => {
            if let Some(o) = render_prim_call(cx, cx.d.templates, p, args, true) {
                format!("{}.", o.inline)
            } else {
                let xs: Vec<_> = args.iter().map(|a| render_expr(cx, a).inline).collect();
                format!("Perform {p}({}).", xs.join(", "))
            }
        }
        Stmt::Perform(e) => format!("Perform {}.", render_expr(cx, e).inline),
        Stmt::IfElse(c, s1, s2) => {
            let l1 = lower_first(render_leaf_stmt_line(cx, s1).trim_end_matches('.'));
            let l2 = lower_first(&render_leaf_stmt_line(cx, s2));
            format!("If {}, {l1}; else {l2}", render_cond(cx, c).inline)
        }
        Stmt::Assert(c) | Stmt::AssertAlways(c) => format!("Assert: {}.", render_cond(cx, c).inline),
        Stmt::AssertIf(c, d) => {
            format!("Assert: If {}, then {}.", render_cond(cx, c).inline, render_cond(cx, d).inline)
        }
        Stmt::Unreachable(_) => "Assert: This step is never reached.".into(),
        Stmt::ThrowVal(Expr::Call(Callee::Alg(a), args)) if a.clause == "ph-new-error" => {
            if let [Expr::FieldName(err)] = args.as_slice() {
                let art = if err.starts_with(['A', 'E', 'I', 'O']) { "an" } else { "a" };
                format!("Throw {art} *{err}* exception.")
            } else {
                format!("Throw {}.", render_expr(cx, &Expr::Call(Callee::Alg(a.clone()), args.clone())).inline)
            }
        }
        Stmt::ThrowVal(Expr::Val(ValLit::Err(err))) => {
            let art = if err.starts_with(['A', 'E', 'I', 'O']) { "an" } else { "a" };
            format!("Throw {art} *{err}* exception.")
        }
        Stmt::ThrowVal(e) => format!("Throw {}.", render_expr(cx, e).inline),
        Stmt::Note(t) => format!("NOTE: {t}"),
        Stmt::Suspend(e, v) => {
            let extra = if *v == 1 { " and remove it from the execution context stack" } else { "" };
            format!("Suspend {}{extra}.", render_expr(cx, e).inline)
        }
        Stmt::Push(e, _) => {
            let ex = render_expr(cx, e).inline;
            format!("Push {ex} onto the execution context stack; {ex} is now the running execution context.")
        }
        Stmt::Remove(e, v) => {
            let extra = if *v == 0 {
                " and restore the execution context that is at the top of the execution context stack as the running execution context"
            } else {
                ""
            };
            format!("Remove {} from the execution context stack{extra}.", render_expr(cx, e).inline)
        }
        Stmt::RemoveRestore(e, r) => format!(
            "Remove {} from the execution context stack and restore {} as the running execution context.",
            render_expr(cx, e).inline,
            render_expr(cx, r).inline
        ),
        Stmt::ResumeTop => "Resume the context that is now on the top of the execution context stack as the running execution context.".into(),
        Stmt::ResumeLet { ctx, val, x } => format!(
            "Resume the suspended evaluation of {} passing {} as the result of the operation that suspended it. Let {} be the Completion Record passed by the resumed computation.",
            render_expr(cx, ctx).inline,
            render_expr(cx, val).inline,
            var_text(x)
        ),
        Stmt::Resume(ctx, v) => format!(
            "Resume {}, passing {}.",
            render_expr(cx, ctx).inline,
            render_expr(cx, v).inline
        ),
        Stmt::SetCodeState(ctx, v) => format!(
            "Set the code evaluation state of {} such that when evaluation is resumed for that execution context, {} will be called with no arguments.",
            render_expr(cx, ctx).inline,
            render_expr(cx, v).inline
        ),
        _ => spectec::print::print_stmt(0, s),
    }
}

fn stmt_closure(s: &Stmt) -> Option<usize> {
    match s {
        Stmt::Let(_, e) | Stmt::Set(_, e) | Stmt::Perform(e) | Stmt::ThrowVal(e) => find_closure_in_expr(e),
        Stmt::Ret(Some(e)) => find_closure_in_expr(e),
        _ => None,
    }
}

fn render_body_pair(cx: &Ctx, head_text: &str, cond_text: Option<&str>, bd: &Body, ind: usize, path_prefix: &str, st_src: String, s_idx: usize, a_idx: usize) -> RenderUnit {
    match bd {
        Body::Inline(st) => {
            let inline = lower_first(&render_leaf_stmt_line(cx, st));
            let text = match cond_text {
                Some(c) => format!("{head_text} {c}, {inline}"),
                None => format!("{head_text}, {inline}"),
            };
            let kids = if let Some(cl) = stmt_closure(st) {
                let kunits = render_units_at(cx, &cx.closures[cl].body, ind + 2, &format!("cl{cl}"));
                UnitBody::Closure(cl, kunits)
            } else {
                UnitBody::None
            };
            RenderUnit { stmt_idx: s_idx, arm_idx: a_idx, spectec_src: st_src, text, kids }
        }
        Body::Block(ns) => {
            let text = match cond_text {
                Some(c) => format!("{head_text} {c}, then"),
                None => format!("{head_text},"),
            };
            let kunits = render_units_at(cx, ns, ind + 2, path_prefix);
            RenderUnit {
                stmt_idx: s_idx,
                arm_idx: a_idx,
                spectec_src: st_src,
                text,
                kids: UnitBody::Stmts(path_prefix.to_string(), kunits),
            }
        }
    }
}

pub fn render_units_at(cx: &Ctx, stmts: &[Stmt], ind: usize, path: &str) -> Vec<RenderUnit> {
    let mut out = Vec::new();
    for (s_idx, s) in stmts.iter().enumerate() {
        let p_here = format!("{path}/{s_idx}");
        match s {
            Stmt::If(c, bd, arms, els) => {
                let cond_s = render_cond(cx, c).inline;
                let st_src = spectec::print::print_stmt(ind, s);
                out.push(render_body_pair(cx, "If", Some(&cond_s), bd, ind, &format!("{p_here}:then"), st_src.clone(), s_idx, 0));
                for (ai, arm) in arms.iter().enumerate() {
                    let ac = render_cond(cx, arm.cond.as_ref().unwrap()).inline;
                    out.push(render_body_pair(cx, "Else if", Some(&ac), &arm.body, ind, &format!("{p_here}:elif:{ai}"), format!("else_if #{ai} of {p_here}"), s_idx, ai + 1));
                }
                if let Some(el) = els {
                    out.push(render_body_pair(cx, "Else", None, &el.body, ind, &format!("{p_here}:else"), format!("else of {p_here}"), s_idx, arms.len() + 1));
                }
            }
            Stmt::Repeat(ns) => {
                let st_src = spectec::print::print_stmt(ind, s);
                let do_p = format!("{p_here}:do");
                let kunits = render_units_at(cx, ns, ind + 2, &do_p);
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text: "Repeat,".into(), kids: UnitBody::Stmts(do_p, kunits) });
            }
            Stmt::RepeatWhile(c, ns) => {
                let st_src = spectec::print::print_stmt(ind, s);
                let do_p = format!("{p_here}:do");
                let kunits = render_units_at(cx, ns, ind + 2, &do_p);
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text: format!("Repeat, while {},", render_cond(cx, c).inline), kids: UnitBody::Stmts(do_p, kunits) });
            }
            Stmt::RepeatUntil(c, ns) => {
                let st_src = spectec::print::print_stmt(ind, s);
                let do_p = format!("{p_here}:do");
                let kunits = render_units_at(cx, ns, ind + 2, &do_p);
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text: format!("Repeat, until {},", render_cond(cx, c).inline), kids: UnitBody::Stmts(do_p, kunits) });
            }
            Stmt::RepeatN(e, ns) => {
                let st_src = spectec::print::print_stmt(ind, s);
                let do_p = format!("{p_here}:do");
                let kunits = render_units_at(cx, ns, ind + 2, &do_p);
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text: format!("Repeat {} times:", render_expr(cx, e).inline), kids: UnitBody::Stmts(do_p, kunits) });
            }
            Stmt::ForEach { x, ty, list, rev, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let ts = ty.as_ref().map_or_else(|| "element ".into(), |t| format!("{} ", render_ty(cx, t)));
                let r = if *rev { " in reverse List order," } else { "" };
                let text = format!("For each {ts}{} of {},{r} do", var_text(x), render_expr(cx, list).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForEachRec { fields, x, list, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let fs: Vec<_> = fields.iter().map(|f| format!("[[{f}]]")).collect();
                let text = format!("For each Record {{ {} }} {} of {}, do", fs.join(", "), var_text(x), render_expr(cx, list).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForRange { x, lo, lo_incl, hi, hi_incl, desc, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let c1 = if *lo_incl { "≤" } else { "&lt;" };
                let c2 = if *hi_incl { "≤" } else { "&lt;" };
                let ord = if *desc { "descending" } else { "ascending" };
                let xv = var_text(x);
                let text = format!("For each integer {xv} such that {} {c1} {xv} {c2} {}, in {ord} order, do", render_expr(cx, lo).inline, render_expr(cx, hi).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForKeys { x, obj, cond, order, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let ord = match order {
                    0 => "in ascending numeric index order",
                    1 => "in ascending chronological order of property creation",
                    _ => "in descending numeric index order",
                };
                let text = format!("For each own property key {} of {} such that {}, {ord}, do", var_text(x), render_expr(cx, obj).inline, render_cond(cx, cond).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForIndex { x, list, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let text = format!("For each index {} of {}, do", var_text(x), render_expr(cx, list).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForChildren { x, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let text = format!("For each child node {} of this Parse Node, do", var_text(x));
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::ForChildrenOf { x, expr, body } => {
                let st_src = spectec::print::print_stmt(ind, s);
                let text = format!("For each child node {} of {}, do", var_text(x), render_expr(cx, expr).inline);
                let do_p = format!("{p_here}:do");
                let kids = match body {
                    Body::Block(ns) => {
                        let ku = render_units_at(cx, ns, ind + 2, &do_p);
                        UnitBody::Stmts(do_p, ku)
                    }
                    Body::Inline(_) => UnitBody::None,
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
            Stmt::Block(_) => {
                // Keep macro block as one unit at current depth so it aligns 1-to-1 against HTML macro line.
                let st_src = spectec::print::print_stmt(ind, s);
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text: "<block>".into(), kids: UnitBody::None });
            }
            _ => {
                let st_src = spectec::print::print_stmt(ind, s);
                let text = render_leaf_stmt_line(cx, s);
                let kids = if let Some(cl) = stmt_closure(s) {
                    let kunits = render_units_at(cx, &cx.closures[cl].body, ind + 2, &format!("cl{cl}"));
                    UnitBody::Closure(cl, kunits)
                } else {
                    UnitBody::None
                };
                out.push(RenderUnit { stmt_idx: s_idx, arm_idx: 0, spectec_src: st_src, text, kids });
            }
        }
    }
    out
}

pub fn render_equation_line(cx: &Ctx, r: &SdoRowDef) -> Option<String> {
    let gs: Vec<String> = r.keys.iter().map(|k| format!("<emu-grammar>{k}</emu-grammar>")).collect();
    let g_str = match gs.as_slice() {
        [] => return None,
        [a] => a.clone(),
        [a, b] => format!("{a} or of {b}"),
        _ => gs.join(" or of "),
    };
    let tail = match r.steps.as_slice() {
        [Stmt::If(c, Body::Inline(s1), arms, Some(els))] if arms.is_empty() => {
            if let (Stmt::Ret(Some(e1)), Body::Inline(s2)) = (s1.as_ref(), &els.body) {
                if let Stmt::Ret(Some(e2)) = s2.as_ref() {
                    format!(
                        "{} if {}. Otherwise, it is {}",
                        render_expr(cx, e1).inline,
                        render_cond(cx, c).inline,
                        render_expr(cx, e2).inline
                    )
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        xs if !xs.is_empty() => {
            let Some(Stmt::Ret(Some(e))) = xs.last() else { return None };
            let mut s = render_expr(cx, e).inline;
            for (i, st) in xs[..xs.len() - 1].iter().enumerate() {
                let Stmt::Let(v, val) = st else { return None };
                let kw = if i == 0 { "where" } else { "and" };
                s.push_str(&format!(", {kw} {} is {}", var_text(v), render_expr(cx, val).inline));
            }
            s
        }
        _ => return None,
    };
    Some(format!("The {} of {g_str} is {tail}.", r.sdo))
}

fn render_early_sent(cx: &Ctx, s: &EarlySent) -> String {
    match s {
        EarlySent::SyntaxError { early, cond, unless } => {
            let hd = if *early {
                "It is an early Syntax Error if"
            } else {
                "It is a Syntax Error if"
            };
            let u = match unless {
                None => String::new(),
                Some((UnlessForm::Plain, k)) => format!(" unless {}", render_cond(cx, k).inline),
                Some((UnlessForm::Comma, k)) => format!(", unless {}", render_cond(cx, k).inline),
                Some((UnlessForm::Optional, k)) => format!("<span normative-optional>, unless {}</span>", render_cond(cx, k).inline),
            };
            format!("{hd} {}{u}.", render_cond(cx, cond).inline)
        }
        EarlySent::SyntaxErrorIns(a, b) => format!(
            "It is a Syntax Error if {} <ins>and {}</ins>.",
            render_cond(cx, a).inline,
            render_cond(cx, b).inline
        ),
        EarlySent::MustCover(p, t) => {
            let ty_str = match t {
                TyExpr::Nt(n) => {
                    let art = if n.starts_with(['A', 'E', 'I', 'O']) { "an" } else { "a" };
                    format!("{art} |{n}|")
                }
                _ => render_ty(cx, t),
            };
            format!("{} must cover {ty_str}.", render_expr(cx, p).inline)
        }
        EarlySent::RulesApplied(_, raw) => format!("The Early Error rules for {raw} are applied."),
        EarlySent::IfInline(c, inner) => format!("If {}, {}", render_cond(cx, c).inline, lower_first(&render_early_sent(cx, inner))),
        EarlySent::Info(st) | EarlySent::NotApplied(_, st) | EarlySent::ForEachIn { stmt: st, .. } | EarlySent::Stmt(st) => {
            render_leaf_stmt_line(cx, st)
        }
    }
}

pub fn render_early_body(cx: &Ctx, r: &EarlyRow, layout: &str, indent: usize) -> String {
    let text = r.sentences.iter().map(|s| render_early_sent(cx, s)).collect::<Vec<_>>().join(" ");
    match layout {
        "block" => format!("\n{}{text}\n{}", " ".repeat(indent + 2), " ".repeat(indent)),
        _ => text,
    }
}

pub fn render_stmts_canonical(ind: usize, stmts: &[Stmt]) -> String {
    let pad = " ".repeat(ind);
    let ls: Vec<String> = stmts
        .iter()
        .map(|s| format!("{pad}{}", spectec::print::print_stmt(ind, s)))
        .collect();
    ls.join("\n")
}

pub fn render_early_canonical(r: &EarlyRow) -> String {
    let full = spectec::print::print_early_row(r);
    // Extract sentences { ... } block cleanly
    let start = full.find("  sentences {\n").unwrap() + "  sentences {\n".len();
    let end = full[start..].find("\n  }").unwrap() + start;
    full[start..end].to_string()
}

pub fn check_can_render_stmts(s: &str, expected_stmts: &[Stmt], ind: usize) -> Result<(), String> {
    // Wrap inside a dummy def to verify `@@spectec` parses cleanly back into AST matching `expected_stmts`!
    let vs: BTreeMap<String, ()> = BTreeMap::new();
    let _ = vs;
    let body_text = if ind == 2 {
        s.to_string()
    } else {
        let shift = ind;
        s.lines()
            .map(|l| {
                let trimmed = if l.len() >= shift && l[..shift].chars().all(|c| c == ' ') {
                    &l[shift..]
                } else {
                    l.trim_start()
                };
                format!("  {trimmed}")
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let wrapped = format!("def @check \"check\" (kind ao params []) vars [] {{\n{body_text}\n}}\n\n");
    let sf = spectec::parse::parse_str("patch.spectec", &wrapped)?;
    let Some(TopItem::Def(def)) = sf.items.into_iter().next() else {
        return Err("failed to parse patch statements".into());
    };
    if def.body != expected_stmts {
        return Err("parsed patch @@spectec AST does not equal live SpecTec AST slice".into());
    }
    Ok(())
}
