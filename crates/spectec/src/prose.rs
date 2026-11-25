//! Human-readable ECMA-262 algorithm prose extractor (`spectec prose`).

use crate::ast::*;
use crate::print::tok_ident;
use std::fmt::Write;

fn render_val(v: &ValLit) -> String {
    match v {
        ValLit::Undefined => "*undefined*".into(),
        ValLit::Null => "*null*".into(),
        ValLit::Bool(true) => "*true*".into(),
        ValLit::Bool(false) => "*false*".into(),
        ValLit::This => "*this*".into(),
        ValLit::Str(s) => format!("*{s:?}*"),
        ValLit::Nan(Sub::None) => "*NaN*".into(),
        ValLit::Nan(Sub::F) => "*NaN*<sub>𝔽</sub>".into(),
        ValLit::Nan(Sub::Z) => "*NaN*<sub>ℤ</sub>".into(),
        ValLit::Num(sg, m, sb) => {
            let sgs = match sg { Sign::None => "", Sign::Plus => "+", Sign::Minus => "-" };
            let ms = match m {
                Mag::Inf => "∞".into(),
                Mag::Num(Numeral::Dec(n)) => n.to_string(),
                Mag::Num(Numeral::Hex(_, d)) => format!("0x{d}"),
                Mag::Num(Numeral::Frac(w, f, p)) => format!("{w}.{:0>width$}", f, width = *p as usize),
            };
            let suf = match sb { Sub::None => "", Sub::F => "<sub>𝔽</sub>", Sub::Z => "<sub>ℤ</sub>" };
            format!("*{sgs}{ms}*{suf}")
        }
        ValLit::Err(f) => format!("a *{f}* exception"),
        ValLit::BigN(Numeral::Dec(n)) => format!("*{n}*<sub>ℤ</sub>"),
        ValLit::BigN(Numeral::Hex(_, d)) => format!("*0x{d}*<sub>ℤ</sub>"),
        ValLit::BigN(Numeral::Frac(w, f, p)) => format!("*{w}.{:0>width$}*<sub>ℤ</sub>", f, width = *p as usize),
    }
}

fn render_expr(e: &Expr) -> String {
    match e {
        Expr::Var(x) => format!("_{x}_"),
        Expr::Bnd(x) => format!("?_{x}_"),
        Expr::Val(v) => render_val(v),
        Expr::Math(Sign::None, Mag::Num(Numeral::Dec(n))) => n.to_string(),
        Expr::Math(sg, m) => {
            let sgs = match sg { Sign::None => "", Sign::Plus => "+", Sign::Minus => "-" };
            let ms = match m {
                Mag::Inf => "∞".into(),
                Mag::Num(Numeral::Dec(n)) => n.to_string(),
                Mag::Num(Numeral::Hex(_, d)) => format!("0x{d}"),
                Mag::Num(Numeral::Frac(w, f, p)) => format!("{w}.{:0>width$}", f, width = *p as usize),
            };
            format!("{sgs}{ms}")
        }
        Expr::Enum(en) => format!("~{en}~"),
        Expr::Param(p) => format!("[{p}]"),
        Expr::Intrinsic(f) => format!("%{f}%"),
        Expr::FieldName(f) => format!("[[{f}]]"),
        Expr::Nt(n, _) => format!("|{n}|"),
        Expr::Prod(ps) => ps.join(" / "),
        Expr::CodeUnit(_, d, Some(nm)) => format!("the code unit 0x{d} ({nm})"),
        Expr::CodeUnit(_, d, None) => format!("the code unit 0x{d}"),
        Expr::CodePoint(_, d, Some(nm)) => format!("the code point U+{d} ({nm})"),
        Expr::CodePoint(_, d, None) => format!("the code point U+{d}"),
        Expr::Code(s) | Expr::Term(s) => format!("`{s}`"),
        Expr::Call(Callee::Alg(a), args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}({})", a.clause, xs.join(", "))
        }
        Expr::Call(Callee::Prim(p), args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{p}({})", xs.join(", "))
        }
        Expr::CallAt(a, args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}({})", a.clause, xs.join(", "))
        }
        Expr::Sdo(s, sub, args) => {
            let mut txt = format!("{s} of {}", render_expr(sub));
            if !args.is_empty() {
                let xs: Vec<_> = args.iter().map(render_expr).collect();
                write!(txt, " with arguments ({})", xs.join(", ")).unwrap();
            }
            txt
        }
        Expr::Component(c, sub) => format!("the {c} of {}", render_expr(sub)),
        Expr::Field(o, f) => format!("{}.[[{f}]]", render_expr(o)),
        Expr::IMethod(o, m, args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}.[[{m}]]({})", render_expr(o), xs.join(", "))
        }
        Expr::CMethod(o, m, args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}.{m}({})", render_expr(o), xs.join(", "))
        }
        Expr::Apply(f, args) => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}({})", render_expr(f), xs.join(", "))
        }
        Expr::Index(o, i) => format!("{}[{}]", render_expr(o), render_expr(i)),
        Expr::Q(x) => format!("? {}", render_expr(x)),
        Expr::Bang(x) => format!("! {}", render_expr(x)),
        Expr::Un(UnOp::Neg, x) => format!("-{}", render_expr(x)),
        Expr::Un(UnOp::Not, x) => format!("not {}", render_expr(x)),
        Expr::Bin(op, a, b) => {
            let os = match op {
                BinOp::Add | BinOp::Plus => "+",
                BinOp::Sub => "-",
                BinOp::Mul | BinOp::Times => "×",
                BinOp::Div => "/",
                BinOp::Modulo => "modulo",
                BinOp::Pow => "^",
            };
            format!("{} {os} {}", render_expr(a), render_expr(b))
        }
        Expr::Paren(x) => format!("({})", render_expr(x)),
        Expr::List(es) => {
            let xs: Vec<_> = es.iter().map(render_expr).collect();
            format!("« {} »", xs.join(", "))
        }
        Expr::Record(sort, fs) => {
            let hd = sort.as_deref().unwrap_or("Record");
            let xs: Vec<_> = fs.iter().map(|(f, v)| format!("[[{f}]]: {}", render_expr(v))).collect();
            format!("{hd} {{ {} }}", xs.join(", "))
        }
        Expr::ResumedWith(x) => format!("the value passed to the resumption of {}", render_expr(x)),
        Expr::ThisNode => "this Parse Node".into(),
        Expr::Child(_, nt) => format!("the |{nt}| child"),
        Expr::ChildOf(x, nt) => format!("the |{nt}| of {}", render_expr(x)),
        Expr::ThisValue => "the *this* value".into(),
        Expr::NewTarget => "NewTarget".into(),
        Expr::Xref(c) => format!("<xref {c}>"),
        Expr::Closure(k) => format!("<closure {k}>"),
        Expr::Table(t) => format!("<table {t}>"),
        Expr::Definition(c) => format!("<def {c}>"),
        Expr::TableStep(t, k) => format!("row {} of table {t}", render_expr(k)),
        Expr::Data(DataLit::Sort(s)) => format!("sort {s}"),
        Expr::Data(DataLit::Choice(i)) => format!("choice {i}"),
        Expr::Data(DataLit::Absent) => "absent".into(),
        Expr::OfCond(c) => render_cond(c),
    }
}

fn render_pred(p: &Pred) -> String {
    match p {
        Pred::IsVal { neg, neither, vals } => {
            let v: Vec<_> = vals.iter().map(render_expr).collect();
            let j = if vals.len() > 1 { if *neither { "neither " } else { "either " } } else { "" };
            let sep = if *neither { " nor " } else { " or " };
            format!("is {}{j}{}", if *neg && !*neither { "not " } else { "" }, v.join(sep))
        }
        Pred::IsTy { neg, neither, tys } => {
            let t: Vec<_> = tys.iter().map(render_ty).collect();
            let j = if tys.len() > 1 { if *neither { "neither " } else { "either " } } else { "" };
            let sep = if *neither { " nor " } else { " or " };
            format!("is {}{j}{}", if *neg && !*neither { "not " } else { "" }, t.join(sep))
        }
        Pred::Call { callee: Callee::Alg(a), args, neg } => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}{}({})", if *neg { "does not satisfy " } else { "satisfies " }, a.clause, xs.join(", "))
        }
        Pred::Call { callee: Callee::Prim(pr), args, neg } => {
            let xs: Vec<_> = args.iter().map(render_expr).collect();
            format!("{}{}({})", if *neg { "not " } else { "" }, pr, xs.join(", "))
        }
    }
}

fn render_cond(c: &Cond) -> String {
    match c {
        Cond::Preds(e, p, rest) => {
            let mut s = format!("{} {}", render_expr(e), render_pred(p));
            for (j, pr) in rest {
                let js = match j { Conj::And => "and", Conj::Or => "or" };
                write!(s, " {js} {}", render_pred(pr)).unwrap();
            }
            s
        }
        Cond::Rel(op, a, b) => {
            let os = match op { RelOp::Lt => "<", RelOp::Le => "≤", RelOp::Gt => ">", RelOp::Ge => "≥", RelOp::Eq => "=", RelOp::Ne => "≠" };
            format!("{} {os} {}", render_expr(a), render_expr(b))
        }
        Cond::And(cs) => cs.iter().map(render_cond).collect::<Vec<_>>().join(" and "),
        Cond::Or(cs) => cs.iter().map(render_cond).collect::<Vec<_>>().join(" or "),
        Cond::Paren(c) => format!("({})", render_cond(c)),
        Cond::Alg(a) => a.clause.clone(),
        Cond::Expr(e) => render_expr(e),
        Cond::Pass(k) => format!("[unchecked: {k}]"),
    }
}

fn render_ty(t: &TyExpr) -> String {
    match t {
        TyExpr::Sort { mods, sort } => {
            if mods.is_empty() { sort.clone() } else { format!("{} {sort}", mods.join(" ")) }
        }
        TyExpr::ListOf(inner) => format!("a List of {}", render_ty(inner)),
        TyExpr::SeqOf(inner) => format!("a sequence of {}", render_ty(inner)),
        TyExpr::ButNot(a, b) => format!("{}, but not {}", render_ty(a), render_ty(b)),
        TyExpr::Doc(s) => s.clone(),
        TyExpr::Union(ts) => ts.iter().map(render_ty).collect::<Vec<_>>().join(" or "),
        TyExpr::Completion(None) => "a Completion Record".into(),
        TyExpr::Completion(Some(inner)) => format!("either a normal completion containing {} or an abrupt completion", render_ty(inner)),
        TyExpr::Interval(t, lo, hi) => format!("{} in [{}, {}]", render_ty(t), render_expr(lo), render_expr(hi)),
        TyExpr::Value(e) => render_expr(e),
        TyExpr::Var(x) => format!("_{x}_"),
        TyExpr::Nt(n) => format!("a |{n}| Parse Node"),
        TyExpr::Record(fs) => {
            let xs: Vec<_> = fs.iter().map(|(f, t)| format!("[[{f}]]: {}", render_ty(t))).collect();
            format!("Record {{ {} }}", xs.join(", "))
        }
        TyExpr::That(t, p, _) => format!("{} that {}", render_ty(t), render_pred(p)),
        TyExpr::Pred(p) => render_pred(p),
    }
}

fn render_steps(out: &mut String, ind: usize, stmts: &[Stmt]) {
    let pad = "  ".repeat(ind);
    for s in stmts {
        match s {
            Stmt::Let(x, e) => writeln!(out, "{pad}1. Let _{x}_ be {}.", render_expr(e)).unwrap(),
            Stmt::Set(Place::Var(x), e) => writeln!(out, "{pad}1. Set _{x}_ to {}.", render_expr(e)).unwrap(),
            Stmt::Set(Place::Field(o, f), e) => writeln!(out, "{pad}1. Set {}.[[{f}]] to {}.", render_expr(o), render_expr(e)).unwrap(),
            Stmt::Set(Place::Expr(lhs), e) => writeln!(out, "{pad}1. Set {} to {}.", render_expr(lhs), render_expr(e)).unwrap(),
            Stmt::Ret(None) => writeln!(out, "{pad}1. Return.").unwrap(),
            Stmt::Ret(Some(e)) => writeln!(out, "{pad}1. Return {}.", render_expr(e)).unwrap(),
            Stmt::Perform(e) => writeln!(out, "{pad}1. Perform {}.", render_expr(e)).unwrap(),
            Stmt::If(c, bd, arms, els) => {
                match bd {
                    Body::Inline(st) => {
                        let mut sub = String::new();
                        render_steps(&mut sub, 0, &[(*st.clone())]);
                        let line = sub.trim_start_matches("1. ").trim_end();
                        writeln!(out, "{pad}1. If {}, {line}", render_cond(c)).unwrap();
                    }
                    Body::Block(ns) => {
                        writeln!(out, "{pad}1. If {}, then:", render_cond(c)).unwrap();
                        render_steps(out, ind + 1, ns);
                    }
                }
                for a in arms {
                    let ac = render_cond(a.cond.as_ref().unwrap());
                    match &a.body {
                        Body::Inline(st) => {
                            let mut sub = String::new();
                            render_steps(&mut sub, 0, &[(*st.clone())]);
                            let line = sub.trim_start_matches("1. ").trim_end();
                            writeln!(out, "{pad}1. Else if {ac}, {line}").unwrap();
                        }
                        Body::Block(ns) => {
                            writeln!(out, "{pad}1. Else if {ac}, then:").unwrap();
                            render_steps(out, ind + 1, ns);
                        }
                    }
                }
                if let Some(a) = els {
                    match &a.body {
                        Body::Inline(st) => {
                            let mut sub = String::new();
                            render_steps(&mut sub, 0, &[(*st.clone())]);
                            let line = sub.trim_start_matches("1. ").trim_end();
                            writeln!(out, "{pad}1. Else, {line}").unwrap();
                        }
                        Body::Block(ns) => {
                            writeln!(out, "{pad}1. Else,").unwrap();
                            render_steps(out, ind + 1, ns);
                        }
                    }
                }
            }
            Stmt::IfElse(c, s1, s2) => {
                writeln!(out, "{pad}1. If {}, {} else {}", render_cond(c), print_stmt_inline(s1), print_stmt_inline(s2)).unwrap();
            }
            Stmt::Assert(c) | Stmt::AssertAlways(c) => writeln!(out, "{pad}1. Assert: {}.", render_cond(c)).unwrap(),
            Stmt::AssertIf(c, d) => writeln!(out, "{pad}1. Assert: If {}, {}.", render_cond(c), render_cond(d)).unwrap(),
            Stmt::Unreachable(_) => writeln!(out, "{pad}1. (unreachable)").unwrap(),
            Stmt::ThrowVal(e) => writeln!(out, "{pad}1. Throw {}.", render_expr(e)).unwrap(),
            Stmt::Note(t) => writeln!(out, "{pad}1. NOTE: {t}").unwrap(),
            Stmt::Repeat(ns) => {
                writeln!(out, "{pad}1. Repeat,").unwrap();
                render_steps(out, ind + 1, ns);
            }
            Stmt::RepeatWhile(c, ns) => {
                writeln!(out, "{pad}1. Repeat, while {},", render_cond(c)).unwrap();
                render_steps(out, ind + 1, ns);
            }
            Stmt::RepeatUntil(c, ns) => {
                writeln!(out, "{pad}1. Repeat, until {},", render_cond(c)).unwrap();
                render_steps(out, ind + 1, ns);
            }
            Stmt::ForEach { x, ty, list, rev, body } => {
                let ts = ty.as_ref().map_or_else(String::new, |t| format!("{} ", render_ty(t)));
                let rs = if *rev { ", in reverse List order" } else { "" };
                writeln!(out, "{pad}1. For each {ts}_{x}_ of {}{rs}, do:", render_expr(list)).unwrap();
                render_body(out, ind + 1, body);
            }
            Stmt::ForRange { x, lo, lo_incl, hi, hi_incl, desc, body } => {
                let dir = if *desc { "down from" } else { "from" };
                let li = if *lo_incl { "inclusive" } else { "exclusive" };
                let hi_s = if *hi_incl { "inclusive" } else { "exclusive" };
                writeln!(out, "{pad}1. For each integer _{x}_ {dir} {} ({li}) to {} ({hi_s}), do:", render_expr(lo), render_expr(hi)).unwrap();
                render_body(out, ind + 1, body);
            }
            Stmt::Block(ns) => render_steps(out, ind, ns),
            other => {
                let line = crate::print::print_stmt(0, other);
                writeln!(out, "{pad}1. {line}.").unwrap();
            }
        }
    }
}

fn print_stmt_inline(s: &Stmt) -> String {
    let mut sub = String::new();
    render_steps(&mut sub, 0, &[s.clone()]);
    sub.trim_start_matches("1. ").trim_end().to_string()
}

fn render_body(out: &mut String, ind: usize, b: &Body) {
    match b {
        Body::Inline(s) => render_steps(out, ind, &[*s.clone()]),
        Body::Block(ns) => render_steps(out, ind, ns),
    }
}

pub fn render_clause(spec: &Spec, clause: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut found = 0usize;
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Def(a) if a.id.clause == clause => {
                    found += 1;
                    let ps: Vec<_> = a
                        .header
                        .params
                        .iter()
                        .map(|p| {
                            let o = if p.optional { "optional " } else { "" };
                            let ts = p.ty.as_ref().map_or_else(String::new, |t| format!(" ({})", render_ty(t)));
                            format!("{o}_{}_{ts}", p.x)
                        })
                        .collect();
                    writeln!(out, "{}({})", a.name, ps.join(", ")).unwrap();
                    render_steps(&mut out, 0, &a.body);
                    for (ci, cl) in a.closures.iter().enumerate() {
                        writeln!(out, "  Closure #{ci} ({})", tok_ident(&a.name)).unwrap();
                        render_steps(&mut out, 1, &cl.body);
                    }
                    out.push('\n');
                }
                TopItem::SdoRow(r) if r.id.clause == clause => {
                    found += 1;
                    writeln!(out, "{} ({})", r.sdo, r.keys.join(" / ")).unwrap();
                    render_steps(&mut out, 0, &r.steps);
                    out.push('\n');
                }
                TopItem::Early(e) if e.id.clause == clause => {
                    found += 1;
                    writeln!(out, "Early Errors ({})", e.keys.join(" / ")).unwrap();
                    for s in &e.sentences {
                        writeln!(out, "  * {s:?}").unwrap();
                    }
                    out.push('\n');
                }
                _ => {}
            }
        }
    }
    if found == 0 {
        return Err(format!("no definition or SDO row found for clause `{clause}`"));
    }
    Ok(out)
}
