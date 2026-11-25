//! Canonical byte-for-byte SpecTec printer and formatter.

use crate::ast::*;
use crate::lexer::{is_clause_char, is_ident_cont, is_ident_start, is_keyword, is_prim_cont, is_prim_start};
use std::fmt::Write;

pub fn esc_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 32 || (c as u32) == 127 => {
                write!(out, "\\u{{{:x}}}", c as u32).unwrap();
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn tok_ident(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) if is_ident_start(c) && cs.all(is_ident_cont) && !is_keyword(s) => s.to_string(),
        _ => format!("#{}", esc_str(s)),
    }
}

pub fn tok_prim(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) if is_prim_start(c) && cs.all(is_prim_cont) && !is_keyword(s) => format!("${s}"),
        _ => format!("${}", esc_str(s)),
    }
}

pub fn tok_clause(s: &str) -> String {
    if !s.is_empty() && s.chars().all(is_clause_char) {
        format!("@{s}")
    } else {
        format!("@{}", esc_str(s))
    }
}

pub fn tok_alg_ref(a: &AlgRef) -> String {
    if a.idx == 0 {
        tok_clause(&a.clause)
    } else {
        format!("{}#{}", tok_clause(&a.clause), a.idx)
    }
}

pub fn tok_field(s: &str) -> String {
    format!("[[{s}]]")
}

pub fn tok_enum(s: &str) -> String {
    format!("~{s}~")
}

pub fn tok_prod(s: &str) -> String {
    format!("p{}", esc_str(s))
}

pub fn tok_table(s: &str) -> String {
    format!("t{}", esc_str(s))
}

pub fn print_sign(s: Sign) -> &'static str {
    match s {
        Sign::None => "",
        Sign::Plus => "+",
        Sign::Minus => "-",
    }
}

pub fn print_numeral(n: &Numeral) -> String {
    match n {
        Numeral::Dec(v) => v.to_string(),
        Numeral::Hex(v, d) => format!("hex({v}, {})", esc_str(d)),
        Numeral::Frac(w, f, p) => format!("frac({w}, {f}, {p})"),
    }
}

pub fn print_mag(m: &Mag) -> String {
    match m {
        Mag::Num(n) => print_numeral(n),
        Mag::Inf => "∞".into(),
    }
}

pub fn print_sub(s: Sub) -> &'static str {
    match s {
        Sub::None => "n",
        Sub::F => "f",
        Sub::Z => "z",
    }
}

pub fn print_val(v: &ValLit) -> String {
    match v {
        ValLit::Undefined => "undefined".into(),
        ValLit::Null => "null".into(),
        ValLit::Bool(true) => "true".into(),
        ValLit::Bool(false) => "false".into(),
        ValLit::This => "this".into(),
        ValLit::Str(s) => esc_str(s),
        ValLit::Nan(Sub::None) => "nan".into(),
        ValLit::Nan(Sub::F) => "nan_f".into(),
        ValLit::Nan(Sub::Z) => "nan_z".into(),
        ValLit::Num(sg, m, sb) => format!("num_{}({}{})", print_sub(*sb), print_sign(*sg), print_mag(m)),
        ValLit::Err(f) => format!("err {}", tok_field(f)),
        ValLit::BigN(n) => format!("bign({})", print_numeral(n)),
    }
}

fn expr_prec(e: &Expr) -> u8 {
    match e {
        Expr::Bin(BinOp::Add | BinOp::Sub | BinOp::Plus, _, _) => 1,
        Expr::Bin(BinOp::Mul | BinOp::Div | BinOp::Modulo | BinOp::Times, _, _) => 2,
        Expr::Bin(BinOp::Pow, _, _) => 3,
        Expr::Un(..) | Expr::Q(_) | Expr::Bang(_) | Expr::Component(..) => {
            // Note: `component` itself prints child at prec 4, its own exprPrec in bootstrap_spectec is 5!
            // Keep exact match with bootstrap_spectec.lean exprPrec!
            match e {
                Expr::Component(..) => 5,
                _ => 4,
            }
        }
        _ => 5,
    }
}

fn bin_sym(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Plus => "plus",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Modulo => "modulo",
        BinOp::Times => "times",
        BinOp::Pow => "^",
    }
}

fn rel_sym(op: RelOp) -> &'static str {
    match op {
        RelOp::Lt => "<",
        RelOp::Le => "<=",
        RelOp::Gt => ">",
        RelOp::Ge => ">=",
        RelOp::Eq => "==",
        RelOp::Ne => "!=",
    }
}

fn print_param_args(args: &[ParamArg]) -> String {
    if args.is_empty() {
        String::new()
    } else {
        let items: Vec<_> = args
            .iter()
            .map(|a| format!("{}{}", if a.plus { "+" } else { "~" }, tok_ident(&a.param)))
            .collect();
        format!("[{}]", items.join(", "))
    }
}

fn print_child(min_prec: u8, e: &Expr) -> String {
    if expr_prec(e) < min_prec {
        format!("{{{}}}", print_expr(e))
    } else {
        print_expr(e)
    }
}

pub fn print_expr(e: &Expr) -> String {
    match e {
        Expr::Var(x) => tok_ident(x),
        Expr::Bnd(x) => format!("?{}", tok_ident(x)),
        Expr::Val(v) => print_val(v),
        Expr::Math(Sign::None, Mag::Num(Numeral::Dec(n))) => n.to_string(),
        Expr::Math(sg, m) => format!("math({}{})", print_sign(*sg), print_mag(m)),
        Expr::Enum(en) => tok_enum(en),
        Expr::Param(p) => format!("param {}", tok_ident(p)),
        Expr::Intrinsic(f) => format!("intrinsic {}", tok_field(f)),
        Expr::FieldName(f) => tok_field(f),
        Expr::Nt(n, args) => format!("|{}{}|", tok_ident(n), print_param_args(args)),
        Expr::Prod(ps) => {
            let ks: Vec<_> = ps.iter().map(|s| tok_prod(s)).collect();
            format!("prods [{}]", ks.join(", "))
        }
        Expr::CodeUnit(n, d, nm) => {
            let ns = nm.as_deref().map_or_else(|| "none".into(), esc_str);
            format!("cu({n}, {}, {ns})", esc_str(d))
        }
        Expr::CodePoint(n, d, nm) => {
            let ns = nm.as_deref().map_or_else(|| "none".into(), esc_str);
            format!("cp({n}, {}, {ns})", esc_str(d))
        }
        Expr::Code(s) => format!("code {}", esc_str(s)),
        Expr::Term(s) => format!("term {}", esc_str(s)),
        Expr::Call(Callee::Alg(a), args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{}({})", tok_alg_ref(a), as_.join(", "))
        }
        Expr::Call(Callee::Prim(p), args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{}({})", tok_prim(p), as_.join(", "))
        }
        Expr::CallAt(a, args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("call_at {}({})", tok_alg_ref(a), as_.join(", "))
        }
        Expr::Sdo(s, sub, args) => {
            let ar = if args.is_empty() {
                String::new()
            } else {
                let as_: Vec<_> = args.iter().map(print_expr).collect();
                format!("; {}", as_.join(", "))
            };
            format!("sdo {}({}{ar})", tok_ident(s), print_expr(sub))
        }
        Expr::Component(c, sub) => format!("component {} of {}", tok_field(c), print_child(4, sub)),
        Expr::Field(obj, f) => format!("{}{}", print_child(5, obj), tok_field(f)),
        Expr::IMethod(obj, m, args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{}{}({})", print_child(5, obj), tok_field(m), as_.join(", "))
        }
        Expr::CMethod(obj, m, args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{}.{}({})", print_child(5, obj), tok_ident(m), as_.join(", "))
        }
        Expr::Apply(f, args) => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{}({})", print_child(5, f), as_.join(", "))
        }
        Expr::Index(obj, i) => format!("{}[{}]", print_child(5, obj), print_expr(i)),
        Expr::Q(x) => format!("? {}", print_child(4, x)),
        Expr::Bang(x) => format!("! {}", print_child(4, x)),
        Expr::Un(UnOp::Neg, x) => format!("neg {}", print_child(4, x)),
        Expr::Un(UnOp::Not, x) => format!("not {}", print_child(4, x)),
        Expr::Bin(op, a, b) => {
            let p = expr_prec(e);
            let lp = if *op == BinOp::Pow { p + 1 } else { p };
            let rp = if *op == BinOp::Pow { p } else { p + 1 };
            format!("{} {} {}", print_child(lp, a), bin_sym(*op), print_child(rp, b))
        }
        Expr::Paren(x) => format!("({})", print_expr(x)),
        Expr::List(es) => {
            let xs: Vec<_> = es.iter().map(print_expr).collect();
            format!("[{}]", xs.join(", "))
        }
        Expr::Record(sort, fs) => {
            let ks = sort.as_deref().map_or_else(String::new, |s| format!(" {}", tok_ident(s)));
            let fstr: Vec<_> = fs
                .iter()
                .map(|(f, v)| format!("{}: {}", tok_field(f), print_expr(v)))
                .collect();
            if fstr.is_empty() {
                format!("record{ks} {{}}")
            } else {
                format!("record{ks} {{ {} }}", fstr.join(", "))
            }
        }
        Expr::ResumedWith(x) => format!("resumed_with({})", print_expr(x)),
        Expr::ThisNode => "this_node".into(),
        Expr::Child(k, n) => format!("child {k} |{}|", tok_ident(n)),
        Expr::ChildOf(x, n) => format!("child_of({}, |{}|)", print_expr(x), tok_ident(n)),
        Expr::ThisValue => "this_value".into(),
        Expr::NewTarget => "new_target".into(),
        Expr::Xref(c) => format!("clause {}", tok_clause(c)),
        Expr::Closure(site) => format!("closure {site}"),
        Expr::Table(t) => format!("table {}", tok_table(t)),
        Expr::Definition(c) => format!("ref {}", tok_clause(c)),
        Expr::TableStep(t, k) => format!("table_step({}, {})", tok_table(t), print_expr(k)),
        Expr::Data(DataLit::Sort(s)) => format!("data sort {}", tok_ident(s)),
        Expr::Data(DataLit::Choice(i)) => format!("data choice {i}"),
        Expr::Data(DataLit::Absent) => "data absent".into(),
        Expr::OfCond(c) => format!("bool({})", print_cond(c)),
    }
}

pub fn print_pred(p: &Pred) -> String {
    match p {
        Pred::IsVal { neg, neither, vals } => {
            let n = if *neg { " not" } else { "" };
            let nei = if *neither { " neither" } else { "" };
            let vs: Vec<_> = vals.iter().map(print_expr).collect();
            format!("is{n}{nei} val {{{}}}", vs.join("; "))
        }
        Pred::IsTy { neg, neither, tys } => {
            let n = if *neg { " not" } else { "" };
            let nei = if *neither { " neither" } else { "" };
            let ts: Vec<_> = tys.iter().map(print_ty).collect();
            format!("is{n}{nei} ty {{{}}}", ts.join("; "))
        }
        Pred::Call { callee: Callee::Alg(a), args, neg } => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{} {}({})", if *neg { "fails" } else { "sat" }, tok_alg_ref(a), as_.join(", "))
        }
        Pred::Call { callee: Callee::Prim(pr), args, neg } => {
            let as_: Vec<_> = args.iter().map(print_expr).collect();
            format!("{} {}({})", if *neg { "fails" } else { "sat" }, tok_prim(pr), as_.join(", "))
        }
    }
}

pub fn print_cond(c: &Cond) -> String {
    match c {
        Cond::Preds(e, p, rest) => {
            let mut out = format!("{} {}", print_expr(e), print_pred(p));
            for (j, pr) in rest {
                let js = match j { Conj::And => "and", Conj::Or => "or" };
                write!(out, " {js} {}", print_pred(pr)).unwrap();
            }
            out
        }
        Cond::Rel(op, a, b) => format!("{} {} {}", print_expr(a), rel_sym(*op), print_expr(b)),
        Cond::And(cs) => {
            if cs.is_empty() {
                "all []".into()
            } else {
                let xs: Vec<_> = cs
                    .iter()
                    .map(|c| match c {
                        Cond::And(_) | Cond::Or(_) => format!("{{{}}}", print_cond(c)),
                        _ => print_cond(c),
                    })
                    .collect();
                xs.join(" and ")
            }
        }
        Cond::Or(cs) => {
            if cs.is_empty() {
                "any []".into()
            } else {
                let xs: Vec<_> = cs
                    .iter()
                    .map(|c| match c {
                        Cond::Or(_) => format!("{{{}}}", print_cond(c)),
                        _ => print_cond(c),
                    })
                    .collect();
                xs.join(" or ")
            }
        }
        Cond::Paren(c) => format!("({})", print_cond(c)),
        Cond::Alg(a) => format!("alg {}", tok_alg_ref(a)),
        Cond::Expr(e) => format!("expr {}", print_expr(e)),
        Cond::Pass(k) => format!("pass {}", esc_str(k)),
    }
}

pub fn print_ty(t: &TyExpr) -> String {
    match t {
        TyExpr::Union(ts) => {
            let xs: Vec<_> = ts
                .iter()
                .map(|x| match x {
                    TyExpr::Union(_) => format!("{{{}}}", print_ty(x)),
                    _ => print_ty(x),
                })
                .collect();
            xs.join(" | ")
        }
        _ => print_ty2(t),
    }
}

fn print_ty2(t: &TyExpr) -> String {
    match t {
        TyExpr::Sort { mods, sort } => {
            if mods.is_empty() {
                tok_ident(sort)
            } else {
                let ms: Vec<_> = mods.iter().map(|m| tok_ident(m)).collect();
                format!("sort [{}] {}", ms.join(", "), tok_ident(sort))
            }
        }
        TyExpr::ListOf(inner) => format!("list<{}>", print_ty(inner)),
        TyExpr::SeqOf(inner) => format!("seq<{}>", print_ty(inner)),
        TyExpr::ButNot(a, b) => format!("butnot({}, {})", print_ty(a), print_ty(b)),
        TyExpr::Doc(s) => format!("doc {}", esc_str(s)),
        TyExpr::Completion(None) => "completion<none>".into(),
        TyExpr::Completion(Some(inner)) => format!("completion<{}>", print_ty(inner)),
        TyExpr::Interval(base, lo, hi) => {
            let bs = match base.as_ref() {
                TyExpr::Union(_) => format!("{{{}}}", print_ty(base)),
                _ => print_ty2(base),
            };
            format!("interval {bs} [{}, {}]", print_expr(lo), print_expr(hi))
        }
        TyExpr::Value(e) => format!("val({})", print_expr(e)),
        TyExpr::Var(x) => format!("var {}", tok_ident(x)),
        TyExpr::Nt(n) => format!("|{}|", tok_ident(n)),
        TyExpr::Record(fs) => {
            let xs: Vec<_> = fs
                .iter()
                .map(|(f, v)| format!("{}: {}", tok_field(f), print_ty(v)))
                .collect();
            if xs.is_empty() {
                "record {}".into()
            } else {
                format!("record {{ {} }}", xs.join(", "))
            }
        }
        TyExpr::That(base, p, rest) => {
            let bs = match base.as_ref() {
                TyExpr::Union(_) | TyExpr::That(..) => format!("{{{}}}", print_ty(base)),
                _ => print_ty2(base),
            };
            let mut out = format!("{bs} that {}", print_pred(p));
            for (j, pr) in rest {
                let js = match j { Conj::And => "and", Conj::Or => "or" };
                write!(out, " {js} {}", print_pred(pr)).unwrap();
            }
            out
        }
        TyExpr::Pred(p) => format!("pred({})", print_pred(p)),
        TyExpr::Union(_) => unreachable!(),
    }
}

fn indent(n: usize) -> String {
    " ".repeat(n)
}

fn print_body(ind: usize, b: &Body) -> String {
    match b {
        Body::Inline(s) => format!("-> {}", print_stmt(ind, s)),
        Body::Block(ns) => {
            let mut out = String::from("{\n");
            for s in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, s)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
    }
}

fn print_arm(ind: usize, a: &Arm) -> String {
    match &a.cond {
        Some(c) => format!("{}else_if {} {}", indent(ind), print_cond(c), print_body(ind, &a.body)),
        None => format!("{}else {}", indent(ind), print_body(ind, &a.body)),
    }
}

pub fn print_stmt(ind: usize, s: &Stmt) -> String {
    match s {
        Stmt::Let(x, e) => format!("let {} = {}", tok_ident(x), print_expr(e)),
        Stmt::Set(Place::Var(x), e) => format!("set var {} = {}", tok_ident(x), print_expr(e)),
        Stmt::Set(Place::Field(o, f), e) => {
            format!("set field {}{} = {}", print_child(5, o), tok_field(f), print_expr(e))
        }
        Stmt::Set(Place::Expr(lhs), e) => {
            format!("set expr {} = {}", print_child(5, lhs), print_expr(e))
        }
        Stmt::Ret(None) => "return".into(),
        Stmt::Ret(Some(e)) => format!("return {}", print_expr(e)),
        Stmt::Perform(e) => format!("perform {}", print_expr(e)),
        Stmt::If(c, bd, arms, els) => {
            let mut out = format!("if {} {}", print_cond(c), print_body(ind, bd));
            for a in arms {
                write!(out, "\n{}", print_arm(ind, a)).unwrap();
            }
            if let Some(a) = els {
                write!(out, "\n{}", print_arm(ind, a)).unwrap();
            }
            out
        }
        Stmt::IfElse(c, s1, s2) => {
            format!("if_else {} {{ {} }} else {{ {} }}", print_cond(c), print_stmt(ind, s1), print_stmt(ind, s2))
        }
        Stmt::Assert(c) => format!("assert {}", print_cond(c)),
        Stmt::AssertAlways(c) => format!("assert! {}", print_cond(c)),
        Stmt::AssertIf(c, d) => format!("assert_if {} then {}", print_cond(c), print_cond(d)),
        Stmt::Unreachable(v) => format!("unreachable {v}"),
        Stmt::ThrowVal(e) => format!("throw {}", print_expr(e)),
        Stmt::Note(t) => format!("note {}", esc_str(t)),
        Stmt::Repeat(ns) => {
            let mut out = String::from("repeat {\n");
            for x in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, x)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
        Stmt::RepeatWhile(c, ns) => {
            let mut out = format!("repeat_while {} {{\n", print_cond(c));
            for x in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, x)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
        Stmt::RepeatUntil(c, ns) => {
            let mut out = format!("repeat_until {} {{\n", print_cond(c));
            for x in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, x)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
        Stmt::ForEach { x, ty, list, rev, body } => {
            let ts = ty.as_ref().map_or_else(String::new, |t| format!(" : {}", print_ty(t)));
            let rs = if *rev { " rev" } else { "" };
            format!("for_each {}{ts}{rs} in {} {}", tok_ident(x), print_expr(list), print_body(ind, body))
        }
        Stmt::ForEachRec { fields, x, list, body } => {
            let fs: Vec<_> = fields.iter().map(|f| tok_field(f)).collect();
            format!("for_each_rec [{}] {} in {} {}", fs.join(", "), tok_ident(x), print_expr(list), print_body(ind, body))
        }
        Stmt::ForRange { x, lo, lo_incl, hi, hi_incl, desc, body } => {
            let lk = if *lo_incl { "incl" } else { "excl" };
            let hk = if *hi_incl { "incl" } else { "excl" };
            let dk = if *desc { " desc" } else { "" };
            format!("for_range {} {lk} {} .. {hk} {}{dk} {}", tok_ident(x), print_expr(lo), print_expr(hi), print_body(ind, body))
        }
        Stmt::ForKeys { x, obj, cond, order, body } => {
            format!("for_keys {} of {} where {} order {order} {}", tok_ident(x), print_expr(obj), print_cond(cond), print_body(ind, body))
        }
        Stmt::ForIndex { x, list, body } => {
            format!("for_index {} of {} {}", tok_ident(x), print_expr(list), print_body(ind, body))
        }
        Stmt::ForChildren { x, body } => format!("for_children {} {}", tok_ident(x), print_body(ind, body)),
        Stmt::ForChildrenOf { x, expr, body } => {
            format!("for_children_of {} in {} {}", tok_ident(x), print_expr(expr), print_body(ind, body))
        }
        Stmt::RepeatN(e, ns) => {
            let mut out = format!("repeat_n {} {{\n", print_expr(e));
            for x in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, x)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
        Stmt::Suspend(e, v) => format!("suspend {} kind {v}", print_expr(e)),
        Stmt::Push(e, v) => format!("push {} kind {v}", print_expr(e)),
        Stmt::Remove(e, v) => format!("remove {} kind {v}", print_expr(e)),
        Stmt::RemoveRestore(e, r) => format!("remove_restore {} with {}", print_expr(e), print_expr(r)),
        Stmt::ResumeTop => "resume_top".into(),
        Stmt::ResumeLet { ctx, val, x } => {
            format!("resume_let {} with {} -> {}", print_expr(ctx), print_expr(val), tok_ident(x))
        }
        Stmt::Resume(e, v) => format!("resume {} with {}", print_expr(e), print_expr(v)),
        Stmt::SetCodeState(e, f) => format!("set_code_state {} to {}", print_expr(e), print_expr(f)),
        Stmt::Block(ns) => {
            let mut out = String::from("block {\n");
            for x in ns {
                writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, x)).unwrap();
            }
            write!(out, "{}}}", indent(ind)).unwrap();
            out
        }
    }
}

fn alg_kind_str(k: AlgKind) -> &'static str {
    match k {
        AlgKind::Ao => "ao",
        AlgKind::Sdo => "sdo",
        AlgKind::Builtin => "builtin",
        AlgKind::InternalMethod => "internal_method",
        AlgKind::ConcreteMethod => "concrete_method",
        AlgKind::NumericMethod => "numeric_method",
        AlgKind::HostDefined => "host_defined",
        AlgKind::ImplDefined => "impl_defined",
        AlgKind::Untyped => "untyped",
    }
}

fn clo_kind_str(k: CloKind) -> &'static str {
    match k {
        CloKind::Abstract => "abstract",
        CloKind::Job => "job",
        CloKind::Matcher => "matcher",
        CloKind::MatcherContinuation => "matcher_continuation",
        CloKind::ReadModifyWrite => "read_modify_write",
    }
}

pub fn print_header(h: &Header) -> String {
    let r = h
        .recv
        .as_ref()
        .map_or_else(String::new, |(x, t)| format!(" recv {} : {}", tok_ident(x), print_ty(t)));
    let ps: Vec<_> = h
        .params
        .iter()
        .map(|p| {
            let t = p.ty.as_ref().map_or_else(String::new, |ty| format!(" : {}", print_ty(ty)));
            let o = if p.optional { " opt" } else { "" };
            let rs = if p.rest { " rest" } else { "" };
            format!("{}{t}{o}{rs}", tok_ident(&p.x))
        })
        .collect();
    let ret = h.ret.as_ref().map_or_else(String::new, |t| format!(" -> {}", print_ty(t)));
    format!("kind {}{r} params [{}]{ret}", alg_kind_str(h.kind), ps.join(", "))
}

pub fn print_sdo_header(h: &SdoHeader) -> String {
    let r = h
        .recv
        .as_ref()
        .map_or_else(String::new, |(s, t)| format!(" recv slot {s} : {}", print_ty(t)));
    let ps: Vec<_> = h
        .params
        .iter()
        .map(|p| {
            let t = p.ty.as_ref().map_or_else(String::new, |ty| format!(" : {}", print_ty(ty)));
            let o = if p.optional { " opt" } else { "" };
            let rs = if p.rest { " rest" } else { "" };
            format!("slot {}{t}{o}{rs}", p.slot)
        })
        .collect();
    let ret = h.ret.as_ref().map_or_else(String::new, |t| format!(" -> {}", print_ty(t)));
    format!("kind {}{r} params [{}]{ret}", alg_kind_str(h.kind), ps.join(", "))
}

pub fn print_closure(ind: usize, c: &CloLit) -> String {
    let p_str = match &c.params {
        None => "none".into(),
        Some(ps) => format!("[{}]", ps.iter().map(|s| tok_ident(s)).collect::<Vec<_>>().join(", ")),
    };
    let c_str = c.captures.iter().map(|s| tok_ident(s)).collect::<Vec<_>>().join(", ");
    let f_str = c.frame.as_ref().map_or_else(String::new, |(a, b, d)| {
        format!(" frame ({}, {}, {})", tok_ident(a), tok_ident(b), tok_ident(d))
    });
    let atom = if c.atomic { " atomic" } else { "" };
    let mut out = format!(
        "{}closure {}{atom} params {p_str} captures [{c_str}]{f_str} {{\n",
        indent(ind),
        clo_kind_str(c.kind)
    );
    for s in &c.body {
        writeln!(out, "{}{}", indent(ind + 2), print_stmt(ind + 2, s)).unwrap();
    }
    writeln!(out, "{}}}", indent(ind)).unwrap();
    out
}

pub fn print_alg_def(a: &AlgDef) -> String {
    let vs: Vec<_> = a.vars.iter().map(|s| tok_ident(s)).collect();
    let mut out = format!(
        "def {} {} ({}) vars [{}] {{\n",
        tok_alg_ref(&a.id),
        esc_str(&a.name),
        print_header(&a.header),
        vs.join(", ")
    );
    for s in &a.body {
        writeln!(out, "  {}", print_stmt(2, s)).unwrap();
    }
    for c in &a.closures {
        out.push_str(&print_closure(2, c));
    }
    out.push_str("}\n\n");
    out
}

pub fn print_sdo_row(r: &SdoRowDef) -> String {
    let fstr = match r.form { RowForm::Alg => "alg", RowForm::Equation => "equation" };
    let ann = if r.annex { " annex" } else { "" };
    let ps: Vec<_> = r.prods.iter().map(|s| tok_prod(s)).collect();
    let ks: Vec<_> = r.keys.iter().map(|s| esc_str(s)).collect();
    let vs: Vec<_> = r.vars.iter().map(|s| tok_ident(s)).collect();
    let mut out = format!(
        "sdo_row {} {} form {fstr}{ann} {{\n  prods [{}]\n  keys [{}]\n  vars [{}]\n  steps {{\n",
        tok_alg_ref(&r.id),
        tok_ident(&r.sdo),
        ps.join(", "),
        ks.join(", "),
        vs.join(", ")
    );
    for s in &r.steps {
        writeln!(out, "    {}", print_stmt(4, s)).unwrap();
    }
    out.push_str("  }\n");
    for c in &r.closures {
        out.push_str(&print_closure(2, c));
    }
    out.push_str("}\n\n");
    out
}

fn print_terminal(t: &Terminal) -> String {
    match t {
        Terminal::Text { text, alt: false } => esc_str(text),
        Terminal::Text { text, alt: true } => format!("alt {}", esc_str(text)),
        Terminal::Cp(c) => format!("cp {c}"),
    }
}

fn print_g_sym(s: &GrammarSym) -> String {
    match s {
        GrammarSym::T(t) => print_terminal(t),
        GrammarSym::Nt(n, args) => {
            if args.is_empty() {
                format!("|{}|", tok_ident(n))
            } else {
                let xs: Vec<_> = args
                    .iter()
                    .map(|a| {
                        let sg = match a.sign {
                            ParamSign::Plus => "+",
                            ParamSign::Tilde => "~",
                            ParamSign::Quest => "?",
                        };
                        format!("{sg}{}", tok_ident(&a.param))
                    })
                    .collect();
                format!("|{}[{}]|", tok_ident(n), xs.join(", "))
            }
        }
    }
}

fn print_look_item(i: &LookItem) -> String {
    match i {
        LookItem::T(t) => print_terminal(t),
        LookItem::NoLT => "noLT".into(),
    }
}

fn print_g_item(i: &GrammarItem) -> String {
    match i {
        GrammarItem::Sym(s, opt) => format!("{}{}", print_g_sym(s), if *opt { "?" } else { "" }),
        GrammarItem::Lookahead(Lookahead::Eq(xs)) => {
            let s: Vec<_> = xs.iter().map(print_look_item).collect();
            format!("[lookahead == {}]", s.join(" "))
        }
        GrammarItem::Lookahead(Lookahead::Ne(xs)) => {
            let s: Vec<_> = xs.iter().map(print_look_item).collect();
            format!("[lookahead != {}]", s.join(" "))
        }
        GrammarItem::Lookahead(Lookahead::Mem(ss)) => {
            let s: Vec<_> = ss
                .iter()
                .map(|xs| xs.iter().map(print_look_item).collect::<Vec<_>>().join(" "))
                .collect();
            format!("[lookahead in {{ {} }}]", s.join(", "))
        }
        GrammarItem::Lookahead(Lookahead::NotMem(ss)) => {
            let s: Vec<_> = ss
                .iter()
                .map(|xs| xs.iter().map(print_look_item).collect::<Vec<_>>().join(" "))
                .collect();
            format!("[lookahead not_in {{ {} }}]", s.join(", "))
        }
        GrammarItem::Lookahead(Lookahead::NotMemNt(nt)) => format!("[lookahead not_in |{}|]", tok_ident(nt)),
        GrammarItem::NoLT => "[noLT]".into(),
        GrammarItem::Empty => "[empty]".into(),
        GrammarItem::ButNot(s, Exclusion::Sym(ex)) => format!("{} butnot {}", print_g_sym(s), print_g_sym(ex)),
        GrammarItem::ButNot(s, Exclusion::OneOf { syms, or_sep }) => {
            let sp = if *or_sep { "or" } else { "plain" };
            let xs: Vec<_> = syms.iter().map(print_g_sym).collect();
            format!("{} butnot one_of {sp} [{}]", print_g_sym(s), xs.join(", "))
        }
        GrammarItem::OnlyIf(p) => format!("[onlyIf {p}]"),
        GrammarItem::Phrase(p) => format!("> {p}"),
    }
}

pub fn print_rule(r: &Rule) -> String {
    let ps: Vec<_> = r.params.iter().map(|s| tok_ident(s)).collect();
    let col = match r.colons {
        Colons::One => ":",
        Colons::Two => "::",
        Colons::Three => ":::",
    };
    let mut out = format!("rule {} |{}| [{}] {col} ", r.grammar.as_str(), tok_ident(&r.lhs), ps.join(", "));
    match &r.body {
        RuleBody::Alts(alts) => {
            out.push_str("{\n");
            for a in alts {
                let g = if a.guard.is_empty() {
                    String::new()
                } else {
                    format!("{} ", print_param_args(&a.guard))
                };
                let rhs: Vec<_> = a.rhs.iter().map(print_g_item).collect();
                let lbl = a.label.as_ref().map_or_else(String::new, |l| format!(" #label {}", esc_str(l)));
                writeln!(out, "  | {g}{}{lbl}", rhs.join(" ")).unwrap();
            }
            out.push_str("}\n\n");
        }
        RuleBody::OneOf(rows) => {
            out.push_str("one_of {\n");
            for row in rows {
                let xs: Vec<_> = row.iter().map(print_terminal).collect();
                writeln!(out, "  row [{}]", xs.join(", ")).unwrap();
            }
            out.push_str("}\n\n");
        }
    }
    out
}

fn print_early_sent(ind: usize, s: &EarlySent) -> String {
    match s {
        EarlySent::SyntaxError { early, cond, unless } => {
            let hd = if *early { "early_syntax_error" } else { "syntax_error" };
            let u = match unless {
                None => String::new(),
                Some((uf, d)) => {
                    let ufs = match uf {
                        UnlessForm::Plain => "plain",
                        UnlessForm::Comma => "comma",
                        UnlessForm::Optional => "opt",
                    };
                    format!(" unless {ufs} {}", print_cond(d))
                }
            };
            format!("{}{hd} {}{u}\n", indent(ind), print_cond(cond))
        }
        EarlySent::SyntaxErrorIns(a, b) => format!("{}syntax_error_ins {} & {}\n", indent(ind), print_cond(a), print_cond(b)),
        EarlySent::MustCover(e, t) => format!("{}must_cover {} : {}\n", indent(ind), print_expr(e), print_ty(t)),
        EarlySent::RulesApplied(ps, raw) => {
            let ks: Vec<_> = ps.iter().map(|s| tok_prod(s)).collect();
            format!("{}rules_applied [{}] {}\n", indent(ind), ks.join(", "), esc_str(raw))
        }
        EarlySent::IfInline(c, inner) => {
            let s = print_early_sent(0, inner);
            let s = s.strip_suffix('\n').unwrap_or(&s);
            format!("{}if_inline {} -> {s}\n", indent(ind), print_cond(c))
        }
        EarlySent::Info(st) => format!("{}info {{ {} }}\n", indent(ind), print_stmt(ind, st)),
        EarlySent::NotApplied(c, st) => format!("{}not_applied {} {{ {} }}\n", indent(ind), print_cond(c), print_stmt(ind, st)),
        EarlySent::ForEachIn { x, ty, list, cond, stmt } => format!(
            "{}for_each_in {} : {} in {} where {} {{ {} }}\n",
            indent(ind),
            tok_ident(x),
            print_ty(ty),
            print_expr(list),
            print_cond(cond),
            print_stmt(ind, stmt)
        ),
        EarlySent::Stmt(st) => format!("{}stmt {{ {} }}\n", indent(ind), print_stmt(ind, st)),
    }
}

pub fn print_early_row(r: &EarlyRow) -> String {
    let ps: Vec<_> = r.prods.iter().map(|s| tok_prod(s)).collect();
    let ks: Vec<_> = r.keys.iter().map(|s| esc_str(s)).collect();
    let vs: Vec<_> = r.vars.iter().map(|s| tok_ident(s)).collect();
    let m = if r.modifies { " modifies" } else { "" };
    let mut out = format!(
        "early {} {}{m} {{\n  prods [{}]\n  keys [{}]\n  vars [{}]\n  sentences {{\n",
        tok_alg_ref(&r.id),
        tok_ident(&r.sdo),
        ps.join(", "),
        ks.join(", "),
        vs.join(", ")
    );
    for s in &r.sentences {
        out.push_str(&print_early_sent(4, s));
    }
    out.push_str("  }\n}\n\n");
    out
}

fn print_tty(t: &TTy) -> String {
    match t {
        TTy::Ty(ty) => print_ty(ty),
        TTy::Records(fs) => {
            let xs: Vec<_> = fs.iter().map(|(f, ty)| format!("{}: {}", tok_field(f), print_ty(ty))).collect();
            format!("records [{}]", xs.join(", "))
        }
    }
}

fn print_sig(g: &Sig) -> String {
    let hd = match g.kind {
        SigKind::Field => format!("field {}", tok_field(&g.name)),
        SigKind::Method => format!("method {}", tok_ident(&g.name)),
    };
    let ps: Vec<_> = g
        .params
        .iter()
        .map(|p| format!("{}: {}{}", tok_ident(&p.x), print_tty(&p.ty), if p.optional { " opt" } else { "" }))
        .collect();
    format!("{hd} ({}) -> {}", ps.join(", "), print_tty(&g.ret))
}

fn print_cell_body(b: &CellBody) -> String {
    match b {
        CellBody::Field(f) => format!("field {}", tok_field(f)),
        CellBody::Ty(t) => format!("ty ({})", print_tty(t)),
        CellBody::Sig(g) => format!("sig ({})", print_sig(g)),
        CellBody::Stmt(st) => format!("stmt {{ {} }}", print_stmt(0, st)),
        CellBody::Alg(a) => format!("alg {}", tok_alg_ref(a)),
        CellBody::Expr(e) => format!("expr ({})", print_expr(e)),
        CellBody::Op(c) => format!("op {}", tok_clause(c)),
        CellBody::Component(f) => format!("component {}", tok_field(f)),
        CellBody::Name(s) => format!("name {}", esc_str(s)),
        CellBody::Lines(cs) => {
            let xs: Vec<_> = cs.iter().map(print_cell_body).collect();
            format!("lines [{}]", xs.join(", "))
        }
        CellBody::Dfn(c) => format!("dfn ({})", print_cell_body(c)),
        CellBody::Code(c) => format!("code ({})", print_cell_body(c)),
        CellBody::Link(h, c) => format!("link {} ({})", esc_str(h), print_cell_body(c)),
        CellBody::Raw(s) => format!("raw {}", esc_str(s)),
        CellBody::Text(s) => format!("text {}", esc_str(s)),
    }
}

pub fn print_table(t: &TableDef) -> String {
    let Some(b) = &t.body else {
        return format!("table {} retired\n\n", tok_table(&t.name));
    };
    let k = match b.kind {
        TableKind::Fields => "fields",
        TableKind::Slots => "slots",
        TableKind::InternalMethods => "internal_methods",
        TableKind::AbstractMethods => "abstract_methods",
        TableKind::Components => "components",
        TableKind::Properties => "properties",
        TableKind::Intrinsics => "intrinsics",
        TableKind::Conversion => "conversion",
        TableKind::Data => "data",
    };
    let cap = b.caption.as_ref().map_or_else(String::new, |s| format!("  caption {}\n", esc_str(s)));
    let sch = b.schema.as_ref().map_or_else(String::new, |(s, hd)| format!("  schema ({}, {hd})\n", esc_str(s)));
    let vs: Vec<_> = b.vars.iter().map(|s| tok_ident(s)).collect();
    let mut out = format!(
        "table {} {}#{} {{\n  kind {k}\n  thead {}\n{cap}{sch}  vars [{}]\n  rows [\n",
        tok_table(&t.name),
        tok_clause(&b.clause),
        b.idx,
        b.thead,
        vs.join(", ")
    );
    for r in &b.rows {
        out.push_str("    row [\n");
        for c in r {
            let sp = if c.rowspan == 1 && c.colspan == 1 {
                String::new()
            } else {
                format!(" span ({}, {})", c.rowspan, c.colspan)
            };
            writeln!(out, "      cell{sp} {{ {} }}", print_cell_body(&c.body)).unwrap();
        }
        out.push_str("    ]\n");
    }
    out.push_str("  ]\n}\n\n");
    out
}

fn print_rkey(k: &RKey) -> String {
    match k {
        RKey::Str(s) => format!("str {}", esc_str(s)),
        RKey::Sym(s) => format!("sym {}", esc_str(s)),
    }
}

fn print_rval(v: &RVal) -> String {
    match v {
        RVal::Undefined => "undefined".into(),
        RVal::Null => "null".into(),
        RVal::Bool(b) => b.to_string(),
        RVal::Str(s) => esc_str(s),
        RVal::Number(bits) => format!("number {bits}"),
        RVal::Obj(i) => format!("obj {i}"),
        RVal::Sym(d) => format!("sym {}", esc_str(d)),
        RVal::GlobalThis => "global_this".into(),
        RVal::Created(a) => format!("created {}", tok_alg_ref(a)),
    }
}

fn print_rattrs(a: RAttrs) -> String {
    format!("{{ w: {}, e: {}, c: {} }}", a.w, a.e, a.c)
}

fn print_rprop(p: &RProp) -> String {
    let vs = match &p.val {
        RPVal::Data(v) => format!("data ({})", print_rval(v)),
        RPVal::Accessor(g, s) => {
            let opt = |o: Option<usize>| o.map_or_else(|| "none".into(), |n| format!("some {n}"));
            format!("accessor ({}, {})", opt(*g), opt(*s))
        }
    };
    let flags = format!(
        "{}{}{}",
        if p.annex_b { " annexB" } else { "" },
        if p.opt { " opt" } else { "" },
        if p.omittable { " omittable" } else { "" }
    );
    format!(
        "      prop {} = {vs} attrs {} {}{flags}\n",
        print_rkey(&p.key),
        print_rattrs(p.attrs),
        tok_clause(&p.clause)
    )
}

pub fn print_robj(o: &RObj) -> String {
    let ns: Vec<_> = o.names.iter().map(|s| tok_field(s)).collect();
    let ks: Vec<_> = o.keys.iter().map(|s| tok_field(s)).collect();
    let kstr = match &o.kind {
        RKind::Ordinary => "ordinary".into(),
        RKind::Exotic(c) => format!("exotic {}", tok_clause(c)),
    };
    let proto = o.proto.map_or_else(|| "none".into(), |p| format!("some {p}"));
    let slots: Vec<_> = o
        .slots
        .iter()
        .map(|(f, v)| format!("({}, {})", tok_field(f), print_rval(v)))
        .collect();
    let fstr = match &o.fn_ {
        None => String::new(),
        Some(f) => {
            let astr = f.alg.as_ref().map_or_else(|| "none".into(), |a| format!("some {}", tok_alg_ref(a)));
            let pstr = f.pfx.as_ref().map_or_else(|| "none".into(), |p| format!("some {}", esc_str(p)));
            format!(
                "  fn {{ alg {astr} len {} name {} pfx {pstr} ctor {} async {} len_attrs {} name_attrs {} }}\n",
                f.len,
                print_rkey(&f.name),
                f.ctor,
                f.is_async,
                print_rattrs(f.len_attrs),
                print_rattrs(f.name_attrs)
            )
        }
    };
    let flags = format!("{}{}", if o.annex_b { " annexB" } else { "" }, if o.opt { " opt" } else { "" });
    let mut out = format!(
        "obj {} {} {}{flags} {{\n  names [{}]\n  keys [{}]\n  kind {kstr}\n  proto {proto} extensible {}\n  slots [{}]\n{fstr}",
        o.idx,
        esc_str(&o.path),
        tok_clause(&o.clause),
        ns.join(", "),
        ks.join(", "),
        o.extensible,
        slots.join(", ")
    );
    if o.props.is_empty() {
        out.push_str("  props []\n}\n\n");
    } else {
        out.push_str("  props [\n");
        for p in &o.props {
            out.push_str(&print_rprop(p));
        }
        out.push_str("  ]\n}\n\n");
    }
    out
}

pub fn print_clause_props(cp: &ClauseProps) -> String {
    let mut out = format!("clause_props {} [\n", tok_clause(&cp.clause));
    for p in &cp.props {
        out.push_str(&print_rprop(p));
    }
    out.push_str("]\n\n");
    out
}

fn print_sort_test(t: &SortTest) -> String {
    match t {
        SortTest::None => "none".into(),
        SortTest::Alg(a) => format!("alg {}", tok_alg_ref(a)),
        SortTest::Prim { name, args, neg } => {
            let as_: Vec<_> = args
                .iter()
                .map(|a| match a {
                    SortTestArg::Subject => "subject".into(),
                    SortTestArg::Enum(e) => tok_enum(e),
                })
                .collect();
            format!("{}{}({})", if *neg { "not " } else { "" }, tok_prim(name), as_.join(", "))
        }
    }
}

pub fn print_decl(d: &Decl) -> String {
    match d {
        Decl::Clause { id, op: None } => format!("clause {}\n", tok_clause(id)),
        Decl::Clause { id, op: Some(op) } => format!("clause {} op {}\n", tok_clause(id), esc_str(op)),
        Decl::Field(f) => format!("field {}\n", tok_field(f)),
        Decl::Enum(e) => format!("enum {}\n", tok_enum(e)),
        Decl::Method(m) => format!("method {}\n", tok_ident(m)),
        Decl::ExternDef { name, sig: None, meaning: None } => format!("extern def {}\n", tok_prim(name)),
        Decl::ExternDef { name, sig, meaning } => format!(
            "extern def {} {{ sig {} meaning {} }}\n",
            tok_prim(name),
            esc_str(sig.as_deref().unwrap_or("")),
            esc_str(meaning.as_deref().unwrap_or(""))
        ),
        Decl::Syntax { name, def: None } => format!("syntax {}\n", tok_ident(name)),
        Decl::Syntax { name, def: Some(sd) } => {
            if sd.super_sorts.is_empty() && !sd.record && sd.test == SortTest::None {
                format!("syntax {} defined {{}}\n", tok_ident(name))
            } else {
                let su: Vec<_> = sd.super_sorts.iter().map(|s| tok_ident(s)).collect();
                format!(
                    "syntax {} defined {{ super [{}] record {} test {} }}\n",
                    tok_ident(name),
                    su.join(", "),
                    sd.record,
                    print_sort_test(&sd.test)
                )
            }
        }
        Decl::Sdo { name, header: None, default: None } => format!("sdo {}\n", tok_ident(name)),
        Decl::Sdo { name, header, default } => {
            let h = header.as_ref().map_or_else(String::new, |hd| format!(" header ({})", print_sdo_header(hd)));
            let d = default.as_ref().map_or_else(String::new, |a| format!(" default {}", tok_alg_ref(a)));
            format!("sdo {} {{{h}{d} }}\n", tok_ident(name))
        }
        Decl::CheckedJobs(cs) => {
            let xs: Vec<_> = cs.iter().map(|c| tok_clause(c)).collect();
            format!("checked_jobs [{}]\n", xs.join(", "))
        }
        Decl::SortAlias { from, to } => format!("sort_alias {} -> {}\n", esc_str(from), tok_ident(to)),
        Decl::GrammarAlt { nt, items } => {
            let xs: Vec<_> = items
                .iter()
                .map(|i| match i {
                    GrammarAltItem::Text(x) => esc_str(x),
                    GrammarAltItem::Cp(n) => format!("cp {}", esc_str(n)),
                })
                .collect();
            format!("grammar_alt |{}| = [{}]\n", tok_ident(nt), xs.join(", "))
        }
        Decl::ClauseProds { clause, prods } => {
            let ps: Vec<_> = prods.iter().map(|s| tok_prod(s)).collect();
            format!("clause_prods {} = [{}]\n", tok_clause(clause), ps.join(", "))
        }
    }
}

fn item_group_tag(item: &TopItem) -> usize {
    match item {
        TopItem::Decl(Decl::Clause { .. }) => 1,
        TopItem::Decl(Decl::Field(_)) => 2,
        TopItem::Decl(Decl::Enum(_)) => 3,
        TopItem::Decl(Decl::Method(_)) => 4,
        TopItem::Decl(Decl::ExternDef { .. }) => 5,
        TopItem::Decl(Decl::Syntax { .. }) => 6,
        TopItem::Decl(Decl::Sdo { .. }) => 7,
        TopItem::Decl(Decl::CheckedJobs(_)) => 8,
        TopItem::Decl(Decl::SortAlias { .. }) => 9,
        TopItem::Decl(Decl::GrammarAlt { .. }) => 10,
        TopItem::Decl(Decl::ClauseProds { .. }) => 11,
        TopItem::Param(_) => 12,
        TopItem::Nt(_) => 13,
        TopItem::Block(_) => 14,
        TopItem::Goal(_) => 15,
        TopItem::Cover(_) => 16,
        TopItem::Semi(_) => 17,
        _ => 0,
    }
}

pub fn print_file(f: &SpecFile) -> String {
    if let [TopItem::SpecModule(m)] = f.items.as_slice() {
        return crate::spec_model::print::print_spec_module(&f.header_comment, m);
    }
    let mut out = String::new();
    if let Some(c) = &f.header_comment {
        out.push_str(c);
        out.push_str("\n\n");
    }
    if let Some(g) = f.grammar_decl {
        writeln!(out, "grammar {}\n", g.as_str()).unwrap();
    }
    let mut prev_tag = None;
    for item in &f.items {
        let tag = item_group_tag(item);
        if tag != 0 {
            if let Some(pt) = prev_tag {
                if pt != tag && pt != 0 {
                    out.push('\n');
                }
            }
        }
        prev_tag = Some(tag);
        match item {
            TopItem::Decl(d) => out.push_str(&print_decl(d)),
            TopItem::Param(p) => writeln!(out, "param {}", tok_ident(p)).unwrap(),
            TopItem::Nt(n) => writeln!(out, "nt {}", tok_ident(n)).unwrap(),
            TopItem::Block(b) => {
                let k = match &b.kind {
                    BlockKind::Main => "main".into(),
                    BlockKind::Supplemental(n) => format!("supplemental |{}|", tok_ident(n)),
                    BlockKind::Overlay { section, mode, cond } => format!("overlay {section} {mode} {cond}"),
                };
                let rs: Vec<_> = b.rules.iter().map(|r| format!("|{}|", tok_ident(r))).collect();
                writeln!(out, "block {} {} {k} [{}]", b.grammar.as_str(), tok_clause(&b.clause), rs.join(", ")).unwrap();
            }
            TopItem::Goal(g) => {
                writeln!(out, "goal |{}| {} src {}", tok_ident(&g.nt), print_param_args(&g.args), g.src).unwrap();
            }
            TopItem::Cover(c) => {
                writeln!(out, "cover {} cover |{}| refined |{}|", tok_prod(&c.context), tok_ident(&c.cover), tok_ident(&c.refined)).unwrap();
            }
            TopItem::Semi(s) => {
                writeln!(out, "semi {} pos {} {}", tok_prod(&s.prod), s.pos, s.kind).unwrap();
            }
            TopItem::Rule(r) => out.push_str(&print_rule(r)),
            TopItem::Early(e) => out.push_str(&print_early_row(e)),
            TopItem::Table(t) => out.push_str(&print_table(t)),
            TopItem::Symbols(syms) => {
                let xs: Vec<_> = syms.iter().map(|s| esc_str(s)).collect();
                writeln!(out, "symbols [{}]\n", xs.join(", ")).unwrap();
            }
            TopItem::RObj(o) => out.push_str(&print_robj(o)),
            TopItem::ClauseProps(cp) => out.push_str(&print_clause_props(cp)),
            TopItem::Def(a) => out.push_str(&print_alg_def(a)),
            TopItem::SdoRow(r) => out.push_str(&print_sdo_row(r)),
            TopItem::SpecModule(m) => out.push_str(&crate::spec_model::print::print_spec_module(&None, m)),
        }
    }
    out
}
