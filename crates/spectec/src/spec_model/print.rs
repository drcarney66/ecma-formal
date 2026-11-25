//! Canonical SpecTec printer and formatter for `spec_model`.

use crate::spec_model::ast::*;
use std::fmt::Write;

fn esc_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn esc_char(ch: char) -> String {
    match ch {
        '\\' => "'\\\\'".into(),
        '\'' => "'\\''".into(),
        '\n' => "'\\n'".into(),
        '\r' => "'\\r'".into(),
        '\t' => "'\\t'".into(),
        c => format!("'{c}'"),
    }
}

fn push_doc(out: &mut String, ind: usize, doc: &Option<String>, bang: bool) {
    let Some(d) = doc else {
        return;
    };
    let pfx = " ".repeat(ind);
    let mark = if bang { "---!" } else { "---" };
    for line in d.split('\n') {
        if line.is_empty() {
            writeln!(out, "{pfx}{mark}").unwrap();
        } else {
            writeln!(out, "{pfx}{mark} {line}").unwrap();
        }
    }
}

fn print_lit(l: &MLit) -> String {
    match l {
        MLit::Int(n) => n.to_string(),
        MLit::Hex(s) => s.clone(),
        MLit::Str(s) => esc_str(s),
        MLit::Char(c) => esc_char(*c),
        MLit::Bool(true) => "true".into(),
        MLit::Bool(false) => "false".into(),
        MLit::Unit => "()".into(),
    }
}

fn print_binder(b: &MBinder) -> String {
    match b {
        MBinder::Explicit { names, ty: Some(t) } => {
            format!("({} : {})", names.join(" "), print_expr(t))
        }
        MBinder::Explicit { names, ty: None } => format!("({})", names.join(" ")),
        MBinder::Implicit { names, ty: Some(t) } => {
            format!("{{{} : {}}}", names.join(" "), print_expr(t))
        }
        MBinder::Implicit { names, ty: None } => format!("{{{}}}", names.join(" ")),
        MBinder::Bare(n) => n.clone(),
        MBinder::In { name, coll } => format!("{name} mem {}", print_expr(coll)),
        MBinder::Rel { name, op, bound } => {
            let sym = match op {
                MRelBoundOp::Lt => "<",
                MRelBoundOp::Le => "<=",
            };
            format!("{name} {sym} {}", print_expr(bound))
        }
    }
}

fn print_binders(bs: &[MBinder]) -> String {
    bs.iter().map(print_binder).collect::<Vec<_>>().join(" ")
}

fn print_pat_prec(p: &MPat, prec: u8) -> String {
    let s = match p {
        MPat::Wild => "_".into(),
        MPat::Dots => "..".into(),
        MPat::Var(v) => v.clone(),
        MPat::Lit(l) => print_lit(l),
        MPat::Tag(t, args) => {
            if args.is_empty() {
                format!(".{t}")
            } else {
                let xs: Vec<_> = args.iter().map(|a| print_pat_prec(a, 0)).collect();
                format!(".{t}({})", xs.join(", "))
            }
        }
        MPat::Ctor(c, args) => {
            if args.is_empty() {
                c.clone()
            } else {
                let xs: Vec<_> = args.iter().map(|a| print_pat_prec(a, 0)).collect();
                format!("{c}({})", xs.join(", "))
            }
        }
        MPat::Tuple(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| print_pat_prec(a, 0)).collect();
            format!("({})", xs.join(", "))
        }
        MPat::AnonCtor(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| print_pat_prec(a, 0)).collect();
            format!("ctor({})", xs.join(", "))
        }
        MPat::List(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| print_pat_prec(a, 0)).collect();
            format!("[{}]", xs.join(", "))
        }
        MPat::Cons(h, t) => {
            let mut l = print_pat_prec(h, 68);
            if matches!(h.as_ref(), MPat::Or(_)) {
                l = format!("({l})");
            }
            let r = print_pat_prec(t, 67);
            let res = format!("{l} :: {r}");
            return if prec > 67 { format!("({res})") } else { res };
        }
        MPat::AddNat(v, n) => {
            let res = format!("{v} + {n}");
            return if prec > 65 { format!("({res})") } else { res };
        }
        MPat::Or(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| print_pat_prec(a, 11)).collect();
            let res = xs.join(" | ");
            return if prec > 10 { format!("({res})") } else { res };
        }
        MPat::As(v, inner) => {
            let inner_s = print_pat_prec(inner, 0);
            format!("{v}@({inner_s})")
        }
    };
    s
}

pub fn print_pat(p: &MPat) -> String {
    print_pat_prec(p, 0)
}

fn expr_prec(e: &MExpr) -> u8 {
    match e {
        MExpr::Ident(_)
        | MExpr::Tag(_)
        | MExpr::Lit(_)
        | MExpr::List(_)
        | MExpr::Tuple(_)
        | MExpr::AnonCtor(_)
        | MExpr::StructLit { .. }
        | MExpr::Do(_)
        | MExpr::Ascribe(..) => 100,
        MExpr::Proj(..) | MExpr::Index(..) | MExpr::IndexOpt(..) | MExpr::Call(..) => 95,
        MExpr::UnOp(MUnOp::Neg | MUnOp::BoolNot | MUnOp::Bind, _) => 75,
        MExpr::UnOp(MUnOp::PropNot, x) => match x.as_ref() {
            MExpr::Quant(..) => 0,
            _ => 40,
        },
        MExpr::BinOp(op, _, _) => bin_prec(*op),
        MExpr::Matches(..) => 50,
        MExpr::Arrow { .. } => 25,
        MExpr::Quant(..)
        | MExpr::Fun(..)
        | MExpr::FunCases(_)
        | MExpr::Let { .. }
        | MExpr::If(..)
        | MExpr::Match(..) => 0,
    }
}

fn bin_prec(op: MBinOp) -> u8 {
    match op {
        MBinOp::Pow => 80,
        MBinOp::Mul | MBinOp::Div | MBinOp::Mod => 70,
        MBinOp::Cons => 67,
        MBinOp::Add | MBinOp::Sub | MBinOp::Append => 65,
        MBinOp::BoolEq
        | MBinOp::BoolNe
        | MBinOp::Lt
        | MBinOp::Le
        | MBinOp::Gt
        | MBinOp::Ge
        | MBinOp::Eq
        | MBinOp::Ne
        | MBinOp::In
        | MBinOp::NotIn => 50,
        MBinOp::BoolAnd | MBinOp::And | MBinOp::Times => 35,
        MBinOp::BoolOr | MBinOp::Or | MBinOp::Sum => 30,
        MBinOp::Iff => 20,
    }
}

fn bin_str(op: MBinOp) -> &'static str {
    match op {
        MBinOp::Pow => "^",
        MBinOp::Mul => "*",
        MBinOp::Div => "/",
        MBinOp::Mod => "%",
        MBinOp::Add => "+",
        MBinOp::Sub => "-",
        MBinOp::Append => "++",
        MBinOp::Cons => "::",
        MBinOp::Times => "times",
        MBinOp::Sum => "sum",
        MBinOp::BoolEq => "==",
        MBinOp::BoolNe => "!=",
        MBinOp::Lt => "<",
        MBinOp::Le => "<=",
        MBinOp::Gt => ">",
        MBinOp::Ge => ">=",
        MBinOp::Eq => "=",
        MBinOp::Ne => "<>",
        MBinOp::In => "mem",
        MBinOp::NotIn => "notmem",
        MBinOp::BoolAnd => "&&",
        MBinOp::BoolOr => "||",
        MBinOp::And => "/\\",
        MBinOp::Or => "\\/",
        MBinOp::Iff => "<=>",
    }
}

fn is_right_assoc(op: MBinOp) -> bool {
    matches!(
        op,
        MBinOp::Pow | MBinOp::Cons | MBinOp::Times | MBinOp::Sum | MBinOp::And | MBinOp::Or
    )
}

fn wrap_prec(e: &MExpr, min: u8, s: String) -> String {
    if expr_prec(e) < min {
        format!("({s})")
    } else {
        s
    }
}

fn print_fun_param(p: &MFunParam) -> String {
    match p {
        MFunParam::Pat(pat) => match pat {
            MPat::Var(_) | MPat::Wild | MPat::Tuple(_) | MPat::AnonCtor(_) | MPat::List(_) => {
                print_pat(pat)
            }
            _ => format!("({})", print_pat(pat)),
        },
        MFunParam::Explicit { names, ty } => format!("({} : {})", names.join(" "), print_expr(ty)),
        MFunParam::Implicit { names, ty: Some(t) } => {
            format!("{{{} : {}}}", names.join(" "), print_expr(t))
        }
        MFunParam::Implicit { names, ty: None } => format!("{{{}}}", names.join(" ")),
    }
}

fn print_arm(arm: &MMatchArm, ind: usize) -> String {
    let pfx = " ".repeat(ind);
    let alts: Vec<_> = arm
        .alts
        .iter()
        .map(|row| row.iter().map(print_pat).collect::<Vec<_>>().join(", "))
        .collect();
    format!("{pfx}| {} => {}", alts.join(" | "), print_expr_ind(&arm.rhs, ind + 2))
}

fn print_do_stmt(st: &MDoStmt, ind: usize) -> String {
    let pfx = " ".repeat(ind);
    match st {
        MDoStmt::LetBind { pat, ty, val } => {
            let tys = ty
                .as_ref()
                .map(|t| format!(" : {}", print_expr_ind(t, ind)))
                .unwrap_or_default();
            format!("{pfx}let {}{tys} <- {};", print_pat(pat), print_expr_ind(val, ind))
        }
        MDoStmt::LetPure { pat, ty, val } => {
            let tys = ty
                .as_ref()
                .map(|t| format!(" : {}", print_expr_ind(t, ind)))
                .unwrap_or_default();
            format!("{pfx}let {}{tys} := {};", print_pat(pat), print_expr_ind(val, ind))
        }
        MDoStmt::Return(e) => format!("{pfx}return {};", print_expr_ind(e, ind)),
        MDoStmt::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut out = format!("{pfx}if {} then {{\n", print_expr_ind(cond, ind));
            for s in then_branch {
                writeln!(out, "{}", print_do_stmt(s, ind + 2)).unwrap();
            }
            write!(out, "{pfx}}}").unwrap();
            if let Some(eb) = else_branch {
                writeln!(out, " else {{").unwrap();
                for s in eb {
                    writeln!(out, "{}", print_do_stmt(s, ind + 2)).unwrap();
                }
                write!(out, "{pfx}}}").unwrap();
            }
            out.push(';');
            out
        }
        MDoStmt::Expr(e) => format!("{pfx}{};", print_expr_ind(e, ind)),
    }
}

pub fn print_expr(e: &MExpr) -> String {
    print_expr_ind(e, 0)
}

fn print_expr_ind(e: &MExpr, ind: usize) -> String {
    match e {
        MExpr::Ident(s) => s.clone(),
        MExpr::Tag(t) => format!(".{t}"),
        MExpr::Lit(l) => print_lit(l),
        MExpr::Proj(base, f) => {
            let b = wrap_prec(base, 95, print_expr_ind(base, ind));
            format!("{b}.{f}")
        }
        MExpr::Call(callee, args) => {
            let c = wrap_prec(callee, 95, print_expr_ind(callee, ind));
            let xs: Vec<_> = args
                .iter()
                .map(|a| match a {
                    MArg::Pos(x) => print_expr_ind(x, ind),
                    MArg::Named(k, x) => format!("{k} := {}", print_expr_ind(x, ind)),
                })
                .collect();
            format!("{c}({})", xs.join(", "))
        }
        MExpr::Index(base, idx) => {
            let b = wrap_prec(base, 95, print_expr_ind(base, ind));
            format!("{b}[{}]", print_expr_ind(idx, ind))
        }
        MExpr::IndexOpt(base, idx) => {
            let b = wrap_prec(base, 95, print_expr_ind(base, ind));
            format!("{b}[{}]?", print_expr_ind(idx, ind))
        }
        MExpr::List(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| print_expr_ind(x, ind)).collect();
            format!("[{}]", ps.join(", "))
        }
        MExpr::Tuple(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| print_expr_ind(x, ind)).collect();
            format!("({})", ps.join(", "))
        }
        MExpr::AnonCtor(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| print_expr_ind(x, ind)).collect();
            format!("ctor({})", ps.join(", "))
        }
        MExpr::StructLit { base, fields } => {
            let b = base
                .as_ref()
                .map(|x| format!("{} with ", print_expr_ind(x, ind)))
                .unwrap_or_default();
            let fs: Vec<_> = fields
                .iter()
                .map(|(k, ov)| match ov {
                    Some(v) => format!("{k} := {}", print_expr_ind(v, ind)),
                    None => k.clone(),
                })
                .collect();
            if b.is_empty() && fs.is_empty() {
                "{}".into()
            } else {
                format!("{{ {b}{} }}", fs.join(", "))
            }
        }
        MExpr::UnOp(MUnOp::Neg, x) => {
            let s = wrap_prec(x, 76, print_expr_ind(x, ind));
            format!("-{s}")
        }
        MExpr::UnOp(MUnOp::BoolNot, x) => {
            let s = wrap_prec(x, 76, print_expr_ind(x, ind));
            format!("!{s}")
        }
        MExpr::UnOp(MUnOp::Bind, x) => {
            let s = wrap_prec(x, 76, print_expr_ind(x, ind));
            format!("<- {s}")
        }
        MExpr::UnOp(MUnOp::PropNot, x) => match x.as_ref() {
            MExpr::Quant(..) => format!("not {}", print_expr_ind(x, ind)),
            _ => {
                let s = wrap_prec(x, 41, print_expr_ind(x, ind));
                format!("not {s}")
            }
        },
        MExpr::BinOp(op, a, b) => {
            let p = bin_prec(*op);
            let lmin = if is_right_assoc(*op) { p + 1 } else { p };
            let rmin = if matches!(b.as_ref(), MExpr::Quant(..) | MExpr::Let { .. } | MExpr::If(..) | MExpr::Fun(..) | MExpr::FunCases(_) | MExpr::Match(..))
                && matches!(op, MBinOp::Eq | MBinOp::Ne | MBinOp::And | MBinOp::Or | MBinOp::Iff)
            {
                0
            } else if matches!(b.as_ref(), MExpr::UnOp(MUnOp::PropNot, _))
                && matches!(op, MBinOp::And | MBinOp::Or | MBinOp::Iff)
            {
                0
            } else if is_right_assoc(*op) {
                p
            } else {
                p + 1
            };
            let ls = wrap_prec(a, lmin, print_expr_ind(a, ind));
            let rs = wrap_prec(b, rmin, print_expr_ind(b, ind));
            format!("{ls} {} {rs}", bin_str(*op))
        }
        MExpr::Arrow { binder, dom, cod } => {
            let lhs = match (binder, dom) {
                (Some(b), _) => print_binder(b),
                (None, Some(d)) => wrap_prec(d, 26, print_expr_ind(d, ind)),
                (None, None) => "_".into(),
            };
            let cod_min = if matches!(cod.as_ref(), MExpr::UnOp(MUnOp::PropNot, _)) {
                0
            } else {
                25
            };
            let rhs = wrap_prec(cod, cod_min, print_expr_ind(cod, ind));
            format!("{lhs} -> {rhs}")
        }
        MExpr::Quant(q, bs, body) => {
            let kw = match q {
                MQuant::Forall => "forall",
                MQuant::Exists => "exists",
            };
            format!("{kw} {}, {}", print_binders(bs), print_expr_ind(body, ind))
        }
        MExpr::Fun(ps, body) => {
            let xs: Vec<_> = ps.iter().map(print_fun_param).collect();
            format!("fun {} => {}", xs.join(" "), print_expr_ind(body, ind))
        }
        MExpr::FunCases(arms) => {
            let mut out = String::from("fun\n");
            for a in arms {
                writeln!(out, "{}", print_arm(a, ind + 2)).unwrap();
            }
            write!(out, "{}end", " ".repeat(ind)).unwrap();
            out
        }
        MExpr::Let {
            pat,
            binders,
            ty,
            val,
            body,
        } => {
            let bs = if binders.is_empty() {
                String::new()
            } else {
                format!(" {}", print_binders(binders))
            };
            let ts = ty
                .as_ref()
                .map(|t| format!(" : {}", print_expr_ind(t, ind)))
                .unwrap_or_default();
            format!(
                "let {}{bs}{ts} := {} in {}",
                print_pat(pat),
                print_expr_ind(val, ind),
                print_expr_ind(body, ind)
            )
        }
        MExpr::If(c, t, f) => {
            format!(
                "if {} then {} else {}",
                print_expr_ind(c, ind),
                print_expr_ind(t, ind),
                print_expr_ind(f, ind)
            )
        }
        MExpr::Match(scrs, arms) => {
            let ss: Vec<_> = scrs.iter().map(|s| print_expr_ind(s, ind)).collect();
            let mut out = format!("match {} with\n", ss.join(", "));
            for a in arms {
                writeln!(out, "{}", print_arm(a, ind + 2)).unwrap();
            }
            write!(out, "{}end", " ".repeat(ind)).unwrap();
            out
        }
        MExpr::Matches(e, pat) => {
            let ls = wrap_prec(e, 51, print_expr_ind(e, ind));
            format!("{ls} matches {}", print_pat(pat))
        }
        MExpr::Do(stmts) => {
            let mut out = String::from("do {\n");
            for s in stmts {
                writeln!(out, "{}", print_do_stmt(s, ind + 2)).unwrap();
            }
            write!(out, "{}}}", " ".repeat(ind)).unwrap();
            out
        }
        MExpr::Ascribe(e, ty) => {
            format!("({} : {})", print_expr_ind(e, ind), print_expr_ind(ty, ind))
        }
    }
}

fn print_def(out: &mut String, d: &MDef, ind: usize, is_where: bool) {
    let pfx = " ".repeat(ind);
    push_doc(out, ind, &d.doc, false);
    let kw = if is_where {
        ""
    } else if d.inline {
        "inline def "
    } else {
        "def "
    };
    let bs = if d.binders.is_empty() {
        String::new()
    } else {
        format!(" {}", print_binders(&d.binders))
    };
    let ts = d
        .ty
        .as_ref()
        .map(|t| format!(" : {}", print_expr_ind(t, ind)))
        .unwrap_or_default();
    match &d.body {
        MDefBody::Expr(e) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts} := {}", d.name, print_expr_ind(e, ind)).unwrap();
        }
        MDefBody::Clauses(arms) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts}", d.name).unwrap();
            for a in arms {
                writeln!(out, "{}", print_arm(a, ind + 2)).unwrap();
            }
            writeln!(out, "{pfx}end").unwrap();
        }
        MDefBody::Struct(fields) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts} {{", d.name).unwrap();
            for f in fields {
                match f {
                    MStructDefField::Val { name, binders, val } => {
                        let fbs = if binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", print_binders(binders))
                        };
                        writeln!(out, "{pfx}  {name}{fbs} := {};", print_expr_ind(val, ind + 2))
                            .unwrap();
                    }
                    MStructDefField::Clauses { name, arms } => {
                        writeln!(out, "{pfx}  {name}").unwrap();
                        for a in arms {
                            writeln!(out, "{}", print_arm(a, ind + 4)).unwrap();
                        }
                        writeln!(out, "{pfx}  end;").unwrap();
                    }
                }
            }
            writeln!(out, "{pfx}}}").unwrap();
        }
    }
    if !d.where_defs.is_empty() {
        writeln!(out, "{pfx}where {{").unwrap();
        for wd in &d.where_defs {
            print_def(out, wd, ind + 2, true);
        }
        writeln!(out, "{pfx}}}").unwrap();
    } else if !is_where {
        // Semicolon not needed; top-level defs are unambiguous.
    }
}

fn print_item(out: &mut String, item: &MItem, ind: usize) {
    let pfx = " ".repeat(ind);
    match item {
        MItem::ModDoc(d) => {
            push_doc(out, ind, &Some(d.clone()), true);
        }
        MItem::Namespace { name, items } => {
            writeln!(out, "{pfx}namespace {name} {{").unwrap();
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push('\n');
                }
                print_item(out, it, ind + 2);
            }
            writeln!(out, "{pfx}}}").unwrap();
        }
        MItem::Section { name, items } => {
            if let Some(n) = name {
                writeln!(out, "{pfx}section {n} {{").unwrap();
            } else {
                writeln!(out, "{pfx}section {{").unwrap();
            }
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push('\n');
                }
                print_item(out, it, ind + 2);
            }
            writeln!(out, "{pfx}}}").unwrap();
        }
        MItem::Mutual { items } => {
            writeln!(out, "{pfx}mutual {{").unwrap();
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push('\n');
                }
                print_item(out, it, ind + 2);
            }
            writeln!(out, "{pfx}}}").unwrap();
        }
        MItem::Open(ns) => {
            writeln!(out, "{pfx}open {}", ns.join(" ")).unwrap();
        }
        MItem::Var(bs) => {
            writeln!(out, "{pfx}var {}", print_binders(bs)).unwrap();
        }
        MItem::Syntax(s) => {
            push_doc(out, ind, &s.doc, false);
            let bs = if s.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", print_binders(&s.binders))
            };
            match &s.body {
                MSyntaxBody::Alias(t) => {
                    writeln!(out, "{pfx}syntax {}{bs} = {}", s.name, print_expr_ind(t, ind))
                        .unwrap();
                }
                MSyntaxBody::Variant(cases) => {
                    writeln!(out, "{pfx}syntax {}{bs} {{", s.name).unwrap();
                    for c in cases {
                        push_doc(out, ind + 2, &c.doc, false);
                        let cbs = if c.binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", print_binders(&c.binders))
                        };
                        writeln!(out, "{pfx}  | {}{cbs}", c.name).unwrap();
                    }
                    writeln!(out, "{pfx}}}").unwrap();
                }
                MSyntaxBody::Record(fields) => {
                    writeln!(out, "{pfx}syntax {}{bs} record {{", s.name).unwrap();
                    for f in fields {
                        push_doc(out, ind + 2, &f.doc, false);
                        let fbs = if f.binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", print_binders(&f.binders))
                        };
                        let def = f
                            .default
                            .as_ref()
                            .map(|d| format!(" := {}", print_expr_ind(d, ind + 2)))
                            .unwrap_or_default();
                        writeln!(
                            out,
                            "{pfx}  {}{fbs} : {}{def};",
                            f.name,
                            print_expr_ind(&f.ty, ind + 2)
                        )
                        .unwrap();
                    }
                    writeln!(out, "{pfx}}}").unwrap();
                }
            }
            if !s.deriving.is_empty() {
                writeln!(out, "{pfx}deriving [{}]", s.deriving.join(", ")).unwrap();
            }
            if let Some((ty, d)) = &s.default_inhabited {
                writeln!(
                    out,
                    "{pfx}inhabited {} := {}",
                    print_expr_ind(ty, ind),
                    print_expr_ind(d, ind)
                )
                .unwrap();
            }
        }
        MItem::Relation(r) => {
            push_doc(out, ind, &r.doc, false);
            let bs = if r.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", print_binders(&r.binders))
            };
            writeln!(
                out,
                "{pfx}relation {}{bs} : {} {{",
                r.name,
                print_expr_ind(&r.sig, ind)
            )
            .unwrap();
            for rl in &r.rules {
                push_doc(out, ind + 2, &rl.doc, false);
                let rbs = if rl.binders.is_empty() {
                    String::new()
                } else {
                    format!(" {}", print_binders(&rl.binders))
                };
                if rl.premises.is_empty() {
                    writeln!(
                        out,
                        "{pfx}  rule {}{rbs} : {};",
                        rl.name,
                        print_expr_ind(&rl.conclusion, ind + 4)
                    )
                    .unwrap();
                } else {
                    let ps: Vec<_> = rl
                        .premises
                        .iter()
                        .map(|p| print_expr_ind(p, ind + 4))
                        .collect();
                    writeln!(
                        out,
                        "{pfx}  rule {}{rbs} : {} :- {};",
                        rl.name,
                        print_expr_ind(&rl.conclusion, ind + 4),
                        ps.join(", ")
                    )
                    .unwrap();
                }
            }
            writeln!(out, "{pfx}}}").unwrap();
        }
        MItem::Laws(ls) => {
            push_doc(out, ind, &ls.doc, false);
            let bs = if ls.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", print_binders(&ls.binders))
            };
            let ext = if ls.extends.is_empty() {
                String::new()
            } else {
                let xs: Vec<_> = ls
                    .extends
                    .iter()
                    .map(|e| print_expr_ind(e, ind))
                    .collect();
                format!(" extends [{}]", xs.join(", "))
            };
            if ls.laws.is_empty() {
                writeln!(out, "{pfx}laws {}{bs}{ext} {{}}", ls.name).unwrap();
            } else {
                writeln!(out, "{pfx}laws {}{bs}{ext} {{", ls.name).unwrap();
                for lw in &ls.laws {
                    push_doc(out, ind + 2, &lw.doc, false);
                    writeln!(
                        out,
                        "{pfx}  law {} : {};",
                        lw.name,
                        print_expr_ind(&lw.prop, ind + 4)
                    )
                    .unwrap();
                }
                writeln!(out, "{pfx}}}").unwrap();
            }
        }
        MItem::Def(d) => print_def(out, d, ind, false),
    }
}

pub fn print_spec_module(header_comment: &Option<String>, m: &SpecModule) -> String {
    let mut out = String::new();
    if let Some(c) = header_comment {
        out.push_str(c);
        out.push_str("\n\n");
    }
    writeln!(out, "spec_module {}", m.target_module).unwrap();
    for imp in &m.imports {
        writeln!(out, "import {imp}").unwrap();
    }
    for it in &m.items {
        out.push('\n');
        print_item(&mut out, it, 0);
    }
    out
}
