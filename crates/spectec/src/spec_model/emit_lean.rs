//! Lean 4 code emitter for `spec_model` modules (`lean/Ecma/Gen/Prose*.lean`).

use crate::ast::{Spec, TopItem};
use crate::spec_model::ast::*;
use std::collections::BTreeMap;
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
    if bang {
        writeln!(out, "{pfx}/-!\n{d}\n{pfx}-/").unwrap();
    } else if !d.contains('\n') {
        writeln!(out, "{pfx}/-- {d} -/").unwrap();
    } else {
        let mut lines = d.split('\n');
        let first = lines.next().unwrap_or("");
        writeln!(out, "{pfx}/-- {first}").unwrap();
        let rest: Vec<_> = lines.collect();
        for (i, line) in rest.iter().enumerate() {
            let last = i + 1 == rest.len();
            if last {
                if line.is_empty() {
                    writeln!(out, "{pfx}-/").unwrap();
                } else {
                    writeln!(out, "{pfx}{line} -/").unwrap();
                }
            } else if line.is_empty() {
                writeln!(out).unwrap();
            } else {
                writeln!(out, "{pfx}{line}").unwrap();
            }
        }
    }
}

fn emit_lit(l: &MLit) -> String {
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

fn emit_binder(b: &MBinder) -> String {
    match b {
        MBinder::Explicit { names, ty: Some(t) } => {
            format!("({} : {})", names.join(" "), emit_expr(t))
        }
        MBinder::Explicit { names, ty: None } => format!("({})", names.join(" ")),
        MBinder::Implicit { names, ty: Some(t) } => {
            format!("{{{} : {}}}", names.join(" "), emit_expr(t))
        }
        MBinder::Implicit { names, ty: None } => format!("{{{}}}", names.join(" ")),
        MBinder::Bare(n) => n.clone(),
        MBinder::In { name, coll } => format!("{name} ∈ {}", emit_expr(coll)),
        MBinder::Rel { name, op, bound } => {
            let sym = match op {
                MRelBoundOp::Lt => "<",
                MRelBoundOp::Le => "≤",
            };
            format!("{name} {sym} {}", emit_expr(bound))
        }
    }
}

fn emit_binders(bs: &[MBinder]) -> String {
    bs.iter().map(emit_binder).collect::<Vec<_>>().join(" ")
}

fn emit_pat(p: &MPat, prec: u8) -> String {
    match p {
        MPat::Wild => "_".into(),
        MPat::Dots => "..".into(),
        MPat::Var(v) => v.clone(),
        MPat::Lit(l) => emit_lit(l),
        MPat::Tag(t, args) => {
            if args.is_empty() {
                format!(".{t}")
            } else {
                let xs: Vec<_> = args.iter().map(|a| emit_pat(a, 100)).collect();
                let res = format!(".{t} {}", xs.join(" "));
                if prec > 90 {
                    format!("({res})")
                } else {
                    res
                }
            }
        }
        MPat::Ctor(c, args) => {
            if args.is_empty() {
                c.clone()
            } else {
                let xs: Vec<_> = args.iter().map(|a| emit_pat(a, 100)).collect();
                let res = format!("{c} {}", xs.join(" "));
                if prec > 90 {
                    format!("({res})")
                } else {
                    res
                }
            }
        }
        MPat::Tuple(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| emit_pat(a, 0)).collect();
            format!("({})", xs.join(", "))
        }
        MPat::AnonCtor(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| emit_pat(a, 0)).collect();
            format!("⟨{}⟩", xs.join(", "))
        }
        MPat::List(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| emit_pat(a, 0)).collect();
            format!("[{}]", xs.join(", "))
        }
        MPat::Cons(h, t) => {
            let ls = emit_pat(h, 68);
            let rs = emit_pat(t, 67);
            let res = format!("{ls} :: {rs}");
            if prec > 67 {
                format!("({res})")
            } else {
                res
            }
        }
        MPat::AddNat(v, n) => {
            let res = format!("{v} + {n}");
            if prec > 65 {
                format!("({res})")
            } else {
                res
            }
        }
        MPat::Or(ps) => {
            let xs: Vec<_> = ps.iter().map(|a| emit_pat(a, 11)).collect();
            let res = xs.join(" | ");
            if prec > 10 {
                format!("({res})")
            } else {
                res
            }
        }
        MPat::As(v, inner) => format!("{v}@({})", emit_pat(inner, 0)),
    }
}

// Operator precedence rules for Lean 4 emission.
trait BinPrecExt {
    fn prec(self) -> u8;
    fn op_str(self) -> &'static str;
    fn right_assoc(self) -> bool;
}

impl BinPrecExt for MBinOp {
    fn prec(self) -> u8 {
        match self {
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

    fn op_str(self) -> &'static str {
        match self {
            MBinOp::Pow => "^",
            MBinOp::Mul => "*",
            MBinOp::Div => "/",
            MBinOp::Mod => "%",
            MBinOp::Add => "+",
            MBinOp::Sub => "-",
            MBinOp::Append => "++",
            MBinOp::Cons => "::",
            MBinOp::Times => "×",
            MBinOp::Sum => "⊕",
            MBinOp::BoolEq => "==",
            MBinOp::BoolNe => "!=",
            MBinOp::Lt => "<",
            MBinOp::Le => "≤",
            MBinOp::Gt => ">",
            MBinOp::Ge => "≥",
            MBinOp::Eq => "=",
            MBinOp::Ne => "≠",
            MBinOp::In => "∈",
            MBinOp::NotIn => "∉",
            MBinOp::BoolAnd => "&&",
            MBinOp::BoolOr => "||",
            MBinOp::And => "∧",
            MBinOp::Or => "∨",
            MBinOp::Iff => "↔",
        }
    }

    fn right_assoc(self) -> bool {
        matches!(
            self,
            MBinOp::Pow | MBinOp::Cons | MBinOp::Times | MBinOp::Sum | MBinOp::And | MBinOp::Or
        )
    }
}

fn lean_expr_prec(e: &MExpr) -> u8 {
    match e {
        MExpr::Ident(_)
        | MExpr::Tag(_)
        | MExpr::Lit(_)
        | MExpr::List(_)
        | MExpr::Tuple(_)
        | MExpr::AnonCtor(_)
        | MExpr::StructLit { .. }
        | MExpr::Ascribe(..) => 100,
        MExpr::Proj(..) | MExpr::Index(..) | MExpr::IndexOpt(..) => 95,
        MExpr::Call(..) => 90,
        MExpr::UnOp(MUnOp::Neg, _) => 75,
        MExpr::UnOp(MUnOp::Bind, _) => 100,
        MExpr::UnOp(MUnOp::BoolNot, _) => 40,
        MExpr::UnOp(MUnOp::PropNot, x) => match x.as_ref() {
            MExpr::Quant(..) => 0,
            _ => 40,
        },
        MExpr::BinOp(op, _, _) => op.prec(),
        MExpr::Matches(..) => 45,
        MExpr::Arrow { .. } => 25,
        MExpr::Quant(..)
        | MExpr::Fun(..)
        | MExpr::FunCases(_)
        | MExpr::Let { .. }
        | MExpr::If(..)
        | MExpr::Match(..)
        | MExpr::Do(_) => 0,
    }
}

fn wrap(e: &MExpr, min: u8, s: String) -> String {
    if lean_expr_prec(e) < min {
        format!("({s})")
    } else {
        s
    }
}

fn emit_fun_param(p: &MFunParam) -> String {
    match p {
        MFunParam::Pat(pat) => match pat {
            MPat::Var(_) | MPat::Wild | MPat::Tuple(_) | MPat::AnonCtor(_) | MPat::List(_) => {
                emit_pat(pat, 0)
            }
            _ => format!("({})", emit_pat(pat, 0)),
        },
        MFunParam::Explicit { names, ty } => format!("({} : {})", names.join(" "), emit_expr(ty)),
        MFunParam::Implicit { names, ty: Some(t) } => {
            format!("{{{} : {}}}", names.join(" "), emit_expr(t))
        }
        MFunParam::Implicit { names, ty: None } => format!("{{{}}}", names.join(" ")),
    }
}

fn emit_arm(arm: &MMatchArm, ind: usize) -> String {
    let pfx = " ".repeat(ind);
    let alts: Vec<_> = arm
        .alts
        .iter()
        .map(|row| row.iter().map(|p| emit_pat(p, 0)).collect::<Vec<_>>().join(", "))
        .collect();
    format!("{pfx}| {} => {}", alts.join(" | "), emit_expr_ind(&arm.rhs, ind + 2))
}

fn emit_do_stmt(st: &MDoStmt, ind: usize) -> String {
    let pfx = " ".repeat(ind);
    match st {
        MDoStmt::LetBind { pat, ty, val } => {
            let tys = ty
                .as_ref()
                .map(|t| format!(" : {}", emit_expr_ind(t, ind)))
                .unwrap_or_default();
            format!("{pfx}let {}{tys} ← {}", emit_pat(pat, 0), emit_expr_ind(val, ind))
        }
        MDoStmt::LetPure { pat, ty, val } => {
            let tys = ty
                .as_ref()
                .map(|t| format!(" : {}", emit_expr_ind(t, ind)))
                .unwrap_or_default();
            format!("{pfx}let {}{tys} := {}", emit_pat(pat, 0), emit_expr_ind(val, ind))
        }
        MDoStmt::Return(e) => format!("{pfx}return {}", emit_expr_ind(e, ind)),
        MDoStmt::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut out = format!("{pfx}if {} then\n", emit_expr_ind(cond, ind));
            for (i, s) in then_branch.iter().enumerate() {
                if i > 0 {
                    out.push('\n');
                }
                out.push_str(&emit_do_stmt(s, ind + 2));
            }
            if let Some(eb) = else_branch {
                out.push_str(&format!("\n{pfx}else\n"));
                for (i, s) in eb.iter().enumerate() {
                    if i > 0 {
                        out.push('\n');
                    }
                    out.push_str(&emit_do_stmt(s, ind + 2));
                }
            }
            out
        }
        MDoStmt::Expr(e) => format!("{pfx}{}", emit_expr_ind(e, ind)),
    }
}

pub fn emit_expr(e: &MExpr) -> String {
    emit_expr_ind(e, 2)
}

fn is_negative_lit(e: &MExpr) -> bool {
    matches!(e, MExpr::UnOp(MUnOp::Neg, x) if matches!(x.as_ref(), MExpr::Lit(MLit::Int(_) | MLit::Hex(_))))
}

fn emit_expr_ind(e: &MExpr, ind: usize) -> String {
    match e {
        MExpr::Ident(s) => s.clone(),
        MExpr::Tag(t) => format!(".{t}"),
        MExpr::Lit(l) => emit_lit(l),
        MExpr::Proj(base, f) => {
            let b = wrap(base, 95, emit_expr_ind(base, ind));
            format!("{b}.{f}")
        }
        MExpr::Call(callee, args) => {
            let c = wrap(callee, 90, emit_expr_ind(callee, ind));
            let xs: Vec<_> = args
                .iter()
                .map(|a| match a {
                    MArg::Pos(x) => {
                        if is_negative_lit(x) {
                            format!("({})", emit_expr_ind(x, ind))
                        } else {
                            wrap(x, 95, emit_expr_ind(x, ind))
                        }
                    }
                    MArg::Named(k, x) => format!("({k} := {})", emit_expr_ind(x, ind)),
                })
                .collect();
            if xs.is_empty() {
                c
            } else {
                format!("{c} {}", xs.join(" "))
            }
        }
        MExpr::Index(base, idx) => {
            let b = wrap(base, 95, emit_expr_ind(base, ind));
            format!("{b}[{}]", emit_expr_ind(idx, ind))
        }
        MExpr::IndexOpt(base, idx) => {
            let b = wrap(base, 95, emit_expr_ind(base, ind));
            format!("{b}[{}]?", emit_expr_ind(idx, ind))
        }
        MExpr::List(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| emit_expr_ind(x, ind)).collect();
            format!("[{}]", ps.join(", "))
        }
        MExpr::Tuple(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| emit_expr_ind(x, ind)).collect();
            format!("({})", ps.join(", "))
        }
        MExpr::AnonCtor(xs) => {
            let ps: Vec<_> = xs.iter().map(|x| emit_expr_ind(x, ind)).collect();
            format!("⟨{}⟩", ps.join(", "))
        }
        MExpr::StructLit { base, fields } => {
            let b = base
                .as_ref()
                .map(|x| format!("{} with ", emit_expr_ind(x, ind)))
                .unwrap_or_default();
            let fs: Vec<_> = fields
                .iter()
                .map(|(k, ov)| match ov {
                    Some(v) => format!("{k} := {}", emit_expr_ind(v, ind)),
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
            let s = wrap(x, 95, emit_expr_ind(x, ind));
            format!("-{s}")
        }
        MExpr::UnOp(MUnOp::BoolNot, x) => {
            // Lean `!` is prefix:40, looser than Call (90) and Postfix (95), tighter than `&&` (35).
            // Never emit `![` because Lean lexes `![` as the vector/matrix macro token.
            let min = if matches!(x.as_ref(), MExpr::Call(..) | MExpr::Proj(..) | MExpr::Index(..) | MExpr::IndexOpt(..) | MExpr::Ident(_) | MExpr::Lit(_)) {
                41
            } else {
                100
            };
            let s = wrap(x, min, emit_expr_ind(x, ind));
            if s.starts_with('[') {
                format!("!({s})")
            } else {
                format!("!{s}")
            }
        }
        MExpr::UnOp(MUnOp::Bind, x) => {
            format!("(← {})", emit_expr_ind(x, ind))
        }
        MExpr::UnOp(MUnOp::PropNot, x) => match x.as_ref() {
            MExpr::Quant(..) => format!("¬{}", emit_expr_ind(x, ind)),
            _ => {
                let s = wrap(x, 41, emit_expr_ind(x, ind));
                format!("¬ {s}")
            }
        },
        MExpr::BinOp(op, a, b) => {
            let p = op.prec();
            let lmin = if op.right_assoc() || p == 50 { p + 1 } else { p };
            let rmin = if matches!(
                b.as_ref(),
                MExpr::Quant(..)
                    | MExpr::Let { .. }
                    | MExpr::If(..)
                    | MExpr::Fun(..)
                    | MExpr::FunCases(_)
                    | MExpr::Match(..)
                    | MExpr::Do(_)
            ) && matches!(
                op,
                MBinOp::Eq | MBinOp::Ne | MBinOp::And | MBinOp::Or | MBinOp::Iff
            ) {
                0
            } else if matches!(b.as_ref(), MExpr::UnOp(MUnOp::PropNot, _))
                && matches!(op, MBinOp::And | MBinOp::Or | MBinOp::Iff)
            {
                0
            } else if op.right_assoc() && p != 50 {
                p
            } else {
                p + 1
            };
            let ls = wrap(a, lmin, emit_expr_ind(a, ind));
            let rs = wrap(b, rmin, emit_expr_ind(b, ind));
            format!("{ls} {} {rs}", op.op_str())
        }
        MExpr::Arrow { binder, dom, cod } => {
            let lhs = match (binder, dom) {
                (Some(b), _) => emit_binder(b),
                (None, Some(d)) => wrap(d, 26, emit_expr_ind(d, ind)),
                (None, None) => "_".into(),
            };
            let cod_min = if matches!(cod.as_ref(), MExpr::UnOp(MUnOp::PropNot, _)) {
                0
            } else {
                25
            };
            let rhs = wrap(cod, cod_min, emit_expr_ind(cod, ind));
            format!("{lhs} → {rhs}")
        }
        MExpr::Quant(q, bs, body) => {
            let kw = match q {
                MQuant::Forall => "∀",
                MQuant::Exists => "∃",
            };
            format!("{kw} {}, {}", emit_binders(bs), emit_expr_ind(body, ind))
        }
        MExpr::Fun(ps, body) => {
            let xs: Vec<_> = ps.iter().map(emit_fun_param).collect();
            format!("fun {} => {}", xs.join(" "), emit_expr_ind(body, ind))
        }
        MExpr::FunCases(arms) => {
            let mut out = String::from("fun");
            for a in arms {
                out.push('\n');
                out.push_str(&emit_arm(a, ind + 2));
            }
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
                format!(" {}", emit_binders(binders))
            };
            let ts = ty
                .as_ref()
                .map(|t| format!(" : {}", emit_expr_ind(t, ind)))
                .unwrap_or_default();
            let val_s = emit_expr_ind(val, ind);
            let val_s = if matches!(
                val.as_ref(),
                MExpr::Do(_) | MExpr::Match(..) | MExpr::FunCases(_) | MExpr::Let { .. }
            ) {
                format!("({val_s})")
            } else {
                val_s
            };
            format!(
                "let {}{bs}{ts} := {val_s}; {}",
                emit_pat(pat, 0),
                emit_expr_ind(body, ind)
            )
        }
        MExpr::If(c, t, f) => {
            format!(
                "if {} then {} else {}",
                emit_expr_ind(c, ind),
                emit_expr_ind(t, ind),
                emit_expr_ind(f, ind)
            )
        }
        MExpr::Match(scrs, arms) => {
            let ss: Vec<_> = scrs.iter().map(|s| emit_expr_ind(s, ind)).collect();
            let mut out = format!("match {} with", ss.join(", "));
            for a in arms {
                out.push('\n');
                out.push_str(&emit_arm(a, ind + 2));
            }
            out
        }
        MExpr::Matches(e, pat) => {
            let ls = wrap(e, 46, emit_expr_ind(e, ind));
            format!("{ls} matches {}", emit_pat(pat, 0))
        }
        MExpr::Do(stmts) => {
            let mut out = String::from("do");
            for s in stmts {
                out.push('\n');
                out.push_str(&emit_do_stmt(s, ind + 2));
            }
            out
        }
        MExpr::Ascribe(e, ty) => {
            format!("({} : {})", emit_expr_ind(e, ind), emit_expr_ind(ty, ind))
        }
    }
}

fn emit_def(out: &mut String, d: &MDef, is_where: bool) {
    let base_ind = if is_where { 2 } else { 0 };
    let pfx = " ".repeat(base_ind);
    push_doc(out, base_ind, &d.doc, false);
    let kw = if is_where {
        ""
    } else if d.inline {
        "@[inline] def "
    } else {
        "def "
    };
    let bs = if d.binders.is_empty() {
        String::new()
    } else {
        format!(" {}", emit_binders(&d.binders))
    };
    let ts = d
        .ty
        .as_ref()
        .map(|t| format!(" : {}", emit_expr(t)))
        .unwrap_or_default();
    let body_ind = base_ind + 2;
    match &d.body {
        MDefBody::Expr(e) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts} :=\n{}{}", d.name, " ".repeat(body_ind), emit_expr_ind(e, body_ind)).unwrap();
        }
        MDefBody::Clauses(arms) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts}", d.name).unwrap();
            for a in arms {
                writeln!(out, "{}", emit_arm(a, body_ind)).unwrap();
            }
        }
        MDefBody::Struct(fields) => {
            writeln!(out, "{pfx}{kw}{}{bs}{ts} where", d.name).unwrap();
            for f in fields {
                match f {
                    MStructDefField::Val { name, binders, val } => {
                        let fbs = if binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", emit_binders(binders))
                        };
                        writeln!(out, "{pfx}  {name}{fbs} := {}", emit_expr_ind(val, body_ind + 2))
                            .unwrap();
                    }
                    MStructDefField::Clauses { name, arms } => {
                        writeln!(out, "{pfx}  {name}").unwrap();
                        for a in arms {
                            writeln!(out, "{}", emit_arm(a, body_ind + 2)).unwrap();
                        }
                    }
                }
            }
        }
    }
    if !d.where_defs.is_empty() {
        writeln!(out, "where").unwrap();
        for wd in &d.where_defs {
            emit_def(out, wd, true);
        }
    }
}

fn emit_item(out: &mut String, item: &MItem) {
    match item {
        MItem::ModDoc(d) => {
            push_doc(out, 0, &Some(d.clone()), true);
        }
        MItem::Namespace { name, items } => {
            writeln!(out, "namespace {name}").unwrap();
            for it in items {
                out.push('\n');
                emit_item(out, it);
            }
            writeln!(out, "\nend {name}").unwrap();
        }
        MItem::Section { name, items } => {
            if let Some(n) = name {
                writeln!(out, "section {n}").unwrap();
            } else {
                writeln!(out, "section").unwrap();
            }
            for it in items {
                out.push('\n');
                emit_item(out, it);
            }
            if let Some(n) = name {
                writeln!(out, "\nend {n}").unwrap();
            } else {
                writeln!(out, "\nend").unwrap();
            }
        }
        MItem::Mutual { items } => {
            writeln!(out, "mutual").unwrap();
            for it in items {
                emit_item(out, it);
            }
            writeln!(out, "end").unwrap();
        }
        MItem::Open(ns) => {
            writeln!(out, "open {}", ns.join(" ")).unwrap();
        }
        MItem::Var(bs) => {
            writeln!(out, "variable {}", emit_binders(bs)).unwrap();
        }
        MItem::Syntax(s) => {
            push_doc(out, 0, &s.doc, false);
            let bs = if s.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", emit_binders(&s.binders))
            };
            match &s.body {
                MSyntaxBody::Alias(t) => {
                    writeln!(out, "abbrev {}{bs} := {}", s.name, emit_expr(t)).unwrap();
                }
                MSyntaxBody::Variant(cases) => {
                    writeln!(out, "inductive {}{bs} where", s.name).unwrap();
                    for c in cases {
                        push_doc(out, 2, &c.doc, false);
                        let cbs = if c.binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", emit_binders(&c.binders))
                        };
                        writeln!(out, "  | {}{cbs}", c.name).unwrap();
                    }
                    if !s.deriving.is_empty() {
                        writeln!(out, "  deriving {}", s.deriving.join(", ")).unwrap();
                    }
                    if let Some((ty, d)) = &s.default_inhabited {
                        let tys = wrap(ty, 95, emit_expr(ty));
                        writeln!(
                            out,
                            "\ninstance : Inhabited {tys} := ⟨{}⟩",
                            emit_expr(d)
                        )
                        .unwrap();
                    }
                }
                MSyntaxBody::Record(fields) => {
                    writeln!(out, "structure {}{bs} where", s.name).unwrap();
                    for f in fields {
                        push_doc(out, 2, &f.doc, false);
                        let fbs = if f.binders.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", emit_binders(&f.binders))
                        };
                        let def = f
                            .default
                            .as_ref()
                            .map(|d| format!(" := {}", emit_expr_ind(d, 4)))
                            .unwrap_or_default();
                        writeln!(out, "  {}{fbs} : {}{def}", f.name, emit_expr_ind(&f.ty, 4))
                            .unwrap();
                    }
                    if !s.deriving.is_empty() {
                        writeln!(out, "  deriving {}", s.deriving.join(", ")).unwrap();
                    }
                }
            }
        }
        MItem::Relation(r) => {
            push_doc(out, 0, &r.doc, false);
            let bs = if r.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", emit_binders(&r.binders))
            };
            writeln!(out, "inductive {}{bs} : {} where", r.name, emit_expr(&r.sig)).unwrap();
            for rl in &r.rules {
                push_doc(out, 2, &rl.doc, false);
                let rbs = if rl.binders.is_empty() {
                    String::new()
                } else {
                    format!(" {}", emit_binders(&rl.binders))
                };
                if rl.premises.is_empty() {
                    writeln!(out, "  | {}{rbs} : {}", rl.name, emit_expr_ind(&rl.conclusion, 4))
                        .unwrap();
                } else {
                    let mut parts: Vec<_> = rl
                        .premises
                        .iter()
                        .map(|p| wrap(p, 26, emit_expr_ind(p, 4)))
                        .collect();
                    parts.push(emit_expr_ind(&rl.conclusion, 4));
                    writeln!(out, "  | {}{rbs} : {}", rl.name, parts.join(" →\n      ")).unwrap();
                }
            }
        }
        MItem::Laws(ls) => {
            push_doc(out, 0, &ls.doc, false);
            let bs = if ls.binders.is_empty() {
                String::new()
            } else {
                format!(" {}", emit_binders(&ls.binders))
            };
            let ext = if ls.extends.is_empty() {
                String::new()
            } else {
                let xs: Vec<_> = ls.extends.iter().map(emit_expr).collect();
                format!(" extends {}", xs.join(", "))
            };
            if ls.laws.is_empty() {
                writeln!(out, "structure {}{bs} : Prop{ext}", ls.name).unwrap();
            } else {
                writeln!(out, "structure {}{bs} : Prop{ext} where", ls.name).unwrap();
                for lw in &ls.laws {
                    push_doc(out, 2, &lw.doc, false);
                    writeln!(out, "  {} : {}", lw.name, emit_expr_ind(&lw.prop, 4)).unwrap();
                }
            }
        }
        MItem::Def(d) => emit_def(out, d, false),
    }
}

pub fn emit_spec_module(m: &SpecModule) -> String {
    let mut out = String::from("module\n\n");
    for imp in &m.imports {
        writeln!(out, "public import {imp}").unwrap();
    }
    if !m.imports.is_empty() {
        out.push('\n');
    }
    writeln!(out, "@[expose] public section").unwrap();
    for it in &m.items {
        out.push('\n');
        emit_item(&mut out, it);
    }
    out
}

pub fn emit(spec: &Spec) -> Result<BTreeMap<String, String>, String> {
    let mut out = BTreeMap::new();
    for f in &spec.files {
        for item in &f.items {
            if let TopItem::SpecModule(m) = item {
                if out.contains_key(&m.target_module) {
                    return Err(format!("duplicate prose target_module `{}`", m.target_module));
                }
                out.insert(m.target_module.clone(), emit_spec_module(m));
            }
        }
    }
    Ok(out)
}
