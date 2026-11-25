//! Rendering `@ph-*` helpers and `$Prim` primitives via `spec/html/call-templates.txt`.

use crate::alg_render::{render_expr, Ctx, Out};
use crate::meta::{CallTemplates, PhTemplate, PrimTemplate};
use spectec::ast::{DataLit, Expr};

fn subst_vars(pat: &str, params: &[String], args: &[String]) -> String {
    let mut out = String::with_capacity(pat.len());
    let mut i = 0;
    let bytes = pat.as_bytes();
    while i < bytes.len() {
        if bytes[i] == b'_' {
            // Check boundary: don't match mid-word underscores if not a param name.
            if let Some(rel_end) = pat[i + 1..].find('_') {
                let name = &pat[i + 1..i + 1 + rel_end];
                let norm = name.replace(' ', "_");
                if let Some(pidx) = params.iter().position(|p| p == name || p == &norm) {
                    if let Some(val) = args.get(pidx) {
                        out.push_str(val);
                        i += 1 + rel_end + 1;
                        continue;
                    }
                }
            }
        }
        let ch = pat[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

pub fn render_ph_call(
    cx: &Ctx,
    t: &PhTemplate,
    args: &[Expr],
) -> Option<Out> {
    if args.len() != t.params.len() {
        return None;
    }
    let mut rendered_args = Vec::with_capacity(args.len());
    for a in args {
        let o = render_expr(cx, a);
        if !o.trailing.is_empty() {
            return None;
        }
        rendered_args.push(o.inline);
    }
    let text = subst_vars(&t.pattern, &t.params, &rendered_args);
    Some(Out::raw(text))
}

fn english_list(items: &[String], conj: &str) -> String {
    match items.len() {
        0 => String::new(),
        1 => items[0].clone(),
        2 => format!("{} {conj} {}", items[0], items[1]),
        n => {
            let mut out = items[..n - 1].join(", ");
            out.push_str(&format!(", {conj} {}", items[n - 1]));
            out
        }
    }
}

pub fn render_prim_call(
    cx: &Ctx,
    templates: &CallTemplates,
    name: &str,
    args: &[Expr],
    want_stmt: bool,
) -> Option<Out> {
    // Strip optional trailing `data choice` args for primitives that match SpecTec calls.
    if name == "WellKnownSymbol" {
        if let [Expr::Val(spectec::ast::ValLit::Str(s))] = args {
            return Some(Out::raw(format!("%{s}%")));
        }
    }
    if name == "GrammarSymbol" {
        if let [Expr::Nt(nt, _)] = args {
            return Some(Out::raw(format!("the |{nt}| grammar symbol")));
        }
    }
    if name == "Component" {
        if let [obj, Expr::FieldName(f)] = args {
            if matches!(obj, Expr::Call(spectec::ast::Callee::Prim(r), a) if r == "Running" && a.is_empty()) {
                return Some(Out::raw(format!("the running execution context's {f}")));
            }
            return Some(Out::raw(format!("the {f} of {}", render_expr(cx, obj).inline)));
        }
    }
    if name == "CoveredBy" {
        if let [Expr::Nt(nt, _), sub] = args {
            return Some(Out::raw(format!("the |{nt}| that is covered by {}", render_expr(cx, sub).inline)));
        }
    }
    if name == "ListElem" {
        if let [Expr::Data(DataLit::Choice(k)), list] = args {
            let ls = render_expr(cx, list).inline;
            let ord = match k {
                0 => "sole",
                1 => "first",
                2 => "last",
                _ => return None,
            };
            return Some(Out::raw(format!("the {ord} element of {ls}")));
        }
    }
    if name == "AgentRecord" {
        if args.is_empty() {
            return Some(Out::raw("the surrounding agent's Agent Record"));
        }
    }
    if name == "CodeUnit" {
        if let [arg] = args {
            if let Expr::CodeUnit(_, d, Some(nm)) = arg {
                return Some(Out::raw(format!("the code unit 0x{d} ({nm})")));
            }
            return Some(Out::raw(format!("the code unit {}", render_expr(cx, arg).inline)));
        }
    }
    let pt: &PrimTemplate = templates.prims.get(name)?;
    if want_stmt && pt.kind != "stmt" {
        return None;
    }
    if !want_stmt && pt.kind == "stmt" {
        return None;
    }
    // Filter out trailing/leading Data::Choice markers if simple 1-arg / 2-arg match fails? Only exact for clean structural rendering:
    let clean_args: Vec<&Expr> = args
        .iter()
        .filter(|a| !matches!(a, Expr::Data(DataLit::Choice(_))))
        .collect();
    if pt.pattern.contains("{list}") {
        let items: Vec<String> = if clean_args.len() == 1 {
            if let Expr::List(es) = clean_args[0] {
                let mut v = Vec::with_capacity(es.len());
                for e in es {
                    let o = render_expr(cx, e);
                    if !o.trailing.is_empty() {
                        return None;
                    }
                    v.push(o.inline);
                }
                v
            } else {
                let o = render_expr(cx, clean_args[0]);
                return Some(Out::raw(pt.pattern.replace("{list}", &o.inline)));
            }
        } else {
            let mut v = Vec::with_capacity(clean_args.len());
            for e in &clean_args {
                let o = render_expr(cx, e);
                if !o.trailing.is_empty() {
                    return None;
                }
                v.push(o.inline);
            }
            v
        };
        return Some(Out::raw(pt.pattern.replace("{list}", &english_list(&items, "and"))));
    }
    if pt.pattern.contains("{args}") {
        let mut xs = Vec::with_capacity(clean_args.len());
        for a in &clean_args {
            let o = render_expr(cx, a);
            if !o.trailing.is_empty() {
                return None;
            }
            xs.push(o.inline);
        }
        return Some(Out::raw(pt.pattern.replace("{args}", &xs.join(", "))));
    }
    let mut s = pt.pattern.clone();
    for (i, a) in clean_args.iter().enumerate() {
        let ph = format!("{{{i}}}");
        if s.contains(&ph) {
            let o = render_expr(cx, a);
            if !o.trailing.is_empty() {
                return None;
            }
            s = s.replace(&ph, &o.inline);
        }
    }
    if s.contains('{') && s.contains('}') {
        // Check no unfilled `{0}` etc. remain
        for idx in 0..8 {
            if s.contains(&format!("{{{idx}}}")) {
                return None;
            }
        }
    }
    Some(Out::raw(s))
}
