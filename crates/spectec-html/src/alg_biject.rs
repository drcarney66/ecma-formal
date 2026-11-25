//! Bidirectional step-tree, SDO equation, Early Error, and grammar key bijection.

use crate::alg_render::{
    check_can_render_stmts, render_early_body, render_early_canonical, render_equation_line,
    render_stmts_canonical, render_units_at, Ctx, DeclsCtx, RenderUnit, UnitBody,
};
use crate::html_scan::{
    instance_alg_text, print_step_tree, step_tree, HtmlSpec, HtmlStep, SpliceItem,
};
use crate::meta::{
    check_all_used, CallTemplates, ItemKey, ItemKindMeta, ItemMeta, StepAttr, StepCont, StepPatch,
    StepPatches,
};
use spectec::ast::{AlgDef, EarlyRow, RowForm, SdoRowDef, Spec, Stmt, TopItem};
use spectec::parse::parse_str;
use spectec::print::{print_early_row, print_sdo_row};
use std::collections::{BTreeMap, BTreeSet};

const ALG_EMBED_PREFIX: &str = "{{ALG:@";

pub struct AlgStats {
    pub html_algs: usize,
    pub html_eqs: usize,
    pub html_early: usize,
    pub alg_keys: usize,
    pub early_keys: usize,
    pub tmpl_slots: usize,
    pub tmpl_instances: usize,
    pub spectec_only_defs: usize,
    pub spectec_only_rows: usize,
    pub structural_steps: usize,
    pub total_html_steps: usize,
    pub attr_only_steps: usize,
    pub patches_count: usize,
    pub structural_eqs: usize,
    pub structural_early: usize,
}

fn find_template_param(h1: &str) -> Option<String> {
    let mut rest = h1;
    while let Some(i) = rest.find('_') {
        let after = &rest[i + 1..];
        if let Some(j) = after.find('_') {
            let w = &after[..j];
            if !w.is_empty() && w.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_') {
                return Some(w.to_string());
            }
            rest = &after[j + 1..];
        } else {
            break;
        }
    }
    None
}

fn format_html_steps_rel(steps: &[HtmlStep]) -> String {
    let full = print_step_tree(0, 0, steps);
    // print_step_tree gives leading `\n` and trailing `\n`. Strip outer newlines so it matches `| ` block cleanly.
    full.trim_matches('\n').to_string()
}

fn lcs_pairs(units: &[RenderUnit], html: &[HtmlStep]) -> Vec<(usize, usize)> {
    let m = units.len();
    let n = html.len();
    let mut dp = vec![vec![0usize; n + 1]; m + 1];
    for i in (0..m).rev() {
        for j in (0..n).rev() {
            dp[i][j] = if units[i].text == html[j].text {
                1 + dp[i + 1][j + 1]
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let mut pairs = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < m && j < n {
        if units[i].text == html[j].text {
            pairs.push((i, j));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    pairs
}

fn spectec_slice_src(stmts: &[Stmt], units: &[RenderUnit], si: usize, sj: usize, ind: usize, path: &str) -> String {
    if si >= sj {
        return format!("<empty {path}:{si}..{sj}>");
    }
    let u0 = &units[si];
    let u1 = &units[sj - 1];
    // If clean whole Stmt boundary (arm_idx == 0 at start and complete statement at end):
    let starts_stmt = u0.arm_idx == 0;
    let ends_stmt = sj == units.len() || units[sj].stmt_idx != u1.stmt_idx;
    if starts_stmt && ends_stmt {
        render_stmts_canonical(ind, &stmts[u0.stmt_idx..=u1.stmt_idx])
    } else {
        units[si..sj]
            .iter()
            .map(|u| u.spectec_src.clone())
            .collect::<Vec<_>>()
            .join("\n")
    }
}

struct AlignState<'a> {
    patches: &'a mut StepPatches,
    kind: String,
    key: ItemKey,
    total_steps: usize,
    structural_steps: usize,
    attr_steps: usize,
}

impl<'a> AlignState<'a> {
    fn new(patches: &'a mut StepPatches, kind: &str, key: ItemKey) -> Self {
        Self {
            patches,
            kind: kind.to_string(),
            key,
            total_steps: 0,
            structural_steps: 0,
            attr_steps: 0,
        }
    }
}

fn align_block(
    st: &mut AlignState,
    stmts: &[Stmt],
    units: &[RenderUnit],
    html: &[HtmlStep],
    ind: usize,
    block_path: &str,
    html_prefix: &str,
) {
    let matches = lcs_pairs(units, html);
    // Sentinel at end
    let mut cur_u = 0usize;
    let mut cur_h = 0usize;
    let sentinels: Vec<(usize, usize)> = matches.iter().copied().chain(std::iter::once((units.len(), html.len()))).collect();

    for (mu, mh) in sentinels {
        if cur_u < mu || cur_h < mh {
            let sub_h = &html[cur_h..mh];
            let ppath = format!("{block_path}:{cur_u}..{mu}");
            let spectec = spectec_slice_src(stmts, units, cur_u, mu, ind, block_path);
            let htext = if sub_h.is_empty() {
                "<none>".into()
            } else {
                format_html_steps_rel(sub_h)
            };
            st.patches.patches.insert(
                (st.kind.clone(), st.key.clone(), ppath.clone()),
                StepPatch {
                    kind: st.kind.clone(),
                    key: st.key.clone(),
                    path: ppath,
                    spectec,
                    html: htext,
                },
            );
            fn count_steps_tree(hs: &[HtmlStep]) -> usize {
                hs.iter().map(|s| 1 + count_steps_tree(&s.kids)).sum()
            }
            st.total_steps += count_steps_tree(sub_h);
        }
        if mu < units.len() && mh < html.len() {
            let u = &units[mu];
            let h = &html[mh];
            let spath = if html_prefix.is_empty() {
                format!("{}", mh + 1)
            } else {
                format!("{html_prefix}.{}", mh + 1)
            };
            st.total_steps += 1;
            st.structural_steps += 1;
            if let Some(a) = &h.attrs {
                st.attr_steps += 1;
                st.patches.attrs.insert(
                    (st.kind.clone(), st.key.clone(), spath.clone()),
                    StepAttr {
                        kind: st.kind.clone(),
                        key: st.key.clone(),
                        path: spath.clone(),
                        attrs: a.clone(),
                    },
                );
            }
            if !h.cont.is_empty() {
                st.patches.conts.insert(
                    (st.kind.clone(), st.key.clone(), spath.clone()),
                    StepCont {
                        kind: st.kind.clone(),
                        key: st.key.clone(),
                        path: spath.clone(),
                        cont: h.cont.join("\n"),
                    },
                );
            }
            // Recurse into matched kids!
            match &u.kids {
                UnitBody::None => {
                    if !h.kids.is_empty() {
                        let ppath = format!("{block_path}/extra_kids:{mu}");
                        st.patches.patches.insert(
                            (st.kind.clone(), st.key.clone(), ppath.clone()),
                            StepPatch {
                                kind: st.kind.clone(),
                                key: st.key.clone(),
                                path: ppath,
                                spectec: format!("<no kids on {}>", u.spectec_src),
                                html: format_html_steps_rel(&h.kids),
                            },
                        );
                        fn count_tree(hs: &[HtmlStep]) -> usize {
                            hs.iter().map(|s| 1 + count_tree(&s.kids)).sum()
                        }
                        st.total_steps += count_tree(&h.kids);
                    }
                }
                UnitBody::Stmts(kid_path, kunits) => {
                    // Find nested stmts slice inside `stmts[u.stmt_idx]`
                    let kid_stmts = child_stmts_of(&stmts[u.stmt_idx], u.arm_idx);
                    align_block(st, kid_stmts, kunits, &h.kids, ind + 2, kid_path, &spath);
                }
                UnitBody::Closure(cl_site, kunits) => {
                    // Closure body lives at root of `closures[cl_site].body`
                    // Look up via dummy slice: note we handle closure patching under `cl<site>` directly!
                    let cl_path = format!("cl{cl_site}");
                    let _ = (kunits, cl_path);
                }
            }
        }
        cur_u = mu + 1;
        cur_h = mh + 1;
    }
}

fn child_stmts_of(s: &Stmt, arm_idx: usize) -> &[Stmt] {
    match s {
        Stmt::If(_, bd, arms, els) => {
            if arm_idx == 0 {
                match bd {
                    spectec::ast::Body::Block(ns) => ns,
                    spectec::ast::Body::Inline(_) => &[],
                }
            } else if arm_idx <= arms.len() {
                match &arms[arm_idx - 1].body {
                    spectec::ast::Body::Block(ns) => ns,
                    spectec::ast::Body::Inline(_) => &[],
                }
            } else if let Some(el) = els {
                match &el.body {
                    spectec::ast::Body::Block(ns) => ns,
                    spectec::ast::Body::Inline(_) => &[],
                }
            } else {
                &[]
            }
        }
        Stmt::Repeat(ns)
        | Stmt::RepeatWhile(_, ns)
        | Stmt::RepeatUntil(_, ns)
        | Stmt::RepeatN(_, ns)
        | Stmt::Block(ns) => ns,
        Stmt::ForEach { body, .. }
        | Stmt::ForEachRec { body, .. }
        | Stmt::ForRange { body, .. }
        | Stmt::ForKeys { body, .. }
        | Stmt::ForIndex { body, .. }
        | Stmt::ForChildren { body, .. }
        | Stmt::ForChildrenOf { body, .. } => match body {
            spectec::ast::Body::Block(ns) => ns,
            spectec::ast::Body::Inline(_) => &[],
        },
        _ => &[],
    }
}

fn align_block_with_closures(
    st: &mut AlignState,
    stmts: &[Stmt],
    closures: &[spectec::ast::CloLit],
    units: &[RenderUnit],
    html: &[HtmlStep],
    ind: usize,
    block_path: &str,
    html_prefix: &str,
) {
    let matches = lcs_pairs(units, html);
    let mut cur_u = 0usize;
    let mut cur_h = 0usize;
    let sentinels: Vec<(usize, usize)> = matches.iter().copied().chain(std::iter::once((units.len(), html.len()))).collect();

    for (mu, mh) in sentinels {
        if cur_u < mu || cur_h < mh {
            let sub_h = &html[cur_h..mh];
            let ppath = format!("{block_path}:{cur_u}..{mu}");
            let spectec = spectec_slice_src(stmts, units, cur_u, mu, ind, block_path);
            let htext = if sub_h.is_empty() { "<none>".into() } else { format_html_steps_rel(sub_h) };
            st.patches.patches.insert(
                (st.kind.clone(), st.key.clone(), ppath.clone()),
                StepPatch { kind: st.kind.clone(), key: st.key.clone(), path: ppath, spectec, html: htext },
            );
            fn count_tree(hs: &[HtmlStep]) -> usize {
                hs.iter().map(|s| 1 + count_tree(&s.kids)).sum()
            }
            st.total_steps += count_tree(sub_h);
        }
        if mu < units.len() && mh < html.len() {
            let u = &units[mu];
            let h = &html[mh];
            let spath = if html_prefix.is_empty() {
                format!("{}", mh + 1)
            } else {
                format!("{html_prefix}.{}", mh + 1)
            };
            st.total_steps += 1;
            st.structural_steps += 1;
            if let Some(a) = &h.attrs {
                st.attr_steps += 1;
                st.patches.attrs.insert(
                    (st.kind.clone(), st.key.clone(), spath.clone()),
                    StepAttr { kind: st.kind.clone(), key: st.key.clone(), path: spath.clone(), attrs: a.clone() },
                );
            }
            if !h.cont.is_empty() {
                st.patches.conts.insert(
                    (st.kind.clone(), st.key.clone(), spath.clone()),
                    StepCont { kind: st.kind.clone(), key: st.key.clone(), path: spath.clone(), cont: h.cont.join("\n") },
                );
            }
            match &u.kids {
                UnitBody::None => {
                    if !h.kids.is_empty() {
                        let ppath = format!("{block_path}/extra_kids:{mu}");
                        st.patches.patches.insert(
                            (st.kind.clone(), st.key.clone(), ppath.clone()),
                            StepPatch {
                                kind: st.kind.clone(),
                                key: st.key.clone(),
                                path: ppath,
                                spectec: format!("<no kids on {}>", u.spectec_src),
                                html: format_html_steps_rel(&h.kids),
                            },
                        );
                        fn count_tree(hs: &[HtmlStep]) -> usize {
                            hs.iter().map(|s| 1 + count_tree(&s.kids)).sum()
                        }
                        st.total_steps += count_tree(&h.kids);
                    }
                }
                UnitBody::Stmts(kid_path, kunits) => {
                    let kid_stmts = child_stmts_of(&stmts[u.stmt_idx], u.arm_idx);
                    align_block_with_closures(st, kid_stmts, closures, kunits, &h.kids, ind + 2, kid_path, &spath);
                }
                UnitBody::Closure(cl_site, kunits) => {
                    let cl_path = format!("cl{cl_site}");
                    let kid_stmts = &closures[*cl_site].body;
                    align_block_with_closures(st, kid_stmts, closures, kunits, &h.kids, 2, &cl_path, &spath);
                }
            }
        }
        cur_u = mu + 1;
        cur_h = mh + 1;
    }
}

fn render_block_from_patches(
    kind: &str,
    key: &ItemKey,
    stmts: &[Stmt],
    closures: &[spectec::ast::CloLit],
    units: &[RenderUnit],
    ind: usize,
    block_path: &str,
    html_prefix: &str,
    patches: &StepPatches,
    used_patches: &mut BTreeSet<(String, ItemKey, String)>,
    used_attrs: &mut BTreeSet<(String, ItemKey, String)>,
    used_conts: &mut BTreeSet<(String, ItemKey, String)>,
    depth: usize,
) -> Result<Vec<HtmlStep>, String> {
    let _ = align_block; // keep cleanly organized
    // Collect any patches anchored inside `block_path:<si>..<sj>`
    let prefix_colon = format!("{block_path}:");
    let mut range_patches: Vec<(usize, usize, &StepPatch, String)> = Vec::new();
    for ((pk, pkey, ppath), pat) in &patches.patches {
        if pk == kind && pkey == key {
            if let Some(rest) = ppath.strip_prefix(&prefix_colon) {
                if !rest.contains('/') {
                    let (a_s, b_s) = rest
                        .split_once("..")
                        .ok_or_else(|| format!("bad patch range {ppath}"))?;
                    let a = a_s.parse::<usize>().map_err(|e| format!("bad patch start {ppath}: {e}"))?;
                    let b = b_s.parse::<usize>().map_err(|e| format!("bad patch end {ppath}: {e}"))?;
                    range_patches.push((a, b, pat, ppath.clone()));
                }
            }
        }
    }
    range_patches.sort_by_key(|(a, b, _, _)| (*a, *b));

    let mut out_steps: Vec<HtmlStep> = Vec::new();
    let mut cur_u = 0usize;
    let mut rp_idx = 0usize;
    while cur_u < units.len() || rp_idx < range_patches.len() {
        if rp_idx < range_patches.len() && range_patches[rp_idx].0 == cur_u {
            let (si, sj, pat, ppath) = &range_patches[rp_idx];
            rp_idx += 1;
            used_patches.insert((kind.to_string(), key.clone(), ppath.clone()));
            // Verify @@spectec matches SpecTec AST slice!
            let expected_st = spectec_slice_src(stmts, units, *si, *sj, ind, block_path);
            if expected_st != pat.spectec {
                return Err(format!(
                    "{kind} {} {ppath}: SpecTec AST changed vs @@spectec in step-patches.txt:\n  live:  {expected_st:?}\n  patch: {:?}",
                    key.fmt_ref(),
                    pat.spectec
                ));
            }
            if *si < *sj && units[*si].arm_idx == 0 && (*sj == units.len() || units[*sj].stmt_idx != units[*sj - 1].stmt_idx) {
                check_can_render_stmts(&pat.spectec, &stmts[units[*si].stmt_idx..=units[*sj - 1].stmt_idx], ind)?;
            }
            if pat.html != "<none>" {
                let wrapped = format!("\n{}\n", pat.html);
                let (_, parsed_sub, _) = step_tree(&wrapped).map_err(|e| format!("{kind} {} {ppath} @@html: {e}", key.fmt_ref()))?;
                fn fix_depth(hs: Vec<HtmlStep>, base_d: usize) -> Vec<HtmlStep> {
                    hs.into_iter()
                        .map(|mut s| {
                            let d = base_d + s.depth;
                            s.depth = d;
                            s.kids = fix_depth(s.kids, base_d);
                            s
                        })
                        .collect()
                }
                out_steps.extend(fix_depth(parsed_sub, depth));
            }
            cur_u = *sj;
        } else {
            let u = &units[cur_u];
            let mh = out_steps.len();
            let spath = if html_prefix.is_empty() {
                format!("{}", mh + 1)
            } else {
                format!("{html_prefix}.{}", mh + 1)
            };
            let attrs = patches.attrs.get(&(kind.to_string(), key.clone(), spath.clone())).map(|a| {
                used_attrs.insert((kind.to_string(), key.clone(), spath.clone()));
                a.attrs.clone()
            });
            let cont = patches
                .conts
                .get(&(kind.to_string(), key.clone(), spath.clone()))
                .map(|c| {
                    used_conts.insert((kind.to_string(), key.clone(), spath.clone()));
                    c.cont.split('\n').map(|s| s.to_string()).collect::<Vec<_>>()
                })
                .unwrap_or_default();
            let kids = match &u.kids {
                UnitBody::None => {
                    let ek_path = format!("{block_path}/extra_kids:{cur_u}");
                    if let Some(pat) = patches.patches.get(&(kind.to_string(), key.clone(), ek_path.clone())) {
                        used_patches.insert((kind.to_string(), key.clone(), ek_path));
                        let wrapped = format!("\n{}\n", pat.html);
                        let (_, parsed_sub, _) = step_tree(&wrapped)?;
                        parsed_sub
                            .into_iter()
                            .map(|mut s| {
                                fn bump(x: &mut HtmlStep, add: usize) {
                                    x.depth += add;
                                    for k in &mut x.kids {
                                        bump(k, add);
                                    }
                                }
                                bump(&mut s, depth + 1);
                                s
                            })
                            .collect()
                    } else {
                        Vec::new()
                    }
                }
                UnitBody::Stmts(kid_path, kunits) => {
                    let kid_stmts = child_stmts_of(&stmts[u.stmt_idx], u.arm_idx);
                    render_block_from_patches(
                        kind,
                        key,
                        kid_stmts,
                        closures,
                        kunits,
                        ind + 2,
                        kid_path,
                        &spath,
                        patches,
                        used_patches,
                        used_attrs,
                        used_conts,
                        depth + 1,
                    )?
                }
                UnitBody::Closure(cl_site, kunits) => {
                    let cl_path = format!("cl{cl_site}");
                    let kid_stmts = &closures[*cl_site].body;
                    render_block_from_patches(
                        kind,
                        key,
                        kid_stmts,
                        closures,
                        kunits,
                        2,
                        &cl_path,
                        &spath,
                        patches,
                        used_patches,
                        used_attrs,
                        used_conts,
                        depth + 1,
                    )?
                }
            };
            out_steps.push(HtmlStep {
                depth,
                attrs,
                text: u.text.clone(),
                cont,
                kids,
            });
            cur_u += 1;
        }
    }
    Ok(out_steps)
}

pub fn bootstrap_all(
    spec: &Spec,
    html: &HtmlSpec,
    templates: &CallTemplates,
) -> Result<(ItemMeta, StepPatches, AlgStats), String> {
    let decls = DeclsCtx::from_spec(spec, templates);
    let mut item_meta = ItemMeta::default();
    let mut patches = StepPatches::default();

    let mut defs: BTreeMap<ItemKey, &AlgDef> = BTreeMap::new();
    let mut rows: BTreeMap<ItemKey, &SdoRowDef> = BTreeMap::new();
    let mut earlies: BTreeMap<ItemKey, &EarlyRow> = BTreeMap::new();

    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Def(a) => {
                    let k = ItemKey::new(&a.id.clause, a.id.idx);
                    defs.insert(k, a);
                }
                TopItem::SdoRow(r) => {
                    let k = ItemKey::new(&r.id.clause, r.id.idx);
                    rows.insert(k, r);
                }
                TopItem::Early(e) => {
                    let k = ItemKey::new(&e.id.clause, e.id.idx);
                    earlies.insert(k, e);
                }
                _ => {}
            }
        }
    }

    let mut stats = AlgStats {
        html_algs: html.algs.len(),
        html_eqs: html.eqs.len(),
        html_early: html.early.len(),
        alg_keys: 0,
        early_keys: 0,
        tmpl_slots: 0,
        tmpl_instances: 0,
        spectec_only_defs: 0,
        spectec_only_rows: 0,
        structural_steps: 0,
        total_html_steps: 0,
        attr_only_steps: 0,
        patches_count: 0,
        structural_eqs: 0,
        structural_early: 0,
    };

    // Track HTML alg templates covered by `/Name` instances
    let mut tmpl_instances: BTreeMap<ItemKey, Vec<(ItemKey, &AlgDef)>> = BTreeMap::new();

    for (key, a) in &defs {
        if key.clause.starts_with("ph-")
            || key.clause.starts_with("sort-")
            || key.clause.starts_with("formal-")
            || key.clause.starts_with("spec-")
        {
            item_meta.items.insert(("spectec_only_def".into(), key.clone()), ItemKindMeta::SpectecOnlyDef);
            stats.spectec_only_defs += 1;
            continue;
        }
        if let Some((tmpl_c, _)) = key.clause.split_once('/') {
            let tmpl_key = ItemKey::new(tmpl_c, key.idx);
            tmpl_instances.entry(tmpl_key).or_default().push((key.clone(), *a));
            item_meta.items.insert(("tmpl_inst".into(), key.clone()), ItemKindMeta::TmplInst);
            stats.tmpl_instances += 1;

            let inst_raw = html
                .instance(&key.clause, key.idx)
                .ok_or_else(|| format!("missing template instance HTML for {}", key.fmt_ref()))?;
            let (base, hsteps, _close) = step_tree(&inst_raw)?;
            let cx = Ctx { d: &decls, closures: &a.closures, depth: 0 };
            let units = render_units_at(&cx, &a.body, 2, "root");
            let mut ast = AlignState::new(&mut patches, "alg", key.clone());
            align_block_with_closures(&mut ast, &a.body, &a.closures, &units, &hsteps, 2, "root", "");
            stats.structural_steps += ast.structural_steps;
            stats.total_html_steps += ast.total_steps;
            stats.attr_only_steps += ast.attr_steps;
            let _ = base;
            continue;
        }

        let ha = html
            .alg_map
            .get(&(key.clause.clone(), key.idx))
            .map(|&i| &html.algs[i])
            .ok_or_else(|| format!("def {} missing in spec.html", key.fmt_ref()))?;
        item_meta.items.insert(
            ("alg".into(), key.clone()),
            ItemKindMeta::Alg { base: ha.base, close: ha.close_indent },
        );
        let cx = Ctx { d: &decls, closures: &a.closures, depth: 0 };
        let units = render_units_at(&cx, &a.body, 2, "root");
        let mut ast = AlignState::new(&mut patches, "alg", key.clone());
        align_block_with_closures(&mut ast, &a.body, &a.closures, &units, &ha.steps, 2, "root", "");
        stats.structural_steps += ast.structural_steps;
        stats.total_html_steps += ast.total_steps;
        stats.attr_only_steps += ast.attr_steps;
    }

    // Handle template base slots (`sec-nativeerror#0`, `sec-typedarray#0`)
    for (tkey, insts) in &tmpl_instances {
        let ha = html
            .alg_map
            .get(&(tkey.clause.clone(), tkey.idx))
            .map(|&i| &html.algs[i])
            .ok_or_else(|| format!("template slot {} missing in spec.html", tkey.fmt_ref()))?;
        let c = html.clauses.iter().find(|c| c.id == tkey.clause).ok_or("missing template clause")?;
        let param = find_template_param(&c.h1).ok_or_else(|| format!("template {} header lacks _P_", tkey.fmt_ref()))?;
        item_meta.items.insert(
            ("tmpl".into(), tkey.clone()),
            ItemKindMeta::Tmpl { param, base: ha.base, close: ha.close_indent },
        );
        stats.tmpl_slots += 1;
        // Anchor template raw HTML to the first instance's canonical SpecTec def!
        let (first_key, first_def) = &insts[0];
        let spec_body = render_stmts_canonical(2, &first_def.body);
        patches.patches.insert(
            ("tmpl".into(), tkey.clone(), first_key.fmt_ref()),
            StepPatch {
                kind: "tmpl".into(),
                key: tkey.clone(),
                path: first_key.fmt_ref(),
                spectec: spec_body,
                html: ha.text.clone(),
            },
        );
    }

    // SDO rows (`form alg` & `form equation`)
    for (key, r) in &rows {
        if key.clause.starts_with("row-") {
            item_meta.items.insert(("spectec_only_row".into(), key.clone()), ItemKindMeta::SpectecOnlyRow);
            stats.spectec_only_rows += 1;
            continue;
        }
        match r.form {
            RowForm::Alg => {
                let ha = html
                    .alg_map
                    .get(&(key.clause.clone(), key.idx))
                    .map(|&i| &html.algs[i])
                    .ok_or_else(|| format!("sdo_row {} missing in spec.html", key.fmt_ref()))?;
                if ha.key_text.as_deref() != r.keys.first().map(|s| s.as_str()) || r.keys.len() != 1 {
                    return Err(format!("sdo_row {} grammar key mismatch", key.fmt_ref()));
                }
                stats.alg_keys += 1;
                item_meta.items.insert(
                    ("row".into(), key.clone()),
                    ItemKindMeta::Row { base: ha.base, close: ha.close_indent },
                );
                let cx = Ctx { d: &decls, closures: &r.closures, depth: 0 };
                let units = render_units_at(&cx, &r.steps, 4, "root");
                let mut ast = AlignState::new(&mut patches, "row", key.clone());
                align_block_with_closures(&mut ast, &r.steps, &r.closures, &units, &ha.steps, 4, "root", "");
                stats.structural_steps += ast.structural_steps;
                stats.total_html_steps += ast.total_steps;
                stats.attr_only_steps += ast.attr_steps;
            }
            RowForm::Equation => {
                let heq = html
                    .eq_map
                    .get(&(key.clause.clone(), key.idx))
                    .map(|&i| &html.eqs[i])
                    .ok_or_else(|| format!("equation {} missing in spec.html", key.fmt_ref()))?;
                item_meta.items.insert(
                    ("eq".into(), key.clone()),
                    ItemKindMeta::Eq { indent: heq.indent },
                );
                let cx = Ctx { d: &decls, closures: &r.closures, depth: 0 };
                let structural = render_equation_line(&cx, r);
                if structural.as_deref() == Some(heq.line_text.as_str()) {
                    stats.structural_eqs += 1;
                } else {
                    patches.patches.insert(
                        ("eq".into(), key.clone(), "body".into()),
                        StepPatch {
                            kind: "eq".into(),
                            key: key.clone(),
                            path: "body".into(),
                            spectec: render_stmts_canonical(4, &r.steps),
                            html: heq.line_text.clone(),
                        },
                    );
                }
            }
        }
    }

    // Early Errors
    for (key, er) in &earlies {
        if key.idx >= 1000 {
            let base = ItemKey::new(&key.clause, key.idx - 1000);
            item_meta.items.insert(("twin".into(), key.clone()), ItemKindMeta::Twin { of: base });
            continue;
        }
        let he = html
            .early_map
            .get(&(key.clause.clone(), key.idx))
            .map(|&i| &html.early[i])
            .ok_or_else(|| format!("early {} missing in spec.html", key.fmt_ref()))?;
        let key_strs: Vec<String> = he.keys.iter().map(|(_, t)| t.clone()).collect();
        if er.keys != key_strs {
            return Err(format!("early {} grammar keys mismatch", key.fmt_ref()));
        }
        stats.early_keys += 1;
        let layout_str = match he.layout {
            crate::html_scan::EarlyLayout::Inline => "inline",
            crate::html_scan::EarlyLayout::Block => "block",
            crate::html_scan::EarlyLayout::Raw => "raw",
        };
        item_meta.items.insert(
            ("early".into(), key.clone()),
            ItemKindMeta::Early { indent: he.indent, layout: layout_str.into() },
        );
        let cx = Ctx { d: &decls, closures: &[], depth: 0 };
        let structural = render_early_body(&cx, er, layout_str, he.indent);
        if layout_str != "raw" && structural == he.text {
            stats.structural_early += 1;
        } else {
            // If raw HTML embeds `<emu-alg>...</emu-alg>` for `Cond::Alg(a)` inside this early row, parameterize it cleanly!
            let mut hbody = he.text.clone();
            for s in &er.sentences {
                if let spectec::ast::EarlySent::SyntaxError { cond: spectec::ast::Cond::And(cs), .. } = s {
                    for c in cs {
                        if let spectec::ast::Cond::Alg(a) = c {
                            let ak = (a.clause.clone(), a.idx);
                            if let Some(&ai) = html.alg_map.get(&ak) {
                                let ha = &html.algs[ai];
                                let needle = format!("<emu-alg>{}</emu-alg>", ha.text);
                                let repl = format!(
                                    "<emu-alg>{ALG_EMBED_PREFIX}{}}}}}</emu-alg>",
                                    ItemKey::new(&a.clause, a.idx).fmt_ref()
                                );
                                hbody = hbody.replace(&needle, &repl);
                            }
                        }
                    }
                }
            }
            patches.patches.insert(
                ("early".into(), key.clone(), "body".into()),
                StepPatch {
                    kind: "early".into(),
                    key: key.clone(),
                    path: "body".into(),
                    spectec: render_early_canonical(er),
                    html: hbody,
                },
            );
        }
    }

    stats.patches_count = patches.patches.len();
    Ok((item_meta, patches, stats))
}

pub fn render_and_check_all(
    spec: &Spec,
    html: &HtmlSpec,
    templates: &CallTemplates,
    item_meta: &ItemMeta,
    patches: &StepPatches,
) -> Result<(Vec<SpliceItem>, AlgStats), String> {
    let decls = DeclsCtx::from_spec(spec, templates);
    let mut defs: BTreeMap<ItemKey, &AlgDef> = BTreeMap::new();
    let mut rows: BTreeMap<ItemKey, &SdoRowDef> = BTreeMap::new();
    let mut earlies: BTreeMap<ItemKey, &EarlyRow> = BTreeMap::new();
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Def(a) => {
                    let k = ItemKey::new(&a.id.clause, a.id.idx);
                    if defs.insert(k.clone(), a).is_some() {
                        return Err(format!("duplicate def {}", k.fmt_ref()));
                    }
                }
                TopItem::SdoRow(r) => {
                    let k = ItemKey::new(&r.id.clause, r.id.idx);
                    if rows.insert(k.clone(), r).is_some() {
                        return Err(format!("duplicate sdo_row {}", k.fmt_ref()));
                    }
                }
                TopItem::Early(e) => {
                    let k = ItemKey::new(&e.id.clause, e.id.idx);
                    if earlies.insert(k.clone(), e).is_some() {
                        return Err(format!("duplicate early {}", k.fmt_ref()));
                    }
                }
                _ => {}
            }
        }
    }

    let mut used_items: BTreeSet<(String, ItemKey)> = BTreeSet::new();
    let mut used_patches: BTreeSet<(String, ItemKey, String)> = BTreeSet::new();
    let mut used_attrs: BTreeSet<(String, ItemKey, String)> = BTreeSet::new();
    let mut used_conts: BTreeSet<(String, ItemKey, String)> = BTreeSet::new();
    let mut splices: Vec<SpliceItem> = Vec::new();
    let mut covered_html_algs: BTreeSet<(String, usize)> = BTreeSet::new();
    let mut covered_html_eqs: BTreeSet<(String, usize)> = BTreeSet::new();
    let mut covered_html_early: BTreeSet<(String, usize)> = BTreeSet::new();
    let mut rendered_alg_bodies: BTreeMap<ItemKey, String> = BTreeMap::new();

    let mut stats = AlgStats {
        html_algs: html.algs.len(),
        html_eqs: html.eqs.len(),
        html_early: html.early.len(),
        alg_keys: 0,
        early_keys: 0,
        tmpl_slots: 0,
        tmpl_instances: 0,
        spectec_only_defs: 0,
        spectec_only_rows: 0,
        structural_steps: 0,
        total_html_steps: 0,
        attr_only_steps: 0,
        patches_count: patches.patches.len(),
        structural_eqs: 0,
        structural_early: 0,
    };

    fn count_steps_info(hs: &[HtmlStep]) -> (usize, usize) {
        let mut tot = 0usize;
        let mut att = 0usize;
        for s in hs {
            tot += 1;
            if s.attrs.is_some() {
                att += 1;
            }
            let (ct, ca) = count_steps_info(&s.kids);
            tot += ct;
            att += ca;
        }
        (tot, att)
    }

    // 1. Render & verify all Defs (`alg`, `tmpl_inst`, `spectec_only_def`)
    for (key, a) in &defs {
        if item_meta.items.contains_key(&("spectec_only_def".into(), key.clone())) {
            used_items.insert(("spectec_only_def".into(), key.clone()));
            stats.spectec_only_defs += 1;
            continue;
        }
        if item_meta.items.contains_key(&("tmpl_inst".into(), key.clone())) {
            used_items.insert(("tmpl_inst".into(), key.clone()));
            stats.tmpl_instances += 1;
            let cx = Ctx { d: &decls, closures: &a.closures, depth: 0 };
            let units = render_units_at(&cx, &a.body, 2, "root");
            let rendered_steps = render_block_from_patches(
                "alg",
                key,
                &a.body,
                &a.closures,
                &units,
                2,
                "root",
                "",
                patches,
                &mut used_patches,
                &mut used_attrs,
                &mut used_conts,
                0,
            )?;
            let want = html
                .instance(&key.clause, key.idx)
                .ok_or_else(|| format!("missing HTML template instance for {}", key.fmt_ref()))?;
            let (base, want_steps, close) = step_tree(&want)?;
            let got = print_step_tree(base, close, &rendered_steps);
            if got != want {
                return Err(format!("template instance {} rendered HTML differs:\ngot:  {got:?}\nwant: {want:?}", key.fmt_ref()));
            }
            let _ = want_steps;
            let (tot, att) = count_steps_info(&rendered_steps);
            stats.total_html_steps += tot;
            stats.attr_only_steps += att;
            continue;
        }
        let Some(ItemKindMeta::Alg { base, close }) = item_meta.items.get(&("alg".into(), key.clone())) else {
            return Err(format!("SpecTec def {} missing in spec/html/item-meta.txt", key.fmt_ref()));
        };
        used_items.insert(("alg".into(), key.clone()));
        let ha = html
            .alg_map
            .get(&(key.clause.clone(), key.idx))
            .map(|&i| &html.algs[i])
            .ok_or_else(|| format!("HTML alg {} not found", key.fmt_ref()))?;
        let cx = Ctx { d: &decls, closures: &a.closures, depth: 0 };
        let units = render_units_at(&cx, &a.body, 2, "root");
        let rendered_steps = render_block_from_patches(
            "alg",
            key,
            &a.body,
            &a.closures,
            &units,
            2,
            "root",
            "",
            patches,
            &mut used_patches,
            &mut used_attrs,
            &mut used_conts,
            0,
        )?;
        let body = print_step_tree(*base, *close, &rendered_steps);
        if body != ha.text {
            return Err(format!(
                "alg {} (spec.html:{}) rendered HTML differs:\ngot:  {body:?}\nwant: {:?}",
                key.fmt_ref(),
                ha.line,
                ha.text
            ));
        }
        let (tot, att) = count_steps_info(&rendered_steps);
        stats.total_html_steps += tot;
        stats.attr_only_steps += att;
        covered_html_algs.insert((key.clause.clone(), key.idx));
        rendered_alg_bodies.insert(key.clone(), body.clone());
        splices.push(SpliceItem {
            start: ha.span.0,
            end: ha.span.1,
            text: body,
            label: format!("alg {}", key.fmt_ref()),
        });
    }

    // 2. Verify & render Template slots (`tmpl @tmpl#idx`)
    for ((tag, tkey), meta_val) in &item_meta.items {
        if tag != "tmpl" {
            continue;
        }
        let ItemKindMeta::Tmpl { param, base, close } = meta_val else { unreachable!() };
        used_items.insert((tag.clone(), tkey.clone()));
        stats.tmpl_slots += 1;
        let ha = html
            .alg_map
            .get(&(tkey.clause.clone(), tkey.idx))
            .map(|&i| &html.algs[i])
            .ok_or_else(|| format!("HTML template alg {} not found", tkey.fmt_ref()))?;
        let mut pat_entry = None;
        for ((pk, pkey, ppath), pat) in &patches.patches {
            if pk == "tmpl" && pkey == tkey {
                pat_entry = Some((ppath.clone(), pat));
                used_patches.insert((pk.clone(), pkey.clone(), ppath.clone()));
                break;
            }
        }
        let Some((anchor_ref, pat)) = pat_entry else {
            return Err(format!("tmpl {} missing @@patch", tkey.fmt_ref()));
        };
        let anchor_key = ItemKey::parse_ref(&anchor_ref)?;
        let anchor_def = defs
            .get(&anchor_key)
            .ok_or_else(|| format!("tmpl {} anchor {} missing in SpecTec", tkey.fmt_ref(), anchor_ref))?;
        let live_st = render_stmts_canonical(2, &anchor_def.body);
        if live_st != pat.spectec {
            return Err(format!("tmpl {} anchor {} SpecTec drifted vs @@spectec", tkey.fmt_ref(), anchor_ref));
        }
        check_can_render_stmts(&pat.spectec, &anchor_def.body, 2)?;
        let (hb, _, hc) = step_tree(&pat.html)?;
        if hb != *base || hc != *close {
            return Err(format!("tmpl {} base/close indent mismatch", tkey.fmt_ref()));
        }
        if pat.html != ha.text {
            return Err(format!("tmpl {} HTML differs from spec.html:{}", tkey.fmt_ref(), ha.line));
        }
        // Check that `instance_alg_text(pat.html, param, Name)` produces every instance!
        for (ikey, _) in &defs {
            if let Some((tc, name)) = ikey.clause.split_once('/') {
                if tc == tkey.clause && ikey.idx == tkey.idx {
                    let instantiated = instance_alg_text(&pat.html, param, name);
                    let want = html.instance(&ikey.clause, ikey.idx).unwrap();
                    if instantiated != want {
                        return Err(format!("tmpl {} instantiating `{name}` does not match HTML instance", tkey.fmt_ref()));
                    }
                }
            }
        }
        covered_html_algs.insert((tkey.clause.clone(), tkey.idx));
        splices.push(SpliceItem {
            start: ha.span.0,
            end: ha.span.1,
            text: pat.html.clone(),
            label: format!("tmpl {}", tkey.fmt_ref()),
        });
    }

    // 3. Render & verify SDO rows (`row`, `eq`, `spectec_only_row`)
    for (key, r) in &rows {
        if item_meta.items.contains_key(&("spectec_only_row".into(), key.clone())) {
            used_items.insert(("spectec_only_row".into(), key.clone()));
            stats.spectec_only_rows += 1;
            continue;
        }
        match r.form {
            RowForm::Alg => {
                let Some(ItemKindMeta::Row { base, close }) = item_meta.items.get(&("row".into(), key.clone())) else {
                    return Err(format!("SpecTec sdo_row {} missing in item-meta.txt", key.fmt_ref()));
                };
                used_items.insert(("row".into(), key.clone()));
                let ha = html
                    .alg_map
                    .get(&(key.clause.clone(), key.idx))
                    .map(|&i| &html.algs[i])
                    .ok_or_else(|| format!("HTML row {} not found", key.fmt_ref()))?;
                // Check grammar key 1-to-1!
                let (kspan_start, kspan_end) = ha
                    .key_span
                    .ok_or_else(|| format!("HTML row {} missing preceding <emu-grammar> key", key.fmt_ref()))?;
                if r.keys.len() != 1 || Some(&r.keys[0]) != ha.key_text.as_ref() {
                    return Err(format!("row {} grammar key differs from spec.html", key.fmt_ref()));
                }
                stats.alg_keys += 1;
                splices.push(SpliceItem {
                    start: kspan_start,
                    end: kspan_end,
                    text: r.keys[0].clone(),
                    label: format!("alg_key {}", key.fmt_ref()),
                });

                let cx = Ctx { d: &decls, closures: &r.closures, depth: 0 };
                let units = render_units_at(&cx, &r.steps, 4, "root");
                let rendered_steps = render_block_from_patches(
                    "row",
                    key,
                    &r.steps,
                    &r.closures,
                    &units,
                    4,
                    "root",
                    "",
                    patches,
                    &mut used_patches,
                    &mut used_attrs,
                    &mut used_conts,
                    0,
                )?;
                let body = print_step_tree(*base, *close, &rendered_steps);
                if body != ha.text {
                    return Err(format!(
                        "row {} (spec.html:{}) rendered HTML differs:\ngot:  {body:?}\nwant: {:?}",
                        key.fmt_ref(),
                        ha.line,
                        ha.text
                    ));
                }
                let (tot, att) = count_steps_info(&rendered_steps);
                stats.total_html_steps += tot;
                stats.attr_only_steps += att;
                covered_html_algs.insert((key.clause.clone(), key.idx));
                splices.push(SpliceItem {
                    start: ha.span.0,
                    end: ha.span.1,
                    text: body,
                    label: format!("row {}", key.fmt_ref()),
                });
            }
            RowForm::Equation => {
                let Some(ItemKindMeta::Eq { indent }) = item_meta.items.get(&("eq".into(), key.clone())) else {
                    return Err(format!("SpecTec equation {} missing in item-meta.txt", key.fmt_ref()));
                };
                used_items.insert(("eq".into(), key.clone()));
                let heq = html
                    .eq_map
                    .get(&(key.clause.clone(), key.idx))
                    .map(|&i| &html.eqs[i])
                    .ok_or_else(|| format!("HTML equation {} not found", key.fmt_ref()))?;
                let pkey = ("eq".into(), key.clone(), "body".into());
                let line_txt = if let Some(pat) = patches.patches.get(&pkey) {
                    used_patches.insert(pkey);
                    let live = render_stmts_canonical(4, &r.steps);
                    if live != pat.spectec {
                        return Err(format!("eq {} SpecTec drifted vs @@spectec", key.fmt_ref()));
                    }
                    check_can_render_stmts(&pat.spectec, &r.steps, 4)?;
                    pat.html.clone()
                } else {
                    stats.structural_eqs += 1;
                    let cx = Ctx { d: &decls, closures: &r.closures, depth: 0 };
                    render_equation_line(&cx, r)
                        .ok_or_else(|| format!("eq {} failed structural equation rendering", key.fmt_ref()))?
                };
                let full_raw = format!("\n{}{line_txt}\n{}", " ".repeat(indent + 2), " ".repeat(*indent));
                if full_raw != heq.text {
                    return Err(format!(
                        "eq {} (spec.html:{}) rendered HTML differs:\ngot:  {full_raw:?}\nwant: {:?}",
                        key.fmt_ref(),
                        heq.line,
                        heq.text
                    ));
                }
                covered_html_eqs.insert((key.clause.clone(), key.idx));
                splices.push(SpliceItem {
                    start: heq.span.0,
                    end: heq.span.1,
                    text: full_raw,
                    label: format!("eq {}", key.fmt_ref()),
                });
            }
        }
    }

    // 4. Verify & render Early Errors (`early`, `twin`)
    for (key, er) in &earlies {
        if key.idx >= 1000 {
            let Some(ItemKindMeta::Twin { of }) = item_meta.items.get(&("twin".into(), key.clone())) else {
                return Err(format!("early twin {} missing in item-meta.txt", key.fmt_ref()));
            };
            used_items.insert(("twin".into(), key.clone()));
            if !earlies.contains_key(of) {
                return Err(format!("early twin {} base {} missing", key.fmt_ref(), of.fmt_ref()));
            }
            continue;
        }
        let Some(ItemKindMeta::Early { indent, layout }) = item_meta.items.get(&("early".into(), key.clone())) else {
            return Err(format!("SpecTec early {} missing in item-meta.txt", key.fmt_ref()));
        };
        used_items.insert(("early".into(), key.clone()));
        let he = html
            .early_map
            .get(&(key.clause.clone(), key.idx))
            .map(|&i| &html.early[i])
            .ok_or_else(|| format!("HTML early {} not found", key.fmt_ref()))?;
        if er.keys.len() != he.keys.len() {
            return Err(format!("early {} key count differs", key.fmt_ref()));
        }
        for (ek, ((ks, ke), hk)) in er.keys.iter().zip(he.keys.iter()) {
            if ek != hk {
                return Err(format!("early {} key differs from spec.html", key.fmt_ref()));
            }
            splices.push(SpliceItem {
                start: *ks,
                end: *ke,
                text: ek.clone(),
                label: format!("early_key {}", key.fmt_ref()),
            });
        }
        stats.early_keys += 1;

        let pkey = ("early".into(), key.clone(), "body".into());
        let body_raw = if let Some(pat) = patches.patches.get(&pkey) {
            used_patches.insert(pkey);
            let live = render_early_canonical(er);
            if live != pat.spectec {
                return Err(format!("early {} SpecTec drifted vs @@spectec", key.fmt_ref()));
            }
            // Also verify @@spectec parses cleanly back into EarlyRow sentences!
            let wrapped = format!(
                "{}",
                print_early_row(er).replace(&live, &pat.spectec)
            );
            let sf = parse_str("early_patch.spectec", &wrapped)?;
            let Some(TopItem::Early(parsed_er)) = sf.items.into_iter().next() else {
                return Err("failed to parse early patch".into());
            };
            if &parsed_er != *er {
                return Err(format!("early {} parsed @@spectec differs", key.fmt_ref()));
            }
            // Substitute any embedded `{{ALG:@clause}}` from dynamically rendered `defs`!
            let mut txt = pat.html.clone();
            while let Some(pos) = txt.find(ALG_EMBED_PREFIX) {
                let rest = &txt[pos + ALG_EMBED_PREFIX.len()..];
                let end = rest.find("}}").ok_or("unclosed ALG placeholder")?;
                let ref_s = &rest[..end];
                let ak = ItemKey::parse_ref(ref_s)?;
                let abody = rendered_alg_bodies
                    .get(&ak)
                    .ok_or_else(|| format!("embedded alg {} not rendered", ak.fmt_ref()))?;
                let full_ph = format!("{ALG_EMBED_PREFIX}{ref_s}}}");
                // Note `}` + `}` matches two closing braces
                let full_ph = format!("{full_ph}}}");
                txt = txt.replace(&full_ph, abody);
            }
            txt
        } else {
            stats.structural_early += 1;
            let cx = Ctx { d: &decls, closures: &[], depth: 0 };
            render_early_body(&cx, er, layout, *indent)
        };
        if body_raw != he.text {
            return Err(format!(
                "early {} (spec.html:{}) rendered HTML differs:\ngot:  {body_raw:?}\nwant: {:?}",
                key.fmt_ref(),
                he.line,
                he.text
            ));
        }
        covered_html_early.insert((key.clause.clone(), key.idx));
        splices.push(SpliceItem {
            start: he.span.0,
            end: he.span.1,
            text: body_raw,
            label: format!("early {}", key.fmt_ref()),
        });
    }

    // 5. Verify 100% coverage & zero unused metadata!
    for ha in &html.algs {
        if !covered_html_algs.contains(&(ha.clause.clone(), ha.idx)) {
            return Err(format!("spec.html alg {}#{} (line {}) not covered by SpecTec", ha.clause, ha.idx, ha.line));
        }
    }
    for heq in &html.eqs {
        if !covered_html_eqs.contains(&(heq.clause.clone(), heq.idx)) {
            return Err(format!("spec.html eq {}#{} (line {}) not covered by SpecTec", heq.clause, heq.idx, heq.line));
        }
    }
    for he in &html.early {
        if !covered_html_early.contains(&(he.clause.clone(), he.idx)) {
            return Err(format!("spec.html early {}#{} (line {}) not covered by SpecTec", he.clause, he.idx, he.line));
        }
    }

    let def_items: BTreeSet<_> = item_meta.items.keys().cloned().collect();
    let def_patches: BTreeSet<_> = patches.patches.keys().cloned().collect();
    let def_attrs: BTreeSet<_> = patches.attrs.keys().cloned().collect();
    let def_conts: BTreeSet<_> = patches.conts.keys().cloned().collect();
    check_all_used(&def_items, &used_items, "item-meta")?;
    check_all_used(&def_patches, &used_patches, "step-patch")?;
    check_all_used(&def_attrs, &used_attrs, "step-attr")?;
    check_all_used(&def_conts, &used_conts, "step-cont")?;

    // Compute exact structural step count (total_html_steps - patched steps)
    let mut patched_html_steps = 0usize;
    for (k, _, _) in &used_patches {
        if k == "alg" || k == "row" {
            // count steps in pat.html
        }
    }
    for pat in patches.patches.values() {
        if (pat.kind == "alg" || pat.kind == "row") && pat.html != "<none>" {
            let wrapped = format!("\n{}\n", pat.html);
            if let Ok((_, ps, _)) = step_tree(&wrapped) {
                let (t, _) = count_steps_info(&ps);
                patched_html_steps += t;
            }
        }
    }
    stats.structural_steps = stats.total_html_steps.saturating_sub(patched_html_steps);
    stats.attr_only_steps = used_attrs.len();
    let _ = print_sdo_row;
    Ok((splices, stats))
}
