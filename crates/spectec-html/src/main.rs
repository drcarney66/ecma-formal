//! `spectec-html`: bidirectional SpecTec <-> `spec.html` algorithms & grammars bijection.

use spectec::ast::TopItem;
use spectec::parse::load_spec_dir;
use spectec_html::alg_biject::{bootstrap_all, render_and_check_all};
use spectec_html::alg_render::{render_early_body, render_equation_line, render_units_at, Ctx, DeclsCtx};
use spectec_html::grammar_biject::{
    bootstrap_grammar, check_grammar_backward, render_grammar_splices, render_rule_exact,
};
use spectec_html::html_scan::{HtmlSpec, SpliceItem};
use spectec_html::meta::{CallTemplates, GrammarMeta, ItemMeta, StepPatches};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn usage() -> &'static str {
    "usage: spectec-html [--spec-dir=DIR] [--meta-dir=DIR] [--spec=FILE] (bootstrap | check [--json=FILE] | render-spec --out=FILE | render-clause --clause=ID)"
}

fn load_all(spec_dir: &Path, html_path: &Path) -> Result<(spectec::ast::Spec, HtmlSpec), String> {
    let spec = load_spec_dir(spec_dir)?;
    let html_src = std::fs::read_to_string(html_path).map_err(|e| format!("{}: {e}", html_path.display()))?;
    let html = HtmlSpec::scan(html_src)?;
    Ok((spec, html))
}

fn cmd_bootstrap(spec_dir: &Path, meta_dir: &Path, html_path: &Path) -> Result<(), String> {
    let (spec, html) = load_all(spec_dir, html_path)?;
    std::fs::create_dir_all(meta_dir).map_err(|e| format!("{}: {e}", meta_dir.display()))?;
    let call_path = meta_dir.join("call-templates.txt");
    let templates = CallTemplates::load(&call_path)?;
    let (gmeta, gstats) = bootstrap_grammar(&spec, &html)?;
    gmeta.save(&meta_dir.join("grammar-meta.txt"))?;
    let (imeta, patches, astats) = bootstrap_all(&spec, &html, &templates)?;
    imeta.save(&meta_dir.join("item-meta.txt"))?;
    patches.save(&meta_dir.join("step-patches.txt"))?;
    println!(
        "ok  bootstrap: {} grammar blocks ({} rule overrides), {} algs, {} eqs, {} early rules; {}/{} steps matched structurally ({} attr-only, {} patches)",
        gstats.html_blocks,
        gstats.rule_overrides,
        astats.html_algs,
        astats.html_eqs,
        astats.html_early,
        astats.structural_steps,
        astats.total_html_steps,
        astats.attr_only_steps,
        astats.patches_count
    );
    Ok(())
}

fn cmd_check(spec_dir: &Path, meta_dir: &Path, html_path: &Path, json_out: Option<&Path>) -> Result<(), String> {
    let (spec, html) = load_all(spec_dir, html_path)?;
    let templates = CallTemplates::load(&meta_dir.join("call-templates.txt"))?;
    let gmeta = GrammarMeta::load(&meta_dir.join("grammar-meta.txt"))?;
    let imeta = ItemMeta::load(&meta_dir.join("item-meta.txt"))?;
    let patches = StepPatches::load(&meta_dir.join("step-patches.txt"))?;

    let gstats = check_grammar_backward(&spec, &html, &gmeta)?;
    let (gsplices, _, _, _) = render_grammar_splices(&spec, &html, &gmeta)?;
    let (asplices, astats) = render_and_check_all(&spec, &html, &templates, &imeta, &patches)?;

    let mut all_splices: Vec<SpliceItem> = gsplices
        .into_iter()
        .map(|(start, end, text, label)| SpliceItem { start, end, text, label })
        .collect();
    all_splices.extend(asplices);

    let regenerated = html.splice(all_splices)?;
    if regenerated != html.src {
        return Err("spliced spec.html differs from input spec.html".into());
    }

    let pct_steps = if astats.total_html_steps == 0 {
        100.0
    } else {
        100.0 * astats.structural_steps as f64 / astats.total_html_steps as f64
    };
    let pct_rules = if gstats.total_rules == 0 {
        100.0
    } else {
        100.0 * (gstats.total_rules - gstats.rule_overrides) as f64 / gstats.total_rules as f64
    };

    println!(
        "ok  grammars: {}/{} HTML blocks ({} spectec-only JSON), {}/{} rules structural ({} overrides, {:.1}%)",
        gstats.html_blocks,
        gstats.html_blocks,
        gstats.spectec_only_blocks,
        gstats.total_rules - gstats.rule_overrides,
        gstats.total_rules,
        gstats.rule_overrides,
        pct_rules
    );
    println!(
        "ok  algorithms: {} HTML algs ({} template slots / {} instances), {} eqs ({} structural), {} early ({} structural), {} alg keys, {} early keys, {} spectec-only defs, {} spectec-only rows",
        astats.html_algs,
        astats.tmpl_slots,
        astats.tmpl_instances,
        astats.html_eqs,
        astats.structural_eqs,
        astats.html_early,
        astats.structural_early,
        astats.alg_keys,
        astats.early_keys,
        astats.spectec_only_defs,
        astats.spectec_only_rows
    );
    println!(
        "ok  steps: {}/{} HTML steps rendered structurally ({:.1}%, {} attr-only, {} patches)",
        astats.structural_steps,
        astats.total_html_steps,
        pct_steps,
        astats.attr_only_steps,
        astats.patches_count
    );
    println!(
        "ok  spec.html bijection: 0 problems ({} bytes verified byte-for-byte via splice)",
        regenerated.len()
    );

    if let Some(jp) = json_out {
        let json = format!(
            "{{\n  \"html_blocks\": {},\n  \"rule_overrides\": {},\n  \"html_algs\": {},\n  \"html_eqs\": {},\n  \"html_early\": {},\n  \"alg_keys\": {},\n  \"early_keys\": {},\n  \"structural_steps\": {},\n  \"total_html_steps\": {},\n  \"patches\": {},\n  \"spec_bytes\": {}\n}}\n",
            gstats.html_blocks,
            gstats.rule_overrides,
            astats.html_algs,
            astats.html_eqs,
            astats.html_early,
            astats.alg_keys,
            astats.early_keys,
            astats.structural_steps,
            astats.total_html_steps,
            astats.patches_count,
            regenerated.len()
        );
        std::fs::write(jp, json).map_err(|e| format!("{}: {e}", jp.display()))?;
    }
    Ok(())
}

fn cmd_render_spec(spec_dir: &Path, meta_dir: &Path, html_path: &Path, out_path: &Path) -> Result<(), String> {
    let (spec, html) = load_all(spec_dir, html_path)?;
    let templates = CallTemplates::load(&meta_dir.join("call-templates.txt"))?;
    let gmeta = GrammarMeta::load(&meta_dir.join("grammar-meta.txt"))?;
    let imeta = ItemMeta::load(&meta_dir.join("item-meta.txt"))?;
    let patches = StepPatches::load(&meta_dir.join("step-patches.txt"))?;

    let (gsplices, _, _, _) = render_grammar_splices(&spec, &html, &gmeta)?;
    let (asplices, _) = render_and_check_all(&spec, &html, &templates, &imeta, &patches)?;
    let mut all_splices: Vec<SpliceItem> = gsplices
        .into_iter()
        .map(|(start, end, text, label)| SpliceItem { start, end, text, label })
        .collect();
    all_splices.extend(asplices);

    let out = html.splice(all_splices)?;
    std::fs::write(out_path, out).map_err(|e| format!("{}: {e}", out_path.display()))?;
    println!("ok  rendered spec written to {}", out_path.display());
    Ok(())
}

fn cmd_render_clause(spec_dir: &Path, meta_dir: &Path, clause: &str) -> Result<(), String> {
    let spec = load_spec_dir(spec_dir)?;
    let templates = CallTemplates::load(&meta_dir.join("call-templates.txt"))?;
    let decls = DeclsCtx::from_spec(&spec, &templates);
    let mut found = 0usize;
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Def(a) if a.id.clause == clause => {
                    found += 1;
                    let cx = Ctx { d: &decls, closures: &a.closures, depth: 0 };
                    let units = render_units_at(&cx, &a.body, 2, "root");
                    fn print_u(u: &[spectec_html::alg_render::RenderUnit], ind: usize) {
                        for x in u {
                            println!("{}1. {}", " ".repeat(ind), x.text);
                            match &x.kids {
                                spectec_html::alg_render::UnitBody::None => {}
                                spectec_html::alg_render::UnitBody::Stmts(_, ks)
                                | spectec_html::alg_render::UnitBody::Closure(_, ks) => print_u(ks, ind + 2),
                            }
                        }
                    }
                    println!("<emu-alg id=\"{}\">", a.id.clause);
                    print_u(&units, 2);
                    println!("</emu-alg>\n");
                }
                TopItem::SdoRow(r) if r.id.clause == clause => {
                    found += 1;
                    let cx = Ctx { d: &decls, closures: &r.closures, depth: 0 };
                    if matches!(r.form, spectec::ast::RowForm::Equation) {
                        if let Some(ln) = render_equation_line(&cx, r) {
                            println!("<li>{ln}</li>");
                        }
                    } else {
                        println!("<emu-grammar>{}</emu-grammar>", r.keys.join(" / "));
                        let units = render_units_at(&cx, &r.steps, 4, "root");
                        for x in &units {
                            println!("  1. {}", x.text);
                        }
                    }
                }
                TopItem::Early(e) if e.id.clause == clause => {
                    found += 1;
                    let cx = Ctx { d: &decls, closures: &[], depth: 0 };
                    println!("<li>{}</li>", render_early_body(&cx, e, "inline", 0));
                }
                TopItem::Block(b) if b.clause == clause => {
                    found += 1;
                    println!("<emu-grammar type=\"definition\">");
                    for lhs in &b.rules {
                        for ff in &spec.files {
                            for it in &ff.items {
                                if let TopItem::Rule(r) = it {
                                    if r.grammar == b.grammar && &r.lhs == lhs {
                                        if let Ok(txt) = render_rule_exact(r) {
                                            println!("{txt}\n");
                                        }
                                    }
                                }
                            }
                        }
                    }
                    println!("</emu-grammar>");
                }
                _ => {}
            }
        }
    }
    if found == 0 {
        return Err(format!("no clause `{clause}` found"));
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut spec_dir = PathBuf::from("spec/spectec");
    let mut meta_dir = PathBuf::from("spec/html");
    let mut html_path = PathBuf::from("external/ecma262/spec.html");
    let mut json_out: Option<PathBuf> = None;
    let mut out_path: Option<PathBuf> = None;
    let mut clause: Option<String> = None;
    let mut cmd: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        if let Some(v) = a.strip_prefix("--spec-dir=") {
            spec_dir = v.into();
        } else if a == "--spec-dir" && i + 1 < args.len() {
            i += 1;
            spec_dir = args[i].clone().into();
        } else if let Some(v) = a.strip_prefix("--meta-dir=") {
            meta_dir = v.into();
        } else if a == "--meta-dir" && i + 1 < args.len() {
            i += 1;
            meta_dir = args[i].clone().into();
        } else if let Some(v) = a.strip_prefix("--spec=") {
            html_path = v.into();
        } else if a == "--spec" && i + 1 < args.len() {
            i += 1;
            html_path = args[i].clone().into();
        } else if let Some(v) = a.strip_prefix("--json=") {
            json_out = Some(v.into());
        } else if a == "--json" && i + 1 < args.len() {
            i += 1;
            json_out = Some(args[i].clone().into());
        } else if let Some(v) = a.strip_prefix("--out=") {
            out_path = Some(v.into());
        } else if a == "--out" && i + 1 < args.len() {
            i += 1;
            out_path = Some(args[i].clone().into());
        } else if let Some(v) = a.strip_prefix("--clause=") {
            clause = Some(v.into());
        } else if a == "--clause" && i + 1 < args.len() {
            i += 1;
            clause = Some(args[i].clone());
        } else if !a.starts_with('-') && cmd.is_none() {
            cmd = Some(a.clone());
        } else {
            eprintln!("{}", usage());
            return ExitCode::from(2);
        }
        i += 1;
    }

    let res = match cmd.as_deref() {
        Some("bootstrap") => cmd_bootstrap(&spec_dir, &meta_dir, &html_path),
        Some("check") => cmd_check(&spec_dir, &meta_dir, &html_path, json_out.as_deref()),
        Some("render-spec") => match out_path.as_deref() {
            Some(o) => cmd_render_spec(&spec_dir, &meta_dir, &html_path, o),
            None => {
                eprintln!("{}", usage());
                return ExitCode::from(2);
            }
        },
        Some("render-clause") => match clause.as_deref() {
            Some(c) => cmd_render_clause(&spec_dir, &meta_dir, c),
            None => {
                eprintln!("{}", usage());
                return ExitCode::from(2);
            }
        },
        _ => {
            eprintln!("{}", usage());
            return ExitCode::from(2);
        }
    };

    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("spectec-html error: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spectec::ast::{Spec, Stmt};
    use spectec::parse::parse_str;
    use spectec_html::alg_render::{render_equation_line, DeclsCtx};

    fn sample_pair() -> (Spec, HtmlSpec, CallTemplates, GrammarMeta, ItemMeta, StepPatches) {
        let g_src = "\
grammar lexical

rule lexical |DemoDigit| [] :: one_of {
  row [\"0\", \"1\"]
}

block lexical @sec-demo main [|DemoDigit|]
";
        let a_src = "\
def @sec-demo-op \"DemoOp\" (kind ao params [x : Number] -> Boolean) vars [x] {
  if x == 1 -> return true
  return false
}
";
        let gfile = parse_str("g.spectec", g_src).unwrap();
        let afile = parse_str("a.spectec", a_src).unwrap();
        let spec = Spec { files: vec![gfile, afile] };

        let html_src = concat!(
            "<emu-clause id=\"sec-demo\">\n",
            "  <h1>Demo Grammar</h1>\n",
            "  <emu-grammar type=\"definition\">\n",
            "    DemoDigit :: one of\n",
            "      `0` `1`\n",
            "  </emu-grammar>\n",
            "</emu-clause>\n",
            "<emu-clause id=\"sec-demo-op\" type=\"abstract operation\">\n",
            "  <h1>DemoOp ( _x_: a Number ): a Boolean</h1>\n",
            "  <emu-alg>\n",
            "    1. If _x_ = 1, return *true*.\n",
            "    1. Return *false*.\n",
            "  </emu-alg>\n",
            "</emu-clause>\n",
        );
        let html = HtmlSpec::scan(html_src.to_string()).unwrap();
        let templates = CallTemplates::default();
        let (gmeta, _) = bootstrap_grammar(&spec, &html).unwrap();
        let (imeta, patches, _) = bootstrap_all(&spec, &html, &templates).unwrap();
        (spec, html, templates, gmeta, imeta, patches)
    }

    #[test]
    fn roundtrip_clean_and_detect_mutation_on_both_sides() {
        let (mut spec, mut html, templates, gmeta, imeta, mut patches) = sample_pair();
        assert!(patches.patches.is_empty(), "expected 0 step patches on structural match, got {:?}", patches.patches);
        assert!(gmeta.overrides.is_empty(), "expected 0 grammar overrides");

        // 1. Clean check passes and splices identically
        let (gs, _, _, _) = render_grammar_splices(&spec, &html, &gmeta).unwrap();
        let (as_, _) = render_and_check_all(&spec, &html, &templates, &imeta, &patches).unwrap();
        let mut items: Vec<SpliceItem> = gs.into_iter().map(|(s, e, t, l)| SpliceItem { start: s, end: e, text: t, label: l }).collect();
        items.extend(as_);
        assert_eq!(html.splice(items).unwrap(), html.src);

        // 2. Mutating an unpatched step in Spec changes rendered HTML AND fails check against spec.html!
        if let TopItem::Def(ref mut def) = spec.files[1].items[0] {
            def.body[1] = Stmt::Ret(Some(spectec::ast::Expr::Val(spectec::ast::ValLit::Bool(true))));
        }
        assert!(render_and_check_all(&spec, &html, &templates, &imeta, &patches).is_err());

        // Fix Spec back and test patching drift detection:
        if let TopItem::Def(ref mut def) = spec.files[1].items[0] {
            def.body[1] = Stmt::Ret(Some(spectec::ast::Expr::Val(spectec::ast::ValLit::Bool(false))));
        }
        patches.patches.insert(
            ("alg".into(), spectec_html::meta::ItemKey::new("sec-demo-op", 0), "root:0..1".into()),
            spectec_html::meta::StepPatch {
                kind: "alg".into(),
                key: spectec_html::meta::ItemKey::new("sec-demo-op", 0),
                path: "root:0..1".into(),
                spectec: "  return *wrong*".into(),
                html: "1. If _x_ = 1, return *true*.".into(),
            },
        );
        assert!(render_and_check_all(&spec, &html, &templates, &imeta, &patches).is_err());
        patches.patches.clear();

        // 3. Mutating spec.html causes check to fail immediately!
        html.algs[0].text = html.algs[0].text.replace("*false*", "*true*");
        assert!(render_and_check_all(&spec, &html, &templates, &imeta, &patches).is_err());
        html.blocks[0].text = html.blocks[0].text.replace("`0` `1`", "`0` `2`");
        assert!(check_grammar_backward(&spec, &html, &gmeta).is_err());

        let _ = (DeclsCtx::from_spec(&spec, &templates), render_equation_line);
    }
}
