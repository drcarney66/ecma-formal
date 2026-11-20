//! `spec-gen --spec SPEC.HTML <command>`: ECMA-262's algorithm notation as data.
//!
//! Commands:
//!   report      coverage, ambiguity and residue figures
//!   roundtrip   print(parse(t)) = t on every step, algorithm body, equation, early-error bullet and emu-table; exit 1 otherwise
//!   steps       one line per step: class, clause, path, text; an equation SDO bullet as step 1
//!   calls       one line per algorithm: sec-id, index, operation, row key, spec-named callees, execution-context forms
//!   meanings    the built-in phrase meanings against their templates' holes and choices
//!   early       Early Errors rules: counts and parse coverage (-v: every bullet not fully structured; -r: the rows' keys)
//!   tables      every emu-table printed back: counts by kind, type-phrase parse rate (-v: each table, unparsed cells)
//!   host        host and implementation requirements by class and clause (-v: each sentence)
//!   memmodel    section 29 outside its algorithms: coverage per clause, round trip
//!   residue     the residue by channel (-lines: the ratchet file; -check FILE: fail on a line FILE lacks;
//!               -permanent: the permanent file; -check-permanent FILE: fail on a difference)
//!   asserts     the Assert and `!` sites by class, and the rows not formal or `!` (-all: every row,
//!               the sites file; -lines: the open rows, the ratchet file; -check FILE: fail on an open
//!               row FILE lacks; -check-all FILE: fail on a difference from -all)
//!   types       the steps not typed by their headers, by kind (-lines: the ratchet file; -check FILE:
//!               fail on a line FILE lacks; -esmeta [FILE]: by algorithm against ESMeta's ignore list,
//!               by default esmeta-ignore.json beside spec.html; -opaque: the header sorts taken as any value;
//!               -cover: sites and variables by precision, as written and under the proposed rules;
//!               -decls: the declarations; -impls: method clauses against their traits; -within: the
//!               sound mode, every site not within the type it needs, slots narrowed along each path;
//!               -dyn: those sites, the dyn ratchet file; -check-dyn FILE: fail on a line FILE lacks)
//!   errata      the errata file: per erratum its resolution, where a literal one stops, its spec-issue
//!               reports (-check FILE: fail on a difference)
//!   lr1         the syntactic grammar's LR(1) automaton, parameters expanded: sizes and conflicts
//!               grouped by token and productions (-annexb: with Annex B's syntactic overlays; -v: every state)
//!   divmode     the div/regexp mode M checked over every instance of lr1's expansion from a goal
//!               (-goal Script|Module, -annexb, -v: every failure)

mod ast;
mod asserts;
mod checks;
mod classify;
mod conv;
mod data;
mod decls;
mod divmode;
mod ids;
mod early;
mod engine;
mod grammar;
mod header;
mod host;
mod lean;
mod lean_early;
mod lean_examples;
mod lean_host;
mod lean_memmodel;
mod lean_realm;
mod lean_tables;
mod lr1;
mod overlay;
mod sig;
mod memmodel;
mod print;
mod realm;
mod residue;
mod spec;
mod stops;
mod tables;
#[cfg(test)]
mod tests;
mod text;
mod token;
mod tydecls;
mod tylang;
mod types;

use classify::{classify, print, Class};
use std::collections::{BTreeMap, HashMap};
use std::process::ExitCode;

struct Args {
    spec: String,
    overlay: Option<String>,
    cmd: String,
    rest: Vec<String>,
}

fn args() -> Result<Args, String> {
    let mut spec = None;
    let mut overlay = None;
    let mut pos = Vec::new();
    for a in std::env::args().skip(1) {
        if let Some(v) = a.strip_prefix("--overlay=") {
            overlay = Some(v.to_string());
        } else if let Some(v) = a.strip_prefix("--spec=") {
            spec = Some(v.to_string());
        } else {
            pos.push(a);
        }
    }
    let spec = spec.ok_or("missing --spec=SPEC.HTML")?;
    if pos.is_empty() {
        return Err("missing command (report, roundtrip, steps, early, tables)".into());
    }
    let cmd = pos.remove(0);
    Ok(Args { spec, overlay, cmd, rest: pos })
}

fn pct(a: usize, b: usize) -> String {
    format!("{:.1}%", 100.0 * a as f64 / b.max(1) as f64)
}

fn run() -> Result<bool, String> {
    let a = args()?;
    let html = std::fs::read_to_string(&a.spec).map_err(|e| format!("{}: {e}", a.spec))?;
    if a.cmd == "divmode" {
        return divmode::run(&html, &a.rest);
    }
    if a.cmd == "lr1" {
        return lr1::run(&html, &a.rest);
    }
    SPEC.with(|s| *s.borrow_mut() = a.spec.clone());
    let mut sp = spec::scan(&html)?;
    let ov = match &a.overlay {
        Some(d) => overlay::read(d)?,
        None => overlay::Overlay::default(),
    };
    overlay::patch(&mut sp, &ov)?;
    let g = grammar::Grammar::new(ov)?;
    match a.cmd.as_str() {
        "steps" => {
            let rows = classify(&sp, &g);
            for r in &rows {
                let (num, cid) = r.alg.clause.map(|c| (sp.clauses[c].number.as_str(), sp.clauses[c].id.as_str())).unwrap_or(("-", "-"));
                println!("{:?}\t{}\t{}\t{}\t{}", r.class, num, cid, r.path, r.step.text);
            }
            for e in classify::classify_eqs(&sp, &g) {
                let c = &sp.clauses[e.eq.clause];
                println!("{:?}\t{}\t{}\t1\t{}", e.class, c.number, c.id, e.eq.text);
            }
            Ok(true)
        }
        "calls" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            for l in calls(&html, &sp, &dt) {
                println!("{l}");
            }
            Ok(true)
        }
        "roundtrip" => roundtrip(&sp, &g),
        "meanings" => {
            print!("{}", conv::meanings(&g));
            Ok(true)
        }
        "wiring" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            let d = &dt.decls;
            let mut seen = std::collections::BTreeSet::new();
            for (p, text, why) in &d.wiring {
                if seen.insert((*p, text, why)) {
                    println!("{}\t{}\t{}", d.prims.name(*p), why.as_deref().unwrap_or("wired"), text);
                }
            }
            let wired = seen.iter().filter(|x| x.2.is_none()).count();
            println!("prose primitive sites: {}, wired {wired}, unwired {}", seen.len(), seen.len() - wired);
            for e in d.sig_errors.iter().cloned().chain(sig::phrases(&g, d)) {
                println!("signature: {e}");
            }
            Ok(true)
        }
        "tables" => {
            let rows = classify(&sp, &g);
            let mut dt = data::build(&html, &sp, &g, &rows);
            let ts = tables::build(&html, &sp, &g, &mut dt);
            let alg = |k: usize| alg_body(&sp, &dt, k);
            let pr = tables::Pr { d: &dt.decls, alg: &alg };
            Ok(tables::report(&sp, &pr, &ts, a.rest.iter().any(|x| x == "-v")))
        }
        "emit" => {
            let out = a.rest.iter().find_map(|x| x.strip_prefix("--out=")).ok_or("emit needs --out=DIR")?;
            let only: Option<Vec<String>> = a.rest.iter().find_map(|x| x.strip_prefix("--only=")).map(|x| x.split(',').map(str::to_string).collect());
            for m in emit(&html, &sp, &g, std::path::Path::new(out), only.as_deref())?.0 {
                println!("{m}");
            }
            Ok(true)
        }
        "modules" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            for (m, ds) in lean::modules(&sp, &dt) {
                for d in ds {
                    println!("{m}\t{}\t{}\t{}", d.name, sp.clauses[d.alg.clause].number, d.steps);
                }
            }
            Ok(true)
        }
        "overlay" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            for p in &g.overlay.prims {
                println!("primitive {} ({}): {}\n    {}", p.name, p.id, p.signature, p.meaning);
            }
            for p in &g.overlay.phrases {
                let uses = rows.iter().filter(|r| r.tree.as_ref().is_some_and(|t| uses_rule(t, p.rule.as_deref().unwrap_or(&p.id)))).count();
                println!("phrase {} ({}, {}): {} uses", p.id, p.kind, p.file, uses);
            }
            for e in &g.overlay.errata {
                for r in &e.readings {
                    for alt in &r.alts {
                        let al = &sp.algs[0];
                        for row in classify::classify_steps(&g, al, &alt.steps) {
                            println!("reading {} {} {} {}: {:?} {}", e.name, r.clause, r.step, alt.reading, row.class, row.step.text);
                        }
                    }
                }
            }
            for e in &dt.anchor_errors {
                println!("unanchored: {e}");
            }
            Ok(overlay_ok(&g))
        }
        "anchor" => {
            // spec-gen anchor CLAUSE PATH: the step's text as spec.html has it, and its hash
            let (cid, path) = (a.rest.first().ok_or("anchor CLAUSE PATH")?, a.rest.get(1).ok_or("anchor CLAUSE PATH")?);
            let ci = sp.clauses.iter().position(|c| &c.id == cid).ok_or("no such clause")?;
            for al in sp.algs.iter().filter(|x| x.clause == Some(ci)) {
                for (p, st) in spec::labelled(&al.steps) {
                    if &p == path {
                        println!("{}\t{}", text::sha256(&st.text), st.text);
                    }
                }
            }
            Ok(true)
        }
        "residue" => match a.rest.first().map(String::as_str) {
            Some("-lines") => {
                let (head, lines) = residue_lines(&html, &sp, &g)?;
                print!("{}{}", head.concat(), lines.concat());
                Ok(true)
            }
            Some("-check") => residue_check(&html, &sp, &g, a.rest.get(1).ok_or("residue -check FILE")?),
            Some("-permanent") => {
                print!("{}", permanent_lines(&html, &sp, &g)?.concat());
                Ok(true)
            }
            Some("-check-permanent") => permanent_check(&html, &sp, &g, a.rest.get(1).ok_or("residue -check-permanent FILE")?),
            _ => {
                residue_report(&html, &sp, &g);
                Ok(true)
            }
        },
        "errata" => {
            let dir = a.overlay.as_deref().ok_or("errata needs --overlay=DIR")?;
            let lines = errata_lines(&g, &std::path::Path::new(dir).join("../../docs/spec-issues"))?;
            match a.rest.first().map(String::as_str) {
                Some("-check") => return errata_check(&lines, a.rest.get(1).ok_or("errata -check FILE")?),
                _ => print!("{}", lines.concat()),
            }
            Ok(true)
        }
        "asserts" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            let sites = asserts::sites(&sp, &g, &dt);
            match a.rest.first().map(String::as_str) {
                Some("-all") => print!("{}", assert_sites(&sites).concat()),
                Some("-lines") => print!("{}", assert_open(&sites).concat()),
                Some("-check") => return asserts_check(&sites, a.rest.get(1).ok_or("asserts -check FILE")?),
                Some("-check-all") => return asserts_check_all(&sites, a.rest.get(1).ok_or("asserts -check-all FILE")?),
                _ => print!("{}{}", asserts::header(&sites, "Assert and `!` sites by class").concat(), sites.iter().filter(|s| !matches!(s.class, "formal" | "bang")).map(asserts::Site::line).collect::<String>()),
            }
            Ok(true)
        }
        "exceptions" => {
            let rows = classify(&sp, &g);
            let dt = data::build(&html, &sp, &g, &rows);
            for a in &dt.algs {
                for (t, why) in &a.exceptions {
                    println!("{}\t{why}\t{t}", sp.clauses[a.clause].id);
                }
            }
            let mut by_cat: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
            for p in &dt.decls.phrases {
                by_cat.entry(p.cat).or_default().push(p.name);
            }
            println!("phrase rows: {}", dt.decls.phrases.len());
            for (c, ns) in &by_cat {
                println!("  {c} {}: {}", ns.len(), ns.join(" "));
            }
            let (a, b, c, d) = dt.header_types;
            println!("header types: {a} of {b} uses parsed, {c} of {d} distinct phrases");
            let mut u = dt.unresolved.clone();
            u.sort();
            u.dedup();
            println!("unresolved X of Y names: {u:?}");
            Ok(true)
        }
        "host" => {
            let h = host::build(&html, &sp, &g);
            if a.rest.iter().any(|x| x == "-hooks") {
                for pa in &h.paras {
                    let Some(c) = pa.clause else { continue };
                    if !matches!(sp.clauses[c].ty.as_deref(), Some("host-defined abstract operation" | "implementation-defined abstract operation")) {
                        continue;
                    }
                    for &(x, y) in &pa.sents {
                        println!("{}\t{}\t{}", sp.clauses[c].op().unwrap_or_default(), pa.tag, crate::text::squash(&pa.raw[x..y]));
                    }
                }
                return Ok(true);
            }
            host::report(&h, &sp, &g.overlay.host_laws, a.rest.iter().any(|x| x == "-v"));
            Ok(true)
        }
        "report" => {
            report(&sp, &g, &a.rest);
            Ok(true)
        }
        "early" => {
            early_report(&sp, &g, &html, &a.rest);
            Ok(true)
        }
        "realm" => {
            let r = realm::build(&html, &sp, &g.overlay.ops)?;
            let funs = r.objs.iter().filter(|o| o.fun.is_some()).count();
            let props: usize = r.objs.iter().map(|o| o.props.len()).sum();
            println!("objects {}, functions {funs}, properties {props}, globals {}, namespace {}", r.objs.len(), r.globals.len(), r.namespace.len());
            for n in a.rest.iter().filter_map(|x| x.strip_prefix("--path=")) {
                println!("{n}: {:?} {:?}", r.by_path(n).map(|o| &r.objs[o].names), r.by_name(n).map(|o| &r.objs[o].path));
            }
            for n in realm::unresolved(&html, &r) {
                println!("unresolved\t%{n}%");
            }
            for o in r.prose() {
                println!("prose\t{}", r.objs[o].path);
            }
            if a.rest.iter().any(|x| x == "-v") {
                for o in &r.objs {
                    let proto = o.proto.map_or("null".to_string(), |p| r.objs[p].path.clone());
                    println!("{}\t{:?}\tproto {proto}\t{:?}\tB {} opt {}\t{:?}", o.path, o.names, o.kind, o.annex_b, o.optional, o.slots);
                    if let Some(f) = &o.fun {
                        println!("  fun {:?} len {} name {:?} ctor {}", f.alg, f.length, realm::name_string(&f.prefix, &f.name), f.ctor);
                    }
                    for p in &o.props {
                        println!("  {:?} {:?} {:?} {} B {} opt {}", p.key, p.val, p.attrs, sp.clauses[p.clause].id, p.annex_b, p.optional);
                    }
                }
                for p in &r.globals {
                    println!("global {:?} {:?} {:?} {} B {} opt {} omit {}", p.key, p.val, p.attrs, sp.clauses[p.clause].id, p.annex_b, p.optional, p.omittable);
                }
                for p in &r.namespace {
                    println!("namespace {:?} {:?} {:?} {}", p.key, p.val, p.attrs, sp.clauses[p.clause].id);
                }
            }
            Ok(true)
        }
        "memmodel" => memmodel_report(&html, &sp, &g, &a.rest),
        "types" => {
            let rows = classify(&sp, &g);
            let mut dt = data::build(&html, &sp, &g, &rows);
            let ts = tables::build_with(&html, &sp, &g, &mut dt, true);
            let td = tydecls::TyDecls::build(&dt.decls, &ts);
            let (mut fs, st) = types::check(&sp, &g, &dt);
            let (impls, impl_n) = types::impls(&sp, &dt, &td);
            fs.extend(impls.iter().cloned());
            fs.extend(types::typings(&sp, &g, &dt, &td));
            match a.rest.first().map(String::as_str) {
                Some("-lines") => print!("{}", types::lines(&fs, &st).concat()),
                Some("-check") => return types::check_file(&fs, a.rest.get(1).ok_or("types -check FILE")?),
                Some("-esmeta") => {
                    let f = a.rest.get(1).cloned().unwrap_or_else(|| std::path::Path::new(&a.spec).with_file_name("esmeta-ignore.json").display().to_string());
                    let names = types::esmeta_names(&std::fs::read_to_string(&f).map_err(|e| format!("{f}: {e}"))?);
                    print!("{}", types::esmeta_diff(&sp, &dt, &fs, &names).concat());
                }
                Some("-cover") => {
                    let (plain, exp) = types::cover(&sp, &g, &dt);
                    print!("{}", types::cover_lines(&plain, &exp).concat());
                    print!("{}", td.field_reads(&dt.decls, exp.field_names()).concat());
                }
                Some("-impls") => print!("{}", types::impl_lines(&impls, &impl_n).concat()),
                Some("-within") => {
                    let (fs, n, v) = types::within(&sp, &g, &dt, &td);
                    print!("{}", types::within_lines(&fs, &n, &v).concat());
                }
                Some("-dyn") => print!("{}", types::dyn_lines(&types::within(&sp, &g, &dt, &td).0).concat()),
                Some("-check-dyn") => return types::check_file(&types::within(&sp, &g, &dt, &td).0, a.rest.get(1).ok_or("types -check-dyn FILE")?),
                Some("-decls") => print!("{}", td.lines(&dt.decls).concat()),
                Some("-opaque") => {
                    for (s, n) in types::opaque_sorts(&dt) {
                        println!("{n}\t{s}");
                    }
                }
                _ => print!("{}", types::lines(&fs, &st).concat()),
            }
            Ok(true)
        }
        c => Err(format!("unknown command {c}")),
    }
}

/// Every parsed step and every body printed from its tree.
fn roundtrip(sp: &spec::Spec, g: &grammar::Grammar) -> Result<bool, String> {
    let rows = classify(&sp, g);
    let mut printed: HashMap<*const spec::Step, String> = HashMap::new();
    let mut bad = 0;
    for r in &rows {
        let out = match &r.tree {
            Some(t) => print(t, &r.toks, &r.step.text),
            None => r.step.text.clone(),
        };
        if out != r.step.text {
            bad += 1;
            if bad <= 20 {
                eprintln!("step differs ({}):\n  src: {}\n  out: {}", r.path, r.step.text, out);
            }
        }
        for (b, bt, tr) in &r.bullets {
            if let Some(t) = tr {
                let o = print(t, bt, b);
                if &o != b {
                    bad += 1;
                    eprintln!("bullet differs:\n  src: {b}\n  out: {o}");
                }
            }
        }
        printed.insert(r.step as *const _, out);
    }
    let mut bodies_bad = 0;
    let mut n = 0;
    for al in sp.algs.iter().filter(|a| !a.example() && !a.tmpl) {
        n += 1;
        let body = spec::print_body(al, &mut |s| printed.get(&(s as *const _)).cloned().unwrap_or_default());
        if body != al.raw {
            bodies_bad += 1;
            if bodies_bad <= 5 {
                eprintln!("body differs at spec.html:{}", al.line);
            }
        }
    }
    println!("steps {} differ {}; bodies {} differ {}", rows.len(), bad, n, bodies_bad);
    // the data: every body printed from its converted steps
    let html = std::fs::read_to_string(spec_path()).unwrap();
    let dt = data::build(&html, sp, g, &rows);
    let mut dbad = 0;
    for a in &dt.algs {
        let al = &sp.algs[a.alg];
        let out = print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
        if out != al.raw {
            dbad += 1;
            if dbad <= 8 {
                let (x, y) = first_diff(&al.raw, &out);
                eprintln!("data body differs at spec.html:{}:\n  src: {x}\n  out: {y}", al.line);
            }
        }
    }
    let mut ebad = 0;
    for e in &dt.eqs {
        let q = &sp.eqs[e.eq];
        if let Some(why) = &e.exception {
            ebad += 1;
            eprintln!("equation without a data shape at spec.html:{} ({why}): {}", q.line, q.text);
            continue;
        }
        let out = print::equation(&dt.decls, &e.vars.names, e.sdo, &e.keys, &e.body, q.indent);
        if out != q.raw {
            ebad += 1;
            eprintln!("equation differs at spec.html:{}:\n  src: {:?}\n  out: {:?}", q.line, q.raw, out);
        }
    }
    println!("equation rows {} differ or unshaped {}", dt.eqs.len(), ebad);
    dbad += ebad;
    let (tbad, rbad) = early_roundtrip(sp, g, &dt);
    println!("early-error bullets {}: trees differ {tbad}; rows differ or unshaped {rbad}", dt.early.len());
    bad += tbad;
    dbad += rbad;
    let exc: usize = dt.algs.iter().map(|a| a.exceptions.len()).sum();
    println!("data bodies {} differ {}; steps kept as prose for want of a data shape: {}", dt.algs.len(), dbad, exc);
    // a parameterized clause is read through its instances: no emitted String names its parameter
    let insts = sp.clauses.iter().filter(|c| c.inst.is_some()).count();
    let vars = dt.algs.iter().filter(|a| sp.algs[a.alg].raw.split("*\"").skip(1).any(|x| x.split("\"*").next().is_some_and(|x| x.contains("<var>")))).count();
    println!("clause instances {insts}; algorithms with a String naming a parameter: {vars}");
    dbad += vars;
    let mut rbad = dt.anchor_errors.len();
    for e in &dt.anchor_errors {
        eprintln!("{e}");
    }
    let mut nread = 0;
    for a in &dt.algs {
        for (e, k, j, ns) in &a.readings {
            let alt = &g.overlay.errata[*e].readings[*k].alts[*j];
            nread += 1;
            let out = print::body(&dt.decls, &a.vars.names, &a.closures, ns, alt.base, alt.close);
            if out != alt.raw {
                rbad += 1;
                let (x, y) = first_diff(&alt.raw, &out);
                eprintln!("reading of {} differs:\n  src: {x}\n  out: {y}", g.overlay.errata[*e].id);
            }
        }
    }
    println!("errata: {} readings print back, {rbad} differ or unanchored", nread);
    let ov = overlay_ok(g) && rbad == 0;
    println!("overlay: {} primitives, {} phrases, patterns {}", g.overlay.prims.len(), g.overlay.phrases.len(), if ov { "print back" } else { "differ" });
    let mut dt = dt;
    let ts = tables::build(&html, sp, g, &mut dt);
    let alg = |k: usize| alg_body(sp, &dt, k);
    let tok = tables::report(sp, &tables::Pr { d: &dt.decls, alg: &alg }, &ts, false);
    let h = host::build(&html, sp, g);
    let hbad = host::roundtrip(&h);
    for m in hbad.iter().take(20) {
        eprintln!("{m}");
    }
    let paras: std::collections::BTreeSet<usize> = h.reqs.iter().map(|r| r.para).collect();
    let sents: usize = h.paras.iter().map(|p| p.sents.len()).sum();
    println!("host: {} paragraphs split into {sents} sentences; requirements {} in {} paragraphs; differ {}", h.paras.len(), h.reqs.len(), paras.len(), hbad.len());
    let doc = memmodel::build(&html, sp, g)?;
    let mm = memmodel::print(&doc, sp) == doc.src;
    println!("memory model (section 29) printed from its data: {}", if mm { "equal" } else { "differs" });
    Ok(bad == 0 && bodies_bad == 0 && dbad == 0 && ov && tok && hbad.is_empty() && mm)
}

/// Early Errors bullets: each sentence printed from its tree, and each row from its data.
fn early_roundtrip(sp: &spec::Spec, g: &grammar::Grammar, dt: &data::Data) -> (usize, usize) {
    let (mut tbad, mut rbad) = (0, 0);
    for (r, er) in early::classify(sp, g).iter().zip(&dt.early) {
        let b = &sp.early.bullets[er.bullet];
        if let Some(t) = &r.tree {
            let out = print(t, &r.toks, &b.text);
            if out != b.text {
                tbad += 1;
                eprintln!("early-error bullet differs (tree) at spec.html:{}:\n  src: {}\n  out: {out}", b.line, b.text);
            }
        }
        if let Some(why) = &er.exception {
            rbad += 1;
            eprintln!("early-error bullet without a data shape at spec.html:{} ({why}): {}", b.line, b.text);
            continue;
        }
        let (layout, want) = if b.flat() { (ast::LiLayout::Inline, &b.text) } else { (b.layout, &b.raw) };
        let out = print::early(&dt.decls, &er.vars.names, &er.body, layout, b.indent);
        if out != *want {
            rbad += 1;
            eprintln!("early-error bullet differs at spec.html:{}:\n  src: {:?}\n  out: {out:?}", b.line, b.raw);
        }
    }
    (tbad, rbad)
}

/// Early Errors: clauses, blocks, bullets by lead and layout, parse classes, sentence forms.
fn early_report(sp: &spec::Spec, g: &grammar::Grammar, html: &str, rest: &[String]) {
    let e = &sp.early;
    let rows = early::classify(sp, g);
    let prods: usize = e.blocks.iter().map(|b| text::productions(&b.raw).len()).sum();
    println!("early errors: {} clauses, {} production blocks ({prods} productions), {} bullets", e.clauses.len(), e.blocks.len(), e.bullets.len());
    let count = |f: &dyn Fn(&early::Bullet) -> String| {
        let mut m: BTreeMap<String, usize> = BTreeMap::new();
        for b in &e.bullets {
            *m.entry(f(b)).or_default() += 1;
        }
        m.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", ")
    };
    println!("  leads: {}", count(&|b| early::lead(&b.text).to_string()));
    println!("  layouts: {}", count(&|b| format!("{:?}", b.layout)));
    let mut cls: BTreeMap<Class, usize> = BTreeMap::new();
    for r in &rows {
        *cls.entry(r.class).or_default() += 1;
    }
    let n = rows.len();
    println!("  parse: {}", cls.iter().map(|(c, k)| format!("{c:?} {k} ({})", pct(*k, n))).collect::<Vec<_>>().join(", "));
    let ties = rows.iter().filter(|r| r.tree.as_ref().is_some_and(|t| classify::has_tie(t))).count();
    let alts = rows.iter().filter(|r| r.tree.as_ref().is_some_and(|t| classify::has_alts(t))).count();
    println!("  competing readings resolved by the rules: {alts}; ties left on declaration order: {ties}");
    let mut forms: BTreeMap<&str, usize> = BTreeMap::new();
    for t in rows.iter().filter_map(|r| r.tree.as_ref()) {
        for s in early::sentences(t) {
            *forms.entry(s.name).or_default() += 1;
        }
    }
    println!("  sentences: {}", forms.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", "));
    let dt = data::build(html, sp, g, &classify(sp, g));
    let exc = dt.early.iter().filter(|r| r.exception.is_some()).count();
    println!("  rows {}; without a data shape: {exc}", dt.early.len());
    if rest.iter().any(|x| x == "-r") {
        for (r, b) in dt.early.iter().zip(&e.bullets) {
            let prods: Vec<&str> = r.prods.iter().map(|&p| dt.decls.prods.name(dt.decls.prod_ids[p])).collect();
            println!("{}\t{}\t{}\tspec.html:{}\t{}", sp.clauses[r.clause].id, r.idx, dt.decls.sdos.name(r.sdo), e.blocks[b.block].line, prods.join(" | "));
        }
    }
    let v = rest.iter().any(|x| x == "-v");
    for (r, b) in rows.iter().zip(&e.bullets) {
        if r.class != Class::S && (v || r.class == Class::U) {
            println!("    {:?} spec.html:{} {}", r.class, b.line, if b.layout == ast::LiLayout::Raw { text::squash(&b.raw) } else { b.text.clone() });
        }
    }
    for (r, b) in dt.early.iter().zip(&e.bullets) {
        if let Some(why) = &r.exception {
            println!("    unshaped spec.html:{} ({why}) {}", b.line, b.text);
        }
    }
}

/// Per algorithm and equation row: sec-id, index, operation (`sdo:` an SDO's), row keys, the
/// callees (an operation's sec-id, also through a phrase or a table's cells, inline ones too, `sdo:`, `[[M]]`, `m:` a concrete method) and the
/// execution-context forms.
fn calls(html: &str, sp: &spec::Spec, dt: &data::Data) -> Vec<String> {
    use checks::Called;
    let d = &dt.decls;
    let tables = tables::scan(html, sp);
    let table_ops = |t: usize| -> Vec<usize> {
        fn ops(b: &tables::Body, out: &mut Vec<usize>) {
            match b {
                tables::Body::Op(c) => out.push(*c),
                tables::Body::Lines(bs) => bs.iter().for_each(|b| ops(b, out)),
                tables::Body::Dfn(b) => ops(b, out),
                _ => {}
            }
        }
        let mut out = vec![];
        for r in tables.get(t).and_then(|t| t.as_ref().ok()).map_or(&[][..], |t| &t.rows[..]) {
            r.cells.iter().for_each(|c| ops(&c.body, &mut out));
        }
        out
    };
    let mut by_name: HashMap<&str, Option<usize>> = HashMap::new();
    for (c, o) in d.ops.iter().enumerate().filter(|(_, o)| !o.is_empty()) {
        by_name.entry(o.as_str()).and_modify(|x| *x = None).or_insert(Some(c));
    }
    let cell_ops = |t: &str| -> Vec<usize> {
        t.split("<td>").skip(1).filter_map(|x| by_name.get(x.split("</td>").next()?.trim()).copied().flatten()).collect()
    };
    let op = |c: usize| match (&d.ops[c], d.pos(c).and_then(|k| sp.clauses[k].ty.as_deref())) {
        (o, _) if o.is_empty() => "-".to_string(),
        (o, Some("sdo")) => format!("sdo:{o}"),
        (o, _) => o.clone(),
    };
    let row = |c: usize, idx: usize, keys: &[String], bodies: Vec<&[ast::Node]>| {
        let (mut callees, mut ctx) = (vec![], vec![]);
        for c in bodies.into_iter().flat_map(checks::callees) {
            match c {
                Called::Alg(c) => callees.push(d.clauses.name(c).to_string()),
                Called::Sdo(s) => callees.push(format!("sdo:{}", d.sdos.name(s))),
                Called::IMethod(m) => callees.push(format!("[[{}]]", d.fields.name(m))),
                Called::CMethod(m) => callees.push(format!("m:{}", d.methods.name(m))),
                Called::Phrase(p) => {
                    if let Some(decls::Meaning::Alg(c)) = d.phrases[p].meaning.as_ref().filter(|m| matches!(m, decls::Meaning::Alg(c) if d.pos(*c).is_some())) {
                        callees.push(d.clauses.name(*c).to_string());
                    }
                }
                Called::Table(t) => callees.extend(table_ops(t).into_iter().map(|c| d.clauses.name(c).to_string())),
                Called::Text(t) => callees.extend(cell_ops(t).into_iter().map(|c| d.clauses.name(c).to_string())),
                Called::Ctx(f) => ctx.push(f),
            }
        }
        let keys = if keys.is_empty() { "-".to_string() } else { keys.join(" | ").split_whitespace().collect::<Vec<_>>().join(" ") };
        format!("{}\t{idx}\t{}\t{keys}\t{}\t{}", d.clauses.name(c), op(c), callees.join(" "), ctx.join(" "))
    };
    let mut out: Vec<String> = dt
        .algs
        .iter()
        .map(|a| row(d.cid(a.clause), a.idx, &a.keys, std::iter::once(&a.body[..]).chain(a.closures.iter().map(|c| &c.body[..])).collect()))
        .collect();
    out.extend(dt.eqs.iter().map(|e| row(d.cid(e.clause), e.idx, &e.keys, vec![&e.body[..]])));
    out
}

/// The `k`th emu-alg's body printed from its data.
fn alg_body(sp: &spec::Spec, dt: &data::Data, k: usize) -> String {
    let al = &sp.algs[k];
    match dt.algs.iter().find(|a| a.alg == k) {
        Some(a) => print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent),
        None => String::new(),
    }
}

/// Section 29 outside its algorithms: coverage per clause, ambiguity, the round trip.
fn memmodel_report(html: &str, sp: &spec::Spec, g: &grammar::Grammar, rest: &[String]) -> Result<bool, String> {
    let doc = memmodel::build(html, sp, g)?;
    let cov = memmodel::coverage(&doc);
    println!("{:<44} {:>5} {:>5} {:>6} {:>5}  {:>9} {:>6}  {:>5} {:>4} {:>5}  follow", "clause", "sents", "core", "phrase", "prose", "atoms c/p", "rows", "notes", "algs", "lines");
    let mut tot = memmodel::Cov::default();
    for (id, c) in &cov {
        let num = sp.clauses.iter().find(|x| &x.id == id).map(|x| x.number.as_str()).unwrap_or("");
        println!(
            "{:<44} {:>5} {:>5} {:>6} {:>5}  {:>9} {:>6}  {:>5} {:>4} {:>5}  {}/{}",
            format!("{num} {id}"), c.sents(), c.core, c.phrase, c.prose, format!("{}/{}", c.atoms_core, c.atoms_phrase),
            format!("{}/{}", c.rows_typed, c.rows), c.notes, c.algs, c.raw, c.follow_ok, c.follow
        );
        for (a, b) in [(&mut tot.core, c.core), (&mut tot.phrase, c.phrase), (&mut tot.prose, c.prose), (&mut tot.atoms_core, c.atoms_core),
            (&mut tot.atoms_phrase, c.atoms_phrase), (&mut tot.rows, c.rows), (&mut tot.rows_typed, c.rows_typed), (&mut tot.desc, c.desc),
            (&mut tot.paras, c.paras), (&mut tot.items, c.items), (&mut tot.tables, c.tables), (&mut tot.notes, c.notes),
            (&mut tot.algs, c.algs), (&mut tot.raw, c.raw), (&mut tot.follow, c.follow), (&mut tot.follow_ok, c.follow_ok)] {
            *a += b;
        }
    }
    let n = tot.sents();
    println!("normative units outside the emu-algs: {} paragraphs, {} list items, {} field tables ({} rows)", tot.paras, tot.items, tot.tables, tot.rows);
    println!(
        "sentences {n}: core {} ({}), phrase {} ({}), prose {} ({}); relational atoms {} core, {} phrase",
        tot.core, pct(tot.core, n), tot.phrase, pct(tot.phrase, n), tot.prose, pct(tot.prose, n), tot.atoms_core, tot.atoms_phrase
    );
    println!("field rows {}: {} with a parsed type; Meaning cells {} (descriptions, plain strings)", tot.rows, tot.rows_typed, tot.desc);
    println!("notes {} (verbatim), emu-algs {} (the step grammar's), verbatim lines {} (headings, headers)", tot.notes, tot.algs, tot.raw);
    println!("\"the following\" sentences {}: {} with the list, table or algorithm they need after them", tot.follow, tot.follow_ok);
    let mut by_cat: BTreeMap<&str, usize> = BTreeMap::new();
    for ph in &doc.md.phrases {
        *by_cat.entry(ph.cat).or_default() += 1;
    }
    println!("memory-model phrase rows {} {by_cat:?}, relation names {}, predicate names {}", doc.md.phrases.len(), doc.md.rels.names.len(), doc.md.names.names.len());
    println!("parsed sentences with a tie left on declaration order: {}", doc.ties.len());
    println!("attachment sites (ties with maximal munch off): resolved by maximal munch {}, still tied {}", doc.sites.0, doc.sites.1);
    for t in &doc.ties {
        println!("    tie: {t}");
    }
    println!("sentences that parsed but print otherwise or have no data shape: {}", doc.exceptions.len());
    for (t, why) in &doc.exceptions {
        println!("    {why}: {t}");
    }
    if rest.iter().any(|x| x == "-v") {
        println!("{}", memmodel::prose_list(&doc).join("\n"));
    }
    if rest.iter().any(|x| x == "-d") {
        println!("{}", memmodel::dump(&doc).join("\n"));
    }
    // reach: the conditions left as prose in section 29's algorithm steps
    let rows = classify(sp, g);
    let mut p = engine::Parser::new(g, 99, false);
    let (mut spans, mut parsed) = (0, 0);
    for r in rows.iter().filter(|r| r.class == Class::K && r.alg.clause.is_some_and(|c| sp.clauses[c].number.starts_with("29."))) {
        let Some(t) = &r.tree else { continue };
        for (i, j) in cond_spans(g, t) {
            spans += 1;
            let ok = p.parse(&r.toks[i..j], "MC").is_some();
            parsed += usize::from(ok);
            if rest.iter().any(|x| x == "-v") {
                println!("    {} {}", if ok { "MC" } else { "--" }, r.toks[i..j].iter().map(|t| t.raw.as_str()).collect::<Vec<_>>().join(" "));
            }
        }
    }
    println!("section 29's residual algorithm steps: {parsed} of {spans} prose conditions parse as relational conditions (MC)");
    let out = memmodel::print(&doc, sp);
    let ok = out == doc.src;
    if !ok {
        let (x, y) = first_diff(&doc.src, &out);
        eprintln!("section 29 differs:\n  src: {x}\n  out: {y}");
    }
    println!("section 29 ({} lines) printed from its data: {}", doc.src.lines().count(), if ok { "equal" } else { "differs" });
    Ok(ok && doc.ties.is_empty())
}

/// The S1 slice (ARC §9.2): §7.1, §10.1, the named operations, PropName.
fn in_s1(number: &str, op: &str) -> bool {
    const NAMES: &[&str] = &[
        "Get", "GetMethod", "Call", "IsCallable", "ValidateAndApplyPropertyDescriptor", "OrdinarySetWithOwnDescriptor", "CreateBuiltinFunction",
        "Await", "GeneratorStart", "GeneratorResume", "GeneratorYield", "RunSuspendedContext", "RunCallerContext", "AsyncBlockStart",
        "Number::multiply", "Math.sqrt", "PropName",
    ];
    number.starts_with("7.1.") || number.starts_with("10.1.") || NAMES.contains(&op)
}

/// A prose span's first four tokens, atoms abstracted: the head a phrase entry would name.
fn prose_head(toks: &[token::Tok]) -> String {
    toks.iter()
        .take(4)
        .map(|t| match t.k {
            token::K::Var => "_".to_string(),
            token::K::Val => "*".to_string(),
            token::K::Nt => "|".to_string(),
            token::K::Num => "N".to_string(),
            _ => t.v.to_lowercase(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Writes the Lean data into `dir` (only the modules in `only`, if given); its messages.
fn emit(html: &str, sp: &spec::Spec, g: &grammar::Grammar, dir: &std::path::Path, only: Option<&[String]>) -> Result<(Vec<String>, decls::Decls), String> {
    let rows = classify(sp, g);
    let mut dt = data::build(html, sp, g, &rows);
    for (at, _) in html.match_indices("href=\"#table-") {
        let id = html[at + "href=\"#".len()..].split('"').next().unwrap_or("");
        if !dt.env.tables.contains_key(id) && !html.contains(&format!("<emu-import href=\"{id}.html\">")) {
            return Err(format!("spec.html:{}: an xref to {id}, which names no emu-table or imported table", spec::line_of(html, at)));
        }
    }
    for (cl, text) in &dt.decls.extremes {
        let path = rows.iter().find(|r| r.alg.clause.is_some_and(|c| sp.clauses[c].id == *cl) && r.step.text == *text).map(|r| r.path.as_str());
        if !path.is_some_and(|p| g.overlay.choice_sites.contains(&format!("{cl} {p}"))) {
            return Err(format!("{cl} {}: an Expr.extreme at a step not in choice-sites.txt: {text}", path.unwrap_or("?")));
        }
    }
    let mut msgs = Vec::new();
    lean::set_ids(&dt.decls);
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    for e in std::fs::read_dir(dir).map_err(|e| e.to_string())? {
        let p = e.map_err(|e| e.to_string())?.path();
        if p.extension().is_some_and(|x| x == "lean") {
            std::fs::remove_file(&p).map_err(|e| e.to_string())?;
        }
    }
    msgs.push(format!("wrote {} tables", lean_tables::emit(html, sp, g, &mut dt, dir)?));
    msgs.push(lean_host::emit(dir, html, sp, g, &mut dt)?);
    let (m, realm) = lean_realm::emit(html, sp, g, &mut dt, dir)?;
    msgs.push(m);
    let bad: Vec<String> = dt.decls.sig_errors.iter().cloned().chain(sig::phrases(g, &dt.decls)).chain(checks::check(sp, g, &dt)).chain(checks::row_children(sp, &dt)).chain(checks::intrinsic_defaults(sp, &dt, &realm)).chain(checks::macro_uses(sp, &dt)).collect();
    if !bad.is_empty() {
        return Err(format!("primitive calls that do not fit their signatures:\n{}", bad.join("\n")));
    }
    lean_memmodel::freeze(html, sp, g, &mut dt.decls)?;
    let mods = lean::modules(sp, &dt);
    std::fs::write(dir.join("Decls.lean"), lean::decls(&dt)).map_err(|e| e.to_string())?;
    std::fs::write(dir.join(overlay::PHRASE_IDS), dt.decls.phrase_index()).map_err(|e| e.to_string())?;
    for (f, t) in [(overlay::PRIM_IDS, &dt.decls.prims), (overlay::SORT_IDS, &dt.decls.sorts), (overlay::FIELD_IDS, &dt.decls.fields), (overlay::ENUM_IDS, &dt.decls.enums)] {
        std::fs::write(dir.join(f), t.names.iter().map(|n| format!("{n}\n")).collect::<String>()).map_err(|e| e.to_string())?;
    }
    let was = |k: &Option<ids::Kept>| k.as_ref().map(|k| k.was()).unwrap_or_default();
    for (f, t, w) in [
        (ids::CLAUSE_IDS, &dt.decls.clauses, dt.decls.clause_was.clone()),
        (ids::SDO_IDS, &dt.decls.sdos, was(&g.overlay.sdo_ids)),
        (ids::METHOD_IDS, &dt.decls.methods, was(&g.overlay.method_ids)),
        (ids::ERRATUM_IDS, &dt.decls.errata_table, was(&g.overlay.erratum_ids)),
        (ids::REASON_IDS, &dt.decls.reasons, was(&g.overlay.reason_ids)),
        (ids::NOTE_IDS, &dt.decls.notes, was(&g.overlay.note_ids)),
        (ids::TABLE_IDS, &dt.decls.tables, was(&g.overlay.table_ids)),
    ] {
        std::fs::write(dir.join(f), ids::render(f, t, &w)).map_err(|e| e.to_string())?;
    }
    let mut written = Vec::new();
    for (m, ds) in &mods {
        if only.is_some_and(|o| !o.contains(m)) {
            continue;
        }
        std::fs::write(dir.join(format!("{m}.lean")), lean::module(sp, &dt, m, ds)?).map_err(|e| e.to_string())?;
        written.push(m.clone());
    }
    if !dt.phrase_algs.is_empty() && only.is_none_or(|o| o.iter().any(|m| m == "Phrases")) {
        for (m, src) in lean::phrases(&dt)? {
            std::fs::write(dir.join(format!("{m}.lean")), src).map_err(|e| e.to_string())?;
        }
        written.push("Phrases".to_string());
    }
    std::fs::write(dir.join("Index.lean"), lean::index(&written)).map_err(|e| e.to_string())?;
    msgs.push(lean_early::emit(sp, &dt, dir)?);
    msgs.push(lean_memmodel::write(html, sp, g, &dt, dir)?);
    msgs.push(lean_examples::write(sp, g, &dt, dir)?);
    let steps: usize = mods.values().flatten().map(|d| d.steps).sum();
    msgs.push(format!("wrote {} data modules ({} algorithms and SDO rows, {} steps) and Decls.lean", mods.len(), mods.values().map(|v| v.len()).sum::<usize>(), steps));
    Ok((msgs, dt.decls))
}

/// The prefix of `t` up to the end of its first parenthesized term (all of `t` if it has none).
fn balanced(t: &str) -> &str {
    let mut depth = 0i32;
    for (i, c) in t.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &t[..=i];
                }
            }
            _ => {}
        }
    }
    t
}

/// The parenthesized Lean term at the start of `t`, its string literals skipped.
fn balanced_term(t: &str) -> &str {
    let (mut depth, mut in_str, mut esc) = (0i32, false, false);
    for (i, c) in t.char_indices() {
        if in_str {
            match (esc, c) {
                (true, _) => esc = false,
                (false, '\\') => esc = true,
                (false, '"') => in_str = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &t[..=i];
                }
            }
            _ => {}
        }
    }
    t
}

/// `t` without the pinned steps of definition readings, which never run (`sReadings` takes the
/// definition): `(.readings e LIT [(.definition, …)])` keeps its alternatives only.
fn without_pinned(t: &str) -> String {
    let mut out = String::with_capacity(t.len());
    let mut rest = t;
    while let Some(k) = rest.find(".readings ") {
        let after = &rest[k + 10..];
        let digits = after.chars().take_while(char::is_ascii_digit).count();
        let lit = after[digits..].trim_start();
        if lit.starts_with('(') {
            let tail = &lit[balanced_term(lit).len()..];
            if tail.trim_start().starts_with("[(.definition,") {
                out.push_str(&rest[..k + 10 + digits]);
                out.push(' ');
                rest = tail;
                continue;
            }
        }
        out.push_str(&rest[..k + 10]);
        rest = after;
    }
    out.push_str(rest);
    out
}

/// The length of the bracketed term `t` opens with (`(…)` or `[…]`, string literals skipped).
fn term_len(t: &str) -> usize {
    let (mut depth, mut quoted, mut escaped) = (0i32, false, false);
    for (i, c) in t.char_indices() {
        if quoted {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                '"' => quoted = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => quoted = true,
            '(' | '[' => depth += 1,
            ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
    }
    t.len()
}

/// `t` without the pinned side of each `.readings e lit alts` whose erratum `e` is a definition
/// reading: the reading stands for it.
fn without_defined(t: &str, parity: &[ast::Reading]) -> String {
    let mut out = String::new();
    let mut rest = t;
    while let Some(k) = rest.find(".readings ") {
        let after = &rest[k + ".readings ".len()..];
        let n: String = after.chars().take_while(char::is_ascii_digit).collect();
        let lit = after[n.len()..].trim_start();
        let defined = n.parse::<usize>().ok().and_then(|e| parity.get(e)) == Some(&ast::Reading::Definition);
        if defined && (lit.starts_with('(') || lit.starts_with('[')) {
            out.push_str(&rest[..k]);
            out.push_str(".readings ");
            out.push_str(&n);
            rest = &lit[term_len(lit)..];
        } else {
            out.push_str(&rest[..k + ".readings ".len()]);
            rest = after;
        }
    }
    out.push_str(rest);
    out
}

/// The phrase ids that the emitted data uses (`.phrase p` and `.mutate p`) outside the pinned
/// side of a definition reading, and its declarations.
fn emitted_phrases(html: &str, sp: &spec::Spec, g: &grammar::Grammar) -> Result<(std::collections::BTreeSet<usize>, decls::Decls), String> {
    let dir = std::env::temp_dir().join(format!("spec-gen-residue-{}", std::process::id()));
    let r = emit(html, sp, g, &dir, None);
    let mut ids = std::collections::BTreeSet::new();
    if let Ok((_, d)) = &r {
        // the data names a reading by its erratum id, `d.parity` by the overlay's order
        let mut parity = vec![ast::Reading::Literal; d.parity.len()];
        for (e, &x) in d.parity.iter().enumerate() {
            let k = lean::eid(e);
            if parity.len() <= k {
                parity.resize(k + 1, ast::Reading::Literal);
            }
            parity[k] = x;
        }
        for e in std::fs::read_dir(&dir).map_err(|e| e.to_string())? {
            let p = e.map_err(|e| e.to_string())?.path();
            let t = without_pinned(&without_defined(&std::fs::read_to_string(&p).unwrap_or_default(), &parity));
            // §29's data numbers its rules' phrases in the memory model's own table; only its
            // field types (`ty := …`) use this table's ids
            let spans: Vec<&str> = if p.file_name().is_some_and(|f| f == "Memory.lean") {
                t.match_indices("ty := ").map(|(k, _)| balanced(&t[k + 6..])).collect()
            } else {
                vec![t.as_str()]
            };
            for t in spans {
                for head in [".phrase ", ".mutate "] {
                    for (k, _) in t.match_indices(head) {
                        let n: String = t[k + head.len()..].chars().take_while(char::is_ascii_digit).collect();
                        if let Ok(n) = n.parse() {
                            ids.insert(n);
                        }
                    }
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    r.map(|(_, d)| (ids, d))
}

/// The steps that readings replace, as (algorithm, path): each reading's steps in the first
/// algorithm of its clause whose step at its path has its text hash, as `data::build` anchors it.
/// `steps` are (clause, algorithm, path, text hash).
fn anchored_steps<'a>(readings: impl Iterator<Item = &'a overlay::Anchor>, steps: &[(&str, usize, &str, String)]) -> Vec<(usize, &'a str)> {
    let mut out = Vec::new();
    for r in readings {
        if let Some(&(_, a, _, _)) = steps.iter().find(|(c, _, p, h)| *c == r.clause && *p == r.step && *h == r.hash) {
            out.extend(std::iter::once(r.step.as_str()).chain(r.also.iter().map(|x| x.0.as_str())).map(|p| (a, p)));
        }
    }
    out
}

/// Whether the step at `path` of algorithm `alg` is a replaced step or one of its substeps.
fn is_read(anchored: &[(usize, &str)], alg: usize, path: &str) -> bool {
    anchored.iter().any(|&(a, p)| a == alg && (path == p || path.strip_prefix(p).is_some_and(|x| x.starts_with('.'))))
}

/// The residue's steps, spec and overlay: the open ones' ratchet lines, and the lines of
/// those an `<emu-permanent>` claims.
struct StepLines {
    open: Vec<String>,
    by_ch: BTreeMap<&'static str, usize>,
    named: BTreeMap<&'static str, &'static str>,
    shut: usize,
    overlay: usize,
    permanent: Vec<String>,
    perm_by: BTreeMap<&'static str, usize>,
}

/// The residue's steps split into open, read by a reading, and permanent; fails on an
/// `<emu-permanent>` that claims no residue step.
fn step_lines(sp: &spec::Spec, g: &grammar::Grammar, rows: &[classify::Row], dt: &data::Data) -> Result<StepLines, String> {
    use std::collections::BTreeSet;
    let res: Vec<&classify::Row> = rows.iter().filter(|r| matches!(r.class, Class::K | Class::U)).collect();
    let own = |r: &classify::Row| r.alg.clause.map_or("-", |c| sp.clauses[c].id.as_str());
    // an instance's steps are its parameterized clause's
    let cid = |r: &classify::Row| r.alg.clause.map_or("-", |c| sp.clauses[sp.home(c)].id.as_str());
    let hashed: Vec<(&str, usize, &str, String)> = rows.iter().map(|r| (cid(r), r.alg.pos, r.path.as_str(), text::sha256(&r.step.text))).collect();
    let anchored = anchored_steps(g.overlay.errata.iter().flat_map(|e| &e.readings), &hashed);
    let read = |r: &classify::Row| is_read(&anchored, r.alg.pos, &r.path);
    // a step whose prose is a closure's call frame read stops nothing
    let framed: BTreeSet<(&str, &str)> = dt.decls.framed.iter().map(|(c, t)| (c.as_str(), t.as_str())).collect();
    let res: Vec<&classify::Row> = res.into_iter().filter(|r| !framed.contains(&(own(r), r.step.text.as_str()))).collect();
    // one row for a step of a parameterized clause, however many instances share it
    let mut shared = BTreeSet::new();
    let res: Vec<&classify::Row> = res.into_iter()
        .filter(|r| r.alg.clause.is_none_or(|c| sp.clauses[c].inst.is_none()) || shared.insert((cid(r), r.alg.idx, r.path.clone(), r.step.text.clone())))
        .collect();
    let (open, shut): (Vec<&classify::Row>, Vec<&classify::Row>) = res.iter().partition(|r| !read(r));
    // (channel, key, path, kind) per open step, the spec's, then the overlay's own
    let mut steps: Vec<(&str, String, String, residue::Claim)> = Vec::new();
    for r in &open {
        steps.push(("", format!("{}#{}", cid(r), r.alg.idx), r.path.clone(), residue::kind(&r.step.text)));
    }
    let overlay_algs = data::overlay_steps(g);
    for (id, al) in &overlay_algs {
        for r in classify::classify_steps(g, al, &al.steps).iter().filter(|r| matches!(r.class, Class::K | Class::U)) {
            steps.push(("overlay", id.clone(), r.path.clone(), residue::kind(&r.step.text)));
        }
    }
    let keys: Vec<(String, String)> = steps.iter().map(|s| (s.1.clone(), s.2.clone())).collect();
    let (claimed, errs) = residue::claim(&keys, &g.overlay.permanent);
    if !errs.is_empty() {
        return Err(errs.join("\n"));
    }
    let mut out = StepLines { open: Vec::new(), by_ch: BTreeMap::new(), named: BTreeMap::new(), shut: shut.len(), overlay: 0, permanent: Vec::new(), perm_by: BTreeMap::new() };
    for ((src, key, path, k), c) in steps.iter().zip(&claimed) {
        let ch = match k.channel {
            residue::Channel::Upstream => "(a)",
            residue::Channel::Prim => "(b)",
            residue::Channel::Annotated => "(c)",
        };
        let what = match k.channel {
            residue::Channel::Upstream => k.reason.unwrap_or(k.kind),
            residue::Channel::Prim => k.prim.map_or("unnamed", |p| p.name),
            residue::Channel::Annotated => k.kind,
        };
        if let Some(i) = c {
            let p = &g.overlay.permanent[*i];
            *out.perm_by.entry(p.class.label()).or_default() += 1;
            out.permanent.push(format!("{}\t{key}\t{path}\t{}\t{}\n", if src.is_empty() { "step" } else { src }, p.class.label(), p.reason));
            continue;
        }
        if src.is_empty() {
            if let Some(p) = k.prim.filter(|_| k.channel == residue::Channel::Prim) {
                out.named.insert(p.name, residue::need(p.name));
            }
            *out.by_ch.entry(ch).or_default() += 1;
            out.open.push(format!("{ch}\t{key}\t{path}\t{what}\n"));
        } else {
            out.overlay += 1;
            out.open.push(format!("overlay\t{key}\t{path}\t{ch} {what}\n"));
        }
    }
    Ok(out)
}

/// The ratchet file: a header of counts, then one line per residue step the overlay does not
/// read or mark permanent (channel, clause#algorithm, step, primitive or reason) and per phrase
/// row without a meaning that the emitted data uses.
fn residue_lines(html: &str, sp: &spec::Spec, g: &grammar::Grammar) -> Result<(Vec<String>, Vec<String>), String> {
    let rows = classify(sp, g);
    let dt = data::build(html, sp, g, &rows);
    let st = step_lines(sp, g, &rows, &dt)?;
    let (used, emitted) = emitted_phrases(html, sp, g)?;
    let mut lines = st.open.clone();
    let (by_ch, named, overlay) = (&st.by_ch, &st.named, st.overlay);
    let open_n: usize = by_ch.values().sum();
    // the emitted table, whose phrases include the record tables' types and their meanings
    let bare: Vec<&decls::Phrase> = emitted.phrases.iter().enumerate().filter(|(i, p)| p.meaning.is_none() && used.contains(i) && !(p.cat == "ER" && lean_early::ER_FORMS.contains(&p.name))).map(|x| x.1).collect();
    for p in &bare {
        lines.push(format!("phrase\t{}\t{}\n", p.cat, p.name));
    }
    let mut early = 0;
    for r in &dt.early {
        for w in lean_early::wrapped(&dt.decls, r) {
            early += 1;
            lines.push(format!("early\t{}.{}\t{w}\n", sp.clauses[r.clause].id, r.idx));
        }
    }
    lines.sort();
    let mut need: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (p, n) in named {
        need.entry(n).or_default().push(p);
    }
    let mut head = vec![
        "# The residue that stops the machine, generated by `spec-gen residue -lines`; `spec-gen residue -check` fails on a line not here.\n".to_string(),
        "# The file only shrinks: an added line needs the coordinator's approval in the merge message.\n".to_string(),
        format!("# steps: {open_n} open ({}), {} read by an overlay reading; phrase rows without a meaning: {}; early-error sentences kept as statements: {early}; overlay steps: {overlay}\n",
            by_ch.iter().map(|(c, n)| format!("{c} {n}")).collect::<Vec<_>>().join(", "), st.shut, bare.len()),
        format!("# (b)'s {} named primitives by need:\n", named.len()),
    ];
    for (n, ps) in &need {
        head.push(format!("#   {n}: {} ({})\n", ps.len(), ps.join(", ")));
    }
    Ok((head, lines))
}

/// Fails when the residue has a line that `file` lacks; prints the file's lines that no longer occur.
fn residue_check(html: &str, sp: &spec::Spec, g: &grammar::Grammar, file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    let mut count: HashMap<&str, isize> = HashMap::new();
    for l in have.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        *count.entry(l).or_default() += 1;
    }
    let (_, lines) = residue_lines(html, sp, g)?;
    let mut new = Vec::new();
    for l in &lines {
        let l = l.trim_end_matches('\n');
        match count.get_mut(l) {
            Some(n) if *n > 0 => *n -= 1,
            _ => new.push(l.to_string()),
        }
    }
    let mut gone: Vec<(&&str, &isize)> = count.iter().filter(|x| *x.1 > 0).collect();
    gone.sort();
    for (l, n) in gone {
        println!("gone ({n}), delete from {file}: {l}");
    }
    for l in &new {
        eprintln!("new residue, not in {file}: {l}");
    }
    Ok(new.is_empty())
}

/// The permanent file: a header, then one line per host requirement sentence whose disposition
/// is not a law (`host`, clause, paragraph.sentence, class, reason) and per residue step an
/// `<emu-permanent>` claims (`step` or `overlay`, clause#algorithm or overlay id, path, class, reason).
fn permanent_lines(html: &str, sp: &spec::Spec, g: &grammar::Grammar) -> Result<Vec<String>, String> {
    let h = host::build(html, sp, g);
    if !h.disp_errors.is_empty() {
        return Err(h.disp_errors.join("\n"));
    }
    let laws = &g.overlay.host_laws;
    let mut by: BTreeMap<&str, usize> = BTreeMap::new();
    let mut lines = Vec::new();
    for r in &h.reqs {
        let Some(l) = r.disp.map(|l| &laws[l]).filter(|l| l.class != overlay::LawClass::Law) else { continue };
        *by.entry(l.class.label()).or_default() += 1;
        lines.push(format!("host\t{}\t{}.{}\t{}\t{}\n", sp.clauses[r.clause].id, h.idx[r.para], r.sent, l.class.label(), l.reason));
    }
    let mut out = vec![
        "# Sentences the base layer gives no meaning on purpose, generated by `spec-gen residue -permanent`; `spec-gen residue -check-permanent` fails on any difference.\n".to_string(),
        "# A line is added only with the coordinator's approval in the merge message. Theorem lines are proof obligations on the model, never assumed.\n".to_string(),
        format!("# host requirement sentences by class: {}\n", by.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", ")),
    ];
    let rows = classify(sp, g);
    let st = step_lines(sp, g, &rows, &data::build(html, sp, g, &rows))?;
    out.push(format!("# residue steps by class: {}\n", st.perm_by.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", ")));
    out.extend(lines);
    let mut steps = st.permanent;
    steps.sort();
    out.extend(steps);
    Ok(out)
}

/// Fails when `file` differs from the permanent lines; prints each line only one side has.
fn permanent_check(html: &str, sp: &spec::Spec, g: &grammar::Grammar, file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    let want = permanent_lines(html, sp, g)?.concat();
    if have == want {
        return Ok(true);
    }
    let (a, b): (std::collections::BTreeSet<&str>, std::collections::BTreeSet<&str>) = (have.lines().collect(), want.lines().collect());
    for l in a.difference(&b) {
        eprintln!("stale, not generated: {l}");
    }
    for l in b.difference(&a) {
        eprintln!("new, not in {file}: {l}");
    }
    eprintln!("{file} differs from `spec-gen residue -permanent`");
    Ok(false)
}

/// The sites file: a header of counts, then every Assert and `!` site.
fn assert_sites(sites: &[asserts::Site]) -> Vec<String> {
    let mut out = asserts::header(sites, "Every Assert and `!` site (class, algorithm, step, text), generated by `spec-gen asserts -all`; `spec-gen asserts -check-all` fails on any difference.");
    out.extend(sites.iter().map(asserts::Site::line));
    out
}

/// The ratchet file: a header, then the open Asserts, sorted.
fn assert_open(sites: &[asserts::Site]) -> Vec<String> {
    let mut out = asserts::header(sites, "The prose Asserts with no meaning, generated by `spec-gen asserts -lines`; `spec-gen asserts -check` fails on a line not here.");
    out.push("# The file only shrinks: an added line needs the coordinator's approval in the merge message.\n".to_string());
    let mut lines: Vec<String> = sites.iter().filter(|s| s.class == "open").map(asserts::Site::line).collect();
    lines.sort();
    out.extend(lines);
    out
}

/// Fails when an open Assert's line is not in `file`; prints the file's lines that no longer occur.
fn asserts_check(sites: &[asserts::Site], file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    let mut count: HashMap<&str, isize> = HashMap::new();
    for l in have.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        *count.entry(l).or_default() += 1;
    }
    let mut new = Vec::new();
    for l in assert_open(sites).iter().filter(|l| !l.starts_with('#')) {
        let l = l.trim_end_matches('\n');
        match count.get_mut(l) {
            Some(n) if *n > 0 => *n -= 1,
            _ => new.push(l.to_string()),
        }
    }
    let mut gone: Vec<(&&str, &isize)> = count.iter().filter(|x| *x.1 > 0).collect();
    gone.sort();
    for (l, n) in gone {
        println!("gone ({n}), delete from {file}: {l}");
    }
    for l in &new {
        eprintln!("new open Assert, not in {file}: {l}");
    }
    Ok(new.is_empty())
}

/// Fails when `file` differs from `spec-gen asserts -all`; prints each line only one side has.
fn asserts_check_all(sites: &[asserts::Site], file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    let want = assert_sites(sites).concat();
    if have == want {
        return Ok(true);
    }
    let (a, b): (std::collections::BTreeSet<&str>, std::collections::BTreeSet<&str>) = (have.lines().collect(), want.lines().collect());
    for l in a.difference(&b) {
        eprintln!("stale, not generated: {l}");
    }
    for l in b.difference(&a) {
        eprintln!("new, not in {file}: {l}");
    }
    eprintln!("{file} differs from `spec-gen asserts -all`");
    Ok(false)
}

/// The revision of tc39/ecma262 the overlay reads (external/ecma262).
const SPEC_REV: &str = "b1eaed82f";

/// The errata file (spec/formal/errata.txt): per erratum of readings.emu, its resolution, kind and switch, where its
/// literal reading stops a run (`none`: nowhere; `-`: another resolution that gives no `stops=`) and the
/// spec-issue reports in `issues` (`NN-*.md`) that name it (`-`: none).
fn errata_lines(g: &grammar::Grammar, issues: &std::path::Path) -> Result<Vec<String>, String> {
    let mut reports = Vec::new();
    // the reports `NN-*.md`, and those of a directory of their own (a proposal's: `DIR/NN-*.md`)
    let mut dirs = vec![(issues.to_path_buf(), String::new())];
    while let Some((dir, prefix)) = dirs.pop() {
        for e in std::fs::read_dir(&dir).map_err(|e| format!("{}: {e}", dir.display()))? {
            let p = e.map_err(|e| e.to_string())?.path();
            let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("").to_string();
            if p.is_dir() && prefix.is_empty() && name != "examples" {
                dirs.push((p.clone(), format!("{name}/")));
            } else if name.ends_with(".md") && name.len() > 3 && name.as_bytes()[..2].iter().all(u8::is_ascii_digit) && name.as_bytes()[2] == b'-' {
                reports.push((format!("{prefix}{name}"), std::fs::read_to_string(&p).map_err(|e| format!("{}: {e}", p.display()))?));
            }
        }
    }
    reports.sort();
    // the name as a word: not part of a longer identifier
    let names = |text: &str, n: &str| {
        text.match_indices(n).any(|(i, _)| {
            let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
            !text[..i].ends_with(word) && !text[i + n.len()..].starts_with(word)
        })
    };
    let mut out = vec![
        "# The errata of readings.emu: name, resolution, kind (`defect`: a defect of the text; `proposal`: a proposed\n".to_string(),
        "# normative change), where its readings are switched (`spec`: in the specification layer, at run time; `parser`:\n".to_string(),
        "# only in the engine's parser, the specification's grammar having the test262 reading; `none`: one reading only),\n".to_string(),
        "# where its literal reading stops a run (<sec-id>@<path>[<caller>], `none`: nowhere, `-`: not given), the\n".to_string(),
        "# spec-issue reports naming it; generated by `spec-gen errata`, and `spec-gen errata -check` fails on any\n".to_string(),
        format!("# difference. spec.html is tc39/ecma262 at {SPEC_REV} (external/ecma262).\n"),
        "# The file only shrinks: an added line needs the user's approval in the merge message.\n".to_string(),
    ];
    for e in g.overlay.errata.iter().filter(|e| e.resolution != "definition") {
        let stops = match () {
            _ if !e.stops_given => "-".to_string(),
            _ if e.stops.is_empty() => "none".to_string(),
            _ => e.stops.iter().map(|s| s.text()).collect::<Vec<_>>().join(" "),
        };
        let rs: Vec<&str> = reports.iter().filter(|(_, t)| names(t, &e.name)).map(|(n, _)| n.as_str()).collect();
        let rs = if rs.is_empty() { "-".to_string() } else { rs.iter().map(|n| format!("docs/spec-issues/{n}")).collect::<Vec<_>>().join(" ") };
        out.push(format!("{}\t{}\t{}\t{}\t{stops}\t{rs}\n", e.name, e.resolution, e.kind, e.switch));
    }
    Ok(out)
}

fn errata_check(lines: &[String], file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    if have == lines.concat() {
        return Ok(true);
    }
    let (a, b): (std::collections::BTreeSet<&str>, std::collections::BTreeSet<&str>) = (have.lines().collect(), lines.iter().map(|l| l.trim_end_matches('\n')).collect());
    for l in a.difference(&b) {
        eprintln!("stale, not generated: {l}");
    }
    for l in b.difference(&a) {
        eprintln!("new, not in {file}: {l}");
    }
    eprintln!("{file} differs from `spec-gen errata`");
    Ok(false)
}

/// The residue by channel and kind, the KILL figures, S1's residue and ESMeta's ignored algorithms.
fn residue_report(html: &str, sp: &spec::Spec, g: &grammar::Grammar) {
    use std::collections::{BTreeSet, HashMap};
    let rows = classify(sp, g);
    let res: Vec<&classify::Row> = rows.iter().filter(|r| matches!(r.class, Class::K | Class::U)).collect();
    println!("residue: {} steps (K {}, U {}), {} of them Asserts", res.len(),
        res.iter().filter(|r| r.class == Class::K).count(), res.iter().filter(|r| r.class == Class::U).count(),
        res.iter().filter(|r| r.step.text.starts_with("Assert:")).count());
    let mut ch: BTreeMap<residue::Channel, Vec<&classify::Row>> = BTreeMap::new();
    for r in &res {
        ch.entry(residue::kind(&r.step.text).channel).or_default().push(r);
    }
    let at = |r: &classify::Row| match r.alg.clause {
        Some(c) => format!("{} {} {}", sp.clauses[c].number, sp.clauses[c].op().unwrap_or_default(), r.path),
        None => format!("- {}", r.path),
    };
    let counts = |rs: &[&classify::Row]| {
        let k = rs.iter().filter(|r| r.class == Class::K).count();
        format!("{} (K {k}, U {})", rs.len(), rs.len() - k)
    };
    for (c, rs) in &ch {
        match c {
            residue::Channel::Upstream => {
                println!("{}: {}, each a spec-issue candidate with its reason", c.label(), counts(rs));
                let mut by: BTreeMap<(&str, &str), Vec<&classify::Row>> = BTreeMap::new();
                for r in rs {
                    let k = residue::kind(&r.step.text);
                    by.entry((k.kind, k.reason.unwrap_or(""))).or_default().push(r);
                }
                let mut last = "";
                for ((kind, reason), v) in &by {
                    if *kind != last {
                        println!("    {kind}: {}", by.iter().filter(|x| x.0 .0 == *kind).map(|x| x.1.len()).sum::<usize>());
                        last = kind;
                    }
                    println!("        reason: {reason} ({})", v.len());
                    for r in v {
                        println!("            {}: {}", at(r), r.step.text);
                    }
                }
            }
            residue::Channel::Prim => {
                let mut by: BTreeMap<&str, Vec<(Option<&residue::Prim>, &classify::Row)>> = BTreeMap::new();
                for r in rs {
                    let p = residue::kind(&r.step.text).prim;
                    by.entry(p.map_or("unnamed", |p| p.group)).or_default().push((p, *r));
                }
                let named: std::collections::BTreeSet<&str> = rs.iter().filter_map(|r| residue::prim(&r.step.text)).map(|p| p.name).collect();
                println!("{}: {}, {} named primitives", c.label(), counts(rs), named.len());
                for (g, v) in &by {
                    println!("    {g}: {}", v.len());
                    for p in residue::PRIMS.iter().filter(|p| p.group == *g) {
                        let uses: Vec<&classify::Row> = v.iter().filter(|x| x.0.is_some_and(|q| q.name == p.name)).map(|x| x.1).collect();
                        if uses.is_empty() {
                            continue;
                        }
                        println!("        {}{}: {} ({} step{})", p.name, p.sig, p.meaning, uses.len(), if uses.len() == 1 { "" } else { "s" });
                        for r in uses {
                            println!("            {}: {}", at(r), r.step.text);
                        }
                    }
                    for (_, r) in v.iter().filter(|x| x.0.is_none()) {
                        println!("        unnamed: {}: {}", at(r), r.step.text);
                    }
                }
            }
            residue::Channel::Annotated => {
                println!("{}: {}", c.label(), counts(rs));
                let mut by: BTreeMap<&str, Vec<&classify::Row>> = BTreeMap::new();
                for r in rs {
                    by.entry(residue::kind(&r.step.text).kind).or_default().push(r);
                }
                for (k, v) in &by {
                    println!("    {k}: {}", counts(v));
                }
            }
        }
    }
    let mut chap: BTreeMap<String, usize> = BTreeMap::new();
    for r in &res {
        let num = r.alg.clause.map(|c| sp.clauses[c].number.clone()).unwrap_or_default();
        *chap.entry(format!("§{}", num.split('.').next().unwrap_or(""))).or_default() += 1;
    }
    let mut chap: Vec<_> = chap.into_iter().collect();
    chap.sort_by(|a, b| b.1.cmp(&a.1));
    println!("by chapter: {}", chap.iter().map(|(c, n)| format!("{c} {n}")).collect::<Vec<_>>().join(", "));
    // KILL figures
    let mut heads: BTreeSet<String> = BTreeSet::new();
    for r in &res {
        match &r.tree {
            Some(t) => engine::visit(t, &mut |n| {
                for it in &n.items {
                    if let engine::Item::P(i, j, _) = it {
                        heads.insert(prose_head(&r.toks[*i..*j]));
                    }
                }
            }),
            None => {
                heads.insert(prose_head(&r.toks));
            }
        }
    }
    let dt = data::build(html, sp, g, &rows);
    let phrases = dt.decls.phrases.len();
    println!("KILL figure 1, projected phrase entries: {phrases} phrase rows + {} distinct residual prose heads = {} (limit 900)", heads.len(), phrases + heads.len());
    let mut steps_per: HashMap<usize, usize> = HashMap::new();
    for r in &rows {
        if let Some(c) = r.alg.clause {
            *steps_per.entry(c).or_default() += 1;
        }
    }
    let mut worst = (0.0f64, String::new());
    for a in &dt.algs {
        let n = steps_per.get(&a.clause).copied().unwrap_or(1);
        let f = a.exceptions.len() as f64 / n as f64;
        if f > worst.0 {
            worst = (f, sp.clauses[a.clause].id.clone());
        }
    }
    println!("KILL figure 2, printer exceptions: worst clause {:.1}% {} (limit 2%); steps without a data shape: {}", 100.0 * worst.0, worst.1,
        dt.algs.iter().map(|a| a.exceptions.len()).sum::<usize>());
    // S1
    let s1: Vec<&&classify::Row> = res.iter().filter(|r| r.alg.clause.is_some_and(|c| in_s1(&sp.clauses[c].number, &sp.clauses[c].op().unwrap_or_default()))).collect();
    let s1_steps = rows.iter().filter(|r| r.alg.clause.is_some_and(|c| in_s1(&sp.clauses[c].number, &sp.clauses[c].op().unwrap_or_default()))).count();
    println!("S1: {} residual steps of {s1_steps}", s1.len());
    for r in &s1 {
        let c = &sp.clauses[r.alg.clause.unwrap()];
        let k = residue::kind(&r.step.text);
        let what = k.prim.map(|p| p.name).or(k.reason).unwrap_or(k.kind);
        println!("    {:?} {} {} [{}; {}] {}", r.class, c.op().unwrap_or_default(), r.path, k.channel.label(), what, r.step.text);
    }
    // ESMeta's ignore list (esmeta-ignore.json in the pinned repository)
    println!("ESMeta's tycheck ignore list:");
    for name in [
        "AsyncFromSyncIteratorContinuation", "AsyncGeneratorYield", "BigIntBitwiseOp", "ClassStaticBlockBody[0,0].EvaluateClassStaticBlockBody",
        "CompareTypedArrayElements", "DecimalEscape[0,1].CapturingGroupNumber", "DoWait", "EvaluateImportCall", "FunctionBody[0,0].EvaluateFunctionBody",
        "FunctionDeclarationInstantiation", "GetViewByteLength", "IncrementModuleAsyncEvaluationCount", "Record[SourceTextModuleRecord].ExecuteModule",
        "TimeString", "TimeZoneString", "TypedArrayLength",
    ] {
        let op = name.rsplit('.').next().unwrap();
        let lhs = name.split('[').next().unwrap();
        let mine: Vec<&classify::Row> = rows
            .iter()
            .filter(|r| {
                r.alg.clause.is_some_and(|c| sp.clauses[c].op().as_deref() == Some(op))
                    && (!name.contains('[') || name.starts_with("Record[") || r.alg.prod.as_deref().is_some_and(|p| p.trim_start().starts_with(lhs)))
            })
            .collect();
        let k = mine.iter().filter(|r| matches!(r.class, Class::K | Class::U)).count();
        println!("  {name}: {} steps, {} structured or NOTE, {k} residual", mine.len(), mine.len() - k);
        for r in mine.iter().filter(|r| matches!(r.class, Class::K | Class::U)) {
            let kd = residue::kind(&r.step.text);
            println!("      {:?} {} [{}] {}", r.class, r.path, kd.channel.label(), r.step.text);
        }
    }
}

/// Whether a tree uses the rule named `name`.
fn uses_rule(t: &engine::Node, name: &str) -> bool {
    let mut hit = false;
    engine::visit(t, &mut |n| hit |= n.name == name);
    hit
}

/// Every overlay pattern prints back from its template, holes named by its variables.
fn overlay_ok(g: &grammar::Grammar) -> bool {
    let mut ok = true;
    for p in &g.overlay.phrases {
        let vars = p.vars();
        let mut k = 0;
        let parts: Vec<token::Part> = p
            .elems()
            .iter()
            .map(|(e, glue)| match e {
                engine::El::Lit(l) => token::Part::Text(token::lit_canon(l).to_string(), *glue),
                engine::El::KindV(_, _, t) => token::Part::Text(t.clone(), *glue),
                _ => {
                    k += 1;
                    token::Part::Text(format!("_{}_", vars[k - 1]), *glue)
                }
            })
            .collect();
        let out = token::join(&parts, &[], "");
        if out != p.pattern {
            ok = false;
            eprintln!("overlay pattern {} does not print back:\n  src: {}\n  out: {out}", p.id, p.pattern);
        }
    }
    ok
}

/// The prose spans of a tree that fill a condition hole (`{C}`).
fn cond_spans(g: &grammar::Grammar, t: &engine::Node) -> Vec<(usize, usize)> {
    fn items(els: &[(engine::El, bool)], its: &[engine::Item], out: &mut Vec<(usize, usize)>) {
        for ((el, _), it) in els.iter().zip(its) {
            match (el, it) {
                (engine::El::Hole("C"), engine::Item::P(i, j, _)) => out.push((*i, *j)),
                (engine::El::Opt(inner), engine::Item::O(Some(v), _)) => items(inner, v, out),
                (engine::El::Alt(alts), engine::Item::A(k, v, _)) => items(&alts[*k], v, out),
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    engine::visit(t, &mut |n| {
        if let engine::Rid::R(ri) = n.rid {
            items(&g.rules[ri].elems, &n.items, &mut out);
        }
    });
    out
}

/// The first differing lines of two texts.
fn first_diff(a: &str, b: &str) -> (String, String) {
    for (x, y) in a.lines().zip(b.lines()) {
        if x != y {
            return (x.to_string(), y.to_string());
        }
    }
    (format!("({} lines)", a.lines().count()), format!("({} lines)", b.lines().count()))
}

thread_local! {
    static SPEC: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}

fn spec_path() -> String {
    SPEC.with(|s| s.borrow().clone())
}

fn report(sp: &spec::Spec, g: &grammar::Grammar, rest: &[String]) {
    let rows = classify(sp, g);
    let n = rows.len();
    let mut cls: BTreeMap<Class, usize> = BTreeMap::new();
    for r in &rows {
        *cls.entry(r.class).or_default() += 1;
    }
    println!("algorithms {} (non-example), steps {}", sp.algs.iter().filter(|a| !a.example() && !a.tmpl).count(), n);
    let eqs = classify::classify_eqs(sp, g);
    let mut ec: BTreeMap<Class, usize> = BTreeMap::new();
    for e in &eqs {
        *ec.entry(e.class).or_default() += 1;
    }
    println!("equation SDOs {}: {ec:?}", eqs.len());
    for e in eqs.iter().filter(|e| e.class != Class::S) {
        println!("    {:?} {}", e.class, e.eq.text);
    }
    for (c, k) in &cls {
        println!("  {:?}: {} ({})", c, k, pct(*k, n));
    }
    let mut by_ty: BTreeMap<&str, BTreeMap<Class, usize>> = BTreeMap::new();
    for r in &rows {
        let ty = r.alg.clause.and_then(|c| sp.clauses[c].ty.as_deref()).unwrap_or("untyped");
        *by_ty.entry(ty).or_default().entry(r.class).or_default() += 1;
    }
    for (ty, m) in &by_ty {
        let t: usize = m.values().sum();
        let s = m.get(&Class::S).copied().unwrap_or(0) + m.get(&Class::Note).copied().unwrap_or(0);
        println!("  {ty}: {t} steps, S+NOTE {}, {m:?}", pct(s, t));
    }
    // algorithms
    let mut per: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
    for r in &rows {
        let e = per.entry(r.alg.pos).or_default();
        e.0 += 1;
        if matches!(r.class, Class::K | Class::U) {
            e.1 += 1;
        }
    }
    let full = per.values().filter(|v| v.1 == 0).count();
    let le1 = per.values().filter(|v| v.1 <= 1).count();
    println!("algorithms fully structured {} ({}), <= 1 residual {} ({})", full, pct(full, per.len()), le1, pct(le1, per.len()));
    // ambiguity: ties left on declaration order, and attachment sites (ties with maximal munch off)
    let ties: Vec<_> = rows.iter().filter(|r| r.class == Class::S && r.tree.as_ref().is_some_and(|t| classify::has_tie(t))).collect();
    let alts = rows.iter().filter(|r| r.class == Class::S && r.tree.as_ref().is_some_and(|t| classify::has_alts(t))).count();
    println!("S steps with competing readings resolved by the rules: {alts}");
    println!("S steps with a tie left on declaration order: {}", ties.len());
    for r in ties.iter().take(if rest.iter().any(|x| x == "-v") { 1000 } else { 10 }) {
        println!("    tie: {}", r.step.text);
    }
    let mut off = engine::Parser::new(g, 99, false);
    off.munch = false;
    let mut on = engine::Parser::new(g, 99, false);
    let mut sites = 0;
    let mut unresolved = 0;
    for r in rows.iter().filter(|r| r.class == Class::S) {
        let a = off.parse(&r.toks, "Step");
        if a.as_ref().is_some_and(|t| classify::has_tie(t)) {
            let b = on.parse(&r.toks, "Step");
            if !b.as_ref().is_some_and(|t| classify::has_tie(t)) {
                sites += 1;
                if rest.iter().any(|x| x == "-a") {
                    println!("    site: {}", r.step.text);
                }
            } else {
                unresolved += 1;
            }
        }
    }
    println!("attachment sites (ties with maximal munch off): resolved by maximal munch {sites}, still tied {unresolved}");
    // tier curve
    let tiers: Vec<u8> = {
        let mut t: Vec<u8> = g.rules.iter().map(|r| r.tier).collect();
        t.sort();
        t.dedup();
        t
    };
    for t in tiers {
        let mut p = engine::Parser::new(g, t, false);
        let ok = rows.iter().filter(|r| p.parse(&r.toks, "Step").is_some()).count();
        let nr = grammar::RULES.iter().filter(|r| r.3 <= t && !r.0.starts_with("H")).count();
        println!("  tier {t}: {nr} templates, {ok} steps ({})", pct(ok, n));
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("spec-gen: {e}");
            ExitCode::FAILURE
        }
    }
}
