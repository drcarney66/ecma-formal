//! `jsgrammar --spec SPEC.HTML --out DIR`: ECMA-262's grammars as Lean data.
//!
//! Reads every `<emu-grammar type="definition">` block of spec.html (not the
//! examples): the lexical, syntactic, RegExp and numeric string grammars, the
//! supplemental (cover) grammars and Annex B's overlays, and writes
//! `lean/Ecma/Grammar/Gen/*.lean` into DIR (deleting the other
//! `.lean` files there): constructor and `List` data in the forms of
//! `Grammar/Core.lean`, the enumerations of the nonterminals, the parameters
//! and each grammar's productions, the goal symbols, the covers, and §12.10's
//! answer for every `;` (docs/parser/GRAMMAR.md). It fails on any form it
//! does not understand, and checks that every `<emu-prodref>` of Annex A
//! names a definition (and its label).
//!
//! The production, nonterminal and parameter ids are the kept ones of
//! `--ids DIR` (else the directory of the first `--readings` file):
//! prod-ids.txt, nt-ids.txt and param-ids.txt (`jsgrammar::ids`), which
//! `--out` writes back into DIR beside the modules.
//!
//! `bazel run //:jsgrammar` runs it on the pinned spec.html, and
//! //:jsgrammar_regen_test checks that the checked-in files are its output.

mod emit;
mod readings;

use jsgrammar::gl::{Gl, G};
use jsgrammar::ids::{self, KeptIds};
use jsgrammar::grammar::{self, parse_alt, terminal_text, Arg, Body, Colons, Item, Rule, Sym, Terminal};
use jsgrammar::spec::Prose;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::path::PathBuf;
use std::process::ExitCode;

/// The most alternatives a data module holds (docs/parser/GRAMMAR.md: each
/// generated module elaborates in ≤ 10 s).
const SHARD_ALTS: usize = 300;

/// The most key blocks one list literal holds.
const KEY_CHUNK: usize = 200;

/// A production: its grammar, its rule (lhs), the alternative (or the `one of`
/// terminal) and its name.
struct Prod<'a> {
    rule: &'a Rule,
    alt: Option<&'a grammar::Alt>,
    name: String,
}

fn productions<'a>(rules: &[&'a Rule]) -> Vec<Prod<'a>> {
    let mut out = Vec::new();
    for r in rules {
        let c = match r.colons {
            Colons::One => ":",
            Colons::Two => "::",
            Colons::Three => ":::",
        };
        match &r.body {
            Body::Alts(alts) => {
                for a in alts {
                    out.push(Prod {
                        rule: r,
                        alt: Some(a),
                        name: format!("{} {c} {}", r.lhs, a.text),
                    });
                }
            }
            Body::OneOf(rows) => {
                for t in rows.iter().flatten() {
                    out.push(Prod {
                        rule: r,
                        alt: None,
                        name: format!("{} {c} {}", r.lhs, terminal_text(t)),
                    });
                }
            }
        }
    }
    out
}

/// `Name` with its first letter lowered (`RegExp` -> `regExp`), an acronym all of it (`JSON` -> `json`).
fn lean_ctor(n: &str) -> String {
    if n.chars().all(|c| c.is_ascii_uppercase()) {
        return n.to_ascii_lowercase();
    }
    let mut c = n.chars();
    let f = c.next().unwrap().to_ascii_lowercase();
    format!("{f}{}", c.as_str())
}

/// `Name[args]` (a goal symbol as the text writes it).
fn parse_instance(t: &str) -> Result<(String, Vec<Arg>), String> {
    let a = parse_alt(t)?;
    match a.rhs.as_slice() {
        [Item::Sym(Sym::Nt(n, args), false)] if a.guard.is_empty() => Ok((n.clone(), args.clone())),
        _ => Err(format!("not a goal symbol: {t}")),
    }
}

/// The shape of a right-hand side, to find a production the text names
/// without its parameters: its symbols' names.
fn shape(rhs: &[Item]) -> Vec<String> {
    let key = |s: &Sym| match s {
        Sym::T(Terminal::Text(t, _)) => format!("`{t}`"),
        Sym::T(Terminal::Cp(c)) => format!("<{c}>"),
        Sym::Nt(n, _) => n.clone(),
    };
    rhs.iter()
        .filter_map(|i| match i {
            Item::Sym(s, opt) => Some(format!("{}{}", key(s), if *opt { "?" } else { "" })),
            Item::ButNot(b, _) => Some(key(b)),
            _ => None,
        })
        .collect()
}

/// The text of `--json`'s file, if given.
fn json_text(json_path: Option<&str>) -> Result<Option<String>, String> {
    json_path.map(|p| std::fs::read_to_string(p).map_err(|e| format!("{p}: {e}"))).transpose()
}

/// The kept id tables (`jsgrammar::ids`) in `dir`: none without one.
fn kept_ids(dir: Option<&str>) -> Result<KeptIds, String> {
    dir.map_or(Ok(KeptIds::default()), |d| ids::read_dir(std::path::Path::new(d)))
}

/// A constructor of `NT` or `Param`: the name, or `retired_Name` for one the grammar no longer has.
fn symbol_ctor(n: &str, live: bool) -> String {
    if live {
        n.to_string()
    } else {
        format!("retired_{n}")
    }
}

fn run(spec_path: &str, out_dir: &str, readings_paths: &[String], json_path: Option<&str>, ids_dir: Option<&str>) -> Result<(), String> {
    let text = std::fs::read_to_string(spec_path).map_err(|e| format!("{spec_path}: {e}"))?;
    let gl = Gl::load_with(&text, json_text(json_path)?.as_deref(), &kept_ids(ids_dir)?)?;
    let (spec, blocks, nts, params) = (&gl.spec, &gl.blocks, &gl.nts, &gl.params);
    let by_g: BTreeMap<G, Vec<(&Rule, &str, &str)>> = gl
        .by_g
        .iter()
        .map(|(g, v)| (*g, v.iter().map(|&(b, r)| (&blocks[b].rules[r], blocks[b].clause.as_str(), blocks[b].file)).collect()))
        .collect();

    let mut files: BTreeMap<String, String> = BTreeMap::new();
    let ns = "Ecma.Grammar";

    // Symbols.
    {
        let mut body = String::new();
        writeln!(
            body,
            "/-- The grammar parameters (§5.1.6), numbered by spec/formal/param-ids.txt (`ParamId` is the constructor\n\
             index): each keeps its number and a new one takes the next, in the order spec.html first declares\n\
             them; one the grammar no longer has stays, as `retired_Name`. -/"
        )
        .unwrap();
        writeln!(body, "inductive Param where").unwrap();
        for (p, &l) in params.iter().zip(&gl.param_live) {
            writeln!(body, "  | {}", symbol_ctor(p, l)).unwrap();
        }
        writeln!(body, "  deriving BEq, Inhabited\n").unwrap();
        writeln!(body, "/-- The nonterminals, numbered by spec/formal/nt-ids.txt (`NtId` is the constructor index): each\nkeeps its number and a new one takes the next, in the order of their first definitions in spec.html\n(then any referenced but never defined, which the lints report, then json.emu's); one the grammar no\nlonger has stays, as `retired_Name`. -/").unwrap();
        writeln!(body, "inductive NT where").unwrap();
        for (n, &l) in nts.iter().zip(&gl.nt_live) {
            writeln!(body, "  | {}", symbol_ctor(n, l)).unwrap();
        }
        writeln!(body, "  deriving BEq, Inhabited\n").unwrap();
        writeln!(body, "/-- `Param`'s names, in its order. -/").unwrap();
        writeln!(
            body,
            "def Param.names : List String :=\n  [{}]\n",
            params
                .iter()
                .map(|p| emit::lean_string(p))
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
        writeln!(body, "/-- `NT`'s names, in its order. -/").unwrap();
        let names: Vec<String> = nts.iter().map(|n| emit::lean_string(n)).collect();
        writeln!(body, "def NT.names : List String :=\n  [{}]\n", names.join(",\n   ")).unwrap();
        writeln!(body, "/-- Every `NT`, in its order. -/").unwrap();
        let all: Vec<String> = nts.iter().zip(&gl.nt_live).map(|(n, &l)| format!(".{}", symbol_ctor(n, l))).collect();
        writeln!(body, "def NT.all : List NT :=\n  [{}]\n", all.join(",\n   ")).unwrap();
        files.insert(
            "Symbols".into(),
            emit::module(
                &[],
                "# The nonterminals and parameters of ECMA-262's grammars",
                ns,
                &body,
            ),
        );
    }

    // Each grammar's rules, sharded; its productions; and its list of rules.
    let core = "Ecma.Grammar.Core".to_string();
    let mut index_imports = Vec::new();
    let mut index = String::new();
    let mut rule_ref: BTreeMap<(G, String), String> = BTreeMap::new();
    for g in G::ALL {
        let Some(rs) = by_g.get(&g) else { continue };
        let gns = format!("{ns}.Gen.{}", g.name());
        let mut shards: Vec<Vec<(&Rule, &str, &str)>> = vec![Vec::new()];
        let mut n = 0;
        for (r, c, f) in rs {
            let k = match &r.body {
                Body::Alts(a) => a.len(),
                Body::OneOf(rows) => rows.iter().map(|r| r.len()).sum::<usize>() / 4 + 1,
            };
            if n + k > SHARD_ALTS && !shards.last().unwrap().is_empty() {
                shards.push(Vec::new());
                n = 0;
            }
            n += k;
            shards.last_mut().unwrap().push((r, c, f));
        }
        let single = shards.len() == 1;
        for (k, shard) in shards.iter().enumerate() {
            let file = if single {
                g.name().to_string()
            } else {
                format!("{}{}", g.name(), k + 1)
            };
            let mut body = String::new();
            for (r, c, f) in shard {
                emit::rule_def(&mut body, r, c, f)?;
                rule_ref.insert((g, r.lhs.clone()), format!("Gen.{}.{}", g.name(), r.lhs));
            }
            let doc = format!(
                "# {}{}",
                g.doc(),
                if single {
                    String::new()
                } else {
                    format!(", part {}", k + 1)
                }
            );
            files.insert(file.clone(), emit::module(&[core.clone()], &doc, &gns, &body));
            index_imports.push(format!("Ecma.Grammar.Gen.{file}"));
        }

        let rules: Vec<&Rule> = rs.iter().map(|(r, _, _)| *r).collect();
        let prods = productions(&rules);
        let mut seen = BTreeSet::new();
        let mut body = String::new();
        writeln!(
            body,
            "/-- The productions of {}, named by their text in spec.html (character references\n\
             decoded, without labels), in spec order: the i-th is the i-th alternative of\n\
             `Gen.{}.rules` (a `one of` definition's terminals one by one). -/",
            g.doc(),
            g.name()
        )
        .unwrap();
        writeln!(body, "inductive Production where").unwrap();
        for p in &prods {
            if !seen.insert(p.name.clone()) {
                return Err(format!("{}:{}: two productions `{}`", rs[0].2, p.rule.line, p.name));
            }
            writeln!(body, "  | {}", emit::guillemets(&p.name)?).unwrap();
        }
        writeln!(body, "  deriving BEq, Inhabited\n").unwrap();
        let file = format!("{}Prod", g.name());
        files.insert(
            file.clone(),
            emit::module(&[], &format!("# The productions of {}", g.doc()), &gns, &body),
        );
        index_imports.push(format!("Ecma.Grammar.Gen.{file}"));

        writeln!(index, "/-- The rules of {}, in spec order. -/", g.doc()).unwrap();
        let refs: Vec<String> = rules.iter().map(|r| format!("Gen.{}.{}", g.name(), r.lhs)).collect();
        writeln!(
            index,
            "def Gen.{}.rules : List Rule :=\n  [{}]\n",
            g.name(),
            refs.join(",\n   ")
        )
        .unwrap();
    }

    writeln!(index, "/-- Each grammar with its rules, in GL's order. -/").unwrap();
    let gs: Vec<String> = G::ALL
        .iter()
        .filter(|g| by_g.contains_key(g))
        .map(|g| format!("(.{}, Gen.{}.rules)", lean_ctor(g.name()), g.name()))
        .collect();
    writeln!(index, "def Gen.grammars : List (GrammarId × List Rule) :=\n  [{}]\n", gs.join(",\n   ")).unwrap();

    // The kept production ids, as runs of consecutive numbers.
    let mut runs: Vec<(usize, usize)> = Vec::new();
    for &id in &gl.prod_ids {
        match runs.last_mut() {
            Some((a, n)) if *a + *n == id => *n += 1,
            _ => runs.push((id, 1)),
        }
    }
    writeln!(
        index,
        "/-- The production id of each right-hand side of `Gen.grammars`, in `prodsOf`'s order: the number\n\
         spec/formal/prod-ids.txt gives it (`GL.ids`). A run `(a, n)` numbers the next `n` right-hand sides\n\
         `a`, `a + 1`, …, `a + n - 1`. -/\ndef Gen.prodIds : List (Nat × Nat) :=\n  [{}]\n",
        runs.iter().map(|(a, n)| format!("({a}, {n})")).collect::<Vec<_>>().join(",\n   ")
    )
    .unwrap();
    writeln!(
        index,
        "/-- The number past every production id of spec/formal/prod-ids.txt, a retired one's included: a\n\
         reading's own right-hand sides are numbered from it. -/\ndef Gen.prodNext : Nat := {}\n",
        gl.prod_numbering.next()
    )
    .unwrap();

    // The blocks, in spec order.
    let mut block_names = Vec::new();
    for b in blocks {
        let kind = match &b.prose {
            Prose::Main => ".main".to_string(),
            Prose::Supplemental { cover, .. } => format!(".supplemental .{cover}"),
            Prose::Overlay { section, mode, cond } => format!(".overlay .{section} .{mode} .{cond}"),
        };
        let rules: Vec<String> = b
            .rules
            .iter()
            .map(|r| rule_ref[&(b.g, r.lhs.clone())].clone())
            .collect();
        let name = if b.g == G::Json { format!("blockJSON{}", b.line) } else { format!("block{}", b.line) };
        writeln!(
            index,
            "def Gen.{name} : Block :=\n  ⟨{}, {}, {kind}, [{}], {}, [{}]⟩\n",
            emit::lean_string(&b.clause),
            b.line,
            rules.join(", "),
            b.indent,
            b.rules
                .iter()
                .enumerate()
                .filter(|(_, r)| r.fmt_ignore)
                .map(|(k, _)| k.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
        block_names.push(format!("Gen.{name}"));
    }
    writeln!(index, "/-- spec.html's definition blocks, in its order. -/").unwrap();
    writeln!(
        index,
        "def Gen.blocks : List Block :=\n  [{}]\n",
        block_names.join(",\n   ")
    )
    .unwrap();

    // The goal symbols.
    let mut goals: Vec<(String, Vec<Arg>, usize, &str)> = Vec::new();
    let mut add_goal = |n: String, a: Vec<Arg>, line: usize, src: &'static str| {
        if !goals.iter().any(|(m, b, _, _)| *m == n && *b == a) {
            goals.push((n, a, line, src));
        }
    };
    for gr in spec.goals.iter().chain(spec.must_cover.iter()) {
        let (n, a) = parse_instance(&grammar::decode(&gr.text)?).map_err(|e| format!("spec.html:{}: {e}", gr.line))?;
        add_goal(n, a, gr.line, gr.src);
    }
    for b in blocks {
        if let Prose::Supplemental { .. } = b.prose {
            add_goal(b.rules[0].lhs.clone(), Vec::new(), b.line, "supplemental");
        }
    }
    for c in &spec.refined_copies {
        let first = if c.text.starts_with('\n') { c.line } else { c.line - 1 };
        let lhs = grammar::parse_block(&c.text, first)?.remove(0).lhs;
        add_goal(lhs, Vec::new(), c.line, "copy");
    }
    if let Some((n, line)) = &gl.json_goal {
        add_goal(n.clone(), Vec::new(), *line, "json");
    }
    for (n, _, line, _) in &goals {
        if !nts.contains(n) {
            return Err(format!("spec.html:{line}: the goal symbol {n} has no definition"));
        }
    }
    writeln!(
        index,
        "/-- The goal symbols spec.html names, with the line of their first mention: the
grammars' goal symbols (§5.1.1–§5.1.5), ParseText's goals, CreateDynamicFunction's
grammar symbols, and the supplemental grammars' (\"must cover\"); then json.emu's
(its line there). -/"
    )
    .unwrap();
    let goal_lines: Vec<String> = goals
        .iter()
        .map(|(n, a, l, src)| format!("⟨.{n}, {}, {l}, .{src}⟩", emit::args(a)))
        .collect();
    writeln!(index, "def Gen.goals : List Goal :=\n  [{}]\n", goal_lines.join(",\n   ")).unwrap();

    // The covers: the supplemental blocks, and the copies of definitions
    // that the prose names as supplemental grammars (each checked against its
    // definition).
    let syn_rules: Vec<&Rule> = by_g[&G::Syntactic].iter().map(|(r, _, _)| *r).collect();
    let syn = productions(&syn_rules);
    let mut copies = Vec::new();
    for c in &spec.refined_copies {
        let first = if c.text.starts_with('\n') { c.line } else { c.line - 1 };
        let rules = grammar::parse_block(&c.text, first)?;
        let [copy] = rules.as_slice() else {
            return Err(format!(
                "spec.html:{}: a supplemental grammar copy of {} rules",
                c.line,
                rules.len()
            ));
        };
        let def = syn_rules
            .iter()
            .find(|r| r.lhs == copy.lhs)
            .ok_or_else(|| format!("spec.html:{}: {} has no definition", c.line, copy.lhs))?;
        let texts = |r: &Rule| match &r.body {
            Body::Alts(a) => a.iter().map(|a| a.text.clone()).collect::<Vec<_>>(),
            Body::OneOf(_) => Vec::new(),
        };
        if def.params != copy.params || def.colons != copy.colons || texts(def) != texts(copy) {
            return Err(format!(
                "spec.html:{}: the supplemental grammar's {} differs from its definition (spec.html:{})",
                c.line, copy.lhs, def.line
            ));
        }
        copies.push((c, copy.lhs.clone()));
    }
    let mut covers = Vec::new();
    let supplementals = blocks
        .iter()
        .map(|b| (&b.prose, b.line, b.rules.first().map(|r| r.lhs.clone())))
        .chain(copies.iter().map(|(c, lhs)| (&c.prose, c.line, Some(lhs.clone()))));
    let mut sorted: Vec<_> = supplementals.collect();
    sorted.sort_by_key(|(_, line, _)| *line);
    for (prose, line, refined) in sorted {
        let Prose::Supplemental { context, cover } = prose else {
            continue;
        };
        let refined = refined.unwrap();
        let context = grammar::decode(context)?;
        let (lhs, rhs) = context
            .split_once(" : ")
            .ok_or_else(|| format!("spec.html:{line}: a production `{context}`"))?;
        let lhs = lhs.split('[').next().unwrap();
        let want = shape(&parse_alt(rhs).map_err(|e| format!("spec.html:{line}: {e}"))?.rhs);
        let found: Vec<&Prod> = syn
            .iter()
            .filter(|p| p.rule.lhs == lhs && p.alt.is_some_and(|a| shape(&a.rhs) == want))
            .collect();
        let [p] = found.as_slice() else {
            return Err(format!(
                "spec.html:{line}: `{context}` names {} productions",
                found.len()
            ));
        };
        covers.push(format!(
            "⟨.{}, .{cover}, .{refined}, {line}⟩",
            emit::guillemets(&p.name)?
        ));
    }
    writeln!(
        index,
        "/-- The supplemental-grammar covers (§5.1.5): the supplemental grammars, with the\nproduction whose instance they refine. Not the early errors' \"must cover\" sites\n(`Cover`). -/"
    )
    .unwrap();
    writeln!(
        index,
        "def Gen.covers : List (Cover Gen.Syntactic.Production) :=\n  [{}]\n",
        covers.join(",\n   ")
    )
    .unwrap();

    // §12.10 for each `;`.
    let rules_of = |n: &'static str| syn.iter().filter(move |p| p.rule.lhs == n);
    for n in [
        "EmptyStatement",
        "ForStatement",
        "DoWhileStatement",
        "LexicalDeclaration",
    ] {
        if rules_of(n).next().is_none() {
            return Err(format!("no {n} in the syntactic grammar (§12.10's semicolons)"));
        }
    }
    if !rules_of("ForStatement").any(|p| {
        p.alt.is_some_and(|a| {
            a.rhs
                .iter()
                .any(|i| matches!(i, Item::Sym(Sym::Nt(n, _), false) if n == "LexicalDeclaration"))
        })
    }) {
        return Err("ForStatement no longer has `for ( LexicalDeclaration …` (§12.10's semicolons)".into());
    }
    // The nonterminals that end a LexicalDeclaration (by their last symbols).
    let mut ends: BTreeSet<String> = BTreeSet::from(["LexicalDeclaration".to_string()]);
    loop {
        let mut more = Vec::new();
        for p in &syn {
            if !ends.contains(&p.rule.lhs) {
                continue;
            }
            let last = p
                .alt
                .and_then(|a| a.rhs.iter().rev().find(|i| !matches!(i, Item::Look(_) | Item::NoLT)));
            if let Some(Item::Sym(Sym::Nt(m, _), _)) = last {
                if !ends.contains(m) {
                    more.push(m.clone());
                }
            }
        }
        if more.is_empty() {
            break;
        }
        ends.extend(more);
    }
    let mut semis = Vec::new();
    for p in &syn {
        let Some(a) = p.alt else { continue };
        let last = a.rhs.iter().rposition(|i| !matches!(i, Item::Look(_) | Item::NoLT));
        for (k, i) in a.rhs.iter().enumerate() {
            let semi = match i {
                Item::Sym(Sym::T(Terminal::Text(t, _)), opt) if t == ";" => {
                    if *opt {
                        return Err(format!("spec.html:{}: an optional `;`", p.rule.line));
                    }
                    true
                }
                _ => false,
            };
            if !semi {
                continue;
            }
            let flag = match p.rule.lhs.as_str() {
                "EmptyStatement" => "emptyStatement",
                "ForStatement" => "forHeader",
                "DoWhileStatement" => "doWhile",
                n if ends.contains(n) && Some(k) == last => "forHeaderIfDeclaration",
                _ => "insertable",
            };
            semis.push(format!("⟨.{}, {k}, .{flag}⟩", emit::guillemets(&p.name)?));
        }
    }
    for (r, _, _) in by_g.get(&G::AnnexB).into_iter().flatten() {
        if let Body::Alts(alts) = &r.body {
            if r.colons == Colons::One
                && alts.iter().any(|a| {
                    a.rhs
                        .iter()
                        .any(|i| matches!(i, Item::Sym(Sym::T(Terminal::Text(t, _)), _) if t == ";"))
                })
            {
                return Err(format!("spec.html:{}: an Annex B production with a `;`", r.line));
            }
        }
    }
    writeln!(
        index,
        "/-- §12.10 for every `;` of the syntactic grammar's productions: whether a virtual
`;` may stand there. -/"
    )
    .unwrap();
    writeln!(
        index,
        "def Gen.semis : List (SemiSite Gen.Syntactic.Production) :=\n  [{}]\n",
        semis.join(",\n   ")
    )
    .unwrap();

    // The overlay files: the readings of rules and the errata's orphan rows.
    let ovl_texts = readings_paths.iter().map(|p| std::fs::read_to_string(p).map_err(|e| format!("{p}: {e}"))).collect::<Result<Vec<_>, _>>()?;
    let ovl_names: Vec<_> = readings_paths.iter().map(|p| p.rsplit('/').next().unwrap_or(p)).collect();
    let ovl: Vec<(&str, &str)> = ovl_names.iter().zip(&ovl_texts).map(|(n, t)| (*n, t.as_str())).collect();
    let orphans = readings::orphans(&ovl)?;
    let mut orphans_met = vec![false; orphans.len()];
    let squash = |t: &str| t.split_whitespace().collect::<Vec<_>>().join(" ");

    // The key blocks, with the ids they name.
    let mut kb = String::new();
    let mut ks = Vec::new();
    for k in &spec.keys {
        let ids = match gl.resolve(&k.text, &k.clause) {
            Ok(ids) => ids,
            // a row an erratum says names no production of the grammar: no ids
            Err(e) => match orphans.iter().position(|o| o.clause == k.clause && squash(&o.grammar) == squash(&k.text)) {
                Some(i) => {
                    orphans_met[i] = true;
                    vec![]
                }
                None => return Err(format!("spec.html:{}: {e}", k.line)),
            },
        };
        ks.push(format!(
            "⟨{}, {}, {}, [{}]⟩",
            emit::lean_string(&k.clause),
            k.line,
            emit::lean_string(&k.text),
            ids.iter().map(|&i| gl.kept_id(i).to_string()).collect::<Vec<_>>().join(", ")
        ));
    }
    // Lists of at most KEY_CHUNK literals: a longer one exceeds the elaborator's recursion depth.
    let mut parts = Vec::new();
    for (i, c) in ks.chunks(KEY_CHUNK).enumerate() {
        writeln!(kb, "def Gen.keys{i} : List KeyBlock :=\n  [{}]\n", c.join(",\n   ")).unwrap();
        parts.push(format!("Gen.keys{i}"));
    }
    writeln!(kb, "/-- spec.html's non-definition `<emu-grammar>` blocks, in its order, with the\nproduction ids each names. -/").unwrap();
    writeln!(kb, "def Gen.keys : List KeyBlock :=\n  {}\n", parts.join(" ++ ")).unwrap();
    files.insert(
        "Keys".into(),
        emit::module(&[core.clone()], "# The key blocks of spec.html and the productions they name", ns, &kb),
    );

    if let Some((o, _)) = orphans.iter().zip(&orphans_met).find(|(_, m)| !**m) {
        return Err(format!("erratum {}: the row {} of {} names a production of the grammar now, or is gone", o.erratum, o.grammar, o.clause));
    }

    // The readings of rules, each erratum's by its kept id (erratum-ids.txt beside the first overlay file).
    let rs = readings::scan(&ovl)?;
    let ids_path = readings_paths.first().map(|p| std::path::Path::new(p).with_file_name("erratum-ids.txt"));
    let kept = match &ids_path {
        Some(p) if p.exists() => readings::erratum_ids(&std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?),
        _ => Default::default(),
    };
    let mut rb = String::new();
    let (mut rds, mut rbs, mut hashes) = (Vec::new(), Vec::new(), Vec::new());
    for r in &rs {
        let at = |e: String| format!("{}:{}: {e}", r.file, r.line);
        let first = if r.text.starts_with('\n') { r.line } else { r.line - 1 };
        let rules = grammar::parse_block(&r.text, first).map_err(at)?;
        let [rule] = rules.as_slice() else {
            return Err(at(format!("{} definitions, not 1", rules.len())));
        };
        if rule.lhs != r.rule {
            return Err(at(format!("a definition of {}, not {}", rule.lhs, r.rule)));
        }
        let b = blocks
            .iter()
            .find(|b| b.clause == r.clause && b.rules.iter().any(|x| x.lhs == r.rule))
            .ok_or_else(|| at(format!("no definition of {} in {}", r.rule, r.clause)))?;
        let indent = grammar::layout(&r.text, &rules).ok_or_else(|| at("a layout this generator does not know".into()))?;
        emit::rule_def(&mut rb, rule, &r.clause, &r.file)?;
        let erratum = match &r.erratum_name {
            None => "none".to_string(),
            Some(n) => match kept.get(n) {
                Some(id) => format!("some {id}"),
                None if kept.is_empty() => format!("some {}", r.erratum.unwrap_or_default()),
                None => return Err(format!("{}:{}: erratum {n} has no id in erratum-ids.txt", r.file, r.line)),
            },
        };
        rds.push(format!("⟨{erratum}, .{}, {}⟩", lean_ctor(b.g.name()), rule.lhs));
        rbs.push(format!("⟨{}, {}, .main, [{}], {indent}, []⟩", emit::lean_string(&r.clause), r.line, rule.lhs));
        hashes.push(emit::lean_string(&r.hash));
    }
    writeln!(rb, "/-- The readings of rules, in the overlay's order. -/").unwrap();
    writeln!(rb, "def readings : List RuleReading :=\n  [{}]\n", rds.join(",\n   ")).unwrap();
    writeln!(rb, "/-- Each reading's definition as a block of the overlay (its line there). -/").unwrap();
    writeln!(rb, "def blocks : List Block :=\n  [{}]\n", rbs.join(",\n   ")).unwrap();
    writeln!(rb, "/-- Each reading's `hash`: SHA-256 of the pinned definition's text. -/").unwrap();
    writeln!(rb, "def hashes : List String :=\n  [{}]\n", hashes.join(", ")).unwrap();
    files.insert(
        "Readings".into(),
        emit::module(&[core.clone()], "# The readings of grammar rules (the `<emu-rule-reading>`s of spec/formal)", &format!("{ns}.Gen.Reading"), &rb),
    );

    files.insert(
        "Index".into(),
        emit::module(
            &index_imports,
            "# ECMA-262's grammars: the rules of each grammar, the blocks, the goal symbols,\nthe covers and the semicolons",
            ns,
            &index,
        ),
    );

    // The kept tables, written back beside the modules (scripts/jsgrammar.py moves them to spec/formal).
    let tables = [
        (ids::PROD_IDS, gl.prod_numbering.render(ids::PROD_IDS)),
        (ids::NT_IDS, gl.nt_numbering.render(ids::NT_IDS)),
        (ids::PARAM_IDS, gl.param_numbering.render(ids::PARAM_IDS)),
    ];

    // Write the files, and delete the directory's other `.lean` files.
    let dir = PathBuf::from(out_dir);
    std::fs::create_dir_all(&dir).map_err(|e| format!("{out_dir}: {e}"))?;
    for entry in std::fs::read_dir(&dir).map_err(|e| format!("{out_dir}: {e}"))? {
        let p = entry.map_err(|e| e.to_string())?.path();
        let stem = p.file_stem().and_then(|s| s.to_str()).unwrap_or_default().to_string();
        if p.extension().is_some_and(|e| e == "lean") && !files.contains_key(&stem) {
            std::fs::remove_file(&p).map_err(|e| format!("{}: {e}", p.display()))?;
        }
    }
    for (name, text) in &files {
        let p = dir.join(format!("{name}.lean"));
        if std::fs::read_to_string(&p).ok().as_deref() != Some(text) {
            std::fs::write(&p, text).map_err(|e| format!("{}: {e}", p.display()))?;
        }
    }
    for (name, text) in &tables {
        let p = dir.join(name);
        std::fs::write(&p, text).map_err(|e| format!("{}: {e}", p.display()))?;
    }
    Ok(())
}

/// `--prods`: GL's numbering, as the index's `prod` lines.
fn prods(spec_path: &str, json_path: Option<&str>, ids_dir: Option<&str>) -> Result<(), String> {
    let text = std::fs::read_to_string(spec_path).map_err(|e| format!("{spec_path}: {e}"))?;
    for l in Gl::load_with(&text, json_text(json_path)?.as_deref(), &kept_ids(ids_dir)?)?.prod_lines() {
        println!("prod {l}");
    }
    Ok(())
}

/// `--keys`: every non-definition block of spec.html resolved: `key LINE
/// CLAUSE IDS`, or `residue LINE CLAUSE REASON`.
fn keys(spec_path: &str, ids_dir: Option<&str>) -> Result<(), String> {
    let text = std::fs::read_to_string(spec_path).map_err(|e| format!("{spec_path}: {e}"))?;
    let gl = Gl::load_with(&text, None, &kept_ids(ids_dir)?)?;
    for k in &gl.spec.keys {
        match gl.resolve(&k.text, &k.clause) {
            Ok(ids) => println!(
                "key {} {} {}",
                k.line,
                k.clause,
                ids.iter().map(|&i| gl.kept_id(i).to_string()).collect::<Vec<_>>().join(",")
            ),
            Err(e) => println!("residue {} {} {e}", k.line, k.clause),
        }
    }
    Ok(())
}

const USAGE: &str =
    "usage: jsgrammar --spec SPEC.HTML [--json JSON.EMU] [--ids DIR] (--out DIR [--readings FILE.EMU]... | --prods | --keys)";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let (mut spec, mut out, mut mode, mut rdg, mut json, mut ids_dir) = (None, None, None, Vec::new(), None, None);
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--spec" if i + 1 < args.len() => spec = Some(args[i + 1].clone()),
            "--out" if i + 1 < args.len() => out = Some(args[i + 1].clone()),
            "--readings" if i + 1 < args.len() => rdg.push(args[i + 1].clone()),
            "--json" if i + 1 < args.len() => json = Some(args[i + 1].clone()),
            "--ids" if i + 1 < args.len() => ids_dir = Some(args[i + 1].clone()),
            m @ ("--prods" | "--keys") => {
                mode = Some(m.to_string());
                i += 1;
                continue;
            }
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        }
        i += 2;
    }
    // the kept tables: --ids, else beside the first overlay file (as erratum-ids.txt)
    let ids_dir = ids_dir.or_else(|| {
        rdg.first().map(|p| std::path::Path::new(p).parent().map_or(".".into(), |d| d.display().to_string()))
    });
    let ids_dir = ids_dir.as_deref();
    let r = match (spec, out, mode.as_deref()) {
        (Some(spec), Some(out), None) => run(&spec, &out, &rdg, json.as_deref(), ids_dir),
        (Some(spec), None, Some("--prods")) => prods(&spec, json.as_deref(), ids_dir),
        (Some(spec), None, Some("--keys")) => keys(&spec, ids_dir),
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("jsgrammar: {e}");
            ExitCode::FAILURE
        }
    }
}
