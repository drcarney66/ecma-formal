//! The `<emu-alg example>` blocks of §5.2 as test data: Ecma.Gen.Examples, which
//! the base does not import. Each is a headerless Alg named by its spec.html line; its
//! parameters are its free variables in first-use order; an operation the spec does not
//! define (`AO`, `Other`, …) is a primitive call, by name in the module's prim table. Ids
//! are ⟨C + k, 0⟩ for the kth example, C the number of clauses, so none is a clause's. The
//! example after `<emu-grammar example>` (spec.html:1025, `Block : { StatementList }`'s
//! Evaluation) is headerless too, its `|StatementList|` a symbol.

use crate::conv::{Conv, Vars};
use crate::data::Data;
use crate::grammar::Grammar;
use crate::lean::{array, closures, list, meaning, nodes, phrase_cat, piece, s};
use crate::spec::{Spec, Step};
use std::collections::HashMap;
use std::fmt::Write;
use std::path::Path;

pub fn write(sp: &Spec, g: &Grammar, dt: &Data, dir: &Path) -> Result<String, String> {
    let base = &dt.decls;
    let mut d = base.clone();
    let anchors: crate::conv::Anchors = HashMap::new();
    let mut defs = Vec::new();
    let mut names = Vec::new();
    for (k, a) in sp.algs.iter().filter(|a| a.example()).enumerate() {
        let rows = crate::classify::classify_steps(g, a, &a.steps);
        let by_step: HashMap<*const Step, &crate::classify::Row> = rows.iter().map(|r| (r.step as *const Step, r)).collect();
        let convert = |vars: Vars, d: &mut crate::decls::Decls| {
            let mut cv = Conv {
                open: Vec::new(),
                rhs: Default::default(),
                lhs: Default::default(),
                narrow: Vec::new(),
                symbols: false,
                channel: crate::ast::Channel::Pending,
                anchors: &anchors,
                stops: None,
                readings: Vec::new(),
                g,
                d,
                env: &dt.env,
                vars,
                rows: &by_step,
                toks: Vec::new(),
                text: String::new(),
                unresolved: Vec::new(),
                exceptions: Vec::new(),
                closures: Vec::new(),
                base: a.base,
                clause: a.clause.map(|c| sp.clauses[c].id.clone()).unwrap_or_default(),
            };
            let body = cv.steps(&a.steps);
            (body, cv.vars, cv.closures, cv.exceptions)
        };
        // the free variables, then the conversion with them first
        let (_, v0, _, _) = convert(Vars::default(), &mut d.clone());
        let free: Vec<String> = v0.names.iter().enumerate().filter(|(i, _)| !v0.bound.contains(i)).map(|(_, n)| n.clone()).collect();
        let mut vars = Vars::default();
        for f in &free {
            vars.slot(f);
        }
        let (body, vars, clos, exceptions) = convert(vars, &mut d);
        if let Some((t, why)) = exceptions.first() {
            return Err(format!("spec.html:{}: an example step without a data shape: {t} ({why})", a.line));
        }
        if crate::print::body(&d, &vars.names, &clos, &body, a.base, a.close_indent) != a.raw {
            return Err(format!("spec.html:{}: the example does not print back", a.line));
        }
        let name = format!("«ex{}»", a.line);
        let params = (0..free.len()).map(|x| format!("{{ x := {x}, ty := none, optional := false, rest := false }}")).collect::<Vec<_>>().join(", ");
        let vs = vars.names.iter().map(|v| s(v)).collect::<Vec<_>>().join(", ");
        defs.push(format!(
            "/-- spec.html:{} -/\ndef {name} : Alg := {{\n  id := ⟨{}, 0⟩\n  name := {}\n  header := {{ kind := .untyped, params := [{params}], ret := none, recv := none, desc := [] }}\n  vars := #[{vs}]\n  attrs := [⟨\"example\", none⟩]\n  indent := {}\n  body := {}\n  closures := {} }}\n",
            a.line,
            base.clauses.names.len() + k,
            s(&format!("ex{}", a.line)),
            a.close_indent,
            nodes(&body),
            closures(&clos)
        ));
        names.push(name);
    }
    let mut fs = Vec::new();
    for (f, t, b) in [
        ("fields", &d.fields, &base.fields),
        ("enums", &d.enums, &base.enums),
        ("sdos", &d.sdos, &base.sdos),
        ("nts", &d.nts, &base.nts),
        ("prims", &d.prims, &base.prims),
        ("sorts", &d.sorts, &base.sorts),
        ("methods", &d.methods, &base.methods),
    ] {
        if t.names.len() > b.names.len() {
            fs.push(format!("{f} := Ecma.Gen.decls.{f} ++ {}", array(t.names[b.names.len()..].iter().map(|x| s(x)).collect())));
        }
    }
    if d.phrases.len() > base.phrases.len() {
        let rows = d.phrases[base.phrases.len()..].iter().map(|p| format!("{{ cat := {}, template := {}, meaning := {} }}", phrase_cat(p.cat), list(&p.template, piece), meaning(&p.meaning)));
        fs.push(format!("phrases := Ecma.Gen.decls.phrases ++ {}", array(rows.collect())));
    }
    let mut o = String::new();
    writeln!(o, "module\n\npublic import Ecma.Gen.Decls\n\n/-! Generated by `spec-gen emit` (crates/spec-gen) from spec.html's `<emu-alg example>` blocks; do not edit. -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.Examples\n\nopen Ecma\n").unwrap();
    let decls = if fs.is_empty() { "Ecma.Gen.decls".to_string() } else { format!("{{ Ecma.Gen.decls with\n    {} }}", fs.join(",\n    ")) };
    writeln!(o, "/-- The declaration tables: the data's, and the names the examples add. -/\ndef decls : Decls := {decls}\n").unwrap();
    for x in &defs {
        writeln!(o, "{x}").unwrap();
    }
    writeln!(o, "/-- The examples, in document order. -/\ndef algs : List Alg := [{}]\n\nend Ecma.Gen.Examples", names.join(", ")).unwrap();
    std::fs::write(dir.join("Examples.lean"), o).map_err(|e| e.to_string())?;
    Ok(format!("wrote {} examples and Examples.lean", names.len()))
}
