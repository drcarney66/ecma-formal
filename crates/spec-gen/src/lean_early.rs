//! The Early Errors rows as Lean modules (`Ecma.Gen.Early*`): terms of
//! `Ecma.Notation.Early`, sharded at `SHARD_ROWS` rows or `SHARD_BYTES`
//! bytes; `Ecma.Gen.Early` lists the shards' rows.

use crate::ast::{Body, Channel, Hole, LiLayout, Stmt, UnlessForm};
use crate::data::{Data, EarlyRow};
use crate::decls::Decls;
use crate::lean::{cond, expr, list, s, stmt, ty, HEADER};
use crate::spec::Spec;
use std::fmt::Write;
use std::path::Path;

pub const SHARD_ROWS: usize = 300;
pub const SHARD_BYTES: usize = 300_000;

/// The ER phrases that `sentence` turns into EarlySentence constructors: never evaluated as phrases.
pub const ER_FORMS: &[&str] = &["syntax-error-ins", "must-cover", "rules-applied", "more-rules", "recursively-applied", "not-applied", "foreach-in"];

/// A sentence: the early-error forms by constructor, any other statement wrapped.
fn sentence(d: &Decls, st: &Stmt) -> Result<String, String> {
    Ok(match st {
        Stmt::SyntaxError(e, c, u) => {
            let u = match u {
                None => "none".to_string(),
                Some((f, c)) => {
                    let f = match f {
                        UnlessForm::Plain => ".plain",
                        UnlessForm::Comma => ".comma",
                        UnlessForm::Optional => ".optional",
                    };
                    format!("(some ({f}, {}))", cond(c))
                }
            };
            format!("(.syntaxError {e} {} {u})", cond(c))
        }
        Stmt::If(c, Body::Inline(x), arms, None) if arms.is_empty() => format!("(.ifInline {} {})", cond(c), sentence(d, x)?),
        Stmt::Phrase(p, hs) if d.phrases[*p].cat == "ER" => match (d.phrases[*p].name, hs.as_slice()) {
            ("syntax-error-ins", [Hole::C(a), Hole::C(b)]) => format!("(.syntaxErrorIns {} {})", cond(a), cond(b)),
            ("must-cover", [Hole::E(p), Hole::T(t)]) => format!("(.mustCover {} {})", expr(p), ty(t)),
            ("rules-applied", [Hole::E(crate::ast::Expr::Prod(ps, raw))]) => format!("(.rulesApplied {} {})", list(ps, |&p| crate::lean::pid(p).to_string()), s(raw)),
            ("more-rules" | "recursively-applied", _) => format!("(.info {})", stmt(st)),
            ("not-applied", [Hole::C(c), ..]) => format!("(.notApplied {} {})", cond(c), stmt(st)),
            ("foreach-in", [Hole::E(crate::ast::Expr::Nt(k, _)), Hole::B(x), Hole::E(l), Hole::Bc(_, c)]) => {
                format!("(.forEachIn {x} {} {} {} {})", ty(&crate::ast::TyExpr::Nt(String::new(), *k, String::new())), expr(l), cond(c), stmt(st))
            }
            (n, _) if ER_FORMS.contains(&n) => return Err(format!("ER phrase {} with holes {hs:?}", d.phrases[*p].name)),
            _ => format!("(.stmt {})", stmt(st)),
        },
        Stmt::Prose(..) => format!("(.stmt {})", stmt(st)),
        _ => return Err(format!("an early-error sentence of no form: {st:?}")),
    })
}

/// The sentences of a row that `sentence` keeps as a statement (prose, or a phrase with no
/// constructor), each described: what stops the row in the semantics.
pub fn wrapped(d: &Decls, r: &EarlyRow) -> Vec<String> {
    fn go(d: &Decls, st: &Stmt, out: &mut Vec<String>) {
        match st {
            Stmt::If(_, Body::Inline(x), arms, None) if arms.is_empty() => go(d, x, out),
            Stmt::Phrase(p, _) if d.phrases[*p].cat == "ER" && ER_FORMS.contains(&d.phrases[*p].name) => {}
            Stmt::Phrase(p, _) => out.push(format!("sentence {} {}", d.phrases[*p].cat, d.phrases[*p].name)),
            Stmt::Prose(ch, _) => out.push(match ch {
                Channel::Pending => "prose".to_string(),
                Channel::Upstream(k, _) => format!("prose (a) {}", d.reasons.name(*k)),
                Channel::Prim(p, _) => format!("prose (b) {}", d.prims.name(*p)),
                Channel::Annotated(k, _) => format!("prose (c) {}", d.notes.name(*k)),
            }),
            _ => {}
        }
    }
    let mut out = Vec::new();
    // a definition reading stands for the pinned sentences; an erratum's readings stand beside them
    let definition = r.readings.as_ref().is_some_and(|(e, _)| d.parity.get(*e) == Some(&crate::ast::Reading::Definition));
    if !definition {
        for n in &r.body {
            go(d, &n.stmt, &mut out);
        }
    }
    for (_, ss) in r.readings.iter().flat_map(|x| &x.1) {
        for n in ss {
            go(d, &n.stmt, &mut out);
        }
    }
    out
}

fn layout(l: LiLayout) -> &'static str {
    match l {
        LiLayout::Inline => ".inline",
        LiLayout::Block => ".block",
        LiLayout::Raw => ".raw",
    }
}

/// A row's definition: its name and source.
pub(crate) fn row(sp: &Spec, d: &Decls, r: &EarlyRow) -> Result<(String, String), String> {
    let b = &sp.early.bullets[r.bullet];
    let c = &sp.clauses[r.clause];
    let name = format!("«{}.{}»", c.id, r.idx);
    let mut body = r.body.iter().map(|n| sentence(d, &n.stmt).map_err(|e| format!("spec.html:{}: {e}", b.line))).collect::<Result<Vec<_>, _>>()?;
    if b.flat() && r.twin.is_none() {
        let t = crate::print::early(d, &r.vars.names, &r.body, LiLayout::Inline, b.indent);
        if t != b.text {
            return Err(format!("spec.html:{}: a raw layout's sentences print as {t:?}, not {:?}", b.line, b.text));
        }
        body = vec![format!("(.layout {} [{}])", s(&b.raw), body.join(", "))];
    }
    if let Some((e, alts)) = &r.readings {
        let mut out = Vec::new();
        for (rd, ss) in alts {
            let ss = ss.iter().map(|n| sentence(d, &n.stmt)).collect::<Result<Vec<_>, _>>().map_err(|e| format!("spec.html:{}: a reading: {e}", b.line))?;
            out.push(format!("({}, [{}])", crate::lean::reading(*rd), ss.join(", ")));
        }
        body = vec![format!("(.readings {} [{}] [{}])", crate::lean::eid(*e), body.join(", "), out.join(", "))];
    }
    let vars = r.vars.names.iter().map(|v| s(v)).collect::<Vec<_>>().join(", ");
    let prods = r.prods.iter().map(|&p| crate::lean::pid(p).to_string()).collect::<Vec<_>>().join(", ");
    let src = format!(
        "/-- {} (§{}) -/\ndef {name} : EarlyRow := {{\n  id := ⟨{}, {}⟩\n  sdo := {}\n  prods := [{prods}]\n  keys := [{}]\n  layout := {}\n  indent := {}\n  vars := #[{vars}]\n  body := [{}] }}\n\n",
        c.id,
        c.number,
        crate::lean::cid(r.clause),
        r.idx,
        r.sdo,
        s(r.twin.as_deref().unwrap_or(&sp.early.blocks[b.block].raw)),
        layout(b.layout),
        b.indent,
        body.join(",\n    ")
    );
    if src.contains("(.prose .pending ") {
        return Err(format!("spec.html:{}: an early-error row with prose in no residue channel", b.line));
    }
    let src = match src.strip_suffix(" }\n\n") {
        Some(x) if r.modifies => format!("{x}\n  modifies := true }}\n\n"),
        _ => src,
    };
    Ok((name, src))
}

/// Writes the shards and their index into `dir`.
pub fn emit(sp: &Spec, dt: &Data, dir: &Path) -> Result<String, String> {
    let mut shards: Vec<Vec<(String, String)>> = vec![vec![]];
    let mut bytes = 0;
    for r in &dt.early {
        if r.exception.is_some() {
            return Err(format!("spec.html:{}: an early-error row without a data shape", sp.early.bullets[r.bullet].line));
        }
        let (name, src) = row(sp, &dt.decls, r)?;
        let cur = shards.last().unwrap();
        if !cur.is_empty() && (cur.len() == SHARD_ROWS || bytes + src.len() > SHARD_BYTES) {
            shards.push(vec![]);
            bytes = 0;
        }
        bytes += src.len();
        shards.last_mut().unwrap().push((name, src));
    }
    let mut mods = Vec::new();
    for (i, sh) in shards.iter().enumerate() {
        let m = format!("Early{}", i + 1);
        let mut o = String::new();
        writeln!(o, "module\n\npublic import Ecma.Notation.Early\n\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.{m}\n\nopen Ecma\n").unwrap();
        for (_, src) in sh {
            o.push_str(src);
        }
        let names = sh.iter().map(|x| x.0.as_str()).collect::<Vec<_>>().join(", ");
        writeln!(o, "/-- The rows of this module, in document order. -/\ndef rows : List EarlyRow := [{names}]\n\nend Ecma.Gen.{m}").unwrap();
        std::fs::write(dir.join(format!("{m}.lean")), o).map_err(|e| e.to_string())?;
        mods.push(m);
    }
    let mut o = String::from("module\n\n");
    for m in &mods {
        writeln!(o, "public import Ecma.Gen.{m}").unwrap();
    }
    writeln!(o, "\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen\n\nopen Ecma\n").unwrap();
    let rows = mods.iter().map(|m| format!("{m}.rows")).collect::<Vec<_>>().join(",\n    ");
    writeln!(o, "/-- Every early-error row, by module. -/\ndef earlyRows : List (List EarlyRow) := [\n    {rows}]\n\nend Ecma.Gen").unwrap();
    std::fs::write(dir.join("Early.lean"), o).map_err(|e| e.to_string())?;
    Ok(format!("wrote {} early-error rows in {} modules and Early.lean", dt.early.len(), mods.len()))
}
