//! The `<emu-table>`s as Lean modules (`Ecma.Gen.Tables_N`): terms of
//! `Ecma.Notation.Tables`, sharded at `SHARD_TABLES` tables or `SHARD_BYTES`;
//! `Ecma.Gen.Tables` lists them, with the schemas' sort aliases.

use crate::ast::{Attr, Id, TyExpr};
use crate::data::Data;
use crate::lean::{expr, s, stmt, ty, HEADER};
use crate::spec::Spec;
use crate::tables::{Body, Cell, Kind, Role, Row, Sig, SigName, TTy, Table};
use std::fmt::Write;
use std::path::Path;

/// The most tables a data module holds.
pub const SHARD_TABLES: usize = 300;
/// The most bytes a data module holds, past which it is split.
pub const SHARD_BYTES: usize = 300_000;

/// A list literal, in chunks of at most 64 elements joined by `++`.
fn list<T>(xs: &[T], f: impl Fn(&T) -> String) -> String {
    if xs.is_empty() {
        return "[]".into();
    }
    xs.chunks(64).map(|c| format!("[{}]", c.iter().map(&f).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(" ++ ")
}

fn b(x: bool) -> &'static str {
    if x {
        "true"
    } else {
        "false"
    }
}

fn opt<T>(x: &Option<T>, f: impl Fn(&T) -> String) -> String {
    match x {
        Some(v) => format!("(some {})", f(v)),
        None => "none".into(),
    }
}

fn attrs(a: &[Attr]) -> String {
    list(a, |a| format!("⟨{}, {}⟩", s(&a.key), opt(&a.value, |v| s(v))))
}

fn kind(k: Kind) -> &'static str {
    match k {
        Kind::Fields => ".fields",
        Kind::Slots => ".slots",
        Kind::InternalMethods => ".internalMethods",
        Kind::AbstractMethods => ".abstractMethods",
        Kind::Components => ".components",
        Kind::Properties => ".properties",
        Kind::Intrinsics => ".intrinsics",
        Kind::Conversion => ".conversion",
        Kind::Data => ".data",
    }
}

fn role(r: Role) -> &'static str {
    match r {
        Role::Head => ".head",
        Role::Name => ".name",
        Role::Type => ".type",
        Role::Sig => ".sig",
        Role::Step => ".step",
        Role::Prose => ".prose",
        Role::Data => ".data",
    }
}

fn fields(fs: &[(Id, TyExpr)]) -> String {
    list(fs, |(f, t)| format!("({f}, {})", ty(t)))
}

fn tty(t: &TTy) -> String {
    match t {
        TTy::Ty(t) => format!("(.ty {})", ty(t)),
        TTy::Records(fs) => format!("(.records {})", fields(fs)),
    }
}

fn sig(x: &Sig) -> String {
    let name = match x.name {
        SigName::Internal(f) => format!(".internal {f}"),
        SigName::Method(m) => format!(".method {m}"),
    };
    let ps = list(&x.params, |p| format!("{{ x := {}, ty := {}, optional := {} }}", p.x, tty(&p.ty), b(p.optional)));
    format!("{{ name := {name}, params := {ps}, ret := {} }}", tty(&x.ret))
}

fn body(sp: &Spec, x: &Body) -> Result<String, String> {
    Ok(match x {
        Body::Field(f) => format!("(.field {f})"),
        Body::Ty(t) => format!("(.ty {})", tty(t)),
        Body::Sig(x) => format!("(.sig {})", sig(x)),
        Body::Stmt(x) => format!("(.stmt {})", stmt(x)),
        Body::Alg(k) => {
            let a = &sp.algs[*k];
            format!("(.alg ⟨{}, {}⟩)", crate::lean::cid(a.clause.ok_or("a table's emu-alg outside a clause")?), a.idx)
        }
        Body::Expr(e) => format!("(.expr {})", expr(e)),
        Body::Op(c) => format!("(.op {c})"),
        Body::Component(f) => format!("(.component {f})"),
        Body::Name(x) => format!("(.name {})", s(x)),
        Body::Lines(bs) => format!("(.lines [{}])", bs.iter().map(|x| body(sp, x)).collect::<Result<Vec<_>, _>>()?.join(", ")),
        Body::Dfn(x) => format!("(.dfn {})", body(sp, x)?),
        Body::Code(x) => format!("(.code {})", body(sp, x)?),
        Body::Link(h, x) => format!("(.link {} {})", s(h), body(sp, x)?),
        Body::Kept(k, x) => format!("(.kept (.annotated {k} none) {})", s(x)),
        Body::Text(x) => format!("(.text {})", s(x)),
    })
}

fn cell(sp: &Spec, c: &Cell) -> Result<String, String> {
    Ok(format!(
        "{{ gap := {}, head := {}, attrs := {}, block := {}, role := {}, body := {} }}",
        c.gap,
        b(c.head),
        attrs(&c.attrs),
        b(c.block),
        role(c.role),
        body(sp, &c.body)?
    ))
}

fn row(sp: &Spec, r: &Row) -> Result<String, String> {
    let cs = r.cells.iter().map(|c| cell(sp, c)).collect::<Result<Vec<_>, _>>()?;
    Ok(format!("{{ gap := {}, attrs := {}, cells := [\n      {}] }}", r.gap, attrs(&r.attrs), cs.join(",\n      ")))
}

/// A table's Lean name: its `id`, else its clause's id and index (`tables::lean_name`).
fn name(sp: &Spec, t: &Table) -> String {
    format!("«{}»", crate::tables::lean_name(sp, t))
}

fn table(sp: &Spec, t: &Table) -> Result<String, String> {
    let c = t.clause.ok_or_else(|| format!("spec.html:{}: a table outside a clause", t.line))?;
    let rows = t.rows.iter().map(|r| row(sp, r)).collect::<Result<Vec<_>, _>>()?;
    let rows = rows.chunks(64).map(|ch| format!("[\n    {}]", ch.join(",\n    "))).collect::<Vec<_>>().join(" ++ ");
    let schema = opt(&crate::tables::schema(t), |(x, add)| format!("({}, {})", s(x), b(*add)));
    let vars = format!("#[{}]", t.vars.names.iter().map(|v| s(v)).collect::<Vec<_>>().join(", "));
    let mut extra = String::new();
    if let Some(x) = &t.caption {
        extra.push_str(&format!("\n  caption := (some {})", s(x)));
    }
    if !t.table_attrs.is_empty() {
        extra.push_str(&format!("\n  tableAttrs := {}", attrs(&t.table_attrs)));
    }
    if t.figure {
        extra.push_str("\n  figure := true");
    }
    Ok(format!(
        "/-- {} (§{}){} -/\ndef {} : Table := {{\n  clause := {}\n  idx := {}\n  col := {}\n  attrs := {}{extra}\n  kind := {}\n  thead := {}\n  schema := {schema}\n  vars := {vars}\n  rows := {rows} }}\n",
        sp.clauses[c].id,
        sp.clauses[c].number,
        t.import.as_deref().map_or(String::new(), |f| format!(", {f}")),
        name(sp, t),
        crate::lean::cid(c),
        t.idx,
        t.col,
        attrs(&t.attrs),
        kind(t.kind),
        b(t.thead)
    ))
}

fn module(name: &str, defs: &[(String, String)]) -> String {
    let mut o = String::new();
    writeln!(o, "module\n\npublic import Ecma.Notation.Tables\n\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.{name}\n\nopen Ecma\n").unwrap();
    for (_, d) in defs {
        writeln!(o, "{d}").unwrap();
    }
    let names: Vec<&str> = defs.iter().map(|x| x.0.as_str()).collect();
    writeln!(o, "/-- The tables of this module, by table id (spec/formal/table-ids.txt). -/\ndef tables : List Table := {}\n", list(&names, |x| x.to_string())).unwrap();
    writeln!(o, "end Ecma.Gen.{name}").unwrap();
    o
}

/// Every table parsed and written as `Tables_N.lean` and `Tables.lean` into `dir`: the number of tables.
pub fn emit(html: &str, sp: &Spec, g: &crate::grammar::Grammar, dt: &mut Data, dir: &Path) -> Result<usize, String> {
    let ts = crate::tables::build(html, sp, g, dt);
    // by kept id (`Decls::table_ids`); a retired id's entry `Table.retired`, under its old name
    let mut by_id: Vec<Option<(String, String)>> = vec![None; dt.decls.tables.names.len()];
    for (i, t) in ts.tables.iter().enumerate() {
        let t = t.as_ref().map_err(|e| e.clone())?;
        if t.rows.is_empty() {
            return Err(format!("spec.html:{}: a table with no rows (a retired table id's entry is the one with none)", t.line));
        }
        by_id[dt.decls.table_ids[i]] = Some((name(sp, t), table(sp, t)?));
    }
    let mut defs = Vec::new();
    for (id, d) in by_id.into_iter().enumerate() {
        defs.push(d.unwrap_or_else(|| {
            let n = format!("«{}»", dt.decls.tables.names[id]);
            let d = format!("/-- table id {id}, retired: the text no longer has this table (spec/formal/table-ids.txt) -/\ndef {n} : Table := Table.retired\n");
            (n, d)
        }));
    }
    let n = defs.len();
    let total: usize = defs.iter().map(|d| d.1.len()).sum();
    let k = total.div_ceil(SHARD_BYTES).max(n.div_ceil(SHARD_TABLES)).max(1);
    let (target, per) = (total.div_ceil(k), n.div_ceil(k));
    let mut shards: Vec<Vec<(String, String)>> = vec![vec![]];
    let mut size = 0;
    for d in defs {
        let cur = shards.last().unwrap();
        if !cur.is_empty() && (size + d.1.len() > target || cur.len() >= per) && shards.len() < k {
            shards.push(vec![]);
            size = 0;
        }
        size += d.1.len();
        shards.last_mut().unwrap().push(d);
    }
    let mods: Vec<String> = (1..=shards.len()).map(|k| format!("Tables_{k}")).collect();
    for (m, defs) in mods.iter().zip(&shards) {
        std::fs::write(dir.join(format!("{m}.lean")), module(m, defs)).map_err(|e| e.to_string())?;
    }
    let mut aliases: Vec<(String, String)> = Vec::new();
    for (x, _) in ts.tables.iter().flatten().filter_map(crate::tables::schema) {
        if let Some(a) = crate::tables::sort_alias(&dt.decls, &x) {
            if !aliases.iter().any(|y| y.0 == x) {
                aliases.push((x, a));
            }
        }
    }
    let mut o = String::new();
    writeln!(o, "module\n\npublic import Ecma.Notation.Tables").unwrap();
    for m in &mods {
        writeln!(o, "public import Ecma.Gen.{m}").unwrap();
    }
    writeln!(o, "\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen\n\nopen Ecma\n").unwrap();
    writeln!(o, "/-- Every table, by module. -/\ndef tables : List (List Table) := [{}]\n", mods.iter().map(|m| format!("{m}.tables")).collect::<Vec<_>>().join(", ")).unwrap();
    writeln!(
        o,
        "/-- Schemas whose name is not a sort, and the sort the algorithms name for them. -/\ndef sortAliases : Array (String × String) :=\n    #[{}]\n",
        aliases.iter().map(|(x, a)| format!("({}, {})", s(x), s(a))).collect::<Vec<_>>().join(",\n      ")
    )
    .unwrap();
    writeln!(o, "end Ecma.Gen").unwrap();
    std::fs::write(dir.join("Tables.lean"), o).map_err(|e| e.to_string())?;
    Ok(n)
}
