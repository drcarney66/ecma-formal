//! The realm table as a Lean module (`Ecma.Gen.Realm`): terms of
//! `Ecma.Notation.Realm`, one definition per object, in creation order.

use crate::data::Data;
use crate::lean::{s, HEADER};
use crate::realm::{Attrs, Behaviour, Key, Kind, Obj, PVal, Prop, Realm, Val};
use crate::spec::Spec;
use std::fmt::Write;
use std::path::Path;

fn list<T>(xs: &[T], f: impl Fn(&T) -> String) -> String {
    if xs.is_empty() {
        return "[]".into();
    }
    xs.chunks(64).map(|c| format!("[{}]", c.iter().map(&f).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(" ++ ")
}

fn opt<T>(x: &Option<T>, f: impl Fn(&T) -> String) -> String {
    match x {
        Some(v) => format!("(some {})", f(v)),
        None => "none".into(),
    }
}

fn key(k: &Key) -> String {
    match k {
        Key::Str(x) => format!("(.str {})", s(x)),
        Key::Sym(d) => format!("(.sym {})", s(d)),
    }
}

fn val(sp: &Spec, dt: &Data, v: &Val) -> Result<String, String> {
    Ok(match v {
        Val::Undefined => ".undefined".into(),
        Val::Bool(x) => format!("(.bool {x})"),
        Val::Str(x) => format!("(.str {})", s(x)),
        Val::Number(b) => format!("(.number {b})"),
        Val::Obj(o) => format!("(.obj {o})"),
        Val::Sym(d) => format!("(.sym {})", s(d)),
        Val::GlobalThis => ".globalThis".into(),
        Val::Created(c, i) => format!("(.created ⟨{}, {i}⟩)", clause(sp, dt, *c)?),
    })
}

fn prop(sp: &Spec, dt: &Data, p: &Prop) -> Result<String, String> {
    let v = match &p.val {
        PVal::Data(v) => format!("(.data {})", val(sp, dt, v)?),
        PVal::Accessor { get, set } => format!("(.accessor {} {})", opt(get, |x| x.to_string()), opt(set, |x| x.to_string())),
    };
    Ok(format!(
        "{{ key := {}, val := {v}, attrs := {}, clause := {}, annexB := {}, optional := {}, omittable := {} }}",
        key(&p.key),
        attrs(&p.attrs),
        clause(sp, dt, p.clause)?,
        p.annex_b,
        p.optional,
        p.omittable
    ))
}

fn props(sp: &Spec, dt: &Data, ps: &[Prop]) -> Result<String, String> {
    let ps = ps.iter().map(|p| prop(sp, dt, p)).collect::<Result<Vec<_>, _>>()?;
    Ok(if ps.is_empty() { "[]".to_string() } else { format!("[\n      {}]", ps.join(",\n      ")) })
}

fn attrs(a: &Attrs) -> String {
    format!("⟨{}, {}, {}⟩", a.writable, a.enumerable, a.configurable)
}

fn clause(sp: &Spec, dt: &Data, c: usize) -> Result<usize, String> {
    let id = &sp.clauses[c].id;
    dt.decls.clauses.get(id).ok_or_else(|| format!("realm: clause {id} has no id"))
}

fn obj(sp: &Spec, dt: &mut Data, o: &Obj) -> Result<String, String> {
    let names: Vec<usize> = o.names.iter().map(|n| dt.decls.fields.intern(n)).collect();
    let keys: Vec<usize> = o.names.iter().map(|n| dt.decls.fields.intern(&format!("%{n}%"))).collect();
    let slots: Vec<(usize, &Val)> = o.slots.iter().map(|(f, v)| (dt.decls.fields.intern(f), v)).collect();
    let kind = match o.kind {
        Kind::Ordinary => ".ordinary".to_string(),
        Kind::Exotic(c) => format!("(.exotic {})", clause(sp, dt, c)?),
    };
    let fun = match &o.fun {
        None => "none".to_string(),
        Some(f) => {
            let alg = match &f.alg {
                None => "none".to_string(),
                Some(Behaviour::Alg(c, i)) => format!("(some ⟨{}, {i}⟩)", clause(sp, dt, *c)?),
                Some(Behaviour::Overlay(id)) => format!("(some ⟨{}, 0⟩)", dt.decls.clauses.get(id).ok_or_else(|| format!("realm: overlay {id} has no clause id"))?),
            };
            format!(
                "(some {{ alg := {alg}, length := {}, name := {}, pfx := {}, ctor := {}, async := {}, lengthAttrs := {}, nameAttrs := {} }})",
                f.length,
                key(&f.name),
                opt(&f.prefix, |p| s(p)),
                f.ctor,
                f.is_async,
                attrs(&f.length_attrs),
                attrs(&f.name_attrs)
            )
        }
    };
    let slots = slots.iter().map(|(f, v)| Ok(format!("({f}, {})", val(sp, dt, v)?))).collect::<Result<Vec<_>, String>>()?;
    Ok(format!(
        "{{ names := {}, keys := {}, path := {}, clause := {}, kind := {kind}, proto := {}, extensible := {},\n    slots := {}, fn? := {fun},\n    props := {},\n    annexB := {}, optional := {} }}",
        list(&names, |n| n.to_string()),
        list(&keys, |n| n.to_string()),
        s(&o.path),
        clause(sp, dt, o.clause)?,
        opt(&o.proto, |p| p.to_string()),
        o.extensible,
        list(&slots, |x| x.clone()),
        props(sp, dt, &o.props)?,
        o.annex_b,
        o.optional
    ))
}

/// The realm table written as `Realm.lean` into `dir`; its message, and the table.
pub fn emit(html: &str, sp: &Spec, g: &crate::grammar::Grammar, dt: &mut Data, dir: &Path) -> Result<(String, Realm), String> {
    let r: Realm = crate::realm::build(html, sp, &g.overlay.ops)?;
    let mut o = String::new();
    writeln!(o, "module\n\npublic import Ecma.Notation.Realm\n\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.Realm\n\nopen Ecma\n").unwrap();
    for (i, x) in r.objs.iter().enumerate() {
        writeln!(o, "/-- {} -/\ndef o{i} : RObj :=\n  {}\n", x.path.replace("-/", "- /"), obj(sp, dt, x)?).unwrap();
    }
    let ids: Vec<usize> = (0..r.objs.len()).collect();
    writeln!(o, "/-- The built-in objects, in creation order. -/\ndef objs : List RObj :=\n  {}\n", list(&ids, |i| format!("o{i}"))).unwrap();
    writeln!(o, "/-- The global object's properties. -/\ndef globals : List RProp :=\n  {}\n", props(sp, dt, &r.globals)?).unwrap();
    writeln!(o, "/-- A Module Namespace Object's own properties (§28.3). -/\ndef namespaceProps : List RProp :=\n  {}\n", props(sp, dt, &r.namespace)?).unwrap();
    let syms = crate::realm::well_known_symbols(html)?;
    writeln!(o, "/-- The well-known symbols' descriptions (§6.1.5.1): well-known symbol `i` has the `i`th. -/\ndef symbols : List String :=\n  {}\n", list(&syms, |d| s(d))).unwrap();
    let cid = |id: &str| dt.decls.clauses.get(id).ok_or_else(|| format!("realm: clause {id} has no id"));
    writeln!(
        o,
        "/-- The properties a clause specifies for an object that is no intrinsic: the global object's, a namespace's. -/\ndef clauseProps : List (ClauseId × List RProp) :=\n  [({}, globals), ({}, namespaceProps)]\n",
        cid("sec-global-object")?,
        cid(crate::realm::NAMESPACE)?
    )
    .unwrap();
    writeln!(o, "end Ecma.Gen.Realm").unwrap();
    std::fs::write(dir.join("Realm.lean"), o).map_err(|e| e.to_string())?;
    Ok((format!("wrote {} realm objects ({} with a prose behaviour)", r.objs.len(), r.prose().len()), r))
}
