//! R1's declarations from the spec: Record kinds and their fields (the field tables and the
//! overlay's record sorts), objects' internal slots (the slot tables), and the traits (the
//! internal-method and abstract-method tables).

use crate::ast::Id;
use crate::decls::Decls;
use crate::tables::{Body, Kind, Role, SigName, TTy, Table, Tables};
use crate::tylang::{of_tyexpr, Hier, T};
use std::collections::BTreeMap;

/// A Record kind's or an object sort's own fields, from its tables.
#[derive(Clone, Debug, Default)]
pub struct Shape {
    /// the sort, or none where the schema names no declared sort
    pub sort: Option<Id>,
    pub name: String,
    /// the nearest Record kind above it
    pub sup: Option<Id>,
    /// internal slots (an object sort) rather than fields
    pub slots: bool,
    pub tables: Vec<String>,
    pub fields: Vec<(Id, T)>,
    /// the fields typed `Any`, with their table cell's text
    pub dynamic: Vec<(Id, String)>,
}

#[derive(Clone, Debug)]
pub struct Method {
    pub name: SigName,
    /// name, type, optional
    pub params: Vec<(String, T, bool)>,
    pub ret: T,
}

/// A family of methods: its root sort (every sort below it implements them) and its parent trait.
#[derive(Clone, Debug)]
pub struct Trait {
    pub name: String,
    pub root: Option<Id>,
    pub sup: Option<usize>,
    pub table: String,
    pub methods: Vec<Method>,
}

#[derive(Clone, Debug, Default)]
pub struct TyDecls {
    pub hier: Hier,
    pub shapes: Vec<Shape>,
    pub traits: Vec<Trait>,
    /// guard operations: *true* only when the first argument is of the type
    pub guards: Vec<(String, T)>,
}

/// A table cell's type.
fn tty(d: &Decls, h: &Hier, t: &TTy) -> T {
    match t {
        TTy::Ty(x) => of_tyexpr(d, h, x),
        TTy::Records(_) => T::List(Box::new(T::Rec(None))),
    }
}

/// A plural sort name (`of="Module Records"`) as its sort.
fn sort_named(d: &Decls, x: &str) -> Option<Id> {
    let x = x.trim();
    d.sorts.get(x).or_else(|| d.sort_folds.get(x).and_then(|f| d.sorts.get(f))).or_else(|| x.strip_suffix('s').and_then(|y| d.sorts.get(y)))
}

impl TyDecls {
    /// From the overlay's record sorts and the parsed tables.
    pub fn build(d: &Decls, ts: &Tables) -> TyDecls {
        let mut hier = Hier::new(d);
        let decl = &ts.declared;
        for (n, t) in &decl.sorts {
            if let (Some(k), Ok(t)) = (d.sorts.get(n), t) {
                let x = tty(d, &hier, t);
                hier.declared.insert(k, x);
            }
        }
        let mut out = TyDecls { hier, ..TyDecls::default() };
        let rec_sup = |s: Id| -> Option<Id> {
            let def = d.sort_defs.get(s)?.as_ref()?;
            def.sup.iter().copied().find(|&p| d.sort_defs.get(p).and_then(Option::as_ref).is_some_and(|x| x.record))
        };
        for (s, def) in d.sort_defs.iter().enumerate() {
            if def.as_ref().is_some_and(|x| x.record) {
                out.shapes.push(Shape { sort: Some(s), name: d.sorts.name(s).to_string(), sup: rec_sup(s), ..Shape::default() });
            }
        }
        for t in ts.tables.iter().flatten() {
            match t.kind {
                Kind::Fields | Kind::Slots => out.shape(d, t, &rec_sup),
                Kind::InternalMethods | Kind::AbstractMethods => out.methods(d, t),
                // a Property Descriptor's fields are the property attributes
                Kind::Data if t.id().as_deref() == Some("table-object-property-attributes") => {
                    let k = out.shape_at(d, d.sorts.get("Property Descriptor"), "Property Descriptor".into(), &rec_sup);
                    out.rows(d, k, t, |c| if let Body::Expr(crate::ast::Expr::FieldName(f)) = c { Some(*f) } else { None });
                }
                _ => {}
            }
        }
        for (of, slots, rows) in &decl.fields {
            let sort = sort_named(d, of).or_else(|| crate::tables::sort_alias(d, of).and_then(|a| d.sorts.get(&a)));
            let k = out.shape_at(d, sort, of.clone(), &rec_sup);
            let h = &out.hier;
            let typed: Vec<(Id, T, Option<String>)> = rows
                .iter()
                .map(|(f, t)| match t {
                    Ok(x) => (*f, tty(d, h, x), Some(crate::tables::tty_text(d, &[], x))),
                    Err(x) => (*f, T::Any, Some(x.clone())),
                })
                .collect();
            let s = &mut out.shapes[k];
            s.slots |= *slots;
            s.tables.push(format!("overlay:{of}"));
            for (f, t, text) in typed {
                if t == T::Any {
                    s.dynamic.push((f, text.unwrap_or_default()));
                }
                s.fields.push((f, t));
            }
        }
        for (op, t) in &decl.guards {
            let x = t.as_ref().map_or(T::Any, |t| tty(d, &out.hier, t));
            out.guards.push((op.clone(), x));
        }
        // a trait's parent: the trait of the nearest sort above its root
        let roots: Vec<Option<Id>> = out.traits.iter().map(|t| t.root).collect();
        let h = &out.hier;
        for (k, t) in out.traits.iter_mut().enumerate() {
            let Some(r) = t.root else { continue };
            let above: Vec<usize> = (0..roots.len()).filter(|&j| j != k && roots[j].is_some_and(|q| q != r && h.below(r, q))).collect();
            t.sup = above.iter().copied().find(|&j| above.iter().all(|&i| roots[j].zip(roots[i]).is_some_and(|(a, b)| h.below(a, b))));
        }
        out
    }

    fn shape(&mut self, d: &Decls, t: &Table, rec_sup: &dyn Fn(Id) -> Option<Id>) {
        let Some((name, _)) = crate::tables::schema(t) else { return };
        let sort = d.sorts.get(&name).or_else(|| crate::tables::sort_alias(d, &name).and_then(|a| d.sorts.get(&a)));
        // a schema named as an event or a Record whose kind is the sort without that word
        let is_rec = |s: Id| d.sort_defs.get(s).and_then(Option::as_ref).is_some_and(|x| x.record);
        let sort = sort.map(|s| {
            let n = d.sorts.name(s);
            let bare = [" Record", " event", " Event"].iter().find_map(|w| n.strip_suffix(w)).and_then(|b| d.sorts.get(b));
            bare.filter(|&b| !is_rec(s) && is_rec(b)).unwrap_or(s)
        });
        let k = self.shape_at(d, sort, name, rec_sup);
        self.shapes[k].slots |= t.kind == Kind::Slots;
        self.rows(d, k, t, |c| if let Body::Field(f) = c { Some(*f) } else { None });
    }

    /// The shape of a sort, or of a schema name without one: found, or added.
    fn shape_at(&mut self, d: &Decls, sort: Option<Id>, name: String, rec_sup: &dyn Fn(Id) -> Option<Id>) -> usize {
        if let Some(k) = self.shapes.iter().position(|s| (sort.is_some() && s.sort == sort) || (sort.is_none() && s.name == name)) {
            return k;
        }
        let name = sort.map_or(name, |s| d.sorts.name(s).to_string());
        self.shapes.push(Shape { sort, name, sup: sort.and_then(rec_sup), ..Shape::default() });
        self.shapes.len() - 1
    }

    /// A table's rows as shape `k`'s fields: the name from the first cell, the type from the Type cell.
    fn rows(&mut self, d: &Decls, k: usize, t: &Table, name: impl Fn(&Body) -> Option<Id>) {
        let s = &mut self.shapes[k];
        s.tables.push(t.id().unwrap_or_default());
        for r in t.rows.iter().skip(1) {
            let Some(f) = r.cells.first().and_then(|c| name(&c.body)) else { continue };
            let cell = r.cells.iter().find(|c| c.role == Role::Type).map(|c| &c.body);
            let ty = match cell {
                Some(Body::Ty(x)) => tty(d, &self.hier, x),
                _ => T::Any,
            };
            if ty == T::Any {
                let text = match cell {
                    Some(Body::Ty(x)) => crate::tables::tty_text(d, &t.vars.names, x),
                    Some(Body::Kept(_, x) | Body::Text(x)) => x.clone(),
                    _ => String::new(),
                };
                s.dynamic.push((f, text));
            }
            s.fields.push((f, ty));
        }
    }

    fn methods(&mut self, d: &Decls, t: &Table) {
        let table = t.id().unwrap_or_default();
        let of = t.attr("of").unwrap_or_default();
        for r in t.rows.iter().skip(1) {
            let Some(Body::Sig(sig)) = r.cells.first().map(|c| &c.body) else { continue };
            let m = Method {
                name: sig.name,
                params: sig.params.iter().map(|p| (t.vars.names.get(p.x).cloned().unwrap_or_default(), self.param(d, &p.ty, p.optional), p.optional)).collect(),
                ret: tty(d, &self.hier, &sig.ret),
            };
            // [[Call]] and [[Construct]] are the Callable and Constructor markers' methods
            let (name, root) = match (t.kind, sig.name) {
                (Kind::InternalMethods, SigName::Internal(f)) if d.fields.name(f) == "Call" => ("Callable".to_string(), d.sorts.get("function object")),
                (Kind::InternalMethods, SigName::Internal(f)) if d.fields.name(f) == "Construct" => ("Constructor".to_string(), d.sorts.get("constructor")),
                (Kind::InternalMethods, _) => ("Object".to_string(), d.sorts.get("Object")),
                _ => {
                    let root = sort_named(d, of);
                    (root.map_or_else(|| of.to_string(), |s| d.sorts.name(s).to_string()), root)
                }
            };
            let k = match self.traits.iter().position(|x| x.name == name) {
                Some(k) => k,
                None => {
                    self.traits.push(Trait { name, root, sup: None, table: table.clone(), methods: Vec::new() });
                    self.traits.len() - 1
                }
            };
            self.traits[k].methods.push(m);
        }
    }

    /// A method parameter's type: `Opt<T>` if optional.
    fn param(&self, d: &Decls, t: &TTy, optional: bool) -> T {
        let x = tty(d, &self.hier, t);
        if optional && x != T::Any { T::opt(&self.hier, x) } else { x }
    }

    /// A Record kind's or object sort's fields: its own, then its supers'.
    pub fn fields_of(&self, s: Id) -> Vec<(Id, &T)> {
        let mut out: Vec<(Id, &T)> = Vec::new();
        let mut cur = Some(s);
        let mut n = 0;
        while let (Some(k), true) = (cur, n < 16) {
            let sh = self.shapes.iter().find(|x| x.sort == Some(k));
            for (f, t) in sh.into_iter().flat_map(|sh| sh.fields.iter()) {
                if !out.iter().any(|x| x.0 == *f) {
                    out.push((*f, t));
                }
            }
            cur = sh.and_then(|sh| sh.sup);
            n += 1;
        }
        out
    }

    /// Each field name's declared types, by shape.
    pub fn by_name(&self) -> BTreeMap<Id, Vec<(usize, &T)>> {
        let mut out: BTreeMap<Id, Vec<(usize, &T)>> = BTreeMap::new();
        for (k, s) in self.shapes.iter().enumerate() {
            for (f, t) in &s.fields {
                out.entry(*f).or_default().push((k, t));
            }
        }
        out
    }

    /// A field's type without its base's kind: the one every declaration gives, if they agree.
    pub fn field(&self, f: Id) -> Option<&T> {
        let all = self.by_name().remove(&f)?;
        let first = all.first()?.1;
        all.iter().all(|x| x.1 == first).then_some(first)
    }

    /// Field reads by name (`spec-gen types -cover`): one declared type, one per kind, an internal method, or none.
    pub fn field_reads(&self, d: &Decls, reads: &BTreeMap<String, usize>) -> Vec<String> {
        let names = self.by_name();
        let methods: Vec<Id> = self.traits.iter().flat_map(|t| t.methods.iter()).filter_map(|m| if let SigName::Internal(f) = m.name { Some(f) } else { None }).collect();
        let mut n = [0usize; 4];
        let mut none: Vec<(usize, &str)> = Vec::new();
        for (f, &c) in reads {
            let id = d.fields.get(f);
            let k = match id.and_then(|x| names.get(&x)) {
                Some(_) if id.and_then(|x| self.field(x)).is_some() => 0,
                Some(_) => 1,
                None if id.is_some_and(|x| methods.contains(&x)) => 2,
                None => {
                    none.push((c, f));
                    3
                }
            };
            n[k] += c;
        }
        none.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(b.1)));
        let mut out = vec![format!("# field reads and writes by declaration: one declared type {}, a type by the base's kind {}, an internal method {}, undeclared {}\n", n[0], n[1], n[2], n[3])];
        out.extend(none.iter().take(40).map(|(c, f)| format!("  {c}\t[[{f}]]\n")));
        out
    }

    /// `spec-gen types -decls`: the counts, then each shape's fields and each trait's methods.
    pub fn lines(&self, d: &Decls) -> Vec<String> {
        let recs: Vec<&Shape> = self.shapes.iter().filter(|s| !s.slots).collect();
        let objs: Vec<&Shape> = self.shapes.iter().filter(|s| s.slots).collect();
        let rows = |ss: &[&Shape]| ss.iter().map(|s| s.fields.len()).sum::<usize>();
        let dynamic: Vec<String> = self.shapes.iter().flat_map(|s| s.dynamic.iter().map(move |x| format!("#   {}.[[{}]]\t{}\n", s.name, d.fields.name(x.0), x.1))).collect();
        let names = self.by_name();
        let differ: Vec<&str> = names.iter().filter(|(_, v)| v.iter().any(|x| x.1 != v[0].1)).map(|(f, _)| d.fields.name(*f)).collect();
        let disjoint = names.values().filter(|v| v.iter().enumerate().any(|(i, a)| v[i + 1..].iter().any(|b| !a.1.meets(&self.hier, b.1)))).count();
        let mut out = vec![
            "# R1's declarations: Record kinds and their fields, objects' internal slots, traits\n".to_string(),
            format!(
                "# record kinds {} ({} with a field table, {} sorts without one), fields {}; object sorts with slots {}, slots {}\n",
                recs.len(),
                recs.iter().filter(|s| !s.tables.is_empty()).count(),
                recs.iter().filter(|s| s.tables.is_empty()).count(),
                rows(&recs),
                objs.len(),
                rows(&objs)
            ),
            format!("# rows typed Any {}: anything, or an opaque sort\n", dynamic.len()),
            format!("# field names {}; with types differing by kind {} ({disjoint} of them disjoint in some two kinds): {}\n", names.len(), differ.len(), differ.join(", ")),
            format!("# traits {}, methods {}; guards {}\n", self.traits.len(), self.traits.iter().map(|t| t.methods.len()).sum::<usize>(), self.guards.len()),
        ];
        out.splice(3..3, dynamic);
        for s in &self.shapes {
            let sup = s.sup.map(|x| format!(" : {}", d.sorts.name(x))).unwrap_or_default();
            let what = if s.slots { "object" } else { "record" };
            let unres = if s.sort.is_none() { " (no sort)" } else { "" };
            let all = s.sort.map_or(s.fields.len(), |k| self.fields_of(k).len());
            out.push(format!("{what}\t{}{sup}{unres}\tfields {all}, own {}\t{}\n", s.name, s.fields.len(), s.tables.join(" ")));
            for (f, t) in &s.fields {
                out.push(format!("  [[{}]]\t{}\n", d.fields.name(*f), t.show(d)));
            }
        }
        for (op, t) in &self.guards {
            let known = if d.ops.iter().any(|x| x == op) { "" } else { "\t(no such operation)" };
            out.push(format!("guard\t{op}\t{}{known}\n", t.show(d)));
        }
        for t in &self.traits {
            let root = t.root.map_or("?", |r| d.sorts.name(r));
            let sup = t.sup.map(|k| format!(" : {}", self.traits[k].name)).unwrap_or_default();
            out.push(format!("trait\t{}{sup}\troot {root}\t{}\n", t.name, t.table));
            for m in &t.methods {
                let name = match m.name {
                    SigName::Internal(f) => format!("[[{}]]", d.fields.name(f)),
                    SigName::Method(x) => d.methods.name(x).to_string(),
                };
                let ps: Vec<String> = m.params.iter().map(|(n, t, o)| format!("{}_{n}_: {}", if *o { "optional " } else { "" }, t.show(d))).collect();
                out.push(format!("  {name}({}) -> {}\n", ps.join(", "), m.ret.show(d)));
            }
        }
        out
    }
}
