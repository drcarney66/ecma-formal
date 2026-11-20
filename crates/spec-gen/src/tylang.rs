//! R1's static types: erasable, Rust-like. A union is over the runtime tags (a value's kind, a
//! Record's kind, an enum value) with no injections; Records are nominal; `Any` is the unknown.

use crate::ast::{Expr, Hole, Id, Mag, Numeral, Sub, TyExpr, ValLit};
use crate::decls::{Decls, Meaning};
use std::collections::{BTreeSet, HashMap};

/// The kinds of names a value may be (`Id<kind>`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IdKind {
    Field,
    Symbol,
}

/// A type; a `Union` is flat, tag-disjoint and sorted (`T::union`), and the empty one is `never`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum T {
    Undefined,
    Null,
    Bool,
    String,
    Symbol,
    Number,
    BigInt,
    /// an Object of every listed sort (exotic kinds, the Callable and Constructor markers)
    Object(BTreeSet<Id>),
    Int,
    Math,
    /// +∞ and -∞
    Inf,
    /// none listed: any enum value
    Enum(BTreeSet<Id>),
    /// a Record of a kind, or of any kind
    Rec(Option<Id>),
    List(Box<T>),
    Normal(Box<T>),
    Abrupt,
    /// an AO's optional parameter not passed (`Val.absent`): a use reads it as itself
    Absent,
    /// a built-in's parameter not passed (`Val.missing`): a use reads it as *undefined*
    Missing,
    /// parameters and result, if known
    Closure(Option<(Vec<T>, Box<T>)>),
    /// a Parse Node, of a nonterminal if known
    Node(Option<Id>),
    Name(IdKind),
    Union(Vec<T>),
    Any,
}

/// A union member's tag: members of one tag merge.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Tag {
    Undefined,
    Null,
    Bool,
    String,
    Symbol,
    Number,
    BigInt,
    Object,
    Math,
    Inf,
    Enum,
    Rec(Option<Id>),
    List,
    Normal,
    Abrupt,
    Absent,
    Missing,
    Closure,
    Node,
    Name(IdKind),
}

/// The sort hierarchy: each sort's supersorts, transitively, and the sorts no narrower than Object.
#[derive(Clone, Debug, Default)]
pub struct Hier {
    ups: HashMap<Id, BTreeSet<Id>>,
    plain: BTreeSet<Id>,
    /// the overlay's `type=` of a sort whose values are held as another kind
    pub declared: HashMap<Id, T>,
}

impl Hier {
    /// From the overlay's sort definitions.
    pub fn new(d: &Decls) -> Hier {
        let mut ups: HashMap<Id, BTreeSet<Id>> = HashMap::new();
        for s in 0..d.sort_defs.len() {
            let mut seen = BTreeSet::new();
            let mut work = vec![s];
            while let Some(x) = work.pop() {
                for &p in d.sort_defs.get(x).and_then(Option::as_ref).map_or(&[][..], |def| def.sup.as_slice()) {
                    if seen.insert(p) {
                        work.push(p);
                    }
                }
            }
            if !seen.is_empty() {
                ups.insert(s, seen);
            }
        }
        let mut plain: BTreeSet<Id> = ["Object", "object"].iter().filter_map(|n| d.sorts.get(n)).collect();
        let above: Vec<Id> = plain.iter().flat_map(|x| ups.get(x).into_iter().flatten().copied()).collect();
        plain.extend(above);
        Hier { ups, plain, declared: HashMap::new() }
    }

    /// `a` is `b` or below it.
    pub fn below(&self, a: Id, b: Id) -> bool {
        a == b || self.ups.get(&a).is_some_and(|u| u.contains(&b))
    }

    /// The sorts of a set that no other member is below.
    fn least(&self, s: &BTreeSet<Id>) -> BTreeSet<Id> {
        s.iter().copied().filter(|&a| !s.iter().any(|&b| b != a && self.below(b, a))).collect()
    }

    /// The sorts narrower than Object that every member of `a` and every member of `b` is below.
    fn common(&self, a: &BTreeSet<Id>, b: &BTreeSet<Id>) -> BTreeSet<Id> {
        let up = |s: &BTreeSet<Id>| -> BTreeSet<Id> { s.iter().flat_map(|&x| std::iter::once(x).chain(self.ups.get(&x).into_iter().flatten().copied())).collect() };
        self.least(&up(a).intersection(&up(b)).copied().filter(|x| !self.plain.contains(x)).collect())
    }
}

impl T {
    pub fn never() -> T {
        T::Union(Vec::new())
    }

    /// `ECMAScript language value`.
    pub fn lang() -> T {
        T::union(&Hier::default(), [T::Undefined, T::Null, T::Bool, T::String, T::Symbol, T::Number, T::BigInt, T::Object(BTreeSet::new())])
    }

    /// `Opt<t>`: `t` or absent.
    pub fn opt(h: &Hier, t: T) -> T {
        T::union(h, [t, T::Absent])
    }

    /// `Completion<t>`: a normal completion of `t`, or an abrupt one.
    pub fn completion(h: &Hier, t: T) -> T {
        T::union(h, [T::Normal(Box::new(t)), T::Abrupt])
    }

    pub fn ext_math(h: &Hier) -> T {
        T::union(h, [T::Math, T::Inf])
    }

    pub fn obj(s: Option<Id>) -> T {
        T::Object(s.into_iter().collect())
    }

    fn tag(&self) -> Option<Tag> {
        Some(match self {
            T::Undefined => Tag::Undefined,
            T::Null => Tag::Null,
            T::Bool => Tag::Bool,
            T::String => Tag::String,
            T::Symbol => Tag::Symbol,
            T::Number => Tag::Number,
            T::BigInt => Tag::BigInt,
            T::Object(_) => Tag::Object,
            T::Int | T::Math => Tag::Math,
            T::Inf => Tag::Inf,
            T::Enum(_) => Tag::Enum,
            T::Rec(k) => Tag::Rec(*k),
            T::List(_) => Tag::List,
            T::Normal(_) => Tag::Normal,
            T::Abrupt => Tag::Abrupt,
            T::Absent => Tag::Absent,
            T::Missing => Tag::Missing,
            T::Closure(_) => Tag::Closure,
            T::Node(_) => Tag::Node,
            T::Name(k) => Tag::Name(*k),
            T::Union(_) | T::Any => return None,
        })
    }

    pub fn members(&self) -> &[T] {
        match self {
            T::Union(ms) => ms,
            t => std::slice::from_ref(t),
        }
    }

    /// The values of all of `ts`: `Any` absorbs, one tag's members merge, a member below another goes.
    pub fn union(h: &Hier, ts: impl IntoIterator<Item = T>) -> T {
        let mut by: Vec<T> = Vec::new();
        for t in ts {
            if t == T::Any {
                return T::Any;
            }
            for m in t.members().iter().cloned() {
                match by.iter().position(|x| x.tag() == m.tag()) {
                    Some(i) => by[i] = merge(h, &by[i], &m),
                    None => by.push(m),
                }
            }
        }
        let keep: Vec<T> = by.iter().enumerate().filter(|(i, a)| !by.iter().enumerate().any(|(j, b)| j != *i && a.sub(h, b) && !(b.sub(h, a) && j > *i))).map(|(_, a)| a.clone()).collect();
        let mut keep = keep;
        keep.sort();
        if keep.len() == 1 { keep.pop().unwrap_or_else(T::never) } else { T::Union(keep) }
    }

    pub fn join(&self, h: &Hier, o: &T) -> T {
        T::union(h, [self.clone(), o.clone()])
    }

    /// Subtyping (`List` invariant, `Normal` covariant, closure parameters contravariant, `Any` inside unknown).
    pub fn sub(&self, h: &Hier, o: &T) -> bool {
        match (self, o) {
            (_, T::Any) => true,
            (T::Any, _) => false,
            (T::Union(ms), _) => ms.iter().all(|m| m.sub(h, o)),
            (_, T::Union(ms)) => ms.iter().any(|m| self.sub(h, m)),
            (T::Object(a), T::Object(b)) => b.iter().all(|&y| h.plain.contains(&y) || a.iter().any(|&x| h.below(x, y))),
            (T::Int, T::Math) => true,
            (T::Enum(a), T::Enum(b)) => b.is_empty() || (!a.is_empty() && a.is_subset(b)),
            (T::Rec(_), T::Rec(None)) => true,
            (T::Rec(Some(a)), T::Rec(Some(b))) => h.below(*a, *b),
            (T::List(a), T::List(b)) => a == b || **b == T::Any,
            (T::Normal(a), T::Normal(b)) => a.sub(h, b),
            (T::Closure(_), T::Closure(None)) => true,
            (T::Closure(Some((pa, ra))), T::Closure(Some((pb, rb)))) => pa.len() == pb.len() && pb.iter().zip(pa).all(|(b, a)| b.sub(h, a)) && ra.sub(h, rb),
            (T::Node(_), T::Node(None)) => true,
            (a, b) => a == b,
        }
    }

    /// Whether some value is of both (the falsifier's test).
    pub fn meets(&self, h: &Hier, o: &T) -> bool {
        match (self, o) {
            (T::Any, _) | (_, T::Any) => true,
            (T::Union(ms), _) => ms.iter().any(|m| m.meets(h, o)),
            (_, T::Union(ms)) => ms.iter().any(|m| self.meets(h, m)),
            (T::Enum(a), T::Enum(b)) => a.is_empty() || b.is_empty() || !a.is_disjoint(b),
            (T::Rec(None), T::Rec(_)) | (T::Rec(_), T::Rec(None)) => true,
            (T::Rec(Some(a)), T::Rec(Some(b))) => h.below(*a, *b) || h.below(*b, *a),
            (T::Normal(a), T::Normal(b)) => a.meets(h, b),
            _ => self.tag() == o.tag(),
        }
    }

    /// As a use reads it (`Val.used`): `Missing` is *undefined*.
    pub fn used(&self, h: &Hier) -> T {
        if self.members().contains(&T::Missing) { T::union(h, self.members().iter().map(|m| if *m == T::Missing { T::Undefined } else { m.clone() })) } else { self.clone() }
    }

    /// The members not within `o`: narrowing by a failed test, as "is present" drops `Absent`.
    pub fn without(&self, h: &Hier, o: &T) -> T {
        match self {
            T::Any => T::Any,
            t => T::union(h, t.members().iter().filter(|m| !m.sub(h, o)).cloned()),
        }
    }

    /// The values of both, member by member: narrowing by a passed test.
    pub fn within(&self, h: &Hier, o: &T) -> T {
        match (self, o) {
            (T::Any, _) => o.clone(),
            (_, T::Any) => self.clone(),
            _ => T::union(h, self.members().iter().flat_map(|m| o.members().iter().filter_map(move |n| meet(h, m, n)))),
        }
    }

    /// Printed with `Opt<…>`, `Completion<…>`, `ExtMath` and `LangValue` for the unions they name.
    pub fn show(&self, d: &Decls) -> String {
        let ms = self.members();
        if matches!(self, T::Union(_)) {
            if ms.is_empty() {
                return "never".into();
            }
            let has = |t: &T| ms.contains(t);
            if has(&T::Absent) {
                return format!("Opt<{}>", T::Union(ms.iter().filter(|m| **m != T::Absent).cloned().collect()).show(d));
            }
            if let (Some(T::Normal(n)), true) = (ms.iter().find(|m| matches!(m, T::Normal(_))), has(&T::Abrupt)) {
                let rest: Vec<T> = ms.iter().filter(|m| !matches!(m, T::Normal(_) | T::Abrupt)).cloned().collect();
                let c = format!("Completion<{}>", n.show(d));
                return if rest.is_empty() { c } else { format!("{} | {c}", T::Union(rest).show_flat(d)) };
            }
        }
        self.show_flat(d)
    }

    fn show_flat(&self, d: &Decls) -> String {
        let ms = self.members();
        if ms.len() == 1 && !matches!(self, T::Union(_)) {
            return self.show_one(d);
        }
        if ms.len() == 1 {
            return ms[0].show(d);
        }
        let mut parts = Vec::new();
        let mut rest: Vec<&T> = ms.iter().collect();
        let lang = [T::Undefined, T::Null, T::Bool, T::String, T::Symbol, T::Number, T::BigInt, T::Object(BTreeSet::new())];
        if lang.iter().all(|l| ms.contains(l)) {
            parts.push("LangValue".to_string());
            rest.retain(|m| !lang.contains(m));
        }
        if rest.contains(&&T::Math) && rest.contains(&&T::Inf) {
            parts.push("ExtMath".to_string());
            rest.retain(|m| !matches!(m, T::Math | T::Inf));
        }
        parts.extend(rest.iter().map(|m| m.show(d)));
        parts.join(" | ")
    }

    fn show_one(&self, d: &Decls) -> String {
        let sorts = |s: &BTreeSet<Id>| s.iter().map(|&x| d.sorts.name(x).to_string()).collect::<Vec<_>>().join(" + ");
        match self {
            T::Undefined => "Undefined".into(),
            T::Null => "Null".into(),
            T::Bool => "Bool".into(),
            T::String => "String".into(),
            T::Symbol => "Symbol".into(),
            T::Number => "Number".into(),
            T::BigInt => "BigInt".into(),
            T::Object(s) if s.is_empty() => "Object".into(),
            T::Object(s) => format!("Object<{}>", sorts(s)),
            T::Int => "Int".into(),
            T::Math => "Math".into(),
            T::Inf => "±∞".into(),
            T::Enum(e) if e.is_empty() => "Enum".into(),
            T::Enum(e) => format!("Enum{{{}}}", e.iter().map(|&x| format!("~{}~", d.enums.name(x))).collect::<Vec<_>>().join(", ")),
            T::Rec(None) => "Rec".into(),
            T::Rec(Some(k)) => format!("Rec<{}>", d.sorts.name(*k)),
            T::List(x) => format!("List<{}>", x.show(d)),
            T::Normal(x) => format!("Normal<{}>", x.show(d)),
            T::Abrupt => "Abrupt".into(),
            T::Absent => "Absent".into(),
            T::Missing => "Missing".into(),
            T::Closure(None) => "Closure".into(),
            T::Closure(Some((ps, r))) => format!("Closure<({}) -> {}>", ps.iter().map(|p| p.show(d)).collect::<Vec<_>>().join(", "), r.show(d)),
            T::Node(None) => "Node".into(),
            T::Node(Some(n)) => format!("Node<{}>", d.nts.name(*n)),
            T::Name(k) => format!("Id<{}>", format!("{k:?}").to_lowercase()),
            T::Union(_) => self.show(d),
            T::Any => "Any".into(),
        }
    }
}

/// Two members of one tag as one: common Object bounds, Int into Math, contents joined, else unknown shape.
fn merge(h: &Hier, a: &T, b: &T) -> T {
    match (a, b) {
        (T::Object(x), T::Object(y)) => T::Object(h.common(x, y)),
        (T::Int, T::Int) => T::Int,
        (T::Int | T::Math, T::Int | T::Math) => T::Math,
        (T::Enum(x), T::Enum(y)) if x.is_empty() || y.is_empty() => T::Enum(BTreeSet::new()),
        (T::Enum(x), T::Enum(y)) => T::Enum(x.union(y).copied().collect()),
        (T::List(x), T::List(y)) => T::List(Box::new(x.join(h, y))),
        (T::Normal(x), T::Normal(y)) => T::Normal(Box::new(x.join(h, y))),
        (x, y) if x == y => x.clone(),
        (T::Closure(_), _) => T::Closure(None),
        (T::Node(_), _) => T::Node(None),
        (x, _) => x.clone(),
    }
}

/// Two members' common values, if any: Object bounds together, the narrower number, kind or enum set.
fn meet(h: &Hier, a: &T, b: &T) -> Option<T> {
    if !a.meets(h, b) {
        return None;
    }
    Some(match (a, b) {
        (T::Object(x), T::Object(y)) => T::Object(h.least(&x.union(y).copied().filter(|s| !h.plain.contains(s)).collect())),
        (T::Int, _) | (_, T::Int) => T::Int,
        (T::Enum(x), y @ T::Enum(_)) if x.is_empty() => y.clone(),
        (x @ T::Enum(_), T::Enum(y)) if y.is_empty() => x.clone(),
        (T::Enum(x), T::Enum(y)) => T::Enum(x.intersection(y).copied().collect()),
        (T::Rec(Some(x)), T::Rec(Some(y))) => T::Rec(Some(if h.below(*x, *y) { *x } else { *y })),
        (T::Rec(x), T::Rec(y)) => T::Rec(x.or(*y)),
        (T::Normal(x), T::Normal(y)) => match x.within(h, y) {
            T::Union(ms) if ms.is_empty() => return None,
            t => T::Normal(Box::new(t)),
        },
        (T::List(x), y @ T::List(_)) if **x == T::Any => y.clone(),
        (T::Closure(None), y @ T::Closure(_)) | (T::Node(None), y @ T::Node(_)) => y.clone(),
        (x, _) => x.clone(),
    })
}

/// A sort's type: the spec's by name, an overlay sort by its definition (Record kind, Object bound, supersort).
pub fn sort_t(d: &Decls, h: &Hier, s: Id) -> T {
    sort_t_at(d, h, s, 0)
}

fn sort_t_at(d: &Decls, h: &Hier, s: Id, depth: usize) -> T {
    let name = d.sorts.name(s);
    match name {
        "Number" => T::Number,
        "String" => T::String,
        "Boolean" => T::Bool,
        "Symbol" => T::Symbol,
        "BigInt" => T::BigInt,
        "undefined" | "Undefined" => T::Undefined,
        "null" | "Null" => T::Null,
        "Object" | "object" => T::obj(None),
        "ECMAScript language value" => T::lang(),
        "property key" => T::union(h, [T::String, T::Symbol]),
        "integer" | "non-negative integer" | "integral mathematical value" | "code unit" | "code point" | "Unicode code point" => T::Int,
        "mathematical value" => T::Math,
        "extended mathematical value" => T::ext_math(h),
        "List" => T::List(Box::new(T::Any)),
        "Record" => T::Rec(None),
        "Parse Node" => T::Node(None),
        "Abstract Closure" => T::Closure(None),
        "nonterminal" | "grammar symbol" => T::Name(IdKind::Symbol),
        "internal slot name" => T::Name(IdKind::Field),
        "Completion Record" => T::completion(h, T::Any),
        "normal completion" => T::Normal(Box::new(T::Any)),
        "abrupt completion" | "throw completion" | "return completion" | "break completion" | "continue completion" => T::Abrupt,
        _ if h.declared.contains_key(&s) => h.declared[&s].clone(),
        _ => {
            // the text's name for a Record kind: the kind's name and ` Record` or ` event`
            let twin = || [" Record", " event"].iter().find_map(|w| name.strip_suffix(w)).and_then(|b| d.sorts.get(b)).filter(|&b| d.sort_defs.get(b).and_then(Option::as_ref).is_some_and(|x| x.record));
            let Some(Some(def)) = d.sort_defs.get(s) else { return twin().map_or(T::Any, |b| T::Rec(Some(b))) };
            if def.record {
                return T::Rec(Some(s));
            }
            if depth > 16 {
                return T::Any;
            }
            // a value is in each supersort: the narrowest known one bounds it
            let mut best = T::Any;
            for &p in &def.sup {
                let x = sort_t_at(d, h, p, depth + 1);
                if x != T::Any && (best == T::Any || x.sub(h, &best)) {
                    best = x;
                }
            }
            match best {
                T::Object(_) => T::obj(Some(s)),
                t => t,
            }
        }
    }
}

/// A header type.
pub fn of_tyexpr(d: &Decls, h: &Hier, t: &TyExpr) -> T {
    match t {
        // a modifier sort narrows (`an ordinary object`)
        TyExpr::Sort(_, ms, s, _) => ms.iter().fold(sort_t(d, h, *s), |t, &m| match t.within(h, &sort_t(d, h, m)) {
            T::Union(xs) if xs.is_empty() => t,
            x => x,
        }),
        TyExpr::ListOf(_, x) => T::List(Box::new(of_tyexpr(d, h, x))),
        TyExpr::Union(_, _, ts) => T::union(h, ts.iter().map(|t| of_tyexpr(d, h, t))),
        TyExpr::Completion(x) => T::Normal(Box::new(x.as_ref().map_or(T::Any, |x| of_tyexpr(d, h, x)))),
        TyExpr::Interval(x, _, _) | TyExpr::That(x, _, _) => of_tyexpr(d, h, x),
        TyExpr::Value(e) => lit_t(e).unwrap_or(T::Any),
        TyExpr::Nt(_, n, _) => T::Node(Some(*n)),
        TyExpr::Record(_) => T::Rec(None),
        TyExpr::Phrase(p, hs) => phrase_t(d, h, *p, hs),
        TyExpr::Var(..) | TyExpr::Prose(_) => T::Any,
    }
}

/// A type phrase's type, by its definition: a closure, a nonterminal's node, or its type bounded.
fn phrase_t(d: &Decls, h: &Hier, p: Id, hs: &[Hole]) -> T {
    let id = match d.phrases.get(p).and_then(|x| x.meaning.as_ref()) {
        Some(Meaning::Alg(c)) => d.clauses.name(*c),
        _ => return T::Any,
    };
    let ty = hs.iter().find_map(|x| if let Hole::T(t) = x { Some(t) } else { None });
    match id {
        "ph-type-abstract-closure" | "ph-type-closure-no-params" | "ph-type-header-closure-no-params" | "ph-type-closure-two-params" => T::Closure(None),
        "ph-type-nt-parse-node" => hs.iter().find_map(|x| if let Hole::E(Expr::Nt(n, _)) = x { Some(T::Node(Some(*n))) } else { None }).unwrap_or(T::Node(None)),
        "ph-type-at-least" => ty.map_or(T::Any, |t| of_tyexpr(d, h, t)),
        "ph-type-intrinsic-keys" => T::Rec(None),
        "ph-type-sequence-of" => T::List(Box::new(ty.map_or(T::Any, |t| of_tyexpr(d, h, t)))),
        _ => T::Any,
    }
}

/// A literal's type.
pub fn lit_t(e: &Expr) -> Option<T> {
    Some(match e {
        Expr::Val(v) => match v {
            ValLit::Undefined => T::Undefined,
            ValLit::Null => T::Null,
            ValLit::True | ValLit::False => T::Bool,
            ValLit::Str(..) => T::String,
            ValLit::NaN(_) | ValLit::Num(_, _, Sub::F) => T::Number,
            ValLit::Num(_, _, Sub::Z) | ValLit::BigN(_) => T::BigInt,
            _ => return None,
        },
        Expr::Math(_, Mag::Num(Numeral::Frac(..))) => T::Math,
        Expr::Math(_, Mag::Num(_)) | Expr::CodeUnit(..) | Expr::CodePoint(..) => T::Int,
        Expr::Math(_, Mag::Inf) => T::Inf,
        Expr::Enum(e) => T::Enum([*e].into()),
        Expr::Code(..) => T::String,
        Expr::Intrinsic(_) => T::obj(None),
        Expr::Paren(x) | Expr::Annot(_, x) => return lit_t(x),
        _ => return None,
    })
}
