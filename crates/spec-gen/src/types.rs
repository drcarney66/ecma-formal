//! P3: the steps typed against the headers. A value's sort is a set of the machine's value
//! kinds (`Ecma.State.Val`), as headers, literals and signatures give them; a finding is a
//! step where two of them cannot meet, so that a run reaching it stops (sortError, or assertFailed
//! for a `?`/`!` of a non-completion in checked mode) or breaks a header.

use crate::ast::{AltForm, Arm, BinOp, Body, Callee, CloLit, Cond, Conj, Expr, Hole, Id, Mag, Node, Part, Place, Pred, RelOp, Stmt, Sub, TyExpr, ValLit};
use crate::conv::Vars;
use crate::data::{Data, Hdr};
use crate::decls::Decls;
use crate::grammar::Grammar;
use crate::spec::Spec;
use crate::tables::SigName;
use crate::tydecls::TyDecls;
use crate::tylang::{lit_t, of_tyexpr, sort_t, Hier, T};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

mod ver;

const UNDEF: u32 = 1;
const NULL: u32 = 1 << 1;
const BOOL: u32 = 1 << 2;
const STR: u32 = 1 << 3;
const SYM: u32 = 1 << 4;
const NUM: u32 = 1 << 5;
const BIG: u32 = 1 << 6;
const OBJ: u32 = 1 << 7;
const MATH: u32 = 1 << 8;
/// +∞ and -∞
const INF: u32 = 1 << 9;
const ENUM: u32 = 1 << 10;
const LIST: u32 = 1 << 11;
/// a Record or an Environment Record
const REC: u32 = 1 << 12;
const NODE: u32 = 1 << 13;
const CLO: u32 = 1 << 14;
/// an optional parameter not passed
const ABSENT: u32 = 1 << 15;
/// grammar symbols, field names, algorithm values, terminals' nodes and the rest
const OTHER: u32 = 1 << 16;
const ALL: u32 = (1 << 17) - 1;
const LANG: u32 = UNDEF | NULL | BOOL | STR | SYM | NUM | BIG | OBJ;
const NAMES: &[(u32, &str)] = &[
    (UNDEF, "undefined"), (NULL, "null"), (BOOL, "Boolean"), (STR, "String"), (SYM, "Symbol"), (NUM, "Number"), (BIG, "BigInt"),
    (OBJ, "Object"), (MATH, "mathematical value"), (INF, "±∞"), (LIST, "List"), (REC, "Record"), (NODE, "Parse Node"),
    (CLO, "Abstract Closure"), (ABSENT, "absent"), (OTHER, "other"),
];

/// Value kinds; with ENUM, the enums it may be (none listed: any).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Atoms {
    bits: u32,
    enums: BTreeSet<Id>,
}

impl Atoms {
    fn of(bits: u32) -> Atoms {
        Atoms { bits, enums: BTreeSet::new() }
    }

    fn top() -> Atoms {
        Atoms::of(ALL)
    }

    fn is_top(&self) -> bool {
        self.bits == ALL && self.enums.is_empty()
    }

    fn join(&mut self, o: &Atoms) {
        let (a, b) = (self.bits & ENUM != 0, o.bits & ENUM != 0);
        self.enums = match (a, b) {
            (true, true) if self.enums.is_empty() || o.enums.is_empty() => BTreeSet::new(),
            (true, true) => self.enums.union(&o.enums).copied().collect(),
            (false, true) => o.enums.clone(),
            _ => std::mem::take(&mut self.enums),
        };
        self.bits |= o.bits;
    }

    fn meets(&self, o: &Atoms) -> bool {
        let both = self.bits & o.bits;
        both & !ENUM != 0 || (both & ENUM != 0 && (self.enums.is_empty() || o.enums.is_empty() || !self.enums.is_disjoint(&o.enums)))
    }

    fn show(&self, d: &Decls) -> Vec<String> {
        let mut out: Vec<String> = NAMES.iter().filter(|(b, _)| self.bits & b != 0).map(|(_, n)| n.to_string()).collect();
        if self.bits & ENUM != 0 {
            if self.enums.is_empty() {
                out.push("enum".into());
            } else {
                out.extend(self.enums.iter().map(|&e| format!("~{}~", d.enums.name(e))));
            }
        }
        out
    }
}

/// A sort: the values it may be (`v`), the values a normal completion of it may hold (`n`),
/// whether it may be an abrupt completion (`ab`), and its Lists' elements (`el`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Ty {
    v: Atoms,
    n: Atoms,
    ab: bool,
    el: Atoms,
}

impl Ty {
    fn val(bits: u32) -> Ty {
        Ty { v: Atoms::of(bits), el: Atoms::top(), ..Ty::default() }
    }

    fn enum1(e: Id) -> Ty {
        Ty { v: Atoms { bits: ENUM, enums: [e].into() }, ..Ty::default() }
    }

    fn list(el: Atoms) -> Ty {
        Ty { v: Atoms::of(LIST), el, ..Ty::default() }
    }

    fn top() -> Ty {
        Ty { v: Atoms::top(), n: Atoms::top(), ab: true, el: Atoms::top() }
    }

    fn normal(n: Atoms) -> Ty {
        Ty { n, ..Ty::default() }
    }

    fn abrupt() -> Ty {
        Ty { ab: true, ..Ty::default() }
    }

    fn is_empty(&self) -> bool {
        self.v.bits == 0 && self.n.bits == 0 && !self.ab
    }

    fn is_top(&self) -> bool {
        self.v.is_top() && self.n.is_top() && self.ab
    }

    /// Whether it may be a completion.
    fn comp(&self) -> bool {
        self.n.bits != 0 || self.ab
    }

    /// Only completions.
    fn only_comp(&self) -> bool {
        self.v.bits == 0 && self.comp()
    }

    fn join(&mut self, o: &Ty) {
        if o.v.bits & LIST != 0 {
            if self.v.bits & LIST != 0 {
                self.el.join(&o.el);
            } else {
                self.el = o.el.clone();
            }
        }
        self.v.join(&o.v);
        self.n.join(&o.n);
        self.ab |= o.ab;
    }

    fn joined(mut self, o: &Ty) -> Ty {
        self.join(o);
        self
    }

    fn meets(&self, o: &Ty) -> bool {
        self.v.meets(&o.v) || self.n.meets(&o.n) || (self.ab && o.ab)
    }

    /// Every value of `self` is one of `o`.
    fn within(&self, o: &Ty) -> bool {
        let a = |x: &Atoms, y: &Atoms| {
            x.bits & !y.bits == 0 && (x.bits & ENUM == 0 || y.enums.is_empty() || (!x.enums.is_empty() && x.enums.is_subset(&y.enums)))
        };
        a(&self.v, &o.v) && a(&self.n, &o.n) && (!self.ab || o.ab)
    }

    /// As returned from an algorithm that returns completions: a value is a normal completion.
    fn wrapped(&self) -> Ty {
        let mut t = self.clone();
        t.n.join(&self.v);
        t
    }

    /// `? e` and `! e`: a normal completion's value, or the value itself.
    fn unwrapped(&self) -> Ty {
        if self.v.is_top() || self.n.is_top() {
            return Ty::top();
        }
        let mut v = self.v.clone();
        v.join(&self.n);
        Ty { v, el: self.el.clone(), ..Ty::default() }
    }

    fn show(&self, d: &Decls) -> String {
        let mut out = self.v.show(d);
        if self.n.bits != 0 {
            out.push(if self.n.is_top() { "normal completion".into() } else { format!("normal completion of {}", self.n.show(d).join(" or ")) });
        }
        if self.ab {
            out.push("abrupt completion".into());
        }
        out.join(" or ")
    }
}

/// The finding kinds, in the report's order.
pub const KINDS: &[&str] = &["arity", "arg", "unchecked", "return", "operand", "base", "check", "literal", "unbound", "impl", "typing"];

/// A finding: algorithm key (`sec-x#n` or an overlay id), step path, kind, what; its line puts the kind first.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Finding {
    pub key: String,
    pub path: String,
    pub kind: &'static str,
    pub what: String,
}

impl Finding {
    pub fn line(&self) -> String {
        format!("{}\t{}\t{}\t{}\n", self.kind, self.key, self.path, self.what)
    }
}

/// A sort named in prose (a primitive's signature): its alternatives, each a sort name; none
/// when a part is not one.
fn text_ty(d: &Decls, s: &str) -> Option<Ty> {
    let s = s.trim().trim_start_matches("either ").trim_start_matches("one of ");
    let mut t = Ty::default();
    for p in s.split(", or ").flat_map(|x| x.split(" or ")).flat_map(|x| x.split(", ")) {
        let p = p.trim();
        let p = p.strip_prefix("a ").or_else(|| p.strip_prefix("an ")).unwrap_or(p);
        if p.starts_with("List of ") {
            t.join(&Ty::list(Atoms::top()));
            continue;
        }
        let id = d.sorts.get(p).or_else(|| d.sort_folds.get(p).and_then(|f| d.sorts.get(f)))?;
        let x = sort_ty(d, id, 0);
        if x.is_top() {
            return None;
        }
        t.join(&x);
    }
    (!t.is_empty()).then_some(t)
}

/// A declared sort: `Known`'s by name, an overlay sort by its supersorts (a Record kind's values
/// are Records); any other is any value.
fn sort_ty(d: &Decls, s: Id, depth: usize) -> Ty {
    let name = d.sorts.name(s);
    let bits = match name {
        "Number" | "integral Number" => NUM,
        "String" => STR,
        "Boolean" => BOOL,
        "Symbol" => SYM,
        "BigInt" => BIG,
        "Object" | "object" => OBJ,
        "List" => LIST,
        "Record" | "Property Descriptor" => REC,
        "integer" | "non-negative integer" | "mathematical value" | "code unit" | "code point" | "integral mathematical value" => MATH,
        "extended mathematical value" => MATH | INF,
        "Parse Node" => NODE,
        "Abstract Closure" => CLO,
        "ECMAScript language value" => LANG,
        "property key" => STR | SYM,
        "undefined" => UNDEF,
        "null" => NULL,
        "nonterminal" | "grammar symbol" => OTHER,
        "Completion Record" => return Ty { ab: true, ..Ty::normal(Atoms::top()) },
        "normal completion" => return Ty::normal(Atoms::top()),
        "abrupt completion" | "throw completion" | "return completion" | "break completion" | "continue completion" => return Ty::abrupt(),
        _ => {
            let Some(Some(def)) = d.sort_defs.get(s) else { return Ty::top() };
            if depth > 16 {
                return Ty::top();
            }
            let mut t: Option<Ty> = None;
            for &p in &def.sup {
                let x = sort_ty(d, p, depth + 1);
                // a value is in each supersort: any one known bounds it, the narrowest best
                if !x.is_top() && t.as_ref().map_or(true, |t| t.is_top() || (x.v.bits & t.v.bits == x.v.bits && !x.comp())) {
                    t = Some(x);
                }
            }
            return match t {
                Some(t) => t,
                None if def.record => Ty::val(REC),
                None => Ty::top(),
            };
        }
    };
    if bits == LIST { Ty::list(Atoms::top()) } else { Ty::val(bits) }
}

/// A header's type.
fn of_ty(d: &Decls, t: &TyExpr) -> Ty {
    match t {
        TyExpr::Sort(_, _, s, _) => sort_ty(d, *s, 0),
        TyExpr::ListOf(_, x) => Ty::list(of_ty(d, x).v),
        TyExpr::Union(_, _, ts) => ts.iter().fold(Ty::default(), |a, t| a.joined(&of_ty(d, t))),
        TyExpr::Completion(Some(x)) => Ty::normal(of_ty(d, x).v),
        TyExpr::Completion(None) => Ty::normal(Atoms::top()),
        TyExpr::Interval(x, _, _) | TyExpr::That(x, _, _) => of_ty(d, x),
        TyExpr::Value(e) => lit_ty(e).unwrap_or_else(Ty::top),
        TyExpr::Nt(..) => Ty::val(NODE),
        TyExpr::Record(_) => Ty::val(REC),
        TyExpr::Phrase(p, hs) => d.type_bound(*p, hs).map_or_else(Ty::top, |t| of_ty(d, &t)),
        TyExpr::Var(..) | TyExpr::Prose(_) => Ty::top(),
    }
}

/// A literal's sort.
fn lit_ty(e: &Expr) -> Option<Ty> {
    Some(match e {
        Expr::Val(v) => match v {
            ValLit::Undefined => Ty::val(UNDEF),
            ValLit::Null => Ty::val(NULL),
            ValLit::True | ValLit::False => Ty::val(BOOL),
            ValLit::Str(..) => Ty::val(STR),
            ValLit::NaN(_) | ValLit::Num(_, _, Sub::F) => Ty::val(NUM),
            ValLit::Num(_, _, Sub::Z) | ValLit::BigN(_) => Ty::val(BIG),
            ValLit::Num(_, _, Sub::None) => Ty::default(),
            ValLit::This => return None,
            ValLit::Err(_) => Ty::val(OTHER),
        },
        Expr::Math(_, Mag::Num(_)) | Expr::CodeUnit(..) | Expr::CodePoint(..) => Ty::val(MATH),
        Expr::Math(_, Mag::Inf) => Ty::val(INF),
        Expr::Enum(e) => Ty::enum1(*e),
        Expr::Code(..) => Ty::val(STR),
        Expr::Intrinsic(_) => Ty::val(OBJ),
        Expr::Paren(x) | Expr::Annot(_, x) => return lit_ty(x),
        _ => return None,
    })
}

/// §5.2.6's notation: parameter sorts, result.
fn notation(name: &str) -> Option<(u32, u32)> {
    Some(match name {
        "𝔽" => (MATH | INF, NUM),
        "ℝ" => (NUM | BIG, MATH),
        "ℤ" => (MATH, BIG),
        "abs" | "floor" | "truncate" | "ln" | "log10" | "log2" => (MATH, MATH),
        "min" | "max" => (MATH | INF, MATH | INF),
        _ => return None,
    })
}

/// The operand kinds `binOp` (Store.lean) takes, and the result's.
fn bin_rule(o: BinOp, a: u32, b: u32) -> u32 {
    let mut r = 0;
    if a & b & MATH != 0 || a & b & BIG != 0 {
        r |= a & b & (MATH | BIG);
    }
    if a & b & NUM != 0 && matches!(o, BinOp::Add | BinOp::Plus | BinOp::Times | BinOp::Sub | BinOp::Mul | BinOp::Div) {
        r |= NUM;
    }
    let xr = (a & INF != 0 && b & (INF | MATH) != 0) || (b & INF != 0 && a & (INF | MATH) != 0);
    if xr && matches!(o, BinOp::Add | BinOp::Sub) {
        r |= INF;
    }
    r
}

/// Whether `relOp` (Store.lean) takes some pair of the operand kinds.
fn rel_ok(a: u32, b: u32) -> bool {
    a & b & (NUM | BIG) != 0 || (a & (MATH | INF) != 0 && b & (MATH | INF) != 0)
}

/// Value kinds as a `T`; any where they include `OTHER` (names, algorithm values).
fn atoms_t(h: &Hier, a: &Atoms, el: Option<&Atoms>) -> T {
    if a.is_top() || a.bits & OTHER != 0 {
        return T::Any;
    }
    let one = [(UNDEF, T::Undefined), (NULL, T::Null), (BOOL, T::Bool), (STR, T::String), (SYM, T::Symbol), (NUM, T::Number), (BIG, T::BigInt), (OBJ, T::obj(None)), (MATH, T::Math), (INF, T::Inf), (REC, T::Rec(None)), (NODE, T::Node(None)), (CLO, T::Closure(None)), (ABSENT, T::Absent)];
    let mut ms: Vec<T> = one.into_iter().filter(|(b, _)| a.bits & b != 0).map(|x| x.1).collect();
    if a.bits & ENUM != 0 {
        ms.push(T::Enum(a.enums.clone()));
    }
    if a.bits & LIST != 0 {
        ms.push(T::List(Box::new(el.map_or(T::Any, |e| atoms_t(h, e, None)))));
    }
    T::union(h, ms)
}

/// A sort as a `T`.
fn ty_t(h: &Hier, t: &Ty) -> T {
    if t.v.is_top() {
        return T::Any;
    }
    let mut ms = vec![atoms_t(h, &t.v, Some(&t.el))];
    if t.n.bits != 0 {
        ms.push(T::Normal(Box::new(atoms_t(h, &t.n, None))));
    }
    if t.ab {
        ms.push(T::Abrupt);
    }
    T::union(h, ms)
}

/// `? x` and `! x` in `T`: a normal completion's value, or the value itself.
fn unwrap_t(h: &Hier, t: &T) -> T {
    match t {
        T::Any => T::Any,
        t => T::union(h, t.members().iter().filter(|m| **m != T::Abrupt).map(|m| if let T::Normal(x) = m { (**x).clone() } else { m.clone() })),
    }
}

/// As returned from an algorithm that returns completions: a value is a normal completion.
fn wrap_t(h: &Hier, t: &T) -> T {
    match t {
        T::Any => T::Any,
        t => T::union(h, t.members().iter().map(|m| if matches!(m, T::Normal(_) | T::Abrupt) { m.clone() } else { T::Normal(Box::new(m.clone())) })),
    }
}

/// `binOp`'s result in `T`, where both operands are within one kind it takes; else any.
fn bin_t(h: &Hier, o: BinOp, a: &T, b: &T) -> T {
    let both = |n: &T| a.sub(h, n) && b.sub(h, n);
    let arith = matches!(o, BinOp::Add | BinOp::Plus | BinOp::Times | BinOp::Sub | BinOp::Mul | BinOp::Div);
    if both(&T::Int) && matches!(o, BinOp::Add | BinOp::Plus | BinOp::Times | BinOp::Sub | BinOp::Mul | BinOp::Modulo) {
        T::Int
    } else if both(&T::Math) {
        T::Math
    } else if both(&T::ext_math(h)) && matches!(o, BinOp::Add | BinOp::Sub) {
        T::ext_math(h)
    } else if both(&T::Number) && arith {
        T::Number
    } else if both(&T::BigInt) {
        T::BigInt
    } else {
        T::Any
    }
}

/// The kinds a sound-mode site falls in: within the type needed, meeting it only, of unknown type, disjoint.
pub const SOUND: [&str; 4] = ["within", "meets", "unknown", "disjoint"];

/// The sound-mode site classes.
const SOUND_SITES: [&str; 4] = ["arguments", "returns", "operands", "bases"];

/// `spec-gen types -cover`'s counts: sites and variables by precision, and why one is any value.
#[derive(Clone, Debug, Default)]
pub struct Cover {
    sites: [[usize; 4]; 3],
    top: BTreeMap<(usize, String), usize>,
    slots: [usize; 4],
    slot_top: BTreeMap<String, usize>,
    imethods: BTreeMap<String, usize>,
    cmethods: BTreeMap<String, usize>,
    applies: usize,
    /// argument sites with a known sort against a typed parameter: within it, meeting it only
    within: [usize; 2],
    /// the sites meeting it only, by parameter sort and argument sort
    overlap: BTreeMap<String, usize>,
    /// variables bound more than once; of them bound to disjoint sorts; of them a completion and then its value
    retyped: [usize; 3],
    /// field reads whose base is any value, an Object or Record, neither
    fields: [usize; 3],
    field_names: BTreeMap<String, usize>,
    /// the sound mode's sites by class and kind (`SOUND`), and its findings
    sound_n: [[usize; 4]; 4],
    sound: Vec<Finding>,
    /// the sound mode's returns disjoint from their algorithm's result typing
    typed: Vec<Finding>,
    /// the versioned slots (algorithm key, slot name) and their versions
    versioned: BTreeMap<(String, String), usize>,
    /// slots (algorithm key, slot name) bound more than once, and of them with more than one binding group
    rebound: [BTreeSet<(String, String)>; 2],
    /// the sound mode's slot types per unit (clause, index), versions after the slots
    units: Vec<((usize, usize), Vec<T>)>,
}

impl Cover {
    /// Field reads and writes by field name.
    pub fn field_names(&self) -> &BTreeMap<String, usize> {
        &self.field_names
    }
}

/// A sort's precision: any value (0), a completion (1), a union of kinds (2), one kind (3).
fn bucket(t: &Ty) -> usize {
    if t.is_empty() || t.v.is_top() || (t.v.bits == 0 && t.n.is_top()) {
        0
    } else if t.comp() {
        1
    } else if (t.v.bits & !ABSENT).count_ones() <= 1 {
        3
    } else {
        2
    }
}

/// Why a slot of a header type is any value.
fn ty_why(d: &Decls, t: &TyExpr) -> String {
    match t {
        TyExpr::Sort(_, _, s, _) if sort_ty(d, *s, 0).is_top() => format!("opaque sort '{}'", d.sorts.name(*s)),
        TyExpr::Sort(..) => "widened by its bindings".into(),
        TyExpr::Completion(Some(x)) => format!("completion of {}", ty_why(d, x)),
        TyExpr::Union(..) => "a union with an opaque member".into(),
        TyExpr::Phrase(p, _) if d.phrases[*p].name == "ht-anything" => "anything".into(),
        TyExpr::Var(..) | TyExpr::Phrase(..) => "a type phrase".into(),
        TyExpr::Prose(_) => "prose (unparsed)".into(),
        _ => "other".into(),
    }
}

/// What the checker knows of the data: the headers by clause, the SDOs', the field ids.
struct Cx<'a> {
    d: &'a Decls,
    g: &'a Grammar,
    /// each operation's header, and the variables its slots index
    hdrs: HashMap<Id, (&'a Hdr, &'a Vars)>,
    sdos: &'a [Option<Hdr>],
    /// each SDO's parameter names, from its first clause's header
    sdo_names: Vec<Vec<String>>,
    /// per site class (arguments, returns, operands): sites checked, sites whose value's sort is known
    stats: std::cell::RefCell<[(usize, usize); 3]>,
    /// `.alg` phrases typed as calls, by their header's return type or else their returns' (`rets`)
    expand: bool,
    rets: HashMap<Id, Ty>,
    /// each phrase algorithm's returns, by clause
    seen_rets: std::cell::RefCell<HashMap<Id, Ty>>,
    cover: std::cell::RefCell<Cover>,
    f_type: Option<Id>,
    f_value: Option<Id>,
    f_target: Option<Id>,
    f_desc: Option<Id>,
    /// the sound mode's declarations: sites are accepted by `T::sub`
    sound: Option<&'a TyDecls>,
    /// the primitives' signature types, by text
    sig_tys: &'a HashMap<String, TyExpr>,
    /// the List parameters their callees only read (`read_only_params`)
    ro: HashSet<(Id, usize)>,
    /// the facts about the callees from the round before; this round's
    facts: Facts,
    facts_out: std::cell::RefCell<Facts>,
}

/// Each AO's parameters (by clause): the type each has at every normal return, where narrower than its own.
pub type Exits = HashMap<Id, Vec<Option<T>>>;

/// The sound mode's facts about callees, a call level per round: AO exits, and each phrase algorithm's result (by clause).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Facts {
    exits: Exits,
    rets: HashMap<Id, T>,
}

type Env = HashMap<Id, Ty>;

/// One algorithm's check: its key, variables, return type (none inside a closure), and findings.
struct Alg<'a, 'c> {
    cx: &'c Cx<'a>,
    key: String,
    clause: String,
    vars: &'a Vars,
    closures: &'a [CloLit],
    env: Env,
    bound: HashSet<Id>,
    /// why each variable's sort is any value
    why: HashMap<Id, String>,
    /// a phrase algorithm's clause, whose returns are recorded
    cid: Option<Id>,
    /// the sound mode's variable types and return type
    tenv: HashMap<Id, T>,
    tret: Option<T>,
    /// the return type is an `<emu-result-type>` typing
    typed: bool,
    /// the sound mode's narrowing on the current path
    flow: std::cell::RefCell<Flow>,
    /// slots a closure assigns through its captures: never narrowed
    fixed: HashSet<Id>,
    /// each element a List step adds (by address): its type there, narrowed
    add_t: std::cell::RefCell<HashMap<usize, T>>,
    /// each binding's value (by `ver::key`): its type there, narrowed
    bind_t: std::cell::RefCell<HashMap<usize, T>>,
    /// each slot bound to a List field's read: the element types an add to it needs (`field_els` of its bindings)
    slot_els: HashMap<Id, (Vec<T>, bool)>,
    /// an AO's clause ids, and its parameters' slots where no step assigns them: `Exits`, at each return
    exit_ids: Vec<Id>,
    exit_slots: Vec<Option<Id>>,
    exit_at: std::cell::RefCell<Option<Vec<Option<T>>>>,
    /// in a closure's steps or the silent pass, where a return records no exit
    quiet: std::cell::Cell<bool>,
    /// slot versions: each read's (by address) and binding's (slot, key) slot, each versioned slot's slots, and the join of them a read of no known version takes
    rd: HashMap<usize, Id>,
    bd: HashMap<(Id, usize), Id>,
    vers: HashMap<Id, Vec<Id>>,
    joined: HashMap<Id, Id>,
    /// a phrase algorithm's steps may complete abruptly (a throw, or `?` of a value that may be abrupt)
    abrupt: std::cell::Cell<bool>,
}

/// Slot types narrowed on a path, over the unit's (`tenv`); `dead` past a step that never falls through.
#[derive(Clone, Debug, Default, PartialEq)]
struct Flow {
    ts: HashMap<Id, T>,
    dead: bool,
}

/// A binding of a variable: to an expression's value, a sort, a header type, or an element of a List.
#[derive(Clone)]
enum Bind<'a> {
    E(&'a Expr),
    /// `ReturnIfAbrupt(x)` and the like (`x` read there): x's normal completion's value
    Unwrap(&'a Expr),
    T(Ty),
    H(&'a TyExpr),
    El(&'a Expr),
}

impl<'a, 'c> Alg<'a, 'c> {
    fn name(&self, x: Id) -> String {
        format!("_{}_", self.vars.names.get(x).map_or("?", String::as_str))
    }

    fn op(&self, c: Id) -> String {
        self.cx.d.ops.get(c).filter(|o| !o.is_empty()).cloned().unwrap_or_else(|| self.cx.d.clauses.name(c).to_string())
    }

    /// An expression's sort; with `out`, its findings at `path`.
    fn ty(&self, e: &Expr, at: At) -> Ty {
        let mut sink = at;
        self.infer(e, &mut sink)
    }

    /// Counts a checked site of class `k` (argument, return, operand), and whether its value's sort is known.
    fn tally(&self, at: &At, k: usize, t: &Ty, e: Option<&Expr>) {
        if at.is_some() {
            let mut st = self.cx.stats.borrow_mut();
            st[k].0 += 1;
            st[k].1 += usize::from(!t.is_empty() && !t.v.is_top());
            let b = bucket(t);
            let mut cv = self.cx.cover.borrow_mut();
            cv.sites[k][b] += 1;
            if b == 0 {
                let c = e.map_or_else(|| "?".to_string(), |e| self.cause(e));
                *cv.top.entry((k, c)).or_default() += 1;
            }
        }
    }

    /// Why an expression's sort is any value: its head form, and a variable's binding.
    fn cause(&self, e: &Expr) -> String {
        let d = self.cx.d;
        match e {
            Expr::Var(x) => match self.why.get(x) {
                Some(w) => format!("variable: {w}"),
                None if !self.env.contains_key(x) => "variable: outer variable (an SDO's parameter or the caller's)".into(),
                None => "variable: ?".into(),
            },
            Expr::Paren(x) | Expr::Annot(_, x) | Expr::Erratum(_, _, x) => self.cause(x),
            Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) => format!("?/! of {}", self.cause(x)),
            Expr::Call(Callee::Alg(c), _) => match self.cx.hdrs.get(c) {
                None => "call: no header".into(),
                Some((h, _)) => match h.result() {
                    None => "call: no return type".into(),
                    Some(t) => format!("call: return type {}", ty_why(d, t)),
                },
            },
            Expr::Call(Callee::Prim(_), _) => "primitive: result not in its signature".into(),
            Expr::Sdo(s, ..) => match self.cx.sdos.get(*s).and_then(Option::as_ref).and_then(|h| h.result()) {
                None => "SDO: no return type".into(),
                Some(t) => format!("SDO: return type {}", ty_why(d, t)),
            },
            Expr::Field(..) | Expr::Component(..) => "field read (Record/slot field types)".into(),
            Expr::IMethod(..) => "internal method (object trait)".into(),
            Expr::CMethod(..) => "concrete method (Record trait)".into(),
            Expr::Apply(..) => "closure call (closure types)".into(),
            Expr::Index(..) => "List element (List<T>)".into(),
            Expr::TableStep(..) => "table step".into(),
            Expr::ResumedWith(_) => "resumed value".into(),
            Expr::ChildOf(..) => "child node".into(),
            Expr::Extreme(..) => "choice".into(),
            Expr::Phrase(p, _) => match d.phrases.get(*p).and_then(|x| x.meaning.as_ref()) {
                None => "phrase: no meaning (residue)".into(),
                Some(crate::decls::Meaning::Alg(_)) if self.cx.expand => "phrase: algorithm whose returns are any value".into(),
                Some(crate::decls::Meaning::Alg(_)) => "phrase: algorithm".into(),
                Some(crate::decls::Meaning::Prim { .. }) => "phrase: primitive result not in its signature".into(),
            },
            Expr::Prose(..) => "prose".into(),
            Expr::Bin(..) | Expr::Neg(_) => "operator of unknown operands".into(),
            Expr::Val(ValLit::This) | Expr::ThisValue(_) => "this value".into(),
            e => {
                let f = format!("{e:?}");
                format!("other form: {}", f.split(['(', ' ', '{']).next().unwrap_or(""))
            }
        }
    }

    fn emit(&self, at: &mut At, kind: &'static str, what: String) {
        if let Some((path, out)) = at {
            out.push(Finding { key: self.key.clone(), path: path.to_string(), kind, what });
        }
    }

    fn args(&self, xs: &[Expr], at: &mut At) -> Vec<Ty> {
        xs.iter().map(|x| self.infer(x, at)).collect()
    }

    /// Arguments against a header's parameters (named by `names`): count and sorts.
    fn call(&self, what: &str, callee: Option<Id>, h: &Hdr, names: &dyn Fn(Id, usize) -> String, args: &[Ty], xs: &[Expr], at: &mut At) {
        let need = h.params.iter().filter(|p| !p.2 && !p.3).count();
        let rest = h.params.iter().any(|p| p.3);
        if args.len() < need || (!rest && args.len() > h.params.len()) {
            let more = if rest { " or more".to_string() } else if need < h.params.len() { format!(" to {}", h.params.len()) } else { String::new() };
            self.emit(at, "arity", format!("{what}: {} arguments for {need}{more} parameters", args.len()));
        }
        for (k, (a, p)) in args.iter().zip(&h.params).enumerate() {
            let (Some(t), false) = (&p.1, p.3) else { continue };
            if let (Some(td), Some(x)) = (self.cx.sound, xs.get(k)) {
                let need = of_tyexpr(self.cx.d, &td.hier, t);
                let need = if p.2 { T::opt(&td.hier, need) } else { need };
                let ro = callee.is_some_and(|c| self.cx.ro.contains(&(c, k)));
                self.sound_arg(at, x, &need, ro, &|| format!("{what} argument {} ({})", k + 1, names(p.0, k)));
            }
            let mut pt = of_ty(self.cx.d, t);
            if p.2 {
                pt.v.join(&Atoms::of(ABSENT));
            }
            self.tally(at, 0, a, xs.get(k));
            if at.is_some() && !a.is_empty() && !pt.is_empty() && bucket(a) != 0 && bucket(&pt) != 0 && a.meets(&pt) {
                let mut cv = self.cx.cover.borrow_mut();
                if a.within(&pt) {
                    cv.within[0] += 1;
                } else {
                    cv.within[1] += 1;
                    *cv.overlap.entry(format!("{} for {}", a.show(self.cx.d), pt.show(self.cx.d))).or_default() += 1;
                }
            }
            if a.is_empty() || pt.is_empty() || a.meets(&pt) {
                continue;
            }
            let kind = if a.only_comp() && !pt.comp() { "unchecked" } else { "arg" };
            self.emit(at, kind, format!("{what} argument {} ({}): {} for {}", k + 1, names(p.0, k), a.show(self.cx.d), pt.show(self.cx.d)));
        }
    }

    fn infer(&self, e: &Expr, at: &mut At) -> Ty {
        let d = self.cx.d;
        if let Some(t) = lit_ty(e) {
            if let Expr::Val(ValLit::Num(_, _, Sub::None)) = e {
                self.emit(at, "literal", "a Number literal with neither 𝔽 nor ℤ".into());
            }
            return t;
        }
        match e {
            Expr::Var(x) => {
                if !self.bound.contains(x) {
                    self.emit(at, "unbound", format!("{} is read but never bound", self.name(*x)));
                }
                self.env.get(x).cloned().unwrap_or_else(Ty::top)
            }
            Expr::Call(Callee::Alg(c), xs) => {
                let args = self.args(xs, at);
                match self.cx.hdrs.get(c) {
                    Some((h, vs)) => {
                        self.call(&self.op(*c), Some(*c), h, &|x, _| format!("_{}_", vs.names.get(x).map_or("?", String::as_str)), &args, xs, at);
                        h.result().map_or_else(Ty::top, |t| of_ty(d, t))
                    }
                    None => Ty::top(),
                }
            }
            Expr::Call(Callee::Prim(p), xs) => {
                let args = self.args(xs, at);
                let name = d.prims.name(*p);
                if let Some((pb, rb)) = notation(name) {
                    if let Some(td) = self.cx.sound {
                        let need = atoms_t(&td.hier, &Atoms::of(pb), None);
                        xs.iter().enumerate().for_each(|(k, x)| self.sound_e(at, 0, x, &need, &|| format!("{name} argument {}", k + 1)));
                    }
                    for (k, a) in args.iter().enumerate() {
                        if !a.is_empty() && !a.meets(&Ty::val(pb)) {
                            let kind = if a.only_comp() { "unchecked" } else { "arg" };
                            self.emit(at, kind, format!("{name} argument {}: {} for {}", k + 1, a.show(d), Ty::val(pb).show(d)));
                        }
                    }
                    return Ty::val(rb);
                }
                let res = self.prim_res(name);
                let Some(sig) = crate::sig::of(self.cx.g, name) else { return res };
                for (k, (a, p)) in args.iter().zip(&sig.params).enumerate() {
                    let Some(pt) = self.sig_ty(p) else { continue };
                    if let (Some(_), Some(x)) = (self.cx.sound, xs.get(k)) {
                        self.sound_e(at, 0, x, &self.sig_t(p), &|| format!("{name} argument {}", k + 1));
                    }
                    if !a.is_empty() && !a.meets(&pt) {
                        let kind = if a.only_comp() && !pt.comp() { "unchecked" } else { "arg" };
                        self.emit(at, kind, format!("{name} argument {}: {} for {}", k + 1, a.show(d), pt.show(d)));
                    }
                }
                res
            }
            Expr::Sdo(s, _, x, xs) => {
                self.sound_e(at, 3, x, &T::Node(None), &|| format!("{} of", d.sdos.name(*s)));
                let node = self.infer(x, at);
                let name = d.sdos.name(*s);
                if !node.is_empty() && node.v.bits & NODE == 0 {
                    self.emit(at, "base", format!("{name} of {}", node.show(d)));
                }
                let args = self.args(xs, at);
                match self.cx.sdos.get(*s).and_then(Option::as_ref) {
                    Some(h) => {
                        let ns = self.cx.sdo_names.get(*s);
                        self.call(name, None, h, &|_, k| format!("_{}_", ns.and_then(|n| n.get(k)).map_or("?", String::as_str)), &args, xs, at);
                        h.result().map_or_else(Ty::top, |t| of_ty(d, t))
                    }
                    None => Ty::top(),
                }
            }
            Expr::Component(f, _, x) | Expr::Field(x, f) => {
                self.sound_field(at, x, *f);
                let b = self.infer(x, at);
                self.field(&b, *f, at)
            }
            Expr::IMethod(x, m, xs) => {
                if at.is_some() {
                    *self.cx.cover.borrow_mut().imethods.entry(d.fields.name(*m).to_string()).or_default() += 1;
                }
                if let Some(td) = self.cx.sound {
                    self.sound_e(at, 3, x, &T::union(&td.hier, [T::obj(None), T::Rec(None)]), &|| format!("[[{}]] of", d.fields.name(*m)));
                }
                let b = self.infer(x, at);
                if !b.is_empty() && b.v.bits & (OBJ | REC) == 0 {
                    self.emit(at, "base", format!("[[{}]] of {}", d.fields.name(*m), b.show(d)));
                }
                self.args(xs, at);
                Ty::top()
            }
            Expr::CMethod(x, m, xs) => {
                if at.is_some() {
                    *self.cx.cover.borrow_mut().cmethods.entry(d.methods.name(*m).to_string()).or_default() += 1;
                }
                self.infer(x, at);
                self.args(xs, at);
                Ty::top()
            }
            Expr::Apply(f, xs) => {
                if at.is_some() {
                    self.cx.cover.borrow_mut().applies += 1;
                }
                self.sound_e(at, 3, f, &T::Closure(None), &|| "a call of".into());
                let t = self.infer(f, at);
                if !t.is_empty() && t.v.bits & (CLO | OTHER) == 0 {
                    self.emit(at, "base", format!("a call of {}", t.show(d)));
                }
                self.args(xs, at);
                Ty::top()
            }
            Expr::Index(x, i) => {
                self.sound_e(at, 3, x, &T::List(Box::new(T::Any)), &|| "an index into".into());
                self.sound_e(at, 3, i, &T::Int, &|| "an index".into());
                let b = self.infer(x, at);
                let k = self.infer(i, at);
                if !b.is_empty() && b.v.bits & LIST == 0 {
                    self.emit(at, "base", format!("an index into {}", b.show(d)));
                }
                if !k.is_empty() && k.v.bits & MATH == 0 {
                    self.emit(at, "base", format!("an index {}", k.show(d)));
                }
                if b.v.bits & LIST != 0 && !b.el.is_top() && b.el.bits != 0 { Ty { v: b.el.clone(), el: Atoms::top(), ..Ty::default() } } else { Ty::top() }
            }
            Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) => {
                if matches!(e, Expr::Q(_)) && at.is_some() && self.counts() && self.infer_t(x).members().iter().any(|m| matches!(m, T::Abrupt | T::Any)) {
                    self.abrupt.set(true);
                }
                let t = self.infer(x, at);
                if !t.is_empty() && !t.comp() && !t.v.is_top() {
                    let q = if matches!(e, Expr::Q(_)) { "?" } else { "!" };
                    self.emit(at, "check", format!("{q} of {}, never a completion", t.show(d)));
                }
                t.unwrapped()
            }
            Expr::Neg(x) => {
                if let Some(td) = self.cx.sound {
                    self.sound_e(at, 2, x, &T::union(&td.hier, [T::ext_math(&td.hier), T::Number, T::BigInt]), &|| "-".into());
                }
                let t = self.infer(x, at);
                let r = t.v.bits & (MATH | INF | NUM | BIG);
                if !t.is_empty() && r == 0 {
                    self.emit(at, "operand", format!("- of {}", t.show(d)));
                    return Ty::top();
                }
                Ty::val(r)
            }
            Expr::Bin(o, x, y) => {
                let (a, b) = (self.infer(x, at), self.infer(y, at));
                if a.is_empty() || b.is_empty() {
                    return Ty::top();
                }
                self.tally(at, 2, &a, Some(x));
                self.tally(at, 2, &b, Some(y));
                if let Some(td) = self.cx.sound {
                    let m = if matches!(o, BinOp::Add | BinOp::Sub) { T::ext_math(&td.hier) } else { T::Math };
                    let num = matches!(o, BinOp::Add | BinOp::Plus | BinOp::Times | BinOp::Sub | BinOp::Mul | BinOp::Div);
                    let kinds: Vec<T> = [Some(m), num.then_some(T::Number), Some(T::BigInt)].into_iter().flatten().collect();
                    self.sound_pair(at, x, y, &kinds, &|| format!("{o:?}"));
                }
                let r = bin_rule(*o, a.v.bits, b.v.bits);
                if r == 0 {
                    self.emit(at, "operand", format!("{o:?}: {} and {}", a.show(d), b.show(d)));
                    return Ty::top();
                }
                Ty::val(r)
            }
            // a List may grow: its elements' sort is the header's only
            Expr::List(xs) => {
                self.args(xs, at);
                Ty::list(Atoms::top())
            }
            Expr::Record(_, k, fs) => {
                // a literal's kind is exactly its own
                if let (Some(td), Some(k)) = (self.cx.sound, k) {
                    for (f, x) in fs {
                        let ts: Vec<T> = td.fields_of(*k).into_iter().filter(|y| y.0 == *f && *y.1 != T::Any).map(|y| y.1.clone()).collect();
                        self.sound_store(at, x, (ts, false), &|| format!("[[{}]] of a {} literal", d.fields.name(*f), d.sorts.name(*k)));
                    }
                }
                for (_, x) in fs {
                    self.infer(x, at);
                }
                match k {
                    Some(k) if d.sorts.name(*k) == "Completion Record" => Ty { ab: true, ..Ty::normal(Atoms::top()) },
                    _ => Ty::val(REC),
                }
            }
            Expr::Closure(_) => Ty::val(CLO),
            Expr::Extreme(_, _, t, c) => {
                self.cond(c, at);
                of_ty(d, t)
            }
            Expr::TableStep(_, k, _) => {
                self.infer(k, at);
                Ty::top()
            }
            Expr::ResumedWith(x) | Expr::ChildOf(x, _, _) => {
                self.infer(x, at);
                Ty::top()
            }
            Expr::ThisNode => Ty::val(NODE),
            Expr::Paren(x) | Expr::Annot(_, x) | Expr::Erratum(_, _, x) => self.infer(x, at),
            Expr::Val(ValLit::This) | Expr::ThisValue(_) => Ty::val(LANG),
            Expr::NewTarget => Ty::val(OBJ | UNDEF),
            Expr::Phrase(p, hs) => self.phrase(*p, hs, None, at),
            Expr::Prose(_, ps) => {
                self.parts(ps, at);
                Ty::top()
            }
            _ => Ty::top(),
        }
    }

    /// A phrase's value: a primitive meaning's arguments against the primitive's parameters
    /// (one shape), and its result; `subject`: a predicate phrase's.
    fn phrase(&self, p: Id, hs: &[Hole], subject: Option<&Ty>, at: &mut At) -> Ty {
        self.holes(hs, at);
        if subject.is_none() {
            self.sound_phrase_args(at, p, hs, None);
        }
        let d = self.cx.d;
        if let Some(t) = d.phrase_typing(p, hs) {
            return of_ty(d, &t);
        }
        if let (true, Some(crate::decls::Meaning::Alg(c))) = (self.cx.expand, d.phrases.get(p).and_then(|x| x.meaning.as_ref())) {
            return match self.cx.hdrs.get(c).and_then(|(h, _)| h.result()) {
                Some(t) => of_ty(d, t),
                None => self.cx.rets.get(c).cloned().unwrap_or_else(Ty::top),
            };
        }
        let Some(crate::decls::Meaning::Prim { prim, args, neg }) = d.phrases.get(p).and_then(|x| x.meaning.as_ref()) else { return Ty::top() };
        let name = d.prims.name(*prim);
        let sigs = crate::sig::all(self.cx.g, name);
        if let [sig] = sigs.as_slice() {
            if sig.params.len() == args.len() && !sig.variadic {
                for (k, (a, pt)) in args.iter().zip(&sig.params).enumerate() {
                    let t = match a {
                        crate::decls::PArg::Hole(i) => match hs.get(*i) {
                            Some(Hole::E(Expr::Var(x))) => self.env.get(x).cloned().unwrap_or_else(Ty::top),
                            Some(Hole::E(e)) => self.infer(e, &mut None),
                            _ => continue,
                        },
                        crate::decls::PArg::Subject => match subject {
                            Some(t) => t.clone(),
                            None => continue,
                        },
                        _ => continue,
                    };
                    let (pt, ptt) = match notation(name) {
                        Some((pb, _)) => (Some(Ty::val(pb)), None),
                        None => (self.sig_ty(pt), Some(self.sig_t(pt))),
                    };
                    let Some(pt) = pt else { continue };
                    if let (Some(td), crate::decls::PArg::Hole(i)) = (self.cx.sound, a) {
                        if let Some(Hole::E(e)) = hs.get(*i) {
                            let need = ptt.unwrap_or_else(|| ty_t(&td.hier, &pt));
                            self.sound_e(at, 0, e, &need, &|| format!("{} ({name}) argument {}", d.phrases[p].name, k + 1));
                        }
                    }
                    if !t.is_empty() && !t.meets(&pt) {
                        let kind = if t.only_comp() && !pt.comp() { "unchecked" } else { "arg" };
                        self.emit(at, kind, format!("{} ({name}) argument {}: {} for {}", d.phrases[p].name, k + 1, t.show(d), pt.show(d)));
                    }
                }
            }
        }
        if *neg {
            return Ty::val(BOOL);
        }
        if let Some((_, b)) = notation(name) {
            return Ty::val(b);
        }
        self.prim_res(name)
    }

    /// A primitive's declared result.
    fn prim_res(&self, name: &str) -> Ty {
        crate::sig::res(self.cx.g, name).and_then(|r| self.sig_ty(&r)).unwrap_or_else(Ty::top)
    }

    /// A signature's type text: by the header-type grammar, else as sort names.
    fn sig_ty(&self, s: &str) -> Option<Ty> {
        let d = self.cx.d;
        self.cx.sig_tys.get(s).map(|t| of_ty(d, t)).filter(|t| !t.is_top()).or_else(|| text_ty(d, s))
    }

    /// `sig_ty` in `T`.
    fn sig_t(&self, s: &str) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        match self.cx.sig_tys.get(s).map(|t| of_tyexpr(self.cx.d, &td.hier, t)) {
            Some(T::Any) | None => text_ty(self.cx.d, s).map_or(T::Any, |t| ty_t(&td.hier, &t)),
            Some(t) => t,
        }
    }

    /// A field's value, where the base may have it.
    fn field(&self, b: &Ty, f: Id, at: &mut At) -> Ty {
        let cx = self.cx;
        if at.is_some() {
            let mut cv = cx.cover.borrow_mut();
            cv.fields[if b.v.is_top() || b.is_empty() { 0 } else if b.v.bits & (OBJ | REC) != 0 { 1 } else { 2 }] += 1;
            *cv.field_names.entry(cx.d.fields.name(f).to_string()).or_default() += 1;
        }
        if b.is_empty() {
            return Ty::top();
        }
        let comp_field = [cx.f_type, cx.f_value, cx.f_target].contains(&Some(f));
        let ok = b.v.bits & (OBJ | REC) != 0 || (b.v.bits & SYM != 0 && cx.f_desc == Some(f)) || (b.comp() && comp_field);
        if !ok {
            self.emit(at, "base", format!("[[{}]] of {}", cx.d.fields.name(f), b.show(cx.d)));
        }
        Ty::top()
    }

    /// The sound mode's test of a field's base: an Object, a Record, or a completion or Symbol with the field.
    fn sound_field(&self, at: &At, x: &Expr, f: Id) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let cx = self.cx;
        let mut need = vec![T::obj(None), T::Rec(None)];
        if [cx.f_type, cx.f_value, cx.f_target].contains(&Some(f)) {
            need.extend([T::Normal(Box::new(T::Any)), T::Abrupt]);
        }
        if cx.f_desc == Some(f) {
            need.push(T::Symbol);
        }
        self.sound_e(at, 3, x, &T::union(&td.hier, need), &|| format!("[[{}]] of", cx.d.fields.name(f)));
    }

    fn cond(&self, c: &Cond, at: &mut At) {
        let d = self.cx.d;
        match c {
            Cond::Preds(e, p, r) => {
                let t = self.infer(e, at);
                for p in std::iter::once(p).chain(r.iter().map(|x| &x.1)) {
                    if let Pred::Phrase(ph, hs) = p {
                        self.sound_phrase_args(at, *ph, hs, Some(e));
                    }
                    self.pred(p, &t, at);
                }
            }
            Cond::Rel(o, x, y) => {
                let (a, b) = (self.infer(x, at), self.infer(y, at));
                self.tally(at, 2, &a, Some(x));
                self.tally(at, 2, &b, Some(y));
                if let Some(td) = self.cx.sound {
                    self.sound_pair(at, x, y, &[T::ext_math(&td.hier), T::Number, T::BigInt], &|| rel_word(*o).into());
                }
                if !a.is_empty() && !b.is_empty() && !rel_ok(a.v.bits, b.v.bits) {
                    self.emit(at, "operand", format!("{}: {} and {}", rel_word(*o), a.show(d), b.show(d)));
                }
            }
            // a later operand is evaluated where the ones before it held (and) or failed (or)
            Cond::And(_, cs) | Cond::Or(_, cs) => {
                let f0 = self.flow();
                for k in cs {
                    self.cond(k, at);
                    self.set_flow(self.branch(k, &self.flow(), matches!(c, Cond::And(..))));
                }
                self.set_flow(f0);
            }
            Cond::Paren(c) => self.cond(c, at),
            Cond::Alg(..) => {}
            Cond::Phrase(p, hs) => {
                self.phrase(*p, hs, None, at);
            }
            Cond::Prose(_, ps) => self.parts(ps, at),
        }
    }

    fn pred(&self, p: &Pred, subject: &Ty, at: &mut At) {
        match p {
            Pred::IsVal(_, _, xs) => {
                self.args(xs, at);
            }
            Pred::IsTy(..) => {}
            Pred::Phrase(p, hs) => {
                self.phrase(*p, hs, Some(subject), at);
            }
        }
    }

    fn holes(&self, hs: &[Hole], at: &mut At) {
        for h in hs {
            match h {
                // a phrase's variable hole may name a variable it binds
                Hole::E(Expr::Var(_)) => {}
                Hole::E(e) => {
                    self.infer(e, at);
                }
                Hole::C(c) | Hole::Bc(_, c) => self.cond(c, at),
                Hole::L(_, xs) => xs.iter().filter(|x| !matches!(x, Expr::Var(_))).for_each(|x| {
                    self.infer(x, at);
                }),
                _ => {}
            }
        }
    }

    fn parts(&self, ps: &[Part], at: &mut At) {
        for p in ps {
            if let Part::Hole(h) = p {
                self.holes(std::slice::from_ref(h), at);
            }
        }
    }
}

/// The sound mode: each site's type in `T`, accepted only when within the type needed.
impl<'a, 'c> Alg<'a, 'c> {
    /// Records a site of class `k` (`SOUND_SITES`) of kind `c` (`SOUND`); a finding unless within.
    fn sound_rec(&self, at: &At, k: usize, c: usize, what: &dyn Fn() -> String) {
        let Some((path, _)) = at else { return };
        let mut cv = self.cx.cover.borrow_mut();
        cv.sound_n[k][c] += 1;
        if c != 0 {
            cv.sound.push(Finding { key: self.key.clone(), path: path.to_string(), kind: SOUND[c], what: what() });
        }
    }

    /// A value of type `t` at a site of class `k` that needs `need`; `what` names the site.
    fn sound_at(&self, at: &At, k: usize, t: &T, need: &T, what: &dyn Fn() -> String) {
        let Some(td) = self.cx.sound else { return };
        let h = &td.hier;
        let t = &t.used(h);
        let c = if t.sub(h, need) { 0 } else if *t == T::Any { 2 } else if t.meets(h, need) { 1 } else { 3 };
        let d = self.cx.d;
        self.sound_rec(at, k, c, &|| format!("{}: {} for {}", what(), t.show(d), need.show(d)));
    }

    /// An expression at a site of class `k` against the type needed.
    fn sound_e(&self, at: &At, k: usize, e: &Expr, need: &T, what: &dyn Fn() -> String) {
        if self.cx.sound.is_some() && at.is_some() {
            self.sound_at(at, k, &self.check_t(e, need), need, what);
        }
    }

    /// An argument for a List parameter the callee only reads (`ro`): its elements within the parameter's.
    fn sound_arg(&self, at: &At, e: &Expr, need: &T, ro: bool, what: &dyn Fn() -> String) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let h = &td.hier;
        let t = self.check_t(e, need);
        let n = list_el(h, need);
        let t = match &t {
            T::Any => T::Any,
            _ if ro && n != T::Any && n != T::never() => T::union(h, t.members().iter().map(|m| match m {
                T::List(el) if el.sub(h, &n) => T::List(Box::new(n.clone())),
                m => m.clone(),
            })),
            _ => t,
        };
        self.sound_at(at, 0, &t, need, what);
    }

    /// A phrase algorithm's holes, and a predicate's subject (its last parameter), against its parameters' types.
    fn sound_phrase_args(&self, at: &At, p: Id, hs: &[Hole], subject: Option<&Expr>) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let d = self.cx.d;
        let Some(crate::decls::Meaning::Alg(c)) = d.phrases.get(p).and_then(|x| x.meaning.as_ref()) else { return };
        let Some((hd, vs)) = self.cx.hdrs.get(c) else { return };
        let xs: Vec<Option<&Expr>> = hs.iter().map(|h| if let Hole::E(e) = h { Some(e) } else { None }).chain(subject.map(Some)).collect();
        if xs.len() != hd.params.len() {
            return;
        }
        for (k, (x, pa)) in xs.iter().zip(&hd.params).enumerate() {
            let (Some(x), Some(t), false) = (x, &pa.1, pa.3) else { continue };
            let need = of_tyexpr(d, &td.hier, t);
            let need = if pa.2 { T::opt(&td.hier, need) } else { need };
            let what = || format!("{} argument {} (_{}_)", d.phrases[p].name, k + 1, vs.names.get(pa.0).map_or("?", String::as_str));
            self.sound_arg(at, x, &need, self.cx.ro.contains(&(*c, k)), &what);
        }
    }

    /// A value a field write stores (`Val` as it is), within each of the field's declared types `ts`; `open`: the base may be of a kind that declares none.
    fn sound_store(&self, at: &At, e: &Expr, (ts, open): (Vec<T>, bool), what: &dyn Fn() -> String) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let h = &td.hier;
        if ts.is_empty() {
            return;
        }
        let all = ts.iter().fold(T::Any, |a, t| a.within(h, t));
        let t = self.infer_t(e);
        let n = list_el(h, &all);
        let t = match &t {
            T::List(el) if fresh(self.cx.d, e) && n != T::Any && n != T::never() && el.sub(h, &n) => T::List(Box::new(n)),
            _ => t,
        };
        self.sound_each(at, &t, (ts, open), what);
    }

    /// A value of type `t` within each of `ts` (non-empty); `open`: at worst meets.
    fn sound_each(&self, at: &At, t: &T, (ts, open): (Vec<T>, bool), what: &dyn Fn() -> String) {
        let Some(td) = self.cx.sound else { return };
        let h = &td.hier;
        let all = ts.iter().fold(T::Any, |a, t| a.within(h, t));
        let any = T::union(h, ts);
        let c = if t.sub(h, &all) { 0 } else if *t == T::Any { 2 } else if open || t.meets(h, &any) { 1 } else { 3 };
        let d = self.cx.d;
        let need = || match (all == any, open) {
            (true, false) => all.show(d),
            (false, false) => format!("each of {}", any.show(d)),
            (_, true) => format!("each of {}, or none", any.show(d)),
        };
        self.sound_rec(at, 0, c, &|| format!("{}: {} for {}", what(), t.show(d), need()));
    }

    /// Field `f`'s declared types at the kinds a base of type `b` may be (a Record's kind and subkinds, any kind for `Rec`, an object's sorts, a completion's value), and whether one may declare none.
    fn store_ts(&self, b: &T, f: Id) -> (Vec<T>, bool) {
        let Some(td) = self.cx.sound else { return (Vec::new(), false) };
        let h = &td.hier;
        let own = |k: Id| td.fields_of(k).into_iter().find(|x| x.0 == f).map(|x| x.1.clone());
        let decl = |slots: bool, ok: &dyn Fn(Option<Id>) -> bool| -> Vec<T> { td.shapes.iter().filter(|s| s.slots == slots && ok(s.sort)).filter_map(|s| s.fields.iter().find(|x| x.0 == f).map(|x| x.1.clone())).collect() };
        let (mut out, mut open) = (Vec::new(), false);
        for m in b.members() {
            match m {
                T::Rec(Some(k)) => {
                    let o = own(*k);
                    open |= o.is_none();
                    out.extend(o);
                    out.extend(decl(false, &|s| s.is_some_and(|s| s != *k && h.below(s, *k))));
                }
                T::Object(ks) => {
                    let o: Vec<T> = ks.iter().filter_map(|&k| own(k)).collect();
                    open |= o.is_empty();
                    out.extend(o);
                    out.extend(decl(true, &|s| s.is_some_and(|s| ks.iter().all(|&k| s != k && h.below(s, k)))));
                }
                T::Rec(None) => {
                    open = true;
                    out.extend(decl(false, &|_| true));
                }
                T::Any => {
                    open = true;
                    out.extend(decl(false, &|_| true).into_iter().chain(decl(true, &|_| true)));
                }
                T::Normal(x) if self.cx.f_value == Some(f) => out.push((**x).clone()),
                T::Normal(_) | T::Abrupt if self.cx.f_type == Some(f) => out.push(T::Enum(BTreeSet::new())),
                _ => {}
            }
        }
        open |= out.contains(&T::Any);
        out.retain(|t| *t != T::Any);
        out.sort();
        out.dedup();
        (out, open)
    }

    /// A List field's element types at every kind its base may be (`store_ts`), with the List's own; `None` unless `l` is a field read.
    fn field_els(&self, l: &Expr) -> Option<(Vec<T>, bool)> {
        let (Expr::Field(x, f) | Expr::Component(f, _, x)) = strip(l) else { return None };
        let h = &self.cx.sound?.hier;
        let (ts, mut open) = self.store_ts(&self.infer_t(x), *f);
        let mut els: Vec<T> = ts.iter().map(|t| list_el(h, t)).chain([list_el(h, &self.infer_t(l))]).filter(|t| *t != T::never()).collect();
        open |= els.contains(&T::Any);
        els.retain(|t| *t != T::Any);
        els.sort();
        els.dedup();
        Some((els, open))
    }

    /// A slot bound to a List field's read (`slot_els`): its bindings' element types, with its own; `None` for any other List.
    fn alias_els(&self, l: &Expr) -> Option<(Vec<T>, bool)> {
        let r @ Expr::Var(x) = strip(l) else { return None };
        let (ts, open) = self.slot_els.get(&self.rid(r, *x)).cloned()?;
        let own = list_el(&self.cx.sound?.hier, &self.infer_t(l));
        let own = if own == T::never() { Vec::new() } else { vec![own] };
        let (mut ts, open) = els_join(Some((ts, open)), (own, false));
        let open = open || ts.contains(&T::Any);
        ts.retain(|t| *t != T::Any);
        Some((ts, open))
    }

    /// An element of type `t` (`e` if it is an expression) added to List `l`: within each element type a field's aliases need, else the List's.
    fn sound_el(&self, at: &At, e: Option<&Expr>, t: &T, l: &Expr, what: &dyn Fn() -> String) {
        let Some(td) = self.cx.sound else { return };
        let h = &td.hier;
        if let Some((ts, open)) = self.field_els(l).or_else(|| self.alias_els(l)) {
            if !ts.is_empty() {
                let all = ts.iter().fold(T::Any, |a, t| a.within(h, t));
                let t = e.map_or_else(|| t.used(h), |e| self.check_t(e, &all));
                self.sound_each(at, &t, (ts, open), what);
            }
            return;
        }
        let need = list_el(h, &self.infer_t(l));
        if need != T::Any && need != T::never() {
            match e {
                Some(e) => self.sound_e(at, 0, e, &need, what),
                None => self.sound_at(at, 0, t, &need, what),
            }
        }
    }

    /// An element a List step adds, within the List's element type where that is known.
    fn sound_add(&self, at: &At, p: Id, hs: &[Hole]) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let h = &td.hier;
        if let (true, Some(Hole::E(a)), Some(Hole::E(b))) = (self.cx.d.phrases.get(p).is_some_and(|x| x.name == "ph-append-elements"), hs.first(), hs.get(1)) {
            self.sound_el(at, None, &elem_t(h, &self.infer_t(a)), b, &|| "the elements added by ph-append-elements".into());
            return;
        }
        let Some((el, l)) = list_add(self.cx.d, p, hs) else { return };
        let t = self.infer_t(el).used(h);
        let mut seen = self.add_t.borrow_mut();
        let j = seen.get(&(el as *const Expr as usize)).map_or(t.clone(), |x| x.join(&td.hier, &t));
        seen.insert(el as *const Expr as usize, j);
        drop(seen);
        self.sound_el(at, Some(el), &t, l, &|| format!("an element added by {}", self.cx.d.phrases[p].name));
    }

    /// An expression's type where `need` is wanted: a new List takes the List type needed if its elements fit.
    fn check_t(&self, e: &Expr, need: &T) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        let h = &td.hier;
        let t = self.infer_t(e).used(h);
        let n = list_el(h, need);
        match &t {
            T::List(el) if fresh(self.cx.d, e) && n != T::Any && n != T::never() && el.sub(h, &n) => T::List(Box::new(n)),
            _ => t,
        }
    }

    /// Two operands both within one of `kinds`, as one operand site.
    fn sound_pair(&self, at: &At, x: &Expr, y: &Expr, kinds: &[T], what: &dyn Fn() -> String) {
        let (Some(td), true) = (self.cx.sound, at.is_some()) else { return };
        let (d, h) = (self.cx.d, &td.hier);
        let (a, b) = (self.infer_t(x).used(h), self.infer_t(y).used(h));
        let need = T::union(h, kinds.iter().cloned());
        let c = if kinds.iter().any(|n| a.sub(h, n) && b.sub(h, n)) {
            0
        } else if a == T::Any || b == T::Any {
            2
        } else if a.meets(h, &need) && b.meets(h, &need) {
            1
        } else {
            3
        };
        self.sound_rec(at, 2, c, &|| format!("{}: {} and {} for {}", what(), a.show(d), b.show(d), need.show(d)));
    }

    /// An expression's type in `T`: header types, declared fields and methods, primitives' value kinds.
    fn infer_t(&self, e: &Expr) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        let (d, h) = (self.cx.d, &td.hier);
        if let Some(t) = lit_t(e) {
            return t;
        }
        let hdr_ret = |r: Option<&TyExpr>| r.map_or(T::Any, |t| of_tyexpr(d, h, t));
        match e {
            Expr::Var(x) => self.slot_t(&self.flow.borrow(), self.rid(e, *x)),
            Expr::Call(Callee::Alg(c), _) => hdr_ret(self.cx.hdrs.get(c).and_then(|(h, _)| h.result())),
            Expr::Call(Callee::Prim(p), _) => {
                let name = d.prims.name(*p);
                match notation(name) {
                    Some(_) if matches!(name, "floor" | "truncate") => T::Int,
                    Some((_, rb)) => atoms_t(h, &Atoms::of(rb), None),
                    None => crate::sig::res(self.cx.g, name).map_or(T::Any, |r| self.sig_t(&r)),
                }
            }
            Expr::Sdo(s, ..) => hdr_ret(self.cx.sdos.get(*s).and_then(Option::as_ref).and_then(|h| h.result())),
            Expr::Component(f, _, x) | Expr::Field(x, f) => self.field_t(&self.infer_t(x), *f),
            Expr::IMethod(_, m, _) => self.method_t(&T::obj(None), SigName::Internal(*m)),
            Expr::CMethod(x, m, _) => self.method_t(&self.infer_t(x), SigName::Method(*m)),
            Expr::Apply(f, _) => match self.infer_t(f) {
                T::Closure(Some((_, r))) => *r,
                _ => T::Any,
            },
            Expr::Index(x, _) => elem_t(h, &self.infer_t(x)),
            Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) => unwrap_t(h, &self.infer_t(x)),
            Expr::Neg(x) => {
                let t = self.infer_t(x);
                if [T::ext_math(h), T::Number, T::BigInt].iter().any(|n| t.sub(h, n)) { t } else { T::Any }
            }
            Expr::Bin(o, x, y) => bin_t(h, *o, &self.infer_t(x), &self.infer_t(y)),
            Expr::List(xs) => T::List(Box::new(T::union(h, xs.iter().map(|x| self.infer_t(x))))),
            Expr::Record(_, k, _) => match k {
                Some(k) => sort_t(d, h, *k),
                None => T::Rec(None),
            },
            Expr::Closure(_) => T::Closure(None),
            Expr::Extreme(_, _, t, _) => of_tyexpr(d, h, t),
            Expr::ThisNode => T::Node(None),
            // the row's own node, or a child, which an optional symbol leaves absent (Leaf.childAt)
            Expr::Child(6, n, _) => T::Node(Some(*n)),
            Expr::Child(_, n, _) | Expr::ChildOf(_, n, _) => T::opt(h, T::Node(Some(*n))),
            Expr::Paren(x) | Expr::Annot(_, x) | Expr::Erratum(_, _, x) => self.infer_t(x),
            Expr::Val(ValLit::This) | Expr::ThisValue(_) => T::lang(),
            Expr::NewTarget => T::union(h, [T::Undefined, T::obj(None)]),
            Expr::Phrase(p, hs) => d.phrase_typing(*p, hs).map_or_else(|| self.phrase_t(*p, hs), |t| of_tyexpr(d, h, &t)),
            _ => T::Any,
        }
    }

    /// A phrase's value in `T`: its algorithm's return type, its primitive's result, a new List's elements.
    fn phrase_t(&self, p: Id, hs: &[Hole]) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        let (d, h) = (self.cx.d, &td.hier);
        if let Some(crate::decls::Meaning::Prim { prim, args, neg: false }) = d.phrases.get(p).and_then(|x| x.meaning.as_ref()) {
            let items: Vec<&Expr> = match args.first() {
                Some(crate::decls::PArg::Hole(i)) => match hs.get(*i) {
                    Some(Hole::E(e)) => vec![e],
                    Some(Hole::L(_, xs)) => xs.iter().collect(),
                    _ => Vec::new(),
                },
                _ => Vec::new(),
            };
            let one = |f: &dyn Fn(T) -> T| if items.is_empty() { T::Any } else { f(T::union(h, items.iter().map(|x| self.infer_t(x)))) };
            match d.prims.name(*prim) {
                "ListNew" => return T::List(Box::new(T::never())),
                "ListOf1" => return one(&|t| T::List(Box::new(t))),
                "Copy" => return one(&|t| t),
                "ListConcat" if !items.is_empty() => {
                    let els: Vec<T> = items.iter().map(|x| list_el(h, &self.infer_t(x))).collect();
                    return if els.contains(&T::Any) { T::List(Box::new(T::Any)) } else { T::List(Box::new(T::union(h, els))) };
                }
                _ => {}
            }
        }
        match d.phrases.get(p).and_then(|x| x.meaning.as_ref()) {
            Some(crate::decls::Meaning::Alg(c)) => self.cx.hdrs.get(c).and_then(|(hd, _)| hd.result()).map_or_else(|| self.cx.facts.rets.get(c).cloned().unwrap_or(T::Any), |t| of_tyexpr(d, h, t)),
            Some(crate::decls::Meaning::Prim { neg: true, .. }) => T::Bool,
            Some(crate::decls::Meaning::Prim { prim, .. }) => {
                let name = d.prims.name(*prim);
                match notation(name) {
                    Some((_, b)) => atoms_t(h, &Atoms::of(b), None),
                    None => crate::sig::res(self.cx.g, name).map_or(T::Any, |r| self.sig_t(&r)),
                }
            }
            _ => T::Any,
        }
    }

    /// A field's type: by the base's Record kind (or its subkinds') or object sorts, a completion's, else Any.
    fn field_t(&self, b: &T, f: Id) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        if *b == T::never() {
            return T::never();
        }
        let h = &td.hier;
        let own = |k: Id| td.fields_of(k).into_iter().find(|x| x.0 == f).map(|x| x.1.clone());
        // a Record of kind k, or an object of sorts ks, may be of a subkind that redeclares the field
        let below = |slots: bool, ks: &[Id]| {
            td.shapes.iter().filter(|s| s.slots == slots && s.sort.is_some_and(|s| ks.iter().all(|&k| s != k && h.below(s, k)))).filter_map(|s| s.fields.iter().find(|x| x.0 == f).map(|x| x.1.clone())).collect::<Vec<T>>()
        };
        let mut out = Vec::new();
        for m in b.members() {
            let t = match m {
                T::Rec(Some(k)) => {
                    let ts = below(false, &[*k]);
                    match own(*k) {
                        Some(t) => T::union(h, ts.into_iter().chain([t])),
                        None if ts.is_empty() => T::Any,
                        None => T::union(h, ts),
                    }
                }
                T::Object(s) => match s.iter().find_map(|&k| own(k)) {
                    Some(t) => T::union(h, below(true, &s.iter().copied().collect::<Vec<_>>()).into_iter().chain([t])),
                    None => T::Any,
                },
                // an anonymous Record's fields are no table's
                T::Rec(None) => T::Any,
                T::Normal(x) if self.cx.f_value == Some(f) => (**x).clone(),
                T::Normal(_) | T::Abrupt if self.cx.f_type == Some(f) => T::Enum(BTreeSet::new()),
                T::Normal(_) | T::Abrupt | T::Symbol => T::Any,
                _ => continue,
            };
            out.push(t);
        }
        if out.is_empty() { T::Any } else { T::union(&td.hier, out) }
    }

    /// A method's result: the trait method of that name whose root the base meets, else the first.
    fn method_t(&self, b: &T, m: SigName) -> T {
        let Some(td) = self.cx.sound else { return T::Any };
        trait_method(self.cx.d, td, b, m).map_or(T::Any, |(_, x)| x.ret.clone())
    }

    /// The variables' types in `T`, as `solve` does in `Ty`; a List slot that holds only new Lists also takes its elements from its `uses`.
    fn solve_t(&mut self, hdr: Option<&Hdr>, bs: &[(Id, Bind)], uses: &[(Id, LUse)]) {
        // a slot bound to a List made elsewhere keeps its bindings' elements: fewer such slots, solved again
        let mut shared: HashSet<Id> = HashSet::new();
        loop {
            self.solve_t_with(hdr, bs, uses, &shared);
            self.join_versions();
            let Some(td) = self.cx.sound else { return };
            let more: HashSet<Id> = bs.iter().filter(|(x, b)| !shared.contains(x) && self.binds_shared(&td.hier, b)).map(|b| b.0).collect();
            if more.is_empty() {
                break;
            }
            shared.extend(more);
        }
        self.slot_els = HashMap::new();
        for (x, b) in bs {
            if let Some(e) = self.field_els_of(b) {
                let y = self.slot_els.remove(x);
                self.slot_els.insert(*x, els_join(y, e));
            }
        }
        for (x, vs) in &self.vers {
            let j = vs.iter().filter_map(|v| self.slot_els.get(v).cloned()).reduce(|a, b| els_join(Some(a), b));
            if let Some(j) = j {
                self.slot_els.insert(self.joined[x], j);
            }
        }
    }

    /// `field_els` of a binding to a field read.
    fn field_els_of(&self, b: &Bind) -> Option<(Vec<T>, bool)> {
        let Bind::E(e) = b else { return None };
        self.field_els(e)
    }

    /// Whether a binding may hold a List not made by it (`fresh`).
    fn binds_shared(&self, h: &Hier, b: &Bind) -> bool {
        let t = match b {
            Bind::E(e) if fresh(self.cx.d, e) => return false,
            Bind::E(e) => self.infer_t(e),
            Bind::T(t) => ty_t(h, t),
            Bind::Unwrap(y) => unwrap_t(h, &self.infer_t(y)),
            Bind::H(t) => of_tyexpr(self.cx.d, h, t),
            Bind::El(l) => elem_t(h, &self.infer_t(l)),
        };
        t == T::Any || t.members().iter().any(|m| matches!(m, T::List(_)))
    }

    /// `solve_t` where the slots in `shared` take no elements from their uses.
    fn solve_t_with(&mut self, hdr: Option<&Hdr>, bs: &[(Id, Bind)], uses: &[(Id, LUse)], shared: &HashSet<Id>) {
        let Some(td) = self.cx.sound else { return };
        let (d, h) = (self.cx.d, &td.hier);
        self.set_flow(Flow::default());
        let mut base: HashMap<Id, T> = HashMap::new();
        if let Some(hd) = hdr {
            let builtin = hd.kind == "builtin";
            let lang = if builtin { T::lang() } else { T::Any };
            for (slot, t, opt, rest) in &hd.params {
                let mut ty = match (rest, t) {
                    (true, _) => T::List(Box::new(lang.clone())),
                    (false, Some(t)) => of_tyexpr(d, h, t),
                    (false, None) => lang.clone(),
                };
                if builtin && !rest {
                    ty = T::union(h, [ty, T::Missing]);
                } else if *opt {
                    ty = T::opt(h, ty);
                }
                base.insert(*slot, base.get(slot).map_or(ty.clone(), |x| x.join(h, &ty)));
            }
            if let Some((slot, t)) = &hd.recv {
                base.insert(*slot, of_tyexpr(d, h, t));
            }
        }
        // from no value for a bound slot: the least fixed point
        self.tenv = base.clone();
        for (x, _) in bs {
            self.tenv.entry(*x).or_insert_with(T::never);
        }
        for _ in 0..12 {
            let mut next: HashMap<Id, T> = base.clone();
            for (x, b) in bs {
                let t = match b {
                    Bind::E(e) => self.infer_t(e),
                    Bind::T(t) => ty_t(h, t),
                    Bind::Unwrap(y) => unwrap_t(h, &self.infer_t(y)),
                    Bind::H(t) => of_tyexpr(d, h, t),
                    Bind::El(l) => elem_t(h, &self.infer_t(l)),
                };
                // both the type where it is bound, narrowed, and the type under these slot types hold
                let t = match ver::key(b).and_then(|k| self.bind_t.borrow().get(&k).cloned()) {
                    Some(seen) => seen.within(h, &t),
                    None => t,
                };
                let j = next.get(x).map_or(t.clone(), |y| y.join(h, &t));
                next.insert(*x, j);
            }
            let mut add: HashMap<Id, T> = HashMap::new();
            for (x, u) in uses.iter().filter(|u| !base.contains_key(&u.0) && !shared.contains(&u.0)) {
                let t = match u {
                    LUse::Add(e, true) => self.add_t.borrow().get(&(*e as *const Expr as usize)).cloned().unwrap_or_else(|| self.infer_t(e).used(h)),
                    LUse::Add(e, false) => self.infer_t(e).used(h),
                    LUse::Alias(y, _) => list_el(h, &self.tenv.get(y).cloned().unwrap_or(T::Any)),
                    LUse::Field(Some(k), f) => td.fields_of(*k).into_iter().find(|x| x.0 == *f).map_or(T::Any, |x| list_el(h, x.1)),
                    LUse::Field(None, _) => T::Any,
                    LUse::FieldOf(b, f) => list_el(h, &self.field_t(&self.infer_t(b), *f)),
                    LUse::AddAll(e) => list_el(h, &self.infer_t(e)),
                    LUse::Arg(c, k) if self.cx.ro.contains(&(*c, *k)) => T::never(),
                    LUse::Arg(c, k) => self.cx.hdrs.get(c).map_or(T::Any, |(hd, _)| param_el(d, h, hd, *k)),
                    LUse::SdoArg(s, k) => self.cx.sdos.get(*s).and_then(Option::as_ref).map_or(T::Any, |hd| param_el(d, h, hd, *k)),
                    LUse::Ret => self.tret.as_ref().map_or(T::Any, |r| list_el(h, &unwrap_t(h, r))),
                    LUse::Escape => T::Any,
                };
                let j = add.get(x).map_or(t.clone(), |y| y.join(h, &t));
                add.insert(*x, j);
            }
            for (x, t) in add {
                if let Some(y) = next.get(&x) {
                    let y = with_els(h, y, &t);
                    next.insert(x, y);
                }
            }
            // a shared List of no known element may hold any
            for x in shared {
                if let Some(y) = next.get(x) {
                    let y = T::union(h, y.members().iter().map(|m| if *m == T::List(Box::new(T::never())) { T::List(Box::new(T::Any)) } else { m.clone() }));
                    next.insert(*x, y);
                }
            }
            // each round joins the one before: an ascending chain
            for (x, t) in next.iter_mut() {
                if let Some(y) = self.tenv.get(x) {
                    *t = t.join(h, y);
                }
            }
            if next == self.tenv {
                self.tenv.values_mut().filter(|t| **t == T::never()).for_each(|t| *t = T::Any);
                return;
            }
            self.tenv = next;
        }
        self.tenv.values_mut().for_each(|t| *t = T::Any);
    }
}

/// Slot versions: a slot whose binding groups (`ver::groups`) have disjoint types takes a slot per group.
impl<'a, 'c> Alg<'a, 'c> {
    /// The slot a read of `x` (the `Expr::Var` at `e`) is of: its version's, else the join of the versions.
    fn rid(&self, e: &Expr, x: Id) -> Id {
        match self.rd.get(&ver::addr(e)) {
            Some(v) => *v,
            None => self.joined.get(&x).copied().unwrap_or(x),
        }
    }

    /// The slot the binding of `x` with key `k` (`ver::key`) assigns.
    fn bid(&self, x: Id, k: usize) -> Id {
        self.bd.get(&(x, k)).copied().unwrap_or(x)
    }

    /// A slot and its versions' slots.
    fn all_ids(&self, x: Id) -> Vec<Id> {
        std::iter::once(x).chain(self.vers.get(&x).into_iter().flatten().copied()).chain(self.joined.get(&x).copied()).collect()
    }

    /// Gives each binding group of the slots in `split` its own slot from `next` on; the entry value's group keeps the slot's.
    fn assign(&mut self, g: &ver::Groups, split: &HashSet<Id>, mut next: Id) {
        (self.rd, self.bd, self.vers, self.joined) = Default::default();
        let mut xs: Vec<&Id> = g.of.keys().filter(|x| split.contains(x)).collect();
        xs.sort();
        for &x in xs {
            let gs = &g.of[&x];
            let first = gs.iter().position(|ks| ks.contains(&ver::ENTRY)).unwrap_or(0);
            let ids: Vec<Id> = (0..gs.len())
                .map(|i| {
                    if i == first {
                        return x;
                    }
                    next += 1;
                    next - 1
                })
                .collect();
            for (i, ks) in gs.iter().enumerate() {
                self.bd.extend(ks.iter().map(|&k| ((x, k), ids[i])));
            }
            self.joined.insert(x, next);
            next += 1;
            self.vers.insert(x, ids);
        }
        for (&a, &(x, i)) in &g.read {
            if let Some(ids) = self.vers.get(&x) {
                self.rd.insert(a, ids[i]);
            }
        }
    }

    /// The bindings and List uses by version.
    fn by_version<'b>(&self, bs: &[(Id, Bind<'b>)], uses: &[Use<'b>]) -> (Vec<(Id, Bind<'b>)>, Vec<(Id, LUse<'b>)>) {
        let bs = bs.iter().map(|(x, b)| (ver::key(b).map_or(*x, |k| self.bid(*x, k)), b.clone())).collect();
        let uses = uses
            .iter()
            .map(|(x, u, a)| {
                let x = match self.rd.get(a) {
                    Some(v) => *v,
                    None => self.joined.get(x).copied().unwrap_or(*x),
                };
                (x, if let LUse::Alias(y, k) = u { LUse::Alias(self.bid(*y, *k), *k) } else { *u })
            })
            .collect();
        (bs, uses)
    }

    /// Versions the slots whose binding groups have disjoint types (or Lists of different elements), and solves the slot types; the bindings and uses by version.
    fn version<'b>(&mut self, hdr: Option<&Hdr>, g: &ver::Groups, bs: &[(Id, Bind<'b>)], uses: &[Use<'b>]) -> (Vec<(Id, Bind<'b>)>, Vec<(Id, LUse<'b>)>) {
        let Some(td) = self.cx.sound else { return self.by_version(bs, uses) };
        let h = &td.hier;
        let next = bs.iter().map(|b| b.0 + 1).chain(hdr.into_iter().flat_map(|hd| hd.params.iter().map(|p| p.0 + 1))).fold(self.vars.names.len(), usize::max);
        let cand: HashSet<Id> = g.of.iter().filter(|(x, gs)| gs.len() > 1 && !g.whole.contains(x)).map(|x| *x.0).collect();
        {
            let mut cv = self.cx.cover.borrow_mut();
            let mut n: HashMap<Id, usize> = HashMap::new();
            bs.iter().for_each(|b| *n.entry(b.0).or_default() += 1);
            hdr.into_iter().flat_map(|hd| hd.params.iter()).for_each(|p| *n.entry(p.0).or_default() += 1);
            cv.rebound[0].extend(n.iter().filter(|x| *x.1 > 1).map(|x| (self.key.clone(), self.name(*x.0))));
            cv.rebound[1].extend(cand.iter().map(|x| (self.key.clone(), self.name(*x))));
        }
        self.assign(g, &cand, next);
        let (vb, vu) = self.by_version(bs, uses);
        self.solve_t(hdr, &vb, &vu);
        let lists = |t: &T| t.members().iter().any(|m| matches!(m, T::List(_)));
        let apart = |a: &T, b: &T| !a.meets(h, b) || (lists(a) && lists(b) && list_el(h, a) != list_el(h, b));
        let split: HashSet<Id> = cand
            .into_iter()
            .filter(|x| {
                let ts: Vec<T> = self.vers[x].iter().map(|v| self.tenv.get(v).cloned().unwrap_or(T::Any)).collect();
                ts.iter().enumerate().any(|(i, a)| ts[i + 1..].iter().any(|b| apart(a, b)))
            })
            .collect();
        self.assign(g, &split, next);
        let mut cv = self.cx.cover.borrow_mut();
        for x in &split {
            cv.versioned.insert((self.key.clone(), self.name(*x)), self.vers[x].len());
        }
        drop(cv);
        let (vb, vu) = self.by_version(bs, uses);
        self.solve_t(hdr, &vb, &vu);
        (vb, vu)
    }

    /// The join of each versioned slot's versions, for a read of no known version.
    fn join_versions(&mut self) {
        let Some(td) = self.cx.sound else { return };
        for (x, vs) in &self.vers {
            let t = T::union(&td.hier, vs.iter().map(|v| self.tenv.get(v).cloned().unwrap_or(T::Any)));
            self.tenv.insert(self.joined[x], t);
        }
    }
}

/// The sound mode's narrowing (§2.4): one pass over the steps, no fixed point.
impl<'a, 'c> Alg<'a, 'c> {
    fn flow(&self) -> Flow {
        self.flow.borrow().clone()
    }

    fn set_flow(&self, f: Flow) {
        if self.cx.sound.is_some() {
            *self.flow.borrow_mut() = f;
        }
    }

    /// A slot's type on a path: narrowed, else the unit's.
    fn slot_t(&self, f: &Flow, x: Id) -> T {
        f.ts.get(&x).or_else(|| self.tenv.get(&x)).cloned().unwrap_or(T::Any)
    }

    /// `f` with slot `x` narrowed to `t`; a slot in `fixed` keeps the unit's type.
    fn with_t(&self, f: &Flow, x: Id, t: T) -> Flow {
        let mut g = f.clone();
        if t == T::Any || self.fixed.contains(&x) || self.tenv.get(&x) == Some(&t) {
            g.ts.remove(&x);
        } else {
            g.ts.insert(x, t);
        }
        g
    }

    /// `f` after `x` is assigned a value of type `t`, within the slot's; a List keeps the slot's elements.
    fn assigned(&self, f: &Flow, x: Id, t: T) -> Flow {
        let Some(td) = self.cx.sound else { return f.clone() };
        let h = &td.hier;
        let slot = self.tenv.get(&x).cloned().unwrap_or(T::Any);
        let t = t.within(h, &slot);
        let t = match slot.members().iter().find(|m| matches!(m, T::List(_))) {
            Some(l) if t != T::Any => T::union(h, t.members().iter().map(|m| if matches!(m, T::List(_)) { l.clone() } else { m.clone() })),
            _ => t,
        };
        let t = if t == T::never() { T::Any } else { t };
        let mut g = f.clone();
        g.ts.remove(&x);
        self.with_t(&g, x, t)
    }

    /// The flows reaching a join, slot by slot the join of their types; dead when none is live.
    fn join_flows(&self, fs: Vec<Flow>) -> Flow {
        let Some(td) = self.cx.sound else { return Flow::default() };
        let live: Vec<&Flow> = fs.iter().filter(|f| !f.dead).collect();
        let Some(first) = live.first() else { return Flow { dead: true, ..fs.first().cloned().unwrap_or_default() } };
        let ts = first.ts.iter().filter_map(|(x, t)| live[1..].iter().try_fold(t.clone(), |j, g| Some(j.join(&td.hier, g.ts.get(x)?))).map(|j| (*x, j))).collect();
        Flow { ts, dead: false }
    }

    /// Records a binding's value type (by `ver::key`) where it is bound.
    fn seen_bind(&self, k: usize, t: &T) {
        let Some(td) = self.cx.sound else { return };
        let mut m = self.bind_t.borrow_mut();
        let j = m.get(&k).map_or(t.clone(), |x| x.join(&td.hier, t));
        m.insert(k, j);
    }

    /// Whether a step here is a phrase algorithm's own, reached, in the real pass.
    fn counts(&self) -> bool {
        self.cx.sound.is_some() && self.cid.is_some() && !self.quiet.get() && !self.flow.borrow().dead
    }

    /// Joins a phrase algorithm's result type with `t`.
    fn ret_t(&self, t: T) {
        let (Some(td), Some(c)) = (self.cx.sound, self.cid) else { return };
        let mut f = self.cx.facts_out.borrow_mut();
        let j = f.rets.get(&c).map_or(t.clone(), |x| x.join(&td.hier, &t));
        f.rets.insert(c, j);
    }

    /// Records the parameters' narrowing at a normal return of an AO.
    fn exit(&self, f: &Flow) {
        let Some(td) = self.cx.sound else { return };
        if self.quiet.get() || f.dead || self.exit_ids.is_empty() {
            return;
        }
        let now: Vec<Option<T>> = self.exit_slots.iter().map(|s| s.and_then(|p| f.ts.get(&p).cloned())).collect();
        let mut e = self.exit_at.borrow_mut();
        *e = Some(match e.take() {
            None => now,
            Some(old) => old.into_iter().zip(now).map(|(a, b)| Some(a?.join(&td.hier, &b?))).collect(),
        });
    }

    /// `f` after a call returned normally (under `?`, `!`, or of no completion): its slot arguments by `Exits`.
    fn guarded(&self, f: &Flow, e: &Expr) -> Flow {
        let Some(td) = self.cx.sound else { return f.clone() };
        let (call, sure) = match strip(e) {
            Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) => (strip(x), true),
            x => (x, false),
        };
        let Expr::Call(Callee::Alg(c), xs) = call else { return f.clone() };
        let Some(ex) = self.cx.facts.exits.get(c) else { return f.clone() };
        let plain = self.cx.hdrs.get(c).and_then(|(h, _)| h.ret.as_ref()).map(|t| of_tyexpr(self.cx.d, &td.hier, t)).is_some_and(|r| r != T::Any && !r.members().iter().any(|m| *m == T::Abrupt));
        if !sure && !plain {
            return f.clone();
        }
        let mut g = f.clone();
        for (x, t) in xs.iter().zip(ex) {
            if let (r @ Expr::Var(v), Some(t)) = (strip(x), t) {
                let v = self.rid(r, *v);
                g = self.with_t(&g, v, narrow_used(&td.hier, &self.slot_t(&g, v), t));
            }
        }
        g
    }

    /// The slots a step or its nested steps may assign (`binds`, phrase steps' variable holes, and a completion's field set).
    fn writes(&self, st: &Stmt) -> HashSet<Id> {
        let mut bs = Vec::new();
        binds_at(Some(st), &[], self.closures, &mut bs, &mut HashSet::new());
        let mut w: HashSet<Id> = bs.into_iter().map(|b| b.0).collect();
        hole_vars(st, &mut w);
        let mut fs = HashSet::new();
        field_sets(st, &mut fs);
        w.extend(fs.into_iter().filter(|&x| self.all_ids(x).iter().any(|v| self.tenv.get(v).is_none_or(|t| t.members().iter().any(|m| matches!(m, T::Normal(_) | T::Abrupt | T::Any))))));
        w
    }

    /// `f` without the narrowing of the slots `st` may assign.
    fn killed(&self, f: &Flow, st: &Stmt) -> Flow {
        let mut g = f.clone();
        if self.cx.sound.is_some() && !g.ts.is_empty() {
            for x in self.writes(st) {
                for v in self.all_ids(x) {
                    g.ts.remove(&v);
                }
            }
        }
        g
    }

    /// The flow where `c` is true (`pos`) or false.
    fn branch(&self, c: &Cond, f: &Flow, pos: bool) -> Flow {
        if self.cx.sound.is_none() {
            return f.clone();
        }
        match c {
            Cond::Paren(c) => self.branch(c, f, pos),
            Cond::And(_, cs) | Cond::Or(_, cs) if matches!(c, Cond::And(..)) == pos => cs.iter().fold(f.clone(), |g, c| self.branch(c, &g, pos)),
            // one of them as `pos`, after the ones before it as `!pos`
            Cond::And(_, cs) | Cond::Or(_, cs) => {
                let mut g = f.clone();
                let mut ends = Vec::new();
                for c in cs {
                    ends.push(self.branch(c, &g, pos));
                    g = self.branch(c, &g, !pos);
                }
                self.join_flows(ends)
            }
            Cond::Preds(e, p, rest) => {
                if rest.windows(2).any(|w| w[0].0 != w[1].0) {
                    return f.clone();
                }
                let (mut t, mut fl) = (self.pred_n(e, p, f, true), self.pred_n(e, p, f, false));
                for (conj, q) in rest {
                    let (t2, f2) = match conj {
                        Conj::And => (self.pred_n(e, q, &t, true), self.join_flows(vec![fl, self.pred_n(e, q, &t, false)])),
                        Conj::Or => (self.join_flows(vec![t, self.pred_n(e, q, &fl, true)]), self.pred_n(e, q, &fl, false)),
                    };
                    (t, fl) = (t2, f2);
                }
                if pos { t } else { fl }
            }
            _ => f.clone(),
        }
    }

    /// The flow where predicate `p` of `e` holds (`pos`) or fails: `e` a slot, or a guard's call (`<emu-guard>`) on one.
    fn pred_n(&self, e: &Expr, p: &Pred, f: &Flow, pos: bool) -> Flow {
        let Some(td) = self.cx.sound else { return f.clone() };
        let (d, h) = (self.cx.d, &td.hier);
        match strip(e) {
            v @ Expr::Var(x) => {
                let x = &self.rid(v, *x);
                let t = self.slot_t(f, *x);
                // a test reads a built-in's parameter not passed (Missing) as *undefined*
                let missing = t.members().contains(&T::Missing);
                let used = |n: T, u: &T| if missing && T::Undefined.sub(h, u) { n.join(h, &T::Missing) } else { n };
                let failed = |cut: &dyn Fn(T) -> T| if missing && cut(T::Undefined) == T::never() { cut(t.clone()).without(h, &T::Missing) } else { cut(t.clone()) };
                let n = match p {
                    Pred::IsVal(neg, form, vs) => {
                        let ts: Vec<Option<T>> = vs.iter().map(|v| lit_t(strip(v))).collect();
                        if pos != (*neg != (*form == AltForm::Neither)) {
                            ts.into_iter().collect::<Option<Vec<T>>>().map(|ts| {
                                let u = T::union(h, ts);
                                used(t.within(h, &u), &u)
                            })
                        } else {
                            Some(failed(&|t| ts.iter().flatten().filter(|v| singleton(v)).fold(t, |t, v| minus(h, &t, v))))
                        }
                    }
                    Pred::IsTy(neg, form, tys) => {
                        if pos != (*neg != (*form == AltForm::Neither)) {
                            let u = T::union(h, tys.iter().map(|x| of_tyexpr(d, h, x)));
                            Some(used(t.within(h, &u), &u))
                        } else {
                            Some(failed(&|t| tys.iter().filter_map(|x| exact_t(d, h, x)).fold(t, |t, u| t.without(h, &u))))
                        }
                    }
                    Pred::Phrase(ph, hs) => match d.phrases.get(*ph).and_then(|x| x.meaning.as_ref()) {
                        Some(crate::decls::Meaning::Prim { prim, args, neg }) => {
                            let holds = pos != *neg;
                            match d.prims.name(*prim) {
                                "Present" if holds => Some(t.without(h, &T::union(h, [T::Absent, T::Missing]))),
                                "Present" => Some(t.within(h, &T::union(h, [T::Absent, T::Missing]))),
                                "HasSlot" if holds => self.slot_sort(args, hs).map(|o| t.within(h, &o)),
                                _ => None,
                            }
                        }
                        _ => None,
                    },
                };
                n.map_or_else(|| f.clone(), |n| self.with_t(f, *x, n))
            }
            // a guard's call, `? IsArray(x)` returning normally
            Expr::Q(y) | Expr::Bang(y) | Expr::BangAt(_, y) if matches!(strip(y), Expr::Call(..)) => self.pred_n(y, p, f, pos),
            Expr::Call(Callee::Alg(c), xs) => {
                let (Pred::IsVal(neg, form, vs), Some(x)) = (p, xs.first()) else { return f.clone() };
                let (r @ Expr::Var(x), [v]) = (strip(x), vs.as_slice()) else { return f.clone() };
                let x = &self.rid(r, *x);
                let yes = match strip(v) {
                    Expr::Val(ValLit::True) => true,
                    Expr::Val(ValLit::False) => false,
                    _ => return f.clone(),
                };
                // the call returned *true*
                if (pos != (*neg != (*form == AltForm::Neither))) != yes {
                    return f.clone();
                }
                let op = self.op(*c);
                match td.guards.iter().find(|g| g.0 == op) {
                    Some((_, t)) => self.with_t(f, *x, narrow_used(h, &self.slot_t(f, *x), t)),
                    None => f.clone(),
                }
            }
            _ => f.clone(),
        }
    }

    /// The object sort that alone declares the slot `has a [[X]] internal slot` names.
    fn slot_sort(&self, args: &[crate::decls::PArg], hs: &[Hole]) -> Option<T> {
        let td = self.cx.sound?;
        let crate::decls::PArg::Hole(i) = args.first()? else { return None };
        let f = match hs.get(*i)? {
            Hole::Field(f) | Hole::E(Expr::FieldName(f)) => *f,
            _ => return None,
        };
        let sorts: Vec<Option<Id>> = td.shapes.iter().filter(|s| s.slots && s.fields.iter().any(|x| x.0 == f)).map(|s| s.sort).collect();
        let [Some(s)] = sorts.as_slice() else { return None };
        match sort_t(self.cx.d, &td.hier, *s) {
            o @ T::Object(_) => Some(o),
            _ => None,
        }
    }
}

/// A slot of type `t` after a call that took it (`Val.used`) returned with its parameter within `u`: Missing stays where `u` admits *undefined*.
fn narrow_used(h: &Hier, t: &T, u: &T) -> T {
    let n = t.within(h, u);
    if t.members().contains(&T::Missing) && T::Undefined.sub(h, u) { n.join(h, &T::Missing) } else { n }
}

/// An expression without parentheses and annotations.
fn strip(e: &Expr) -> &Expr {
    match e {
        Expr::Paren(x) | Expr::Annot(_, x) => strip(x),
        e => e,
    }
}

/// A type of one value: *undefined*, *null*, one enum value.
fn singleton(t: &T) -> bool {
    matches!(t, T::Undefined | T::Null) || matches!(t, T::Enum(s) if s.len() == 1)
}

/// `t` without the one value `v` (`singleton`).
fn minus(h: &Hier, t: &T, v: &T) -> T {
    if *t == T::Any {
        return T::Any;
    }
    T::union(
        h,
        t.members().iter().filter_map(|m| match (m, v) {
            (T::Enum(s), T::Enum(e)) if !s.is_empty() => Some(T::Enum(s.difference(e).copied().collect())).filter(|x| *x != T::Enum(BTreeSet::new())),
            (m, v) if m == v => None,
            (m, _) => Some(m.clone()),
        }),
    )
}

/// A type test's type when every value of it passes the test, so that a failed test removes it.
fn exact_t(d: &Decls, h: &Hier, t: &TyExpr) -> Option<T> {
    match t {
        TyExpr::Sort(_, ms, s, _) if ms.is_empty() => {
            let named = matches!(
                d.sorts.name(*s),
                "Number" | "String" | "Boolean" | "Symbol" | "BigInt" | "undefined" | "Undefined" | "null" | "Null" | "Object" | "object" | "ECMAScript language value" | "property key" | "integer" | "mathematical value" | "extended mathematical value" | "List" | "Record" | "Parse Node" | "Abstract Closure" | "Completion Record" | "normal completion" | "abrupt completion"
            );
            let t = sort_t(d, h, *s);
            let own = match &t {
                T::Rec(Some(k)) => k == s,
                T::Object(b) => b.contains(s),
                _ => false,
            };
            (named || own).then_some(t)
        }
        TyExpr::Value(e) => lit_t(e).filter(singleton),
        TyExpr::Union(_, _, ts) => ts.iter().map(|x| exact_t(d, h, x)).collect::<Option<Vec<T>>>().map(|ts| T::union(h, ts)),
        _ => None,
    }
}

/// A step's nested steps: its bodies', readings' and fallback's.
fn sub_steps(st: &Stmt) -> Vec<&Stmt> {
    fn body<'s>(b: &'s Body, out: &mut Vec<&'s Stmt>) {
        match b {
            Body::Inline(s) => out.push(s),
            Body::Block(ns) => out.extend(ns.iter().map(|n| &n.stmt)),
        }
    }
    let mut out = Vec::new();
    match st {
        Stmt::If(_, b, arms, els) => {
            body(b, &mut out);
            arms.iter().chain(els.iter()).for_each(|a| body(&a.body, &mut out));
        }
        Stmt::IfElse(_, x, y) => out.extend([&**x, &**y]),
        Stmt::Repeat(ns) | Stmt::RepeatWhile(_, ns) | Stmt::RepeatUntil(_, ns) | Stmt::RepeatN(_, ns) => out.extend(ns.iter().map(|n| &n.stmt)),
        Stmt::ForEach(.., b) | Stmt::ForEachRec(.., b) | Stmt::ForSuchThat(.., b) | Stmt::ForKeys(.., b) | Stmt::ForIndex(.., b) | Stmt::ForChildren(_, b) | Stmt::ForChildrenOf(_, _, b) | Stmt::ForRange(.., b) => body(b, &mut out),
        Stmt::FindSuchThat(.., s) => out.push(s),
        Stmt::Readings(_, s, alts) => {
            out.push(s);
            out.extend(alts.iter().flat_map(|(_, ns)| ns.iter().map(|n| &n.stmt)));
        }
        Stmt::WithSteps(s, ns) => {
            out.push(s);
            out.extend(ns.iter().map(|n| &n.stmt));
        }
        _ => {}
    }
    out
}

/// The variables phrase and prose steps name, which they may assign (`Set _x_ to the string-concatenation of:`).
fn hole_vars(st: &Stmt, out: &mut HashSet<Id>) {
    match st {
        Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => out.extend(hs.iter().filter_map(|h| if let Hole::E(Expr::Var(x)) = h { Some(*x) } else { None })),
        Stmt::Prose(_, ps) => out.extend(ps.iter().filter_map(|p| if let Part::Hole(Hole::E(Expr::Var(x))) = p { Some(*x) } else { None })),
        _ => {}
    }
    sub_steps(st).into_iter().for_each(|s| hole_vars(s, out));
}

/// The slots whose field a step or its nested steps set (`Set _x_.[[F]] to …`).
fn field_sets(st: &Stmt, out: &mut HashSet<Id>) {
    if let Stmt::Set(Place::Field(b, _), _) = st {
        if let Expr::Var(x) = strip(b) {
            out.insert(*x);
        }
    }
    sub_steps(st).into_iter().for_each(|s| field_sets(s, out));
}

/// A use of a slot's List: an element added, passed, returned, stored, or kept where its elements are unknown.
#[derive(Clone, Copy, Debug)]
enum LUse<'a> {
    /// an element, and whether a List step adds it (a checked site)
    Add(&'a Expr, bool),
    AddAll(&'a Expr),
    Arg(Id, usize),
    SdoArg(Id, usize),
    Ret,
    /// assigned to another slot (by the binding of that key), which then holds the same List
    Alias(Id, usize),
    /// stored in a field of a Record of a kind, or of the base expression's type
    Field(Option<Id>, Id),
    FieldOf(&'a Expr, Id),
    Escape,
}

/// The primitives that read a List and keep no reference to it.
const LIST_READS: &[&str] = &["ListLen", "Contains", "ListElem", "IsEmpty", "SameLength", "ListFind", "Count", "Copy", "ListConcat", "RemoveElem", "RemoveFirst", "RemoveLast", "Reverse", "HasSlots", "CodePoints", "StrOfUnits", "string-concatenation", "StoreBytes"];

/// A List step's added element and its List: Append, Prepend, Insert, Add (`SetAdd`), and Replace's new element.
fn list_add<'e>(d: &Decls, p: Id, hs: &'e [Hole]) -> Option<(&'e Expr, &'e Expr)> {
    let Some(crate::decls::Meaning::Prim { prim, args, .. }) = d.phrases.get(p).and_then(|x| x.meaning.as_ref()) else { return None };
    let hole = |k: usize| match args.get(k)? {
        crate::decls::PArg::Hole(i) => match hs.get(*i)? {
            Hole::E(e) => Some(e),
            _ => None,
        },
        _ => None,
    };
    match d.prims.name(*prim) {
        "Append" | "Prepend" | "Insert" | "SetAdd" => Some((hole(0)?, hole(1)?)),
        "ReplaceElem" => Some((hole(2)?, hole(0)?)),
        _ => None,
    }
}

/// Each phrase algorithm's clause and its parameter count: a phrase's holes are its arguments.
type Arity = HashMap<Id, usize>;

/// A slot's List use, and the address of the read it is at (0: none).
type Use<'a> = (Id, LUse<'a>, usize);

/// The List uses of the slots in steps `ns` and in the closures.
fn list_uses<'a>(d: &Decls, ar: &Arity, ns: &'a [Node], closures: &'a [CloLit]) -> Vec<Use<'a>> {
    /// A phrase's holes: an algorithm's arguments, else read or kept as `phrase_at` says.
    fn phrase<'a>(d: &Decls, ar: &Arity, p: Id, hs: &'a [Hole], out: &mut Vec<Use<'a>>) {
        match d.phrases.get(p).and_then(|x| x.meaning.as_ref()) {
            Some(crate::decls::Meaning::Alg(c)) if ar.get(c) == Some(&hs.len()) => {
                for (k, h) in hs.iter().enumerate() {
                    match h {
                        Hole::E(x) => e(d, ar, x, Some(LUse::Arg(*c, k)), out),
                        h => holes(d, ar, std::slice::from_ref(h), Some(LUse::Escape), out),
                    }
                }
            }
            _ => holes(d, ar, hs, phrase_at(d, p), out),
        }
    }
    fn e<'a>(d: &Decls, ar: &Arity, x: &'a Expr, at: Option<LUse<'a>>, out: &mut Vec<Use<'a>>) {
        let esc = Some(LUse::Escape);
        match x {
            Expr::Var(v) => out.extend(at.map(|u| (*v, u, ver::addr(x)))),
            Expr::Paren(y) | Expr::Annot(_, y) | Expr::Erratum(_, _, y) | Expr::Q(y) | Expr::Bang(y) | Expr::BangAt(_, y) => e(d, ar, y, at, out),
            Expr::Call(Callee::Alg(c), xs) => xs.iter().enumerate().for_each(|(k, y)| e(d, ar, y, Some(LUse::Arg(*c, k)), out)),
            Expr::Call(Callee::Prim(p), xs) => {
                let at = if LIST_READS.contains(&d.prims.name(*p)) { None } else { esc };
                xs.iter().for_each(|y| e(d, ar, y, at, out));
            }
            Expr::Sdo(s, _, y, xs) => {
                e(d, ar, y, None, out);
                xs.iter().enumerate().for_each(|(k, z)| e(d, ar, z, Some(LUse::SdoArg(*s, k)), out));
            }
            Expr::IMethod(y, _, xs) | Expr::CMethod(y, _, xs) | Expr::Apply(y, xs) => {
                e(d, ar, y, None, out);
                xs.iter().for_each(|z| e(d, ar, z, esc, out));
            }
            Expr::Index(y, z) | Expr::Bin(_, y, z) => {
                e(d, ar, y, None, out);
                e(d, ar, z, None, out);
            }
            Expr::Field(y, _) | Expr::Component(_, _, y) | Expr::Neg(y) => e(d, ar, y, None, out),
            Expr::List(xs) => xs.iter().for_each(|y| e(d, ar, y, esc, out)),
            Expr::Record(_, k, fs) => fs.iter().for_each(|(f, y)| e(d, ar, y, Some(LUse::Field(*k, *f)), out)),
            Expr::Phrase(p, hs) => phrase(d, ar, *p, hs, out),
            Expr::Extreme(_, _, _, c) => cond(d, ar, c, out),
            Expr::TableStep(_, y, z) => {
                e(d, ar, y, esc, out);
                e(d, ar, z, esc, out);
            }
            Expr::Definition(y, _) | Expr::Table(_, y) | Expr::ResumedWith(y) | Expr::ChildOf(y, _, _) => e(d, ar, y, esc, out),
            Expr::Prose(_, ps) => parts(d, ar, ps, esc, out),
            _ => {}
        }
    }
    /// A phrase's holes keep no reference to a List read by a primitive in `LIST_READS`.
    fn phrase_at<'a>(d: &Decls, p: Id) -> Option<LUse<'a>> {
        match d.phrases.get(p).and_then(|x| x.meaning.as_ref()) {
            Some(crate::decls::Meaning::Prim { prim, .. }) if LIST_READS.contains(&d.prims.name(*prim)) => None,
            _ => Some(LUse::Escape),
        }
    }
    fn holes<'a>(d: &Decls, ar: &Arity, hs: &'a [Hole], at: Option<LUse<'a>>, out: &mut Vec<Use<'a>>) {
        for h in hs {
            match h {
                Hole::E(x) => e(d, ar, x, at, out),
                Hole::L(_, xs) => xs.iter().for_each(|x| e(d, ar, x, at, out)),
                Hole::C(c) | Hole::Bc(_, c) => cond(d, ar, c, out),
                _ => {}
            }
        }
    }
    fn parts<'a>(d: &Decls, ar: &Arity, ps: &'a [Part], at: Option<LUse<'a>>, out: &mut Vec<Use<'a>>) {
        for p in ps {
            if let Part::Hole(h) = p {
                holes(d, ar, std::slice::from_ref(h), at, out);
            }
        }
    }
    fn cond<'a>(d: &Decls, ar: &Arity, c: &'a Cond, out: &mut Vec<Use<'a>>) {
        match c {
            Cond::Preds(x, p, r) => {
                e(d, ar, x, None, out);
                for p in std::iter::once(p).chain(r.iter().map(|x| &x.1)) {
                    match p {
                        Pred::IsVal(_, _, xs) => xs.iter().for_each(|y| e(d, ar, y, None, out)),
                        Pred::Phrase(_, hs) => holes(d, ar, hs, None, out),
                        Pred::IsTy(..) => {}
                    }
                }
            }
            Cond::Rel(_, x, y) => {
                e(d, ar, x, None, out);
                e(d, ar, y, None, out);
            }
            Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().for_each(|c| cond(d, ar, c, out)),
            Cond::Paren(c) => cond(d, ar, c, out),
            Cond::Phrase(_, hs) => holes(d, ar, hs, None, out),
            Cond::Prose(_, ps) => parts(d, ar, ps, None, out),
            Cond::Alg(..) => {}
        }
    }
    fn stmt<'a>(d: &Decls, ar: &Arity, s: &'a Stmt, out: &mut Vec<Use<'a>>) {
        let esc = Some(LUse::Escape);
        match s {
            Stmt::Let(y, x) | Stmt::Set(Place::Var(y), x) => e(d, ar, x, Some(LUse::Alias(*y, ver::addr(x))), out),
            Stmt::ThrowVal(x) | Stmt::Suspend(x, _) | Stmt::Push(x, _) | Stmt::Remove(x, _) => e(d, ar, x, esc, out),
            Stmt::Set(Place::Field(b, f), x) => {
                e(d, ar, b, None, out);
                e(d, ar, x, Some(LUse::FieldOf(b, *f)), out);
            }
            Stmt::Set(Place::Expr(p), x) => {
                if let Expr::Index(l, i) = strip(p) {
                    if let Expr::Var(v) = strip(l) {
                        out.push((*v, LUse::Add(x, false), ver::addr(strip(l))));
                    }
                    e(d, ar, l, None, out);
                    e(d, ar, i, None, out);
                } else {
                    e(d, ar, p, esc, out);
                }
                e(d, ar, x, esc, out);
            }
            Stmt::Ret(Some(x)) | Stmt::RetSee(x, _) => e(d, ar, x, Some(LUse::Ret), out),
            Stmt::Perform(x) | Stmt::RepeatN(x, _) | Stmt::ForEach(_, _, x, _, _) | Stmt::ForEachRec(_, _, x, _) | Stmt::ForIndex(_, x, _) | Stmt::ForChildrenOf(_, x, _) => e(d, ar, x, None, out),
            Stmt::ForRange(_, lo, _, hi, _, _, _) => {
                e(d, ar, lo, None, out);
                e(d, ar, hi, None, out);
            }
            Stmt::If(c, ..) | Stmt::IfElse(c, ..) | Stmt::Assert(c) | Stmt::AssertAt(_, c) | Stmt::RepeatWhile(c, _) | Stmt::RepeatUntil(c, _) | Stmt::ForSuchThat(_, _, c, _, _) | Stmt::FindSuchThat(_, _, c, _, _) => cond(d, ar, c, out),
            Stmt::AssertIf(c, x) => {
                cond(d, ar, c, out);
                cond(d, ar, x, out);
            }
            Stmt::ForKeys(_, o, c, _, _) => {
                e(d, ar, o, None, out);
                cond(d, ar, c, out);
            }
            Stmt::LetSuchThat(_, c, os) => {
                cond(d, ar, c, out);
                os.iter().for_each(|(_, x)| e(d, ar, x, None, out));
            }
            Stmt::SyntaxError(_, c, u) => {
                cond(d, ar, c, out);
                if let Some((_, u)) = u {
                    cond(d, ar, u, out);
                }
            }
            Stmt::Macro(_, xs) => xs.iter().for_each(|x| e(d, ar, x, esc, out)),
            Stmt::RemoveRestore(x, y) | Stmt::Resume(x, y) | Stmt::SetCodeState(x, y) | Stmt::ResumeLet(x, y, _, _) => {
                e(d, ar, x, esc, out);
                e(d, ar, y, esc, out);
            }
            Stmt::Mutate(p, hs) | Stmt::Phrase(p, hs) => match list_add(d, *p, hs) {
                Some((el, l)) => {
                    if let Expr::Var(v) = strip(l) {
                        out.push((*v, LUse::Add(el, true), ver::addr(strip(l))));
                    }
                    e(d, ar, el, esc, out);
                    hs.iter().filter_map(|h| if let Hole::E(x) = h { Some(x) } else { None }).filter(|x| !std::ptr::eq(*x, el)).for_each(|x| e(d, ar, x, None, out));
                }
                None if d.phrases.get(*p).is_some_and(|x| x.name == "ph-append-elements") => {
                    if let (Some(Hole::E(a)), Some(Hole::E(b))) = (hs.first(), hs.get(1)) {
                        if let Expr::Var(v) = strip(b) {
                            out.push((*v, LUse::AddAll(a), ver::addr(strip(b))));
                        }
                        e(d, ar, a, None, out);
                        e(d, ar, b, None, out);
                    }
                }
                None => phrase(d, ar, *p, hs, out),
            },
            Stmt::Prose(_, ps) | Stmt::Note(ps) => parts(d, ar, ps, esc, out),
            _ => {}
        }
        sub_steps(s).into_iter().for_each(|s| stmt(d, ar, s, out));
    }
    let mut out = Vec::new();
    for n in ns.iter().chain(closures.iter().flat_map(|c| c.body.iter())) {
        stmt(d, ar, &n.stmt, &mut out);
    }
    out
}

/// Two sets of element types an add must meet, as one.
fn els_join(a: Option<(Vec<T>, bool)>, (mut ts, open): (Vec<T>, bool)) -> (Vec<T>, bool) {
    let Some((us, o)) = a else { return (ts, open) };
    ts.extend(us);
    ts.sort();
    ts.dedup();
    (ts, open || o)
}

/// The elements of a type's List members: never if it has none, any if it is unknown.
fn list_el(h: &Hier, t: &T) -> T {
    if *t == T::Any {
        return T::Any;
    }
    T::union(h, t.members().iter().filter_map(|m| if let T::List(e) = m { Some((**e).clone()) } else { None }))
}

/// A List element's type (an index, a loop's variable): any where the type has no List member.
fn elem_t(h: &Hier, t: &T) -> T {
    match list_el(h, t) {
        T::Union(ms) if ms.is_empty() && !t.members().is_empty() && !t.members().iter().any(|m| matches!(m, T::List(_))) => T::Any,
        el => el,
    }
}

/// `t` with elements of type `el` added to its List members.
fn with_els(h: &Hier, t: &T, el: &T) -> T {
    if *t == T::Any || *el == T::never() {
        return t.clone();
    }
    T::union(h, t.members().iter().map(|m| match m {
        T::List(e) => T::List(Box::new(e.join(h, el))),
        m => m.clone(),
    }))
}

/// What a callee's parameter `k` may add to a List passed for it: its type's List elements, any if unknown.
fn param_el(d: &Decls, h: &Hier, hd: &Hdr, k: usize) -> T {
    match hd.params.get(k) {
        Some((_, Some(t), _, false)) => list_el(h, &of_tyexpr(d, h, t)),
        _ => T::Any,
    }
}

/// A new List: a literal, an empty List, a concatenation, a copy, a List of one element.
fn fresh(d: &Decls, e: &Expr) -> bool {
    match strip(e) {
        Expr::List(_) => true,
        Expr::Phrase(p, _) => matches!(d.phrases.get(*p).and_then(|x| x.meaning.as_ref()), Some(crate::decls::Meaning::Prim { prim, neg: false, .. }) if matches!(d.prims.name(*prim), "ListNew" | "ListConcat" | "Copy" | "ListOf1")),
        _ => false,
    }
}

/// The List parameters (clause, index) a callee only reads or passes to such a parameter, to a fixed point.
fn read_only_params(d: &Decls, ar: &Arity, units: &[(Id, &Hdr, &[Node], &[CloLit])]) -> HashSet<(Id, usize)> {
    let mut ro: HashSet<(Id, usize)> = HashSet::new();
    let mut bad: HashSet<(Id, usize)> = HashSet::new();
    let mut edges: Vec<((Id, usize), (Id, usize))> = Vec::new();
    for (c, hd, body, closures) in units {
        let slot_k: HashMap<Id, usize> = hd.params.iter().enumerate().filter(|(_, p)| !p.3).map(|(k, p)| (p.0, k)).collect();
        ro.extend(slot_k.values().map(|&k| (*c, k)));
        for (x, u, _) in list_uses(d, ar, body, closures) {
            let Some(&k) = slot_k.get(&x) else { continue };
            match u {
                LUse::Arg(c2, k2) => edges.push(((*c, k), (c2, k2))),
                _ => {
                    bad.insert((*c, k));
                }
            }
        }
    }
    ro.retain(|p| !bad.contains(p));
    loop {
        let n = ro.len();
        let gone: Vec<(Id, usize)> = edges.iter().filter(|(a, b)| ro.contains(a) && !ro.contains(b)).map(|e| e.0).collect();
        ro.retain(|p| !gone.contains(p));
        if ro.len() == n {
            return ro;
        }
    }
}

/// The trait method named `m` whose trait's root the receiver type meets, else the first of that name.
fn trait_method<'t>(d: &Decls, td: &'t TyDecls, recv: &T, m: SigName) -> Option<(&'t crate::tydecls::Trait, &'t crate::tydecls::Method)> {
    let cands: Vec<_> = td.traits.iter().flat_map(|t| t.methods.iter().filter(move |x| x.name == m).map(move |x| (t, x))).collect();
    cands.iter().find(|(t, _)| t.root.is_some_and(|r| recv.meets(&td.hier, &sort_t(d, &td.hier, r)))).or(cands.first()).copied()
}

fn rel_word(o: RelOp) -> &'static str {
    match o {
        RelOp::Lt => "<",
        RelOp::Le => "≤",
        RelOp::Gt => ">",
        RelOp::Ge => "≥",
        RelOp::Eq => "=",
        RelOp::Ne => "≠",
    }
}

/// Every binding of a variable in steps, their closures' and their readings'.
fn binds<'a>(ns: &'a [Node], closures: &'a [CloLit], out: &mut Vec<(Id, Bind<'a>)>, seen: &mut HashSet<usize>) {
    binds_at(None, ns, closures, out, seen)
}

/// The bindings of a step, if any, then of steps `ns`, with the closures they define.
fn binds_at<'a>(first: Option<&'a Stmt>, ns: &'a [Node], closures: &'a [CloLit], out: &mut Vec<(Id, Bind<'a>)>, seen: &mut HashSet<usize>) {
    fn holes<'a>(hs: &'a [Hole], out: &mut Vec<(Id, Bind<'a>)>) {
        for h in hs {
            match h {
                Hole::B(x) => out.push((*x, Bind::T(Ty::top()))),
                Hole::Bc(xs, _) => out.extend(xs.iter().map(|x| (*x, Bind::T(Ty::top())))),
                _ => {}
            }
        }
    }
    fn cond<'a>(c: &'a Cond, out: &mut Vec<(Id, Bind<'a>)>) {
        match c {
            Cond::Preds(_, p, r) => {
                for p in std::iter::once(p).chain(r.iter().map(|x| &x.1)) {
                    if let Pred::Phrase(_, hs) = p {
                        holes(hs, out);
                    }
                }
            }
            Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().for_each(|c| cond(c, out)),
            Cond::Paren(c) => cond(c, out),
            Cond::Phrase(_, hs) => holes(hs, out),
            _ => {}
        }
    }
    fn exprs<'a>(e: &'a Expr, out: &mut Vec<(Id, Bind<'a>)>, ks: &mut Vec<usize>) {
        match e {
            Expr::Closure(k) => ks.push(*k),
            Expr::Extreme(_, x, t, c) => {
                out.push((*x, Bind::H(t)));
                cond(c, out);
            }
            Expr::Phrase(_, hs) => {
                holes(hs, out);
                hs.iter().for_each(|h| if let Hole::E(x) = h { exprs(x, out, ks) });
            }
            Expr::Call(_, xs) | Expr::List(xs) => xs.iter().for_each(|x| exprs(x, out, ks)),
            Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
                exprs(x, out, ks);
                xs.iter().for_each(|x| exprs(x, out, ks));
            }
            Expr::Component(_, _, x) | Expr::Field(x, _) | Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) | Expr::Erratum(_, _, x) | Expr::Neg(x) | Expr::Paren(x) | Expr::Annot(_, x) => exprs(x, out, ks),
            Expr::Index(x, y) | Expr::Bin(_, x, y) => {
                exprs(x, out, ks);
                exprs(y, out, ks);
            }
            Expr::Record(_, _, fs) => fs.iter().for_each(|(_, x)| exprs(x, out, ks)),
            _ => {}
        }
    }
    fn body<'a>(b: &'a Body, out: &mut Vec<(Id, Bind<'a>)>, ks: &mut Vec<usize>, ns: &mut Vec<&'a [Node]>) {
        match b {
            Body::Inline(s) => stmt(s, out, ks, ns),
            Body::Block(b) => ns.push(b),
        }
    }
    fn stmt<'a>(s: &'a Stmt, out: &mut Vec<(Id, Bind<'a>)>, ks: &mut Vec<usize>, ns: &mut Vec<&'a [Node]>) {
        let mut all = |e: &'a Expr, out: &mut Vec<(Id, Bind<'a>)>| exprs(e, out, ks);
        match s {
            Stmt::Let(x, e) => {
                out.push((*x, Bind::E(e)));
                all(e, out);
            }
            Stmt::Set(p, e) => {
                if let Place::Var(x) = p {
                    out.push((*x, Bind::E(e)));
                }
                all(e, out);
            }
            Stmt::Ret(Some(e)) | Stmt::Perform(e) | Stmt::ThrowVal(e) | Stmt::RetSee(e, _) => all(e, out),
            Stmt::If(c, b, arms, els) => {
                cond(c, out);
                body(b, out, ks, ns);
                for a in arms.iter().chain(els.iter()) {
                    if let Some(c) = &a.cond {
                        cond(c, out);
                    }
                    body(&a.body, out, ks, ns);
                }
            }
            Stmt::IfElse(c, x, y) => {
                cond(c, out);
                stmt(x, out, ks, ns);
                stmt(y, out, ks, ns);
            }
            Stmt::Repeat(b) | Stmt::RepeatWhile(_, b) | Stmt::RepeatUntil(_, b) | Stmt::RepeatN(_, b) => ns.push(b),
            Stmt::ForEach(x, t, l, _, b) => {
                out.push((*x, t.as_ref().map_or(Bind::El(l), |t| Bind::H(t))));
                all(l, out);
                body(b, out, ks, ns);
            }
            Stmt::ForEachRec(_, x, l, b) => {
                out.push((*x, Bind::El(l)));
                all(l, out);
                body(b, out, ks, ns);
            }
            Stmt::ForSuchThat(x, t, c, _, b) => {
                out.push((*x, Bind::H(t)));
                cond(c, out);
                body(b, out, ks, ns);
            }
            Stmt::ForKeys(x, _, c, _, b) => {
                out.push((*x, Bind::T(Ty::val(STR | SYM))));
                cond(c, out);
                body(b, out, ks, ns);
            }
            Stmt::ForIndex(x, _, b) | Stmt::ForRange(x, _, _, _, _, _, b) => {
                out.push((*x, Bind::T(Ty::val(MATH))));
                body(b, out, ks, ns);
            }
            Stmt::ForChildren(x, b) | Stmt::ForChildrenOf(x, _, b) => {
                out.push((*x, Bind::T(Ty::val(NODE | OTHER))));
                body(b, out, ks, ns);
            }
            Stmt::FindSuchThat(x, t, c, _, s) => {
                out.push((*x, Bind::H(t)));
                cond(c, out);
                stmt(s, out, ks, ns);
            }
            Stmt::LetSuchThat(xs, c, _) => {
                out.extend(xs.iter().map(|x| (*x, Bind::T(Ty::val(MATH)))));
                cond(c, out);
            }
            Stmt::ResumeLet(_, _, x, _) => out.push((*x, Bind::T(Ty::top()))),
            Stmt::Macro(_, xs) => {
                if let Some(e @ Expr::Var(x)) = xs.first() {
                    out.push((*x, Bind::Unwrap(e)));
                }
            }
            Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => {
                holes(hs, out);
                hs.iter().for_each(|h| if let Hole::E(x) = h { all(x, out) });
            }
            // prose may bind the variables it names
            Stmt::Prose(_, ps) => {
                for p in ps {
                    if let Part::Hole(Hole::E(Expr::Var(x))) = p {
                        out.push((*x, Bind::T(Ty::top())));
                    }
                }
            }
            Stmt::Readings(_, s, alts) => {
                stmt(s, out, ks, ns);
                ns.extend(alts.iter().map(|(_, b)| b.as_slice()));
            }
            Stmt::WithSteps(s, b) => {
                stmt(s, out, ks, ns);
                ns.push(b);
            }
            Stmt::Assert(c) => cond(c, out),
            _ => {}
        }
    }
    fn one<'a>(s: &'a Stmt, closures: &'a [CloLit], out: &mut Vec<(Id, Bind<'a>)>, work: &mut Vec<&'a [Node]>, seen: &mut HashSet<usize>) {
        let mut ks = Vec::new();
        stmt(s, out, &mut ks, work);
        for k in ks {
            if let Some(c) = closures.get(k).filter(|_| seen.insert(k)) {
                out.extend(c.params.iter().flatten().chain(c.caps.iter()).map(|x| (*x, Bind::T(Ty::top()))));
                if let Some((a, b, c)) = c.frame {
                    out.extend([a, b, c].map(|x| (x, Bind::T(Ty::top()))));
                }
                work.push(&c.body);
            }
        }
    }
    let mut work: Vec<&'a [Node]> = vec![ns];
    if let Some(s) = first {
        one(s, closures, out, &mut work, seen);
    }
    while let Some(ns) = work.pop() {
        for n in ns {
            one(&n.stmt, closures, out, &mut work, seen);
        }
    }
}

/// The closures a statement's own expressions define, by index in the closure table.
fn own_closures(st: &Stmt) -> Vec<usize> {
    fn e(x: &Expr, ks: &mut Vec<usize>) {
        match x {
            Expr::Closure(k) => ks.push(*k),
            Expr::Call(_, xs) | Expr::List(xs) => xs.iter().for_each(|x| e(x, ks)),
            Expr::Sdo(_, _, x, xs) | Expr::IMethod(x, _, xs) | Expr::CMethod(x, _, xs) | Expr::Apply(x, xs) => {
                e(x, ks);
                xs.iter().for_each(|x| e(x, ks));
            }
            Expr::Q(x) | Expr::Bang(x) | Expr::BangAt(_, x) | Expr::Erratum(_, _, x) | Expr::Paren(x) | Expr::Annot(_, x) => e(x, ks),
            Expr::Phrase(_, hs) => hs.iter().for_each(|h| if let Hole::E(x) = h { e(x, ks) }),
            _ => {}
        }
    }
    let mut ks = Vec::new();
    match st {
        Stmt::Let(_, x) | Stmt::Perform(x) | Stmt::Set(_, x) | Stmt::Ret(Some(x)) => e(x, &mut ks),
        Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => hs.iter().for_each(|h| if let Hole::E(x) = h { e(x, &mut ks) }),
        _ => {}
    }
    ks
}

type At<'o> = Option<(&'o str, &'o mut Vec<Finding>)>;

impl<'a, 'c> Alg<'a, 'c> {
    /// The variables' sorts: the header's, joined with every binding's, to a fixed point.
    fn solve(&mut self, hdr: Option<&Hdr>, bs: &[(Id, Bind)]) {
        let d = self.cx.d;
        let mut base: Env = HashMap::new();
        if let Some(h) = hdr {
            // a built-in's parameter is Opt<LangValue>: an argument not passed is not present (spec.html:30367)
            let builtin = h.kind == "builtin";
            for (slot, t, opt, rest) in &h.params {
                let mut ty = match (rest, t) {
                    (true, _) => Ty::list(Atoms::top()),
                    (false, Some(t)) => of_ty(d, t),
                    (false, None) if builtin => Ty::val(LANG),
                    (false, None) => Ty::top(),
                };
                if *opt || (builtin && !rest) {
                    ty.v.join(&Atoms::of(ABSENT));
                }
                base.entry(*slot).or_default().join(&ty);
            }
            if let Some((slot, t)) = &h.recv {
                base.entry(*slot).or_default().join(&of_ty(d, t));
            }
        }
        self.bound = base.keys().copied().chain(bs.iter().map(|b| b.0)).collect();
        let mut env = base.clone();
        for (x, _) in bs {
            env.entry(*x).or_default();
        }
        self.env = env;
        let mut done = false;
        for _ in 0..12 {
            let mut next = base.clone();
            for (x, b) in bs {
                let t = match b {
                    Bind::E(e) => self.ty(e, None),
                    Bind::T(t) => t.clone(),
                    Bind::Unwrap(x) => self.ty(x, None).unwrapped(),
                    Bind::H(t) => of_ty(d, t),
                    Bind::El(l) => {
                        let lt = self.ty(l, None);
                        if lt.is_empty() {
                            Ty::default()
                        } else if lt.v.bits & LIST != 0 && lt.el.bits != 0 && !lt.el.is_top() {
                            Ty { v: lt.el.clone(), el: Atoms::top(), ..Ty::default() }
                        } else {
                            Ty::top()
                        }
                    }
                };
                next.entry(*x).or_default().join(&t);
            }
            if next == self.env {
                done = true;
                break;
            }
            self.env = next;
        }
        for t in self.env.values_mut() {
            if !done || t.is_empty() {
                *t = Ty::top();
            }
        }
        // why each variable of any value is: its parameter's type, or its first binding of any value
        let mut why: HashMap<Id, String> = HashMap::new();
        if let Some(h) = hdr {
            for (slot, t, _, rest) in &h.params {
                if !*rest && self.env.get(slot).is_some_and(|t| t.v.is_top()) {
                    why.insert(*slot, t.as_ref().map_or_else(|| "parameter: untyped".to_string(), |t| format!("parameter: {}", ty_why(d, t))));
                }
            }
            if let Some((slot, t)) = &h.recv {
                why.insert(*slot, format!("receiver: {}", ty_why(d, t)));
            }
        }
        if !done {
            for x in self.env.keys() {
                why.entry(*x).or_insert_with(|| "no fixed point".into());
            }
        }
        for _ in 0..2 {
            self.why = why.clone();
            for (x, b) in bs {
                if why.contains_key(x) || !self.env.get(x).is_some_and(|t| t.v.is_top()) {
                    continue;
                }
                let w = match b {
                    Bind::E(e) if self.ty(e, None).v.is_top() => format!("bound to {}", self.cause(e)),
                    Bind::T(t) if t.v.is_top() => "binder: phrase hole, closure parameter or capture, resumption".into(),
                    Bind::Unwrap(_) => "unwrapped completion".into(),
                    Bind::H(t) if of_ty(d, t).v.is_top() => format!("declared {}", ty_why(d, t)),
                    Bind::El(l) if self.ty(l, None).el.is_top() => format!("element of a List of any value ({})", self.cause_list(l)),
                    _ => continue,
                };
                why.insert(*x, w);
            }
        }
        self.why = why;
        // variables whose bindings' sorts are disjoint: a flow-insensitive slot type is their union
        let mut per: HashMap<Id, Vec<Ty>> = HashMap::new();
        for (x, b) in bs {
            let t = match b {
                Bind::E(e) => self.ty(e, None),
                Bind::T(t) => t.clone(),
                Bind::Unwrap(x) => self.ty(x, None).unwrapped(),
                Bind::H(t) => of_ty(d, t),
                Bind::El(_) => continue,
            };
            per.entry(*x).or_default().push(t);
        }
        if let Some(h) = hdr {
            for (slot, t, _, _) in &h.params {
                if let Some(t) = t {
                    per.entry(*slot).or_default().push(of_ty(d, t));
                }
            }
        }
        let mut cv = self.cx.cover.borrow_mut();
        for ts in per.values().filter(|ts| ts.len() > 1) {
            cv.retyped[0] += 1;
            let known: Vec<&Ty> = ts.iter().filter(|t| !t.is_empty() && !t.v.is_top() && !(t.v.bits == 0 && t.n.is_top())).collect();
            if known.iter().enumerate().any(|(i, a)| known[i + 1..].iter().any(|b| !a.meets(b))) {
                cv.retyped[1] += 1;
                if known.iter().any(|t| t.only_comp()) && known.iter().any(|t| !t.comp()) {
                    cv.retyped[2] += 1;
                }
            }
        }
    }

    /// Why a List's elements are any value.
    fn cause_list(&self, l: &Expr) -> String {
        match l {
            Expr::Var(x) => format!("variable: {}", self.why.get(x).map_or("its bindings", String::as_str)),
            e => self.cause(e),
        }
    }

    fn nodes(&self, ns: &[Node], d: usize, pre: &str, ret: Option<&Ty>, out: &mut Vec<Finding>) {
        let mut i = 1;
        for n in ns {
            self.node(n, d, pre, i, ret, out);
            i += crate::asserts::width(n);
        }
    }

    fn node(&self, n: &Node, d: usize, pre: &str, i: usize, ret: Option<&Ty>, out: &mut Vec<Finding>) {
        let at = |k: usize| format!("{pre}{}", crate::asserts::label(d, k));
        let (st, rd) = match &n.stmt {
            Stmt::Readings(e, s, alts) => (&**s, Some((*e, alts))),
            s => (s, None),
        };
        // a definition reading's pinned step is never run
        let pinned = !rd.is_some_and(|(_, alts)| alts.iter().any(|(r, _)| *r == crate::ast::Reading::Definition));
        let f0 = self.flow();
        let mut ends = Vec::new();
        if !pinned {
        } else if let Stmt::If(c, b, arms, els) = st {
            self.if_steps(c, b, arms, els, d, &at(i), &|k| at(i + 1 + k), ret, out);
            ends.push(self.flow());
        } else {
            self.stmt(st, d, &at(i), ret, out);
            ends.push(self.flow());
        }
        if let Some((e, alts)) = rd {
            self.set_flow(f0.clone());
            ends.extend(self.alts(e, &at(i), alts, ret, out));
            self.set_flow(if ends.is_empty() { f0 } else { self.join_flows(ends) });
        }
    }

    /// An If's condition and arms (`arm_path`: each further arm's step), then the join of the arms' ends.
    #[allow(clippy::too_many_arguments)]
    fn if_steps(&self, c: &Cond, b: &Body, arms: &[Arm], els: &Option<Arm>, d: usize, path: &str, arm_path: &dyn Fn(usize) -> String, ret: Option<&Ty>, out: &mut Vec<Finding>) {
        let f0 = self.flow();
        self.cond(c, &mut Some((path, &mut *out)));
        let mut rest = self.branch(c, &f0, false);
        self.set_flow(self.branch(c, &f0, true));
        self.body(b, d, path, ret, out);
        let mut ends = vec![self.flow()];
        for (k, a) in arms.iter().chain(els.iter()).enumerate() {
            let p = arm_path(k);
            self.set_flow(rest.clone());
            if let Some(c) = &a.cond {
                self.cond(c, &mut Some((p.as_str(), &mut *out)));
                self.set_flow(self.branch(c, &rest, true));
                rest = self.branch(c, &rest, false);
            }
            self.body(&a.body, d, &p, ret, out);
            ends.push(self.flow());
        }
        if !els.as_ref().is_some_and(|a| a.cond.is_none()) {
            ends.push(rest);
        }
        self.set_flow(self.join_flows(ends));
    }

    fn body(&self, b: &Body, d: usize, path: &str, ret: Option<&Ty>, out: &mut Vec<Finding>) {
        match b {
            Body::Inline(s) => self.stmt(s, d, path, ret, out),
            Body::Block(ns) => self.nodes(ns, d + 1, &format!("{path}."), ret, out),
        }
    }

    /// An erratum's readings at `path`: each its own steps, under its overlay id; the flow at each one's end.
    fn alts(&self, e: usize, path: &str, alts: &[(crate::ast::Reading, Vec<Node>)], ret: Option<&Ty>, out: &mut Vec<Finding>) -> Vec<Flow> {
        let Some(er) = self.cx.g.overlay.errata.get(e) else { return Vec::new() };
        let Some(an) = er.readings.iter().find(|r| r.clause == self.clause && r.step == path) else { return Vec::new() };
        let f0 = self.flow();
        let mut ends = Vec::new();
        for ((_, ns), alt) in alts.iter().zip(&an.alts) {
            self.set_flow(f0.clone());
            let mut sub = Vec::new();
            self.nodes(ns, 0, "", ret, &mut sub);
            ends.push(self.flow());
            let key = format!("{}/{}@{}/{}", er.id, an.clause, an.step, alt.reading);
            out.extend(sub.into_iter().map(|f| Finding { key: key.clone(), ..f }));
        }
        ends
    }

    /// A value a step needs of some kinds: a finding where it has none of them.
    fn need(&self, t: &Ty, bits: u32, kind: &'static str, what: &str, at: &mut At) {
        if !t.is_empty() && t.v.bits & bits == 0 {
            self.emit(at, kind, format!("{what} {}", t.show(self.cx.d)));
        }
    }

    fn stmt(&self, st: &Stmt, d: usize, path: &str, ret: Option<&Ty>, out: &mut Vec<Finding>) {
        let block = |ns: &[Node], out: &mut Vec<Finding>| self.nodes(ns, d + 1, &format!("{path}."), ret, out);
        if let Stmt::If(c, b, arms, els) = st {
            return self.if_steps(c, b, arms, els, d, path, &|_| path.to_string(), ret, out);
        }
        // a loop's head keeps the narrowing of the slots its body never assigns
        let looped = matches!(
            st,
            Stmt::Repeat(_) | Stmt::RepeatWhile(..) | Stmt::RepeatUntil(..) | Stmt::RepeatN(..) | Stmt::ForEach(..) | Stmt::ForEachRec(..) | Stmt::ForSuchThat(..) | Stmt::ForKeys(..) | Stmt::ForIndex(..) | Stmt::ForChildren(..) | Stmt::ForChildrenOf(..) | Stmt::ForRange(..) | Stmt::WithSteps(..) | Stmt::FindSuchThat(..)
        );
        let f0 = self.flow();
        let head = if looped { self.killed(&f0, st) } else { f0.clone() };
        self.set_flow(head.clone());
        {
            let at = &mut Some((path, &mut *out));
            match st {
                Stmt::Let(_, e) | Stmt::Perform(e) | Stmt::ThrowVal(e) | Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) => {
                    self.infer(e, at);
                }
                Stmt::Set(p, e) => {
                    match p {
                        Place::Field(x, f) => {
                            self.sound_field(at, x, *f);
                            self.sound_store(at, e, self.store_ts(&self.infer_t(x), *f), &|| format!("a value set in [[{}]]", self.cx.d.fields.name(*f)));
                            let b = self.infer(x, at);
                            self.field(&b, *f, at);
                        }
                        Place::Expr(x) => {
                            if let (Some(_), Expr::Index(l, _)) = (self.cx.sound, strip(x)) {
                                self.sound_el(at, Some(e), &T::Any, l, &|| "an element set in a List".into());
                            }
                            self.infer(x, at);
                        }
                        Place::Var(_) => {}
                    }
                    self.infer(e, at);
                }
                Stmt::Ret(None) if self.counts() => {
                    let unused = self.cx.d.enums.get("unused").map_or(T::Any, |u| T::Enum([u].into()));
                    self.ret_t(unused);
                }
                Stmt::Ret(Some(e)) | Stmt::RetSee(e, _) => {
                    if let (Some(td), true) = (self.cx.sound, self.counts()) {
                        self.ret_t(self.infer_t(e).used(&td.hier));
                    }
                    let t = self.infer(e, at);
                    if let Some(c) = self.cid {
                        self.cx.seen_rets.borrow_mut().entry(c).or_default().join(&t);
                    }
                    if let (Some(td), Some(tr), true) = (self.cx.sound, &self.tret, ret.is_some()) {
                        let te = self.check_t(e, &unwrap_t(&td.hier, tr));
                        let te = if tr.members().iter().any(|m| matches!(m, T::Normal(_) | T::Abrupt)) { wrap_t(&td.hier, &te) } else { te };
                        self.sound_at(at, 1, &te, tr, &|| "a return".into());
                        if self.typed && te != T::Any && !te.meets(&td.hier, tr) {
                            let (path, d) = (at.as_ref().map_or("", |x| x.0), self.cx.d);
                            self.cx.cover.borrow_mut().typed.push(Finding { key: self.key.clone(), path: path.to_string(), kind: "typing", what: format!("a return: {} not within the typing {}", te.show(d), tr.show(d)) });
                        }
                    }
                    if let Some(r) = ret {
                        self.tally(at, 1, &t, Some(e));
                        let t = if r.comp() { t.wrapped() } else { t };
                        if !t.is_empty() && !r.is_empty() && !t.meets(r) {
                            let d = self.cx.d;
                            self.emit(at, "return", format!("{} for {}", t.show(d), r.show(d)));
                        }
                    }
                }
                Stmt::IfElse(c, ..) | Stmt::Assert(c) | Stmt::RepeatWhile(c, _) | Stmt::RepeatUntil(c, _) | Stmt::ForSuchThat(_, _, c, _, _) | Stmt::FindSuchThat(_, _, c, _, _) => self.cond(c, at),
                Stmt::AssertIf(c, e) => {
                    self.cond(c, at);
                    self.cond(e, at);
                }
                Stmt::RepeatN(e, _) => {
                    self.sound_e(at, 3, e, &T::Int, &|| "a count of".into());
                    let t = self.infer(e, at);
                    self.need(&t, MATH, "operand", "a count of", at);
                }
                Stmt::ForEach(_, _, l, _, _) | Stmt::ForEachRec(_, _, l, _) | Stmt::ForIndex(_, l, _) => {
                    self.sound_e(at, 3, l, &T::List(Box::new(T::Any)), &|| "a loop over".into());
                    let t = self.infer(l, at);
                    self.need(&t, LIST, "base", "a loop over", at);
                }
                Stmt::ForChildrenOf(_, l, _) => {
                    self.infer(l, at);
                }
                Stmt::ForKeys(_, o, c, _, _) => {
                    self.infer(o, at);
                    self.cond(c, at);
                }
                Stmt::ForRange(_, lo, _, hi, _, _, _) => {
                    for e in [lo, hi] {
                        self.sound_e(at, 3, e, &T::Int, &|| "a bound".into());
                        let t = self.infer(e, at);
                        self.need(&t, MATH, "operand", "a bound", at);
                    }
                }
                Stmt::Macro(_, xs) => {
                    self.args(xs, at);
                }
                Stmt::RemoveRestore(x, y) | Stmt::Resume(x, y) | Stmt::SetCodeState(x, y) | Stmt::ResumeLet(x, y, _, _) => {
                    self.infer(x, at);
                    self.infer(y, at);
                }
                Stmt::LetSuchThat(_, c, os) => {
                    self.cond(c, at);
                    for (_, e) in os {
                        self.infer(e, at);
                    }
                }
                Stmt::SyntaxError(_, c, u) => {
                    self.cond(c, at);
                    if let Some((_, u)) = u {
                        self.cond(u, at);
                    }
                }
                Stmt::Phrase(p, hs) | Stmt::Mutate(p, hs) => {
                    self.sound_add(at, *p, hs);
                    self.phrase(*p, hs, None, at);
                }
                Stmt::Prose(_, ps) | Stmt::Note(ps) => self.parts(ps, at),
                _ => {}
            }
        }
        // a closure's steps return from the closure, and start with no narrowing
        for k in own_closures(st) {
            if let Some(c) = self.closures.get(k) {
                let (saved, q) = (self.flow(), self.quiet.replace(true));
                self.set_flow(Flow::default());
                self.nodes(&c.body, d + 1, &format!("{path}."), None, out);
                self.set_flow(saved);
                self.quiet.set(q);
            }
        }
        match st {
            Stmt::IfElse(c, x, y) => {
                self.set_flow(self.branch(c, &head, true));
                self.stmt(x, d, path, ret, out);
                let a = self.flow();
                self.set_flow(self.branch(c, &head, false));
                self.stmt(y, d, path, ret, out);
                let b = self.flow();
                self.set_flow(self.join_flows(vec![a, b]));
            }
            Stmt::FindSuchThat(.., s) => {
                self.stmt(s, d, path, ret, out);
                let e = self.flow();
                self.set_flow(self.join_flows(vec![head, e]));
            }
            Stmt::Repeat(ns) | Stmt::RepeatN(_, ns) => {
                block(ns, out);
                self.set_flow(head);
            }
            Stmt::RepeatWhile(c, ns) => {
                self.set_flow(self.branch(c, &head, true));
                block(ns, out);
                self.set_flow(self.branch(c, &head, false));
            }
            Stmt::RepeatUntil(c, ns) => {
                block(ns, out);
                self.set_flow(self.branch(c, &head, true));
            }
            Stmt::ForEach(x, None, l, _, b) => {
                if let Some(td) = self.cx.sound {
                    let t = elem_t(&td.hier, &self.infer_t(l));
                    self.seen_bind(ver::addr(l), &t);
                    self.set_flow(self.with_t(&head, self.bid(*x, ver::addr(l)), t));
                }
                self.body(b, d, path, ret, out);
                self.set_flow(head);
            }
            Stmt::ForEach(.., b) | Stmt::ForEachRec(.., b) | Stmt::ForSuchThat(.., b) | Stmt::ForKeys(.., b) | Stmt::ForIndex(.., b) | Stmt::ForChildren(_, b) | Stmt::ForChildrenOf(_, _, b) | Stmt::ForRange(.., b) => {
                self.body(b, d, path, ret, out);
                self.set_flow(head);
            }
            Stmt::Readings(e, s, alts) => {
                let mut ends = Vec::new();
                if !alts.iter().any(|(r, _)| *r == crate::ast::Reading::Definition) {
                    self.stmt(s, d, path, ret, out);
                    ends.push(self.flow());
                }
                self.set_flow(f0.clone());
                ends.extend(self.alts(*e, path, alts, ret, out));
                self.set_flow(if ends.is_empty() { f0 } else { self.join_flows(ends) });
            }
            Stmt::WithSteps(s, ns) => {
                self.stmt(s, d, path, ret, out);
                block(ns, out);
                self.set_flow(head);
            }
            _ => self.effect(st),
        }
    }

    /// The narrowing after a step without nested steps: an assignment, an Assert, a return or throw.
    fn effect(&self, st: &Stmt) {
        let Some(td) = self.cx.sound else { return };
        let f = self.flow();
        let g = match st {
            Stmt::Let(x, e) | Stmt::Set(Place::Var(x), e) => {
                let t = self.infer_t(e);
                self.seen_bind(ver::addr(e), &t);
                self.assigned(&self.guarded(&self.killed(&f, st), e), self.bid(*x, ver::addr(e)), t)
            }
            Stmt::Perform(e) => self.guarded(&self.killed(&f, st), e),
            // a completion is a value: setting its field assigns the slot
            Stmt::Set(Place::Field(b, _), _) => {
                let mut g = self.killed(&f, st);
                if let r @ Expr::Var(x) = strip(b) {
                    let x = self.rid(r, *x);
                    if self.slot_t(&g, x).members().iter().any(|m| matches!(m, T::Normal(_) | T::Abrupt | T::Any)) {
                        g.ts.remove(&x);
                    }
                }
                g
            }
            Stmt::Macro(_, xs) => match xs.first() {
                Some(r @ Expr::Var(x)) => {
                    let old = self.slot_t(&f, self.rid(r, *x));
                    if self.counts() && old.members().iter().any(|m| matches!(m, T::Abrupt | T::Any)) {
                        self.abrupt.set(true);
                    }
                    let t = unwrap_t(&td.hier, &old);
                    self.seen_bind(ver::addr(r), &t);
                    self.assigned(&f, self.bid(*x, ver::addr(r)), t)
                }
                _ => self.killed(&f, st),
            },
            Stmt::Ret(_) | Stmt::RetSee(..) => {
                self.exit(&f);
                Flow { dead: true, ..f }
            }
            Stmt::ThrowErr(_) | Stmt::ThrowVal(_) | Stmt::Unreachable(_) => {
                if !matches!(st, Stmt::Unreachable(_)) && self.counts() {
                    self.abrupt.set(true);
                }
                Flow { dead: true, ..f }
            }
            Stmt::Assert(c) | Stmt::AssertAt(_, c) => self.branch(c, &f, true),
            Stmt::AssertIf(c, e) => self.join_flows(vec![self.branch(e, &self.branch(c, &f, true), true), self.branch(c, &f, false)]),
            _ => self.killed(&f, st),
        };
        self.set_flow(g);
    }
}

/// Every finding: the algorithms in the spec's order, the equation rows, then the overlay's algorithms and rows.
pub fn check(sp: &Spec, g: &Grammar, dt: &Data) -> (Vec<Finding>, [(usize, usize); 3]) {
    let (fs, st, _, _) = check_with(sp, g, dt, false, HashMap::new(), None);
    (fs, st)
}

/// The sound mode: every site whose value's type is not within the one it needs; the sites by class and kind; the versioned slots (algorithm, slot) and their versions.
pub fn within(sp: &Spec, g: &Grammar, dt: &Data, td: &TyDecls) -> (Vec<Finding>, [[usize; 4]; 4], Versioned) {
    let (fs, n, v, _) = within_units(sp, g, dt, td);
    (fs, n, v)
}

/// The sound mode's slot types per unit (clause, index), versions after the slots.
pub type UnitTys = Vec<((usize, usize), Vec<T>)>;

/// `within`, and each unit's slot types.
pub fn within_units(sp: &Spec, g: &Grammar, dt: &Data, td: &TyDecls) -> (Vec<Finding>, [[usize; 4]; 4], Versioned, UnitTys) {
    // the callees' facts through the calls, a round per level (a bound, not a fixed point)
    let mut ex = Facts::default();
    let mut cv = Cover::default();
    for _ in 0..4 {
        let (_, _, c, _, next) = check_at(sp, g, dt, false, HashMap::new(), Some(td), ex.clone());
        cv = c;
        if next == ex {
            break;
        }
        ex = next;
    }
    let mut seen = HashSet::new();
    let mut fs = cv.sound;
    fs.retain(|f| seen.insert(f.clone()));
    (fs, cv.sound_n, Versioned { slots: cv.versioned, rebound: [cv.rebound[0].len(), cv.rebound[1].len()] }, cv.units)
}

/// The type a method clause's `for` entry names where it has no variable (`a module namespace exotic object`).
fn recv_t(d: &Decls, h: &Hier, c: &crate::spec::Clause) -> T {
    let f = c.dl_entry("for").map(|f| crate::text::squash(&crate::text::strip_tags(&f))).unwrap_or_default();
    let f = f.split(" _").next().unwrap_or("");
    let f = f.strip_prefix("a ").or_else(|| f.strip_prefix("an ")).unwrap_or(f);
    d.sorts.get(f).or_else(|| d.sort_folds.get(f).and_then(|x| d.sorts.get(x))).map_or(T::Any, |s| sort_t(d, h, s))
}

/// Method clauses against their traits (receiver meets the root, parameters contravariant, result covariant); counts: implementations, unknown positions, methods of no trait.
pub fn impls(sp: &Spec, dt: &Data, td: &TyDecls) -> (Vec<Finding>, [usize; 3]) {
    let (d, h) = (&dt.decls, &td.hier);
    let mut out = Vec::new();
    let mut n = [0usize; 3];
    for a in dt.algs.iter().filter(|a| matches!(a.hdr.kind, "internalMethod" | "concreteMethod")) {
        let c = &sp.clauses[a.clause];
        let op = c.op().unwrap_or_default();
        let name = match op.strip_prefix("[[").and_then(|x| x.strip_suffix("]]")) {
            Some(f) => d.fields.get(f).map(SigName::Internal),
            None => d.methods.get(&op).map(SigName::Method),
        };
        let recv = match &a.hdr.recv {
            Some((_, t)) => of_tyexpr(d, h, t),
            None => recv_t(d, h, c),
        };
        let Some((tr, m)) = name.and_then(|x| trait_method(d, td, &recv, x)) else {
            n[2] += 1;
            continue;
        };
        n[0] += 1;
        n[1] += usize::from(recv == T::Any);
        let key = format!("{}#{}", sp.clauses[sp.home(a.clause)].id, sp.algs[a.alg].idx);
        let mut emit = |what: String| out.push(Finding { key: key.clone(), path: String::new(), kind: "impl", what });
        let root = tr.root.map_or(T::Any, |r| sort_t(d, h, r));
        if !recv.meets(h, &root) {
            emit(format!("{op}: receiver {} for {}'s {}", recv.show(d), tr.name, root.show(d)));
        }
        let ps: Vec<_> = a.hdr.params.iter().filter(|p| !p.3).collect();
        if ps.len() < m.params.len() || ps[m.params.len()..].iter().any(|p| !p.2) {
            emit(format!("{op}: {} parameters for {}'s {}", ps.len(), tr.name, m.params.len()));
        }
        let pname = |slot: usize| a.vars.names.get(slot).map_or("?", String::as_str).to_string();
        for (k, (p, (_, pt, popt))) in ps.iter().zip(&m.params).enumerate() {
            if *popt && !p.2 {
                emit(format!("{op} parameter {} (_{}_): required, optional in {}", k + 1, pname(p.0), tr.name));
            }
            let it = p.1.as_ref().map_or(T::Any, |t| of_tyexpr(d, h, t));
            if it == T::Any || *pt == T::Any {
                n[1] += 1;
                continue;
            }
            let it = if p.2 { T::opt(h, it) } else { it };
            if !pt.sub(h, &it) {
                emit(format!("{op} parameter {} (_{}_): {}'s {} not within {}", k + 1, pname(p.0), tr.name, pt.show(d), it.show(d)));
            }
        }
        let ir = a.hdr.ret.as_ref().map_or(T::Any, |t| of_tyexpr(d, h, t));
        if ir == T::Any || m.ret == T::Any {
            n[1] += 1;
        } else if !ir.sub(h, &m.ret) {
            emit(format!("{op}: result {} not within {}'s {}", ir.show(d), tr.name, m.ret.show(d)));
        }
    }
    (out, n)
}

/// Each result typing (`<emu-result-type>`) not within its header's result type (`T::sub`), and each return the sound mode finds disjoint from its typing.
pub fn typings(sp: &Spec, g: &Grammar, dt: &Data, td: &TyDecls) -> Vec<Finding> {
    let (d, h) = (&dt.decls, &td.hier);
    let algs = dt.algs.iter().map(|a| (sp.clauses[a.clause].id.clone(), &a.hdr));
    let sdos = dt.sdo_headers.iter().enumerate().filter_map(|(k, x)| x.as_ref().map(|x| (d.sdos.name(k).to_string(), x)));
    let phrases = dt.phrase_algs.iter().map(|p| (p.id.clone(), &p.hdr));
    let mut out: Vec<Finding> = Vec::new();
    for (key, hdr) in algs.chain(sdos).chain(phrases) {
        let Some(t) = &hdr.typing else { continue };
        let (it, ret) = (of_tyexpr(d, h, t), hdr.ret.as_ref().map_or(T::Any, |r| of_tyexpr(d, h, r)));
        if !it.sub(h, &ret) {
            out.push(Finding { key, path: String::new(), kind: "typing", what: format!("result {} not within the header's {}", it.show(d), ret.show(d)) });
        }
    }
    out.extend(check_with(sp, g, dt, false, HashMap::new(), Some(td)).2.typed);
    out.sort();
    out.dedup();
    out
}

/// `spec-gen types -impls`: the counts, then each finding's line, sorted.
pub fn impl_lines(fs: &[Finding], n: &[usize; 3]) -> Vec<String> {
    let mut out = vec![format!("# trait implementations checked {}, positions of unknown type {}, methods of no trait {}; findings {}\n", n[0], n[1], n[2], fs.len())];
    let mut ls: Vec<String> = fs.iter().map(Finding::line).collect();
    ls.sort();
    out.extend(ls);
    out
}

/// The sound mode's versioned slots (algorithm key, slot name: versions), and the counts of slots bound more than once and of them with more than one binding group.
#[derive(Debug, Default)]
pub struct Versioned {
    pub slots: BTreeMap<(String, String), usize>,
    pub rebound: [usize; 2],
}

/// `spec-gen types -within`: the sites by class and kind, the versioned slots, then each finding's line, sorted.
pub fn within_lines(fs: &[Finding], n: &[[usize; 4]; 4], v: &Versioned) -> Vec<String> {
    let mut out = vec!["# The sound mode: a site whose value's type is not within the one it needs (`T::sub`), by kind: meets (narrowing needed), unknown (a type of any value), disjoint.\n".to_string()];
    for (k, c) in SOUND_SITES.iter().zip(n) {
        out.push(format!("# {k} {}: {}\n", c.iter().sum::<usize>(), SOUND.iter().zip(c).map(|(s, x)| format!("{s} {x}")).collect::<Vec<_>>().join(", ")));
    }
    out.push(format!("# slots bound more than once {}, of them with more than one binding group {}, versioned {} (versions {})\n", v.rebound[0], v.rebound[1], v.slots.len(), v.slots.values().sum::<usize>()));
    out.extend(v.slots.iter().map(|((k, x), n)| format!("# versioned\t{k}\t{x}\t{n}\n")));
    let mut ls: Vec<String> = fs.iter().map(Finding::line).collect();
    ls.sort();
    out.extend(ls);
    out
}

/// The coverage as written, and with phrases expanded (phrase algorithms' returns iterated three times).
pub fn cover(sp: &Spec, g: &Grammar, dt: &Data) -> (Cover, Cover) {
    let (_, _, plain, _) = check_with(sp, g, dt, false, HashMap::new(), None);
    let mut rets = HashMap::new();
    let mut exp = Cover::default();
    for _ in 0..3 {
        let (_, _, c, r) = check_with(sp, g, dt, true, rets, None);
        exp = c;
        rets = r;
    }
    (plain, exp)
}

/// The check, and its coverage; with `expand`, `.alg` phrases typed as calls; with `sound`, the sound mode's sites.
pub fn check_with(sp: &Spec, g: &Grammar, dt: &Data, expand: bool, rets: HashMap<Id, Ty>, sound: Option<&TyDecls>) -> (Vec<Finding>, [(usize, usize); 3], Cover, HashMap<Id, Ty>) {
    let (fs, st, cv, rets, _) = check_at(sp, g, dt, expand, rets, sound, Facts::default());
    (fs, st, cv, rets)
}

/// `check_with`, with the callees' facts of the round before (`Facts`); and this round's.
#[allow(clippy::type_complexity)]
fn check_at(sp: &Spec, g: &Grammar, dt: &Data, expand: bool, rets: HashMap<Id, Ty>, sound: Option<&TyDecls>, facts: Facts) -> (Vec<Finding>, [(usize, usize); 3], Cover, HashMap<Id, Ty>, Facts) {
    let d = &dt.decls;
    let mut hdrs: HashMap<Id, (&Hdr, &Vars)> = HashMap::new();
    for a in &dt.algs {
        for c in [a.clause, sp.home(a.clause)] {
            if let Some(id) = d.clauses.get(&sp.clauses[c].id) {
                hdrs.entry(id).or_insert((&a.hdr, &a.vars));
            }
        }
    }
    for p in &dt.phrase_algs {
        hdrs.entry(p.clause).or_insert((&p.hdr, &p.vars));
    }
    let sdo_names: Vec<Vec<String>> = (0..d.sdos.names.len())
        .map(|k| {
            let cl = sp.clauses.iter().find(|c| c.ty.as_deref() == Some("sdo") && c.op().as_deref() == Some(d.sdos.name(k)));
            cl.map(|c| crate::header::parse(c).params.into_iter().map(|p| p.name).collect()).unwrap_or_default()
        })
        .collect();
    let ar: Arity = dt.phrase_algs.iter().map(|p| (p.clause, p.hdr.params.len())).collect();
    let ro = match sound {
        Some(_) => {
            let mut units: Vec<(Id, &Hdr, &[Node], &[CloLit])> = Vec::new();
            for a in &dt.algs {
                for c in [a.clause, sp.home(a.clause)] {
                    if let Some(id) = d.clauses.get(&sp.clauses[c].id) {
                        units.push((id, &a.hdr, &a.body, &a.closures));
                    }
                }
            }
            units.extend(dt.phrase_algs.iter().map(|p| (p.clause, &p.hdr, p.body.as_slice(), p.closures.as_slice())));
            read_only_params(d, &ar, &units)
        }
        None => HashSet::new(),
    };
    let cx = Cx {
        facts,
        facts_out: Default::default(),
        ro,
        d,
        g,
        hdrs,
        sdos: &dt.sdo_headers,
        sdo_names,
        stats: Default::default(),
        expand,
        rets,
        seen_rets: Default::default(),
        cover: Default::default(),
        f_type: d.fields.get("Type"),
        f_value: d.fields.get("Value"),
        f_target: d.fields.get("Target"),
        f_desc: d.fields.get("Description"),
        sound,
        sig_tys: &dt.sig_tys,
    };
    let mut out = Vec::new();
    // one algorithm: its key, clause, header, return type, body, closures, variables, and the
    // variables bound outside it (none: every one)
    let mut one = |uid: (usize, usize), key: String, clause: String, hdr: Option<&Hdr>, rh: Option<&Hdr>, body: &[Node], closures: &[CloLit], vars: &Vars, outer: Option<&[String]>, cid: Option<Id>, ids: Vec<Id>| {
        let (rty, typed) = (rh.and_then(Hdr::result), rh.is_some_and(|h| h.typing.is_some()));
        let mut bs = Vec::new();
        binds(body, closures, &mut bs, &mut HashSet::new());
        let ret = rty.map(|t| of_ty(d, t));
        let tret = sound.zip(rty).map(|(td, t)| of_tyexpr(d, &td.hier, t));
        let mut a = Alg { cx: &cx, key, clause, vars, closures, env: HashMap::new(), bound: HashSet::new(), why: HashMap::new(), cid, tenv: HashMap::new(), tret, typed, flow: Default::default(), fixed: HashSet::new(), add_t: Default::default(), bind_t: Default::default(), slot_els: HashMap::new(), exit_ids: Vec::new(), exit_slots: Vec::new(), exit_at: Default::default(), quiet: Default::default(), rd: HashMap::new(), bd: HashMap::new(), vers: HashMap::new(), joined: HashMap::new(), abrupt: Default::default() };
        a.solve(hdr, &bs);
        let raw = if sound.is_some() { list_uses(d, &ar, body, closures) } else { Vec::new() };
        let (mut vbs, mut uses) = (Vec::new(), Vec::new());
        if sound.is_some() {
            (vbs, uses) = a.version(hdr, &ver::groups(body, closures, &bs), &bs, &raw);
            // a slot a closure assigns, through its captures, may change while the steps run
            for c in closures {
                let mut w = Vec::new();
                binds(&c.body, closures, &mut w, &mut HashSet::new());
                let mut ws: HashSet<Id> = w.into_iter().map(|b| b.0).collect();
                c.body.iter().for_each(|n| hole_vars(&n.stmt, &mut ws));
                a.fixed.extend(c.caps.iter().filter(|x| ws.contains(x)));
            }
        }
        {
            let mut cv = cx.cover.borrow_mut();
            for (x, t) in &a.env {
                let b = bucket(t);
                cv.slots[b] += 1;
                if b == 0 {
                    let w = a.why.get(x).cloned().unwrap_or_else(|| "outer variable (an SDO's parameter or the caller's)".into());
                    *cv.slot_top.entry(w).or_default() += 1;
                }
            }
        }
        match outer {
            Some(ns) => a.bound.extend(ns.iter().filter_map(|n| vars.names.iter().position(|x| x == n))),
            None => a.bound.extend(0..vars.names.len()),
        }
        let ret = ret.as_ref().filter(|r| !r.is_top());
        // bindings and the elements a List step adds take their narrowed types from a first, silent pass
        if sound.is_some() {
            let saved = (std::mem::take(&mut *cx.cover.borrow_mut()), *cx.stats.borrow(), std::mem::take(&mut *cx.seen_rets.borrow_mut()));
            a.quiet.set(true);
            a.nodes(body, 0, "", ret, &mut Vec::new());
            a.quiet.set(false);
            (*cx.cover.borrow_mut(), *cx.stats.borrow_mut(), *cx.seen_rets.borrow_mut()) = saved;
            a.set_flow(Flow::default());
            a.solve_t(hdr, &vbs, &uses);
            let n = a.tenv.keys().map(|x| x + 1).fold(vars.names.len(), usize::max);
            cx.cover.borrow_mut().units.push((uid, (0..n).map(|x| a.tenv.get(&x).cloned().unwrap_or(T::Any)).collect()));
        }
        if let (Some(h), true) = (hdr, sound.is_some() && !ids.is_empty()) {
            let mut w = Vec::new();
            binds(body, closures, &mut w, &mut HashSet::new());
            let mut ws: HashSet<Id> = w.into_iter().map(|b| b.0).collect();
            body.iter().for_each(|n| hole_vars(&n.stmt, &mut ws));
            a.exit_slots = h.params.iter().map(|p| (!p.3 && !ws.contains(&p.0)).then_some(p.0)).collect();
            a.exit_ids = ids;
        }
        let mut found = Vec::new();
        a.nodes(body, 0, "", ret, &mut found);
        if a.abrupt.get() {
            a.ret_t(T::Abrupt);
        }
        // a body that ends without a return returns there
        a.exit(&a.flow());
        if let (Some(td), Some(now)) = (sound, a.exit_at.take()) {
            let ex = &mut cx.facts_out.borrow_mut().exits;
            for id in &a.exit_ids {
                let j = match ex.remove(id) {
                    None => now.clone(),
                    Some(old) => old.into_iter().zip(now.iter()).map(|(x, y)| Some(x?.join(&td.hier, y.as_ref()?))).collect(),
                };
                ex.insert(*id, j);
            }
        }
        out.extend(found);
    };
    for a in &dt.algs {
        let al = &sp.algs[a.alg];
        let cid = sp.clauses[sp.home(a.clause)].id.clone();
        // a table's step cell reads its referrer's variables; an SDO row its SDO's parameters
        let cell = dt.env.table_spans.iter().any(|r| r.contains(&al.pos));
        let s = sp.clauses[a.clause].op().and_then(|o| d.sdos.get(&o));
        let sdo = s.map(|s| cx.sdo_names[s].as_slice());
        let outer = if cell { None } else { Some(sdo.unwrap_or(&[])) };
        // an SDO's row: its SDO's typed result where its own header has none
        let typed = s.and_then(|s| dt.sdo_headers.get(s)).and_then(Option::as_ref).filter(|h| h.typing.is_some());
        let rh = if a.hdr.result().is_none() { typed.or(Some(&a.hdr)) } else { Some(&a.hdr) };
        let ids: Vec<Id> = [a.clause, sp.home(a.clause)].iter().filter_map(|&c| d.clauses.get(&sp.clauses[c].id)).collect::<BTreeSet<Id>>().into_iter().collect();
        one((d.cid(a.clause), a.idx), format!("{cid}#{}", al.idx), cid, Some(&a.hdr), rh, &a.body, &a.closures, &a.vars, outer, None, ids);
    }
    for e in dt.eqs.iter().filter(|e| e.exception.is_none()) {
        let cid = sp.clauses[sp.home(e.clause)].id.clone();
        let h = dt.sdo_headers.get(e.sdo).and_then(Option::as_ref);
        let names = cx.sdo_names[e.sdo].as_slice();
        one((d.cid(e.clause), e.idx), format!("{cid}#{}", e.idx), cid, None, h, &e.body, &[], &e.vars, Some(names), None, Vec::new());
    }
    for p in &dt.phrase_algs {
        one((p.clause, 0), p.id.clone(), String::new(), Some(&p.hdr), Some(&p.hdr), &p.body, &p.closures, &p.vars, Some(&[]), Some(p.clause), Vec::new());
    }
    for r in &dt.reading_rows {
        let s = d.sdos.get(&r.sdo);
        let h = s.and_then(|s| dt.sdo_headers.get(s)).and_then(Option::as_ref);
        let names = s.map_or(&[][..], |s| cx.sdo_names[s].as_slice());
        one((r.clause, 0), r.id.clone(), String::new(), None, h, r.steps(), &r.closures, &r.vars, Some(names), None, Vec::new());
    }
    // a parameterized clause's finding once, however many instances share it
    let mut seen = HashSet::new();
    out.retain(|f| seen.insert(f.clone()));
    let st = *cx.stats.borrow();
    let cv = cx.cover.borrow().clone();
    let rets = cx.seen_rets.borrow().clone();
    let ex = cx.facts_out.borrow().clone();
    (out, st, cv, rets, ex)
}

/// `spec-gen types -cover`: the program as written and with phrases expanded.
pub fn cover_lines(plain: &Cover, exp: &Cover) -> Vec<String> {
    const CLS: [&str; 3] = ["arguments", "returns", "operands"];
    let pct = |n: usize, of: usize| if of == 0 { 0.0 } else { 100.0 * n as f64 / of as f64 };
    let row = |what: &str, b: &[usize; 4]| {
        let n: usize = b.iter().sum();
        format!("{what}\t{n}\tany {} ({:.1}%)\tcompletion {} ({:.1}%)\tunion {} ({:.1}%)\tone kind {} ({:.1}%)\n", b[0], pct(b[0], n), b[1], pct(b[1], n), b[2], pct(b[2], n), b[3], pct(b[3], n))
    };
    let mut out = vec!["# sites and variables by precision: as written, then under the proposed rule (phrases expanded: `.alg` phrases typed as calls)\n".to_string()];
    for (tag, c) in [("written", plain), ("proposed", exp)] {
        for (k, n) in CLS.iter().enumerate() {
            out.push(row(&format!("{tag} {n}"), &c.sites[k]));
        }
        out.push(row(&format!("{tag} variables"), &c.slots));
    }
    let top = |m: &BTreeMap<String, usize>, n: usize, out: &mut Vec<String>| {
        let mut v: Vec<(&String, &usize)> = m.iter().collect();
        v.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        out.extend(v.into_iter().take(n).map(|(k, c)| format!("  {c}\t{k}\n")));
    };
    for (k, n) in CLS.iter().enumerate() {
        let mut by: BTreeMap<String, usize> = BTreeMap::new();
        let mut head: BTreeMap<String, usize> = BTreeMap::new();
        for ((kk, c), m) in &exp.top {
            if *kk == k {
                *by.entry(c.clone()).or_default() += m;
                *head.entry(c.split(':').next().unwrap_or(c).to_string()).or_default() += m;
            }
        }
        out.push(format!("# proposed {n} of any value, by head form\n"));
        top(&head, 40, &mut out);
        out.push(format!("# proposed {n} of any value, by cause\n"));
        top(&by, 40, &mut out);
    }
    out.push("# proposed variables of any value, by cause\n".into());
    top(&exp.slot_top, 60, &mut out);
    out.push(format!("# internal methods: {} sites, {} names\n", exp.imethods.values().sum::<usize>(), exp.imethods.len()));
    top(&exp.imethods, 40, &mut out);
    out.push(format!("# concrete methods: {} sites, {} names\n", exp.cmethods.values().sum::<usize>(), exp.cmethods.len()));
    top(&exp.cmethods, 60, &mut out);
    out.push(format!("# closure calls: {}\n", exp.applies));
    out.push(format!(
        "# argument sites, both sorts known: within the parameter's {}, meeting it only {} (narrowing or a checked cast), by sorts:\n",
        exp.within[0], exp.within[1]
    ));
    top(&exp.overlap, 40, &mut out);
    out.push(format!(
        "# variables bound more than once: {}; to disjoint sorts: {}; of them a completion, then a value: {}\n",
        exp.retyped[0], exp.retyped[1], exp.retyped[2]
    ));
    out.push(format!(
        "# field reads and writes: {} (base any value {}, an Object or Record {}, other {}), {} field names\n",
        exp.fields.iter().sum::<usize>(),
        exp.fields[0],
        exp.fields[1],
        exp.fields[2],
        exp.field_names.len()
    ));
    top(&exp.field_names, 40, &mut out);
    out
}

/// The sorts the headers name that the checker takes as any value: name, uses.
pub fn opaque_sorts(dt: &Data) -> Vec<(String, usize)> {
    fn walk(t: &TyExpr, f: &mut dyn FnMut(Id)) {
        match t {
            TyExpr::Sort(_, _, s, _) => f(*s),
            TyExpr::ListOf(_, x) | TyExpr::Interval(x, _, _) | TyExpr::That(x, _, _) => walk(x, f),
            TyExpr::Completion(Some(x)) => walk(x, f),
            TyExpr::Union(_, _, ts) => ts.iter().for_each(|t| walk(t, f)),
            TyExpr::Record(fs) => fs.iter().for_each(|(_, t)| walk(t, f)),
            _ => {}
        }
    }
    let d = &dt.decls;
    let mut uses: BTreeMap<String, usize> = BTreeMap::new();
    let hs = dt.algs.iter().map(|a| &a.hdr).chain(dt.phrase_algs.iter().map(|p| &p.hdr)).chain(dt.sdo_headers.iter().flatten());
    for h in hs {
        for t in h.params.iter().filter_map(|p| p.1.as_ref()).chain(h.ret.iter()).chain(h.recv.iter().map(|r| &r.1)) {
            walk(t, &mut |s| {
                if sort_ty(d, s, 0).is_top() {
                    *uses.entry(d.sorts.name(s).to_string()).or_default() += 1;
                }
            });
        }
    }
    let mut v: Vec<(String, usize)> = uses.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    v
}

/// `spec-gen types -dyn`, the dyn ratchet file: the sound mode's lines by kind, then each line, sorted.
pub fn dyn_lines(fs: &[Finding]) -> Vec<String> {
    let mut ls: Vec<String> = fs.iter().map(Finding::line).collect();
    ls.sort();
    ls.dedup();
    let by = |k: &str| ls.iter().filter(|l| l.split('\t').next() == Some(k)).count();
    let mut out = vec![
        "# The dyn sites: the sound mode's sites not within the type they need, which keep their dynamic check; generated by `spec-gen types -dyn`; `spec-gen types -check-dyn` fails on a line not here.\n".to_string(),
        format!("# lines: {}; {}\n", ls.len(), SOUND[1..].iter().map(|k| format!("{k} {}", by(k))).collect::<Vec<_>>().join(", ")),
        "# The file only shrinks: an added line needs the coordinator's approval in the merge message.\n".to_string(),
    ];
    out.extend(ls);
    out
}

/// The ratchet file: a header with the counts, then each finding's line, sorted.
pub fn lines(fs: &[Finding], st: &[(usize, usize); 3]) -> Vec<String> {
    let mut by: BTreeMap<&str, usize> = BTreeMap::new();
    for f in fs {
        *by.entry(f.kind).or_default() += 1;
    }
    let mut out = vec![
        "# The steps not typed by their headers, generated by `spec-gen types -lines`; `spec-gen types -check` fails on a line not here.\n".to_string(),
        format!("# findings: {}; {}\n", fs.len(), KINDS.iter().map(|k| format!("{k} {}", by.get(k).unwrap_or(&0))).collect::<Vec<_>>().join(", ")),
        format!("# sites checked, of them with a known sort: arguments {} {}, returns {} {}, operands {} {}\n", st[0].0, st[0].1, st[1].0, st[1].1, st[2].0, st[2].1),
        "# The file only shrinks: an added line needs the coordinator's approval in the merge message.\n".to_string(),
    ];
    let mut ls: Vec<String> = fs.iter().map(Finding::line).collect();
    ls.sort();
    out.extend(ls);
    out
}

/// Fails when a finding's line is not in `file`; prints the file's lines that no longer occur.
pub fn check_file(fs: &[Finding], file: &str) -> Result<bool, String> {
    let have = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
    let mut count: HashMap<&str, isize> = HashMap::new();
    for l in have.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        *count.entry(l).or_default() += 1;
    }
    let mut new = Vec::new();
    for f in fs {
        let l = f.line();
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
    new.sort();
    for l in &new {
        eprintln!("new type finding, not in {file}: {l}");
    }
    Ok(new.is_empty())
}

/// ESMeta's ignore list (a JSON array of strings): its names.
pub fn esmeta_names(text: &str) -> Vec<String> {
    text.split('"').skip(1).step_by(2).map(str::to_string).collect()
}

/// Whether ESMeta's algorithm name (`Op`, `Lhs[i,j].Op`, `Record[Kind].Op`) names the algorithm at `key`.
pub(crate) fn esmeta_names_alg(name: &str, op: &str, prod: Option<&str>) -> bool {
    let (head, nop) = name.rsplit_once('.').map_or(("", name), |(a, b)| (a, b));
    if nop != op {
        return false;
    }
    match head.split_once('[') {
        Some((lhs, _)) if lhs != "Record" => prod.is_some_and(|p| p.trim_start().split_whitespace().next() == Some(lhs)),
        _ => true,
    }
}

/// The findings by algorithm against ESMeta's ignore list: each line `both`, `esmeta-only` or
/// `ours-only`, the name, and our count.
pub fn esmeta_diff(sp: &Spec, dt: &Data, fs: &[Finding], names: &[String]) -> Vec<String> {
    let mut by_key: BTreeMap<&str, usize> = BTreeMap::new();
    for f in fs {
        *by_key.entry(f.key.as_str()).or_default() += 1;
    }
    // each key's operation and SDO production
    let mut alg_of: HashMap<String, (String, Option<String>)> = HashMap::new();
    for a in &dt.algs {
        let al = &sp.algs[a.alg];
        let c = &sp.clauses[sp.home(a.clause)];
        alg_of.insert(format!("{}#{}", c.id, al.idx), (c.op().unwrap_or_default(), al.prod.clone()));
    }
    let mut out = Vec::new();
    let mut matched: HashSet<&str> = HashSet::new();
    for n in names {
        let keys: Vec<&str> = by_key.keys().copied().filter(|k| alg_of.get(*k).is_some_and(|(op, prod)| esmeta_names_alg(n, op, prod.as_deref()))).collect();
        let count: usize = keys.iter().map(|k| by_key[k]).sum();
        matched.extend(keys.iter().copied());
        if count > 0 {
            out.push(format!("both\t{n}\t{count}\t{}\n", keys.join(" ")));
        } else {
            out.push(format!("esmeta-only\t{n}\t0\t-\n"));
        }
    }
    for (k, c) in &by_key {
        if !matched.contains(k) {
            let op = alg_of.get(*k).map_or(*k, |x| x.0.as_str());
            out.push(format!("ours-only\t{op}\t{c}\t{k}\n"));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each versioned slot's groups as the positions of their bindings, from the unit's body.
    fn group_shape(body: &[Node], closures: &[CloLit]) -> Vec<(Id, Vec<Vec<usize>>)> {
        let mut bs = Vec::new();
        binds(body, closures, &mut bs, &mut HashSet::new());
        let g = ver::groups(body, closures, &bs);
        let at = |k: usize| if k == ver::ENTRY { 0 } else { 1 + bs.iter().position(|b| ver::key(&b.1) == Some(k)).unwrap() };
        let mut out: Vec<_> = g.of.iter().map(|(x, gs)| (*x, gs.iter().map(|ks| ks.iter().map(|&k| at(k)).collect()).collect())).collect();
        out.sort();
        out
    }

    #[test]
    fn binding_groups_follow_the_bindings_not_their_addresses() {
        let html = crate::tests::op("    1. Let _x_ be 1.
    1. Let _y_ be _x_.
    1. Set _x_ to \"s\".
    1. Return _x_.");
        let dt = crate::tests::build(&html);
        let a = &dt.algs[0];
        let first = group_shape(&a.body, &a.closures);
        assert!(first.iter().any(|(_, gs)| gs.len() > 1), "{first:?}");
        assert!(first.iter().all(|(_, gs)| gs.windows(2).all(|w| w[0].iter().min() < w[1].iter().min())), "{first:?}");
        // the same unit at other addresses
        for n in [1usize, 7, 64] {
            let junk: Vec<Vec<u8>> = (0..n * 50).map(|i| vec![0; 8 + i % 40]).collect();
            let (body, closures) = (a.body.clone(), a.closures.clone());
            assert_eq!(group_shape(&body, &closures), first);
            drop(junk);
        }
    }
}
