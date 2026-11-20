//! The whole data: declarations, and every algorithm converted.

use crate::ast::{CloLit, LiLayout, Node, Part, Stmt, TyExpr};
use crate::classify::Row;
use crate::conv::{Conv, Env, Vars};
use crate::decls::Decls;
use crate::grammar::Grammar;
use crate::spec::{Spec, Step};
use std::collections::HashMap;

/// A parsed header: kind, parameters (slot, type, optional, rest), return type, receiver.
pub struct Hdr {
    pub kind: &'static str,
    pub params: Vec<(usize, Option<TyExpr>, bool, bool)>,
    pub ret: Option<TyExpr>,
    pub recv: Option<(usize, TyExpr)>,
    pub desc: String,
    /// the overlay's typing of the result (`<emu-result-type>`), which the machine ignores
    pub typing: Option<TyExpr>,
}

impl Hdr {
    /// The result's type: the overlay's typing, else the header's.
    pub fn result(&self) -> Option<&TyExpr> {
        self.typing.as_ref().or(self.ret.as_ref())
    }
}

pub struct Alg {
    /// index into `Spec::algs`
    pub alg: usize,
    /// an SDO row's grammar key as written, and its productions
    pub keys: Vec<String>,
    pub prods: Vec<usize>,
    pub clause: usize,
    pub idx: usize,
    pub hdr: Hdr,
    pub vars: Vars,
    pub body: Vec<Node>,
    pub closures: Vec<CloLit>,
    /// the errata readings' steps converted: erratum, anchor, reading, steps
    pub readings: Vec<(usize, usize, usize, Vec<Node>)>,
    /// steps kept as prose for want of a data shape: text, reason
    pub exceptions: Vec<(String, String)>,
    /// the SDO an annex clause extends with this row (`extends`)
    pub ext: Option<Ext>,
}

/// An annex row's place in the SDO it extends ("The static semantics of X are augmented with the
/// following").
#[derive(Clone, Debug)]
pub struct Ext {
    pub op: String,
    /// the SDO's first `sdo` clause
    pub clause: usize,
    /// under "… rules are replaced": the row stands in place of the main text's on its productions
    pub replaces: bool,
}

/// The SDO an annex algorithm extends: the last paragraph before it in its clause that names an
/// operation the annex extends, where an SDO defines it, and whether a "rules are replaced"
/// paragraph follows it.
pub fn extends(html: &str, sp: &Spec, a: &crate::spec::Alg) -> Option<Ext> {
    extends_at(html, sp, a.clause?, a.pos)
}

/// The SDO annex clause `cl` extends at offset `pos` of spec.html, as `extends`.
pub fn extends_at(html: &str, sp: &Spec, cl: usize, pos: usize) -> Option<Ext> {
    let c = &sp.clauses[cl];
    if !c.number.starts_with(|x: char| x.is_ascii_uppercase()) {
        return None;
    }
    let before = &html[c.start..pos];
    let paras: Vec<&str> = before.split("<p>").skip(1).map(|p| p.split("</p>").next().unwrap_or("")).collect();
    let (k, op) = paras.iter().enumerate().rev().find_map(|(k, p)| {
        let p = crate::text::squash(p);
        if !(p.contains(" is extended as follows") || p.contains(" are augmented with the following")) {
            return None;
        }
        let rest = p.split_once("emantics of ")?.1;
        let op = rest.split([' ', ':']).next()?.to_string();
        Some((k, op))
    })?;
    let replaces = paras[k + 1..].last().is_some_and(|p| p.contains(" are replaced"));
    let clause = sp.clauses.iter().position(|d| !d.number.starts_with(|x: char| x.is_ascii_uppercase()) && d.op().as_deref() == Some(op.as_str()) && d.ty.as_deref() == Some("sdo"))?;
    Some(Ext { op, clause, replaces })
}

/// The end of clause `cl`'s own text: the start of its first nested clause, or its end.
fn own_end(sp: &Spec, cl: usize) -> usize {
    let c = &sp.clauses[cl];
    sp.clauses.iter().map(|d| d.start).filter(|&s| s > c.start && s < c.end).min().unwrap_or(c.end)
}

/// An equation SDO row.
pub struct EqRow {
    /// index into `Spec::eqs`
    pub eq: usize,
    pub clause: usize,
    pub idx: usize,
    pub sdo: usize,
    /// the grammar keys as written, one per `<emu-grammar>`
    pub keys: Vec<String>,
    pub prods: Vec<usize>,
    pub vars: Vars,
    pub body: Vec<Node>,
    /// why the bullet has no data shape, if it has none (it is kept as prose)
    pub exception: Option<String>,
}

/// An early-error rule row: one bullet of an Early Errors clause.
pub struct EarlyRow {
    /// index into `Early::bullets`
    pub bullet: usize,
    pub clause: usize,
    pub idx: usize,
    /// the SDO "Early Errors"
    pub sdo: usize,
    pub prods: Vec<usize>,
    pub vars: Vars,
    /// its sentences
    pub body: Vec<Node>,
    /// why a sentence has no data shape, if one has none (the bullet is kept as prose)
    pub exception: Option<String>,
    /// the rule's readings: erratum, and each reading's sentences
    pub readings: Option<(usize, Vec<(crate::ast::Reading, Vec<Node>)>)>,
    /// a rule reading's copy on other productions (`also=`): their key; its literal body is empty
    pub twin: Option<String>,
    /// an annex rule that modifies the main rules of its productions (they stand for them)
    pub modifies: bool,
}

/// An overlay algorithm: a phrase's meaning (`<emu-phrase>`'s `<emu-alg>`) or a sort's test.
pub struct PhraseAlg {
    /// the phrase's id, or the sort's (`sort_alg_id`)
    pub id: String,
    /// the overlay file it is in
    pub file: String,
    /// its clause in `Decls::clauses`, after spec.html's
    pub clause: usize,
    /// its steps, as an algorithm of no clause
    pub alg: crate::spec::Alg,
    pub hdr: Hdr,
    pub vars: Vars,
    pub body: Vec<Node>,
    pub closures: Vec<CloLit>,
    pub exceptions: Vec<(String, String)>,
}

/// Primitive names retired for naming an operation or a concrete method (their ids stay):
/// HasBinding, which BindingsHas replaces; IsDateTimeRepresentable, DateTimeString and
/// CaptureGroupName, the overlay's operations of those names.
const RETIRED_PRIMS: &[&str] = &["HasBinding", "IsDateTimeRepresentable", "DateTimeString", "CaptureGroupName"];

/// Live primitives that share an operation's name and are reached only as phrase meanings, never
/// by name: Contains (a List's element, beside the SDO Contains) and NumericValue (a code point's,
/// beside the SDO NumericValue).
const PHRASE_ONLY_PRIMS: &[&str] = &["Contains", "NumericValue"];

/// An SDO row the overlay adds by a reading.
pub struct ReadingRow {
    pub id: String,
    pub file: String,
    /// the reading's own clause
    pub clause: usize,
    pub sdo: String,
    pub keys: Vec<String>,
    pub prods: Vec<usize>,
    pub alg: crate::spec::Alg,
    pub vars: Vars,
    pub body: Vec<Node>,
    pub closures: Vec<CloLit>,
    pub exceptions: Vec<(String, String)>,
    /// the erratum whose `test262 proposed` reading the row is: `body` is then one step, its readings
    pub erratum: Option<usize>,
    /// a row of an annex clause that extends the SDO
    pub annex: bool,
}

impl ReadingRow {
    /// The row's own steps: under an erratum, its other readings'.
    pub fn steps(&self) -> &[Node] {
        match (&self.erratum, self.body.as_slice()) {
            (Some(_), [Node { stmt: Stmt::Readings(_, _, alts), .. }]) => &alts[0].1,
            _ => &self.body,
        }
    }
}

pub struct Data {
    /// the overlay's algorithms: phrase meanings, then sort tests
    pub phrase_algs: Vec<PhraseAlg>,
    /// the SDO rows the overlay's readings add
    pub reading_rows: Vec<ReadingRow>,
    /// the row readings that add no row, and why
    pub row_errors: Vec<String>,
    /// primitive names that are also an operation's or a concrete method's (a call by name
    /// reaches the operation)
    pub name_clashes: Vec<String>,
    /// the overlay's primitives: name, signature, meaning
    pub overlay_docs: Vec<(String, String, String)>,
    /// errata readings whose anchor names no step
    pub anchor_errors: Vec<String>,
    pub eqs: Vec<EqRow>,
    /// each SDO's header (its first `sdo` clause's), by SdoId
    pub sdo_headers: Vec<Option<Hdr>>,
    pub early: Vec<EarlyRow>,
    /// header type phrases: occurrences parsed, occurrences, distinct parsed, distinct
    pub header_types: (usize, usize, usize, usize),
    /// the primitives' signature types (`sig::texts`) the header-type grammar parses, by text
    pub sig_tys: HashMap<String, TyExpr>,
    pub decls: Decls,
    pub env: Env,
    pub algs: Vec<Alg>,
    pub unresolved: Vec<String>,
}

/// The names the converter resolves: each operation's first defining clause (its clause id, from `cids`, each
/// spec.html clause's: `Decls::cids`), and the components.
pub fn env(html: &str, sp: &Spec, cids: &[usize], kept: &jsgrammar::ids::KeptIds) -> Env {
    let mut ops = HashMap::new();
    let mut nt_params = HashMap::new();
    for (i, c) in sp.clauses.iter().enumerate() {
        let op = c.op().unwrap_or_default();
        if !op.is_empty() && !ops.contains_key(&op) {
            let ts: Vec<String> = crate::header::parse(c).params.into_iter().map(|p| p.ty.unwrap_or_default()).collect();
            nt_params.insert(op.clone(), crate::sig::nt_params(&ts));
            ops.insert(op, cids[i]);
        }
    }
    let scanned = crate::tables::scan(html, sp);
    let components = crate::tables::first_column(&scanned, crate::tables::Kind::Components);
    let tables = scanned.iter().enumerate().filter_map(|(i, t)| Some((t.as_ref().ok()?.id()?, i))).collect();
    let table_spans = scanned.iter().map(|t| t.as_ref().map_or(0..0, |t| t.pos..t.pos + t.raw.len())).collect();
    let table_names = scanned.iter().enumerate().map(|(i, t)| t.as_ref().map_or_else(|_| format!("?{i}"), |t| crate::tables::lean_name(sp, t))).collect();
    let figures = scanned.iter().enumerate().filter_map(|(i, t)| t.as_ref().ok().filter(|t| t.figure).map(|t| (crate::text::squash(&t.raw), i))).collect();
    let gl = jsgrammar::gl::Gl::load_with(html, None, kept).unwrap_or_else(|e| panic!("the grammars: {e}"));
    let algs = sp.algs.iter().filter_map(|a| Some(((sp.clauses[a.clause?].id.clone(), a.raw.clone()), a.idx))).collect();
    let symbols = crate::realm::well_known_symbols(html).unwrap_or_default();
    Env { ops, nt_params, components, gl, algs, tables, table_names, table_spans, figures, symbols }
}

/// The SDOs defined by equation bullets: `<li>The MV of <emu-grammar>`.
fn equation_sdos(html: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (i, _) in html.match_indices("<li>") {
        let Some(rest) = html[i + 4..].trim_start().strip_prefix("The ") else { continue };
        if let Some(sp) = rest.find(" of <emu-grammar") {
            let name = &rest[..sp];
            if !name.is_empty() && name.len() < 16 && name.chars().all(|c| c.is_ascii_alphanumeric()) && !out.iter().any(|x| x == name) {
                out.push(name.to_string());
            }
        }
    }
    out
}

/// `Ecma.Known`'s sorts, which the value decides.
pub const SORTS: &[&str] = &[
    "Completion Record", "Number", "String", "Boolean", "Symbol", "BigInt", "Object", "List", "Record", "integer",
    "mathematical value", "extended mathematical value", "Parse Node", "Abstract Closure", "ECMAScript language value",
    "property key", "normal completion", "abrupt completion", "throw completion", "return completion", "undefined", "null",
    "non-negative integer", "Property Descriptor",
];

/// The names `Ecma.Known` (Syntax.lean) fixes, interned first at its indices;
/// phrase row 0 is "a newly created ‹E› object", SDO 0 is "Early Errors". Under a
/// frozen primitive index, a Known primitive keeps its index id and a new one is appended.
fn seed_known(d: &mut Decls, g: &Grammar) {
    const ENUMS: &[&str] = &["normal", "throw", "return", "break", "continue", "empty", "unused", "accessor", "data"];
    const FIELDS: &[&str] = &[
        "Type", "Value", "Target", "Realm", "Intrinsics", "code evaluation state", "Writable", "Getter", "Setter", "Enumerable", "Configurable",
        "Function", "ScriptOrModule", "LexicalEnvironment", "VariableEnvironment", "PrivateEnvironment", "Generator",
        "Description",
];

    const PRIMS: &[&str] = &[
        "𝔽", "ℝ", "ℤ", "abs", "floor", "min", "max", "truncate", "Append", "Prepend", "Remove", "length", "newError", "the empty String",
        "string-concatenation", "clamping", "OwnPropertyLookup", "OwnPropertyCreate", "OwnPropertyReplace", "OwnPropertySetAttribute",
        "OwnPropertyRemove", "HasNoFields", "IsOrdinaryMethod", "implementation-approximated", "implementation-defined choice",
        "nondeterministic byte", "nondeterministic bytes", "the host is a web browser", "ListNew", "ListConcat", "ListLen", "Contains",
        "ListElem", "ListOf1", "Copy", "IsEmpty", "SameLength", "ListFind", "Count", "Insert", "RemoveElem", "RemoveFirst", "RemoveLast", "Reverse",
        "ReplaceElem", "SetAdd", "StoreBytes", "CodeUnit", "StrOfUnits", "Substring", "StrLen", "UnitAt", "NumericValue", "FirstUnit",
        "StartsWith", "CodePointCount", "UnitOrPointOf", "CodePointMatched", "CodePoints", "EmptyCodePoints", "SourceText", "Component",
        "HasField", "HasSlot", "HasMethod", "HasSlots", "AttrValue", "SlotsListed", "NewRecord", "Present", "ChildOf", "Running", "CurrentRealm",
        "ActiveFunction", "AgentRecord", "SurroundingAgent", "StackEmpty", "IsSuspended", "Child", "ThisNode", "CoveredBy", "NodeContains",
        "GrammarSymbol", "InstanceOf", "IsFinite", "InInterval", "Parity", "Remainder", "XMath", "Negative", "NumberFor", "BigIntFor", "Bitwise",
        "Pi", "TimeConst", "Chain", "CharSetUnion", "CharSetOne", "CharSetUnionAll", "Char", "CharValue", "KeysOrdered",
        "OwnPropertyHas", "OneIndexedList", "ParseGoal", "NewSymbol", "NaNEncoding", "MustCoverChild", "ApproxInteger",
        "TableRowValue", "NewBindingsRecord", "HasBinding", "BindingFor", "AddBinding", "RemoveBinding", "BindingNames", "StrictFromOutside",
        "ClosureArity", "RecordFieldNames",
        "HasParam", "GoalSymbolOf", "InDirectEval",
        "MathFn", "UnicodeNormalize",
    ];
    for x in ENUMS {
        d.enums.intern(x);
    }
    for x in FIELDS {
        d.fields.intern(x);
    }
    for x in SORTS {
        d.sorts.intern(x);
    }
    for x in PRIMS {
        d.prims.intern(x);
    }
    for p in &g.overlay.prims {
        d.prims.intern(&p.name);
    }
    d.sdos.intern("Early Errors");
    let r = g.rules.iter().find(|r| r.cat == "P" && r.name == "new-error").unwrap();
    let els = r.elems.clone();
    d.phrase("P", "new-error", || crate::conv::pieces(&els));
}

pub(crate) fn reading_of(r: &str) -> crate::ast::Reading {
    match r {
        "test262" => crate::ast::Reading::Test262,
        "definition" => crate::ast::Reading::Definition,
        _ => crate::ast::Reading::Proposed,
    }
}

/// Header type-phrase statistics: occurrences parsed and seen, and each distinct phrase's result.
type Stats<'s> = Option<(&'s mut (usize, usize), &'s mut HashMap<String, bool>)>;

/// A header type phrase.
fn parse_ty(cv: &mut Conv, hp: &mut crate::engine::Parser, text: &str) -> Result<TyExpr, String> {
    let toks = crate::token::tokenize(text);
    let tree = hp.parse(&toks, "HT");
    cv.toks = toks;
    cv.text = text.to_string();
    tree.ok_or_else(String::new).and_then(|t| cv.ht(&t))
}

/// A clause's header: kind, parameters and receiver as slots of `cv`'s variables, types parsed.
fn header_of(cv: &mut Conv, hp: &mut crate::engine::Parser, c: &crate::spec::Clause, header: &crate::header::Header, mut stats: Stats) -> Hdr {
    let mut ty = |cv: &mut Conv, text: &str| -> TyExpr {
        let r = parse_ty(cv, hp, text);
        if let Some((occ, distinct)) = stats.as_mut() {
            if r.is_err() && std::env::var("ECMA_HT_FAIL").is_ok() {
                eprintln!("ht-fail\t{text}");
            }
            distinct.insert(text.to_string(), r.is_ok());
            occ.0 += usize::from(r.is_ok());
            occ.1 += 1;
        }
        r.unwrap_or_else(|_| TyExpr::Prose(vec![Part::Text(text.to_string())]))
    };
    let kind = match c.ty.as_deref() {
        Some("abstract operation") => "ao",
        Some("sdo") => "sdo",
        Some("built-in function") => "builtin",
        Some("internal method") => "internalMethod",
        Some("concrete method") => "concreteMethod",
        Some("numeric method") => "numericMethod",
        Some("host-defined abstract operation") => "hostDefined",
        Some("implementation-defined abstract operation") => "implDefined",
        _ => "untyped",
    };
    let mut params = Vec::new();
    for p in &header.params {
        let t = p.ty.as_ref().map(|t| ty(cv, t));
        params.push((cv.vars.slot(&p.name), t, p.optional, p.rest));
    }
    let ret = header.ret.as_ref().map(|t| ty(cv, t));
    let recv = header.recv.as_ref().map(|(r, t)| (cv.vars.slot(r), ty(cv, t)));
    let desc = c.dl_entry("description").map(|d| crate::text::squash(&d)).unwrap_or_default();
    let typing = typing_of(cv, hp, &c.id);
    Hdr { kind, params, ret, recv, desc, typing }
}

/// The overlay's result typing of the clause or phrase `id` (`<emu-result-type>`), parsed without declaring a name.
fn typing_of(cv: &mut Conv, hp: &mut crate::engine::Parser, id: &str) -> Option<TyExpr> {
    let g = cv.g;
    let r = g.overlay.result_types.iter().find(|r| r.clause == id)?;
    let (saved, before) = ((cv.d.clone(), cv.vars.clone()), (sizes(cv.d), cv.vars.names.len()));
    let why = match parse_ty(cv, hp, &r.ty) {
        Ok(t) if (sizes(cv.d), cv.vars.names.len()) == before => return Some(t),
        Ok(_) => "declares a name",
        Err(_) => "is not a header type",
    };
    (*cv.d, cv.vars) = saved;
    cv.d.typing_errors.push(format!("{}: <emu-result-type clause={}>: {:?} {why}", r.file, r.clause, r.ty));
    None
}

/// `t` with each type hole's variable `Var(_, x)` as its position among `pa`'s parameters; none if one is not a parameter.
fn at_positions(t: &TyExpr, pa: &PhraseAlg) -> Option<TyExpr> {
    Some(match t {
        TyExpr::Var(a, x) => TyExpr::Var(a.clone(), pa.hdr.params.iter().position(|q| q.0 == *x)?),
        TyExpr::ListOf(a, x) => TyExpr::ListOf(a.clone(), Box::new(at_positions(x, pa)?)),
        TyExpr::Union(f, c, ts) => TyExpr::Union(*f, *c, ts.iter().map(|t| at_positions(t, pa)).collect::<Option<_>>()?),
        TyExpr::Completion(x) => TyExpr::Completion(match x {
            Some(x) => Some(Box::new(at_positions(x, pa)?)),
            None => None,
        }),
        t => t.clone(),
    })
}

/// Each expression phrase's result typing (`<emu-result-type>`), a type hole as its position.
fn phrase_typings(d: &Decls, pas: &[PhraseAlg]) -> HashMap<crate::ast::Id, TyExpr> {
    let mut out = HashMap::new();
    for (p, ph) in d.phrases.iter().enumerate() {
        let Some(crate::decls::Meaning::Alg(c)) = &ph.meaning else { continue };
        let Some(pa) = pas.iter().find(|x| x.clause == *c) else { continue };
        if let Some(t) = pa.hdr.typing.as_ref().and_then(|t| at_positions(t, pa)) {
            out.insert(p, t);
        }
    }
    out
}

/// Each type phrase's bound: the type its test's leading `If _v_ is (not) a T, return …` steps admit.
fn type_bounds(d: &Decls, pas: &[PhraseAlg]) -> HashMap<crate::ast::Id, TyExpr> {
    use crate::ast::{AltForm, Body, Cond, ConnForm, Expr, Pred, ValLit};
    let mut out = HashMap::new();
    for (p, ph) in d.phrases.iter().enumerate() {
        let Some(crate::decls::Meaning::Alg(c)) = &ph.meaning else { continue };
        if matches!(ph.cat, "Step" | "P" | "CA" | "PRED") {
            continue;
        }
        let Some(pa) = pas.iter().find(|x| x.clause == *c) else { continue };
        let Some(&(v, ..)) = pa.hdr.params.last() else { continue };
        // the types a step `If v is (not) T…, return b.` tests, for b
        let test = |st: &Stmt, b: bool| -> Option<Vec<TyExpr>> {
            let Stmt::If(Cond::Preds(Expr::Var(x), Pred::IsTy(neg, _, ts), more), body, arms, None) = st else { return None };
            let ret = match body {
                Body::Inline(s) => Some(&**s),
                Body::Block(ns) if ns.len() == 1 => Some(&ns[0].stmt),
                Body::Block(_) => None,
            };
            let lit = if b { ValLit::True } else { ValLit::False };
            (*x == v && more.is_empty() && arms.is_empty() && *neg != b && matches!(ret, Some(Stmt::Ret(Some(Expr::Val(r)))) if *r == lit)).then(|| ts.clone())
        };
        let ts = match pa.body.split_last() {
            Some((last, guards)) if !guards.is_empty() && matches!(last.stmt, Stmt::Ret(Some(Expr::Val(ValLit::False)))) && guards.iter().all(|n| test(&n.stmt, true).is_some()) => {
                guards.iter().flat_map(|n| test(&n.stmt, true).unwrap_or_default()).collect()
            }
            _ => match pa.body.first().and_then(|n| test(&n.stmt, false)) {
                Some(ts) => ts,
                None => continue,
            },
        };
        let t = if ts.len() == 1 { ts[0].clone() } else { TyExpr::Union(AltForm::Or, ConnForm::Plain, ts) };
        if let Some(t) = at_positions(&t, pa) {
            out.insert(p, t);
        }
    }
    out
}

/// The sizes of the tables a parse may add to.
fn sizes(d: &Decls) -> [usize; 12] {
    [d.clauses.names.len(), d.fields.names.len(), d.enums.names.len(), d.sdos.names.len(), d.nts.names.len(), d.prods.names.len(), d.prims.names.len(), d.sorts.names.len(), d.methods.names.len(), d.phrases.len(), d.reasons.names.len(), d.sig_errors.len()]
}

/// The signature types the header-type grammar parses over a copy of `d` without declaring a name.
fn sig_tys(g: &Grammar, d: &Decls, env: &Env, hp: &mut crate::engine::Parser) -> HashMap<String, TyExpr> {
    let (anchors, rows) = (HashMap::new(), HashMap::new());
    let mut out = HashMap::new();
    let mut scratch = d.clone();
    for text in crate::sig::texts(g, &d.prims.names) {
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
            d: &mut scratch,
            env,
            vars: Vars::default(),
            rows: &rows,
            toks: Vec::new(),
            text: String::new(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: 0,
            clause: String::new(),
        };
        let t = parse_ty(&mut cv, hp, &text);
        if sizes(&scratch) != sizes(d) {
            scratch = d.clone();
        } else if let Ok(t) = t {
            out.insert(text, t);
        }
    }
    out
}

/// The overlay's algorithms, in order: phrase meanings, then sort tests (id, file, steps).
fn overlay_algs(g: &Grammar) -> Vec<(String, String, &crate::overlay::PhraseAlg)> {
    let phrases = g.overlay.phrases.iter().filter_map(|p| p.alg.as_ref().map(|a| (p.id.clone(), p.file.clone(), a)));
    let sorts = g.overlay.sorts.iter().filter_map(|s| match &s.test {
        crate::overlay::SortTest::Steps(a) => Some((sort_alg_id(&s.name), format!("sorts.emu, {}", s.clause), a)),
        _ => None,
    });
    let ops = g.overlay.ops.iter().map(|o| (o.id.clone(), o.file.clone(), &o.alg));
    phrases.chain(sorts).chain(ops).collect()
}

/// Steps outside spec.html as an algorithm of no clause.
fn loose_alg(raw: &str, base: usize, close: usize, steps: &[Step]) -> crate::spec::Alg {
    crate::spec::Alg { pos: 0, line: 0, attrs: String::new(), raw: raw.to_string(), clause: None, idx: 0, prod: None, base, steps: steps.to_vec(), close_indent: close, tmpl: false }
}

/// The SDO a row belongs to: its clause's, or the one its annex clause extends.
fn row_op(sp: &Spec, a: &Alg) -> String {
    a.ext.as_ref().map_or_else(|| sp.clauses[a.clause].op().unwrap_or_default(), |e| e.op.clone())
}

/// The one nonterminal the right-hand sides `prods` share, and whether each is that nonterminal alone.
fn sole_nt(gl: &jsgrammar::gl::Gl, prods: &[usize]) -> Option<(String, bool)> {
    let mut out: Option<(String, bool)> = None;
    for &p in prods {
        let shape = gl.shape(&gl.prods[p]);
        let [nt] = &shape.iter().filter(|x| gl.nt(x).is_some()).collect::<Vec<_>>()[..] else { return None };
        if shape.iter().any(|x| gl.nt(x).is_none() && !x.starts_with('`')) || out.as_ref().is_some_and(|(n, _)| n != *nt) {
            return None;
        }
        let chain = shape.len() == 1 && out.as_ref().is_none_or(|o| o.1);
        out = Some(((*nt).clone(), chain));
    }
    out
}

/// Whether SDO `sdo` has no row on any production of `nt`, nor of the nonterminals its chain productions name.
fn no_rows(gl: &jsgrammar::gl::Gl, sp: &Spec, algs: &[Alg], sdo: &str, nt: &str, seen: &mut Vec<String>) -> bool {
    if seen.iter().any(|x| x == nt) {
        return true;
    }
    seen.push(nt.to_string());
    let Some(k) = gl.nt(nt) else { return false };
    gl.prods.iter().enumerate().filter(|(_, p)| p.lhs == k).all(|(i, p)| {
        let shape = gl.shape(p);
        !algs.iter().any(|a| a.prods.contains(&i) && row_op(sp, a) == sdo)
            && match &shape[..] {
                [x] if gl.nt(x).is_some() => no_rows(gl, sp, algs, sdo, x, seen),
                _ => true,
            }
    })
}

/// The overlay's own algorithms, by entry id: phrase algorithms, sort tests, operations, and
/// each reading alternative (`erratum/clause@step/reading`).
pub fn overlay_steps(g: &Grammar) -> Vec<(String, crate::spec::Alg)> {
    let mut out: Vec<(String, crate::spec::Alg)> = overlay_algs(g).into_iter().map(|(id, _, pa)| (id, loose_alg(&pa.raw, pa.base, pa.close, &pa.steps))).collect();
    for r in &g.overlay.rows {
        out.push((r.id.clone(), loose_alg(&r.alg.raw, r.alg.base, r.alg.close, &r.alg.steps)));
    }
    for e in &g.overlay.errata {
        for r in &e.readings {
            for x in &r.alts {
                out.push((format!("{}/{}@{}/{}", e.id, r.clause, r.step, x.key()), loose_alg(&x.raw, x.base, x.close, &x.steps)));
            }
        }
    }
    out
}

/// An overlay abstract operation's clause, as spec.html's are scanned.
fn op_clause(o: &crate::overlay::Op) -> crate::spec::Clause {
    crate::spec::Clause { id: o.id.clone(), ty: Some(o.ty.clone()), h1: o.h1.clone(), dl: o.dl.clone(), ..Default::default() }
}

/// A sort's test algorithm's id: `sort-` and its name, hyphenated.
pub fn sort_alg_id(name: &str) -> String {
    format!("sort-{}", name.replace(' ', "-"))
}

/// Each overlay sort's definition: its supersort, its record kind, and its test on the
/// subject _v_ (a primitive, an operation, or its steps' algorithm).
fn sort_defs(g: &Grammar, d: &mut Decls, env: &Env) {
    use crate::decls::{Meaning, PArg, SortDef};
    for s in &g.overlay.sorts {
        let id = d.sorts.intern(&s.name);
        let sup = s.sup.iter().map(|x| d.sort_of(x).0).collect();
        let test = match &s.test {
            crate::overlay::SortTest::None => None,
            crate::overlay::SortTest::Prim(p, args, neg) => {
                let prim = d.prims.intern(p);
                let args = args
                    .iter()
                    .map(|a| match a {
                        crate::overlay::Arg::Var(_) => PArg::Subject,
                        crate::overlay::Arg::Enum(e) => PArg::Enum(d.enums.intern(e)),
                        crate::overlay::Arg::Field(f) => PArg::Field(d.fields.intern(f)),
                    })
                    .collect();
                Some(Meaning::Prim { prim, args, neg: *neg })
            }
            crate::overlay::SortTest::Op(op) => Some(Meaning::Alg(*env.ops.get(op).unwrap_or_else(|| panic!("sort {}: alg={op} names no operation", s.name)))),
            crate::overlay::SortTest::Steps(_) => Some(Meaning::Alg(d.clauses.get(&sort_alg_id(&s.name)).expect("a sort algorithm's clause"))),
        };
        if d.sort_defs.len() <= id {
            d.sort_defs.resize(id + 1, None);
        }
        let ctx = crate::conv::sort_context(g, d, id).map(|x| x.0);
        d.sort_defs[id] = Some(SortDef { sup, test, record: s.record, ctx });
    }
}

/// The declarations every conversion starts from, and the name environment.
pub fn base(html: &str, sp: &Spec, g: &Grammar) -> (Decls, Env) {
    let mut d = Decls::default();
    if let Some(k) = &g.overlay.clause_ids {
        d.clauses.seed(k);
        d.clause_was = k.was();
        d.ops = vec![String::new(); d.clauses.names.len()];
    }
    if let Some(k) = &g.overlay.sdo_ids {
        d.sdos.seed(k);
    }
    if let Some(k) = &g.overlay.method_ids {
        d.methods.seed(k);
    }
    if let Some(k) = &g.overlay.reason_ids {
        d.reasons.seed(k);
    }
    if let Some(k) = &g.overlay.note_ids {
        d.notes.seed(k);
    }
    d.freeze_phrases(&g.overlay.phrase_ids);
    for n in &g.overlay.prim_ids {
        d.prims.intern(n);
    }
    for n in &g.overlay.sort_ids {
        d.sorts.intern(n);
    }
    for n in &g.overlay.field_ids {
        d.fields.intern(n);
    }
    for n in &g.overlay.enum_ids {
        d.enums.intern(n);
    }
    seed_known(&mut d, g);
    // the clauses the kept table has first, so that an id an `oldids` names is free only if no clause has it
    let mut cids = vec![usize::MAX; sp.clauses.len()];
    for (k, c) in sp.clauses.iter().enumerate() {
        if d.clauses.get(&c.id).is_some() {
            cids[k] = d.intern_clause(&c.id, &[]);
        }
    }
    for (k, c) in sp.clauses.iter().enumerate() {
        if cids[k] == usize::MAX {
            cids[k] = d.intern_clause(&c.id, &c.oldids);
        }
        let op = c.op().unwrap_or_default();
        if !op.is_empty() && c.ty.as_deref() == Some("sdo") {
            d.sdos.intern(&op);
        }
        d.set_op(cids[k], op);
    }
    d.set_cids(cids);
    for (ci, c) in sp.clauses.iter().enumerate().filter(|(_, c)| c.ty.as_deref() == Some("sdo")) {
        if !html[c.start..c.end].contains("implicitly has the following default definition of") {
            continue;
        }
        let sdo = d.sdos.intern(&c.op().unwrap_or_default());
        if let Some(a) = sp.algs.iter().find(|a| a.clause == Some(ci) && a.prod.is_none()) {
            d.sdo_defaults.push((sdo, d.cid(ci), a.idx));
        }
    }
    let (ctx, algs): (Vec<_>, Vec<_>) = overlay_algs(g).into_iter().map(|x| x.0).partition(|id| g.overlay.sorts.iter().any(|s| s.context.as_ref() == Some(id)));
    for id in algs {
        let c = d.intern_clause(&id, &[]);
        d.set_op(c, g.overlay.ops.iter().find(|o| o.id == id).and_then(|o| op_clause(o).op()).unwrap_or_default());
    }
    for r in &g.overlay.rows {
        let c = d.intern_clause(&r.id, &[]);
        d.set_op(c, String::new());
    }
    // the sorts' context phrases' algorithms come last, so that adding one shifts no other id
    for id in ctx {
        let c = d.intern_clause(&id, &[]);
        d.set_op(c, String::new());
    }
    d.declare_sorts(SORTS.iter().copied().chain(g.overlay.sorts.iter().map(|s| s.name.as_str())));
    for s in equation_sdos(html) {
        d.sdos.intern(&s);
    }
    let mut env = env(html, sp, &d.cids, &g.overlay.grammar_ids);
    for o in &g.overlay.ops {
        let c = op_clause(o);
        env.ops.insert(c.op().unwrap_or_default(), d.clauses.get(&o.id).expect("an overlay operation's clause"));
    }
    for (n, c) in &g.overlay.steps_names {
        let ci = sp.clauses.iter().position(|x| &x.id == c).unwrap_or_else(|| panic!("emu-steps-name {n}: no clause {c}"));
        assert!(sp.algs.iter().any(|a| a.clause == Some(ci) && a.idx == 0), "emu-steps-name {n}: {c} has no algorithm");
        let i = d.clauses.get(c).expect("a spec clause's id");
        if d.ops[i].is_empty() {
            d.ops[i] = n.clone();
        }
        env.ops.insert(n.clone(), i);
    }
    // by kept id (jsgrammar `ids`): the names of the ids up to the last this grammar (without json.emu's) has
    for n in env.gl.prod_names() {
        d.prods.intern(&n);
    }
    for n in env.gl.live_nts() {
        d.nts.intern(n);
    }
    for p in env.gl.live_params() {
        d.params.intern(p);
    }
    d.prod_ids = env.gl.prod_ids.clone();
    if let Some(k) = &g.overlay.table_ids {
        d.tables.seed(k);
    }
    d.table_ids = env.table_names.iter().map(|n| d.tables.intern(n)).collect();
    (d, env)
}

/// An anchor's index for a step a multi-step reading covers after its first.
pub const COVERED: usize = usize::MAX;

/// The errata the machine reads outside any step (`Ecma.Known`'s erratum ids, Syntax.lean): the first
/// errata of the overlay, in this order.
/// The index among the errata's orphan rows (`<emu-orphan-row>`, in order) of the one at clause `cid` with
/// the grammar key `key`.
fn orphan_of(g: &Grammar, cid: &str, key: &str) -> Option<usize> {
    let squash = |t: &str| t.split_whitespace().collect::<Vec<_>>().join(" ");
    g.overlay.errata.iter().flat_map(|e| e.orphans.iter()).position(|o| o.clause == cid && squash(&o.grammar) == squash(key))
}

/// The errata `Ecma.Known` names, at their kept ids (1, MustCoverOtherRules, is retired).
pub const KNOWN_ERRATA: &[(usize, &str)] = &[(0, "UnitChainChild"), (2, "StringValueReservedWord"), (3, "LookaheadSourceTokens"),
    (4, "HTMLCloseCommentToken"), (5, "AnnexBRegExpOrder"), (6, "AnnexBGroupCount"), (7, "AnnexBModifierEarlyErrors"), (8, "CoveredNodeParent")];

pub fn build(html: &str, sp: &Spec, g: &Grammar, rows: &[Row]) -> Data {
    let (mut d, env) = base(html, sp, g);
    if let Some(k) = &g.overlay.erratum_ids {
        d.errata_table.seed(k);
    }
    d.erratum_ids = g.overlay.errata.iter().map(|e| d.errata_table.intern(&e.name)).collect();
    // errata: each anchored step, and its readings' steps parsed as steps of its algorithm
    let mut anchors: crate::conv::Anchors = HashMap::new();
    let mut covered = Vec::new();
    let mut extra: Vec<Row> = Vec::new();
    let mut anchor_errors = Vec::new();
    let mut stops = crate::stops::StopSites::default();
    // an overlay that names any of them (the repository's) has each at its id
    let known = g.overlay.errata.iter().any(|e| KNOWN_ERRATA.iter().any(|(_, n)| *n == e.name));
    let mut names = std::collections::HashSet::new();
    for e in &g.overlay.errata {
        if !names.insert(e.name.as_str()) {
            anchor_errors.push(format!("{}: a second erratum named {}", e.id, e.name));
        }
    }
    for &(i, n) in KNOWN_ERRATA {
        if known && d.errata_table.get(n) != Some(i) {
            anchor_errors.push(format!("erratum {i} is not {n}, which Ecma.Known reads at that id"));
        }
    }
    d.permanent = g.overlay.permanent.iter().map(|p| (p.clause.clone(), p.step.clone(), p.class.label())).collect();
    for (ei, e) in g.overlay.errata.iter().enumerate() {
        d.errata.push(e.name.clone());
        d.errata_ids.push(e.id.clone());
        let parity = match e.resolution.as_str() {
            "test262" => crate::ast::Reading::Test262,
            "literal" => crate::ast::Reading::Literal,
            "definition" => crate::ast::Reading::Definition,
            _ => crate::ast::Reading::Proposed,
        };
        d.parity.push(parity);
        let valid_readings = if e.resolution == "definition" {
            Vec::new()
        } else if e.switch == "none" {
            vec![parity]
        } else {
            let (mut has_t, mut has_p) = (false, false);
            for a in &e.readings {
                for alt in &a.alts {
                    for r in alt.readings() {
                        if r == "test262" { has_t = true; }
                        if r == "proposed" { has_p = true; }
                    }
                }
            }
            for rule in &e.rules {
                for (r, _) in &rule.alts {
                    for w in r.split(' ') {
                        if w == "test262" { has_t = true; }
                        if w == "proposed" { has_p = true; }
                    }
                }
            }
            for r in &e.rule_readings {
                if r == "test262" { has_t = true; }
                if r == "proposed" { has_p = true; }
            }
            if g.overlay.rows.iter().any(|row| row.erratum.as_deref() == Some(e.name.as_str())) {
                has_t = true;
                has_p = true;
            }
            if !has_t && !has_p {
                has_t = true;
                has_p = true;
            }
            let mut rs = vec![crate::ast::Reading::Literal];
            if has_t { rs.push(crate::ast::Reading::Test262); }
            if has_p { rs.push(crate::ast::Reading::Proposed); }
            rs
        };
        d.erratum_readings.push(valid_readings);
        // each stop names a step of its clause (`-`: a clause with no algorithm), and a clause as caller
        for st in &e.stops {
            let cl = d.clauses.get(&st.clause);
            let algs: Vec<_> = sp.algs.iter().filter(|a| !a.tmpl && a.clause.is_some_and(|c| Some(d.cid(sp.home(c))) == cl)).collect();
            if cl.is_none() {
                anchor_errors.push(format!("{}: stops at {}, no clause", e.id, st.text()));
            } else if st.path == "-" && !algs.is_empty() {
                anchor_errors.push(format!("{}: stops at {}, outside the steps of a clause with steps", e.id, st.text()));
            } else if st.path != "-" && !algs.iter().any(|a| crate::spec::labelled(&a.steps).iter().any(|(p, _)| *p == st.path)) {
                anchor_errors.push(format!("{}: stops at {}, no such step", e.id, st.text()));
            }
            if st.caller.as_ref().is_some_and(|c| d.clauses.get(c).is_none()) {
                anchor_errors.push(format!("{}: stops at {}, no caller clause", e.id, st.text()));
            }
            // a step's checks are labelled at the step, or at its caller's calls of the clause; the
            // job loop's check per clause whose Jobs it checks
            match (&st.caller, cl, st.path.as_str()) {
                (Some(k), Some(_), "-") if st.clause == "sec-jobs" => {
                    if let Some(k) = d.clauses.get(k) {
                        d.job_errata.push((k, ei));
                    }
                }
                (None, _, "-") if st.clause == "sec-jobs" => anchor_errors.push(format!("{}: stops at {}, the job loop with no caller", e.id, st.text())),
                (_, _, "-") => {}
                (Some(k), Some(c), _) => {
                    stops.calls.entry(k.clone()).or_default().push((c, ei));
                    for a in &algs {
                        if let Some((_, s)) = crate::spec::labelled(&a.steps).into_iter().find(|(p, _)| *p == st.path) {
                            stops.steps.entry(s as *const Step).or_insert(None);
                        }
                    }
                }
                (None, _, _) => {
                    for a in &algs {
                        if let Some((_, s)) = crate::spec::labelled(&a.steps).into_iter().find(|(p, _)| *p == st.path) {
                            stops.steps.insert(s as *const Step, Some(ei));
                        }
                    }
                }
                (Some(_), None, _) => {}
            }
            d.erratum_stops.push((ei, st.clause.clone(), st.path.clone(), st.caller.clone()));
        }
        for (k, r) in e.readings.iter().enumerate() {
            let cl = d.clauses.get(&r.clause);
            // a parameterized clause's reading reads each of its instances
            let found: Vec<_> = sp.algs.iter().filter(|a| !a.tmpl && a.clause.is_some_and(|c| Some(d.cid(sp.home(c))) == cl)).filter_map(|a| {
                crate::spec::labelled(&a.steps).into_iter().find(|(p, s)| *p == r.step && crate::text::sha256(&s.text) == r.hash).map(|(_, s)| (a, s))
            }).collect();
            if found.is_empty() {
                anchor_errors.push(format!("{}: no step {} with that text hash in {}", e.id, r.step, r.clause));
            }
            for (a, s) in found {
                for (st, h) in &r.also {
                    if !crate::spec::labelled(&a.steps).iter().any(|(p, s)| p == st && crate::text::sha256(&s.text) == *h) {
                        anchor_errors.push(format!("{}: no step {st} with that text hash in {}", e.id, r.clause));
                    }
                }
                let alts: Vec<_> = r.alts.iter().flat_map(|x| x.readings().map(|q| (reading_of(q), x.steps.as_slice()))).collect();
                // a later sibling step the reading also replaces: under each reading, no steps
                let below = format!("{}.", r.step);
                for (p, t) in crate::spec::labelled(&a.steps) {
                    if !p.starts_with(&below) && r.also.iter().any(|(st, h)| *st == p && crate::text::sha256(&t.text) == *h) {
                        covered.push((t as *const Step, (ei, COVERED, alts.iter().map(|(q, _)| (*q, &[][..])).collect())));
                    }
                }
                anchors.entry(s as *const Step).or_default().push((ei, k, alts));
                for x in &r.alts {
                    extra.extend(crate::classify::classify_steps(g, a, &x.steps));
                }
            }
        }
    }
    // a step with an erratum of its own keeps it
    for (t, x) in covered {
        anchors.entry(t).or_insert_with(|| vec![x]);
    }
    let by_step: HashMap<*const Step, &Row> = rows.iter().chain(extra.iter()).map(|r| (r.step as *const Step, r)).collect();
    let mut algs = Vec::new();
    let mut unresolved = Vec::new();
    let mut hp = crate::engine::Parser::new(g, 99, false);
    let mut occ = (0usize, 0usize);
    let mut distinct: HashMap<String, bool> = HashMap::new();
    let mut seen = std::collections::HashSet::new();
    // each table a `the value that … corresponds to in` step refers to: its referrer's variables
    let mut referrers: HashMap<usize, Vec<String>> = HashMap::new();
    // tables whose step cells were numbered without a referrer
    let mut unreferred = std::collections::HashSet::new();
    for (ai, a) in sp.algs.iter().enumerate() {
        if a.example() || a.tmpl {
            continue;
        }
        let Some(cl) = a.clause else { continue };
        let (keys, prods) = match &a.prod {
            Some(k) => (vec![k.clone()], env.gl.resolve(k, &sp.clauses[cl].id).unwrap_or_else(|e| panic!("spec.html:{}: {e}", a.line))),
            None => (vec![], vec![]),
        };
        let ext = extends(html, sp, a).filter(|_| a.prod.is_some());
        // an annex row reads its SDO's parameters, as the SDO's own rows do
        let hcl = ext.as_ref().map_or(cl, |e| e.clause);
        let mut header = crate::header::parse(&sp.clauses[hcl]);
        if header.params.is_empty() && sp.clauses[cl].ty.as_deref() == Some("built-in function") {
            header.params = crate::header::prose_params(&sp.clauses[cl].body(html));
        }
        if header.params.is_empty() && sp.clauses[cl].ty.is_none() && a.prod.is_some() {
            header.params = crate::header::extended_params(&html[sp.clauses[cl].start..a.pos], &sp.clauses).unwrap_or_else(|e| panic!("spec.html:{}: {e}", a.line));
        }
        let mut vars = Vars::default();
        if sp.clauses[cl].ty.as_deref() == Some("built-in function") {
            vars.slot("this value");
            vars.slot("NewTarget");
        }
        if let Some((r, _)) = &header.recv {
            vars.slot(r);
        }
        for p in &header.params {
            vars.slot(&p.name);
        }
        // a step cell of such a table: numbered after its referrer
        if let Some(t) = env.table_spans.iter().position(|r| r.contains(&a.pos)) {
            match referrers.get(&t) {
                Some(names) => {
                    for n in names {
                        vars.slot(n);
                    }
                }
                None => {
                    unreferred.insert(t);
                }
            }
        }
        let mut cv = Conv {
            open: Vec::new(),
            rhs: Default::default(),
            lhs: Default::default(),
            narrow: Vec::new(),
            symbols: false,
            channel: crate::ast::Channel::Pending,
            anchors: &anchors,
            stops: Some(&stops),
            readings: Vec::new(),
            g,
            d: &mut d,
            env: &env,
            vars,
            rows: &by_step,
            toks: Vec::new(),
            text: String::new(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: a.base,
            clause: sp.clauses[cl].id.clone(),
        };
        cv.set_rhs(&keys);
        let body = cv.steps(&a.steps);
        let first = seen.insert(cl);
        let hdr = header_of(&mut cv, &mut hp, &sp.clauses[hcl], &header, if first { Some((&mut occ, &mut distinct)) } else { None });
        let (vars, exceptions, closures, readings) = (cv.vars, cv.exceptions, cv.closures, cv.readings);
        unresolved.extend(cv.unresolved);
        for (_, why) in &exceptions {
            assert!(!why.starts_with(crate::conv::FRAME_ERR), "spec.html:{}: {why}", a.line);
        }
        let builtin = sp.clauses[cl].ty.as_deref() == Some("built-in function");
        assert!(builtin || crate::checks::frame_reads(&body) == 0, "spec.html:{}: the *this* value, NewTarget or the arguments List read outside every closure", a.line);
        for t in crate::checks::table_steps(&body).into_iter().collect::<std::collections::BTreeSet<_>>() {
            assert!(!unreferred.contains(&t), "spec.html:{}: a table's step cells come before the step that refers to it", a.line);
            assert!(referrers.insert(t, vars.names.clone()).is_none(), "spec.html:{}: a table with a second referrer", a.line);
        }
        algs.push(Alg { alg: ai, keys, prods, clause: cl, idx: a.idx, hdr, vars, body, closures, readings, exceptions, ext });
    }
    // an annex row shares a main row's production exactly where its clause says the rules are replaced
    for a in algs.iter().filter(|a| a.ext.is_some()) {
        let e = a.ext.as_ref().unwrap();
        let op = &e.op;
        let clash = algs.iter().any(|m| {
            m.ext.is_none() && m.hdr.kind == "sdo" && sp.clauses[m.clause].op().as_deref() == Some(op.as_str()) && m.prods.iter().any(|p| a.prods.contains(p))
        });
        assert!(clash == e.replaces, "spec.html:{}: an annex row of {op} {} a main row's production, {} \"are replaced\"", sp.algs[a.alg].line, if clash { "on" } else { "on no" }, if clash { "not under" } else { "under" });
    }
    // each caller-conditioned stop labels a call in its caller
    for (k, cs) in &stops.calls {
        for &(c, e) in cs {
            if !stops.called.borrow().iter().any(|(k2, c2, e2)| k2 == k && *c2 == c && *e2 == e) {
                anchor_errors.push(format!("{}: stops under {k}, which calls {} nowhere", d.errata_ids[e], d.clauses.names[c]));
            }
        }
    }
    let mut phrase_algs = Vec::new();
    for (id, file, pa) in overlay_algs(g) {
        let clause = d.clauses.get(&id).expect("an overlay algorithm's clause");
        let alg = loose_alg(&pa.raw, pa.base, pa.close, &pa.steps);
        let rows = crate::classify::classify_steps(g, &alg, &alg.steps);
        let by_step: HashMap<*const Step, &Row> = rows.iter().map(|r| (r.step as *const Step, r)).collect();
        let op = g.overlay.ops.iter().find(|o| o.id == id).map(op_clause);
        let header = op.as_ref().map(crate::header::parse);
        let mut vars = Vars::default();
        let phrase = g.overlay.phrases.iter().find(|q| q.id == id);
        let layout = phrase.map(|q| g.phrase_layout(q)).unwrap_or_default();
        let occ = phrase.map(|q| q.vars()).unwrap_or_default();
        let mut named = pa.params.iter();
        let mut order: Vec<(String, Option<&String>)> = Vec::new();
        let mut h = 0;
        for (k, &w) in layout.iter().enumerate() {
            if w {
                order.push((format!("choice {k}"), None));
                continue;
            }
            // a repeated variable's later holes bind unused parameters
            if occ.get(h).is_some_and(|v| occ[..h].contains(v)) {
                order.push((format!("repeat {k}"), None));
            } else if let Some((name, t)) = named.next() {
                order.push((name.clone(), Some(t)));
            }
            h += 1;
        }
        order.extend(named.map(|(name, t)| (name.clone(), Some(t))));
        if op.as_ref().is_some_and(|c| c.ty.as_deref() == Some("built-in function")) {
            vars.slot("this value");
            vars.slot("NewTarget");
        }
        match &header {
            Some(h) => h.params.iter().for_each(|p| {
                vars.slot(&p.name);
            }),
            None => order.iter().for_each(|(name, _)| {
                vars.slot(name);
            }),
        }
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
            d: &mut d,
            env: &env,
            vars,
            rows: &by_step,
            toks: Vec::new(),
            text: String::new(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: alg.base,
            clause: id.clone(),
        };
        let body = cv.steps(&alg.steps);
        let mut hdr = match (&op, &header) {
            (Some(c), Some(h)) => header_of(&mut cv, &mut hp, c, h, None),
            _ => {
                let mut params = Vec::new();
                for (name, t) in &order {
                    let slot = cv.vars.slot(name);
                    let t = t.map(|t| parse_ty(&mut cv, &mut hp, t).unwrap_or_else(|_| TyExpr::Prose(vec![Part::Text(t.clone())])));
                    params.push((slot, t, false, false));
                }
                Hdr { kind: "ao", params, ret: None, recv: None, desc: String::new(), typing: None }
            }
        };
        if hdr.typing.is_none() {
            hdr.typing = typing_of(&mut cv, &mut hp, &id);
        }
        unresolved.extend(cv.unresolved);
        let (vars, exceptions, closures) = (cv.vars, cv.exceptions, cv.closures);
        phrase_algs.push(PhraseAlg { id, file, clause, alg, hdr, vars, body, closures, exceptions });
    }
    // the rows the overlay's readings add: each for productions no row of its SDO has
    let mut reading_rows = Vec::new();
    let mut row_errors = Vec::new();
    for rr in &g.overlay.rows {
        // the SDO's clause, or an annex clause that extends it (its header that of the SDO's clause)
        let cl = sp.clauses.iter().position(|c| c.id == rr.clause);
        let ext = cl.filter(|&c| sp.clauses[c].ty.as_deref() != Some("sdo")).and_then(|c| extends_at(html, sp, c, own_end(sp, c)));
        let Some(cl) = cl.filter(|&c| sp.clauses[c].ty.as_deref() == Some("sdo") || ext.is_some()) else {
            row_errors.push(format!("{}: no SDO clause {}", rr.id, rr.clause));
            continue;
        };
        let hcl = ext.as_ref().map_or(cl, |e| e.clause);
        let sdo = sp.clauses[hcl].op().unwrap_or_default();
        let prods = match env.gl.resolve(&rr.grammar, &rr.grammar_clause) {
            Ok(ps) if !ps.is_empty() => ps,
            Ok(_) => {
                row_errors.push(format!("{}: {} names no production", rr.id, rr.grammar));
                continue;
            }
            Err(e) => {
                row_errors.push(format!("{}: {e}", rr.id));
                continue;
            }
        };
        // an SDO with a default definition has a meaning for every production already, but for the
        // productions of an annex grammar-clause
        let annex_prods = sp.clauses.iter().find(|c| c.id == rr.grammar_clause).is_some_and(|c| c.number.starts_with(|x: char| x.is_ascii_uppercase()));
        if !annex_prods && d.sdos.get(&sdo).is_some_and(|s| d.sdo_defaults.iter().any(|x| x.0 == s)) {
            row_errors.push(format!("{}: {sdo} has a default definition", rr.id));
            continue;
        }
        let has = |a: &Alg| row_op(sp, a) == sdo && a.prods.iter().any(|p| prods.contains(p));
        if algs.iter().any(has) {
            row_errors.push(format!("{}: {sdo} already has a row for {}", rr.id, rr.grammar));
            continue;
        }
        let alg = loose_alg(&rr.alg.raw, rr.alg.base, rr.alg.close, &rr.alg.steps);
        // an erratum's row: its literal reading is the SDO of the sole nonterminal, the chain production's rule;
        // a unit chain, or a chain with terminals whose nonterminal's chain has no row. An erratum with one reading
        // (`switch="none"`) has its row as that reading: its literal text, no row at all, is not run.
        let erratum = match &rr.erratum {
            Some(n) if g.overlay.errata.iter().any(|e| &e.name == n && e.switch == "none") => None,
            Some(n) => match (g.overlay.errata.iter().position(|e| &e.name == n), sole_nt(&env.gl, &prods)) {
                (Some(ei), Some((nt, chain))) if (chain || no_rows(&env.gl, sp, &algs, &sdo, &nt, &mut Vec::new())) && crate::header::parse(&sp.clauses[hcl]).params.is_empty() => {
                    let pad = " ".repeat(rr.alg.base);
                    let raw = format!("\n{pad}1. Return {sdo} of |{nt}|.\n{}", " ".repeat(rr.alg.close));
                    let (base, steps, close) = crate::spec::step_tree(&raw).expect("a chain rule's step");
                    Some((ei, loose_alg(&raw, base, close, &steps)))
                }
                _ => {
                    row_errors.push(format!("{}: an erratum's row is for a chain production, a unit chain or one with terminals whose nonterminal's chain has no row, of an SDO without parameters", rr.id));
                    continue;
                }
            },
            None => None,
        };
        let mut rows = crate::classify::classify_steps(g, &alg, &alg.steps);
        if let Some((_, lit)) = &erratum {
            rows.extend(crate::classify::classify_steps(g, lit, &lit.steps));
        }
        let by_step: HashMap<*const Step, &Row> = rows.iter().map(|r| (r.step as *const Step, r)).collect();
        let header = crate::header::parse(&sp.clauses[hcl]);
        let mut vars = Vars::default();
        for p in &header.params {
            vars.slot(&p.name);
        }
        let keys = vec![rr.grammar.clone()];
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
            d: &mut d,
            env: &env,
            vars,
            rows: &by_step,
            toks: Vec::new(),
            text: String::new(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: alg.base,
            clause: rr.grammar_clause.clone(),
        };
        cv.set_rhs(&keys);
        let mut body = cv.steps(&alg.steps);
        if let Some((ei, lit)) = &erratum {
            let Some(Node { attrs, stmt }) = cv.steps(&lit.steps).into_iter().next() else { unreachable!() };
            body = vec![Node { attrs, stmt: Stmt::Readings(*ei, Box::new(stmt), vec![(crate::ast::Reading::Test262, body.clone()), (crate::ast::Reading::Proposed, body)]) }];
        }
        unresolved.extend(cv.unresolved);
        let (vars, exceptions, closures) = (cv.vars, cv.exceptions, cv.closures);
        let clause = d.clauses.get(&rr.id).expect("a row reading's clause");
        let erratum = erratum.map(|x| x.0);
        reading_rows.push(ReadingRow { id: rr.id.clone(), file: rr.file.clone(), clause, sdo, keys, prods, alg, vars, body, closures, exceptions, erratum, annex: ext.is_some() });
    }
    anchor_errors.extend(row_errors.iter().cloned());
    sort_defs(g, &mut d, &env);
    let mut eqs = Vec::new();
    let mut orphans_met = vec![false; g.overlay.errata.iter().map(|e| e.orphans.len()).sum()];
    for (k, er) in crate::classify::classify_eqs(sp, g).iter().enumerate() {
        let e = &sp.eqs[k];
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
            d: &mut d,
            env: &env,
            vars: Vars::default(),
            rows: &by_step,
            toks: er.toks.clone(),
            text: e.text.clone(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: 0,
            clause: sp.clauses[e.clause].id.clone(),
        };
        let r = match &er.tree {
            Some(t) => cv.equation(t),
            None => Err("an equation with no form".to_string()),
        };
        let (sdo, prods, body, exception) = match r {
            Ok((sdo, prods, body)) => (sdo, prods, body, None),
            Err(why) => (0, vec![], vec![], Some(why)),
        };
        let vars = cv.vars;
        let keys: Vec<String> = prods;
        let mut prods = Vec::new();
        let cid = &sp.clauses[e.clause].id;
        for k in &keys {
            match env.gl.resolve(k, cid) {
                Ok(ps) => prods.extend(ps),
                // a row an erratum says names no production of the grammar: kept with none, never applied
                Err(x) => match orphan_of(g, cid, k) {
                    Some(i) => orphans_met[i] = true,
                    // read without the overlay, or with none that says so: the row is kept with none, an error of
                    // the data that `roundtrip` reports
                    None => anchor_errors.push(format!("spec.html:{}: {x}: an equation row whose key names no production, and no emu-orphan-row says so", e.line)),
                },
            }
        }
        eqs.push(EqRow { eq: k, clause: e.clause, idx: e.idx, sdo, keys, prods, vars, body, exception });
    }
    for ((name, o), met) in g.overlay.errata.iter().flat_map(|e| e.orphans.iter().map(move |o| (&e.name, o))).zip(&orphans_met) {
        if !met {
            anchor_errors.push(format!("erratum {name}: the row {} of {} names a production of the grammar now, or is gone", o.grammar, o.clause));
        }
    }
    let mut sdo_headers = Vec::new();
    for k in 0..d.sdos.names.len() {
        let name = d.sdos.name(k).to_string();
        let cl = sp.clauses.iter().position(|c| c.ty.as_deref() == Some("sdo") && c.op().as_deref() == Some(name.as_str()));
        sdo_headers.push(cl.map(|cl| {
            let header = crate::header::parse(&sp.clauses[cl]);
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
                d: &mut d,
                env: &env,
                vars: Vars::default(),
                rows: &by_step,
                toks: Vec::new(),
                text: String::new(),
                unresolved: Vec::new(),
                exceptions: Vec::new(),
                closures: Vec::new(),
                base: 0,
                clause: sp.clauses[cl].id.clone(),
            };
            header_of(&mut cv, &mut hp, &sp.clauses[cl], &header, None)
        }));
    }
    let sig_tys = sig_tys(g, &d, &env, &mut hp);
    d.type_bounds = type_bounds(&d, &phrase_algs);
    d.phrase_typings = phrase_typings(&d, &phrase_algs);
    d.typing_errors.sort();
    d.typing_errors.dedup();
    anchor_errors.append(&mut d.typing_errors);
    for r in &g.overlay.result_types {
        if !sp.clauses.iter().any(|c| c.id == r.clause && c.ty.is_some()) && !phrase_algs.iter().any(|p| p.id == r.clause) {
            anchor_errors.push(format!("{}: <emu-result-type clause={}>: no operation's clause or phrase", r.file, r.clause));
        }
    }
    let mut early = early_rows(sp, g, &mut d, &env, &by_step, &anchors, &mut anchor_errors);
    modified_rules(html, sp, &mut early);
    let dp = distinct.values().filter(|&&v| v).count();
    let overlay_docs = g.overlay.prims.iter().map(|p| (p.name.clone(), p.signature.clone(), p.meaning.clone())).collect();
    let name_clashes = d.prims.names.iter().filter(|n| env.ops.contains_key(n.as_str()) && !RETIRED_PRIMS.contains(&n.as_str()) && !PHRASE_ONLY_PRIMS.contains(&n.as_str())).cloned().collect();
    Data { phrase_algs, reading_rows, row_errors, name_clashes, overlay_docs, anchor_errors, early, eqs, sdo_headers, header_types: (occ.0, occ.1, dp, distinct.len()), sig_tys, decls: d, env, algs, unresolved }
}

/// Every Early Errors bullet as a row: its block's productions and its sentences.
/// Marks each annex rule on a main rule's production as modifying it: its block follows "the rules
/// for the following productions are modified".
fn modified_rules(html: &str, sp: &Spec, rows: &mut [EarlyRow]) {
    let annex = |c: usize| sp.clauses[c].number.starts_with(|x: char| x.is_ascii_uppercase());
    for i in 0..rows.len() {
        let r = &rows[i];
        if !annex(r.clause) || !rows.iter().any(|m| !annex(m.clause) && m.prods.iter().any(|p| r.prods.contains(p))) {
            continue;
        }
        let line = sp.early.blocks[sp.early.bullets[r.bullet].block].line;
        let at = html.match_indices('\n').nth(line - 2).map_or(0, |x| x.0);
        let p = html[..at].rfind("<p>").filter(|&p| p > sp.clauses[r.clause].start).map(|p| &html[p..at]);
        assert!(p.is_some_and(|p| p.contains("are modified")), "spec.html:{line}: an annex rule on a main rule's production, not under \"are modified\"");
        rows[i].modifies = true;
    }
}

/// The index offset of a twin row (`EarlyRow::twin`) in its clause: past every bullet's index.
pub const TWIN_IDX: usize = 1000;

fn early_rows(
    sp: &Spec,
    g: &Grammar,
    d: &mut Decls,
    env: &Env,
    by_step: &HashMap<*const Step, &Row>,
    anchors: &crate::conv::Anchors,
    errors: &mut Vec<String>,
) -> Vec<EarlyRow> {
    let sdo = d.sdos.intern("Early Errors");
    let squash = |t: &str| t.split_whitespace().collect::<Vec<_>>().join(" ");
    // the rule readings, by clause, grammar, position in the block and text hash
    let mut rules: HashMap<(String, String, usize, String), (usize, &crate::overlay::RuleAnchor)> = HashMap::new();
    for (ei, e) in g.overlay.errata.iter().enumerate() {
        for r in &e.rules {
            if rules.insert((r.clause.clone(), squash(&r.grammar), r.rule, r.hash.clone()), (ei, r)).is_some() {
                errors.push(format!("{}: a second reading of rule {} of {} in {}", e.id, r.rule, r.grammar, r.clause));
            }
        }
    }
    let mut used = std::collections::HashSet::new();
    let mut strict = crate::engine::Parser::new(g, 99, false);
    let mut out = Vec::new();
    let mut twins = Vec::new();
    for (k, er) in crate::early::classify(sp, g).iter().enumerate() {
        let b = &sp.early.bullets[k];
        let raw = &sp.early.blocks[b.block].raw;
        let prods = env.gl.resolve(raw, &sp.clauses[b.clause].id).unwrap_or_else(|x| panic!("spec.html:{}: {x}", b.line));
        let mut cv = Conv {
            open: Vec::new(),
            rhs: Default::default(),
            lhs: Default::default(),
            narrow: Vec::new(),
            symbols: false,
            channel: crate::early::channel(d, b),
            anchors,
            stops: None,
            readings: Vec::new(),
            g,
            d: &mut *d,
            env,
            vars: Vars::default(),
            rows: by_step,
            toks: er.toks.clone(),
            text: b.text.clone(),
            unresolved: Vec::new(),
            exceptions: Vec::new(),
            closures: Vec::new(),
            base: 0,
            clause: sp.clauses[b.clause].id.clone(),
        };
        cv.set_rhs(std::slice::from_ref(raw));
        let node = |stmt: Stmt| Node { attrs: vec![], stmt };
        let r = match &er.tree {
            Some(t) => crate::early::sentences(t).iter().map(|s| cv.stmt(s, &[]).map(node)).collect::<Result<Vec<_>, _>>(),
            None => Err(String::new()),
        };
        let (body, exception) = match r {
            Ok(body) => (body, None),
            Err(why) => {
                let parts = if b.layout == LiLayout::Raw { vec![Part::Text(b.raw.clone())] } else { cv.prose(0, er.toks.len()) };
                (vec![node(Stmt::Prose(cv.channel, parts))], (!why.is_empty()).then_some(why))
            }
        };
        let rule = sp.early.bullets[..k].iter().filter(|x| x.block == b.block).count();
        let key = (sp.clauses[b.clause].id.clone(), squash(raw), rule, crate::text::sha256(&b.raw));
        let mut readings = None;
        if let Some(&(ei, ra)) = rules.get(&key) {
            used.insert(key.clone());
            let mut alts = Vec::new();
            for (reading, text) in &ra.alts {
                let toks = crate::token::tokenize(text);
                let Some(t) = strict.parse(&toks, "EB") else {
                    errors.push(format!("{}: the {reading} reading does not parse: {text}", g.overlay.errata[ei].id));
                    continue;
                };
                cv.toks = toks;
                cv.text = text.clone();
                match crate::early::sentences(&t).iter().map(|s| cv.stmt(s, &[]).map(node)).collect::<Result<Vec<_>, _>>() {
                    Ok(ss) => alts.push((reading_of(reading), ss)),
                    Err(why) => errors.push(format!("{}: the {reading} reading has no data shape: {why}", g.overlay.errata[ei].id)),
                }
            }
            readings = Some((ei, alts));
        }
        out.push(EarlyRow { bullet: k, clause: b.clause, idx: b.idx, sdo, prods, vars: cv.vars, body, exception, readings, modifies: false, twin: None });
        if let Some(&(ei, ra)) = rules.get(&key) {
            if let Some((also, aclause)) = &ra.also {
                let r = out.last().unwrap();
                match env.gl.resolve(also, aclause) {
                    Ok(ps) => twins.push(EarlyRow {
                        bullet: k,
                        clause: r.clause,
                        idx: TWIN_IDX + r.idx,
                        sdo,
                        prods: ps,
                        vars: r.vars.clone(),
                        body: vec![],
                        exception: None,
                        readings: r.readings.clone(),
                        modifies: false,
                        twin: Some(also.clone()),
                    }),
                    Err(e) => errors.push(format!("{}: also {also:?} in {aclause}: {e}", g.overlay.errata[ei].id)),
                }
            }
        }
    }
    // after the bullets' rows, which stay in bullet order
    out.extend(twins);
    for (key, (ei, _)) in &rules {
        if !used.contains(key) {
            errors.push(format!("{}: no rule {} of {} with that text hash in {}", g.overlay.errata[*ei].id, key.2, key.1, key.0));
        }
    }
    out
}
