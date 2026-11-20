//! Primitive call sites against their signatures: the overlay's `<emu-signature>`,
//! the residue classifier's, or §5.2.6's notation. A mismatch fails emission.

use crate::decls::Decls;
use crate::grammar::Grammar;

/// A primitive's parameter sorts and result; `variadic`: one or more arguments of the last sort.
pub struct Sig {
    pub params: Vec<String>,
    pub res: String,
    pub variadic: bool,
}

/// §5.2.6's notation: name, parameter count (0: one or more), result.
const NOTATION: &[(&str, usize, &str)] = &[
    ("𝔽", 1, "Number"),
    ("ℝ", 1, "mathematical value"),
    ("ℤ", 1, "BigInt"),
    ("abs", 1, "mathematical value"),
    ("floor", 1, "integer"),
    ("truncate", 1, "integer"),
    ("min", 0, "mathematical value"),
    ("max", 0, "mathematical value"),
    ("ln", 1, "mathematical value"),
    ("log10", 1, "mathematical value"),
    ("log2", 1, "mathematical value"),
    ("scf", 1, "code point"),
];

/// The `Ecma.Known` primitives' parameters, from the argument shapes their meanings take
/// (`Prims/*.lean`): a primitive with several shapes lists each.
const KNOWN: &[(&str, &[&[&str]])] = &[
    ("Running", &[&[]]),
    ("CurrentRealm", &[&[]]),
    ("ActiveFunction", &[&[]]),
    ("AgentRecord", &[&[]]),
    ("SurroundingAgent", &[&[]]),
    ("StackEmpty", &[&[]]),
    ("IsSuspended", &[&["value"]]),
    ("ListNew", &[&[]]),
    ("ListConcat", &[&["List"]]),
    ("ListLen", &[&["List"]]),
    ("Contains", &[&["value", "value"]]),
    ("ListElem", &[&["choice", "List"]]),
    ("ListOf1", &[&["value"]]),
    ("Copy", &[&["List or Record"]]),
    ("IsEmpty", &[&["List or String"]]),
    ("SameLength", &[&["List"]]),
    ("ListFind", &[&["field", "List", "value"]]),
    ("Count", &[&["choice", "value"]]),
    ("Insert", &[&["value", "List"]]),
    ("RemoveElem", &[&["value", "List"]]),
    ("RemoveFirst", &[&["List"]]),
    ("RemoveLast", &[&["List"]]),
    ("Reverse", &[&["List"]]),
    ("ReplaceElem", &[&["List", "value", "value"]]),
    ("SetAdd", &[&["value", "List"]]),
    ("StoreBytes", &[&["List", "Data Block", "integer"]]),
    ("ThisNode", &[&[]]),
    ("GrammarSymbol", &[&["nonterminal"]]),
    ("InstanceOf", &[&["Parse Node", "value"]]),
    ("ChildOf", &[&["nonterminal", "Parse Node"]]),
    ("IsFinite", &[&["value"]]),
    ("InInterval", &[&["value", "value", "value"]]),
    ("Parity", &[&["choice", "mathematical value"]]),
    ("Remainder", &[&["mathematical value", "mathematical value"]]),
    ("XMath", &[&["Number"]]),
    ("Negative", &[&["value"]]),
    ("BigIntFor", &[&["mathematical value"]]),
    ("NumberFor", &[&["choice", "extended mathematical value"], &["extended mathematical value"]]),
    ("Bitwise", &[&["choice", "value", "value"]]),
    ("Pi", &[&[]]),
    ("MathFn", &[&["choice", "mathematical value"]]),
    ("TimeConst", &[&["choice"]]),
    ("Chain", &[&["value", "choice", "value", "choice", "value"]]),
    ("Component", &[&["value", "field"]]),
    ("HasField", &[&["field", "value"]]),
    ("HasSlot", &[&["field", "value"]]),
    ("HasMethod", &[&["field", "value"]]),
    ("HasSlots", &[&["List", "value"]]),
    ("AttrValue", &[&["value", "field"]]),
    ("SlotsListed", &[&["value"]]),
    ("NewRecord", &[&["sort"]]),
    ("Present", &[&["value"]]),
    ("CodeUnit", &[&["integer"]]),
    ("StrOfUnits", &[&["code unit or String"]]),
    ("string-concatenation", &[&["code unit or String"]]),
    ("StrLen", &[&["String"]]),
    ("UnitAt", &[&["integer", "String"]]),
    ("NumericValue", &[&["code point or code unit"]]),
    ("FirstUnit", &[&["String"]]),
    ("CodePointCount", &[&["value", "value"]]),
    ("UnitOrPointOf", &[&["choice", "integer"]]),
    ("CodePointMatched", &[&["Parse Node"]]),
    ("CodePoints", &[&["List"]]),
    ("EmptyCodePoints", &[&[]]),
    ("SourceText", &[&["Parse Node"]]),
    ("CharSetUnion", &[&["choice", "value", "value"]]),
    ("Char", &[&["integer"]]),
    ("CharValue", &[&["value"]]),
    ("ClosureArity", &[&["value"]]),
    ("RecordFieldNames", &[&["value"]]),
];

/// The results of `Ecma.Known` primitives, as header types, from the values their meanings give (`Prims/*.lean`, `Leaf.lean`).
const KNOWN_RES: &[(&str, &str)] = &[
    ("Running", "an execution context"),
    ("CurrentRealm", "a Realm Record"),
    ("ActiveFunction", "an Object or *null*"),
    ("AgentRecord", "an Agent Record"),
    ("StackEmpty", "a Boolean"),
    ("IsSuspended", "a Boolean"),
    ("Negative", "a Number, a BigInt, or an extended mathematical value"),
    ("ListNew", "a List"),
    ("ListConcat", "a List"),
    ("ListLen", "a non-negative integer"),
    ("Contains", "a Boolean"),
    ("ListOf1", "a List"),
    ("Copy", "a List or a Record"),
    ("IsEmpty", "a Boolean"),
    ("SameLength", "a Boolean"),
    ("Count", "a non-negative integer"),
    ("CodeUnit", "a code unit"),
    ("StrOfUnits", "a String"),
    ("string-concatenation", "a String"),
    ("the empty String", "a String"),
    ("Substring", "a String"),
    ("StrLen", "a non-negative integer"),
    ("UnitAt", "a code unit"),
    ("NumericValue", "a non-negative integer"),
    ("FirstUnit", "a code unit"),
    ("StartsWith", "a Boolean"),
    ("CodePointCount", "a non-negative integer"),
    ("UnitOrPointOf", "a code point or a code unit"),
    ("CodePointMatched", "a code point"),
    ("CodePoints", "a List of code points"),
    ("EmptyCodePoints", "a List of code points"),
    ("SourceText", "a List of code points"),
    ("clamping", "a mathematical value"),
    ("HasField", "a Boolean"),
    ("HasSlot", "a Boolean"),
    ("HasMethod", "a Boolean"),
    ("HasSlots", "a Boolean"),
    ("NewRecord", "a Record or a List"),
    ("Present", "a Boolean"),
    ("CoveredBy", "a Parse Node"),
    ("NodeContains", "a Boolean"),
    ("InstanceOf", "a Boolean"),
    ("IsFinite", "a Boolean"),
    ("InInterval", "a Boolean"),
    ("Parity", "a Boolean"),
    ("Chain", "a Boolean"),
    ("Remainder", "a mathematical value"),
    ("XMath", "an extended mathematical value"),
    ("NumberFor", "a Number or a BigInt"),
    ("BigIntFor", "a BigInt"),
    ("Pi", "a mathematical value"),
    ("CharSetUnion", "a CharSet"),
    ("CharSetOne", "a CharSet"),
    ("CharSetUnionAll", "a CharSet"),
    ("Char", "a character"),
    ("CharValue", "a non-negative integer"),
    ("NewSymbol", "a Symbol"),
];

/// The `KNOWN` primitives that take one or more arguments of their last sort.
const VARIADIC: &[&str] = &["StrOfUnits", "string-concatenation"];

/// Every signature the primitive `name` has: a Known primitive's shapes, or its declared one.
pub fn all(g: &Grammar, name: &str) -> Vec<Sig> {
    match KNOWN.iter().find(|k| k.0 == name) {
        Some((_, shapes)) => shapes.iter().map(|ps| Sig { params: ps.iter().map(|x| x.to_string()).collect(), res: String::new(), variadic: VARIADIC.contains(&name) }).collect(),
        None => of(g, name).into_iter().collect(),
    }
}

/// The declared signature of the primitive `name`, if it has one.
pub fn of(g: &Grammar, name: &str) -> Option<Sig> {
    if let Some(&(_, n, res)) = NOTATION.iter().find(|x| x.0 == name) {
        return Some(Sig { params: vec!["mathematical value".into(); n.max(1)], res: res.into(), variadic: n == 0 });
    }
    let text = g.overlay.prims.iter().find(|p| p.name == name).map(|p| p.signature.as_str()).or_else(|| crate::residue::PRIMS.iter().find(|p| p.name == name).map(|p| p.sig))?;
    let (params, res) = crate::residue::sig_parts(text)?;
    Some(Sig { params, res, variadic: false })
}

/// The declared result of the primitive `name`: a Known primitive's, else its signature's.
pub fn res(g: &Grammar, name: &str) -> Option<String> {
    KNOWN_RES.iter().find(|k| k.0 == name).map(|k| k.1.to_string()).or_else(|| of(g, name).map(|s| s.res))
}

/// Every type text the primitives' signatures and results write.
pub fn texts(g: &Grammar, names: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for n in names {
        for s in all(g, n).into_iter().chain(of(g, n)) {
            out.extend(s.params);
        }
        out.extend(res(g, n));
    }
    out.sort();
    out.dedup();
    out
}

/// Whether a declared parameter type is a nonterminal: `a nonterminal`, `a nonterminal in one of the ECMAScript grammars`.
pub fn is_nt(t: &str) -> bool {
    let t = t.trim().trim_start_matches("optional ");
    let t = t.strip_prefix("a ").unwrap_or(t);
    t == "nonterminal" || t.starts_with("nonterminal in ")
}

/// The positions of the parameter types that are nonterminals.
pub fn nt_params<S: AsRef<str>>(ts: &[S]) -> Vec<usize> {
    ts.iter().enumerate().filter(|(_, t)| is_nt(t.as_ref())).map(|(k, _)| k).collect()
}

/// Why `n` arguments do not fit `s`, if they do not.
fn arity(s: &Sig, n: usize) -> Option<String> {
    let ok = if s.variadic { n >= s.params.len() } else { n == s.params.len() };
    (!ok).then(|| format!("{n} argument{} for {}{} parameter{}", if n == 1 { "" } else { "s" }, s.params.len(), if s.variadic { " or more" } else { "" }, if s.params.len() == 1 { "" } else { "s" }))
}

/// Why a call of `name` with `n` arguments does not fit its signature, if it has one and they do not.
pub fn call(g: &Grammar, name: &str, n: usize) -> Option<String> {
    arity(&of(g, name)?, n)
}

/// Every primitive phrase meaning whose primitive's signature it does not fit: arity,
/// and a negated meaning's primitive giving a Boolean.
pub fn phrases(g: &Grammar, d: &Decls) -> Vec<String> {
    let mut out = Vec::new();
    for (i, p) in d.phrases.iter().enumerate() {
        let Some(crate::decls::Meaning::Prim { prim, args, neg }) = &p.meaning else { continue };
        let name = d.prims.name(*prim);
        let sigs = all(g, name);
        if !sigs.is_empty() && sigs.iter().all(|s| arity(s, args.len()).is_some()) {
            out.push(format!("phrase {i} ({} {}): {name}: {}", p.cat, p.name, arity(&sigs[0], args.len()).unwrap_or_default()));
        }
        let Some(s) = of(g, name) else { continue };
        if *neg && !s.res.contains("Boolean") {
            out.push(format!("phrase {i} ({} {}): {name}: negated, but the result is {}", p.cat, p.name, s.res));
        }
    }
    out
}
