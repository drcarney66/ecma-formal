//! Parse trees to the data (`ast`): the core forms to their constructors,
//! every other template to a phrase row with its holes, prose spans to
//! residue with typed holes.

use crate::ast::*;
use crate::decls::{Decls, HoleKind, Piece};
use crate::engine::{El, Item, Kc, Node as PNode, Rid};
use crate::grammar::{Grammar, MODS};
use crate::token::{lit_canon, Tok, K};
use crate::classify::{Class, Row};
use crate::spec::Step;
use std::collections::HashMap;
use std::rc::Rc;

/// An algorithm's variables: names by slot.
#[derive(Default, Clone)]
pub struct Vars {
    pub names: Vec<String>,
    /// the slots a binder named first (`Let _x_ be`, `For each _x_`, …)
    pub bound: Vec<Id>,
}

impl Vars {
    pub fn slot(&mut self, name: &str) -> Id {
        if let Some(i) = self.names.iter().position(|n| n == name) {
            return i;
        }
        self.names.push(name.to_string());
        self.names.len() - 1
    }
}

/// A context sort's context phrase, registered, and the name of the variable it reads.
pub(crate) fn sort_context(g: &Grammar, d: &mut Decls, s: Id) -> Option<(Id, String)> {
    let name = d.sorts.name(s);
    let c = g.overlay.sorts.iter().find(|x| x.name == name)?.context.as_ref()?;
    let v = g.overlay.phrases.iter().find(|p| p.id == *c)?.vars().into_iter().next()?;
    let r = g.rules.iter().find(|r| r.cat == "PRED" && r.name == c.as_str())?;
    let els = r.elems.clone();
    let p = d.phrase("PRED", r.name, || pieces(&els));
    if d.phrases[p].meaning.is_none() {
        d.phrases[p].meaning = Some(crate::decls::Meaning::Alg(d.clauses.get(c)?));
    }
    d.sort_ctx.insert(s, p);
    Some((p, v))
}

/// A conversion failure: the form the converter has no data shape for.
pub type Res<T> = Result<T, String>;

/// Names resolved through the declarations.
pub struct Env {
    /// operation name -> defining clause
    pub ops: std::collections::HashMap<String, Id>,
    /// operation name -> the positions of its parameters whose type is a nonterminal
    pub nt_params: std::collections::HashMap<String, Vec<usize>>,
    /// execution-context components
    pub components: Vec<String>,
    /// the grammars: production and nonterminal ids for grammar keys
    pub gl: jsgrammar::gl::Gl,
    /// each algorithm's index in its clause, by clause id and the text between its tags
    pub algs: std::collections::HashMap<(String, String), usize>,
    /// each `emu-table`'s index among the emitted tables, by its id
    pub tables: std::collections::HashMap<String, usize>,
    /// each `emu-table`'s Lean name (`tables::lean_name`), by index
    pub table_names: Vec<String>,
    /// each `emu-table`'s span in spec.html, by index
    pub table_spans: Vec<std::ops::Range<usize>>,
    /// each step's own table (a `figure`): its index among the emitted tables, by its text squashed
    pub figures: std::collections::HashMap<String, usize>,
    /// the well-known symbols' descriptions (`Symbol.iterator`)
    pub symbols: Vec<String>,
}

pub struct Conv<'a, 'b> {
    pub g: &'a Grammar,
    pub d: &'b mut Decls,
    pub env: &'a Env,
    pub vars: Vars,
    /// the parsed steps, by step
    pub rows: &'a HashMap<*const Step, &'a Row<'a>>,
    /// the current step's tokens and text
    pub toks: Vec<Tok>,
    pub text: String,
    /// unresolved "X of Y" names met
    pub unresolved: Vec<String>,
    /// steps the converter has no shape for (kept as prose): text and reason
    pub exceptions: Vec<(String, String)>,
    /// the algorithm's Abstract Closure literals, in text order
    pub closures: Vec<CloLit>,
    /// the closure literals whose bodies are being converted, innermost last, with the
    /// *this* value form read so far (bare or not)
    pub open: Vec<(usize, Option<bool>)>,
    /// the column of the algorithm's depth-0 steps
    pub base: usize,
    /// the id of the clause being converted (grammar keys resolve within it)
    pub clause: String,
    /// the channel of the step being converted's prose, from the residue classifier
    pub channel: Channel,
    /// steps with an erratum: the erratum, its anchor, the readings' steps
    pub anchors: &'a Anchors<'a>,
    /// the literal errata's stop sites the converted steps label
    pub stops: Option<&'a crate::stops::StopSites>,
    /// the readings' steps converted: erratum, anchor, reading, steps
    pub readings: Vec<(usize, usize, usize, Vec<Node>)>,
    /// in an SDO row, the nonterminals of its productions' right-hand sides: a bare
    /// `|X|` among them is a child of the row's Parse Node, any other a grammar symbol
    pub rhs: std::collections::HashSet<String>,
    /// in an SDO row, its productions' left-hand sides: a bare `|X|` naming one (and no
    /// right-hand side's symbol) is the row's Parse Node
    pub lhs: std::collections::HashSet<String>,
    /// inside `If |Y| is <emu-grammar>P</emu-grammar>`: `|Y|` and P's right-hand-side nonterminals
    pub narrow: Vec<(Expr, std::collections::HashSet<String>)>,
    /// a bare `|X|` that is a whole value of a predicate on a variable names the grammar symbol
    pub symbols: bool,
}

/// A frame slot's name: the marker, then the words it prints as.
pub const FRAME: &str = "#";
const THIS: &str = "#the *this* value";
const THIS_BARE: &str = "#*this* value";
const NEW_TARGET: &str = "#NewTarget";
/// The start of a call frame error's reason (`Conv::exceptions`).
pub const FRAME_ERR: &str = "call frame: ";
/// The prose a closure's arguments List is read with.
pub const ARGUMENTS: &str = "the List of arguments that was passed to this function by [[Call]] or [[Construct]]";

/// The phrases whose first `|X|` is the Parse Node they speak of (`Conv::node_of`), not a symbol.
const NODE_SUBJECT: &[(&str, &str)] = &[("P", "contains-infix"), ("CA", "contains-cond"), ("ER", "must-cover")];

/// Steps with an erratum: the erratum and anchor indices, and each reading's steps; the first outermost.
pub type Anchors<'a> = HashMap<*const Step, Vec<(usize, usize, Vec<(Reading, &'a [Step])>)>>;

fn items_of(n: &PNode) -> &[Item] {
    &n.items
}

/// The right-hand-side nonterminals of productions.
pub fn prod_rhs(gl: &jsgrammar::gl::Gl, ps: &[usize]) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    for &p in ps {
        let Some(a) = gl.alt(gl.prods[p].at) else { continue };
        for i in &a.rhs {
            if let jsgrammar::grammar::Item::Sym(jsgrammar::grammar::Sym::Nt(n, _), _) | jsgrammar::grammar::Item::ButNot(jsgrammar::grammar::Sym::Nt(n, _), _) = i {
                out.insert(n.clone());
            }
        }
    }
    out
}

fn child(it: &Item) -> Option<&Rc<PNode>> {
    match it {
        Item::N(n, _) => Some(n),
        _ => None,
    }
}

fn hole_kind(c: &str) -> HoleKind {
    match c {
        "C" | "HC" | "HCA" => HoleKind::C,
        "T" | "TN" | "HT" | "HT1" | "HTALT" | "TALT" => HoleKind::T,
        "V" => HoleKind::B,
        "SI" | "SIn" => HoleKind::S,
        "EL" | "ALT" | "Args" | "ArgsP" | "FieldNames" | "FieldEL" => HoleKind::L,
        "CAPS" => HoleKind::Text,
        _ => HoleKind::E,
    }
}

fn kind_hole(k: Kc) -> HoleKind {
    match k {
        Kc::Cap | Kc::Low | Kc::Up | Kc::K(K::Word | K::NotRefO | K::NotRefC) => HoleKind::Text,
        _ => HoleKind::E,
    }
}

/// A template's argument slots in the order `holes` fills them (a choice's selector, then
/// the chosen alternative's slots): each value hole's and each top-level choice's index
/// there. A hole inside a choice is a value hole when every alternative has the same
/// number of holes and no choice; after any other choice, positions depend on the
/// alternative taken, and later holes have none (`None`).
pub struct Slots {
    pub holes: Vec<Option<usize>>,
    /// per choice: its selector's index, and whether no slot follows it
    pub choices: Vec<Option<(usize, bool)>>,
}

pub fn slots(els: &[(El, bool)]) -> Slots {
    fn width(els: &[(El, bool)]) -> Option<usize> {
        let mut w = 0;
        for (el, _) in els {
            match el {
                El::Lit(_) | El::KindV(..) => {}
                El::Kind(_) | El::Hole(_) => w += 1,
                El::Opt(_) | El::Alt(_) => return None,
            }
        }
        Some(w)
    }
    let mut s = Slots { holes: Vec::new(), choices: Vec::new() };
    let mut at = Some(0);
    for (k, (el, _)) in els.iter().enumerate() {
        match el {
            El::Lit(_) | El::KindV(..) => {}
            El::Kind(_) | El::Hole(_) => {
                s.holes.push(at);
                at = at.map(|a| a + 1);
            }
            El::Opt(_) | El::Alt(_) => {
                let alts: Vec<&[(El, bool)]> = match el {
                    El::Opt(inner) => vec![inner, &[]],
                    El::Alt(a) => a.iter().map(|x| &x[..]).collect(),
                    _ => unreachable!(),
                };
                let tail = els[k + 1..].iter().all(|(e, _)| matches!(e, El::Lit(_) | El::KindV(..)));
                s.choices.push(at.map(|a| (a, tail)));
                at = at.map(|a| a + 1);
                let ws: Vec<Option<usize>> = alts.iter().map(|a| width(a)).collect();
                match ws[0] {
                    Some(w) if ws.iter().all(|x| *x == Some(w)) => {
                        for _ in 0..w {
                            s.holes.push(at);
                            at = at.map(|a| a + 1);
                        }
                    }
                    _ => at = None,
                }
            }
        }
    }
    s
}

/// A built-in meaning's argument, as its table writes it.
enum MArg {
    Subject,
    /// an index into the instance's holes; `field`: its words name a field
    Hole(usize, bool),
    /// an index into the instance's holes: a list hole, its elements spread
    Spread(usize),
    This,
    Sort(&'static str),
    /// a choice's alternative, fixed
    Choice(usize),
}

/// `S` the subject; `N` the Nth value hole (`slots`), `fN` the same, its words a field's
/// name; `*N` the same, a list hole, its elements as arguments; `wN` the Nth top-level choice's selector, `wN.k` the kth hole of its alternative
/// when no slot follows the choice (absent when another is taken); `=this` this Parse Node;
/// `=sort:Name` a sort; `=choice:K` the Kth alternative of the primitive's choice.
fn meaning_arg(s: &Slots, a: &'static str) -> Res<MArg> {
    if a == "S" {
        return Ok(MArg::Subject);
    }
    if a == "=this" {
        return Ok(MArg::This);
    }
    if let Some(n) = a.strip_prefix("=sort:") {
        return Ok(MArg::Sort(n));
    }
    if let Some(k) = a.strip_prefix("=choice:") {
        return k.parse().map(MArg::Choice).map_err(|_| format!("meaning argument {a}: not =choice:K"));
    }
    let bad = |e: &str| format!("meaning argument {a}: {e}");
    if let Some(n) = a.strip_prefix('*') {
        return match meaning_arg(s, n)? {
            MArg::Hole(f, false) => Ok(MArg::Spread(f)),
            _ => Err(bad("not *N")),
        };
    }
    if let Some(c) = a.strip_prefix('w') {
        let (c, k) = match c.split_once('.') {
            Some((c, k)) => (c, Some(k.parse::<usize>().map_err(|_| bad("not wN.k"))?)),
            None => (c, None),
        };
        let c: usize = c.parse().map_err(|_| bad("not wN"))?;
        let (at, tail) = s.choices.get(c).ok_or_else(|| bad("the template has no such choice"))?.ok_or_else(|| bad("after a choice whose alternatives differ in holes"))?;
        return match k {
            None => Ok(MArg::Hole(at, false)),
            Some(_) if !tail => Err(bad("a slot follows the choice")),
            Some(k) => Ok(MArg::Hole(at + 1 + k, false)),
        };
    }
    let (field, n) = match a.strip_prefix('f') {
        Some(n) => (true, n),
        None => (false, a),
    };
    let i: usize = n.parse().map_err(|_| bad("not a number"))?;
    match s.holes.get(i) {
        Some(Some(f)) => Ok(MArg::Hole(*f, field)),
        Some(None) => Err(bad("after a choice whose alternatives differ in holes")),
        None => Err(bad("the template has no such hole")),
    }
}

/// A template's pieces.
pub fn pieces(els: &[(El, bool)]) -> Vec<Piece> {
    let mut out = Vec::new();
    for (el, glue) in els {
        if *glue {
            out.push(Piece::Glue);
        }
        out.push(match el {
            El::Lit(l) => Piece::Word(lit_canon(l).to_string()),
            El::Kind(k) => Piece::Hole(kind_hole(*k)),
            El::KindV(_, _, text) => Piece::Word(text.clone()),
            El::Hole(c) => Piece::Hole(hole_kind(c)),
            El::Opt(inner) => Piece::Choice(vec![pieces(inner), vec![]]),
            El::Alt(alts) => Piece::Choice(alts.iter().map(|a| pieces(a)).collect()),
        });
    }
    out
}

fn parse_numeral(s: &str) -> Res<Numeral> {
    if let Some(h) = s.strip_prefix("0x") {
        return Ok(Numeral::Hex(u128::from_str_radix(h, 16).map_err(|e| e.to_string())?, h.to_string()));
    }
    if let Some((w, f)) = s.split_once('.') {
        let wn: u128 = w.parse().map_err(|_| format!("numeral {s}"))?;
        if wn.to_string() != w {
            return Err(format!("numeral with leading zeros: {s}"));
        }
        let fv: u128 = f.parse().map_err(|_| format!("numeral {s}"))?;
        return Ok(Numeral::Frac(wn, fv, f.len()));
    }
    let n: u128 = s.parse().map_err(|_| format!("numeral {s}"))?;
    if n.to_string() != s {
        return Err(format!("numeral with leading zeros: {s}"));
    }
    Ok(Numeral::Dec(n))
}

fn sub_of(c: Option<char>) -> Sub {
    match c {
        Some('𝔽') => Sub::F,
        Some('ℤ') => Sub::Z,
        _ => Sub::None,
    }
}

/// Whether a built-in rule has a meaning in `BUILTIN_MEANINGS`.
pub fn builtin_meaning(cat: &str, name: &str) -> bool {
    BUILTIN_MEANINGS.iter().any(|m| m.0 == cat && m.1 == name)
}

/// Phrases the machine gives directly (§5.2 and §6's notation): category, rule, the
/// `Ecma.Known` primitive, its arguments ("S" the predicate's subject, else a hole
/// index, choice holes included), and whether the phrasing negates it.
const BUILTIN_MEANINGS: &[(&str, &str, &str, &[&str], bool)] = &[
    ("P", "empty-string", "the empty String", &[], false),
    // `the |X| lexical grammar production`: the nonterminal
    ("P", "lexical-production", "GrammarSymbol", &["0"], false),
    // Tables: the table, the value's column, the key's column, the key
    ("P", "table-lookup-key", "TableLookup", &["1", "0", "2", "3"], false),
    // the row "for X": keyed by the table's first column
    ("P", "table-lookup-row", "TableRowValue", &["1", "0", "2"], false),
    ("P", "strcat", "string-concatenation", &["*0"], false),
    ("P", "clamp", "clamping", &["0", "1", "2"], false),
    ("P", "approx", "implementation-approximated", &["0"], false),
    ("P", "impl-choice", "implementation-defined choice", &["0", "1"], false),
    ("CA", "host-web", "the host is a web browser", &["w0", "w0.0"], false),
    // Lists (§6.2.2)
    ("P", "new-list", "ListNew", &[], false),
    ("P", "empty-coll", "ListNew", &[], false),
    ("P", "listcat", "ListConcat", &["0"], false),
    ("P", "numel", "ListLen", &["0"], false),
    ("P", "numel-of", "ListLen", &["0"], false),
    ("PRED", "contains", "Contains", &["0", "S"], false),
    ("PRED", "not-contains", "Contains", &["0", "S"], true),
    ("PRED", "not-include", "Contains", &["0", "S"], true),
    ("P", "elem", "ListElem", &["w0", "0"], false),
    ("P", "list-sole", "ListOf1", &["0"], false),
    ("P", "copy", "Copy", &["0"], false),
    ("PRED", "empty", "IsEmpty", &["S"], false),
    ("PRED", "empty-list", "IsEmpty", &["S"], false),
    ("PRED", "not-empty", "IsEmpty", &["S"], true),
    ("CA", "same-count", "SameLength", &["0"], false),
    ("CA", "not-same-count", "SameLength", &["0"], true),
    ("P", "select-whose", "ListFind", &["2", "1", "3"], false),
    ("P", "number-of", "Count", &["w0", "0"], false),
    ("Step", "append", "Append", &["0", "1"], false),
    ("Step", "prepend", "Prepend", &["0", "1"], false),
    ("Step", "insert-first", "Insert", &["0", "1"], false),
    ("Step", "remove", "RemoveElem", &["0", "1"], false),
    ("Step", "remove-first", "RemoveFirst", &["0"], false),
    ("Step", "remove-last", "RemoveLast", &["0"], false),
    ("Step", "reverse", "Reverse", &["0"], false),
    ("Step", "replace-elem", "ReplaceElem", &["0", "1", "2"], false),
    ("Step", "add", "SetAdd", &["0", "1"], false),
    ("Step", "store-bytes", "StoreBytes", &["0", "1", "3"], false),
    // Strings and code points (§6.1.4)
    ("P", "code-unit", "CodeUnit", &["0"], false),
    ("P", "string-of", "StrOfUnits", &["*0"], false),
    ("P", "substring", "Substring", &["0", "1", "w0.0"], false),
    ("P", "length", "StrLen", &["0"], false),
    ("P", "cu-at", "UnitAt", &["0", "1"], false),
    ("P", "numeric-value", "NumericValue", &["0"], false),
    // grammatical parameters (the subject, or this production's node) and the parse
    ("PRED", "has-param", "HasParam", &["S", "0"], false),
    ("PRED", "not-has-param", "HasParam", &["S", "0"], true),
    ("CA", "param-not-set", "HasParam", &["=this", "0"], true),
    // a parser invocation's facts, at any node it made: this production's
    ("CA", "direct-eval", "InDirectEval", &["=this"], false),
    ("P", "goal-symbol", "GoalSymbolOf", &["=this"], false),
    ("P", "first-cu", "FirstUnit", &["0"], false),
    ("PRED", "starts-with", "StartsWith", &["0", "S"], false),
    ("P", "numcp-excl", "CodePointCount", &["0", "1"], false),
    ("P", "cp-whose", "UnitOrPointOf", &["w0", "0"], false),
    ("P", "code-point", "UnitOrPointOf", &["=choice:0", "w1.0"], false),
    ("P", "cp-matched", "CodePointMatched", &["0"], false),
    ("P", "cp-this-prod", "CodePointMatched", &["=this"], false),
    ("P", "cp-list", "CodePoints", &["0"], false),
    ("P", "empty-seq", "EmptyCodePoints", &[], false),
    ("P", "source-text", "SourceText", &["0"], false),
    ("P", "recognized-as", "SourceText", &["0"], false),
    // Records, objects and slots (§6.2.1, §6.1.7)
    ("P", "poss", "Component", &["0", "f1"], false),
    ("P", "component", "Component", &["1", "f0"], false),
    ("P", "component-value", "Component", &["1", "f0"], false),
    ("PRED", "has-component", "HasField", &["f0", "S"], false),
    ("PRED", "not-has-component", "HasField", &["f0", "S"], true),
    ("PRED", "has-field", "HasField", &["0", "S"], false),
    ("PRED", "not-has-field", "HasField", &["0", "S"], true),
    ("PRED", "has-slot", "HasSlot", &["0", "S"], false),
    ("PRED", "not-has-slot", "HasSlot", &["0", "S"], true),
    ("PRED", "has-method", "HasMethod", &["0", "S"], false),
    ("PRED", "has-slots", "HasSlots", &["0", "S"], false),
    ("P", "attr-of", "AttrValue", &["0", "1"], false),
    ("P", "slots-listed", "SlotsListed", &["0"], false),
    ("P", "new-thing", "NewRecord", &["0"], false),
    ("P", "pd-empty", "NewRecord", &["=sort:Property Descriptor"], false),
    ("PRED", "present", "Present", &["S"], false),
    ("PRED", "not-present", "Present", &["S"], true),
    ("P", "nt-of", "ChildOf", &["0", "1"], false),
    // Execution contexts and agents (§9.4, §9.7)
    ("P", "running-ctx", "Running", &[], false),
    ("P", "current-realm", "CurrentRealm", &[], false),
    ("P", "active-fn", "ActiveFunction", &[], false),
    ("P", "agent-record", "AgentRecord", &[], false),
    ("P", "agent-record-poss", "AgentRecord", &[], false),
    ("P", "surrounding-agent", "SurroundingAgent", &[], false),
    ("CA", "stack-empty", "StackEmpty", &[], false),
    ("PRED", "already-suspended", "IsSuspended", &["S"], true),
    // Parse Nodes and grammar (§5.1)
    ("P", "covered", "CoveredBy", &["0", "1"], false),
    ("P", "processed-as", "CoveredBy", &["0", "1"], false),
    ("P", "grammar-symbol", "GrammarSymbol", &["0"], false),
    ("PRED", "instance-of", "InstanceOf", &["S", "0"], false),
    ("PRED", "instance-of-prod-p", "InstanceOf", &["S", "0"], false),
    ("PRED", "instance-var", "InstanceOf", &["S", "0"], false),
    // Mathematical and Number values (§5.2.6, §6.1.6)
    ("PRED", "finite", "IsFinite", &["S"], false),
    ("PRED", "not-finite", "IsFinite", &["S"], true),
    ("PRED", "interval", "InInterval", &["0", "1", "S"], false),
    ("PRED", "not-interval", "InInterval", &["0", "1", "S"], true),
    ("PRED", "parity", "Parity", &["w0", "S"], false),
    ("P", "remainder", "Remainder", &["0", "1"], false),
    ("P", "ext-math-value", "XMath", &["0"], false),
    ("P", "negative-of", "Negative", &["0"], false),
    ("P", "number-for", "NumberFor", &["0"], false),
    ("P", "number-corresponds", "NumberFor", &["w0", "0"], false),
    ("P", "bigint-for", "BigIntFor", &["0"], false),
    ("PRED", "own-prop", "OwnPropertyHas", &["S", "0"], false),
    ("PRED", "not-own-prop", "OwnPropertyHas", &["S", "0"], true),
    ("PRED", "own-prop-named", "OwnPropertyHas", &["S", "0"], false),
    ("PRED", "not-own-prop-named", "OwnPropertyHas", &["S", "0"], true),
    ("P", "bitwise", "Bitwise", &["w1", "0", "1"], false),
    ("P", "pi", "Pi", &[], false),
    ("P", "math-fn", "MathFn", &["w0", "0"], false),
    ("P", "constant", "TimeConst", &["w0"], false),
    ("CA", "rel3", "Chain", &["0", "w0", "1", "w1", "2"], false),
    // CharSets (§22.2.2)
    ("P", "charset-op", "CharSetUnion", &["w0", "0", "1"], false),
    ("P", "charset-one", "CharSetOne", &["0"], false),
    ("P", "charset-single", "CharSetOne", &["0"], false),
    ("P", "union", "CharSetUnionAll", &["0"], false),
    ("P", "character", "Char", &["0"], false),
    ("P", "char-whose", "Char", &["0"], false),
    ("P", "char-value", "CharValue", &["0"], false),
];

/// The built-in meanings against their templates: per row, the template with its value
/// holes numbered (‹N›) and choices numbered (wN), the primitive and its arguments.
pub fn meanings(g: &crate::grammar::Grammar) -> String {
    fn show(els: &[(El, bool)], v: &mut usize, w: &mut Option<&mut usize>, out: &mut Vec<String>) {
        for (el, _) in els {
            match el {
                El::Lit(l) => out.push(lit_canon(l).to_string()),
                El::KindV(_, _, t) => out.push(t.clone()),
                El::Kind(_) | El::Hole(_) => {
                    let c = match el {
                        El::Hole(c) => c.to_string(),
                        _ => "tok".into(),
                    };
                    out.push(format!("‹{v}:{c}›"));
                    *v += 1;
                }
                El::Opt(_) | El::Alt(_) => {
                    let alts: Vec<&[(El, bool)]> = match el {
                        El::Opt(inner) => vec![inner, &[]],
                        El::Alt(a) => a.iter().map(|x| &x[..]).collect(),
                        _ => unreachable!(),
                    };
                    let tag = match w {
                        Some(n) => {
                            let t = format!("w{n}");
                            **n += 1;
                            t
                        }
                        None => "w?".into(),
                    };
                    let start = *v;
                    let mut parts = Vec::new();
                    for a in alts {
                        *v = start;
                        let mut o = Vec::new();
                        show(a, v, &mut None, &mut o);
                        parts.push(o.join(" "));
                    }
                    out.push(format!("({})^{tag}", parts.join(" | ")));
                }
            }
        }
    }
    let mut out = String::new();
    for &(cat, name, prim, args, neg) in BUILTIN_MEANINGS {
        for r in g.rules.iter().filter(|r| r.cat == cat && r.name == name) {
            let (mut v, mut w) = (0, 0);
            let mut o = Vec::new();
            show(&r.elems, &mut v, &mut Some(&mut w), &mut o);
            let sl = slots(&r.elems);
            let res: Vec<String> = args.iter().map(|a| match meaning_arg(&sl, a) {
                Ok(MArg::Hole(f, _)) => format!("{a}=#{f}"),
                Ok(_) => a.to_string(),
                Err(e) => format!("{a}=ERR({e})"),
            }).collect();
            out += &format!("{cat}\t{name}\t{}{prim}({})\t{}\n", if neg { "not " } else { "" }, res.join(", "), o.join(" "));
        }
    }
    out
}

/// A code literal as the terminal grammar symbol it stands for, where it prints back as written.
fn as_term(e: Expr) -> Expr {
    match e {
        Expr::Code(s, w) if w.is_empty() => Expr::Term(s),
        e => e,
    }
}

/// Alternatives that name grammar symbols: with a nonterminal among them, code literals are terminals.
fn symbols(vs: Vec<Expr>) -> Vec<Expr> {
    if vs.iter().any(|v| matches!(v, Expr::Nt(..))) {
        vs.into_iter().map(as_term).collect()
    } else {
        vs
    }
}

/// The phrases whose hole of this index is a grammar symbol: a code literal there is a terminal.
const SYMBOL_HOLES: &[(&str, usize)] = &[("contains-infix", 1), ("contains-cond", 1), ("token-word", 0), ("token-nt", 1), ("not-nested", 0), ("not-nested-alt", 0)];

/// Holes a template repeats (by index into the instance's holes): `starting at _b_[_i_]`
/// names the block it stores into; annexb-foreach's `any … _x_ such that … Contains _x_`.
const SAME_HOLES: &[(&str, usize, usize)] = &[("store-bytes", 1, 2), ("annexb-foreach", 4, 6)];

/// Templates whose conditions test each candidate of the variables they bind (by hole index).
const BINDER_CONDS: &[(&str, &str, &[usize])] =
    &[("CA", "two-distinct", &[2, 3]), ("PRED", "two-entries", &[0, 1]), ("PRED", "contains-such", &[2]), ("PRED", "not-contains-such", &[2]), ("PRED", "contains-one-such", &[1]), ("ER", "foreach-in", &[1])];

/// Step templates with nested steps that iterate: the hole of this index is the variable the nested
/// steps run with, bound in turn to each element of the List the phrase's meaning gives.
const ITERATING_STEPS: &[(&str, usize)] = &[("annexb-foreach", 1)];

/// Step templates whose nested steps are an Abstract Closure with no parameters, the phrase's last
/// hole: it captures the variables of the algorithm the nested steps read.
pub const CLOSURE_STEPS: &[&str] = &["annexb-evaluated"];

/// Whether the variable in slot `x` occurs in `v` (an AST value).
fn reads(x: Id, v: &impl std::fmt::Debug) -> bool {
    format!("{v:?}").contains(&format!("Var({x})"))
}

/// An error constructor's name, as a value: `*TypeError*`.
pub fn is_error_name(v: &str) -> bool {
    v.len() > 5 && v.ends_with("Error") && v.starts_with(|c: char| c.is_ascii_uppercase()) && v.chars().all(|c| c.is_ascii_alphanumeric())
}

impl<'a, 'b> Conv<'a, 'b> {
    fn tok(&self, i: usize) -> &Tok {
        &self.toks[i]
    }

    /// The residue of a prose span: verbatim text, variables as typed holes.
    pub fn prose(&mut self, i: usize, j: usize) -> Vec<Part> {
        let mut parts = Vec::new();
        let mut text = String::new();
        for k in i..j {
            let t = &self.toks[k];
            if k > i {
                text.push_str(&self.text[self.toks[k - 1].e..t.s]);
            }
            if t.k == K::Var {
                if !text.is_empty() {
                    parts.push(Part::Text(std::mem::take(&mut text)));
                }
                let v = t.v.clone();
                parts.push(Part::Hole(Hole::E(Expr::Var(self.vars.slot(&v)))));
            } else {
                text.push_str(&t.raw);
            }
        }
        if !text.is_empty() {
            parts.push(Part::Text(text));
        }
        parts
    }

    pub fn val(&mut self, t: &Tok) -> Res<ValLit> {
        let v = t.v.as_str();
        let sub = sub_of(t.sub);
        let plain = |x: ValLit| if t.sub.is_none() { Ok(x) } else { Err(format!("value with a subscript: {}", t.raw)) };
        match v {
            "undefined" => return plain(ValLit::Undefined),
            "null" => return plain(ValLit::Null),
            "true" => return plain(ValLit::True),
            "false" => return plain(ValLit::False),
            "this" => return plain(ValLit::This),
            "NaN" => return Ok(ValLit::NaN(sub)),
            _ => {}
        }
        if is_error_name(v) {
            return plain(ValLit::Err(self.d.fields.intern(v)));
        }
        if v.len() >= 2 && v.starts_with('"') && v.ends_with('"') {
            let (t, w) = crate::text::literal(&v[1..v.len() - 1]);
            return plain(ValLit::Str(t, w));
        }
        let (sign, rest) = match v.chars().next() {
            Some('+') => (Sign::Plus, &v[1..]),
            Some('-') => (Sign::Minus, &v[1..]),
            _ => (Sign::None, v),
        };
        let mag = if rest == "∞" { Mag::Inf } else { Mag::Num(parse_numeral(rest).map_err(|_| format!("value {}", t.raw))?) };
        Ok(ValLit::Num(sign, mag, sub))
    }

    fn xref(&self, t: &Tok) -> Res<Expr> {
        let raw = &t.raw;
        let form = if raw.ends_with("></emu-xref>") {
            if raw.ends_with(" title></emu-xref>") {
                XrefForm::Title
            } else {
                XrefForm::Plain
            }
        } else {
            let a = raw.find('>').unwrap() + 1;
            let b = raw.len() - "</emu-xref>".len();
            XrefForm::Content(raw[a..b].to_string())
        };
        let e = Expr::Xref(t.v.clone(), form, self.d.clauses.get(&t.v));
        if crate::print::xref_text(&e) != *raw {
            return Err(format!("xref form {raw}"));
        }
        Ok(match self.env.tables.get(&t.v) {
            Some(&i) => Expr::Table(i, Box::new(e)),
            None => e,
        })
    }

    /// An atom token as an expression.
    pub(crate) fn tok_expr(&mut self, i: usize) -> Res<Expr> {
        let t = self.tok(i).clone();
        Ok(match t.k {
            K::Var => Expr::Var(self.vars.slot(&t.v)),
            K::Val => Expr::Val(self.val(&t)?),
            K::Enum => Expr::Enum(self.d.enums.intern(&t.v)),
            K::Intr if self.env.symbols.contains(&t.v) => Expr::Call(Callee::Prim(self.d.prims.intern("WellKnownSymbol")), vec![Expr::Val(ValLit::Str(t.v.clone(), String::new()))]),
            K::Intr => Expr::Intrinsic(self.d.fields.intern(&t.v)),
            K::Field => Expr::FieldName(self.d.fields.intern(&t.v)),
            K::Nt => {
                let (name, suffix) = split_nt(&t.v);
                let mut xs = Vec::new();
                if !suffix.is_empty() {
                    let inner = suffix.strip_prefix('[').and_then(|x| x.strip_suffix(']')).ok_or_else(|| format!("a grammar symbol's suffix {suffix:?}"))?;
                    for a in inner.split(", ") {
                        let (b, p) = match a.split_at(a.chars().next().map_or(0, |c| c.len_utf8())) {
                            ("+", p) => (true, p),
                            ("~", p) => (false, p),
                            _ => return Err(format!("a grammar symbol's parameter {a:?}")),
                        };
                        xs.push((self.d.params.get(p).ok_or_else(|| format!("parameter {p} not GL's"))?, b));
                    }
                }
                Expr::Nt(self.d.nts.intern(name), xs)
            }
            K::Gram => {
                let a = t.raw.find('>').map(|a| a + 1).unwrap_or(0);
                let inner = &t.raw[a..t.raw.len() - "</emu-grammar>".len()];
                let ps = self.env.gl.resolve(inner, &self.clause)?;
                if ps.is_empty() {
                    return Err("an empty grammar key".into());
                }
                Expr::Prod(ps, t.raw.clone())
            }
            K::Code if t.v.len() > 1 && t.v.ends_with('n') && t.v[..t.v.len() - 1].bytes().all(|b| b.is_ascii_digit()) => {
                Expr::Val(ValLit::BigN(parse_numeral(&t.v[..t.v.len() - 1])?))
            }
            K::Code => {
                let (c, w) = crate::text::literal(&t.v);
                Expr::Code(c, w)
            }
            K::Xref => self.xref(&t)?,
            K::Num => {
                if t.sub.is_some() {
                    return Err(format!("numeral with a subscript: {}", t.raw));
                }
                if let Some(h) = t.v.strip_prefix("U+") {
                    Expr::CodePoint(u128::from_str_radix(h, 16).unwrap(), h.to_string(), None)
                } else {
                    Expr::Math(Sign::None, Mag::Num(parse_numeral(&t.v)?))
                }
            }
            _ => return Err(format!("token {:?} as an expression", t.raw)),
        })
    }

    // ---------------------------------------------------------------- phrases

    /// A template rule's node as a phrase row and its holes.
    pub fn phrase(&mut self, n: &PNode) -> Res<(Id, Vec<Hole>)> {
        let Rid::R(ri) = n.rid else { return Err(format!("built-in {} as a phrase", n.name)) };
        let r = &self.g.rules[ri];
        let cat = match r.cat {
            "SI" | "SIn" => "Step",
            "ERI" => "ER",
            c => c,
        };
        let rr = if cat != r.cat { self.g.rules.iter().find(|x| x.cat == cat && x.name == r.name).unwrap() } else { r };
        let els = rr.elems.clone();
        let id = self.d.phrase(cat, r.name, || pieces(&els));
        let mut holes = Vec::new();
        self.holes(&r.elems, items_of(n), &mut holes)?;
        if r.name == "production-in" {
            for h in &holes {
                if let Hole::E(Expr::Xref(_, _, Some(c))) = h {
                    self.d.prod_clauses.insert(*c);
                }
            }
        }
        for &(_, k) in SYMBOL_HOLES.iter().filter(|x| x.0 == r.name) {
            if let Some(Hole::E(e)) = holes.get_mut(k) {
                *e = as_term(std::mem::replace(e, Expr::NewTarget));
            }
        }
        if let Some(&(_, _, bs)) = BINDER_CONDS.iter().find(|b| b.0 == cat && b.1 == r.name) {
            let xs = bs
                .iter()
                .map(|&k| match holes.get(k) {
                    Some(Hole::B(x) | Hole::E(Expr::Var(x))) => Ok(*x),
                    h => Err(format!("{}: binder hole {k} is {h:?}", r.name)),
                })
                .collect::<Res<Vec<_>>>()?;
            holes = holes.into_iter().map(|h| if let Hole::C(c) = h { Hole::Bc(xs.clone(), c) } else { h }).collect();
        }
        if NODE_SUBJECT.contains(&(cat, r.name)) {
            if let Some(h) = holes.iter_mut().find(|h| matches!(h, Hole::E(Expr::Nt(..)))) {
                let Hole::E(x) = std::mem::replace(h, Hole::W(0)) else { unreachable!() };
                *h = Hole::E(self.node_of(x));
            }
        }
        if let Some(&(_, _, prim, args, neg)) = BUILTIN_MEANINGS.iter().find(|m| m.0 == cat && m.1 == r.name) {
            let sl = slots(&rr.elems);
            let margs = args.iter().map(|a| meaning_arg(&sl, a)).collect::<Res<Vec<_>>>().map_err(|e| format!("{}: {e}", r.name))?;
            for a in &margs {
                if let MArg::Hole(f, true) = a {
                    let Some(Hole::Text(w)) = holes.get(*f) else { return Err(format!("{}: a field argument not words", r.name)) };
                    holes[*f] = Hole::Field(self.d.fields.intern(&w.clone()));
                }
                if let MArg::Spread(f) = a {
                    if *f + 1 != holes.len() || !matches!(holes[*f], Hole::L(..)) || holes[..*f].iter().any(|h| matches!(h, Hole::L(..))) || !matches!(margs.last(), Some(MArg::Spread(_))) {
                        return Err(format!("{}: a spread argument not the only and last list hole", r.name));
                    }
                }
            }
            for &(name, a, b) in SAME_HOLES {
                if name == r.name && holes.get(a) != holes.get(b) {
                    return Err(format!("{}: holes {a} and {b} differ", r.name));
                }
            }
            if self.d.phrases[id].meaning.is_none() {
                let prim = self.d.prims.get(prim).ok_or_else(|| format!("primitive {prim} not seeded"))?;
                let mut pargs = Vec::new();
                for a in margs.iter() {
                    pargs.push(match a {
                        MArg::Subject => crate::decls::PArg::Subject,
                        MArg::Hole(f, _) => crate::decls::PArg::Hole(*f),
                        MArg::Spread(f) => crate::decls::PArg::Spread(*f),
                        MArg::This => crate::decls::PArg::ThisNode,
                        MArg::Sort(n) => crate::decls::PArg::Sort(self.d.sorts.intern(n)),
                        MArg::Choice(k) => crate::decls::PArg::Choice(*k),
                    });
                }
                let args = pargs;
                self.d.phrases[id].meaning = Some(crate::decls::Meaning::Prim { prim, args, neg });
            }
        }
        self.overlay_meaning(cat, r.name, id, &holes)?;
        Ok((id, holes))
    }

    /// A use of the `PARSER_FORMS` row `name` of `cat` that a statement form is read through.
    fn parser_form(&mut self, cat: &'static str, name: &'static str, holes: Vec<Hole>) -> Res<Expr> {
        Ok(Expr::Phrase(self.parser_form_id(cat, name, &holes)?, holes))
    }

    /// The phrase row of the `PARSER_FORMS` row `name` of `cat`, used with `holes`.
    fn parser_form_id(&mut self, cat: &'static str, name: &'static str, holes: &[Hole]) -> Res<Id> {
        let &(_, _, t) = crate::grammar::PARSER_FORMS.iter().find(|f| f.0 == cat && f.1 == name).ok_or_else(|| format!("no parser form {cat} {name}"))?;
        let els = crate::engine::Rule::new(0, cat, name, t, 6, None).elems;
        let id = self.d.phrase(cat, name, || pieces(&els));
        self.overlay_meaning(cat, name, id, holes)?;
        Ok(id)
    }

    /// An `If` or `Else if` condition `L contains a T x such that C` whose consequent `body` reads
    /// `x`: the binding form `contains-such-binds`, `x` bound in the consequent.
    fn bind_such(&mut self, c: Cond, body: &impl std::fmt::Debug) -> Res<Cond> {
        if let Cond::Preds(l, Pred::Phrase(p, hs), rest) = &c {
            match hs.as_slice() {
                [w, t, Hole::E(Expr::Var(x)), Hole::Bc(xs, k)] if rest.is_empty() && self.d.phrases[*p].name == "contains-such" && reads(*x, body) => {
                    let holes = vec![w.clone(), t.clone(), Hole::B(*x), Hole::Bc(xs.clone(), k.clone())];
                    let id = self.parser_form_id("PRED", "contains-such-binds", &holes)?;
                    return Ok(Cond::Preds(l.clone(), Pred::Phrase(id, holes), vec![]));
                }
                _ => {}
            }
        }
        self.closed_such(&c, body)?;
        Ok(c)
    }

    /// Err when a `contains a T x such that C` in `c` binds an `x` that `body` reads: its
    /// meaning is closed.
    fn closed_such(&self, c: &Cond, body: &impl std::fmt::Debug) -> Res<()> {
        let open = |p: &Pred| match p {
            Pred::Phrase(id, hs) if self.d.phrases[*id].name == "contains-such" => matches!(hs.get(2), Some(Hole::E(Expr::Var(x))) if reads(*x, body)),
            _ => false,
        };
        match c {
            Cond::Preds(_, p, rest) if open(p) || rest.iter().any(|(_, q)| open(q)) => Err("contains-such: its variable read outside its condition".into()),
            Cond::And(_, cs) | Cond::Or(_, cs) => cs.iter().try_for_each(|c| self.closed_such(c, body)),
            Cond::Paren(c) => self.closed_such(c, body),
            _ => Ok(()),
        }
    }

    /// Phrase `id`'s meaning from the overlay entry that claims rule `name` of `cat`, if one does.
    fn overlay_meaning(&mut self, cat: &str, name: &str, id: Id, holes: &[Hole]) -> Res<()> {
        let Some(op) = self.g.overlay_phrase(cat, name) else { return Ok(()) };
        let vars = op.vars();
        for (i, v) in vars.iter().enumerate().filter(|_| !op.all_alternatives) {
            if let Some(j) = vars[..i].iter().position(|w| w == v) {
                if holes[i] != holes[j] {
                    return Err(format!("{}: _{v}_ bound to two expressions", op.id));
                }
            }
        }
        let selectors = self.g.phrase_layout(op).iter().filter(|&&w| w).count();
        if op.alg.is_some() && holes.len() != vars.len() + selectors {
            return Err(format!("{}: {} holes for {} parameters and {selectors} choices", op.id, holes.len(), vars.len()));
        }
        if self.d.phrases[id].meaning.is_none() && op.alg.is_some() {
            let c = self.d.clauses.get(&op.id).ok_or_else(|| format!("{}: its algorithm has no clause", op.id))?;
            self.d.phrases[id].meaning = Some(crate::decls::Meaning::Alg(c));
        }
        if self.d.phrases[id].meaning.is_none() {
            let mut args = Vec::new();
            for a in &op.args {
                args.push(match a {
                    crate::overlay::Arg::Enum(e) => crate::decls::PArg::Enum(self.d.enums.intern(e)),
                    crate::overlay::Arg::Field(f) => crate::decls::PArg::Field(self.d.fields.intern(f)),
                    crate::overlay::Arg::Var(v) if op.subject.as_deref() == Some(v.as_str()) => crate::decls::PArg::Subject,
                    crate::overlay::Arg::Var(v) => crate::decls::PArg::Hole(
                        vars.iter().position(|w| w == v).ok_or_else(|| format!("{}: _{v}_ not in the pattern", op.id))?,
                    ),
                });
            }
            let prim = self.d.prims.intern(&op.prim);
            self.d.phrases[id].meaning = Some(crate::decls::Meaning::Prim { prim, args, neg: op.neg });
        }
        Ok(())
    }

    fn holes(&mut self, els: &[(El, bool)], items: &[Item], out: &mut Vec<Hole>) -> Res<()> {
        for ((el, _), it) in els.iter().zip(items) {
            match (el, it) {
                (El::Lit(_), _) | (El::KindV(..), _) => {}
                (El::Kind(k), Item::T(i, _)) => out.push(match kind_hole(*k) {
                    HoleKind::Text => Hole::Text(self.tok(*i).v.clone()),
                    _ => Hole::E(self.tok_expr(*i)?),
                }),
                (El::Hole(c), Item::N(n, _)) => out.push(self.hole(c, n)?),
                (El::Hole(c), Item::P(i, j, _)) => {
                    let parts = self.prose(*i, *j);
                    out.push(match hole_kind(c) {
                        HoleKind::C => Hole::C(self.pcond(parts)),
                        HoleKind::T => Hole::T(TyExpr::Prose(parts)),
                        HoleKind::L => Hole::E(self.pexpr(parts)),
                        _ => Hole::E(self.pexpr(parts)),
                    });
                }
                (El::Opt(inner), Item::O(v, _)) => match v {
                    Some(v) => {
                        out.push(Hole::W(0));
                        self.holes(inner, v, out)?;
                    }
                    None => out.push(Hole::W(1)),
                },
                (El::Alt(alts), Item::A(k, v, _)) => {
                    out.push(Hole::W(*k));
                    self.holes(&alts[*k], v, out)?;
                }
                _ => return Err(format!("template element {el:?} against {it:?}")),
            }
        }
        Ok(())
    }

    /// A hole's content by its category.
    pub(crate) fn hole(&mut self, c: &str, n: &PNode) -> Res<Hole> {
        Ok(match hole_kind(c) {
            HoleKind::E => Hole::E(self.expr(n)?),
            HoleKind::C => Hole::C(self.cond(n)?),
            HoleKind::T if c.starts_with("HT") => Hole::T(self.ht(n)?),
            HoleKind::T => Hole::T(self.ty(n)?),
            HoleKind::B => Hole::B(self.bind(n)?),
            HoleKind::S => return Err("a statement hole in a phrase template".into()),
            HoleKind::L => {
                let (f, xs) = self.list(n)?;
                Hole::L(f, xs)
            }
            HoleKind::Text => Hole::Text(self.words(n)),
        })
    }

    fn words(&self, n: &PNode) -> String {
        n.items.iter().filter_map(|it| if let Item::T(i, _) = it { Some(self.tok(*i).v.clone()) } else { None }).collect::<Vec<_>>().join(" ")
    }

    pub(crate) fn bind(&mut self, n: &PNode) -> Res<Id> {
        match n.items.as_slice() {
            [Item::T(i, _)] if self.tok(*i).k == K::Var => {
                let v = self.tok(*i).v.clone();
                let n = self.vars.names.len();
                let x = self.vars.slot(&v);
                if x == n {
                    self.vars.bound.push(x);
                }
                Ok(x)
            }
            _ => Err("a binder that is not a variable".into()),
        }
    }

    /// A list node (Args, EL, ALT, ArgsP, FieldNames, FieldEL) and its form.
    fn list(&mut self, n: &PNode) -> Res<(ListForm, Vec<Expr>)> {
        self.list_at(n, &[])
    }

    /// A list node; a bare `|X|` at a position in `nts` is the grammar symbol.
    fn list_at(&mut self, n: &PNode, nts: &[usize]) -> Res<(ListForm, Vec<Expr>)> {
        match n.name {
            "args" => {
                let xs = match &n.items[1] {
                    Item::O(Some(v), _) => self.list_at(child(&v[0]).unwrap(), nts)?.1,
                    _ => vec![],
                };
                Ok((ListForm::Paren, xs))
            }
            "list" => {
                let xs = n.items.iter().filter_map(child).enumerate().map(|(k, c)| self.arg_at(c, nts.contains(&k))).collect::<Res<Vec<_>>>()?;
                Ok((ListForm::Comma, xs))
            }
            "elist" => {
                let conj = n.items.iter().find_map(|it| match it {
                    Item::L(w, _) if w == "and" => Some(Conj::And),
                    Item::L(w, _) if w == "or" => Some(Conj::Or),
                    _ => None,
                });
                let xs = n.items.iter().filter_map(child).map(|c| self.expr(c)).collect::<Res<Vec<_>>>()?;
                let f = ListForm::English(conj.unwrap());
                if crate::print::english_ok(n.items.len(), xs.len()) {
                    Ok((f, xs))
                } else {
                    Err("an English list in an irregular form".into())
                }
            }
            "elist1" => Ok((ListForm::Comma, vec![self.expr(child(&n.items[0]).unwrap())?])),
            _ => Err(format!("{} as a list", n.name)),
        }
    }

    /// The SDO row's productions, by their keys: the nonterminals of their right-hand sides.
    /// A bare `|X|` as a node where the row or an enclosing production test names one: a
    /// right-hand-side child (5), the row's own node (6), or a child of the tested node.
    fn node_of(&self, x: Expr) -> Expr {
        let Expr::Nt(k, xs) = x else { return x };
        let n = self.d.nts.name(k);
        let goal = || crate::print::goal_text(self.d, &xs);
        if self.lhs.contains(n) {
            Expr::Child(6, k, goal())
        } else if self.rhs.contains(n) {
            Expr::Child(5, k, goal())
        } else if let Some((y, _)) = self.narrow.iter().rev().find(|(_, r)| r.contains(n)) {
            Expr::ChildOf(Box::new(y.clone()), k, goal())
        } else {
            Expr::Nt(k, xs)
        }
    }

    /// The right-hand-side nonterminals of productions.
    fn prod_rhs(&self, ps: &[usize]) -> std::collections::HashSet<String> {
        prod_rhs(&self.env.gl, ps)
    }

    /// The narrowing an `If` condition `|Y| is <emu-grammar>P</emu-grammar>` gives its body, if it is one.
    fn narrowing(&self, c: &Cond) -> Option<(Expr, std::collections::HashSet<String>)> {
        match c {
            Cond::Preds(y @ (Expr::Child(..) | Expr::ChildOf(..)), Pred::IsVal(false, _, vs), rest) if rest.is_empty() => match vs.as_slice() {
                [Expr::Prod(ps, _)] => Some((y.clone(), self.prod_rhs(ps))),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn set_rhs(&mut self, keys: &[String]) {
        let gl = &self.env.gl;
        self.rhs.clear();
        self.lhs.clear();
        let mut every: Option<std::collections::HashSet<String>> = None;
        for k in keys {
            for p in gl.resolve(k, &self.clause).unwrap_or_default() {
                self.lhs.insert(gl.nts[gl.prods[p].lhs].clone());
                let mut here = std::collections::HashSet::new();
                if let Some(a) = gl.alt(gl.prods[p].at) {
                    for i in &a.rhs {
                        if let jsgrammar::grammar::Item::Sym(jsgrammar::grammar::Sym::Nt(n, _), _) | jsgrammar::grammar::Item::ButNot(jsgrammar::grammar::Sym::Nt(n, _), _) = i {
                            here.insert(n.clone());
                        }
                    }
                }
                self.rhs.extend(here.iter().cloned());
                every = Some(match every {
                    None => here,
                    Some(e) => e.intersection(&here).cloned().collect(),
                });
            }
        }
        // a left-hand side some production lacks on its right is the row's own node
        let every = every.unwrap_or_default();
        self.lhs.retain(|n| !every.contains(n));
    }

    // ---------------------------------------------------------------- expressions

    pub fn expr(&mut self, n: &PNode) -> Res<Expr> {
        self.arg_at(n, false)
    }

    /// An expression; `nt`: it is passed where a nonterminal is declared, so a bare `|X|` is the symbol.
    fn arg_at(&mut self, n: &PNode, nt: bool) -> Res<Expr> {
        let sym = std::mem::take(&mut self.symbols);
        let r = self.expr_at(n, sym || nt);
        self.symbols = sym;
        r
    }

    /// An expression; `sym`: a bare `|X|` here is the grammar symbol (`Conv::symbols`), which
    /// the expressions inside it do not inherit.
    fn expr_at(&mut self, n: &PNode, sym: bool) -> Res<Expr> {
        let it = &n.items;
        let c = |k: usize| child(&it[k]).unwrap();
        Ok(match n.name {
            "var" | "val" | "enum" | "intrinsic" | "nonterminal" | "field-name" | "xref" | "code" | "grammar-lit" | "fn"
                if matches!(it.as_slice(), [Item::T(..)]) =>
            {
                let Item::T(i, _) = it[0] else { unreachable!() };
                let x = self.tok_expr(i)?;
                if sym {
                    x
                } else {
                    self.node_of(x)
                }
            }
            "num" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                self.tok_expr(i)?
            }
            "table-step" => {
                let key = self.expr(c(3))?;
                let Some(Item::T(i, _)) = it.last() else { unreachable!() };
                match self.tok_expr(*i)? {
                    Expr::Table(t, x) => Expr::TableStep(t, Box::new(key), x),
                    _ => return Err("the value a key corresponds to in an xref that is not a table".into()),
                }
            }
            "extreme" => {
                let Item::A(k, _, _) = it[1] else { unreachable!() };
                let t = self.tn(c(2), String::new())?;
                let x = self.bind(c(3))?;
                let want = if k == 0 { Sign::Plus } else { Sign::Minus };
                if self.expr(c(7))? != Expr::Math(want, Mag::Inf) {
                    return Err("an extreme whose infinity is not its direction".into());
                }
                let cond = self.cond(c(11))?;
                self.d.extremes.push((self.clause.clone(), self.text.clone()));
                Expr::Extreme(k == 0, x, Box::new(t), Box::new(cond))
            }
            "call" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                let name = self.tok(i).v.clone();
                let nts = match self.env.ops.get(&name) {
                    Some(_) => self.env.nt_params.get(&name).cloned().unwrap_or_default(),
                    None => crate::sig::of(self.g, &name).map(|s| crate::sig::nt_params(&s.params)).unwrap_or_default(),
                };
                let (_, args) = self.list_at(c(1), &nts)?;
                let callee = match self.env.ops.get(&name) {
                    Some(&cl) => Callee::Alg(cl),
                    None => {
                        if let Some(why) = crate::sig::call(self.g, &name, args.len()) {
                            self.d.sig_errors.push(format!("{}: {name}: {why}", self.clause));
                        }
                        Callee::Prim(self.d.prims.intern(&name))
                    }
                };
                Expr::Call(callee, args)
            }
            "call-num" => {
                let Item::A(k, _, _) = &it[0] else { unreachable!() };
                let name = ["𝔽", "ℝ", "ℤ"][*k];
                let (_, args) = self.list(c(1))?;
                if let Some(why) = crate::sig::call(self.g, name, args.len()) {
                    self.d.sig_errors.push(format!("{}: {name}: {why}", self.clause));
                }
                Expr::Call(Callee::Prim(self.d.prims.intern(name)), args)
            }
            "paren" => Expr::Paren(Box::new(self.expr(c(1))?)),
            "list-lit" => {
                let xs = match &it[1] {
                    Item::O(Some(v), _) => self.list(child(&v[0]).unwrap())?.1,
                    _ => vec![],
                };
                Expr::List(xs)
            }
            "meta" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                let attrs = parse_attrs(&self.tok(i).raw["<emu-meta".len()..self.tok(i).raw.len() - 1])?;
                Expr::Annot(attrs, Box::new(self.expr(c(1))?))
            }
            "inf" => Expr::Math(Sign::None, Mag::Inf),
            "this" => self.this_value(false)?,
            "this-bare" => self.this_value(true)?,
            "newtarget" => match self.frame()? {
                Some((_, nt, _)) => Expr::Var(nt),
                None => Expr::NewTarget,
            },
            "this-parse-node" => Expr::ThisNode,
            "cs-nt" | "cs-var" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                self.tok_expr(i)?
            }
            "the-nt" | "cs-the" => {
                let Item::A(k, _, _) = it[1] else { unreachable!() };
                // `the fourth |X|` is 7: 5 and 6 are the bare `|X|`
                let k = if k == 5 { 7 } else { k };
                let Item::T(i, _) = it[2] else { unreachable!() };
                let v = self.tok(i).v.clone();
                let (name, suffix) = split_nt(&v);
                let (name, suffix) = (name.to_string(), suffix.to_string());
                Expr::Child(k, self.d.nts.intern(&name), suffix)
            }
            "cuname" => match &it[0] {
                Item::N(x, _) => self.expr(x)?,
                _ => self.cuname(n)?,
            },
            "sdo" | "sdo-arg" | "sdo-args" => self.sdo(n)?,
            "sdo-early" => Expr::Sdo(self.d.sdos.intern("Early Errors"), Article::None, Box::new(self.expr(c(3))?), vec![]),
            "rec" | "rec-empty" => self.record(n)?,
            "closure" | "closure-atomic" => return Err("a closure outside a step".into()),
            "unary:?" => Expr::Q(Box::new(self.expr(c(1))?)),
            "unary:!" => Expr::Bang(Box::new(self.expr(c(1))?)),
            "unary:-" | "unary:+" => {
                let sign = if n.name == "unary:-" { Sign::Minus } else { Sign::Plus };
                match self.expr(c(1))? {
                    Expr::Math(Sign::None, m) => Expr::Math(sign, m),
                    e if sign == Sign::Minus => Expr::Neg(Box::new(e)),
                    _ => return Err("unary + on a non-literal".into()),
                }
            }
            "field" => {
                let Item::T(i, _) = it[2] else { unreachable!() };
                let f = self.d.fields.intern(&self.tok(i).v.clone());
                Expr::Field(Box::new(self.expr(c(0))?), f)
            }
            "apply" => {
                let (_, args) = self.list(c(1))?;
                match self.expr(c(0))? {
                    Expr::Field(e, f) => Expr::IMethod(e, f, args),
                    f => Expr::Apply(Box::new(f), args),
                }
            }
            "mcall" => {
                let Item::T(i, _) = it[2] else { unreachable!() };
                let m = self.d.methods.intern(&self.tok(i).v.clone());
                let (_, args) = self.list(c(3))?;
                Expr::CMethod(Box::new(self.expr(c(0))?), m, args)
            }
            "index" => Expr::Index(Box::new(self.expr(c(0))?), Box::new(self.expr(c(2))?)),
            "pow" => Expr::Bin(BinOp::Pow, Box::new(self.expr(c(0))?), Box::new(self.expr(c(2))?)),
            "poss" => {
                let words = it[2..].iter().map(|x| if let Item::T(i, _) = x { self.tok(*i).v.clone() } else { String::new() });
                let words: Vec<String> = words.collect();
                let id = self.d.phrase("P", "poss", || vec![Piece::Hole(HoleKind::E), Piece::Glue, Piece::Word("'s".into()), Piece::Hole(HoleKind::Text)]);
                if self.d.phrases[id].meaning.is_none() {
                    let &(_, _, prim, _, neg) = BUILTIN_MEANINGS.iter().find(|m| m.0 == "P" && m.1 == "poss").unwrap();
                    let prim = self.d.prims.get(prim).ok_or_else(|| format!("primitive {prim} not seeded"))?;
                    let args = vec![crate::decls::PArg::Hole(0), crate::decls::PArg::Hole(1)];
                    self.d.phrases[id].meaning = Some(crate::decls::Meaning::Prim { prim, args, neg });
                }
                Expr::Phrase(id, vec![Hole::E(self.expr(c(0))?), Hole::Field(self.d.fields.intern(&words.join(" ")))])
            }
            name if name.starts_with("arith:") => {
                let op = match &name[6..] {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "×" => BinOp::Mul,
                    "/" => BinOp::Div,
                    "modulo" => BinOp::Modulo,
                    "plus" => BinOp::Plus,
                    "times" => BinOp::Times,
                    o => return Err(format!("operator {o}")),
                };
                Expr::Bin(op, Box::new(self.expr(c(0))?), Box::new(self.expr(c(2))?))
            }
            "elist1" | "hs-e" | "hs-h" | "hv-e" => self.expr(c(0))?,
            "occurrences" => {
                let id = self.d.phrase("P", "occurrences", || {
                    vec![Piece::Hole(HoleKind::E), Piece::Word("occurrences".into()), Piece::Word("of".into()), Piece::Hole(HoleKind::E)]
                });
                let holes = vec![Hole::E(self.expr(c(0))?), Hole::E(self.expr(c(3))?)];
                self.overlay_meaning("P", "occurrences", id, &holes)?;
                Expr::Phrase(id, holes)
            }
            "that-is" => {
                let holes = vec![Hole::E(self.expr(c(0))?), Hole::E(self.expr(c(5))?)];
                self.parser_form("P", "that-is", holes)?
            }
            "grammar-param" => {
                let Item::A(_, alt, _) = &it[0] else { return Err("a grammar parameter".into()) };
                let Some(Item::T(i, _)) = alt.first() else { return Err("a grammar parameter".into()) };
                let v = self.tok(*i).v.clone();
                Expr::Param(self.d.params.get(&v).ok_or_else(|| format!("grammar parameter {v}"))?)
            }
            "if-and-if" => {
                let id = self.d.phrase("P", "if-and-if", || {
                    let w = |s: &str| Piece::Word(s.into());
                    vec![Piece::Hole(HoleKind::E), w("if"), Piece::Hole(HoleKind::C), w("and"), Piece::Hole(HoleKind::E), w("if"), Piece::Hole(HoleKind::C)]
                });
                let holes = vec![Hole::E(self.expr(c(0))?), Hole::C(self.cond(c(2))?), Hole::E(self.expr(c(4))?), Hole::C(self.cond(c(6))?)];
                self.overlay_meaning("P", "if-and-if", id, &holes)?;
                Expr::Phrase(id, holes)
            }
            "resumed-with" => Expr::ResumedWith(Box::new(self.expr(c(5))?)),
            _ => match n.rid {
                Rid::R(_) => {
                    let (p, h) = self.phrase(n)?;
                    Expr::Phrase(p, h)
                }
                Rid::B(b) => return Err(format!("built-in {b} as an expression")),
            },
        })
    }

    fn cuname(&mut self, n: &PNode) -> Res<Expr> {
        let Item::T(i, _) = n.items[0] else { unreachable!() };
        let num = self.tok(i).v.clone();
        let name: Vec<String> = n.items[2..n.items.len() - 1]
            .iter()
            .map(|x| if let Item::T(k, _) = x { self.tok(*k).v.clone() } else { String::new() })
            .collect();
        let name = Some(name.join(" "));
        Ok(if let Some(h) = num.strip_prefix("0x") {
            Expr::CodeUnit(u128::from_str_radix(h, 16).unwrap(), h.to_string(), name)
        } else {
            let h = num.strip_prefix("U+").unwrap();
            Expr::CodePoint(u128::from_str_radix(h, 16).unwrap(), h.to_string(), name)
        })
    }

    fn sdo(&mut self, n: &PNode) -> Res<Expr> {
        let it = &n.items;
        let art = match &it[0] {
            Item::O(Some(_), _) => Article::The,
            _ => Article::None,
        };
        let Item::T(i, _) = it[1] else { unreachable!() };
        let name = self.tok(i).v.clone();
        let subj = self.expr(child(&it[3]).unwrap())?;
        let args = match n.name {
            "sdo-arg" => vec![self.expr(child(&it[6]).unwrap())?],
            "sdo-args" => {
                let (f, xs) = self.list(child(&it[6]).unwrap())?;
                if f != ListForm::English(Conj::And) {
                    return Err("SDO arguments not an and-list".into());
                }
                xs
            }
            _ => vec![],
        };
        if self.env.components.contains(&name) && args.is_empty() {
            return Ok(Expr::Component(self.d.fields.intern(&name), art, Box::new(subj)));
        }
        if self.d.sdos.get(&name).is_none() {
            self.unresolved.push(name.clone());
        }
        Ok(Expr::Sdo(self.d.sdos.intern(&name), art, Box::new(subj), args))
    }

    fn record(&mut self, n: &PNode) -> Res<Expr> {
        let it = &n.items;
        let art = match &it[0] {
            Item::O(Some(_), _) => Article::The,
            _ => Article::None,
        };
        let kind = match &it[1] {
            Item::O(Some(v), _) => Some(self.d.sorts.intern(&self.words(child(&v[0]).unwrap()))),
            _ => None,
        };
        let mut fs = Vec::new();
        if n.name == "rec" {
            let fl = child(&it[3]).unwrap();
            for f in fl.items.iter().filter_map(child) {
                let Item::T(i, _) = f.items[0] else { unreachable!() };
                let fid = self.d.fields.intern(&self.tok(i).v.clone());
                fs.push((fid, self.expr(child(&f.items[2]).unwrap())?));
            }
        }
        Ok(Expr::Record(art, kind, fs))
    }

    /// The innermost open closure's frame slots, allocated on first use; None outside every closure.
    fn frame(&mut self) -> Res<Option<(Id, Id, Id)>> {
        self.frame_as(THIS)
    }

    /// `frame`, its *this* value slot named `this` if allocated here.
    fn frame_as(&mut self, this: &str) -> Res<Option<(Id, Id, Id)>> {
        let Some(&(site, _)) = self.open.last() else { return Ok(None) };
        if self.open.len() > 1 {
            return Err(format!("{FRAME_ERR}a read in a nested closure"));
        }
        if self.closures[site].frame.is_none() {
            let f = (self.vars.slot(this), self.vars.slot(NEW_TARGET), self.vars.slot(&format!("{FRAME}{ARGUMENTS}")));
            self.closures[site].frame = Some(f);
        }
        Ok(self.closures[site].frame)
    }

    /// The *this* value (`bare`: without "the"): its frame slot inside a closure, one form per closure.
    fn this_value(&mut self, bare: bool) -> Res<Expr> {
        let name = if bare { THIS_BARE } else { THIS };
        let Some((t, nt, a)) = self.frame_as(name)? else { return Ok(Expr::ThisValue(bare)) };
        let (site, seen) = self.open.last_mut().unwrap();
        let site = *site;
        match seen {
            Some(b) if *b != bare => return Err(format!("{FRAME_ERR}both the *this* value and *this* value read")),
            Some(_) => return Ok(Expr::Var(t)),
            None => *seen = Some(bare),
        }
        let t = if self.vars.names[t] == name { t } else { self.vars.slot(name) };
        self.closures[site].frame = Some((t, nt, a));
        Ok(Expr::Var(t))
    }

    fn closure(&mut self, n: &PNode, kids: &[Step]) -> Res<Expr> {
        let it = &n.items;
        let tn = self.words(child(&it[2]).unwrap());
        let kind = match tn.as_str() {
            "Abstract Closure" => CloKind::Abstract,
            "Job Abstract Closure" => CloKind::Job,
            "Matcher" => CloKind::Matcher,
            "MatcherContinuation" => CloKind::MatcherContinuation,
            "read-modify-write modification function" => CloKind::ReadModifyWrite,
            k => return Err(format!("closure kind {k}")),
        };
        let params = match &it[4] {
            Item::A(0, _, _) => None,
            Item::A(_, v, _) => {
                let n = self.vars.names.len();
                let (_, xs) = self.list(child(&v[1]).unwrap())?;
                self.vars.bound.extend(n..self.vars.names.len());
                Some(xs.into_iter().map(|x| if let Expr::Var(s) = x { Ok(s) } else { Err("a closure parameter that is not a variable".to_string()) }).collect::<Res<Vec<_>>>()?)
            }
            _ => unreachable!(),
        };
        let caps = match &it[7] {
            Item::A(0, _, _) => vec![],
            Item::A(_, v, _) => {
                let e = child(&v[0]).unwrap();
                let (_, xs) = if e.name == "elist1" { (ListForm::Comma, vec![self.expr(child(&e.items[0]).unwrap())?]) } else { self.list(e)? };
                if e.name == "elist" && !matches!(self.list(e)?.0, ListForm::English(Conj::And)) {
                    return Err("captures not an and-list".into());
                }
                xs.into_iter().map(|x| if let Expr::Var(s) = x { Ok(s) } else { Err("a capture that is not a variable".to_string()) }).collect::<Res<Vec<_>>>()?
            }
            _ => unreachable!(),
        };
        let site = self.closures.len();
        self.closures.push(CloLit { kind, atomic: n.name == "closure-atomic", params, caps, body: vec![], frame: None });
        self.open.push((site, None));
        let body = self.steps(kids);
        self.open.pop();
        self.closures[site].body = body;
        Ok(Expr::Closure(site))
    }

    /// A step's nested steps as an Abstract Closure with no parameters, capturing the variables
    /// bound before it that they read.
    fn steps_closure(&mut self, kids: &[Step]) -> Expr {
        let known = self.vars.names.len();
        let site = self.closures.len();
        self.closures.push(CloLit { kind: CloKind::Abstract, atomic: false, params: None, caps: (0..known).collect(), body: vec![], frame: None });
        self.open.push((site, None));
        let body = self.steps(kids);
        self.open.pop();
        self.closures[site].caps = (0..known).filter(|&x| reads(x, &body)).collect();
        self.closures[site].body = body;
        Expr::Closure(site)
    }

    // ---------------------------------------------------------------- conditions

    pub fn cond(&mut self, n: &PNode) -> Res<Cond> {
        if n.name.starts_with("cond:") {
            return self.conn(n);
        }
        let it = &n.items;
        let c = |k: usize| child(&it[k]).unwrap();
        Ok(match n.name {
            "pred" => {
                let subj = self.expr(c(0))?;
                let saved = std::mem::replace(&mut self.symbols, matches!(subj, Expr::Var(_)));
                let r = self.preds(c(1));
                self.symbols = saved;
                let (p, rest) = r?;
                Cond::Preds(subj, p, rest)
            }
            "rel" => {
                let Item::A(k, _, _) = it[1] else { unreachable!() };
                let op = [RelOp::Lt, RelOp::Le, RelOp::Gt, RelOp::Ge, RelOp::Eq, RelOp::Ne][k];
                Cond::Rel(op, self.expr(c(0))?, self.expr(c(2))?)
            }
            "paren" => Cond::Paren(Box::new(self.cond(c(1))?)),
            "alg-true" => {
                let Some(Item::T(i, _)) = it.last() else { unreachable!() };
                let raw = self.tok(*i).raw.clone();
                let inner = raw.find('>').map(|a| &raw[a + 1..raw.len() - "</emu-alg>".len()]).unwrap_or("");
                let idx = *self.env.algs.get(&(self.clause.clone(), inner.to_string())).ok_or("an emu-alg not in its clause")?;
                let c = self.d.clauses.get(&self.clause).ok_or("a clause without an id")?;
                Cond::Alg(c, idx, raw)
            }
            "both-following" => match self.cond(it.last().and_then(child).unwrap())? {
                Cond::And(ConnForm::Plain, cs) if cs.len() == 2 => Cond::And(ConnForm::Following, cs),
                _ => return Err("both of the following conditions, not two".into()),
            },
            "cond-orif" => Cond::Or(ConnForm::OrIf, vec![self.cond(c(0))?, self.cond(it.last().and_then(child).unwrap())?]),
            "cond-iff" => {
                let words = crate::grammar::OUTER_CONNS.iter().find(|x| x.0 == n.name).unwrap().1;
                let id = self.d.phrase("CA", &n.name[5..], || {
                    let mut ps = vec![Piece::Hole(HoleKind::C)];
                    ps.extend(words.iter().map(|w| Piece::Word(w.to_string())));
                    ps.push(Piece::Hole(HoleKind::C));
                    ps
                });
                let holes = vec![Hole::C(self.cond(c(0))?), Hole::C(self.cond(it.last().and_then(child).unwrap())?)];
                self.overlay_meaning("CA", &n.name[5..], id, &holes)?;
                Cond::Phrase(id, holes)
            }
            "hc" | "hc-one" | "hca-c" => self.cond(c(0))?,
            "hc-and" => Cond::And(ConnForm::Plain, vec![self.cond(c(0))?, self.cond(c(2))?]),
            "hc-subj" => {
                let subj = self.expr(c(0))?;
                let (p, rest) = self.preds(c(1))?;
                Cond::Preds(subj, p, rest)
            }
            _ => {
                let (p, h) = self.phrase(n)?;
                Cond::Phrase(p, h)
            }
        })
    }

    /// A chain of conditions and connectives, left-associated by the parser.
    fn conn(&mut self, n: &PNode) -> Res<Cond> {
        // flatten the left spine: c0 conn1 c1 conn2 c2 …
        let mut conds = Vec::new();
        let mut conns: Vec<Vec<String>> = Vec::new();
        let mut cur = n;
        loop {
            if !cur.name.starts_with("cond:") {
                conds.push(cur);
                break;
            }
            let last = child(cur.items.last().unwrap()).unwrap();
            conds.push(last);
            conns.push(cur.items[1..cur.items.len() - 1].iter().map(|x| if let Item::L(w, _) = x { w.clone() } else { String::new() }).collect());
            cur = child(&cur.items[0]).unwrap();
        }
        conds.reverse();
        conns.reverse();
        let cs = conds.into_iter().map(|c| self.cond(c)).collect::<Res<Vec<_>>>()?;
        build_conn(cs, &conns)
    }

    fn preds(&mut self, n: &PNode) -> Res<(Pred, Vec<(Conj, Pred)>)> {
        let mut first = None;
        let mut rest = Vec::new();
        let mut conj = None;
        for it in &n.items {
            match it {
                Item::N(p, _) => {
                    let p = self.pred(p)?;
                    match conj.take() {
                        None => first = Some(p),
                        Some(c) => rest.push((c, p)),
                    }
                }
                Item::L(w, _) => conj = Some(if w == "and" { Conj::And } else { Conj::Or }),
                _ => return Err("predicate list".into()),
            }
        }
        Ok((first.unwrap(), rest))
    }

    fn alt_items(&mut self, n: &PNode, conj: Conj) -> Res<Vec<Expr>> {
        let (f, xs) = self.list(n)?;
        if f != ListForm::English(conj) {
            return Err("alternatives not an or-list".into());
        }
        Ok(xs)
    }

    fn pred(&mut self, n: &PNode) -> Res<Pred> {
        let it = &n.items;
        let c = |k: usize| child(&it[k]).unwrap();
        Ok(match n.name {
            "is" => Pred::IsVal(false, AltForm::Or, vec![self.expr(c(1))?]),
            "is-not" => Pred::IsVal(true, AltForm::Or, vec![self.expr(c(2))?]),
            "either" => Pred::IsVal(false, AltForm::Either, self.alt_items(c(2), Conj::Or)?),
            "is-alt" => Pred::IsVal(false, AltForm::Or, self.alt_items(c(1), Conj::Or)?),
            "one-of" => Pred::IsVal(false, AltForm::OneOf, symbols(self.alt_items(c(3), Conj::Or)?)),
            "not-one-of" => Pred::IsVal(true, AltForm::OneOf, symbols(self.alt_items(c(4), Conj::Or)?)),
            "neither" => Pred::IsVal(false, AltForm::Neither, vec![self.expr(c(2))?, self.expr(c(4))?]),
            "is-type" => Pred::IsTy(false, AltForm::Or, vec![self.ty(c(1))?]),
            "is-not-type" => Pred::IsTy(true, AltForm::Or, vec![self.ty(c(2))?]),
            "is-type-or" => Pred::IsTy(false, AltForm::Or, vec![self.ty(c(1))?, self.ty(c(3))?]),
            "not-type-nor" => Pred::IsTy(false, AltForm::Neither, vec![self.ty(c(2))?, self.ty(c(4))?]),
            "is-type-either" => Pred::IsTy(false, AltForm::Either, vec![self.ty(c(2))?, self.ty(c(4))?]),
            "either-types" => {
                let neg = matches!(it[1], Item::O(Some(_), _));
                let ts = c(3);
                if !ts.items.iter().any(|x| matches!(x, Item::L(w, _) if w == "or")) {
                    return Err("type alternatives not an or-list".into());
                }
                let ts = ts.items.iter().filter_map(child).map(|t| self.ty(t)).collect::<Res<Vec<_>>>()?;
                Pred::IsTy(neg, AltForm::Either, ts)
            }
            _ => {
                let (p, h) = self.phrase(n)?;
                Pred::Phrase(p, h)
            }
        })
    }

    // ---------------------------------------------------------------- types

    pub fn ty(&mut self, n: &PNode) -> Res<TyExpr> {
        let it = &n.items;
        let c = |k: usize| child(&it[k]).unwrap();
        let article = |it: &Item| match it {
            Item::A(0, _, _) => "a".to_string(),
            Item::A(_, _, _) => "an".to_string(),
            _ => String::new(),
        };
        Ok(match n.name {
            "a" => self.tn(c(1), article(&it[0]))?,
            "type" | "type-of" => self.tn(n, String::new())?,
            "elist" => {
                let ts = it.iter().filter_map(child).map(|t| self.ty(t)).collect::<Res<Vec<_>>>()?;
                if !it.iter().any(|x| matches!(x, Item::L(w, _) if w == "or")) || !crate::print::english_ok(it.len(), ts.len()) {
                    return Err("type alternatives not an or-list".into());
                }
                TyExpr::Union(AltForm::Or, ConnForm::Plain, ts)
            }
            "a-list-of" => TyExpr::ListOf(article(&it[0]), Box::new(self.tn(c(3), String::new())?)),
            "a-nt" => {
                let Item::T(i, _) = it[1] else { unreachable!() };
                let v = self.tok(i).v.clone();
                let (name, suffix) = split_nt(&v);
                let (name, suffix) = (name.to_string(), suffix.to_string());
                TyExpr::Nt(article(&it[0]), self.d.nts.intern(&name), suffix)
            }
            "a-var" => {
                let Item::T(i, _) = it[1] else { unreachable!() };
                let v = self.tok(i).v.clone();
                TyExpr::Var(article(&it[0]), self.vars.slot(&v))
            }
            "a-nt-that" => {
                let Item::T(i, _) = it[1] else { unreachable!() };
                let v = self.tok(i).v.clone();
                let (name, suffix) = split_nt(&v);
                let (name, suffix) = (name.to_string(), suffix.to_string());
                let t = TyExpr::Nt(article(&it[0]), self.d.nts.intern(&name), suffix);
                let (p, rest) = self.preds(c(3))?;
                TyExpr::That(Box::new(t), p, rest)
            }
            "a-that" => {
                let t = self.tn(c(1), article(&it[0]))?;
                let (p, rest) = self.preds(c(3))?;
                TyExpr::That(Box::new(t), p, rest)
            }
            _ => match n.rid {
                Rid::R(_) => {
                    let (p, h) = self.phrase(n)?;
                    TyExpr::Phrase(p, h)
                }
                Rid::B(b) => return Err(format!("built-in {b} as a type")),
            },
        })
    }

    /// A type noun: modifiers and a sort, or `List of T`.
    pub(crate) fn tn(&mut self, n: &PNode, article: String) -> Res<TyExpr> {
        if n.name == "type-of" {
            let outer = child(&n.items[0]).unwrap();
            if self.words(outer) != "List" {
                return Err(format!("type {} of", self.words(outer)));
            }
            return Ok(TyExpr::ListOf(article, Box::new(self.tn(child(&n.items[2]).unwrap(), String::new())?)));
        }
        let ws: Vec<String> = self.words(n).split(' ').map(str::to_string).collect();
        let mut k = 0;
        while k + 1 < ws.len() && MODS.contains(&ws[k].as_str()) {
            k += 1;
        }
        let mut mods = Vec::new();
        let mut i = 0;
        while i < k {
            let two = (i + 1 < k).then(|| format!("{} {}", ws[i], ws[i + 1])).filter(|t| self.d.sort_names.contains(t));
            mods.push(self.d.sorts.intern(two.as_deref().unwrap_or(&ws[i])));
            i += if two.is_some() { 2 } else { 1 };
        }
        let (s, written) = self.d.sort_of(&ws[k..].join(" "));
        let t = TyExpr::Sort(article, mods, s, written);
        Ok(match sort_context(self.g, self.d, s).and_then(|(p, v)| Some((p, self.in_scope(&v)?))) {
            Some((p, x)) => TyExpr::That(Box::new(t), Pred::Phrase(p, vec![Hole::E(Expr::Var(x))]), vec![]),
            None => t,
        })
    }

    /// The slot of the variable named `v` where the step being converted reads it: one met
    /// already and, inside closure literals, a parameter or capture of each.
    fn in_scope(&self, v: &str) -> Option<Id> {
        let x = self.vars.names.iter().position(|n| n == v)?;
        let seen = |c: &CloLit| c.caps.contains(&x) || c.params.as_ref().is_some_and(|ps| ps.contains(&x));
        self.open.iter().all(|&(k, _)| self.closures.get(k).is_some_and(seen)).then_some(x)
    }

    // ---------------------------------------------------------------- statements

    /// A step's statement (without If/Else grouping); `kids` are the step's children.
    pub fn stmt(&mut self, n: &PNode, kids: &[Step]) -> Res<Stmt> {
        let it = &n.items;
        let c = |k: usize| child(&it[k]);
        let e = |cv: &mut Self, k: usize| -> Res<Expr> {
            match &it[k] {
                Item::N(x, _) => cv.expr(x),
                Item::P(i, j, _) => {
                    let p = cv.prose(*i, *j);
                    Ok(cv.pexpr(p))
                }
                _ => Err("expression slot".into()),
            }
        };
        let cnd = |cv: &mut Self, k: usize| -> Res<Cond> {
            match &it[k] {
                Item::N(x, _) => cv.cond(x),
                Item::P(i, j, _) => {
                    let p = cv.prose(*i, *j);
                    Ok(cv.pcond(p))
                }
                _ => Err("condition slot".into()),
            }
        };
        let inline = |cv: &mut Self, k: usize| -> Res<Box<Stmt>> { Ok(Box::new(cv.stmt(c(k).unwrap(), &[])?)) };
        let no_kids = |_: &mut Self| -> Res<()> { if kids.is_empty() { Ok(()) } else { Err("nested steps under a step that has none".into()) } };
        let st = match n.name {
            "let" => {
                no_kids(self)?;
                Stmt::Let(self.bind(c(1).unwrap())?, e(self, 3)?)
            }
            "let-closure" => {
                let x = self.bind(c(1).unwrap())?;
                Stmt::Let(x, self.closure(c(3).unwrap(), kids)?)
            }
            "return-closure" => Stmt::Ret(Some(self.closure(c(1).unwrap(), kids)?)),
            "set" => {
                no_kids(self)?;
                let place = match e(self, 1)? {
                    Expr::Var(x) => Place::Var(x),
                    Expr::Field(b, f) => Place::Field(*b, f),
                    x => Place::Expr(x),
                };
                Stmt::Set(place, e(self, 3)?)
            }
            "set-definition" | "set-as-specified" => {
                no_kids(self)?;
                let place = match e(self, 1)? {
                    Expr::Var(x) => Place::Var(x),
                    Expr::Field(b, f) => Place::Field(*b, f),
                    x => Place::Expr(x),
                };
                let as_specified = n.name == "set-as-specified";
                let Item::T(i, _) = it[if as_specified { 5 } else { 7 }] else { return Err("set-definition: no xref".into()) };
                match self.tok_expr(i)? {
                    x @ Expr::Xref(..) => Stmt::Set(place, Expr::Definition(Box::new(x), as_specified)),
                    _ => return Err("set-definition: an xref to a table".into()),
                }
            }
            "return" => {
                no_kids(self)?;
                Stmt::Ret(Some(e(self, 1)?))
            }
            "return-unit" => Stmt::Ret(None),
            "perform" => {
                no_kids(self)?;
                Stmt::Perform(e(self, 1)?)
            }
            "if-then" => {
                let c = cnd(self, 1)?;
                let nw = self.narrowing(&c);
                let pushed = nw.map(|x| self.narrow.push(x)).is_some();
                let body = self.steps(kids);
                if pushed {
                    self.narrow.pop();
                }
                Stmt::If(self.bind_such(c, &body)?, Body::Block(body), vec![], None)
            }
            "if-inline" => {
                no_kids(self)?;
                let c = cnd(self, 1)?;
                let nw = self.narrowing(&c);
                let pushed = nw.map(|x| self.narrow.push(x)).is_some();
                let body = inline(self, 3);
                if pushed {
                    self.narrow.pop();
                }
                let body = body?;
                Stmt::If(self.bind_such(c, &body)?, Body::Inline(body), vec![], None)
            }
            "if-else-inline" => {
                no_kids(self)?;
                Stmt::IfElse(cnd(self, 1)?, inline(self, 3)?, inline(self, 6)?)
            }
            "assert" => Stmt::Assert(cnd(self, 2)?),
            "assert-if" => Stmt::AssertIf(cnd(self, 3)?, cnd(self, 6)?),
            "unreachable" => Stmt::Unreachable(0),
            "throw" => {
                let Item::T(i, _) = it[2] else { unreachable!() };
                let v = self.tok(i).v.clone();
                if !is_error_name(&v) || self.tok(i).sub.is_some() {
                    return Err(format!("throw of {v}"));
                }
                let id = self.d.fields.intern(&v);
                let art = if matches!(it[1], Item::A(0, _, _)) { "a" } else { "an" };
                if art != crate::print::article_for(&v) {
                    return Err(format!("article {art} before {v}"));
                }
                Stmt::ThrowErr(id)
            }
            "throw-value" => Stmt::ThrowVal(e(self, 1)?),
            "syntax-error" => {
                let early = matches!(it[2], Item::A(1, _, _));
                let c = cnd(self, 6)?;
                let unless = match &it[7] {
                    Item::O(Some(v), _) => {
                        let Item::A(k, w, _) = &v[0] else { unreachable!() };
                        let tag = |cv: &Self, x: &Item, want: &str| matches!(x, Item::T(i, _) if cv.tok(*i).raw == want);
                        let (form, at) = match k {
                            0 => (UnlessForm::Plain, 1),
                            1 => (UnlessForm::Comma, 2),
                            _ if tag(self, &w[0], crate::print::OPT_OPEN) && tag(self, &w[4], "</span>") => (UnlessForm::Optional, 3),
                            _ => return Err("an exception in a span that is not normative-optional".into()),
                        };
                        Some((form, self.slot_cond(&w[at])?))
                    }
                    _ => None,
                };
                Stmt::SyntaxError(early, c, unless)
            }
            "note" => {
                let p = child(&it[2]).unwrap();
                let Item::P(i, j, _) = p.items[0] else { unreachable!() };
                Stmt::Note(vec![Part::Text(self.text[self.toks[i].s..self.toks[j - 1].e].to_string())])
            }
            "repeat" => Stmt::Repeat(self.steps(kids)),
            "repeat-while" => Stmt::RepeatWhile(cnd(self, 3)?, self.steps(kids)),
            "repeat-until" => Stmt::RepeatUntil(cnd(self, 3)?, self.steps(kids)),
            "foreach" | "foreach-rev" => {
                let x = self.bind(c(3).unwrap())?;
                let l = e(self, 5)?;
                Stmt::ForEach(x, None, l, n.name == "foreach-rev", Body::Block(self.steps(kids)))
            }
            "foreach-typed" | "foreach-typed-rev" => {
                let t = match &it[2] {
                    Item::N(t, _) if t.name == "elist" => {
                        let ts = t.items.iter().filter_map(child).map(|x| self.tn(x, String::new())).collect::<Res<Vec<_>>>()?;
                        if ts.len() != 2 {
                            return Err("type nouns in an irregular form".into());
                        }
                        TyExpr::Union(AltForm::Or, ConnForm::Plain, ts)
                    }
                    Item::N(t, _) => self.tn(t, String::new())?,
                    Item::P(i, j, _) => TyExpr::Prose(self.prose(*i, *j)),
                    _ => unreachable!(),
                };
                let x = self.bind(c(3).unwrap())?;
                let l = e(self, 5)?;
                Stmt::ForEach(x, Some(t), l, n.name == "foreach-typed-rev", Body::Block(self.steps(kids)))
            }
            "foreach-backwards" => {
                let t = match &it[2] {
                    Item::N(t, _) => self.tn(t, String::new())?,
                    Item::P(i, j, _) => TyExpr::Prose(self.prose(*i, *j)),
                    _ => unreachable!(),
                };
                let x = self.bind(c(3).unwrap())?;
                let l = e(self, 5)?;
                let l = self.parser_form("P", "iter-backwards", vec![Hole::E(l)])?;
                Stmt::ForEach(x, Some(t), l, false, Body::Block(self.steps(kids)))
            }
            "foreach-nt" => {
                let Item::T(i, _) = it[2] else { unreachable!() };
                let v = self.tok(i).v.clone();
                let (name, suffix) = split_nt(&v);
                let (name, suffix) = (name.to_string(), suffix.to_string());
                let t = TyExpr::Nt(String::new(), self.d.nts.intern(&name), suffix);
                let x = self.bind(c(3).unwrap())?;
                let l = e(self, 5)?;
                Stmt::ForEach(x, Some(t), l, false, Body::Block(self.steps(kids)))
            }
            "foreach-recpat" => {
                let fl = c(4).unwrap();
                let fs = fl
                    .items
                    .iter()
                    .filter_map(child)
                    .map(|f| {
                        let Item::T(i, _) = f.items[0] else { unreachable!() };
                        let v = self.tok(i).v.clone();
                        self.d.fields.intern(&v)
                    })
                    .collect();
                let x = self.bind(c(6).unwrap())?;
                let l = e(self, 8)?;
                Stmt::ForEachRec(fs, x, l, Body::Block(self.steps(kids)))
            }
            "macro" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                let name = self.tok(i).v.clone();
                match self.env.ops.get(&name) {
                    Some(&cl) => {
                        let (_, args) = self.list(c(1).unwrap())?;
                        Stmt::Macro(cl, args)
                    }
                    None => return Err(format!("macro {name} names no operation")),
                }
            }
            "find-such-that" => {
                let Item::A(a, _, _) = it[1] else { unreachable!() };
                let t = self.tn(c(2).unwrap(), (if a == 0 { "a" } else { "an" }).to_string())?;
                let x = self.bind(c(3).unwrap())?;
                let k = cnd(self, 6)?;
                let e = self.expr(c(it.len() - 2).unwrap())?;
                Stmt::FindSuchThat(x, t, k, "because some argument is out of range".into(), Box::new(Stmt::Ret(Some(e))))
            }
            "let-such-that" => {
                let xs = c(1).unwrap().items.iter().filter_map(child).map(|v| self.bind(v)).collect::<Res<Vec<_>>>()?;
                let k = cnd(self, 6)?;
                let mut objs = Vec::new();
                let mut at = c(12).cloned();
                while let Some(o) = at {
                    let obj = child(&o.items[0]).ok_or("an objective")?.clone();
                    let Item::A(dir, _, _) = obj.items[3] else { return Err("an objective's direction".into()) };
                    objs.push((dir == 1, self.expr(child(&obj.items[0]).ok_or("an objective's expression")?)?));
                    at = o.items.get(5).and_then(child).cloned();
                }
                Stmt::LetSuchThat(xs, k, objs)
            }
            "let-such-that-any" => {
                let xs = c(1).unwrap().items.iter().filter_map(child).map(|v| self.bind(v)).collect::<Res<Vec<_>>>()?;
                Stmt::LetSuchThat(xs, cnd(self, 6)?, Vec::new())
            }
            "foreach-such-that" => {
                let t = match &it[2] {
                    Item::N(t, _) => self.tn(t, String::new())?,
                    Item::P(i, j, _) => TyExpr::Prose(self.prose(*i, *j)),
                    _ => unreachable!(),
                };
                let x = self.bind(c(3).unwrap())?;
                let k = cnd(self, 6)?;
                let body = self.steps(kids);
                self.closed_such(&k, &body)?;
                Stmt::ForSuchThat(x, t, k, None, Body::Block(body))
            }
            "foreach-int" => {
                let x = self.bind(c(3).unwrap())?;
                let k = cnd(self, 6)?;
                let Item::A(order, _, _) = it[9] else { unreachable!() };
                let range = match &k {
                    Cond::Phrase(p, h) if self.d.phrases[*p].name == "rel3" => match h.as_slice() {
                        [Hole::E(lo), Hole::W(a), Hole::E(Expr::Var(m)), Hole::W(b), Hole::E(hi)] if *m == x => {
                            Some((lo.clone(), *a == 1, hi.clone(), *b == 1))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let body = Body::Block(self.steps(kids));
                match range {
                    Some((lo, li, hi, hii)) => Stmt::ForRange(x, lo, li, hi, hii, order == 1, body),
                    None => {
                        let int = TyExpr::Sort(String::new(), vec![], self.d.sorts.intern("integer"), String::new());
                        Stmt::ForSuchThat(x, int, k, Some(order), body)
                    }
                }
            }
            "foreach-own-key" => {
                let x = self.bind(c(5).unwrap())?;
                let o = e(self, 7)?;
                let k = cnd(self, 10)?;
                let Item::A(order, _, _) = it[13] else { unreachable!() };
                Stmt::ForKeys(x, o, k, order, Body::Block(self.steps(kids)))
            }
            "foreach-index" => {
                let x = self.bind(c(3).unwrap())?;
                let l = e(self, 5)?;
                Stmt::ForIndex(x, l, Body::Block(self.steps(kids)))
            }
            "foreach-child" => {
                let x = self.bind(c(4).unwrap())?;
                Stmt::ForChildren(x, Body::Block(self.steps(kids)))
            }
            "foreach-child-of" => {
                let x = self.bind(c(4).unwrap())?;
                let e = e(self, 6)?;
                Stmt::ForChildrenOf(x, e, Body::Block(self.steps(kids)))
            }
            "repeat-times" => {
                let n = e(self, 1)?;
                Stmt::RepeatN(n, self.steps(kids))
            }
            "let-table" => {
                no_kids(self)?;
                let x = self.bind(c(1).unwrap())?;
                let Item::A(k, _, _) = it[4] else { return Err("let-table without its choice".into()) };
                let holes = vec![Hole::W(k), Hole::E(e(self, 7)?)];
                let p = self.parser_form_id("P", "assoc-table", &holes)?;
                // the second-column entry of the key's row; the table's hole comes with the step's continuation lines
                if self.d.phrases[p].meaning.is_none() {
                    let prim = self.d.prims.get("TableAssociated").ok_or("TableAssociated not seeded")?;
                    let args = vec![crate::decls::PArg::Hole(2), crate::decls::PArg::Hole(1)];
                    self.d.phrases[p].meaning = Some(crate::decls::Meaning::Prim { prim, args, neg: false });
                }
                Stmt::Let(x, Expr::Phrase(p, holes))
            }
            "let-see" => {
                no_kids(self)?;
                let x = self.bind(c(1).unwrap())?;
                let Item::T(i, _) = it[6] else { unreachable!() };
                let holes = vec![Hole::E(e(self, 3)?), Hole::E(self.tok_expr(i)?)];
                let v = self.parser_form("P", "see-xref", holes)?;
                Stmt::Let(x, v)
            }
            "return-see" => {
                no_kids(self)?;
                let x = e(self, 1)?;
                let Item::T(i, _) = it[4] else { unreachable!() };
                Stmt::RetSee(x, self.tok_expr(i)?)
            }
            "let-colon" | "return-colon" | "set-colon" => {
                no_kids(self)?;
                let r = self.g.rules.iter().find(|r| r.cat == "P" && r.name == "strcat-colon").unwrap();
                let els = r.elems.clone();
                let p = self.d.phrase("P", "strcat-colon", || pieces(&els));
                if self.d.phrases[p].meaning.is_none() {
                    let prim = self.d.prims.get("string-concatenation").ok_or("string-concatenation not seeded")?;
                    self.d.phrases[p].meaning = Some(crate::decls::Meaning::Prim { prim, args: vec![crate::decls::PArg::Spread(0)], neg: false });
                }
                let v = Expr::Phrase(p, vec![]);
                match n.name {
                    "let-colon" => Stmt::Let(self.bind(c(1).unwrap())?, v),
                    "return-colon" => Stmt::Ret(Some(v)),
                    _ => {
                        let place = match e(self, 1)? {
                            Expr::Var(x) => Place::Var(x),
                            Expr::Field(b, f) => Place::Field(*b, f),
                            x => Place::Expr(x),
                        };
                        Stmt::Set(place, v)
                    }
                }
            }
            "suspend" | "suspend-remove" | "push-ctx" | "remove-ctx-restore-top" | "remove-ctx" | "remove-ctx-restore" | "resume-top"
            | "resume-passing" | "set-eval-state" | "resume-let" => {
                no_kids(self)?;
                let mut es = Vec::new();
                for it in it.iter() {
                    if let Item::N(x, _) = it {
                        if x.name != "var" || x.rid != crate::engine::Rid::R(self.g.rules.iter().position(|r| r.cat == "V").unwrap()) {
                            es.push(self.expr(x)?);
                        }
                    }
                }
                let mut es = es.into_iter();
                let mut e = || es.next().ok_or_else(|| "a context step with too few expressions".to_string());
                match n.name {
                    "suspend" => Stmt::Suspend(e()?, 0),
                    "suspend-remove" => Stmt::Suspend(e()?, 1),
                    "push-ctx" => {
                        let (a, b) = (e()?, e()?);
                        if a != b {
                            return Err("a Push step naming two contexts".into());
                        }
                        Stmt::Push(a, 0)
                    }
                    "remove-ctx-restore-top" => Stmt::Remove(e()?, 0),
                    "remove-ctx" => Stmt::Remove(e()?, 1),
                    "remove-ctx-restore" => Stmt::RemoveRestore(e()?, e()?),
                    "resume-top" => Stmt::ResumeTop,
                    "resume-passing" => Stmt::Resume(e()?, e()?),
                    "set-eval-state" => Stmt::SetCodeState(e()?, e()?),
                    _ => {
                        let Item::T(i, _) = it[0] else { unreachable!() };
                        let raw = self.tok(i).raw.clone();
                        let attrs = parse_attrs(&raw["<emu-meta".len()..raw.len() - 1])?;
                        let x = self.bind(c(21).unwrap())?;
                        Stmt::ResumeLet(e()?, e()?, x, attrs)
                    }
                }
            }
            name if CLOSURE_STEPS.contains(&name) && !kids.is_empty() => {
                let (p, mut h) = self.phrase(n)?;
                h.push(Hole::E(self.steps_closure(kids)));
                Stmt::Phrase(p, h)
            }
            name => {
                let (p, h) = self.phrase(n)?;
                let nested = self.steps(kids);
                let st = match name {
                    "append" | "remove" | "remove-first" | "remove-last" | "insert-first" | "prepend" | "add" | "reverse" | "replace-elem"
                    | "store-bytes" | "remove-these" | "replace-in" | "append-fields" => Stmt::Mutate(p, h),
                    _ => Stmt::Phrase(p, h),
                };
                match ITERATING_STEPS.iter().find(|s| s.0 == name) {
                    Some(&(_, k)) if !kids.is_empty() => {
                        let Stmt::Phrase(p, h) = st else { return Err(format!("{name}: an iterating step as a mutation")) };
                        let x = match h.get(k) {
                            Some(Hole::B(x) | Hole::E(Expr::Var(x))) => *x,
                            h => return Err(format!("{name}: iterated hole {k} is {h:?}")),
                        };
                        Stmt::ForEach(x, None, Expr::Phrase(p, h), false, Body::Block(nested))
                    }
                    _ if kids.is_empty() => st,
                    _ => Stmt::WithSteps(Box::new(st), nested),
                }
            }
        };
        Ok(st)
    }
}

/// `Name[params]_opt` split into the name and the suffix as written.
pub fn split_nt(v: &str) -> (&str, &str) {
    let end = v.find(|c: char| c == '[').unwrap_or(v.len());
    let end = if v[..end].ends_with("_opt") { end - 4 } else { end };
    (&v[..end], &v[end..])
}

/// Attributes `k="v"` / `k`, space-separated, as in a tag.
pub fn parse_attrs(s: &str) -> Res<Vec<Attr>> {
    let mut out = Vec::new();
    let mut rest = s;
    loop {
        rest = rest.strip_prefix(' ').ok_or_else(|| format!("attributes {s:?}"))?;
        let k_end = rest.find(|c: char| c == '=' || c == ' ').unwrap_or(rest.len());
        let key = rest[..k_end].to_string();
        rest = &rest[k_end..];
        let value = if let Some(r) = rest.strip_prefix("=\"") {
            let e = r.find('"').ok_or("unterminated attribute")?;
            let v = r[..e].to_string();
            rest = &r[e + 1..];
            Some(v)
        } else {
            None
        };
        out.push(Attr { key, value });
        if rest.is_empty() {
            return Ok(out);
        }
    }
}

/// Step attributes `id="x", normative-optional`.
pub fn parse_step_attrs(s: &str) -> Res<Vec<Attr>> {
    let mut out = Vec::new();
    for part in s.split(", ") {
        match part.split_once('=') {
            Some((k, v)) if v.len() >= 2 && v.starts_with('"') && v.ends_with('"') => {
                out.push(Attr { key: k.to_string(), value: Some(v[1..v.len() - 1].to_string()) })
            }
            None if !part.is_empty() && !part.contains(' ') => out.push(Attr { key: part.to_string(), value: None }),
            _ => return Err(format!("step attributes {s:?}")),
        }
    }
    Ok(out)
}

/// Connectives between conditions, as the parser left-associates them: bare
/// commas collect a list that a `, and` / `, or` closes; a plain `and` / `or`
/// joins two (and extends a plain group of the same conjunction).
fn build_conn(cs: Vec<Cond>, conns: &[Vec<String>]) -> Res<Cond> {
    // one `, and` / `, or` among plain connectives and no bare commas: the comma is the main break
    // (`a and b, or c and d` is `(a and b) or (c and d)`)
    let commas: Vec<usize> = (0..conns.len()).filter(|&k| conns[k].len() == 2).collect();
    if let [k] = commas[..] {
        if conns.iter().all(|c| c.len() == 2 || (c.len() == 1 && c[0] != ",")) && conns.len() > 1 {
            let mut cs = cs;
            let right = cs.split_off(k + 1);
            let (l, r) = (build_conn(cs, &conns[..k])?, build_conn(right, &conns[k + 1..])?);
            return Ok(match conns[k][1].as_str() {
                "and" => Cond::And(ConnForm::Comma, vec![l, r]),
                _ => Cond::Or(ConnForm::Comma, vec![l, r]),
            });
        }
    }
    let mut it = cs.into_iter();
    let mut left = it.next().unwrap();
    let mut pending: Vec<Cond> = Vec::new();
    for conn in conns {
        let next = it.next().unwrap();
        let Some(w) = conn.iter().find(|w| *w == "and" || *w == "or") else {
            pending.push(next);
            continue;
        };
        let conj = if w == "and" { Conj::And } else { Conj::Or };
        let form = if conn.len() == 2 { ConnForm::Comma } else { ConnForm::Plain };
        if form == ConnForm::Plain && !pending.is_empty() {
            return Err("a comma list closed without a comma".into());
        }
        let mut items = match (form, left) {
            (ConnForm::Plain, Cond::And(ConnForm::Plain, xs)) if conj == Conj::And => xs,
            (ConnForm::Plain, Cond::Or(ConnForm::Plain, xs)) if conj == Conj::Or => xs,
            (_, l) => vec![l],
        };
        items.append(&mut pending);
        items.push(next);
        left = match conj {
            Conj::And => Cond::And(form, items),
            Conj::Or => Cond::Or(form, items),
        };
    }
    if !pending.is_empty() {
        return Err("a condition list with no conjunction".into());
    }
    Ok(left)
}

impl<'a, 'b> Conv<'a, 'b> {
    /// Sibling steps: each converted, an `Else if` / `Else` step joined to
    /// the `If` before it; a step with no data shape stays prose and is listed.
    pub fn steps(&mut self, ss: &[Step]) -> Vec<Node> {
        let mut out: Vec<Node> = Vec::new();
        for s in ss {
            let saved = (std::mem::take(&mut self.toks), std::mem::take(&mut self.text), self.channel);
            self.channel = self.claim(&s.text);
            if let Err(e) = self.step(s, &mut out) {
                self.exceptions.push((s.text.clone(), e));
                let mut n = self.prose_step(s);
                self.label(s, &mut n.stmt);
                out.push(n);
            }
            (self.toks, self.text, self.channel) = saved;
        }
        out
    }

    /// The channel of a prose fragment at `pos`: the step's, its primitive kept only where
    /// the fragment's holes are the primitive's arguments.
    fn wire(&mut self, parts: &[Part], nested: bool, pos: crate::residue::Pos) -> Channel {
        let p = match self.channel {
            Channel::Prim(p, _) | Channel::Upstream(_, Some(p)) | Channel::Annotated(_, Some(p)) => p,
            c => return c,
        };
        let why = crate::residue::unwired(self.d.prims.name(p), parts, nested, pos);
        let w = why.is_none();
        self.d.wiring.push((p, self.text.clone(), why));
        match self.channel {
            Channel::Prim(p, _) => Channel::Prim(p, w),
            Channel::Upstream(r, _) => Channel::Upstream(r, w.then_some(p)),
            Channel::Annotated(k, _) => Channel::Annotated(k, w.then_some(p)),
            c => c,
        }
    }

    fn pexpr(&mut self, parts: Vec<Part>) -> Expr {
        if let [Part::Text(t)] = &parts[..] {
            if t == ARGUMENTS && matches!(self.channel, Channel::Prim(p, _) if self.d.prims.name(p) == "PassedArguments") {
                match self.frame() {
                    Ok(Some((_, _, a))) => {
                        self.d.framed.push((self.clause.clone(), self.text.clone()));
                        return Expr::Var(a);
                    }
                    Ok(None) => {}
                    Err(e) => self.exceptions.push((self.text.clone(), e)),
                }
            }
        }
        Expr::Prose(self.wire(&parts, false, crate::residue::Pos::Expr), parts)
    }

    fn pcond(&mut self, parts: Vec<Part>) -> Cond {
        Cond::Prose(self.wire(&parts, false, crate::residue::Pos::Cond), parts)
    }

    /// The residue channel the classifier claims for a step's prose.
    fn claim(&mut self, text: &str) -> Channel {
        let c = crate::residue::kind(text);
        match c.channel {
            crate::residue::Channel::Upstream => Channel::Upstream(self.d.reasons.intern(c.reason.unwrap_or(c.kind)), c.prim.map(|p| self.d.prims.intern(p.name))),
            crate::residue::Channel::Prim => match c.prim {
                Some(p) => Channel::Prim(self.d.prims.intern(p.name), false),
                None => Channel::Annotated(self.d.notes.intern(c.kind), None),
            },
            crate::residue::Channel::Annotated => Channel::Annotated(self.d.notes.intern(c.kind), c.prim.map(|p| self.d.prims.intern(p.name))),
        }
    }

    /// A step's continuation lines, indented from its marker's column.
    fn rel_cont(&self, s: &Step) -> Res<String> {
        let ind = self.base + 2 * s.depth;
        let pre = " ".repeat(ind);
        s.cont
            .iter()
            .map(|l| l.strip_prefix(&pre).map(str::to_string).ok_or_else(|| "a continuation line left of its step".to_string()))
            .collect::<Res<Vec<_>>>()
            .map(|v| v.join("\n"))
    }

    /// A step kept whole as prose (with its continuation lines and kids).
    fn prose_step(&mut self, s: &Step) -> Node {
        self.toks = crate::token::tokenize(&s.text);
        self.text = s.text.clone();
        let mut parts = self.prose(0, self.toks.len());
        if !s.cont.is_empty() {
            parts.push(Part::Hole(Hole::Text(self.rel_cont(s).expect("continuation lines left of their step"))));
        }
        let nested = if s.kids.is_empty() { None } else { Some(self.steps(&s.kids)) };
        let attrs = s.attrs.as_deref().map(parse_step_attrs).transpose().ok().flatten().unwrap_or_default();
        let ch = self.wire(&parts, nested.is_some(), crate::residue::Pos::Stmt);
        let stmt = Stmt::Prose(ch, parts);
        Node { attrs, stmt: match nested {
            Some(ns) => Stmt::WithSteps(Box::new(stmt), ns),
            None => stmt,
        } }
    }

    fn step(&mut self, s: &Step, out: &mut Vec<Node>) -> Res<()> {
        let row: &Row = self.rows.get(&(s as *const Step)).ok_or("a step that was not parsed")?;
        let attrs = match &s.attrs {
            Some(a) => parse_step_attrs(a)?,
            None => vec![],
        };
        self.toks = row.toks.clone();
        self.text = s.text.clone();
        let Some(tree) = row.tree.clone() else {
            let mut n = self.prose_step(s);
            n.attrs = attrs;
            self.label(s, &mut n.stmt);
            n.stmt = self.with_readings(s, n.stmt);
            out.push(n);
            return Ok(());
        };
        let it = &tree.items;
        // a prose condition may carry an objective ("k is as small as possible"): the step stays prose
        if tree.name == "let-such-that-any" && matches!(it[6], Item::P(..)) {
            let mut n = self.prose_step(s);
            n.attrs = attrs;
            self.label(s, &mut n.stmt);
            n.stmt = self.with_readings(s, n.stmt);
            out.push(n);
            return Ok(());
        }
        let slot_cond = |cv: &mut Self, k: usize| -> Res<Cond> {
            match &it[k] {
                Item::N(x, _) => cv.cond(x),
                Item::P(i, j, _) => {
                    let p = cv.prose(*i, *j);
                    Ok(cv.pcond(p))
                }
                _ => Err("condition slot".into()),
            }
        };
        let arm = match tree.name {
            "elseif-starts" => {
                let subj = match &it[2] {
                    Item::N(x, _) => self.expr(x)?,
                    Item::P(i, j, _) => { let p = self.prose(*i, *j); self.pexpr(p) },
                    _ => unreachable!(),
                };
                let arg = match &it[5] {
                    Item::N(x, _) => self.expr(x)?,
                    Item::P(i, j, _) => { let p = self.prose(*i, *j); self.pexpr(p) },
                    _ => unreachable!(),
                };
                let r = self.g.rules.iter().find(|r| r.cat == "PRED" && r.name == "starts-with").unwrap();
                let els = r.elems.clone();
                let p = self.d.phrase("PRED", "starts-with", || pieces(&els));
                let c = Cond::Preds(subj, Pred::Phrase(p, vec![Hole::E(arg)]), vec![]);
                Some(Arm { attrs: attrs.clone(), cond: Some(c), body: Body::Block(self.steps(&s.kids)) })
            }
            "elseif-then" => {
                let c = slot_cond(self, 2)?;
                let body = self.steps(&s.kids);
                Some(Arm { attrs: attrs.clone(), cond: Some(self.bind_such(c, &body)?), body: Body::Block(body) })
            }
            "elseif-inline" => {
                let c = slot_cond(self, 2)?;
                let body = Box::new(self.stmt(child(&it[4]).unwrap(), &[])?);
                Some(Arm { attrs: attrs.clone(), cond: Some(self.bind_such(c, &body)?), body: Body::Inline(body) })
            }
            "else" => Some(Arm { attrs: attrs.clone(), cond: None, body: Body::Block(self.steps(&s.kids)) }),
            "else-inline" => Some(Arm { attrs: attrs.clone(), cond: None, body: Body::Inline(Box::new(self.stmt(child(&it[2]).unwrap(), &[])?)) }),
            _ => None,
        };
        if let Some(mut a) = arm {
            if let Some(x) = self.stops {
                x.label_arm(s, &self.clause, &mut a);
            }
            // a covered Else joins its If under the reading that replaces both
            let covered = match self.anchors.get(&(s as *const Step)).map(Vec::as_slice) {
                Some([(e, k, _)]) if *k == crate::data::COVERED => Some(*e),
                Some(_) => return Err("an erratum anchored on an Else step".into()),
                None => None,
            };
            if matches!(a.body, Body::Inline(_)) && !s.kids.is_empty() {
                return Err("nested steps under an inline Else".into());
            }
            if !s.cont.is_empty() {
                return Err("continuation lines under an Else".into());
            }
            let last = match out.last_mut() {
                Some(Node { stmt: Stmt::Readings(e, lit, _), .. }) if covered == Some(*e) => Some(&mut **lit),
                Some(_) if covered.is_some() => return Err("a covered Else step without its reading".into()),
                Some(n) => Some(&mut n.stmt),
                None => None,
            };
            return match last {
                Some(Stmt::If(_, _, arms, els)) if els.is_none() => {
                    if a.cond.is_some() {
                        arms.push(a);
                    } else {
                        *els = Some(a);
                    }
                    Ok(())
                }
                _ => Err("an Else step without its If".into()),
            };
        }
        let mut st = self.stmt(&tree, &s.kids)?;
        if !s.cont.is_empty() {
            let cont = if row.bullets.is_empty() {
                Hole::Text(self.rel_cont(s)?)
            } else {
                if row.bullets.len() != s.cont.len() {
                    return Err("bullets mixed with other continuation lines".into());
                }
                let mut xs = Vec::new();
                for (b, bt, tr) in &row.bullets {
                    self.toks = bt.clone();
                    self.text = b.clone();
                    xs.push(match tr {
                        Some(t) => self.expr(t)?,
                        None => {
                            let p = self.prose(0, bt.len());
                            self.pexpr(p)
                        }
                    });
                }
                Hole::L(ListForm::Bullets, xs)
            };
            let step = match &mut st {
                Stmt::WithSteps(inner, _) => &mut **inner,
                st => st,
            };
            match step {
                Stmt::Phrase(_, hs) | Stmt::Mutate(_, hs) => hs.push(cont),
                Stmt::Let(_, Expr::Phrase(p, hs)) if self.d.phrases[*p].name == "assoc-table" => {
                    let Hole::Text(t) = &cont else { return Err("a step's table as bullets".into()) };
                    let &i = self.env.figures.get(&crate::text::squash(t)).ok_or("a step's table that is not a figure")?;
                    hs.push(Hole::E(Expr::Table(i, Box::new(Expr::Xref(String::new(), XrefForm::Plain, None)))));
                    hs.push(cont);
                }
                Stmt::Let(_, Expr::Phrase(_, hs)) | Stmt::Ret(Some(Expr::Phrase(_, hs))) | Stmt::Set(_, Expr::Phrase(_, hs)) => hs.push(cont),
                _ => return Err("continuation lines under a core statement".into()),
            }
        } else if matches!(&st, Stmt::Let(_, Expr::Phrase(p, _)) if self.d.phrases[*p].name == "assoc-table") {
            return Err("an associated-with step without its table".into());
        }
        let _ = Class::S;
        self.label(s, &mut st);
        let st = self.with_readings(s, st);
        out.push(Node { attrs, stmt: st });
        Ok(())
    }

    /// A step's own statement with its erratum stop sites labelled (`stops::StopSites`).
    fn label(&self, s: &Step, st: &mut Stmt) {
        if let Some(x) = self.stops {
            x.label(s, &self.clause, st);
        }
    }

    /// An anchored step's statement with its errata readings' steps converted, a later erratum's inside an earlier's.
    fn with_readings(&mut self, s: &Step, mut st: Stmt) -> Stmt {
        let xs = self.anchors.get(&(s as *const Step)).cloned().unwrap_or_default();
        for (e, k, alts) in xs.into_iter().rev() {
            let mut conv: Vec<(Reading, Vec<Node>)> = Vec::new();
            // readings that share one overlay alternative (consecutive, the same steps) share its conversion
            let (mut j, mut last) = (0, None);
            for (rd, steps) in alts.iter() {
                let same = last == Some((steps.as_ptr(), steps.len()));
                let ns = match conv.last() {
                    Some((_, ns)) if same => ns.clone(),
                    _ => {
                        let ns = self.steps(steps);
                        if k != crate::data::COVERED {
                            self.readings.push((e, k, j, ns.clone()));
                        }
                        j += 1;
                        ns
                    }
                };
                last = Some((steps.as_ptr(), steps.len()));
                conv.push((*rd, ns));
            }
            st = Stmt::Readings(e, Box::new(st), conv);
        }
        st
    }
}

impl<'a, 'b> Conv<'a, 'b> {
    /// Header type alternatives: `a or b`, `a, b, or c`, `a, or b`.
    fn ht_union(&mut self, f: AltForm, l: &PNode) -> Res<TyExpr> {
        let ts = l.items.iter().filter_map(child).map(|t| self.ht(t)).collect::<Res<Vec<_>>>()?;
        let comma = l.items.iter().any(|x| matches!(x, Item::L(w, _) if w == ","));
        let form = if comma { ConnForm::Comma } else { ConnForm::Plain };
        if !(ts.len() == 2 || comma) {
            return Err("type alternatives in an irregular form".into());
        }
        Ok(TyExpr::Union(f, form, ts))
    }

    /// A Record type's field list (category HFL): `[[F]] (T) and [[G]] (U)`.
    fn ht_fields(&mut self, l: &PNode) -> Res<TyExpr> {
        let fs = if l.name == "elist1" { vec![child(&l.items[0]).unwrap().clone()] } else { l.items.iter().filter_map(child).cloned().collect() };
        let mut out = Vec::new();
        for f in fs {
            let Item::T(i, _) = f.items[0] else { unreachable!() };
            let fid = self.d.fields.intern(&self.tok(i).v.clone());
            out.push((fid, self.ht(child(&f.items[2]).unwrap())?));
        }
        Ok(TyExpr::Record(out))
    }

    /// A header type phrase's tree (category HT) as a type.
    pub fn ht(&mut self, n: &PNode) -> Res<TyExpr> {
        let it = &n.items;
        let c = |k: usize| child(&it[k]).unwrap();
        Ok(match n.name {
            "ht-one" | "ht-type" => {
                let x = c(0);
                if n.name == "ht-type" {
                    self.ty(x)?
                } else {
                    self.ht(x)?
                }
            }
            "ht-alt" | "ht-either" | "ht-one-of" => {
                let (f, l) = match n.name {
                    "ht-alt" => (AltForm::Or, c(0)),
                    "ht-either" => (AltForm::Either, c(1)),
                    _ => (AltForm::OneOf, c(2)),
                };
                self.ht_union(f, l)?
            }
            "elist" => self.ht_union(AltForm::Or, n)?,
            "ht-list-of" => {
                let a = if matches!(it[0], Item::A(0, _, _)) { "a" } else { "an" };
                TyExpr::ListOf(a.to_string(), Box::new(self.ht(c(3))?))
            }
            "ht-bare" => self.tn(c(0), String::new())?,
            "ht-enum" => {
                let Item::T(i, _) = it[0] else { unreachable!() };
                TyExpr::Value(self.tok_expr(i)?)
            }
            "ht-value" => TyExpr::Value(self.expr(c(0))?),
            "ht-normal" => TyExpr::Completion(Some(Box::new(self.ht(c(4))?))),
            "ht-interval" => {
                let a = if matches!(it[0], Item::A(0, _, _)) { "a" } else { "an" };
                let t = self.tn(c(1), a.to_string())?;
                TyExpr::Interval(Box::new(t), self.expr(c(7))?, self.expr(c(9))?)
            }
            "ht-record" => self.ht_fields(c(4))?,
            "ht-list-of-records" => {
                let a = if matches!(it[0], Item::A(0, _, _)) { "a" } else { "an" };
                TyExpr::ListOf(a.to_string(), Box::new(self.ht_fields(c(6))?))
            }
            _ => {
                let (p, h) = self.phrase(n)?;
                TyExpr::Phrase(p, h)
            }
        })
    }
}

impl<'a, 'b> Conv<'a, 'b> {
    fn slot_expr(&mut self, it: &Item) -> Res<Expr> {
        match it {
            Item::N(x, _) => self.expr(x),
            Item::P(i, j, _) => Ok({ let p = self.prose(*i, *j); self.pexpr(p) }),
            _ => Err("expression slot".into()),
        }
    }

    fn slot_cond(&mut self, it: &Item) -> Res<Cond> {
        match it {
            Item::N(x, _) => self.cond(x),
            Item::P(i, j, _) => Ok({ let p = self.prose(*i, *j); self.pcond(p) }),
            _ => Err("condition slot".into()),
        }
    }

    /// An equation bullet: its SDO, its productions (as written) and its body: a
    /// return; lets (the `where` bindings) then a return; or an If whose inline
    /// return and Else arm are the two cases.
    pub fn equation(&mut self, n: &PNode) -> Res<(Id, Vec<String>, Vec<Node>)> {
        let it = &n.items;
        let Item::T(i, _) = it[1] else { unreachable!() };
        let name = self.tok(i).v.clone();
        let sdo = self.d.sdos.get(&name).ok_or_else(|| format!("equation SDO {name} undeclared"))?;
        let mut prods = Vec::new();
        let mut g = child(&it[3]).unwrap().clone();
        loop {
            let Item::T(k, _) = g.items[0] else { unreachable!() };
            let raw = self.tok(k).raw.clone();
            let a = raw.find('>').unwrap() + 1;
            let inner = raw[a..raw.len() - "</emu-grammar>".len()].to_string();
            if raw[..a] != *"<emu-grammar>" || crate::text::squash(&inner) != inner {
                return Err(format!("an equation's production not in plain form: {raw}"));
            }
            prods.push(inner);
            match g.items.last() {
                Some(Item::N(x, _)) => g = x.clone(),
                _ => break,
            }
        }
        self.set_rhs(&prods);
        let node = |s: Stmt| Node { attrs: vec![], stmt: s };
        let body = match n.name {
            "eq" => vec![node(Stmt::Ret(Some(self.slot_expr(&it[5])?)))],
            "eq-where" => {
                let e = self.slot_expr(&it[5])?;
                let mut lets = Vec::new();
                let mut w = child(&it[8]).unwrap().clone();
                let mut bare = false;
                loop {
                    let x = self.bind(child(&w.items[0]).unwrap())?;
                    let attrs = if bare { vec![Attr { key: "and-bare".into(), value: None }] } else { vec![] };
                    lets.push(Node { attrs, stmt: Stmt::Let(x, self.slot_expr(&w.items[2])?) });
                    bare = w.name == "wh-and-bare";
                    match w.items.last() {
                        Some(Item::N(nx, _)) if w.name == "wh-and" || bare => w = nx.clone(),
                        _ => break,
                    }
                }
                lets.push(node(Stmt::Ret(Some(e))));
                lets
            }
            "eq-if" => {
                let e1 = self.slot_expr(&it[5])?;
                let c = self.slot_cond(&it[7])?;
                let e2 = self.slot_expr(&it[13])?;
                let els = Arm { attrs: vec![], cond: None, body: Body::Inline(Box::new(Stmt::Ret(Some(e2)))) };
                vec![node(Stmt::If(c, Body::Inline(Box::new(Stmt::Ret(Some(e1)))), vec![], Some(els)))]
            }
            _ => return Err(format!("equation form {}", n.name)),
        };
        Ok((sdo, prods, body))
    }
}
