//! Section 29, the memory model, outside its emu-algs: the clause tree as
//! blocks (paragraphs, list items, field tables, notes), every sentence
//! parsed by the relational templates below (categories `M…` and `DFN`,
//! unreachable from `Step`) into data, and the whole section printed back
//! byte for byte from the data.
//!
//! The relational core: a relation is the least relation closed under rules
//! (`For events _a_ and _b_, _a_ R _b_ in _x_ if C.`), or a host-provided
//! strict partial order, a strict total order or a function satisfying
//! conditions; a predicate holds of an execution if a condition does. A
//! sentence ending in "the following" takes the list, table or algorithm
//! after it. Relation and predicate names are interned in definition order.

use crate::ast::{AltForm, Conj, ConnForm, Expr, Hole, Id, Part, TyExpr};
use crate::conv::{Conv, Res, Vars};
use crate::decls::{Decls, Table};
use crate::engine::{mk, El, Item, Kc, Node as PNode, Parser, Rid};
use crate::grammar::{conn, list_of, Grammar, Out, R};
use crate::print::Printer;
use crate::spec::Spec;
use crate::token::{lit_canon, tokenize, K};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

// ---------------------------------------------------------------- grammar

/// The relational templates: (category, name, template, tier, synonym of).
pub const RULES: &[R] = &[
    // sentences
    ("MMS", "sort-union", "( A | An ) {DFN} is either {MSORTS} [ Record ] .", 1, None),
    ("MMS", "reldef-least", "For a candidate execution {V} , its {DFN} Relation is the least Relation on {TN} that satisfies the following .", 1, None),
    (
        "MMS",
        "reldef-host",
        "For a candidate execution {V} , its {DFN} Relation is a host-provided strict partial order on {TN} that satisfies at least the following .",
        1,
        None,
    ),
    ("MMS", "reldef-total", "For a candidate execution {V} , {DFN} is a strict total order of all {TN} in {E} that satisfies the following .", 1, None),
    (
        "MMS",
        "fndef",
        "For a candidate execution {V} , its {DFN} function is a mathematical function mapping {TN} in {E} to Lists of {TN} in {E} that satisfies the following conditions .",
        1,
        None,
    ),
    ("MMS", "preddef", "( A candidate execution | An execution ) [ {V} ] ( has | is ) {MPN} if {MC} .", 1, None),
    ("MMS", "for", "For {MBS} , {MF} .", 1, None),
    ("MMS", "formula", "{MF} .", 1, None),
    // declared sentences
    ("MMS", "record-sort", "( A | An ) {DFN} [ of the evaluation of an agent cluster ] is a Record with the following fields .", 1, None),
    ("MMS", "empty-record", "( A | An ) {DFN} is a {TN} whose fields are empty Lists .", 1, None),
    (
        "MMS",
        "synchronize-events",
        "Some operations also introduce {DFN} , which have no fields and exist purely to directly constrain the permitted orderings of other events .",
        1,
        None,
    ),
    ("MMS", "introduced", "{TN} are introduced to {TN} by abstract operations or by methods on the Atomics object .", 1, None),
    ("MMS", "host-events", "And finally , there are host-specific events .", 1, None),
    (
        "MMS",
        "range-def",
        "Let the {DFN} of a {TN} {V} be the Set of all integers in the interval from {E} '(' inclusive ')' to {E} '(' exclusive ')' .",
        1,
        None,
    ),
    ("MMS", "range-rel", "Two events ^' memory ranges are ( equal | overlapping | disjoint ) when {MC} .", 1, None),
    ("MMS", "ordered-by", "Events are ordered within candidate executions by the relations defined below .", 1, None),
    (
        "MMS",
        "parameterized",
        "The following relations and mathematical functions are parameterized over a particular candidate execution and order its Memory events .",
        1,
        None,
    ),
    ("MMS", "indexed-in-range", "Each event {V} with index {V} in {E} has {E} in its memory range .", 1, None),
    ("MMS", "admits-function", "A candidate execution always admits a $WORD function .", 1, None),
    ("MMS", "some-valid", "All programs have at least one valid execution .", 1, None),
    ("MMS", "program-drf", "A program is data race free if all its executions are data race free .", 1, None),
    ("MMS", "sc-drf", "The memory model guarantees sequential consistency of all events for data race free programs .", 1, None),
    // formulas
    ("MF", "rule", "{MCA} if {MC}", 1, None),
    ("MF", "holds", "{MC}", 1, None),
    ("MF", "implies", "if {MC} , [ then ] {MC}", 1, None),
    // binders
    ("MBS", "one", "{MB}", 1, None),
    ("MBS", "two", "{MB} and {MB}", 1, None),
    ("MB", "pair", "{MTY} {V} and {V} [ such that {MC} ]", 1, None),
    ("MB", "pair-in", "{MTY} {V} and {V} that are contained in {E}", 1, None),
    ("MB", "each", "each {MTY} {V} in {E}", 1, None),
    ("MB", "elem", "each element {V} of {E}", 1, None),
    ("MB", "one", "( a | an ) {MTY} {V}", 1, None),
    // condition atoms
    ("MCA", "rel", "{E} {MREL} {E} [ in {E} ]", 1, None),
    ("MCA", "exists", "there ( is | exists ) ( some | an | a | no ) {MTY} {V} [ ( in {E} | that has {E} in its memory range ) ] such that {MC}", 1, None),
    ("MCA", "not", "it is not the case that [ both ] {MC}", 1, None),
    ("MCA", "same", "{E} and {E} are [ not ] the same {TN}", 1, None),
    ("MCA", "contains", "{MME} contains {MME}", 1, None),
    ("MCA", "contains2", "{MME} contains [ both ] {MME} and {MME}", 1, None),
    ("MCA", "ranges", "{E} and {E} ( have | do not have ) ( equal | overlapping | disjoint ) memory ranges", 1, None),
    ("MCA", "before", "{E} is before {E} in List order of {E}", 1, None),
    ("MCA", "following", "( any | all ) of the following [ conditions ] are true", 1, None),
    ("MCA", "following-the", "the following is true", 1, None),
    ("MCA", "following-alg", "the following algorithm returns $VAL", 1, None),
    ("MCA", "pred", "{E} ( has | is ) {MPN}", 1, None),
    ("MCA", "pred2", "{E} and {E} are in a {MPN} [ in {E} ]", 1, None),
    ("MCA", "in-range", "{E} has {E} in its memory range", 1, None),
    ("MCA", "is-a", "{E} is [ either ] ( a | an ) {MTY}", 1, None),
    ("MCA", "core", "{CA}", 1, Some("rel")),
    // declared condition atoms
    ("MCA", "not-in", "{E} is not in {E}", 1, None),
    ("MCA", "same-fields", "the events [ do not ] have the same ( {FieldEL} | {FN} )", 1, None),
    ("MCA", "ranges-not-equal", "the ranges are not equal", 1, None),
    ("MCA", "intersection", "their intersection is non-empty", 1, None),
    ("MCA", "neither-range", "their ranges are neither equal nor overlapping", 1, None),
    ("MCA", "no-cycle", "there is no cycle in the union of {MREL} and {MREL} in {E}", 1, None),
    ("MCA", "admits", "( {E} | it ) admits ( a | an ) {MREL} Relation [ that is a strict partial order ]", 1, None),
    ("MCA", "host-provides", "the host provides a {MREL} Relation for {E}", 1, None),
    ("MCA", "list-of-writes", "{MME} is a List of length {E} whose elements are {MTY} {V} such that {MC}", 1, None),
    (
        "MCA",
        "not-infinitely-many",
        "it is not the case that there is an infinite number of {MTY} in {E} with equal memory range that is memory-order before {E}",
        1,
        None,
    ),
    ("MCA", "no-two-in-race", "there are no two events in {E} that are in a data race", 1, None),
    // expressions, names, types
    ("MME", "e", "{E}", 1, Some("in")),
    ("MME", "in", "{P} in {E}", 1, None),
    ("MME", "pair", "'(' {E} , {E} ')'", 1, None),
    ("MREL", "rel", "( is-agent-order-before | reads-from | host-synchronizes-with | synchronizes-with | happens-before | is-memory-order-before )", 1, None),
    (
        "MPN",
        "lex",
        "( valid chosen reads | coherent reads | tear free reads | sequentially consistent atomics | a valid execution '(' or simply an execution ')' )",
        1,
        None,
    ),
    ("MPN", "dfn", "{DFN}", 1, None),
    ("MPN", "xref", "$XREF", 1, None),
    ("MTY", "one", "{TN}", 1, None),
    ("MTY", "or", "{TN} or {TN}", 1, None),
    ("MTY", "execution", "execution", 1, None),
    ("MSORT", "dfn", "[ ( a | an ) ] {DFN}", 1, None),
    ("MSORT", "ty", "[ ( a | an | such a ) ] {TN}", 1, None),
    // a field table's Value cell
    ("MMT", "ht", "{HT}", 1, None),
];

/// A defined term: `<dfn [variants="…"]>words</dfn>` or `<em>words</em>`.
pub fn b_dfn(p: &mut Parser, i: usize) -> Out {
    if i >= p.n || p.t[i].k != K::Tag {
        return vec![];
    }
    let open = p.t[i].v.as_str();
    let close = if open == "<em>" {
        "</em>"
    } else if open == "<dfn>" || open.starts_with("<dfn ") {
        "</dfn>"
    } else {
        return vec![];
    };
    let mut k = i + 1;
    while k < p.n && p.t[k].k == K::Word && k - i <= 6 {
        k += 1;
    }
    if k == i + 1 || k >= p.n || p.t[k].k != K::Tag || p.t[k].v != close {
        return vec![];
    }
    let mut items = vec![Item::T(i, false)];
    items.extend((i + 1..k).map(|w| Item::T(w, w == i + 1)));
    items.push(Item::T(k, true));
    vec![(k + 1, mk(Rid::B("dfn"), "dfn", items, i, k + 1))]
}

/// Relational conditions joined by connectives, by maximal munch.
pub fn b_mc(p: &mut Parser, i: usize) -> Out {
    let munch = p.munch;
    conn(p, i, "MCA", munch, true)
}

/// Sorts as alternatives: `a A or a B`, `A, B, or C`.
pub fn b_msorts(p: &mut Parser, i: usize) -> Out {
    list_of(p, i, "MSORT", true, &["or"], false)
}

// ---------------------------------------------------------------- data

/// A defined term as written.
#[derive(Clone, Debug, PartialEq)]
pub enum TermTag {
    /// `<dfn>`, or `<dfn variants="…">`
    Dfn(Option<String>),
    Em,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Term {
    pub tag: TermTag,
    pub words: String,
}

/// A predicate's name: a lexicon entry (`names`), an entry's defining occurrence as a term, or a cross-reference.
#[derive(Clone, Debug, PartialEq)]
pub enum PName {
    Lex(Id),
    Term(Id, TermTag),
    Xref(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum MExpr {
    E(Expr),
    /// `f(a) in _x_`: a function of an execution
    In(Expr, Expr),
    /// `(a, b)`
    Pair(Expr, Expr),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Quant {
    Some,
    An,
    A,
    No,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RangeRel {
    Equal,
    Overlapping,
    Disjoint,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Verb {
    Has,
    Is,
    /// `_a_ and _b_ are in a …`
    AreIn,
}

/// The list after the sentence, as a condition: its items' disjunction or
/// conjunction (with "conditions" written), or its sole item.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Following {
    Any(bool),
    All(bool),
    The,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    /// `a R b [in x]`
    Rel(Id, Expr, Expr, Option<Expr>),
    /// `there (is | exists) (some | an | a | no) T x [in S | that has b in its memory range] such that C`
    Exists(bool, Quant, TyExpr, Id, Option<Dom>, Box<MCond>),
    /// `it is not the case that [both] C`
    Not(bool, Box<MCond>),
    /// `a and b are [not] the same T`
    Same(bool, Expr, Expr, TyExpr),
    /// `S contains [both] a [and b]`
    Contains(MExpr, bool, Vec<MExpr>),
    /// `a and b [do not] have equal memory ranges`
    Ranges(bool, RangeRel, Expr, Expr),
    /// `a is before b in List order of L`
    Before(Expr, Expr, Expr),
    Following(Following),
    /// `the following algorithm returns v`
    FollowingAlg(Expr),
    /// `x has P`, `x is P`, `a and b are in a P [in x]`
    Pred(Vec<Expr>, Verb, PName, Option<Expr>),
    /// `e has b in its memory range`
    InRange(Expr, Expr),
    /// `there is no cycle in the union of R and S in x`
    NoCycle(Vec<Id>, Expr),
    /// `(x | it) admits (a | an) R Relation [that is a strict partial order]`
    Admits(Option<Expr>, String, Id, bool),
    /// `e is [either] a T`
    IsA(Expr, bool, String, TyExpr),
    /// a condition of the step grammar
    Core(crate::ast::Cond),
    Phrase(Id, Vec<MHole>),
}

/// An existential's restriction.
#[derive(Clone, Debug, PartialEq)]
pub enum Dom {
    /// `in S`
    In(Expr),
    /// `that has b in its memory range`
    HasInRange(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum MCond {
    Atom(Box<Atom>),
    And(ConnForm, Vec<MCond>),
    Or(ConnForm, Vec<MCond>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Binder {
    /// `events _a_ and _b_ [such that C]`
    Pair(TyExpr, Id, Id, Option<MCond>),
    /// `events _a_ and _b_ that are contained in S`
    PairIn(TyExpr, Id, Id, Expr),
    /// `each T _x_ in S`
    Each(TyExpr, Id, Expr),
    /// `each element _x_ of L`
    Elem(Id, Expr),
    /// `an T _x_`
    One(String, TyExpr, Id),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Formula {
    /// `head if body`
    Rule(Atom, MCond),
    Holds(MCond),
    /// `if C, [then] D`
    Implies(bool, MCond, MCond),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RelKind {
    /// the least Relation on T closed under the rules after it
    Least(TyExpr),
    /// a host-provided strict partial order on T satisfying at least the list after it
    Host(TyExpr),
    /// a strict total order of all T in S satisfying the list after it
    Total(TyExpr, Expr),
    /// a function from T in S to Lists of U in S' satisfying the list after it
    Function(TyExpr, Expr, TyExpr, Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum SortRef {
    Term(Term),
    Ty(TyExpr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Sent {
    /// `A T is either a U, V, or W [Record].`: article, term, (article, sort) alternatives
    SortUnion(String, Term, Vec<(String, SortRef)>, bool),
    /// `For a candidate execution _x_, its R Relation is ….`: a relation or a function of the execution (`rels`), its term's tag
    RelDef(Id, Id, TermTag, RelKind),
    /// `A candidate execution [_x_] has P if C.`, or (`true`) of `An execution`: a valid one
    PredDef(bool, Option<Id>, Verb, PName, MCond),
    /// `Two events' memory ranges are R when C.`
    RangeDef(RangeRel, MCond),
    /// `For B [and B], F.`
    For(Vec<Binder>, Formula),
    /// `F.`
    Formula(Formula),
    Phrase(Id, Vec<MHole>),
    Prose(Vec<Part>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum MHole {
    H(Hole),
    Term(Term),
    Rel(Id),
    Name(PName),
    C(MCond),
    E(MExpr),
    T(TyExpr),
    W(usize),
}

/// A template piece of a phrase row; a hole names its category.
#[derive(Clone, Debug, PartialEq)]
pub enum MPiece {
    Word(String),
    Glue,
    Hole(&'static str),
    Choice(Vec<Vec<MPiece>>),
}

pub struct MPhrase {
    pub cat: &'static str,
    pub name: &'static str,
    pub template: Vec<MPiece>,
}

/// The memory model's own tables: relation names, predicate names, phrase rows.
#[derive(Default)]
pub struct MDecls {
    pub rels: Table,
    pub names: Table,
    pub phrases: Vec<MPhrase>,
    ix: HashMap<(&'static str, &'static str), Id>,
}

impl MDecls {
    fn phrase(&mut self, cat: &'static str, name: &'static str, els: &[(El, bool)]) -> Id {
        if let Some(&i) = self.ix.get(&(cat, name)) {
            return i;
        }
        self.phrases.push(MPhrase { cat, name, template: pieces(els) });
        self.ix.insert((cat, name), self.phrases.len() - 1);
        self.phrases.len() - 1
    }
}

fn pieces(els: &[(El, bool)]) -> Vec<MPiece> {
    let mut out = Vec::new();
    for (el, glue) in els {
        if *glue {
            out.push(MPiece::Glue);
        }
        out.push(match el {
            El::Lit(l) => MPiece::Word(lit_canon(l).to_string()),
            El::Kind(_) | El::KindV(..) => MPiece::Hole("TOK"),
            El::Hole(c) => MPiece::Hole(c),
            El::Opt(inner) => MPiece::Choice(vec![pieces(inner), vec![]]),
            El::Alt(alts) => MPiece::Choice(alts.iter().map(|a| pieces(a)).collect()),
        });
    }
    out
}

#[derive(Clone, Debug)]
pub struct FieldRow {
    pub field: Id,
    pub ty: TyExpr,
    /// the Meaning cell, a description
    pub desc: String,
}

#[derive(Clone, Debug)]
pub struct FieldTable {
    pub id: String,
    pub caption: String,
    pub heads: Vec<String>,
    pub rows: Vec<FieldRow>,
}

/// A list item: one line (`<li>…</li>`), or blocks on the lines between its tags.
#[derive(Clone, Debug)]
pub struct Li {
    pub inline: Option<Vec<Sent>>,
    pub kids: Vec<Block>,
}

#[derive(Clone, Debug)]
pub enum Block {
    /// `<emu-clause{attrs}>`, its variables, its blocks
    Clause { indent: usize, attrs: String, vars: Vec<String>, kids: Vec<Block> },
    Para { indent: usize, sents: Vec<Sent> },
    /// a list item's text on a line of its own
    Text { indent: usize, sents: Vec<Sent> },
    List { indent: usize, items: Vec<Li> },
    Table { indent: usize, table: FieldTable },
    /// a note, its lines verbatim
    Note { indent: usize, lines: Vec<String> },
    /// an emu-alg, by its index in `Spec::algs`
    Alg { indent: usize, alg: usize },
    /// an operation's `<h1>` over several lines, verbatim (its header is the step grammar's)
    Heading(Vec<String>),
    /// a line kept verbatim (a heading, an operation's `dl`)
    Raw(String),
    Blank,
}

/// The section as data.
pub struct Doc {
    pub d: Decls,
    pub md: MDecls,
    pub blocks: Vec<Block>,
    /// the section's text in spec.html
    pub src: String,
    /// sentences that parsed but are kept as prose: text, reason
    pub exceptions: Vec<(String, String)>,
    /// parsed sentences with a tie left on declaration order
    pub ties: Vec<String>,
    /// sentences tied with maximal munch off: resolved by it, still tied
    pub sites: (usize, usize),
}

// ---------------------------------------------------------------- scanning and conversion

enum Fl<'n> {
    N(&'n Rc<PNode>),
    W(usize),
    T(usize),
}

fn flat_items<'n>(els: &[(El, bool)], items: &'n [Item], out: &mut Vec<Fl<'n>>) {
    for ((el, _), it) in els.iter().zip(items) {
        match (el, it) {
            (El::Kind(_), Item::T(i, _)) => out.push(Fl::T(*i)),
            (El::Hole(_), Item::N(n, _)) => out.push(Fl::N(n)),
            (El::Opt(inner), Item::O(v, _)) => match v {
                Some(v) => {
                    out.push(Fl::W(0));
                    flat_items(inner, v, out);
                }
                None => out.push(Fl::W(1)),
            },
            (El::Alt(alts), Item::A(k, v, _)) => {
                out.push(Fl::W(*k));
                flat_items(&alts[*k], v, out);
            }
            _ => {}
        }
    }
}

struct Src<'s> {
    lines: Vec<&'s str>,
    offs: Vec<usize>,
    i: usize,
}

struct B<'c, 'g> {
    cv: Conv<'c, 'c>,
    p: Parser<'g>,
    /// maximal munch off, to count the attachment sites it resolves
    off: Parser<'g>,
    sites: (usize, usize),
    md: MDecls,
    algs: HashMap<usize, usize>,
    sp: &'c Spec,
    exceptions: Vec<(String, String)>,
    ties: Vec<String>,
}

fn indent_of(l: &str) -> usize {
    l.len() - l.trim_start_matches(' ').len()
}

fn cap_first(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) => c.to_uppercase().chain(cs).collect(),
        None => String::new(),
    }
}

impl<'c, 'g> B<'c, 'g> {
    fn blocks(&mut self, s: &mut Src, stop: Option<&str>) -> Res<Vec<Block>> {
        let mut out = Vec::new();
        while s.i < s.lines.len() {
            let line = s.lines[s.i];
            if Some(line) == stop {
                s.i += 1;
                return Ok(out);
            }
            out.push(self.block(s)?);
        }
        match stop {
            Some(x) => Err(format!("missing {x:?}")),
            None => Ok(out),
        }
    }

    /// The lines from the current one to the one equal to `close`, both included.
    fn until(s: &mut Src, close: &str) -> Res<Vec<String>> {
        let a = s.i;
        while s.i < s.lines.len() && s.lines[s.i] != close {
            s.i += 1;
        }
        if s.i == s.lines.len() {
            return Err(format!("missing {close:?}"));
        }
        s.i += 1;
        Ok(s.lines[a..s.i].iter().map(|l| l.to_string()).collect())
    }

    fn block(&mut self, s: &mut Src) -> Res<Block> {
        let line = s.lines[s.i];
        if line.is_empty() {
            s.i += 1;
            return Ok(Block::Blank);
        }
        let ind = indent_of(line);
        let pad = " ".repeat(ind);
        let t = &line[ind..];
        if let Some(a) = t.strip_prefix("<emu-clause").and_then(|r| r.strip_suffix('>')) {
            s.i += 1;
            let saved = std::mem::take(&mut self.cv.vars);
            let kids = self.blocks(s, Some(&format!("{pad}</emu-clause>")));
            let vars = std::mem::replace(&mut self.cv.vars, saved);
            return Ok(Block::Clause { indent: ind, attrs: a.to_string(), vars: vars.names, kids: kids? });
        }
        if let Some(x) = t.strip_prefix("<p>").and_then(|r| r.strip_suffix("</p>")) {
            s.i += 1;
            return Ok(Block::Para { indent: ind, sents: self.sentences(x) });
        }
        if t == "<ul>" {
            s.i += 1;
            let close = format!("{pad}</ul>");
            let mut items = Vec::new();
            while s.i < s.lines.len() && s.lines[s.i] != close {
                let l = s.lines[s.i];
                let li = l.strip_prefix(&format!("{pad}  ")).ok_or_else(|| format!("a list line {l:?}"))?;
                if let Some(x) = li.strip_prefix("<li>").and_then(|r| r.strip_suffix("</li>")) {
                    s.i += 1;
                    items.push(Li { inline: Some(self.sentences(x)), kids: vec![] });
                } else if li == "<li>" {
                    s.i += 1;
                    let kids = self.blocks(s, Some(&format!("{pad}  </li>")))?;
                    items.push(Li { inline: None, kids });
                } else {
                    return Err(format!("a list line {l:?}"));
                }
            }
            s.i += 1;
            return Ok(Block::List { indent: ind, items });
        }
        if t.starts_with("<emu-table ") {
            let a = s.i;
            let lines = Self::until(s, &format!("{pad}</emu-table>"))?;
            match self.table(ind, &lines) {
                Ok(table) => return Ok(Block::Table { indent: ind, table }),
                Err(e) => {
                    self.exceptions.push((lines[0].clone(), e));
                    s.i = a + 1;
                    return Ok(Block::Raw(line.to_string()));
                }
            }
        }
        if t == "<h1>" {
            let lines = Self::until(s, &format!("{pad}</h1>"))?;
            return Ok(Block::Heading(lines));
        }
        if t == "<emu-note>" {
            let lines = Self::until(s, &format!("{pad}</emu-note>"))?;
            return Ok(Block::Note { indent: ind, lines: lines[1..lines.len() - 1].to_vec() });
        }
        if t == "<emu-alg>" {
            let pos = s.offs[s.i] + ind;
            let lines = Self::until(s, &format!("{pad}</emu-alg>"))?;
            let alg = *self.algs.get(&pos).ok_or("an emu-alg the scanner did not see")?;
            let raw = format!("\n{}\n{pad}", lines[1..lines.len() - 1].join("\n"));
            if self.sp.algs[alg].raw != raw {
                return Err(format!("emu-alg at {pos} differs from the scanner's"));
            }
            return Ok(Block::Alg { indent: ind, alg });
        }
        s.i += 1;
        if !t.starts_with('<') {
            return Ok(Block::Text { indent: ind, sents: self.sentences(t) });
        }
        Ok(Block::Raw(line.to_string()))
    }

    fn table(&mut self, ind: usize, lines: &[String]) -> Res<FieldTable> {
        let head = &lines[0][ind..];
        let id = crate::spec::attr(head, "id").ok_or("a table without an id")?;
        let caption = crate::spec::attr(head, "caption").ok_or("a table without a caption")?;
        let cell = |l: &str, tag: &str| l.trim().strip_prefix(&format!("<{tag}>")).and_then(|r| r.strip_suffix(&format!("</{tag}>"))).map(str::to_string);
        let heads: Vec<String> = lines.iter().filter_map(|l| cell(l, "th")).collect();
        let tds: Vec<String> = lines.iter().filter_map(|l| cell(l, "td")).collect();
        if tds.len() % 3 != 0 || heads.len() != 3 {
            return Err("a table not of three columns".into());
        }
        let mut rows = Vec::new();
        for r in tds.chunks(3) {
            let field = r[0].strip_prefix("[[").and_then(|x| x.strip_suffix("]]")).ok_or("a first cell that is not a field name")?;
            let field = self.cv.d.fields.intern(field);
            let ty = self.value_type(&r[1]);
            rows.push(FieldRow { field, ty, desc: r[2].clone() });
        }
        let t = FieldTable { id, caption, heads, rows };
        let printed = print_table(self.cv.d, &self.cv.vars.names, ind, &t);
        if printed != lines.join("\n") {
            return Err("a table not in the canonical layout".into());
        }
        Ok(t)
    }

    /// A Value cell as a type (prose if it does not parse or print back).
    fn value_type(&mut self, text: &str) -> TyExpr {
        let toks = tokenize(text);
        let tree = self.p.parse(&toks, "MMT");
        self.cv.toks = toks;
        self.cv.text = text.to_string();
        let r = match &tree {
            Some(t) if t.name == "ht" => match &t.items[0] {
                Item::N(h, _) => self.cv.ht(h),
                _ => Err("an HT hole".into()),
            },
            Some(t) => self.cv.ty(t),
            None => Err("no type".into()),
        };
        match r {
            Ok(ty) => {
                let mut p = Printer::new(self.cv.d, &[], &[]);
                p.ty(&ty);
                if p.take_text() == text {
                    return ty;
                }
                self.exceptions.push((text.to_string(), "a type that prints otherwise".into()));
            }
            Err(e) if tree.is_some() => self.exceptions.push((text.to_string(), e)),
            Err(_) => {}
        }
        TyExpr::Prose(vec![Part::Text(text.to_string())])
    }

    /// A text's sentences: split after a full stop before a capitalized word.
    fn sentences(&mut self, text: &str) -> Vec<Sent> {
        let toks = tokenize(text);
        let mut segs = Vec::new();
        let mut a = 0;
        for k in 0..toks.len() {
            let stop = toks[k].k == K::Punct && toks[k].v == ".";
            if stop && (k + 1 == toks.len() || (toks[k + 1].k == K::Word && toks[k + 1].v.starts_with(|c: char| c.is_ascii_uppercase()))) {
                segs.push((a, k + 1));
                a = k + 1;
            }
        }
        if a < toks.len() {
            segs.push((a, toks.len()));
        }
        let parts: Vec<&str> = segs.iter().map(|&(a, b)| &text[toks[a].s..toks[b - 1].e]).collect();
        if parts.is_empty() || parts.join(" ") != text {
            return vec![self.prose(text)];
        }
        parts.iter().map(|t| self.sentence(t)).collect()
    }

    fn prose(&mut self, text: &str) -> Sent {
        self.cv.toks = tokenize(text);
        self.cv.text = text.to_string();
        let n = self.cv.toks.len();
        Sent::Prose(self.cv.prose(0, n))
    }

    /// One sentence parsed (a capitalized first word also tried lower-cased), converted and printed back.
    fn sentence(&mut self, text: &str) -> Sent {
        let mut toks = tokenize(text);
        let mut tree = self.p.parse(&toks, "MMS");
        if tree.is_none() && toks[0].k == K::Word && toks[0].v.starts_with(|c: char| c.is_ascii_uppercase()) {
            let mut low = toks.clone();
            let lc = |s: &str| {
                let mut cs = s.chars();
                cs.next().map(|c| c.to_lowercase().chain(cs).collect::<String>()).unwrap_or_default()
            };
            low[0].v = lc(&low[0].v);
            low[0].raw = lc(&low[0].raw);
            tree = self.p.parse(&low, "MMS");
            if tree.is_some() {
                toks = low;
            }
        }
        let Some(tree) = tree else { return self.prose(text) };
        if self.off.parse(&toks, "MMS").is_some_and(|t| crate::classify::has_tie(&t)) {
            if crate::classify::has_tie(&tree) {
                self.sites.1 += 1;
            } else {
                self.sites.0 += 1;
            }
        }
        if crate::classify::has_tie(&tree) {
            let mut at = Vec::new();
            crate::engine::visit(&tree, &mut |n| {
                if n.tie {
                    at.push(format!("{} [{}]", n.name, toks[n.s..n.e].iter().map(|t| t.raw.as_str()).collect::<Vec<_>>().join(" ")));
                }
            });
            self.ties.push(format!("{text}\n      at {}", at.join("; ")));
        }
        self.cv.toks = toks;
        self.cv.text = text.to_string();
        match self.sent(&tree) {
            Ok(s) => {
                let out = print_sent(&self.cv.d, &self.md, &self.cv.vars.names, &s);
                if out == text {
                    return s;
                }
                self.exceptions.push((text.to_string(), format!("prints as {out}")));
            }
            Err(e) => self.exceptions.push((text.to_string(), e)),
        }
        self.prose(text)
    }

    fn flat<'n>(&self, n: &'n PNode) -> Vec<Fl<'n>> {
        let mut out = Vec::new();
        if let Rid::R(ri) = n.rid {
            flat_items(&self.cv.g.rules[ri].elems, &n.items, &mut out);
        }
        out
    }

    fn sent(&mut self, n: &PNode) -> Res<Sent> {
        use Fl::{N, W};
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("sort-union", [W(a), N(t), N(l), W(r)]) => Sent::SortUnion(["A", "An"][*a].into(), self.term(t)?, self.sorts(l)?, *r == 0),
            ("reldef-least", [N(x), N(t), N(on)]) => {
                let (x, (r, tag)) = (self.cv.bind(x)?, self.reldef(t)?);
                Sent::RelDef(x, r, tag, RelKind::Least(self.tn(on)?))
            }
            ("reldef-host", [N(x), N(t), N(on)]) => {
                let (x, (r, tag)) = (self.cv.bind(x)?, self.reldef(t)?);
                Sent::RelDef(x, r, tag, RelKind::Host(self.tn(on)?))
            }
            ("reldef-total", [N(x), N(t), N(of), N(e)]) => {
                let (x, (r, tag)) = (self.cv.bind(x)?, self.reldef(t)?);
                Sent::RelDef(x, r, tag, RelKind::Total(self.tn(of)?, self.cv.expr(e)?))
            }
            ("fndef", [N(x), N(t), N(t1), N(e1), N(t2), N(e2)]) => {
                let (x, (r, tag)) = (self.cv.bind(x)?, self.reldef(t)?);
                let k = RelKind::Function(self.tn(t1)?, self.cv.expr(e1)?, self.tn(t2)?, self.cv.expr(e2)?);
                Sent::RelDef(x, r, tag, k)
            }
            ("preddef", [W(s), rest @ ..]) => {
                let (x, rest) = match rest {
                    [W(0), N(x), rest @ ..] => (Some(self.cv.bind(x)?), rest),
                    [W(_), rest @ ..] => (None, rest),
                    _ => return Err("a predicate definition".into()),
                };
                let [W(v), N(pn), N(c)] = rest else { return Err("a predicate definition".into()) };
                Sent::PredDef(*s == 1, x, [Verb::Has, Verb::Is][*v], self.pname(pn)?, self.mcond(c)?)
            }
            ("range-rel", [W(k), N(c)]) => Sent::RangeDef([RangeRel::Equal, RangeRel::Overlapping, RangeRel::Disjoint][*k], self.mcond(c)?),
            ("for", [N(bs), N(fm)]) => Sent::For(self.binders(bs)?, self.formula(fm)?),
            ("formula", [N(fm)]) => Sent::Formula(self.formula(fm)?),
            _ => {
                let (id, hs) = self.phrase(n)?;
                Sent::Phrase(id, hs)
            }
        })
    }

    /// A relation definition's term: its entry in `rels`, and its tag.
    fn reldef(&mut self, n: &PNode) -> Res<(Id, TermTag)> {
        let t = self.term(n)?;
        Ok((self.md.rels.intern(&t.words), t.tag))
    }

    fn tn(&mut self, n: &PNode) -> Res<TyExpr> {
        self.cv.tn(n, String::new())
    }

    fn term(&mut self, n: &PNode) -> Res<Term> {
        let toks: Vec<usize> = n.items.iter().filter_map(|it| if let Item::T(i, _) = it { Some(*i) } else { None }).collect();
        let open = self.cv.toks[toks[0]].v.clone();
        let tag = if open == "<em>" {
            TermTag::Em
        } else if open == "<dfn>" {
            TermTag::Dfn(None)
        } else {
            let v = crate::spec::attr(&open, "variants").ok_or_else(|| format!("a term tag {open}"))?;
            TermTag::Dfn(Some(v))
        };
        let words = toks[1..toks.len() - 1].iter().map(|&i| self.cv.toks[i].v.clone()).collect::<Vec<_>>().join(" ");
        let t = Term { tag, words };
        if term_open(&t) != open {
            return Err(format!("a term tag {open}"));
        }
        Ok(t)
    }

    fn sorts(&mut self, n: &PNode) -> Res<Vec<(String, SortRef)>> {
        use Fl::{N, W};
        let items: Vec<&Rc<PNode>> = n.items.iter().filter_map(|it| if let Item::N(x, _) = it { Some(x) } else { None }).collect();
        if !crate::print::english_ok(n.items.len(), items.len()) {
            return Err("sort alternatives in an irregular form".into());
        }
        let mut out = Vec::new();
        for s in items {
            let f = self.flat(s);
            out.push(match (s.name, f.as_slice()) {
                ("dfn", [W(0), W(a), N(t)]) => (["a", "an"][*a].to_string(), SortRef::Term(self.term(t)?)),
                ("dfn", [W(_), N(t)]) => (String::new(), SortRef::Term(self.term(t)?)),
                ("ty", [W(0), W(a), N(t)]) => (["a", "an", "such a"][*a].to_string(), SortRef::Ty(self.tn(t)?)),
                ("ty", [W(_), N(t)]) => (String::new(), SortRef::Ty(self.tn(t)?)),
                _ => return Err("a sort alternative".into()),
            });
        }
        Ok(out)
    }

    fn binders(&mut self, n: &PNode) -> Res<Vec<Binder>> {
        let f = self.flat(n);
        let mut out = Vec::new();
        for x in f {
            if let Fl::N(b) = x {
                out.push(self.binder(b)?);
            }
        }
        Ok(out)
    }

    fn binder(&mut self, n: &PNode) -> Res<Binder> {
        use Fl::{N, W};
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("pair", [N(t), N(x), N(y), rest @ ..]) => {
                let (t, x, y) = (self.mty(t)?, self.cv.bind(x)?, self.cv.bind(y)?);
                let such = match rest {
                    [W(0), N(c)] => Some(self.mcond(c)?),
                    _ => None,
                };
                Binder::Pair(t, x, y, such)
            }
            ("pair-in", [N(t), N(x), N(y), N(e)]) => Binder::PairIn(self.mty(t)?, self.cv.bind(x)?, self.cv.bind(y)?, self.cv.expr(e)?),
            ("each", [N(t), N(x), N(e)]) => Binder::Each(self.mty(t)?, self.cv.bind(x)?, self.cv.expr(e)?),
            ("elem", [N(x), N(e)]) => Binder::Elem(self.cv.bind(x)?, self.cv.expr(e)?),
            ("one", [W(a), N(t), N(x)]) => Binder::One(["a", "an"][*a].into(), self.mty(t)?, self.cv.bind(x)?),
            _ => return Err(format!("binder {}", n.name)),
        })
    }

    fn mty(&mut self, n: &PNode) -> Res<TyExpr> {
        use Fl::N;
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("one", [N(t)]) => self.tn(t)?,
            ("or", [N(a), N(b)]) => TyExpr::Union(AltForm::Or, ConnForm::Plain, vec![self.tn(a)?, self.tn(b)?]),
            ("execution", []) => TyExpr::Sort(String::new(), vec![], self.cv.d.sorts.intern("execution"), String::new()),
            _ => return Err(format!("type {}", n.name)),
        })
    }

    fn formula(&mut self, n: &PNode) -> Res<Formula> {
        use Fl::{N, W};
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("rule", [N(a), N(c)]) => Formula::Rule(self.atom(a)?, self.mcond(c)?),
            ("holds", [N(c)]) => Formula::Holds(self.mcond(c)?),
            ("implies", [N(c), W(t), N(d)]) => Formula::Implies(*t == 0, self.mcond(c)?, self.mcond(d)?),
            _ => return Err(format!("formula {}", n.name)),
        })
    }

    /// A chain of atoms and connectives (left-associated by the parser), grouped as `conv` groups conditions.
    fn mcond(&mut self, n: &PNode) -> Res<MCond> {
        if !n.name.starts_with("cond:") {
            return Ok(MCond::Atom(Box::new(self.atom(n)?)));
        }
        let mut atoms = Vec::new();
        let mut conns: Vec<Vec<String>> = Vec::new();
        let mut cur = n;
        loop {
            if !cur.name.starts_with("cond:") {
                atoms.push(cur);
                break;
            }
            let Some(Item::N(last, _)) = cur.items.last() else { return Err("a connective".into()) };
            atoms.push(last);
            conns.push(cur.items[1..cur.items.len() - 1].iter().map(|x| if let Item::L(w, _) = x { w.clone() } else { String::new() }).collect());
            let Item::N(first, _) = &cur.items[0] else { return Err("a connective".into()) };
            cur = first;
        }
        atoms.reverse();
        conns.reverse();
        let cs = atoms.into_iter().map(|a| self.atom(a).map(|x| MCond::Atom(Box::new(x)))).collect::<Res<Vec<_>>>()?;
        build_conn(cs, &conns)
    }

    fn atom(&mut self, n: &PNode) -> Res<Atom> {
        use Fl::{N, T, W};
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("rel", [N(a), N(r), N(b), rest @ ..]) => {
                let (r, a, b) = (self.rel(r)?, self.cv.expr(a)?, self.cv.expr(b)?);
                let x = match rest {
                    [W(0), N(x)] => Some(self.cv.expr(x)?),
                    _ => None,
                };
                Atom::Rel(r, a, b, x)
            }
            ("exists", [W(v), W(q), N(t), N(x), rest @ ..]) => {
                let (t, x) = (self.mty(t)?, self.cv.bind(x)?);
                let (dom, c) = match rest {
                    [W(0), W(0), N(e), N(c)] => (Some(Dom::In(self.cv.expr(e)?)), c),
                    [W(0), W(_), N(e), N(c)] => (Some(Dom::HasInRange(self.cv.expr(e)?)), c),
                    [W(_), N(c)] => (None, c),
                    _ => return Err("an existential".into()),
                };
                let q = [Quant::Some, Quant::An, Quant::A, Quant::No][*q];
                Atom::Exists(*v == 1, q, t, x, dom, Box::new(self.mcond(c)?))
            }
            ("not", [W(b), N(c)]) => Atom::Not(*b == 0, Box::new(self.mcond(c)?)),
            ("same", [N(a), N(b), W(neg), N(t)]) => Atom::Same(*neg == 0, self.cv.expr(a)?, self.cv.expr(b)?, self.tn(t)?),
            ("contains", [N(s), N(e)]) => Atom::Contains(self.mexpr(s)?, false, vec![self.mexpr(e)?]),
            ("contains2", [N(s), W(b), N(x), N(y)]) => Atom::Contains(self.mexpr(s)?, *b == 0, vec![self.mexpr(x)?, self.mexpr(y)?]),
            ("ranges", [N(a), N(b), W(neg), W(k)]) => {
                let k = [RangeRel::Equal, RangeRel::Overlapping, RangeRel::Disjoint][*k];
                Atom::Ranges(*neg == 1, k, self.cv.expr(a)?, self.cv.expr(b)?)
            }
            ("before", [N(a), N(b), N(l)]) => Atom::Before(self.cv.expr(a)?, self.cv.expr(b)?, self.cv.expr(l)?),
            ("following", [W(q), W(c)]) => Atom::Following(if *q == 0 { Following::Any(*c == 0) } else { Following::All(*c == 0) }),
            ("following-the", []) => Atom::Following(Following::The),
            ("following-alg", [T(i)]) => Atom::FollowingAlg(self.cv.tok_expr(*i)?),
            ("pred", [N(e), W(v), N(pn)]) => Atom::Pred(vec![self.cv.expr(e)?], [Verb::Has, Verb::Is][*v], self.pname(pn)?, None),
            ("pred2", [N(a), N(b), N(pn), rest @ ..]) => {
                let (a, b, pn) = (self.cv.expr(a)?, self.cv.expr(b)?, self.pname(pn)?);
                let x = match rest {
                    [W(0), N(x)] => Some(self.cv.expr(x)?),
                    _ => None,
                };
                Atom::Pred(vec![a, b], Verb::AreIn, pn, x)
            }
            ("in-range", [N(e), N(b)]) => Atom::InRange(self.cv.expr(e)?, self.cv.expr(b)?),
            ("no-cycle", [N(r), N(q), N(x)]) => Atom::NoCycle(vec![self.rel(r)?, self.rel(q)?], self.cv.expr(x)?),
            ("admits", [W(s), rest @ ..]) => {
                let (x, rest) = match rest {
                    [N(x), rest @ ..] if *s == 0 => (Some(self.cv.expr(x)?), rest),
                    _ => (None, rest),
                };
                let [W(a), N(r), W(po)] = rest else { return Err("an admits atom".into()) };
                Atom::Admits(x, ["a", "an"][*a].into(), self.rel(r)?, *po == 0)
            }
            ("is-a", [N(e), W(ei), W(a), N(t)]) => Atom::IsA(self.cv.expr(e)?, *ei == 0, ["a", "an"][*a].into(), self.mty(t)?),
            ("core", [N(c)]) => Atom::Core(self.cv.cond(c)?),
            _ => {
                let (id, hs) = self.phrase(n)?;
                Atom::Phrase(id, hs)
            }
        })
    }

    fn mexpr(&mut self, n: &PNode) -> Res<MExpr> {
        use Fl::N;
        let f = self.flat(n);
        Ok(match (n.name, f.as_slice()) {
            ("e", [N(e)]) => MExpr::E(self.cv.expr(e)?),
            ("in", [N(fx), N(x)]) => match self.cv.expr(fx)? {
                c @ Expr::Call(..) => MExpr::In(c, self.cv.expr(x)?),
                _ => return Err("`in` after an expression that is not a call".into()),
            },
            ("pair", [N(a), N(b)]) => MExpr::Pair(self.cv.expr(a)?, self.cv.expr(b)?),
            _ => return Err(format!("expression {}", n.name)),
        })
    }

    /// The alternative an `( a | b )` element took, as its words.
    fn alt_words(n: &PNode) -> Res<String> {
        match n.items.as_slice() {
            [Item::A(_, v, _)] => Ok(v.iter().filter_map(|x| if let Item::L(w, _) = x { Some(w.clone()) } else { None }).collect::<Vec<_>>().join(" ")),
            _ => Err(format!("{} is not a choice", n.name)),
        }
    }

    fn rel(&mut self, n: &PNode) -> Res<Id> {
        let w = Self::alt_words(n)?;
        Ok(self.md.rels.intern(&w))
    }

    fn pname(&mut self, n: &PNode) -> Res<PName> {
        match n.name {
            "lex" => {
                let w = Self::alt_words(n)?;
                Ok(PName::Lex(self.md.names.intern(&w)))
            }
            "xref" => match n.items.as_slice() {
                [Item::T(i, _)] => Ok(PName::Xref(self.cv.tok_expr(*i)?)),
                _ => Err("a predicate cross-reference".into()),
            },
            _ => match n.items.as_slice() {
                [Item::N(t, _)] => {
                    let t = self.term(t)?;
                    Ok(PName::Term(self.md.names.intern(&t.words), t.tag))
                }
                _ => Err("a predicate name".into()),
            },
        }
    }

    fn phrase(&mut self, n: &PNode) -> Res<(Id, Vec<MHole>)> {
        let Rid::R(ri) = n.rid else { return Err(format!("built-in {} as a phrase", n.name)) };
        let g = self.cv.g;
        let r = &g.rules[ri];
        let id = self.md.phrase(r.cat, r.name, &r.elems);
        let mut hs = Vec::new();
        self.holes(&r.elems, &n.items, &mut hs)?;
        Ok((id, hs))
    }

    fn holes(&mut self, els: &[(El, bool)], items: &[Item], out: &mut Vec<MHole>) -> Res<()> {
        for ((el, _), it) in els.iter().zip(items) {
            match (el, it) {
                (El::Lit(_), _) | (El::KindV(..), _) => {}
                (El::Kind(k), Item::T(i, _)) => out.push(MHole::H(match k {
                    Kc::K(K::Word) | Kc::Cap | Kc::Low | Kc::Up => Hole::Text(self.cv.toks[*i].v.clone()),
                    _ => Hole::E(self.cv.tok_expr(*i)?),
                })),
                (El::Hole(c), Item::N(m, _)) => out.push(self.hole(c, m)?),
                (El::Opt(inner), Item::O(v, _)) => match v {
                    Some(v) => {
                        out.push(MHole::W(0));
                        self.holes(inner, v, out)?;
                    }
                    None => out.push(MHole::W(1)),
                },
                (El::Alt(alts), Item::A(k, v, _)) => {
                    out.push(MHole::W(*k));
                    self.holes(&alts[*k], v, out)?;
                }
                _ => return Err(format!("template element {el:?} against {it:?}")),
            }
        }
        Ok(())
    }

    fn hole(&mut self, c: &str, n: &PNode) -> Res<MHole> {
        Ok(match c {
            "DFN" => MHole::Term(self.term(n)?),
            "MREL" => MHole::Rel(self.rel(n)?),
            "MPN" => MHole::Name(self.pname(n)?),
            "MC" | "MCA" => MHole::C(self.mcond(n)?),
            "MME" => MHole::E(self.mexpr(n)?),
            "MTY" => MHole::T(self.mty(n)?),
            "CA" => MHole::H(Hole::C(self.cv.cond(n)?)),
            "E" | "P" | "V" | "TN" | "T" | "FN" | "FieldEL" => MHole::H(self.cv.hole(c, n)?),
            _ => return Err(format!("a {c} hole")),
        })
    }
}

/// Connectives between conditions, grouped as `conv::build_conn` groups the step grammar's.
fn build_conn(cs: Vec<MCond>, conns: &[Vec<String>]) -> Res<MCond> {
    let mut it = cs.into_iter();
    let mut left = it.next().ok_or("an empty condition")?;
    let mut pending: Vec<MCond> = Vec::new();
    for c in conns {
        let next = it.next().ok_or("a connective without its condition")?;
        let Some(w) = c.iter().find(|w| *w == "and" || *w == "or") else {
            pending.push(next);
            continue;
        };
        let conj = if w == "and" { Conj::And } else { Conj::Or };
        let form = if c.len() == 2 { ConnForm::Comma } else { ConnForm::Plain };
        if form == ConnForm::Plain && !pending.is_empty() {
            return Err("a comma list closed without a comma".into());
        }
        let mut items = match (form, left) {
            (ConnForm::Plain, MCond::And(ConnForm::Plain, xs)) if conj == Conj::And => xs,
            (ConnForm::Plain, MCond::Or(ConnForm::Plain, xs)) if conj == Conj::Or => xs,
            (_, l) => vec![l],
        };
        items.append(&mut pending);
        items.push(next);
        left = match conj {
            Conj::And => MCond::And(form, items),
            Conj::Or => MCond::Or(form, items),
        };
    }
    if !pending.is_empty() {
        return Err("a condition list with no conjunction".into());
    }
    Ok(left)
}

/// Section 29 scanned and converted, with declaration tables of its own.
pub fn build(html: &str, sp: &Spec, g: &Grammar) -> Res<Doc> {
    let mut d = Decls::default();
    let mut cids = Vec::new();
    for cl in &sp.clauses {
        let c = d.intern_clause(&cl.id, &[]);
        d.set_op(c, cl.op().unwrap_or_default());
        cids.push(c);
    }
    d.set_cids(cids);
    build_on(html, sp, g, d)
}

/// Section 29 scanned and converted, its names interned after `d`'s. The first pass
/// finds the definitions, which seed the relation and predicate lexicons in document order.
pub fn build_on(html: &str, sp: &Spec, g: &Grammar, mut d: Decls) -> Res<Doc> {
    let c = sp.clauses.iter().find(|c| c.id == "sec-memory-model").ok_or("no sec-memory-model clause")?;
    let start = html[..c.start].rfind("<emu-clause").ok_or("no clause tag")?;
    let end = c.end + "</emu-clause>".len();
    let src = &html[start..end];
    let env = crate::data::env(html, sp, &d.cids, &g.overlay.grammar_ids);
    let first = pass(src, start, sp, g, &env, &mut d, MDecls::default())?;
    let mut seed = MDecls::default();
    seeds(&first.0, &first.1, &mut seed);
    let (blocks, md, exceptions, ties, sites) = pass(src, start, sp, g, &env, &mut d, seed)?;
    Ok(Doc { d, md, blocks, src: src.to_string(), exceptions, ties, sites })
}

type Pass = (Vec<Block>, MDecls, Vec<(String, String)>, Vec<String>, (usize, usize));

fn pass(src: &str, start: usize, sp: &Spec, g: &Grammar, env: &crate::conv::Env, d: &mut Decls, md: MDecls) -> Res<Pass> {
    let rows = HashMap::new();
    let mut lines = Vec::new();
    let mut offs = Vec::new();
    let mut o = start;
    for l in src.split('\n') {
        lines.push(l);
        offs.push(o);
        o += l.len() + 1;
    }
    let mut s = Src { lines, offs, i: 0 };
    let no_anchors = crate::conv::Anchors::new();
    let cv = Conv {
        open: Vec::new(),
        rhs: Default::default(),
            lhs: Default::default(),
            narrow: Vec::new(),
            symbols: false,
        channel: crate::ast::Channel::Pending,
        clause: String::new(),
        anchors: &no_anchors,
        stops: None,
        readings: Vec::new(),
        g,
        d,
        env,
        vars: Vars::default(),
        rows: &rows,
        toks: Vec::new(),
        text: String::new(),
        unresolved: Vec::new(),
        exceptions: Vec::new(),
        closures: Vec::new(),
        base: 0,
    };
    let algs = sp.algs.iter().enumerate().map(|(k, a)| (a.pos, k)).collect();
    let mut off = Parser::new(g, 99, false);
    off.munch = false;
    let mut b = B { cv, p: Parser::new(g, 99, false), off, sites: (0, 0), md, algs, sp, exceptions: Vec::new(), ties: Vec::new() };
    let blocks = b.blocks(&mut s, None)?;
    Ok((blocks, b.md, b.exceptions, b.ties, b.sites))
}

/// The relations and predicates the blocks define, in document order: relation
/// definitions, predicate definitions, and rules whose head is a predicate.
fn seeds(bs: &[Block], md: &MDecls, out: &mut MDecls) {
    let pname = |n: &PName, out: &mut MDecls| match n {
        PName::Lex(i) | PName::Term(i, _) => {
            out.names.intern(md.names.name(*i));
        }
        PName::Xref(_) => {}
    };
    let mut sent = |s: &Sent, out: &mut MDecls| match s {
        Sent::RelDef(_, r, _, _) => {
            out.rels.intern(md.rels.name(*r));
        }
        Sent::PredDef(_, _, _, n, _) => pname(n, out),
        Sent::For(_, Formula::Rule(Atom::Pred(_, _, n, _), _)) | Sent::Formula(Formula::Rule(Atom::Pred(_, _, n, _), _)) => pname(n, out),
        _ => {}
    };
    fn go(bs: &[Block], f: &mut dyn FnMut(&Sent, &mut MDecls), out: &mut MDecls) {
        for b in bs {
            match b {
                Block::Clause { kids, .. } => go(kids, f, out),
                Block::Para { sents, .. } | Block::Text { sents, .. } => sents.iter().for_each(|s| f(s, out)),
                Block::List { items, .. } => {
                    for li in items {
                        li.inline.iter().flatten().for_each(|s| f(s, out));
                        go(&li.kids, f, out);
                    }
                }
                _ => {}
            }
        }
    }
    go(bs, &mut sent, out);
}

// ---------------------------------------------------------------- printing

fn term_open(t: &Term) -> String {
    match &t.tag {
        TermTag::Em => "<em>".into(),
        TermTag::Dfn(None) => "<dfn>".into(),
        TermTag::Dfn(Some(v)) => format!("<dfn variants=\"{v}\">"),
    }
}

fn term(p: &mut Printer, t: &Term) {
    p.w(&term_open(t));
    for (i, w) in t.words.split(' ').enumerate() {
        if i == 0 {
            p.gw(w);
        } else {
            p.w(w);
        }
    }
    p.gw(if t.tag == TermTag::Em { "</em>" } else { "</dfn>" });
}

struct MP<'a, 'p> {
    p: &'p mut Printer<'a>,
    md: &'a MDecls,
}

impl<'a, 'p> MP<'a, 'p> {
    fn sent(&mut self, s: &'a Sent) {
        match s {
            Sent::SortUnion(a, t, alts, rec) => {
                self.p.w(a);
                term(self.p, t);
                self.p.words("is either");
                self.p.english(alts, "or", |p, (a, s)| {
                    if !a.is_empty() {
                        p.words(a);
                    }
                    match s {
                        SortRef::Term(t) => term(p, t),
                        SortRef::Ty(t) => p.ty(t),
                    }
                });
                if *rec {
                    self.p.w("Record");
                }
                self.p.w(".");
            }
            Sent::RelDef(x, r, tag, k) => {
                self.p.words("For a candidate execution");
                self.p.var(x);
                self.p.w(",");
                if !matches!(k, RelKind::Total(..)) {
                    self.p.w("its");
                }
                term(self.p, &Term { tag: tag.clone(), words: self.md.rels.name(*r).to_string() });
                match k {
                    RelKind::Least(on) => {
                        self.p.words("Relation is the least Relation on");
                        self.p.ty(on);
                        self.p.words("that satisfies the following .");
                    }
                    RelKind::Host(on) => {
                        self.p.words("Relation is a host-provided strict partial order on");
                        self.p.ty(on);
                        self.p.words("that satisfies at least the following .");
                    }
                    RelKind::Total(of, e) => {
                        self.p.words("is a strict total order of all");
                        self.p.ty(of);
                        self.p.w("in");
                        self.p.expr(e);
                        self.p.words("that satisfies the following .");
                    }
                    RelKind::Function(t1, e1, t2, e2) => {
                        self.p.words("function is a mathematical function mapping");
                        self.p.ty(t1);
                        self.p.w("in");
                        self.p.expr(e1);
                        self.p.words("to Lists of");
                        self.p.ty(t2);
                        self.p.w("in");
                        self.p.expr(e2);
                        self.p.words("that satisfies the following conditions .");
                    }
                }
            }
            Sent::PredDef(valid, x, v, n, c) => {
                self.p.words(if *valid { "An execution" } else { "A candidate execution" });
                if let Some(x) = x {
                    self.p.var(x);
                }
                self.verb(*v);
                self.pname(n);
                self.p.w("if");
                self.mcond(c);
                self.p.w(".");
            }
            Sent::RangeDef(k, c) => {
                self.p.words("Two events");
                self.p.gw("'");
                self.p.words("memory ranges are");
                self.p.w(range_word(*k));
                self.p.w("when");
                self.mcond(c);
                self.p.w(".");
            }
            Sent::For(bs, f) => {
                self.p.w("For");
                for (i, b) in bs.iter().enumerate() {
                    if i > 0 {
                        self.p.w("and");
                    }
                    self.binder(b);
                }
                self.p.w(",");
                self.formula(f);
                self.p.w(".");
            }
            Sent::Formula(f) => {
                self.formula(f);
                self.p.w(".");
            }
            Sent::Phrase(id, hs) => self.phrase(*id, hs),
            Sent::Prose(_) => unreachable!("prose is printed verbatim"),
        }
    }

    fn verb(&mut self, v: Verb) {
        self.p.words(match v {
            Verb::Has => "has",
            Verb::Is => "is",
            Verb::AreIn => "are in a",
        });
    }

    fn pname(&mut self, n: &'a PName) {
        match n {
            PName::Lex(i) => self.p.words(self.md.names.name(*i)),
            PName::Term(i, tag) => term(self.p, &Term { tag: tag.clone(), words: self.md.names.name(*i).to_string() }),
            PName::Xref(e) => self.p.expr(e),
        }
    }

    fn binder(&mut self, b: &'a Binder) {
        match b {
            Binder::Pair(t, x, y, such) => {
                self.p.ty(t);
                self.p.var(x);
                self.p.w("and");
                self.p.var(y);
                if let Some(c) = such {
                    self.p.words("such that");
                    self.mcond(c);
                }
            }
            Binder::PairIn(t, x, y, e) => {
                self.p.ty(t);
                self.p.var(x);
                self.p.w("and");
                self.p.var(y);
                self.p.words("that are contained in");
                self.p.expr(e);
            }
            Binder::Each(t, x, e) => {
                self.p.w("each");
                self.p.ty(t);
                self.p.var(x);
                self.p.w("in");
                self.p.expr(e);
            }
            Binder::Elem(x, e) => {
                self.p.words("each element");
                self.p.var(x);
                self.p.w("of");
                self.p.expr(e);
            }
            Binder::One(a, t, x) => {
                self.p.w(a);
                self.p.ty(t);
                self.p.var(x);
            }
        }
    }

    fn formula(&mut self, f: &'a Formula) {
        match f {
            Formula::Rule(a, c) => {
                self.atom(a);
                self.p.w("if");
                self.mcond(c);
            }
            Formula::Holds(c) => self.mcond(c),
            Formula::Implies(then, c, d) => {
                self.p.w("if");
                self.mcond(c);
                self.p.w(",");
                if *then {
                    self.p.w("then");
                }
                self.mcond(d);
            }
        }
    }

    fn mcond(&mut self, c: &'a MCond) {
        match c {
            MCond::Atom(a) => self.atom(a),
            MCond::And(f, cs) | MCond::Or(f, cs) => {
                let conj = if matches!(c, MCond::And(..)) { "and" } else { "or" };
                let n = cs.len();
                for (i, x) in cs.iter().enumerate() {
                    if i > 0 {
                        if *f == ConnForm::Comma {
                            self.p.w(",");
                        }
                        if *f == ConnForm::Plain || i == n - 1 {
                            self.p.w(conj);
                        }
                    }
                    self.mcond(x);
                }
            }
        }
    }

    fn atom(&mut self, a: &'a Atom) {
        match a {
            Atom::Rel(r, x, y, e) => {
                self.p.expr(x);
                self.p.w(self.md.rels.name(*r));
                self.p.expr(y);
                if let Some(e) = e {
                    self.p.w("in");
                    self.p.expr(e);
                }
            }
            Atom::Exists(v, q, t, x, dom, c) => {
                self.p.w("there");
                self.p.w(if *v { "exists" } else { "is" });
                self.p.w(match q {
                    Quant::Some => "some",
                    Quant::An => "an",
                    Quant::A => "a",
                    Quant::No => "no",
                });
                self.p.ty(t);
                self.p.var(x);
                match dom {
                    Some(Dom::In(e)) => {
                        self.p.w("in");
                        self.p.expr(e);
                    }
                    Some(Dom::HasInRange(e)) => {
                        self.p.words("that has");
                        self.p.expr(e);
                        self.p.words("in its memory range");
                    }
                    None => {}
                }
                self.p.words("such that");
                self.mcond(c);
            }
            Atom::Not(both, c) => {
                self.p.words("it is not the case that");
                if *both {
                    self.p.w("both");
                }
                self.mcond(c);
            }
            Atom::Same(neg, x, y, t) => {
                self.p.expr(x);
                self.p.w("and");
                self.p.expr(y);
                self.p.w("are");
                if *neg {
                    self.p.w("not");
                }
                self.p.words("the same");
                self.p.ty(t);
            }
            Atom::Contains(s, both, xs) => {
                self.mexpr(s);
                self.p.w("contains");
                if *both {
                    self.p.w("both");
                }
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        self.p.w("and");
                    }
                    self.mexpr(x);
                }
            }
            Atom::Ranges(neg, k, x, y) => {
                self.p.expr(x);
                self.p.w("and");
                self.p.expr(y);
                self.p.words(if *neg { "do not have" } else { "have" });
                self.p.w(range_word(*k));
                self.p.words("memory ranges");
            }
            Atom::Before(x, y, l) => {
                self.p.expr(x);
                self.p.words("is before");
                self.p.expr(y);
                self.p.words("in List order of");
                self.p.expr(l);
            }
            Atom::Following(f) => match f {
                Following::Any(c) | Following::All(c) => {
                    self.p.w(if matches!(f, Following::Any(_)) { "any" } else { "all" });
                    self.p.words("of the following");
                    if *c {
                        self.p.w("conditions");
                    }
                    self.p.words("are true");
                }
                Following::The => self.p.words("the following is true"),
            },
            Atom::FollowingAlg(e) => {
                self.p.words("the following algorithm returns");
                self.p.expr(e);
            }
            Atom::Pred(xs, v, n, e) => {
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        self.p.w("and");
                    }
                    self.p.expr(x);
                }
                self.verb(*v);
                self.pname(n);
                if let Some(e) = e {
                    self.p.w("in");
                    self.p.expr(e);
                }
            }
            Atom::NoCycle(rs, x) => {
                self.p.words("there is no cycle in the union of");
                for (i, r) in rs.iter().enumerate() {
                    if i > 0 {
                        self.p.w("and");
                    }
                    self.p.w(self.md.rels.name(*r));
                }
                self.p.w("in");
                self.p.expr(x);
            }
            Atom::Admits(x, a, r, po) => {
                match x {
                    Some(x) => self.p.expr(x),
                    None => self.p.w("it"),
                }
                self.p.w("admits");
                self.p.w(a);
                self.p.w(self.md.rels.name(*r));
                self.p.w("Relation");
                if *po {
                    self.p.words("that is a strict partial order");
                }
            }
            Atom::InRange(e, b) => {
                self.p.expr(e);
                self.p.w("has");
                self.p.expr(b);
                self.p.words("in its memory range");
            }
            Atom::IsA(e, either, a, t) => {
                self.p.expr(e);
                self.p.w("is");
                if *either {
                    self.p.w("either");
                }
                self.p.w(a);
                self.p.ty(t);
            }
            Atom::Core(c) => self.p.cond(c),
            Atom::Phrase(id, hs) => self.phrase(*id, hs),
        }
    }

    fn mexpr(&mut self, e: &'a MExpr) {
        match e {
            MExpr::E(e) => self.p.expr(e),
            MExpr::In(f, x) => {
                self.p.expr(f);
                self.p.w("in");
                self.p.expr(x);
            }
            MExpr::Pair(a, b) => {
                self.p.w("(");
                self.p.expr(a);
                self.p.w(",");
                self.p.expr(b);
                self.p.w(")");
            }
        }
    }

    fn phrase(&mut self, id: Id, hs: &'a [MHole]) {
        let mut it = hs.iter();
        let t = &self.md.phrases[id].template;
        self.pieces(t, &mut it);
        assert!(it.next().is_none(), "a phrase with too many holes");
    }

    fn pieces(&mut self, ps: &'a [MPiece], hs: &mut std::slice::Iter<'a, MHole>) {
        for pc in ps {
            match pc {
                MPiece::Word(w) => self.p.w(w),
                MPiece::Glue => {
                    self.p.g();
                }
                MPiece::Hole(_) => {
                    let h = hs.next().expect("a phrase with too few holes");
                    match h {
                        MHole::H(h) => self.p.hole(h),
                        MHole::Term(t) => term(self.p, t),
                        MHole::Rel(r) => self.p.w(self.md.rels.name(*r)),
                        MHole::Name(n) => self.pname(n),
                        MHole::C(c) => self.mcond(c),
                        MHole::E(e) => self.mexpr(e),
                        MHole::T(t) => self.p.ty(t),
                        MHole::W(_) => panic!("a choice index for a hole"),
                    }
                }
                MPiece::Choice(alts) => {
                    let Some(MHole::W(k)) = hs.next() else { panic!("a choice without its index") };
                    self.pieces(&alts[*k], hs);
                }
            }
        }
    }
}

fn range_word(k: RangeRel) -> &'static str {
    match k {
        RangeRel::Equal => "equal",
        RangeRel::Overlapping => "overlapping",
        RangeRel::Disjoint => "disjoint",
    }
}

fn prose_text(vars: &[String], ps: &[Part]) -> String {
    let mut s = String::new();
    for p in ps {
        match p {
            Part::Text(t) => s.push_str(t),
            Part::Hole(Hole::E(Expr::Var(x))) => s.push_str(&format!("_{}_", vars[*x])),
            Part::Hole(h) => panic!("a prose hole {h:?}"),
        }
    }
    s
}

/// A sentence printed: verbatim if prose, else from its data, first letter capitalized.
pub fn print_sent(d: &Decls, md: &MDecls, vars: &[String], s: &Sent) -> String {
    if let Sent::Prose(ps) = s {
        return prose_text(vars, ps);
    }
    let mut p = Printer::new(d, vars, &[]);
    MP { p: &mut p, md }.sent(s);
    cap_first(&p.take_text())
}

fn print_sents(d: &Decls, md: &MDecls, vars: &[String], ss: &[Sent]) -> String {
    ss.iter().map(|s| print_sent(d, md, vars, s)).collect::<Vec<_>>().join(" ")
}

fn print_table(d: &Decls, vars: &[String], ind: usize, t: &FieldTable) -> String {
    let pad = |k: usize| " ".repeat(ind + k);
    let mut out = vec![format!("{}<emu-table id=\"{}\" caption=\"{}\">", pad(0), t.id, t.caption), format!("{}<table>", pad(2))];
    out.push(format!("{}<thead>", pad(4)));
    out.push(format!("{}<tr>", pad(6)));
    for h in &t.heads {
        out.push(format!("{}<th>{h}</th>", pad(8)));
    }
    out.push(format!("{}</tr>", pad(6)));
    out.push(format!("{}</thead>", pad(4)));
    for r in &t.rows {
        let mut p = Printer::new(d, vars, &[]);
        p.ty(&r.ty);
        let ty = p.take_text();
        out.push(format!("{}<tr>", pad(4)));
        out.push(format!("{}<td>[[{}]]</td>", pad(6), d.fields.name(r.field)));
        out.push(format!("{}<td>{ty}</td>", pad(6)));
        out.push(format!("{}<td>{}</td>", pad(6), r.desc));
        out.push(format!("{}</tr>", pad(4)));
    }
    out.push(format!("{}</table>", pad(2)));
    out.push(format!("{}</emu-table>", pad(0)));
    out.join("\n")
}

fn print_blocks(doc: &Doc, sp: &Spec, vars: &[String], bs: &[Block], out: &mut Vec<String>) {
    let (d, md) = (&doc.d, &doc.md);
    for b in bs {
        match b {
            Block::Clause { indent, attrs, vars, kids } => {
                out.push(format!("{}<emu-clause{attrs}>", " ".repeat(*indent)));
                print_blocks(doc, sp, vars, kids, out);
                out.push(format!("{}</emu-clause>", " ".repeat(*indent)));
            }
            Block::Para { indent, sents } => out.push(format!("{}<p>{}</p>", " ".repeat(*indent), print_sents(d, md, vars, sents))),
            Block::Text { indent, sents } => out.push(format!("{}{}", " ".repeat(*indent), print_sents(d, md, vars, sents))),
            Block::List { indent, items } => {
                let pad = " ".repeat(*indent);
                out.push(format!("{pad}<ul>"));
                for li in items {
                    match &li.inline {
                        Some(ss) => out.push(format!("{pad}  <li>{}</li>", print_sents(d, md, vars, ss))),
                        None => {
                            out.push(format!("{pad}  <li>"));
                            print_blocks(doc, sp, vars, &li.kids, out);
                            out.push(format!("{pad}  </li>"));
                        }
                    }
                }
                out.push(format!("{pad}</ul>"));
            }
            Block::Table { indent, table } => out.push(print_table(d, vars, *indent, table)),
            Block::Note { indent, lines } => {
                out.push(format!("{}<emu-note>", " ".repeat(*indent)));
                out.extend(lines.iter().cloned());
                out.push(format!("{}</emu-note>", " ".repeat(*indent)));
            }
            Block::Alg { indent, alg } => out.push(format!("{}<emu-alg>{}</emu-alg>", " ".repeat(*indent), sp.algs[*alg].raw)),
            Block::Heading(ls) => out.extend(ls.iter().cloned()),
            Block::Raw(l) => out.push(l.clone()),
            Block::Blank => out.push(String::new()),
        }
    }
}

/// The whole section printed from the data.
pub fn print(doc: &Doc, sp: &Spec) -> String {
    let mut out = Vec::new();
    print_blocks(doc, sp, &[], &doc.blocks, &mut out);
    out.join("\n")
}

// ---------------------------------------------------------------- coverage

/// Per clause: sentences by class, field rows, notes, algorithms, verbatim lines, attachments.
#[derive(Default, Clone, Copy)]
pub struct Cov {
    pub core: usize,
    pub phrase: usize,
    pub prose: usize,
    /// relational atoms with a core constructor, and phrase atoms
    pub atoms_core: usize,
    pub atoms_phrase: usize,
    pub rows: usize,
    pub rows_typed: usize,
    /// a field table's Meaning cells
    pub desc: usize,
    /// paragraphs, list items, field tables
    pub paras: usize,
    pub items: usize,
    pub tables: usize,
    pub notes: usize,
    pub algs: usize,
    pub raw: usize,
    /// sentences ending in "the following …", and those with the block they need after them
    pub follow: usize,
    pub follow_ok: usize,
}

impl Cov {
    pub fn sents(&self) -> usize {
        self.core + self.phrase + self.prose
    }

    fn add(&mut self, o: &Cov) {
        self.core += o.core;
        self.phrase += o.phrase;
        self.prose += o.prose;
        self.atoms_core += o.atoms_core;
        self.atoms_phrase += o.atoms_phrase;
        self.rows += o.rows;
        self.rows_typed += o.rows_typed;
        self.desc += o.desc;
        self.paras += o.paras;
        self.items += o.items;
        self.tables += o.tables;
        self.notes += o.notes;
        self.algs += o.algs;
        self.raw += o.raw;
        self.follow += o.follow;
        self.follow_ok += o.follow_ok;
    }
}

/// What a sentence needs after it: a list, a table or an algorithm.
#[derive(PartialEq, Clone, Copy)]
enum Need {
    List,
    Table,
    Alg,
}

fn atoms_c(c: &MCond, need: &mut Option<Need>, cov: &mut Cov) {
    match c {
        MCond::Atom(a) => atom_c(a, need, cov),
        MCond::And(_, cs) | MCond::Or(_, cs) => cs.iter().for_each(|x| atoms_c(x, need, cov)),
    }
}

fn atom_c(a: &Atom, need: &mut Option<Need>, cov: &mut Cov) {
    match a {
        Atom::Phrase(_, hs) => {
            cov.atoms_phrase += 1;
            for h in hs {
                if let MHole::C(c) = h {
                    atoms_c(c, need, cov);
                }
            }
        }
        Atom::Exists(.., c) | Atom::Not(_, c) => {
            cov.atoms_core += 1;
            atoms_c(c, need, cov);
        }
        Atom::Following(_) => {
            cov.atoms_core += 1;
            *need = Some(Need::List);
        }
        Atom::FollowingAlg(_) => {
            cov.atoms_core += 1;
            *need = Some(Need::Alg);
        }
        _ => cov.atoms_core += 1,
    }
}

fn formula_c(f: &Formula, need: &mut Option<Need>, cov: &mut Cov) {
    match f {
        Formula::Rule(a, c) => {
            atom_c(a, need, cov);
            atoms_c(c, need, cov);
        }
        Formula::Holds(c) => atoms_c(c, need, cov),
        Formula::Implies(_, c, d) => {
            atoms_c(c, need, cov);
            atoms_c(d, need, cov);
        }
    }
}

/// A sentence counted; what it needs after it.
fn sent_c(md: &MDecls, s: &Sent, cov: &mut Cov) -> Option<Need> {
    let mut need = None;
    match s {
        Sent::Prose(_) => cov.prose += 1,
        Sent::Phrase(id, hs) => {
            cov.phrase += 1;
            if md.phrases[*id].name == "record-sort" {
                need = Some(Need::Table);
            }
            for h in hs {
                if let MHole::C(c) = h {
                    atoms_c(c, &mut need, cov);
                }
            }
        }
        Sent::RelDef(..) => {
            cov.core += 1;
            need = Some(Need::List);
        }
        Sent::PredDef(.., c) | Sent::RangeDef(_, c) => {
            cov.core += 1;
            atoms_c(c, &mut need, cov);
        }
        Sent::For(bs, f) => {
            cov.core += 1;
            for b in bs {
                if let Binder::Pair(_, _, _, Some(c)) = b {
                    atoms_c(c, &mut need, cov);
                }
            }
            formula_c(f, &mut need, cov);
        }
        Sent::Formula(f) => {
            cov.core += 1;
            formula_c(f, &mut need, cov);
        }
        Sent::SortUnion(..) => cov.core += 1,
    }
    need
}

fn cover(md: &MDecls, bs: &[Block], clause: &str, out: &mut BTreeMap<String, Cov>, order: &mut Vec<String>) {
    let mut cur = Cov::default();
    let mut pending: Option<Need> = None;
    let sents_need = |ss: &[Sent], cur: &mut Cov| -> Option<Need> {
        let mut last = None;
        for s in ss {
            last = sent_c(md, s, cur);
        }
        last
    };
    for b in bs {
        if matches!(b, Block::Blank) {
            continue;
        }
        if let Some(n) = pending.take() {
            let ok = matches!((n, b), (Need::List, Block::List { .. }) | (Need::Table, Block::Table { .. }) | (Need::Alg, Block::Alg { .. }));
            cur.follow_ok += usize::from(ok);
        }
        match b {
            Block::Clause { attrs, kids, .. } => {
                let id = crate::spec::attr(attrs, "id").unwrap_or_default();
                cover(md, kids, &id, out, order);
            }
            Block::Para { sents, .. } | Block::Text { sents, .. } => {
                cur.paras += usize::from(matches!(b, Block::Para { .. }));
                pending = sents_need(sents, &mut cur);
            }
            Block::List { items, .. } => {
                cur.items += items.len();
                for li in items {
                    match &li.inline {
                        Some(ss) => {
                            if sents_need(ss, &mut cur).is_some() {
                                cur.follow += 1;
                            }
                        }
                        None => {
                            let mut sub = BTreeMap::new();
                            let mut so = Vec::new();
                            cover(md, &li.kids, clause, &mut sub, &mut so);
                            if let Some(c) = sub.get(clause) {
                                cur.add(c);
                            }
                        }
                    }
                }
            }
            Block::Table { table, .. } => {
                cur.tables += 1;
                cur.rows += table.rows.len();
                cur.rows_typed += table.rows.iter().filter(|r| !matches!(r.ty, TyExpr::Prose(_))).count();
                cur.desc += table.rows.len();
            }
            Block::Note { .. } => cur.notes += 1,
            Block::Alg { .. } => cur.algs += 1,
            Block::Raw(_) => cur.raw += 1,
            Block::Heading(ls) => cur.raw += ls.len(),
            Block::Blank => {}
        }
        if pending.is_some() {
            cur.follow += 1;
        }
    }
    if !out.contains_key(clause) {
        order.push(clause.to_string());
    }
    out.entry(clause.to_string()).or_default().add(&cur);
}

/// Coverage per clause, in document order.
pub fn coverage(doc: &Doc) -> Vec<(String, Cov)> {
    let mut m = BTreeMap::new();
    let mut order = Vec::new();
    cover(&doc.md, &doc.blocks, "", &mut m, &mut order);
    let mut out: Vec<(String, Cov)> = order.into_iter().filter(|c| !c.is_empty()).map(|c| (c.clone(), m[&c])).collect();
    out.sort_by_key(|(c, _)| doc_pos(&doc.blocks, c));
    out
}

fn doc_pos(bs: &[Block], id: &str) -> usize {
    let mut k = 0;
    fn go(bs: &[Block], id: &str, k: &mut usize) -> bool {
        for b in bs {
            if let Block::Clause { attrs, kids, .. } = b {
                *k += 1;
                if crate::spec::attr(attrs, "id").as_deref() == Some(id) || go(kids, id, k) {
                    return true;
                }
            }
        }
        false
    }
    go(bs, id, &mut k);
    k
}

/// Every parsed sentence's data, by clause.
pub fn dump(doc: &Doc) -> Vec<String> {
    fn go(bs: &[Block], id: &str, out: &mut Vec<String>) {
        for b in bs {
            match b {
                Block::Clause { attrs, kids, .. } => go(kids, &crate::spec::attr(attrs, "id").unwrap_or_default(), out),
                Block::Para { sents, .. } | Block::Text { sents, .. } => out.extend(sents.iter().filter(|s| !matches!(s, Sent::Prose(_))).map(|s| format!("{id}: {s:?}"))),
                Block::List { items, .. } => {
                    for li in items {
                        out.extend(li.inline.iter().flatten().filter(|s| !matches!(s, Sent::Prose(_))).map(|s| format!("{id}: {s:?}")));
                        go(&li.kids, id, out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    go(&doc.blocks, "", &mut out);
    out
}

/// Every prose sentence, by clause: text.
pub fn prose_list(doc: &Doc) -> Vec<String> {
    fn go(bs: &[Block], id: &str, vars: &[String], out: &mut Vec<String>) {
        let sents = |ss: &[Sent], vars: &[String], out: &mut Vec<String>| {
            for s in ss {
                if let Sent::Prose(ps) = s {
                    out.push(format!("    prose {id}: {}", prose_text(vars, ps)));
                }
            }
        };
        for b in bs {
            match b {
                Block::Clause { attrs, vars, kids, .. } => go(kids, &crate::spec::attr(attrs, "id").unwrap_or_default(), vars, out),
                Block::Para { sents: ss, .. } | Block::Text { sents: ss, .. } => sents(ss, vars, out),
                Block::List { items, .. } => {
                    for li in items {
                        if let Some(ss) = &li.inline {
                            sents(ss, vars, out);
                        }
                        go(&li.kids, id, vars, out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    go(&doc.blocks, "", &[], &mut out);
    out
}
