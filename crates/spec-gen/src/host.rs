//! Host and implementation requirements: every sentence with "must" or
//! "shall" outside algorithms, notes, examples and informative annexes, and
//! every item of a list such a sentence introduces, with its clause. Each
//! paragraph is split into sentences exactly; each requirement is parsed by
//! the host templates (categories `H*`) over the step grammar's conditions,
//! expressions and types, converted to `Req`, and printed back.

use crate::ast::{Channel, Cond, Expr, Hole, Id, Part, Stmt, TyExpr};
use crate::conv::{Conv, Vars};
use crate::decls::Decls;
use crate::engine::{Item, Node as PNode, Parser};
use crate::grammar::{Grammar, R};
use crate::spec::{line_of, Spec};
use crate::token::{tokenize, Tok, K};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

/// Tags that end a paragraph (open or close).
const BLOCK: &[&str] = &[
    "p", "li", "ul", "ol", "td", "th", "tr", "table", "thead", "tbody", "emu-table", "figure", "figcaption", "emu-figure", "dl", "dt", "dd",
    "h1", "h2", "h3", "div", "emu-note", "emu-alg", "emu-example", "emu-clause", "emu-annex", "emu-intro", "pre", "br", "img", "style",
    "emu-import", "emu-concrete-method-dfns", "emu-internal-method-dfns", "html", "head", "body", "meta", "link",
];

/// Blocks whose content is not normative prose.
const SKIP: &[&str] = &["emu-note", "emu-alg", "emu-example", "pre", "h1", "h2", "h3", "style", "figure", "emu-figure"];

/// A paragraph: a maximal run of inline content between block tags.
pub struct Para {
    pub clause: Option<usize>,
    /// the end of its byte range in spec.html
    pub end: usize,
    pub line: usize,
    /// the block tag that opens the run
    pub tag: String,
    /// the last `<h2>` before it in its clause (an invariant's method)
    pub heading: Option<String>,
    pub raw: String,
    /// sentence spans in `raw`
    pub sents: Vec<(usize, usize)>,
    /// the paragraph whose list this one is an item of (its lead-in, ending in a colon)
    pub lead: Option<usize>,
    /// in an informative annex
    pub informative: bool,
}

fn tag_name(s: &str) -> (&str, bool) {
    let close = s.starts_with("</");
    let b = if close { 2 } else { 1 };
    let e = s[b..].find(|c: char| !(c.is_ascii_alphanumeric() || c == '-')).map(|e| e + b).unwrap_or(s.len());
    (&s[b..e], close)
}

/// Every paragraph outside the skipped blocks.
pub fn paragraphs(html: &str, sp: &Spec) -> Vec<Para> {
    let mut out = Vec::new();
    let mut skip: Vec<String> = Vec::new();
    let mut run_start = 0;
    let mut run_tag = String::new();
    let mut heading: Option<(usize, String)> = None;
    let mut lists: Vec<Option<usize>> = Vec::new();
    let mut i = 0;
    let emit = |a: usize, b: usize, tag: &str, skipping: bool, heading: &Option<(usize, String)>, lists: &[Option<usize>], out: &mut Vec<Para>| {
        if skipping || html[a..b].trim().is_empty() {
            return;
        }
        let clause = clause_at(sp, a);
        let heading = heading.as_ref().filter(|(c, _)| Some(*c) == clause.map(|c| sp.clauses[c].start)).map(|(_, h)| h.clone());
        out.push(Para { clause, end: b, line: line_of(html, a), tag: tag.to_string(), heading, raw: html[a..b].to_string(), sents: vec![], lead: lists.last().copied().flatten(), informative: false });
    };
    while let Some(off) = html[i..].find('<') {
        let p = i + off;
        if html[p..].starts_with("<!--") {
            let e = html[p..].find("-->").map(|e| p + e + 3).unwrap_or(html.len());
            emit(run_start, p, &run_tag, !skip.is_empty(), &heading, &lists, &mut out);
            run_start = e;
            i = e;
            continue;
        }
        let gt = match html[p..].find('>') {
            Some(g) => p + g + 1,
            None => break,
        };
        let (name, close) = tag_name(&html[p..gt]);
        if !BLOCK.contains(&name) {
            i = p + 1;
            continue;
        }
        emit(run_start, p, &run_tag, !skip.is_empty(), &heading, &lists, &mut out);
        if (name == "ul" || name == "ol") && skip.is_empty() {
            if close {
                lists.pop();
            } else {
                let lead = out.len().checked_sub(1).filter(|&k| {
                    let q: &Para = &out[k];
                    let gap = html[q.end..p].trim();
                    q.raw.trim_end().ends_with(':') && (gap.is_empty() || gap == "</p>")
                });
                lists.push(lead);
            }
        }
        if SKIP.contains(&name) {
            if close {
                if skip.last().map(String::as_str) == Some(name) {
                    skip.pop();
                }
            } else {
                skip.push(name.to_string());
            }
        }
        if name == "h2" && !close {
            if let Some(e) = html[gt..].find("</h2>") {
                if let Some(c) = clause_at(sp, p) {
                    heading = Some((sp.clauses[c].start, crate::text::squash(&html[gt..gt + e])));
                }
            }
        }
        if name == "h1" && !close {
            heading = None;
        }
        run_start = gt;
        run_tag = if close { String::new() } else { name.to_string() };
        i = gt;
    }
    for pa in &mut out {
        pa.sents = sentences(&pa.raw);
        pa.informative = pa.clause.is_some_and(|c| informative(html, sp, c));
    }
    out
}

/// Whether a clause is in an annex not marked normative.
fn informative(html: &str, sp: &Spec, c: usize) -> bool {
    let top = sp.clauses[c].number.split('.').next().unwrap_or("");
    if !top.starts_with(|ch: char| ch.is_ascii_uppercase()) {
        return false;
    }
    let Some(t) = sp.clauses.iter().find(|x| x.number == top) else { return true };
    let open = html[..t.start].rfind('<').map(|i| &html[i..t.start]).unwrap_or("");
    !open.split_whitespace().any(|a| a == "normative" || a == "normative>")
}

fn clause_at(sp: &Spec, pos: usize) -> Option<usize> {
    sp.clauses.iter().enumerate().filter(|(_, c)| c.inst.is_none() && c.start <= pos && pos < c.end).max_by_key(|(_, c)| c.start).map(|(i, _)| i)
}

const ABBREV: &[&str] = &["e.g", "i.e", "etc", "vs", "cf"];

/// Whether a token can open a sentence.
fn opens(t: &Tok) -> bool {
    match t.k {
        K::Word => t.v.starts_with(|c: char| c.is_uppercase()),
        K::Punct => t.v == "“" || t.v == "\"" || t.v == "(",
        K::Num | K::Var | K::Val | K::Field | K::Xref | K::Code | K::Intr | K::Nt | K::Tag | K::Link => true,
        _ => false,
    }
}

/// The sentences of a paragraph, as spans: a sentence ends at `.`, `!` or
/// `?` outside parentheses (or at the `)` closing a parenthesized sentence),
/// followed by white space and a token that opens one; the text between
/// sentences is white space.
pub fn sentences(raw: &str) -> Vec<(usize, usize)> {
    let toks = tokenize(raw);
    let mut out = Vec::new();
    if toks.is_empty() {
        return out;
    }
    let mut start = toks[0].s;
    let mut depth = 0i32;
    let stop = |t: &Tok| t.k == K::Punct && matches!(t.v.as_str(), "." | "!" | "?");
    for k in 0..toks.len() {
        let t = &toks[k];
        let close = t.k == K::Punct && t.v == ")";
        if t.k == K::Punct && t.v == "(" {
            depth += 1;
        }
        if close {
            depth -= 1;
        }
        let end = if close { depth == 0 && k > 0 && stop(&toks[k - 1]) && toks[k - 1].e == t.s } else { stop(t) && depth <= 0 };
        if !end {
            continue;
        }
        let before = &raw[start..t.s];
        if ABBREV.iter().any(|a| before.ends_with(a) && !before[..before.len() - a.len()].ends_with(|c: char| c.is_alphanumeric())) {
            continue;
        }
        match toks.get(k + 1) {
            None => {
                out.push((start, t.e));
                start = raw.len();
            }
            Some(n) if n.s > t.e && opens(n) => {
                out.push((start, t.e));
                start = n.s;
                depth = 0;
            }
            _ => {}
        }
    }
    let last = toks.last().unwrap().e;
    if start < last {
        out.push((start, last));
    }
    out
}

/// Whether a sentence has the word must or shall.
pub fn normative(s: &str) -> bool {
    tokenize(s).iter().any(|t| t.k == K::Word && (t.v == "must" || t.v == "shall"))
}

// ---------------------------------------------------------------- the data

/// The modal of a requirement.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Modal {
    Must,
    MustNot,
    MustNever,
    MustAlso,
    Shall,
    ShallNot,
    /// no modal word: the duty states its verb (`will`, `represents`, `schedules`)
    Indicative,
}

pub const MODALS: &[(Modal, &str)] = &[
    (Modal::Must, "must"),
    (Modal::MustNot, "must not"),
    (Modal::MustNever, "must never"),
    (Modal::MustAlso, "must also"),
    (Modal::Shall, "shall"),
    (Modal::ShallNot, "shall not"),
];

/// How a trailing condition is attached.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Post {
    /// `, unless C`
    CommaUnless,
    /// `unless C`
    Unless,
    /// `if C`
    If,
}

/// What the subject must do or be.
#[derive(Clone, Debug, PartialEq)]
pub enum Duty {
    /// `return T` (a value is a singleton type)
    Return(TyExpr),
    /// `be T`
    Be(TyExpr),
    Phrase(Id, Vec<Hole>),
}

/// A requirement's leading premise.
#[derive(Clone, Debug, PartialEq)]
pub enum Premise {
    /// `If C,` (with `then`)
    If(Cond, bool),
    /// `Each time it is called …` (with a comma): every invocation
    EachTime(Expr, bool),
    /// `Unless C,`
    Unless(Cond),
    /// `When C,`
    When(Cond),
    /// `Otherwise,`: none of the paragraph's earlier premises holds
    Otherwise,
}

/// The operation a requirement constrains.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum HookRef {
    /// the clause's operation
    Alg(usize),
    /// an internal method (§6.1.7.3's `<h2>`)
    Method(Id),
    /// every host hook (§4.2)
    Every,
}

/// `[If C, [then]] S must D [, unless C'] .` (or `:` before a list).
#[derive(Clone, Debug, PartialEq)]
pub struct Must {
    pub premise: Option<Premise>,
    pub subject: Expr,
    pub modal: Modal,
    pub duty: Duty,
    pub post: Option<(Post, Cond)>,
    /// `, unless either`: the exceptions are the list that follows
    pub either: bool,
    /// ends in a colon (introduces a list)
    pub colon: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Req {
    Must(Must),
    /// a list item under a modal lead-in: `[If C,] C'.`
    Holds(Option<Cond>, Cond),
    /// a list item written as an algorithm step
    Step(Stmt),
    /// a hook's default: `The default implementation of H is to return E.` (H by its clause)
    Default(usize, Expr),
    /// a whole-sentence template
    Phrase(Id, Vec<Hole>),
    Prose(Channel, Vec<Part>),
}

/// A requirement sentence: its form, and whether its first letter is a capital.
#[derive(Clone, Debug, PartialEq)]
pub struct Sentence {
    pub cap: bool,
    pub req: Req,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Class {
    /// the core form, its premise a condition the step grammar parses, over the hook
    Cond,
    /// a list item that is an algorithm step
    Step,
    /// structured by host templates
    Template,
    Prose,
}

impl Why {
    pub fn label(self) -> &'static str {
        match self {
            Why::Modal => "modal",
            Why::Item => "item",
            Why::Default => "default",
            Why::Indicative => "indicative",
        }
    }
}

impl Class {
    pub fn label(self) -> &'static str {
        match self {
            Class::Cond => "condition",
            Class::Step => "step",
            Class::Template => "template",
            Class::Prose => "prose",
        }
    }
}

/// Why a sentence is selected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Why {
    /// it says must or shall
    Modal,
    /// an item of a list a modal sentence introduces
    Item,
    /// a hook clause's default implementation
    Default,
    /// an indicative constraint on a hook (`will`, `represents`, `schedules`)
    Indicative,
}

/// A requirement with its place: clause, paragraph and sentence.
pub struct HostReq {
    pub clause: usize,
    /// the operation it constrains
    pub hook: Option<HookRef>,
    pub para: usize,
    pub sent: usize,
    pub why: Why,
    pub vars: Vars,
    pub text: String,
    pub s: Sentence,
    pub class: Class,
    /// why the parse was not converted, if it was not
    pub exception: Option<String>,
    /// a tie left on declaration order in its parse
    pub tie: bool,
    /// its disposition: an index into the overlay's host laws
    pub disp: Option<usize>,
}

pub struct Host {
    pub paras: Vec<Para>,
    pub reqs: Vec<HostReq>,
    pub decls: Decls,
    /// sentences in informative annexes, left out
    pub informative: usize,
    /// each paragraph's index among its clause's paragraphs
    pub idx: Vec<usize>,
    /// the host laws that name no requirement, or that collide
    pub disp_errors: Vec<String>,
}

// ---------------------------------------------------------------- the templates

/// The host templates: categories HR (a requirement sentence), HI (an item
/// under a modal lead-in), HS (a subject), HD (a duty), HC (a condition).
pub const RULES: &[R] = &[
    (
        "HR",
        "req",
        "[ ( if {HC} , [ then ] | each time {HCALL} [ , ] | unless {HC} , ) ] {HS} ( must | must not | must never | must also | shall | shall not ) {HD} [ ( , unless | unless | if ) {HC} ] [ , unless either ] ( . | : )",
        1,
        None,
    ),
    ("HI", "holds", "[ if {HC} , ] {HC} .", 1, None),
    ("HDEF", "default", "the default implementation of $WORD is to return {E} .", 1, None),
    // conditions: the step grammar's, or host atoms
    ("HC", "hc", "{C}", 1, None),
    ("HC", "hc-one", "{HCA}", 1, None),
    ("HC", "hc-and", "{HCA} and {HCA}", 1, None),
    ("HCA", "hca-c", "{CA}", 1, None),
    ("HCA", "hc-subj", "{HSH} {PREDS}", 1, None),
    ("HCA", "target-ext", "[ the ] target is ( non-extensible | extensible )", 1, None),
    ("HCA", "hook-returns", "$FIELD returns {E}", 1, None),
    ("HCA", "observed", "{E} ( was previously | has previously been ) observed as {HPROP} of the target [ ( with value {E} | whose $FIELD attribute is {E} ) ]", 1, None),
    ("HCA", "described", "{E} is described as {HPROP}", 1, None),
    ("HCA", "non-existent", "{E} is ( non-existent | a non-existent own property )", 1, None),
    ("HCA", "attr-may-change", "the $FIELD attribute may change from {E} to {E}", 1, None),
    ("HCA", "same-value", "{E} is [ the ] SameValue as {HV}", 1, None),
    ("HCA", "hook-completes", "{HSH} ( completes | does not complete ) normally with {E}", 1, None),
    ("HCA", "hook-no-detach", "{HSH} does not detach {E}", 1, None),
    ("HPROP", "prop", "( a | an ) [ non-configurable [ , ] ] [ ( non-writable | writable ) ] [ own ] [ ( data or accessor | data | accessor ) ] property", 1, None),
    ("HCA", "is-prop", "{E} is {HPROP}", 1, None),
    ("HCA", "prop-change", "{HPROP} can be changed into {HPROP}", 1, None),
    ("HCA", "attrs-same", "all attributes of {E} are the SameValue as {E} 's attributes", 1, None),
    ("HCA", "closure-returns", "an Abstract Closure returns a Completion Record", 1, None),
    ("HV", "hv-e", "{E}", 1, None),
    ("HV", "observed-value", "the target 's observed $FIELD value", 1, None),
    ("HV", "attr-value", "{E} 's $FIELD attribute", 1, None),
    ("HCALL", "hook-call", "( this operation | it ) is called [ with a specific ( {E} as its argument | {E} , {E} pair as arguments ) ]", 1, None),
    // subjects: an expression, or a host subject
    ("HS", "hs-e", "{E}", 1, Some("hs-h")),
    ("HS", "hs-h", "{HSH}", 1, None),
    ("HSH", "hook-it", "it", 1, None),
    ("HSH", "hook-self", "( this | the ) ( abstract operation | operation )", 1, None),
    ("HSH", "hook-impl", "( an | the ) implementation of $WORD", 1, None),
    ("HSH", "hook-method", "$FIELD [ {ArgsP} ]", 1, None),
    ("HSH", "hook-method-op", "the $FIELD operation", 1, None),
    ("HSH", "hook-result", "the ( return value | returned $WORD )", 1, None),
    ("HSH", "hook-result-elem", "each element of the returned $WORD", 1, None),
    ("HSH", "hook-result-fulfilled", "the returned $WORD , when fulfilled ,", 1, None),
    ("HSH", "hook-calls", "all future calls to $FIELD [ {ArgsP} ] [ on the target ]", 1, None),
    ("HSH", "hook-target", "the target", 1, None),
    ("HSH", "hook-attr", "( the | {E} 's ) $FIELD attribute", 1, None),
    ("HSH", "hook-returned-by", "the value returned by any internal method", 1, None),
    ("HSH", "host-env", "the host environment", 1, None),
    ("HSH", "impl", "( an | the ) implementation", 1, None),
    ("HSH", "binding", "( a | an ) [ uninitialized ] binding [ for {E} ]", 1, None),
    ("HSH", "agents", "all agents within a cluster", 1, None),
    ("HSH", "impl-402", "an ECMAScript implementation that includes the ECMA-402 Internationalization API", 1, None),
    ("HSH", "hosts-not-web", "ECMAScript hosts that are not web browsers", 1, None),
    ("HSH", "op-name", "$CAP", 1, None),
    ("HSH", "this-module", "this module", 1, None),
    ("HSH", "the-method", "the method", 1, None),
    ("HSH", "this-field", "this ( field | property )", 1, None),
    ("HSH", "builtin-fn", "a built-in function object", 1, None),
    ("HSH", "such-method", "such a $FIELD internal method", 1, None),
    ("HSH", "impl-callables", "implementation-defined callable objects", 1, None),
    ("HSH", "that-cr", "that Completion Record", 1, None),
    ("HSH", "math-random", "each $CODE function created for distinct realms", 1, None),
    ("HSH", "these-indices", "these indices", 1, None),
    ("HSH", "nt-following", "the $NT immediately following ( a | an ) $NT", 1, None),
    ("HSH", "hook-two-calls", "any two calls of ( this abstract operation | it ) with the same ( argument | arguments )", 1, None),
    ("HSH", "host-hook", "( a | an ) host hook", 1, None),
    ("HSH", "host-hooks", "all host hooks", 1, None),
    ("HSH", "their-impls", "their implementations", 1, None),
    ("HSH", "jobs", "jobs", 1, None),
    ("HSH", "job-closure", "the Abstract Closure", 1, None),
    ("HSH", "collections", "( maps | set objects | WeakMaps | WeakSets )", 1, None),
    // duties
    ("HD", "hook-return", "return {HT}", 1, None),
    ("HD", "hook-be", "be {HT}", 1, None),
    ("HD", "hook-return-only", "return {HT} and perform no other steps", 1, None),
    ("HD", "hook-return-same-value", "return the SameValue as {E}", 1, None),
    ("HD", "hook-return-whose", "return ( a | an ) {TN} whose $FIELD field is {E}", 1, None),
    ("HD", "hook-be-with-slot", "be ( a | an ) {TN} with ( a | an ) $FIELD internal slot", 1, None),
    ("HD", "hook-have-method", "have ( a | an ) $FIELD internal method", 1, None),
    ("HD", "hook-perform", "perform {E}", 1, None),
    ("HD", "hook-perform-return", "perform and return {E}", 1, None),
    ("HD", "hook-deterministic", "be deterministic with respect to its parameters", 1, None),
    ("HD", "hook-same-result", "return the same result", 1, None),
    ("HD", "hook-same-kind", "return the same kind of Completion Record", 1, None),
    ("HD", "hook-same-list", "return the same List with the same contents in the same order", 1, None),
    ("HD", "hook-no-duplicates", "contain any duplicate entries", 1, None),
    ("HD", "hook-fulfill", "fulfill with {HT}", 1, None),
    ("HD", "hook-completion-either", "be a Completion Record with either", 1, None),
    ("HD", "return-nonext", "return {HT} and the target is now considered non-extensible", 1, None),
    ("HD", "contain-observed", "contain at least the keys of all non-configurable own properties that have previously been observed", 1, None),
    ("HD", "contain-observable", "contain only the keys of all own properties of the target that are observable using $FIELD", 1, None),
    ("HD", "describe-non-existent", "describe {E} as non-existent '(' i ^. ^e ^. $FIELD [ {ArgsP} ] must return {E} ')'", 1, None),
    ("HD", "conform-following", "conform to [ at least ] the following requirements", 1, None),
    ("HD", "conform-in", "conform to the requirements in $XREF [ as well as the following ]", 1, None),
    ("HD", "conform-interface", "conform to the [ async ] ( $CAP | iterator ) interface", 1, None),
    ("HD", "conform-invariants", "conform to the list of invariants specified below", 1, None),
    ("HD", "use-default", "use the default implementation of $WORD", 1, None),
    ("HD", "already-exist", "already exist [ in ( this Environment Record | the DeclarativeRecord | {E} ) ] [ for {E} ]", 1, None),
    ("HD", "agents-field", "have ( the same value | the same values | different values ) for the $FIELD field in their respective Agent Records [ ; similarly for the $FIELD and $FIELD fields ]", 1, None),
    ("HD", "implement-402", "implement this method as specified in ECMA-402", 1, None),
    ("HD", "completed-before", "have completed successfully prior to invoking this method", 1, None),
    ("HD", "cover", "cover ( a | an ) $NT", 1, None),
    ("HD", "hook-modify", "modify $FIELD", 1, None),
    ("HD", "settled", "be already settled", 1, None),
    ("HD", "have-method-def", "have ( a | an ) $FIELD internal method that conforms to the definition in $XREF", 1, None),
    ("HD", "conform-def", "conform to the definition in $XREF", 1, None),
    ("HD", "distinct-sequence", "produce a distinct sequence of values from successive calls", 1, None),
    ("HD", "have-attributes", "have the attributes {E}", 1, None),
    ("HD", "satisfy-invariant", "satisfy the invariant that {C}", 1, None),
    ("HD", "be-nt-or", "be ( a | an ) $NT or $NT", 1, None),
    ("HD", "be-extended", "be extended [ to include $NT or $NT as defined in $XREF ]", 1, None),
    ("HD", "return-pd-whose", "return Property Descriptor whose $FIELD is SameValue as {HV}", 1, None),
    ("HD", "hook-opaque", "treat {E} as an opaque value to be passed through to $WORD", 1, None),
    ("HD", "hook-return-attrs", "return {HT} , each indicating a supported attribute", 1, None),
    (
        "HD",
        "host-perform-module",
        "perform {E} , where {V} is either a normal completion containing the loaded Module Record or a throw completion , either synchronously or asynchronously",
        1,
        None,
    ),
    ("HD", "host-perform-where", "perform {E} , where {V} is {HT} , either synchronously or asynchronously", 1, None),
    ("HD", "jobs-order", "run in the same order as the $WORD invocations that scheduled them", 1, None),
    ("HD", "return-own-errors", "return {HT} , implementing its own handling of errors", 1, None),
    ("HD", "listed-in", "be listed in Annex $XREF", 1, None),
    ("HD", "sublinear", "be implemented using either hash tables or other mechanisms that , on average , provide access times that are sublinear on the number of ( elements | key ^/ ^value pairs ) in the collection", 1, None),
    ("HD", "implement-as-in-402", "implement the $WORD abstract operation as specified in ECMA-402", 1, None),
    // list items under a modal lead-in
    ("HI", "let-at-invocation", "let {V} be {E} at the time $WORD is invoked .", 1, None),
    ("HI", "host-steps", "perform any host-defined ( preparation | cleanup ) steps [ , after which the execution context stack must be empty ] .", 1, None),
    ("HI", "invoke-job", "$NOTREFO Invoke $NOTREFC the Job Abstract Closure .", 1, None),
    ("HI", "one-job", "only one Job may be actively undergoing evaluation at any point in time in an agent .", 1, None),
    // indicative constraints of hooks: `[When C, | Otherwise,] S D.`
    ("HRI", "ind", "[ ( when {HC} , | otherwise , ) ] {HS} {HDI} .", 1, None),
    ("HSH", "hook-result-each", "each value in the returned $WORD", 1, None),
    (
        "HCA",
        "input-transition",
        "the input represents a local time ( occurring more than once because of a negative | skipped because of a positive ) time zone transition '(' e ^. ^g ^. when daylight saving time ( ends | begins ) or the time zone offset is ( decreased | increased ) due to a time zone rule change ')'",
        1,
        None,
    ),
    ("HDI", "will-have", "will have ( more than one element | one element ) [ and will be sorted by ascending numerical value ]", 1, None),
    ("HDI", "will-be-empty", "will be empty", 1, None),
    (
        "HDI",
        "represents-epoch-ns",
        "represents an epoch nanoseconds count that corresponds to the given ISO $NUM=8601 calendar date and wall-clock time in the named time zone identified by {E}",
        1,
        None,
    ),
    (
        "HDI",
        "represents-offset-ns",
        "represents the offset from UTC , in nanoseconds , of the named time zone identified by {E} , at the instant corresponding with the epoch nanoseconds count {E}",
        1,
        None,
    ),
    (
        "HDI",
        "returns-time-zone",
        "returns {HT} representing the host environment 's current time zone , which is either {HT} representing a UTC offset for which $CAP returns {E} , or a primary time zone identifier",
        1,
        None,
    ),
    ("HDI", "schedules", "schedules {E} to be performed at some future time , if possible", 1, None),
    // whole sentences
    (
        "HR",
        "subclass",
        "subclass constructors that intend to inherit the specified ( $CAP | $VAR | $CODE ) behaviour must include a $CODE=super call to the ( $CAP | $VAR | $CODE ) constructor to create and initialize ( the subclass instance | subclass instances | a subclass instance ) with {HSLOTS} .",
        1,
        None,
    ),
    (
        "HR",
        "subclass-exotic",
        "subclass constructors that intend to inherit the exotic $CAP behaviour must include a $CODE=super call to the $CAP constructor to initialize subclass instances that are $CAP exotic objects .",
        1,
        None,
    ),
    (
        "HR",
        "job-steps",
        "if {HC} , each time {E} is invoked the implementation must perform implementation-defined steps such that ( execution is prepared to evaluate ECMAScript code | {E} is the active script or module ) at the time of {E} 's invocation .",
        1,
        None,
    ),
    (
        "HR",
        "job-when",
        "at some future point in time , when there is no running context in the agent for which the job is scheduled and that agent 's execution context stack is empty , the implementation must :",
        1,
        None,
    ),
    ("HR", "for-any", "for any $CAP , {HS} must {HD} .", 1, None),
    ("HR", "job-completion", "once evaluation of a Job starts , it must run to completion before evaluation of any other Job starts in an agent .", 1, None),
    (
        "HR",
        "tz-402",
        "time zone aware implementations , including all implementations that implement the ECMA-402 Internationalization API , must implement the $WORD abstract operation as specified in ECMA-402 .",
        1,
        None,
    ),
    ("HSLOTS", "slot", "( a | an ) $FIELD internal slot", 1, None),
    ("HSLOTS", "state-for", "the internal state necessary to support the built-in methods of ( $CODE [ and $CODE ] | $INTR ^$CODE )", 1, None),
    ("HSLOTS", "slots", "the necessary internal slots", 1, None),
    ("HSLOTS", "slots-for", "the internal slots necessary for built-in [ async ] ( $CAP | function ) behaviour", 1, None),
    (
        "HR",
        "params-402",
        "[ the ( meaning | meanings ) of the optional [ second and third ] parameters to this method are defined in ECMA-402 ; ] implementations that do not include ECMA-402 support must not ( use those parameter positions for ( anything else | other purposes ) | assign any other interpretation to those parameter positions ) .",
        1,
        None,
    ),
];

// ---------------------------------------------------------------- building

/// The operation a paragraph's requirements constrain, and its parameters.
fn hook(sp: &Spec, paras: &[Para], pi: usize, d: &mut Decls) -> (Option<HookRef>, Vec<String>) {
    let pa = &paras[pi];
    let Some(c) = pa.clause else { return (None, vec![]) };
    let host_hooks = |q: &Para| ["All host hooks ", "A host hook "].iter().any(|h| q.raw.trim_start().starts_with(h));
    if host_hooks(pa) || pa.lead.is_some_and(|l| host_hooks(&paras[l])) {
        return (Some(HookRef::Every), vec![]);
    }
    let cl = &sp.clauses[c];
    if let Some(h) = &pa.heading {
        if let Some(rest) = h.strip_prefix("[[") {
            let name = rest.split("]]").next().unwrap_or("");
            let vars = tokenize(h).iter().filter(|t| t.k == K::Var).map(|t| t.v.clone()).collect();
            return (Some(HookRef::Method(d.fields.intern(name))), vars);
        }
    }
    if cl.ty.is_none() {
        return (None, vec![]);
    }
    let hd = crate::header::parse(cl);
    let mut vars: Vec<String> = hd.recv.iter().map(|(r, _)| r.clone()).collect();
    vars.extend(hd.params.iter().map(|p| p.name.clone()));
    (Some(HookRef::Alg(c)), vars)
}

/// Whether every must or shall of a sentence is outside its main clause: in
/// parentheses or quotes, after `that`, `which` or `programmers`, or in an
/// `if` or `when` clause before its comma. Such a sentence is not a requirement.
fn subordinate(text: &str) -> bool {
    if text.starts_with("In the circumstance that ") {
        return true;
    }
    let toks = tokenize(text);
    let (mut paren, mut quote) = (0i32, 0i32);
    let mut cond_open = false;
    let mut any = false;
    for (k, t) in toks.iter().enumerate() {
        match (t.k, t.v.as_str()) {
            (K::Punct, "(") => paren += 1,
            (K::Punct, ")") => paren -= 1,
            (K::Punct, "“") => quote += 1,
            (K::Punct, "”") => quote -= 1,
            (K::Punct, ",") => cond_open = false,
            (K::Word, "when" | "When") => cond_open = true,
            // an if clause that a comma closes after the modal
            (K::Word, "if" | "If") => cond_open = toks[k..].iter().any(|t| t.k == K::Punct && t.v == ",") && !toks[k..].iter().take_while(|t| t.v != ",").all(|t| t.v != "must" && t.v != "shall"),
            (K::Word, "must" | "shall") => {
                any = true;
                let prev = k.checked_sub(1).map(|j| toks[j].v.as_str()).unwrap_or("");
                let sub = paren > 0 || quote > 0 || cond_open || matches!(prev, "that" | "which" | "programmers" | "Programmers");
                if !sub {
                    return false;
                }
            }
            _ => {}
        }
    }
    any
}

/// Channel (c)'s kind for a requirement sentence kept as prose.
fn prose_kind(pa: &Para, si: usize, text: &str, governed: bool) -> &'static str {
    if subordinate(text) {
        "not a requirement"
    } else if si == 0 && pa.tag != "li" && !governed && text.starts_with(|c: char| c.is_lowercase()) {
        "sentence broken by a nested list"
    } else {
        "requirement without a host template"
    }
}

/// The tokens of a sentence for parsing: its first word lower-cased when
/// only its first letter is a capital (and whether it was).
fn sentence_toks(text: &str) -> (Vec<Tok>, bool) {
    let mut toks = tokenize(text);
    let mut cap = false;
    if let Some(t) = toks.first_mut() {
        let mut cs = t.v.chars();
        if t.k == K::Word && cs.next().is_some_and(|c| c.is_ascii_uppercase()) && !cs.any(|c| c.is_uppercase()) {
            t.v = t.v.to_lowercase();
            cap = true;
        }
    }
    (toks, cap)
}

fn child(it: &Item) -> Option<&Rc<PNode>> {
    match it {
        Item::N(n, _) => Some(n),
        _ => None,
    }
}

/// Whether a parse is a hook condition: every subject and duty a hook form,
/// and no phrase rows outside the step grammar's own.
fn hook_form(g: &Grammar, n: &PNode) -> bool {
    let mut ok = matches!(n.name, "req" | "holds" | "default");
    crate::engine::visit(n, &mut |x| {
        let core = matches!(x.name, "req" | "holds" | "default" | "hc" | "hc-one" | "hc-and" | "hca-c" | "hc-subj" | "hs-e" | "hs-h") || x.name.starts_with("hook-");
        ok &= core || !is_host_rule(g, x);
    });
    ok
}

/// The host template categories.
const CATS: &[&str] = &["HR", "HRI", "HDI", "HI", "HDEF", "HC", "HCA", "HPROP", "HV", "HCALL", "HS", "HSH", "HD", "HSLOTS"];

/// Whether a node is made by a host template.
fn is_host_rule(g: &Grammar, x: &PNode) -> bool {
    matches!(x.rid, crate::engine::Rid::R(i) if CATS.contains(&g.rules[i].cat))
}

impl<'a, 'b> Conv<'a, 'b> {
    /// A requirement sentence's tree (category HR or HI) as a requirement.
    fn req(&mut self, n: &PNode) -> Result<Req, String> {
        let it = &n.items;
        match n.name {
            "req" => {
                let premise = match &it[0] {
                    Item::O(Some(v), _) => match &v[0] {
                        Item::A(0, w, _) => Some(Premise::If(self.cond(child(&w[1]).unwrap())?, matches!(w[3], Item::O(Some(_), _)))),
                        Item::A(1, w, _) => Some(Premise::EachTime(self.expr(child(&w[2]).unwrap())?, matches!(w[3], Item::O(Some(_), _)))),
                        Item::A(_, w, _) => Some(Premise::Unless(self.cond(child(&w[1]).unwrap())?)),
                        _ => unreachable!(),
                    },
                    _ => None,
                };
                let subject = self.expr(child(&it[1]).unwrap())?;
                let Item::A(k, _, _) = it[2] else { unreachable!() };
                let modal = MODALS[k].0;
                let d = child(&it[3]).unwrap();
                let duty = match d.name {
                    "hook-return" => Duty::Return(self.ht(child(&d.items[1]).unwrap())?),
                    "hook-be" => Duty::Be(self.ht(child(&d.items[1]).unwrap())?),
                    _ => {
                        let (p, h) = self.phrase(d)?;
                        Duty::Phrase(p, h)
                    }
                };
                let post = match &it[4] {
                    Item::O(Some(v), _) => {
                        let Item::A(k, _, _) = v[0] else { unreachable!() };
                        let f = [Post::CommaUnless, Post::Unless, Post::If][k];
                        Some((f, self.cond(child(&v[1]).unwrap())?))
                    }
                    _ => None,
                };
                let either = matches!(it[5], Item::O(Some(_), _));
                let Item::A(end, _, _) = it[6] else { unreachable!() };
                Ok(Req::Must(Must { premise, subject, modal, duty, post, either, colon: end == 1 }))
            }
            "ind" => {
                let premise = match &it[0] {
                    Item::O(Some(v), _) => match &v[0] {
                        Item::A(0, w, _) => Some(Premise::When(self.cond(child(&w[1]).unwrap())?)),
                        _ => Some(Premise::Otherwise),
                    },
                    _ => None,
                };
                let subject = self.expr(child(&it[1]).unwrap())?;
                let (p, h) = self.phrase(child(&it[2]).unwrap())?;
                Ok(Req::Must(Must { premise, subject, modal: Modal::Indicative, duty: Duty::Phrase(p, h), post: None, either: false, colon: false }))
            }
            "default" => {
                let Item::T(i, _) = it[4] else { unreachable!() };
                let name = &self.toks[i].v;
                let c = *self.env.ops.get(name).ok_or_else(|| format!("no operation {name}"))?;
                Ok(Req::Default(c, self.expr(child(&it[8]).unwrap())?))
            }
            "holds" => {
                let p = match &it[0] {
                    Item::O(Some(v), _) => Some(self.cond(child(&v[1]).unwrap())?),
                    _ => None,
                };
                Ok(Req::Holds(p, self.cond(child(&it[1]).unwrap())?))
            }
            _ => {
                let (p, h) = self.phrase(n)?;
                Ok(Req::Phrase(p, h))
            }
        }
    }
}

/// Every requirement, parsed, classed and converted, over fresh declarations.
pub fn build(html: &str, sp: &Spec, g: &Grammar) -> Host {
    let (d, env) = crate::data::base(html, sp, g);
    build_on(html, sp, g, d, &env)
}

/// Every requirement, parsed, classed and converted, interned into `d`.
pub fn build_on(html: &str, sp: &Spec, g: &Grammar, mut d: Decls, env: &crate::conv::Env) -> Host {
    let no_anchors = crate::conv::Anchors::new();
    let paras = paragraphs(html, sp);
    let rows = HashMap::new();
    let mut strict = Parser::new(g, 99, false);
    let mut reqs = Vec::new();
    let mut informative = 0;
    let modal_lead = |l: usize| paras[l].sents.last().is_some_and(|&(a, b)| normative(&paras[l].raw[a..b]));
    let is_hook = |c: usize| matches!(sp.clauses[c].ty.as_deref(), Some("host-defined abstract operation" | "implementation-defined abstract operation"));
    // implementation-defined operations that state their constraints without must or shall
    let mut quiet: std::collections::HashSet<usize> =
        (0..sp.clauses.len()).filter(|&c| sp.clauses[c].ty.as_deref() == Some("implementation-defined abstract operation")).collect();
    for pa in &paras {
        if pa.sents.iter().any(|&(a, b)| normative(&pa.raw[a..b])) {
            pa.clause.map(|c| quiet.remove(&c));
        }
    }
    for (pi, pa) in paras.iter().enumerate() {
        let governed = pa.tag == "li" && pa.lead.is_some_and(modal_lead);
        let Some(clause) = pa.clause else { continue };
        let hook_clause = is_hook(clause);
        let (hk, params) = hook(sp, &paras, pi, &mut d);
        let first = reqs.len();
        let mut pvars = Vars::default();
        for p in &params {
            pvars.slot(p);
        }
        for (si, &(a, b)) in pa.sents.iter().enumerate() {
            let text = &pa.raw[a..b];
            let why = if normative(text) {
                Why::Modal
            } else if governed {
                Why::Item
            } else if hook_clause && text.starts_with("The default implementation of ") && text.contains(" is to return ") {
                Why::Default
            } else if (quiet.contains(&clause) && matches!(pa.tag.as_str(), "p" | "dd") && !text.ends_with(':'))
                || (hook_clause && text.starts_with("An implementation of "))
            {
                Why::Indicative
            } else {
                continue;
            };
            if pa.informative {
                informative += 1;
                continue;
            }
            let vars = std::mem::take(&mut pvars);
            let (low, lowered) = sentence_toks(text);
            let orig = tokenize(text);
            let not_req = why == Why::Modal && subordinate(text);
            let parse = |p: &mut Parser, toks: &[Tok]| match why {
                _ if not_req => None,
                Why::Default => p.parse(toks, "HDEF"),
                Why::Indicative => p.parse(toks, "HRI"),
                _ => p.parse(toks, "HR").or_else(|| if governed { p.parse(toks, "HI") } else { None }),
            };
            let (tree, toks, cap) = match parse(&mut strict, &low) {
                Some(t) => (Some(t), low, lowered),
                None if lowered => (parse(&mut strict, &orig), orig.clone(), false),
                None => (None, low, false),
            };
            let mut cv = Conv {
                open: Vec::new(),
                rhs: Default::default(),
            lhs: Default::default(),
            narrow: Vec::new(),
            symbols: false,
                channel: crate::ast::Channel::Pending,
                clause: sp.clauses[clause].id.clone(),
                anchors: &no_anchors,
                stops: None,
                readings: Vec::new(),
                g,
                d: &mut d,
                env,
                vars,
                rows: &rows,
                toks: toks.clone(),
                text: text.to_string(),
                unresolved: vec![],
                exceptions: vec![],
                closures: vec![],
                base: 0,
            };
            let mut class = Class::Prose;
            let mut req = Err(String::new());
            let mut tie = false;
            if let Some(t) = tree {
                class = if hk.is_some() && hook_form(g, &t) { Class::Cond } else { Class::Template };
                tie = crate::classify::has_tie(&t);
                req = cv.req(&t);
            } else if governed {
                if let Some(t) = strict.parse(&orig, "Step") {
                    cv.toks = orig;
                    class = Class::Step;
                    tie = crate::classify::has_tie(&t);
                    req = cv.stmt(&t, &[]).map(Req::Step);
                }
            }
            let req = req.and_then(|r| {
                let s = Sentence { cap: cap && class != Class::Step, req: r };
                let out = crate::print::requirement(cv.d, &cv.vars.names, &s);
                if out == text { Ok(s) } else { Err(format!("printed as {out}")) }
            });
            let (s, exception) = match req {
                Ok(s) => (s, None),
                Err(e) => {
                    cv.toks = tokenize(text);
                    let parts = cv.prose(0, cv.toks.len());
                    class = Class::Prose;
                    let ch = if e.is_empty() {
                        Channel::Annotated(cv.d.notes.intern(prose_kind(pa, si, text, governed)), None)
                    } else {
                        Channel::Upstream(cv.d.reasons.intern("a requirement parsed but printed otherwise: its spacing is irregular"), None)
                    };
                    (Sentence { cap: false, req: Req::Prose(ch, parts) }, if e.is_empty() { None } else { Some(e) })
                }
            };
            pvars = cv.vars;
            reqs.push(HostReq { clause, hook: hk, para: pi, sent: si, why, vars: Vars::default(), text: text.to_string(), s, class, exception, tie, disp: None });
        }
        for r in reqs[first..].iter_mut() {
            r.vars = pvars.clone();
        }
    }
    let idx = para_idx(&paras);
    let disp_errors = dispose(&mut reqs, &idx, sp, &g.overlay.host_laws);
    Host { paras, reqs, decls: d, informative, idx, disp_errors }
}

/// Each paragraph's index among the paragraphs of its clause.
pub fn para_idx(paras: &[Para]) -> Vec<usize> {
    let mut seen: HashMap<usize, usize> = HashMap::new();
    paras
        .iter()
        .map(|pa| {
            let k = seen.entry(pa.clause.unwrap_or(usize::MAX)).or_default();
            *k += 1;
            *k - 1
        })
        .collect()
}

/// Gives each requirement the most specific host law covering it (sentence, then paragraph,
/// then clause); the errors: a law whose place is unknown or holds no requirement, and a
/// requirement two laws cover at the same place.
pub fn dispose(reqs: &mut [HostReq], idx: &[usize], sp: &Spec, laws: &[crate::overlay::HostLaw]) -> Vec<String> {
    let by_id: HashMap<&str, usize> = sp.clauses.iter().enumerate().map(|(i, c)| (c.id.as_str(), i)).collect();
    let mut bad = Vec::new();
    let mut at: Vec<Option<(usize, usize)>> = vec![None; reqs.len()];
    for (li, l) in laws.iter().enumerate() {
        let place = format!("{}{}{} ({})", l.clause, l.para.map_or(String::new(), |p| format!(" ¶{p}")), l.sent.map_or(String::new(), |s| format!(".{s}")), l.file);
        let Some(&c) = by_id.get(l.clause.as_str()) else {
            bad.push(format!("host law {place}: no such clause"));
            continue;
        };
        let rank = l.para.is_some() as usize + l.sent.is_some() as usize;
        let mut any = false;
        for (ri, r) in reqs.iter().enumerate() {
            if r.clause != c || l.para.is_some_and(|p| p != idx[r.para]) || l.sent.is_some_and(|s| s != r.sent) {
                continue;
            }
            any = true;
            match at[ri] {
                Some((_, k)) if k == rank => bad.push(format!("host law {place}: another law covers \"{}\" at the same place", r.text)),
                Some((_, k)) if k > rank => {}
                _ => at[ri] = Some((li, rank)),
            }
        }
        if !any {
            bad.push(format!("host law {place}: no requirement sentence there"));
        }
    }
    for (r, a) in reqs.iter_mut().zip(at) {
        r.disp = a.map(|x| x.0);
    }
    bad
}

/// Every requirement printed from its data, and every paragraph holding
/// one printed from its sentences: the mismatches. Every paragraph's
/// sentences are separated by white space only.
pub fn roundtrip(h: &Host) -> Vec<String> {
    let mut bad = h.disp_errors.clone();
    for pa in &h.paras {
        let mut at = 0;
        for &(a, b) in &pa.sents {
            if !pa.raw[at..a].chars().all(char::is_whitespace) {
                bad.push(format!("text between sentences at spec.html:{}: {:?}", pa.line, &pa.raw[at..a]));
            }
            at = b;
        }
        if !pa.raw[at..].chars().all(char::is_whitespace) {
            bad.push(format!("text after the last sentence at spec.html:{}", pa.line));
        }
    }
    let mut printed: HashMap<(usize, usize), String> = HashMap::new();
    for r in &h.reqs {
        let out = crate::print::requirement(&h.decls, &r.vars.names, &r.s);
        if out != r.text {
            bad.push(format!("requirement differs at spec.html:{}:\n  src: {}\n  out: {}", h.paras[r.para].line, r.text, out));
        }
        printed.insert((r.para, r.sent), out);
    }
    let mut seen = std::collections::BTreeSet::new();
    for r in &h.reqs {
        if !seen.insert(r.para) {
            continue;
        }
        let pa = &h.paras[r.para];
        let mut out = String::new();
        let mut at = 0;
        for (si, &(a, b)) in pa.sents.iter().enumerate() {
            let gap = &pa.raw[at..a];
            if !gap.chars().all(char::is_whitespace) {
                bad.push(format!("text between sentences at spec.html:{}: {gap:?}", pa.line));
            }
            out.push_str(gap);
            out.push_str(printed.get(&(r.para, si)).map(String::as_str).unwrap_or(&pa.raw[a..b]));
            at = b;
        }
        out.push_str(&pa.raw[at..]);
        if out != pa.raw {
            bad.push(format!("paragraph differs at spec.html:{}", pa.line));
        }
    }
    bad
}

/// Counts by class, by clause, and the hooks.
pub fn report(h: &Host, sp: &Spec, g_laws: &[crate::overlay::HostLaw], verbose: bool) {
    let n = h.reqs.len();
    let count = |w: Why| h.reqs.iter().filter(|r| r.why == w).count();
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for r in &h.reqs {
        match &r.s.req {
            Req::Prose(Channel::Annotated(k, _), _) => *kinds.entry(format!("(c) {}", h.decls.notes.name(*k))).or_default() += 1,
            Req::Prose(Channel::Upstream(k, _), _) => *kinds.entry(format!("(a) {}", h.decls.reasons.name(*k))).or_default() += 1,
            Req::Prose(..) => *kinds.entry("pending".to_string()).or_default() += 1,
            _ => {}
        }
    }
    let clauses: std::collections::BTreeSet<usize> = h.reqs.iter().map(|r| r.clause).collect();
    let mclauses: std::collections::BTreeSet<usize> = h.reqs.iter().filter(|r| r.why == Why::Modal).map(|r| r.clause).collect();
    println!(
        "requirements {n} in {} clauses: {} modal sentences (must, shall) in {} clauses, {} list items under a modal lead-in, {} hook defaults, {} indicative hook constraints; {} more in informative annexes left out",
        clauses.len(),
        count(Why::Modal),
        mclauses.len(),
        count(Why::Item),
        count(Why::Default),
        count(Why::Indicative),
        h.informative
    );
    println!("prose by channel: {}", kinds.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", "));
    let mut by: BTreeMap<Class, BTreeMap<Why, usize>> = BTreeMap::new();
    for r in &h.reqs {
        *by.entry(r.class).or_default().entry(r.why).or_default() += 1;
    }
    for (c, m) in &by {
        let t: usize = m.values().sum();
        let parts: Vec<String> = m.iter().map(|(w, k)| format!("{k} {}", w.label())).collect();
        println!("  {}: {t} ({})", c.label(), parts.join(", "));
    }
    let mut disp: BTreeMap<&str, usize> = BTreeMap::new();
    for r in &h.reqs {
        *disp.entry(r.disp.map_or("none", |l| g_laws[l].class.label())).or_default() += 1;
    }
    println!("dispositions: {}", disp.iter().map(|(k, v)| format!("{k} {v}")).collect::<Vec<_>>().join(", "));
    for e in &h.disp_errors {
        println!("    {e}");
    }
    println!("phrase rows: {}; parses with a tie left on declaration order: {}", h.decls.phrases.len(), h.reqs.iter().filter(|r| r.tie).count());
    for r in h.reqs.iter().filter(|r| r.tie) {
        println!("    tie: {}", r.text);
    }
    let exc = h.reqs.iter().filter(|r| r.exception.is_some()).count();
    println!("parsed but without a data shape (kept as prose): {exc}");
    for r in h.reqs.iter().filter(|r| r.exception.is_some()) {
        println!("    {}: {}", r.exception.as_deref().unwrap_or(""), r.text);
    }
    println!("hooks (host-defined and implementation-defined operations):");
    for (c, cl) in sp.clauses.iter().enumerate() {
        if !matches!(cl.ty.as_deref(), Some("host-defined abstract operation" | "implementation-defined abstract operation")) {
            continue;
        }
        let mut m: BTreeMap<Class, usize> = BTreeMap::new();
        for r in h.reqs.iter().filter(|r| r.clause == c) {
            *m.entry(r.class).or_default() += 1;
        }
        let k = if cl.ty.as_deref() == Some("host-defined abstract operation") { "host" } else { "impl" };
        println!("  {k} §{} {}: {}", cl.number, cl.op().unwrap_or_default(), counts(&m));
    }
    println!("by clause:");
    for &c in &clauses {
        let cl = &sp.clauses[c];
        let mut m: BTreeMap<Class, usize> = BTreeMap::new();
        for r in h.reqs.iter().filter(|r| r.clause == c) {
            *m.entry(r.class).or_default() += 1;
        }
        println!("  §{} {} [{}]: {}", cl.number, cl.id, cl.ty.as_deref().unwrap_or("-"), counts(&m));
        if verbose {
            for r in h.reqs.iter().filter(|r| r.clause == c) {
                let hook = match r.hook {
                    Some(HookRef::Alg(c)) => format!(", {}", h.decls.ops[c]),
                    Some(HookRef::Method(m)) => format!(", [[{}]]", h.decls.fields.name(m)),
                    Some(HookRef::Every) => ", every host hook".to_string(),
                    None => String::new(),
                };
                let kind = match &r.s.req {
                    Req::Prose(Channel::Annotated(k, _), _) => format!(" [{}]", h.decls.notes.name(*k)),
                    Req::Prose(Channel::Upstream(k, _), _) => format!(" [{}]", h.decls.reasons.name(*k)),
                    _ => String::new(),
                };
                let disp = r.disp.map_or(String::new(), |l| format!(" <{}>", g_laws[l].class.label()));
                println!("      ¶{}.{} {} ({}{hook}){kind}{disp} {}", h.idx[r.para], r.sent, r.class.label(), r.why.label(), r.text);
            }
        }
    }
}

fn counts(m: &BTreeMap<Class, usize>) -> String {
    let t: usize = m.values().sum();
    let parts: Vec<String> = m.iter().map(|(c, k)| format!("{} {k}", c.label())).collect();
    format!("{t} ({})", parts.join(", "))
}

#[cfg(test)]
mod tests {
    use super::sentences;

    fn split(t: &str) -> Vec<&str> {
        sentences(t).into_iter().map(|(a, b)| &t[a..b]).collect()
    }

    #[test]
    fn sentence_ends() {
        assert_eq!(split("A must b. (See Annex <emu-xref href=\"#x\"></emu-xref>.) If c, d must e."), vec!["A must b.", "(See Annex <emu-xref href=\"#x\"></emu-xref>.)", "If c, d must e."]);
        assert_eq!(split("It must (i.e. always) hold. Then *x.y* is 1.5."), vec!["It must (i.e. always) hold.", "Then *x.y* is 1.5."]);
        assert_eq!(split("Use e.g. Foo here.\n  Next one"), vec!["Use e.g. Foo here.", "Next one"]);
        assert_eq!(split("\n  Calls `Math.exp`. done.\n"), vec!["Calls `Math.exp`. done."]);
    }
}
