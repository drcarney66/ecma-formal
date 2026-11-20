//! The overlay (spec/formal/*.emu): declared primitives (`<emu-primitive>`)
//! and phrases (`<emu-phrase>`), each phrase a pattern in the steps' own
//! wording whose variables are holes, and a meaning: a primitive applied to
//! the pattern's variables, enum values, or (for a predicate) its subject; or
//! an algorithm of the overlay (`<emu-alg>`) whose parameters are the pattern's
//! variables, then the subject, typed by `<emu-params>`.

use crate::engine::El;
use crate::token::{canon, join, tokenize, Part, Tok, K};

pub struct Prim {
    pub id: String,
    pub name: String,
    pub signature: String,
    pub meaning: String,
}

/// An argument of a phrase's meaning.
#[derive(Clone, Debug, PartialEq)]
pub enum Arg {
    Var(String),
    Enum(String),
    /// `[[F]]`: a field or internal slot name
    Field(String),
}

pub struct Phrase {
    pub id: String,
    /// statement, expression, condition, predicate or type
    pub kind: String,
    /// a predicate's or a type's subject variable (the value tested)
    pub subject: Option<String>,
    /// a type's category: that of the type rule it claims (T, HT or HT1)
    pub tcat: Option<&'static str>,
    pub prim: String,
    pub args: Vec<Arg>,
    pub neg: bool,
    /// the phrase's meaning as an algorithm, in place of `prim`
    pub alg: Option<PhraseAlg>,
    /// the built-in rule whose meaning this is, in place of a rule of its own
    pub rule: Option<String>,
    /// the phrase's meaning holds for every alternative of the rule's word choices; the pattern is one of them
    pub all_alternatives: bool,
    /// a literal of the phrase's meaning spells out what the spec states in prose (`literals="spelled"`)
    pub spelled: bool,
    pub pattern: String,
    pub file: String,
}

/// A phrase meaning written as steps: its parameters (name, type) and its `<emu-alg>`.
pub struct PhraseAlg {
    pub params: Vec<(String, String)>,
    pub raw: String,
    pub base: usize,
    pub close: usize,
    pub steps: Vec<crate::spec::Step>,
}

/// A data sort (`<emu-sort>`): its supersort, whether its values are the Records of
/// its kind, its test on a value _v_ (a primitive, an operation, or steps), if any, and its
/// context (`context="ph-…"`): the predicate phrase over the context's variable that refines
/// the test where that variable is in scope.
pub struct Sort {
    pub name: String,
    pub sup: Option<String>,
    pub record: bool,
    pub test: SortTest,
    pub clause: String,
    pub context: Option<String>,
    /// `type="…"`: the type phrase its values are held as
    pub ty: Option<String>,
}

/// `<emu-fields of="S" clause="…" [slots]>`: fields or internal slots declared only in prose, a
/// `[[F]]: type phrase` per line; `of` a sort, or a schema name.
pub struct Fields {
    pub of: String,
    pub slots: bool,
    pub rows: Vec<(String, String)>,
}

/// `<emu-guard op="Op" type="…">`: the operation returns *true* only when its first argument is of the type.
pub struct Guard {
    pub op: String,
    pub ty: String,
}

pub enum SortTest {
    None,
    /// `test="[not ]Prim(_v_, …)"`
    Prim(String, Vec<Arg>, bool),
    /// `alg="aoid"`: the operation applied to _v_
    Op(String),
    /// an `<emu-alg>` over _v_
    Steps(PhraseAlg),
}

/// The steps of one or more readings (`<emu-alg reading="…">`, space-separated where the
/// readings agree), in place of the anchored step.
pub struct Alt {
    pub reading: String,
    pub raw: String,
    pub base: usize,
    pub close: usize,
    pub steps: Vec<crate::spec::Step>,
}

impl Alt {
    /// Its readings, in the attribute's order.
    pub fn readings(&self) -> impl Iterator<Item = &str> {
        self.reading.split(' ')
    }

    /// Its readings as one id part (`test262+proposed`).
    pub fn key(&self) -> String {
        self.reading.replace(' ', "+")
    }
}

/// An `<emu-reading>`: the step it replaces (clause id, step path, SHA-256 of the
/// step's text as spec.html has it) and the readings' steps.
pub struct Anchor {
    pub clause: String,
    pub step: String,
    pub hash: String,
    pub alts: Vec<Alt>,
    /// the further steps the readings replace (step path, hash): their steps come first at
    /// `step`, and return on every path
    pub also: Vec<(String, String)>,
}

/// An operation of the overlay (`<emu-clause type="abstract operation">`, or `type="built-in
/// function"` with `behaviour-of`: the clause of the object, or of the prose-only function, whose
/// behaviour it is): its clause
/// id, type, `<h1>` and header `<dl>`, and its steps.
pub struct Op {
    pub id: String,
    pub ty: String,
    pub behaviour_of: Option<String>,
    pub h1: String,
    pub dl: String,
    pub alg: PhraseAlg,
    pub file: String,
}

/// An SDO row the pinned text lacks (`<emu-reading id=… clause=… grammar=…>`): its id, the
/// SDO's clause, the row's grammar key and the clause it resolves in (`grammar-clause=`, else the
/// SDO's), its steps, and the erratum it is the `test262 proposed` reading of (inside an
/// `<emu-erratum>`: its literal reading has no row).
pub struct RowReading {
    pub id: String,
    pub clause: String,
    pub grammar: String,
    pub grammar_clause: String,
    pub alg: PhraseAlg,
    pub file: String,
    pub erratum: Option<String>,
}

/// An `<emu-erratum>`: a defect of the pinned text (or a proposed normative change, `kind="proposal"`),
/// today's resolution, its readings, and where its literal text stops a run (`stops=`: required on a
/// `literal` one, never on a `proposed` one, optional on another).
pub struct Erratum {
    pub id: String,
    pub name: String,
    pub resolution: String,
    /// `defect` (a defect of the text, the default) or `proposal` (a proposed normative change)
    pub kind: String,
    /// where its readings are switched: `spec` (the specification layer, the default), `parser` (only the
    /// engine's parser), `none` (one reading only)
    pub switch: String,
    pub readings: Vec<Anchor>,
    pub rules: Vec<RuleAnchor>,
    pub rule_readings: Vec<String>,
    pub stops: Vec<ErratumStop>,
    /// whether it has `stops=`
    pub stops_given: bool,
    /// the equation rows it says name a production the grammar does not have (`<emu-orphan-row>`)
    pub orphans: Vec<OrphanRow>,
}

/// An `<emu-orphan-row clause=… grammar=…>`: an equation row of the clause whose grammar key names no
/// production of the grammar. The row is kept with no production, so it is never applied.
#[derive(Clone, Debug)]
pub struct OrphanRow {
    pub clause: String,
    pub grammar: String,
}

/// A site where an erratum's literal text stops a run (`stops="<sec-id>@<path>[<caller>] …"`): an
/// Assert, a `!` or a step with no result, at step `path` of the clause's algorithm (`-`: outside any
/// step: the job loop's check of §9.5 for `sec-jobs`, or a clause with no algorithm), only under the innermost caller `caller` if named.
#[derive(Clone, Debug, PartialEq)]
pub struct ErratumStop {
    pub clause: String,
    pub path: String,
    pub caller: Option<String>,
}

impl ErratumStop {
    /// As written in `stops=`.
    pub fn text(&self) -> String {
        match &self.caller {
            Some(c) => format!("{}@{}[{c}]", self.clause, self.path),
            None => format!("{}@{}", self.clause, self.path),
        }
    }
}

/// The sites of a `stops=` attribute: space-separated `<sec-id>@<path>` or `<sec-id>@<path>[<caller>]`.
fn erratum_stops(id: &str, s: &str) -> Result<Vec<ErratumStop>, String> {
    s.split_whitespace()
        .map(|w| {
            let bad = || format!("{id}: stops {w:?} is not <sec-id>@<path>[<caller sec-id>]");
            let (site, caller) = match w.strip_suffix(']') {
                Some(x) => x.split_once('[').map(|(a, c)| (a, Some(c.to_string()))).ok_or_else(bad)?,
                None => (w, None),
            };
            let (clause, path) = site.split_once('@').ok_or_else(bad)?;
            if clause.is_empty() || path.is_empty() || caller.as_deref().is_some_and(|c| c.is_empty() || c.contains(['[', ']', '@'])) {
                return Err(bad());
            }
            Ok(ErratumStop { clause: clause.into(), path: path.into(), caller })
        })
        .collect()
}

/// An early-error rule's reading (`<emu-reading clause=… grammar=… rule=… hash=…>`): the
/// Early Errors clause, its block's grammar, the rule's position in the block's list, the
/// SHA-256 of its `<li>` content, and each reading's replacement sentences (`<p reading=…>`);
/// `also` (`also=… also-clause=…`): productions the readings, not the literal text, also hold on.
pub struct RuleAnchor {
    pub clause: String,
    pub grammar: String,
    pub rule: usize,
    pub hash: String,
    pub alts: Vec<(String, String)>,
    pub also: Option<(String, String)>,
}

/// A rule anchor from its tag and body; `readings`: the readings its alternatives may be.
fn rule_anchor(id: &str, rt: &str, rb: &str, readings: &[&str]) -> Result<RuleAnchor, String> {
    let need = |a: &str| attr(rt, a).ok_or_else(|| format!("{id}: a rule reading without its {a}"));
    let rule = need("rule")?.parse().map_err(|_| format!("{id}: rule is not an index"))?;
    let mut alts = Vec::new();
    for (pt, pb) in elements(rb, "p") {
        let reading = attr(pt, "reading").ok_or_else(|| format!("{id}: a rule reading's <p> without its reading"))?;
        if !readings.contains(&reading.as_str()) {
            return Err(format!("{id}: reading {reading:?}"));
        }
        alts.push((reading, pb.to_string()));
    }
    if alts.is_empty() {
        return Err(format!("{id}: a rule reading without a <p reading=…> sentence"));
    }
    let also = match (attr(rt, "also"), attr(rt, "also-clause")) {
        (Some(g), Some(c)) => Some((g, c)),
        (None, None) => None,
        _ => return Err(format!("{id}: also= without also-clause= or the reverse")),
    };
    Ok(RuleAnchor { clause: need("clause")?, grammar: need("grammar")?, rule, hash: need("hash")?, alts, also })
}

#[derive(Default)]
pub struct Overlay {
    pub prims: Vec<Prim>,
    pub phrases: Vec<Phrase>,
    /// the errata, then the definition readings (`<emu-reading steps=…>` outside an erratum,
    /// resolution `definition`)
    pub errata: Vec<Erratum>,
    pub sorts: Vec<Sort>,
    pub fields: Vec<Fields>,
    pub guards: Vec<Guard>,
    pub ops: Vec<Op>,
    /// the rows a reading adds to an SDO (`<emu-reading grammar=…>`)
    pub rows: Vec<RowReading>,
    /// the frozen phrase ids (`phrase-ids.txt`): category and name, by id
    pub phrase_ids: Vec<(String, String)>,
    /// the frozen primitive ids (`prim-ids.txt`): name, by id
    pub prim_ids: Vec<String>,
    /// the frozen sort ids (`sort-ids.txt`): name, by id
    pub sort_ids: Vec<String>,
    /// the frozen field ids (`field-ids.txt`): name, by id
    pub field_ids: Vec<String>,
    /// the frozen enum ids (`enum-ids.txt`): name, by id
    pub enum_ids: Vec<String>,
    /// the kept clause, SDO, concrete-method and erratum ids (`crate::ids`), where the files are
    pub clause_ids: Option<crate::ids::Kept>,
    pub sdo_ids: Option<crate::ids::Kept>,
    pub method_ids: Option<crate::ids::Kept>,
    pub erratum_ids: Option<crate::ids::Kept>,
    /// the kept residue reason and kind ids
    pub reason_ids: Option<crate::ids::Kept>,
    pub note_ids: Option<crate::ids::Kept>,
    /// the kept production, nonterminal and parameter ids (`prod-ids.txt`, `nt-ids.txt`, `param-ids.txt`:
    /// crates/jsgrammar `ids`, which writes them)
    pub grammar_ids: jsgrammar::ids::KeptIds,
    /// the kept table ids (`table-ids.txt`), by the table's Lean name
    pub table_ids: Option<crate::ids::Kept>,
    /// the steps where `Expr.extreme` may stand (`choice-sites.txt`): `clause step`
    pub choice_sites: Vec<String>,
    /// the host requirement sentences' dispositions (`<emu-host-law>`)
    pub host_laws: Vec<HostLaw>,
    /// the rules of the overlay's own grammars (`<emu-grammar type="definition">` outside a reading)
    pub grammar: Vec<jsgrammar::grammar::Rule>,
    /// the residue steps given no meaning on purpose (`<emu-permanent>`)
    pub permanent: Vec<Permanent>,
    /// names for algorithms the text writes without one (`<emu-steps-name name=… clause=…>`):
    /// the name, and the clause whose first algorithm it calls
    pub steps_names: Vec<(String, String)>,
    /// steps put before a spec algorithm's (`<emu-step-patch>`)
    pub step_patches: Vec<StepPatch>,
    /// the results typed narrower than their headers (`<emu-result-type>`)
    pub result_types: Vec<ResultType>,
}

/// `<emu-result-type clause=…>T</emu-result-type>`: the clause's operation's result typed T, which its meaning ignores.
#[derive(Clone, Debug)]
pub struct ResultType {
    pub clause: String,
    pub ty: String,
    pub file: String,
}

/// An `<emu-step-patch clause= alg= hash= [nest=]><emu-alg>…</emu-alg></emu-step-patch>`: steps put
/// before those of the clause's `alg`th algorithm, whose body has SHA-256 `hash`; `nest="C M"` puts
/// clause C's `M`th algorithm under the last of them.
pub struct StepPatch {
    pub clause: String,
    pub alg: usize,
    pub hash: String,
    pub nest: Option<(String, usize)>,
    /// the emu-alg's body
    pub raw: String,
    pub file: String,
}

/// A step patch from its tag and content.
fn step_patch(tag: &str, body: &str, file: &str) -> Result<StepPatch, String> {
    let clause = attr(tag, "clause").ok_or("an emu-step-patch without its clause")?;
    let num = |v: &str| v.parse::<usize>().map_err(|_| format!("{clause}: emu-step-patch index {v:?}"));
    let alg = num(&attr(tag, "alg").ok_or_else(|| format!("{clause}: an emu-step-patch without its alg"))?)?;
    let hash = attr(tag, "hash").ok_or_else(|| format!("{clause}: an emu-step-patch without its hash"))?;
    let nest = match attr(tag, "nest") {
        Some(n) => {
            let (c, m) = n.split_once(' ').ok_or_else(|| format!("{clause}: emu-step-patch nest {n:?} is not `<sec-id> <index>`"))?;
            Some((c.to_string(), num(m)?))
        }
        None => None,
    };
    let [(_, raw)] = elements(body, "emu-alg")[..] else { return Err(format!("{clause}: an emu-step-patch has one emu-alg")) };
    crate::spec::step_tree(raw).map_err(|e| format!("{clause}: emu-step-patch: {e}"))?;
    Ok(StepPatch { clause, alg, hash, nest, raw: raw.to_string(), file: file.to_string() })
}

/// The step lines of an emu-alg body, its first step's column moved to `col`.
fn shifted(raw: &str, col: usize) -> Vec<String> {
    let lines: Vec<&str> = raw.split('\n').collect();
    let body = &lines[1..lines.len() - 1];
    let base = body.iter().filter(|l| !l.trim().is_empty()).map(|l| l.len() - l.trim_start().len()).min().unwrap_or(0);
    body.iter().map(|l| if l.trim().is_empty() { l.to_string() } else { format!("{}{}", " ".repeat(col), &l[base..]) }).collect()
}

/// Applies the overlay's step patches to the scanned algorithms: each patched body is the patch's
/// steps at the algorithm's column, then its own; source positions stay those of spec.html.
pub fn patch(sp: &mut crate::spec::Spec, o: &Overlay) -> Result<(), String> {
    let find = |sp: &crate::spec::Spec, c: &str, k: usize| {
        let ci = sp.clauses.iter().position(|x| x.id == c).ok_or_else(|| format!("emu-step-patch: no clause {c}"))?;
        sp.algs.iter().position(|a| a.clause == Some(ci) && a.idx == k).ok_or_else(|| format!("emu-step-patch: {c} has no algorithm {k}"))
    };
    for p in &o.step_patches {
        let ai = find(sp, &p.clause, p.alg)?;
        let a = &sp.algs[ai];
        if crate::text::sha256(&a.raw) != p.hash {
            return Err(format!("{}: emu-step-patch on {} {}: the algorithm's hash is {}", p.file, p.clause, p.alg, crate::text::sha256(&a.raw)));
        }
        let mut lines = shifted(&p.raw, a.base);
        if let Some((c, m)) = &p.nest {
            let last = lines.iter().rev().find(|l| crate::spec::step_line(l).is_some()).ok_or("emu-step-patch: no step")?;
            let col = last.len() - last.trim_start().len() + 2;
            lines.extend(shifted(&sp.algs[find(sp, c, *m)?].raw, col));
        }
        let raw = format!("\n{}\n{}", lines.join("\n"), &a.raw[1..]);
        let (base, steps, close) = crate::spec::step_tree(&raw).map_err(|e| format!("{}: emu-step-patch on {}: {e}", p.file, p.clause))?;
        let a = &mut sp.algs[ai];
        (a.raw, a.base, a.steps, a.close_indent) = (raw, base, steps, close);
    }
    Ok(())
}

/// What a host requirement sentence is, when the base layer gives it no meaning of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LawClass {
    /// a `Host.WF` field states it
    Law,
    /// a property the specification's own algorithms must have: a proof obligation
    Theorem,
    /// advice to programs
    Advice,
    /// outside the base layer (ECMA-402, agent clusters, extensions)
    Scope,
    /// the grammar and its early errors carry it
    Syntax,
    /// about cost or safety, not results
    Nonfunctional,
}

impl LawClass {
    pub const ALL: [LawClass; 6] = [LawClass::Law, LawClass::Theorem, LawClass::Advice, LawClass::Scope, LawClass::Syntax, LawClass::Nonfunctional];

    pub fn label(self) -> &'static str {
        match self {
            LawClass::Law => "law",
            LawClass::Theorem => "theorem",
            LawClass::Advice => "advice",
            LawClass::Scope => "scope",
            LawClass::Syntax => "syntax",
            LawClass::Nonfunctional => "nonfunctional",
        }
    }
}

/// An `<emu-host-law clause= [para=] [sent=] class= [law=]>reason</emu-host-law>`: the
/// requirement sentences of a clause, of its paragraph `para` (its index among the clause's
/// paragraphs), or that paragraph's sentence `sent`, and what they are.
pub struct HostLaw {
    pub clause: String,
    pub para: Option<usize>,
    pub sent: Option<usize>,
    pub class: LawClass,
    /// the `Host.WF` field stating it (class law only)
    pub law: Option<String>,
    pub reason: String,
    pub file: String,
}

/// A host law from its tag and content.
pub fn host_law(tag: &str, body: &str, file: &str) -> Result<HostLaw, String> {
    let clause = attr(tag, "clause").ok_or("an emu-host-law without its clause")?;
    let num = |k: &str| attr(tag, k).map(|v| v.parse::<usize>().map_err(|_| format!("{clause}: emu-host-law {k}={v:?}"))).transpose();
    let (para, sent) = (num("para")?, num("sent")?);
    if sent.is_some() && para.is_none() {
        return Err(format!("{clause}: emu-host-law sent= without para="));
    }
    let c = attr(tag, "class").ok_or_else(|| format!("{clause}: an emu-host-law without its class"))?;
    let class = LawClass::ALL.into_iter().find(|k| k.label() == c).ok_or_else(|| format!("{clause}: emu-host-law class {c:?}"))?;
    let law = attr(tag, "law");
    match (&law, class) {
        (None, LawClass::Law) => return Err(format!("{clause}: class=\"law\" without law=")),
        (Some(_), k) if k != LawClass::Law => return Err(format!("{clause}: law= on class {c:?}")),
        (Some(f), _) if !f.starts_with(|x: char| x.is_ascii_alphabetic() || x == '_') || !f.chars().all(|x| x.is_ascii_alphanumeric() || x == '_') => {
            return Err(format!("{clause}: law={f:?} is not a field name"))
        }
        _ => {}
    }
    let reason = crate::text::squash(body);
    if reason.is_empty() {
        return Err(format!("{clause}: an emu-host-law without its reason"));
    }
    Ok(HostLaw { clause, para, sent, class, law, reason, file: file.to_string() })
}

/// Why a residue step has no meaning of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StepClass {
    /// an Assert about where a value or a call came from: no test on the state at the step
    AssertProvenance,
    /// an Assert about what a later step or the caller will do
    AssertFuture,
    /// a NOTE's alternative algorithm, which the normative steps do not use
    Informative,
    /// a test on what an object's internal methods have returned before, which the state does not record
    History,
}

impl StepClass {
    pub const ALL: [StepClass; 4] = [StepClass::AssertProvenance, StepClass::AssertFuture, StepClass::Informative, StepClass::History];

    pub fn label(self) -> &'static str {
        match self {
            StepClass::AssertProvenance => "assert-provenance",
            StepClass::AssertFuture => "assert-future",
            StepClass::Informative => "informative",
            StepClass::History => "history",
        }
    }
}

/// An `<emu-permanent clause= step= class=>reason</emu-permanent>`: the residue step at `step`
/// of the clause (`sec-x`, or `sec-x#n` for its n-th algorithm) or overlay algorithm (its
/// residue id), and why it stays without a meaning.
pub struct Permanent {
    pub clause: String,
    pub step: String,
    pub class: StepClass,
    pub reason: String,
    pub file: String,
}

/// A permanent step entry from its tag and content.
pub fn permanent(tag: &str, body: &str, file: &str) -> Result<Permanent, String> {
    let clause = attr(tag, "clause").ok_or("an emu-permanent without its clause")?;
    let step = attr(tag, "step").ok_or_else(|| format!("{clause}: an emu-permanent without its step"))?;
    let c = attr(tag, "class").ok_or_else(|| format!("{clause} {step}: an emu-permanent without its class"))?;
    let class = StepClass::ALL.into_iter().find(|k| k.label() == c).ok_or_else(|| format!("{clause} {step}: emu-permanent class {c:?}"))?;
    let reason = crate::text::squash(body);
    if reason.is_empty() {
        return Err(format!("{clause} {step}: an emu-permanent without its reason"));
    }
    Ok(Permanent { clause, step, class, reason, file: file.to_string() })
}

fn attr(tag: &str, name: &str) -> Option<String> {
    crate::spec::attr(tag, name)
}

/// The elements `<name …>…</name>` of `s`: the opening tag and the content.
fn elements<'s>(s: &'s str, name: &str) -> Vec<(&'s str, &'s str)> {
    let open = format!("<{name}");
    let close = format!("</{name}>");
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(a) = s[i..].find(&open).map(|a| i + a) {
        let after = &s[a + open.len()..];
        if !after.starts_with([' ', '>']) {
            i = a + open.len();
            continue;
        }
        let Some(gt) = s[a..].find('>').map(|g| a + g + 1) else { break };
        let Some(end) = s[gt..].find(&close).map(|e| gt + e) else { break };
        out.push((&s[a..gt], &s[gt..end]));
        i = end + close.len();
    }
    out
}

/// Every `<name …>` opening tag of `s` and the content up to the next `</name>`: for
/// elements that hold no element of their own kind, at any depth.
fn leaf_elements<'s>(s: &'s str, name: &str) -> Vec<(&'s str, &'s str)> {
    let (open, close) = (format!("<{name}"), format!("</{name}>"));
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(a) = s[i..].find(&open).map(|a| i + a) {
        i = a + open.len();
        if !s[i..].starts_with([' ', '>']) {
            continue;
        }
        let Some(gt) = s[a..].find('>').map(|g| a + g + 1) else { break };
        let Some(end) = s[gt..].find(&close).map(|e| gt + e) else { break };
        if !s[gt..end].contains(&open) {
            out.push((&s[a..gt], &s[gt..end]));
        }
    }
    out
}

/// `[not ]Name(_a_, ~e~, …)`.
fn parse_meaning(m: &str) -> Result<(String, Vec<Arg>, bool), String> {
    let (neg, m) = match m.strip_prefix("not ") {
        Some(r) => (true, r),
        None => (false, m),
    };
    let open = m.find('(').ok_or_else(|| format!("meaning {m:?}"))?;
    let inner = m[open + 1..].strip_suffix(')').ok_or_else(|| format!("meaning {m:?}"))?;
    let mut args = Vec::new();
    for a in inner.split(", ").filter(|a| !a.is_empty()) {
        if let Some(v) = a.strip_prefix('_').and_then(|v| v.strip_suffix('_')) {
            args.push(Arg::Var(v.to_string()));
        } else if let Some(e) = a.strip_prefix('~').and_then(|v| v.strip_suffix('~')) {
            args.push(Arg::Enum(e.to_string()));
        } else if let Some(f) = a.strip_prefix("[[").and_then(|v| v.strip_suffix("]]")) {
            args.push(Arg::Field(f.to_string()));
        } else {
            return Err(format!("meaning argument {a:?}"));
        }
    }
    Ok((m[..open].to_string(), args, neg))
}

/// `_a_: T, _b_: U`: each parameter's name and type; a type may hold commas.
fn parse_params(s: &str) -> Result<Vec<(String, String)>, String> {
    let s = crate::text::squash(s);
    let mut starts = Vec::new();
    for (i, _) in s.match_indices('_') {
        let at_start = i == 0 || s[..i].ends_with(", ");
        if at_start {
            if let Some(end) = s[i + 1..].find("_: ") {
                let name = &s[i + 1..i + 1 + end];
                if !name.is_empty() && name.chars().all(|c| c.is_alphanumeric()) {
                    starts.push((i, name.to_string(), i + 1 + end + 3));
                }
            }
        }
    }
    let mut out = Vec::new();
    for (k, (_, name, ty)) in starts.iter().enumerate() {
        let end = starts.get(k + 1).map(|x| x.0 - 2).unwrap_or(s.len());
        out.push((name.clone(), s[*ty..end].trim().to_string()));
    }
    if out.is_empty() && !s.trim().is_empty() {
        return Err(format!("emu-params {s:?}"));
    }
    Ok(out)
}

/// Every id in `phrase-unreviewed.txt` names an overlay entry.
/// The overlay's grammar rules: each nonterminal defined once, every one they name defined.
fn check_grammar(rules: &[jsgrammar::grammar::Rule]) -> Result<(), String> {
    for (i, r) in rules.iter().enumerate() {
        if rules[..i].iter().any(|q| q.lhs == r.lhs) {
            return Err(format!("the overlay's grammar defines {} twice", r.lhs));
        }
        let jsgrammar::grammar::Body::Alts(alts) = &r.body else { continue };
        let mut nts = Vec::new();
        alts.iter().flat_map(|a| &a.rhs).for_each(|i| jsgrammar::gl::item_nts(i, &mut nts));
        if let Some(n) = nts.iter().find(|n| !rules.iter().any(|q| &q.lhs == *n)) {
            return Err(format!("the overlay's grammar: {} names {n}, which it does not define", r.lhs));
        }
    }
    Ok(())
}

fn check_unreviewed(dir: &str, o: &Overlay) -> Result<(), String> {
    let path = format!("{dir}/phrase-unreviewed.txt");
    let Ok(s) = std::fs::read_to_string(&path) else { return Ok(()) };
    for l in s.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        if !o.prims.iter().any(|p| p.id == l) && !o.phrases.iter().any(|p| p.id == l) && !o.errata.iter().any(|e| e.id == l) && !o.rows.iter().any(|r| r.id == l) {
            return Err(format!("{path}: {l} names no overlay entry"));
        }
    }
    Ok(())
}

/// `phrase-ids.txt`: a line `cat name` per phrase id, in id order.
fn phrase_ids(dir: &str) -> Result<Vec<(String, String)>, String> {
    let path = format!("{dir}/{PHRASE_IDS}");
    let Ok(s) = std::fs::read_to_string(&path) else { return Ok(Vec::new()) };
    s.lines()
        .map(|l| l.split_once(' ').map(|(c, n)| (c.to_string(), n.to_string())).ok_or_else(|| format!("{path}: {l}: not `cat name`")))
        .collect()
}

/// The primitives the machine implements that a sort's test may name without an overlay declaration.
const KNOWN_TESTS: &[&str] = &["IsFinite", "IsEmpty"];

/// The categories of type rules a `kind="type"` phrase may claim.
const TYPE_CATS: &[&str] = &["T", "HT", "HT1"];

/// The phrase index's file name in the overlay directory.
pub const PHRASE_IDS: &str = "phrase-ids.txt";

/// The primitive index's file name in the overlay directory: a name per line, in id order.
pub const PRIM_IDS: &str = "prim-ids.txt";

/// The sort index's file name in the overlay directory: a name per line, in id order.
pub const SORT_IDS: &str = "sort-ids.txt";

/// The field index's file name in the overlay directory: a name per line, in id order.
pub const FIELD_IDS: &str = "field-ids.txt";

/// The enum index's file name in the overlay directory: a name per line, in id order.
pub const ENUM_IDS: &str = "enum-ids.txt";

pub fn read(dir: &str) -> Result<Overlay, String> {
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .map_err(|e| format!("{dir}: {e}"))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "emu"))
        .collect();
    files.sort();
    let mut o = Overlay::default();
    let mut defs = Vec::new();
    for f in files {
        let s = std::fs::read_to_string(&f).map_err(|e| format!("{}: {e}", f.display()))?;
        let file = f.file_name().unwrap().to_string_lossy().to_string();
        for (tag, body) in elements(&s, "emu-primitive") {
            let sig = elements(body, "emu-signature").first().map(|x| x.1.to_string()).ok_or("an emu-primitive without its signature")?;
            let p = elements(body, "p").first().map(|x| crate::text::squash(x.1)).unwrap_or_default();
            o.prims.push(Prim {
                id: attr(tag, "id").ok_or("an emu-primitive without an id")?,
                name: attr(tag, "name").ok_or("an emu-primitive without a name")?,
                signature: sig,
                meaning: p,
            });
        }
        for (tag, _) in elements(&s, "emu-steps-name") {
            let need = |k: &str| attr(tag, k).ok_or_else(|| format!("an emu-steps-name without {k}"));
            o.steps_names.push((need("name")?, need("clause")?));
        }
        for (tag, body) in elements(&s, "emu-step-patch") {
            o.step_patches.push(step_patch(tag, body, &file)?);
        }
        for (tag, body) in elements(&s, "emu-result-type") {
            let clause = attr(tag, "clause").ok_or("an emu-result-type without a clause")?;
            o.result_types.push(ResultType { clause, ty: crate::text::squash(body), file: file.clone() });
        }
        for (tag, body) in elements(&s, "emu-host-law") {
            o.host_laws.push(host_law(tag, body, &file)?);
        }
        for (tag, body) in elements(&s, "emu-permanent") {
            o.permanent.push(permanent(tag, body, &file)?);
        }
        for (tag, body) in elements(&s, "emu-erratum") {
            let id = attr(tag, "id").ok_or("an emu-erratum without an id")?;
            let mut readings = Vec::new();
            let mut rules = Vec::new();
            for (rt, rb) in elements(body, "emu-reading") {
                // a row reading: read with the others below
                if attr(rt, "grammar").is_some() && attr(rt, "rule").is_none() {
                    continue;
                }
                if attr(rt, "rule").is_some() {
                    rules.push(rule_anchor(&id, rt, rb, &["test262", "proposed"])?);
                    continue;
                }
                let mut alts = Vec::new();
                let mut seen = Vec::new();
                for (at, ab) in elements(rb, "emu-alg") {
                    let reading = attr(at, "reading").ok_or_else(|| format!("{id}: an emu-alg without its reading"))?;
                    // each of test262 and proposed at most once per step
                    for r in reading.split(' ') {
                        if r != "test262" && r != "proposed" || seen.contains(&r.to_string()) {
                            return Err(format!("{id}: reading {reading:?}"));
                        }
                        seen.push(r.to_string());
                    }
                    let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("{id}: {e}"))?;
                    alts.push(Alt { reading, raw: ab.to_string(), base, close, steps });
                }
                readings.push(Anchor {
                    clause: attr(rt, "clause").ok_or_else(|| format!("{id}: an emu-reading without its clause"))?,
                    step: attr(rt, "step").ok_or_else(|| format!("{id}: an emu-reading without its step"))?,
                    hash: attr(rt, "hash").ok_or_else(|| format!("{id}: an emu-reading without its hash"))?,
                    alts,
                    also: vec![],
                });
            }
            let resolution = attr(tag, "resolution").ok_or_else(|| format!("{id}: no resolution"))?;
            if !["test262", "literal", "proposed", "pending"].contains(&resolution.as_str()) {
                return Err(format!("{id}: resolution {resolution:?}"));
            }
            // a literal erratum says where its text stops (`stops=""`: nowhere); a proposed one never stops; another may, for its literal reading
            let stops = match (resolution.as_str(), attr(tag, "stops")) {
                ("proposed", Some(_)) => return Err(format!("{id}: a proposed erratum with stops=")),
                (_, Some(x)) => erratum_stops(&id, &x)?,
                ("literal", None) => return Err(format!("{id}: a literal erratum without stops=")),
                (_, None) => vec![],
            };
            let stops_given = attr(tag, "stops").is_some();
            let kind = attr(tag, "kind").unwrap_or_else(|| "defect".into());
            if !["defect", "proposal"].contains(&kind.as_str()) {
                return Err(format!("{id}: kind {kind:?}"));
            }
            let switch = attr(tag, "switch").unwrap_or_else(|| "spec".into());
            if !["spec", "parser", "none"].contains(&switch.as_str()) {
                return Err(format!("{id}: switch {switch:?}"));
            }
            let mut orphans = Vec::new();
            for (ot, _) in elements(body, "emu-orphan-row") {
                let need = |a: &str| attr(ot, a).ok_or_else(|| format!("{id}: an emu-orphan-row without its {a}"));
                orphans.push(OrphanRow { clause: need("clause")?, grammar: need("grammar")? });
            }
            let mut rule_readings = Vec::new();
            for (_, rb) in elements(body, "emu-rule-reading") {
                for (gt, _) in elements(rb, "emu-grammar") {
                    if let Some(rd) = attr(gt, "reading") {
                        for x in rd.split(' ').filter(|x| !x.is_empty()) {
                            rule_readings.push(x.to_string());
                        }
                    }
                }
            }
            o.errata.push(Erratum { name: attr(tag, "name").ok_or_else(|| format!("{id}: no name"))?, id, resolution, kind, switch, readings, rules, rule_readings, stops, stops_given, orphans });
        }
        let errata: Vec<std::ops::Range<usize>> = elements(&s, "emu-erratum").iter().map(|(t, b)| {
            let a = t.as_ptr() as usize - s.as_ptr() as usize;
            a..b.as_ptr() as usize - s.as_ptr() as usize + b.len()
        }).collect();
        for (rt, rb) in elements(&s, "emu-reading") {
            let at = rt.as_ptr() as usize - s.as_ptr() as usize;
            if attr(rt, "rule").is_some() {
                if errata.iter().any(|r| r.contains(&at)) {
                    continue;
                }
                let (clause, hash) = (attr(rt, "clause").unwrap_or_default(), attr(rt, "hash").unwrap_or_default());
                let id = format!("definition-{clause}-rule-{}", &hash[..hash.len().min(12)]);
                if defs.iter().any(|d: &Erratum| d.id == id) {
                    return Err(format!("{id}: two definition readings with one id"));
                }
                let r = rule_anchor(&id, rt, rb, &["definition"])?;
                defs.push(Erratum { name: id.clone(), id, resolution: "definition".into(), kind: "defect".into(), switch: "spec".into(), readings: vec![], rules: vec![r], rule_readings: vec![], stops: vec![], stops_given: false, orphans: vec![] });
                continue;
            }
            if let Some(grammar) = attr(rt, "grammar") {
                let id = attr(rt, "id").ok_or_else(|| format!("a row reading for {grammar} without an id"))?;
                let clause = attr(rt, "clause").ok_or_else(|| format!("{id}: no clause"))?;
                // an erratum's row is its `test262 proposed` reading; any other has no attributes
                let erratum = errata.iter().position(|r| r.contains(&at)).map(|k| attr(elements(&s, "emu-erratum")[k].0, "name").unwrap_or_default());
                let [(at, ab)] = elements(rb, "emu-alg")[..] else { return Err(format!("{id}: a row reading has one emu-alg")) };
                let want = if erratum.is_some() { "reading=\"test262 proposed\">" } else { ">" };
                if at.trim_start_matches("<emu-alg").trim() != want {
                    return Err(format!("{id}: a row reading's emu-alg tag is not <emu-alg{}{want}", if erratum.is_some() { " " } else { "" }));
                }
                let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("{id}: {e}"))?;
                let alg = PhraseAlg { params: vec![], raw: ab.to_string(), base, close, steps };
                let grammar_clause = attr(rt, "grammar-clause").unwrap_or_else(|| clause.clone());
                o.rows.push(RowReading { id, clause, grammar, grammar_clause, alg, file: file.clone(), erratum });
                continue;
            }
            let (Some(clause), Some(steps)) = (attr(rt, "clause"), attr(rt, "steps")) else { continue };
            // an SDO clause's algorithms share step numbers: there an `id` tells their readings apart
            let id = attr(rt, "id").unwrap_or_else(|| format!("definition-{clause}-{}", steps.split(' ').next().unwrap_or("")));
            if defs.iter().any(|d: &Erratum| d.id == id) {
                return Err(format!("{id}: two definition readings with one id"));
            }
            let hashes = attr(rt, "hashes").ok_or_else(|| format!("{id}: no hashes"))?;
            let pairs: Vec<(String, String)> = steps.split(' ').map(str::to_string).zip(hashes.split(' ').map(str::to_string)).collect();
            if pairs.is_empty() || pairs.len() != steps.split(' ').count() || pairs.len() != hashes.split(' ').count() {
                return Err(format!("{id}: steps and hashes differ in number"));
            }
            let mut alts = Vec::new();
            for (at, ab) in elements(rb, "emu-alg") {
                if attr(at, "reading").as_deref() != Some("definition") {
                    return Err(format!("{id}: an emu-alg outside an erratum is a definition reading"));
                }
                let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("{id}: {e}"))?;
                alts.push(Alt { reading: "definition".into(), raw: ab.to_string(), base, close, steps });
            }
            let (step, hash) = pairs[0].clone();
            let anchor = Anchor { clause, step, hash, alts, also: pairs[1..].to_vec() };
            defs.push(Erratum { name: id.clone(), id, resolution: "definition".into(), kind: "defect".into(), switch: "spec".into(), readings: vec![anchor], rules: vec![], rule_readings: vec![], stops: vec![], stops_given: false, orphans: vec![] });
        }
        for (tag, body) in elements(&s, "emu-grammar") {
            if attr(tag, "type").as_deref() != Some("definition") || attr(tag, "reading").is_some() {
                continue;
            }
            let line = s[..tag.as_ptr() as usize - s.as_ptr() as usize].lines().count() + 1;
            let rules = jsgrammar::grammar::parse_block(body, line).map_err(|e| format!("{file}: {}", e.trim_start_matches("spec.html:")))?;
            o.grammar.extend(rules);
        }
        for (tag, body) in leaf_elements(&s, "emu-clause") {
            let Some(ty) = attr(tag, "type").filter(|t| t == "abstract operation" || t == "built-in function") else { continue };
            let id = attr(tag, "id").ok_or("an overlay abstract operation without an id")?;
            let behaviour_of = attr(tag, "behaviour-of");
            if (ty == "built-in function") != behaviour_of.is_some() {
                return Err(format!("{id}: behaviour-of exactly on a built-in function"));
            }
            let h1 = elements(body, "h1").first().map(|x| x.1.to_string()).ok_or_else(|| format!("{id}: no h1"))?;
            let dl = body.find("<dl class=\"header\">").map(|a| body[a..].split("<emu-alg").next().unwrap_or("").to_string()).unwrap_or_default();
            let ab = elements(body, "emu-alg").first().map(|x| x.1).ok_or_else(|| format!("{id}: no emu-alg"))?;
            let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("{id}: {e}"))?;
            let alg = PhraseAlg { params: vec![], raw: ab.to_string(), base, close, steps };
            o.ops.push(Op { id, ty, behaviour_of, h1, dl, alg, file: file.clone() });
        }
        for (tag, body) in elements(&s, "emu-sort") {
            let name = attr(tag, "name").ok_or("an emu-sort without a name")?;
            let alg = elements(body, "emu-alg").first().map(|x| x.1);
            let test = match (attr(tag, "test"), attr(tag, "alg"), alg) {
                (None, None, None) => SortTest::None,
                (Some(t), None, None) => {
                    let (prim, args, neg) = parse_meaning(&t).map_err(|e| format!("sort {name}: {e}"))?;
                    if !o.prims.iter().any(|p| p.name == prim) && !KNOWN_TESTS.contains(&prim.as_str()) {
                        return Err(format!("sort {name}: test names no declared primitive {prim}"));
                    }
                    SortTest::Prim(prim, args, neg)
                }
                (None, Some(op), None) => SortTest::Op(op),
                (None, None, Some(ab)) => {
                    let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("sort {name}: {e}"))?;
                    SortTest::Steps(PhraseAlg { params: vec![("v".into(), "anything".into())], raw: ab.to_string(), base, close, steps })
                }
                _ => return Err(format!("sort {name}: more than one of test=, alg= and an emu-alg")),
            };
            let record = tag.split(|c: char| c.is_whitespace() || c == '>').any(|w| w == "record");
            o.sorts.push(Sort { name, sup: attr(tag, "super"), record, test, clause: attr(tag, "clause").unwrap_or_default(), context: attr(tag, "context"), ty: attr(tag, "type") });
        }
        for (tag, body) in elements(&s, "emu-fields") {
            let of = attr(tag, "of").ok_or("an emu-fields without of=")?;
            let mut rows = Vec::new();
            for l in body.lines().map(str::trim).filter(|l| !l.is_empty()) {
                let (f, t) = l.strip_prefix("[[").and_then(|x| x.split_once("]]: ")).ok_or_else(|| format!("emu-fields {of}: not [[F]]: T: {l:?}"))?;
                rows.push((f.to_string(), t.to_string()));
            }
            let slots = tag.split(|c: char| c.is_whitespace() || c == '>').any(|w| w == "slots");
            o.fields.push(Fields { of, slots, rows });
        }
        for (tag, _) in elements(&s, "emu-guard") {
            let need = |k: &str| attr(tag, k).ok_or_else(|| format!("an emu-guard without {k}="));
            o.guards.push(Guard { op: need("op")?, ty: need("type")? });
        }
        for (tag, body) in elements(&s, "emu-phrase") {
            let id = attr(tag, "id").ok_or("an emu-phrase without an id")?;
            let pattern = elements(body, "emu-pattern").first().map(|x| x.1.to_string()).ok_or_else(|| format!("{id}: no pattern"))?;
            let subject = attr(tag, "subject").map(|v| v.trim_matches('_').to_string());
            let kind = attr(tag, "kind").unwrap_or_default();
            if subject.is_some() != (kind == "predicate" || kind == "type") {
                return Err(format!("{id}: a subject exactly when the kind is predicate or type"));
            }
            let tcat = if kind == "type" {
                let rn = attr(tag, "rule").ok_or_else(|| format!("{id}: a type phrase claims a rule (rule=)"))?;
                let cats: Vec<&'static str> = crate::grammar::RULES.iter().filter(|r| r.1 == rn && TYPE_CATS.contains(&r.0)).map(|r| r.0).collect();
                match cats.as_slice() {
                    [c] => Some(*c),
                    _ => return Err(format!("{id}: rule {rn} is not one type rule ({cats:?})")),
                }
            } else {
                None
            };
            let (prim, args, neg, alg) = match (attr(tag, "meaning"), elements(body, "emu-alg").first()) {
                (Some(m), None) => {
                    let (prim, args, neg) = parse_meaning(&m)?;
                    if !o.prims.iter().any(|p| p.name == prim) {
                        return Err(format!("{id}: meaning names no declared primitive {prim}"));
                    }
                    (prim, args, neg, None)
                }
                (None, Some((_, ab))) => {
                    let params = parse_params(elements(body, "emu-params").first().map(|x| x.1).unwrap_or(""))?;
                    let mut want: Vec<String> = Vec::new();
                    for t in tokenize(&pattern).iter().filter(|t| t.k == K::Var) {
                        if !want.contains(&t.v) {
                            want.push(t.v.clone());
                        }
                    }
                    if subject.as_ref().is_some_and(|x| want.contains(x)) {
                        return Err(format!("{id}: the subject is also a variable of the pattern"));
                    }
                    want.extend(subject.clone());
                    let mut names: Vec<String> = params.iter().map(|p| p.0.clone()).collect();
                    if attr(tag, "rule").is_some_and(|r| crate::conv::CLOSURE_STEPS.contains(&r.as_str())) && names.pop().is_none() {
                        return Err(format!("{id}: no emu-params entry for its nested steps"));
                    }
                    if names != want {
                        return Err(format!("{id}: emu-params {names:?}, not the pattern's variables then the subject {want:?}"));
                    }
                    let (base, steps, close) = crate::spec::step_tree(ab).map_err(|e| format!("{id}: {e}"))?;
                    (String::new(), vec![], false, Some(PhraseAlg { params, raw: ab.to_string(), base, close, steps }))
                }
                _ => return Err(format!("{id}: a meaning attribute or an emu-alg, not both or neither")),
            };
            let all_alternatives = match attr(tag, "alternatives").as_deref() {
                None => false,
                Some("all") => true,
                Some(a) => return Err(format!("{id}: alternatives {a:?}")),
            };
            if all_alternatives && (attr(tag, "rule").is_none() || alg.is_none() || elements(body, "p").is_empty()) {
                return Err(format!("{id}: alternatives=\"all\" needs rule=, an emu-alg, and a <p> saying why the alternatives are synonyms"));
            }
            let spelled = match attr(tag, "literals").as_deref() {
                None => false,
                Some("spelled") if !elements(body, "p").is_empty() => true,
                Some("spelled") => return Err(format!("{id}: literals=\"spelled\" without a <p> naming the prose")),
                Some(l) => return Err(format!("{id}: literals {l:?}")),
            };
            o.phrases.push(Phrase {
                id,
                kind,
                subject,
                tcat,
                spelled,
                prim,
                args,
                neg,
                alg,
                rule: attr(tag, "rule"),
                all_alternatives,
                pattern,
                file: file.clone(),
            });
        }
    }
    o.errata.extend(defs);
    for s in &o.sorts {
        let Some(c) = &s.context else { continue };
        let ok = o.phrases.iter().find(|p| p.id == *c).is_some_and(|p| p.kind == "predicate" && p.alg.is_some() && p.rule.is_none() && p.vars().len() == 1);
        if !ok {
            return Err(format!("sort {}: context {c} is no predicate phrase with steps over one variable and the subject", s.name));
        }
    }
    check_grammar(&o.grammar)?;
    check_unreviewed(dir, &o)?;
    o.phrase_ids = phrase_ids(dir)?;
    let names = |f: &str| std::fs::read_to_string(format!("{dir}/{f}")).map(|s| s.lines().map(str::to_string).collect()).unwrap_or_default();
    o.prim_ids = names(PRIM_IDS);
    o.sort_ids = names(SORT_IDS);
    o.field_ids = names(FIELD_IDS);
    o.enum_ids = names(ENUM_IDS);
    o.clause_ids = crate::ids::read(dir, crate::ids::CLAUSE_IDS)?;
    o.sdo_ids = crate::ids::read(dir, crate::ids::SDO_IDS)?;
    o.method_ids = crate::ids::read(dir, crate::ids::METHOD_IDS)?;
    o.erratum_ids = crate::ids::read(dir, crate::ids::ERRATUM_IDS)?;
    o.reason_ids = crate::ids::read(dir, crate::ids::REASON_IDS)?;
    o.note_ids = crate::ids::read(dir, crate::ids::NOTE_IDS)?;
    o.grammar_ids = jsgrammar::ids::read_dir(std::path::Path::new(dir))?;
    o.table_ids = crate::ids::read(dir, crate::ids::TABLE_IDS)?;
    o.choice_sites = names("choice-sites.txt").into_iter().filter(|l: &String| !l.starts_with('#') && !l.is_empty()).map(|l| l.split('\t').next().unwrap_or("").to_string()).collect();
    Ok(o)
}

impl Phrase {
    /// The grammar category its pattern extends.
    pub fn cat(&self) -> Result<&'static str, String> {
        Ok(match self.kind.as_str() {
            "step" => "Step",
            "expression" => "P",
            "condition" => "CA",
            "predicate" => "PRED",
            "type" => self.tcat.ok_or_else(|| format!("{}: a type phrase without its rule's category", self.id))?,
            k => return Err(format!("{}: kind {k:?}", self.id)),
        })
    }

    /// The pattern's template: its variables are expression holes, every other token literal;
    /// glued to the token before where the pattern has no space and printing would put one.
    pub fn elems(&self) -> Vec<(El, bool)> {
        let toks = tokenize(&self.pattern);
        toks.iter()
            .enumerate()
            .map(|(i, t)| {
                let el = match t.k {
                    K::Var => El::Hole("E"),
                    K::Word | K::Punct | K::Poss => El::Lit(t.v.clone()),
                    k => El::KindV(k, t.v.clone(), canon(t)),
                };
                let glue = i > 0 && toks[i - 1].e == t.s && {
                    let pair = [Part::Text(toks[i - 1].raw.clone(), false), Part::Text(t.raw.clone(), false)];
                    join(&pair, &[], "").len() > toks[i - 1].raw.len() + t.raw.len()
                };
                (el, glue)
            })
            .collect()
    }

    /// The pattern's variables, in order: the holes.
    pub fn vars(&self) -> Vec<String> {
        tokenize(&self.pattern).iter().filter(|t| t.k == K::Var).map(|t: &Tok| t.v.clone()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erratum_stops_parse() {
        let s = erratum_stops("e", "sec-a@9 sec-b@1.a[sec-c] sec-jobs@-").unwrap();
        assert_eq!(s.iter().map(ErratumStop::text).collect::<Vec<_>>(), ["sec-a@9", "sec-b@1.a[sec-c]", "sec-jobs@-"]);
        assert_eq!(s[1].caller.as_deref(), Some("sec-c"));
        assert!(erratum_stops("e", "").unwrap().is_empty());
        for bad in ["sec-a", "@1", "sec-a@", "sec-a@1[]", "sec-a@1[x@y]", "sec-a@1]"] {
            assert!(erratum_stops("e", bad).is_err(), "{bad}");
        }
    }
}
