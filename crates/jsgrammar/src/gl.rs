//! GL: the grammars of spec.html's definition blocks, with one numbering of
//! their nonterminals (`NtId`) and of their right-hand sides (`ProdId`).
//!
//! The right-hand sides are listed (`Gl::prods`) grammar by grammar
//! (`G::ALL`), then by written alternative in each grammar's `Production`
//! order, and within an alternative over the presence masks of its optional
//! symbols (§5.1.6, "Optional Symbols": each alternative with `k` of them
//! specifies `2^k` right-hand sides), absent before present, the first
//! optional symbol the most significant. A `one of` terminal is one
//! right-hand side. Here a `ProdId` is a position in that list; the id the
//! output prints is the kept number `Gl::prod_ids` gives it
//! (spec/formal/prod-ids.txt, `crate::ids`), which is the position when
//! there is no table.
//!
//! The nonterminals are numbered by spec/formal/nt-ids.txt and the
//! parameters by param-ids.txt: `Gl::nts` and `Gl::params` are by kept id,
//! a new one after every number the table has, in the order of first
//! definition (then the nonterminals referenced but never defined); an
//! entry the grammar no longer has (or, loaded without json.emu, the JSON
//! grammar's) keeps its place, not live (`nt_live`, `param_live`).

use crate::grammar::{self, Body, Colons, Exclusion, Item, Rule, Sym, Terminal};
use crate::ids::{KeptIds, Numbering};
use crate::spec::{self, Prose, Spec};
use std::collections::{BTreeMap, BTreeSet};

pub type NtId = usize;
pub type ProdId = usize;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum G {
    NumericString,
    Lexical,
    Syntactic,
    RegExp,
    AnnexB,
    Json,
}

impl G {
    pub const ALL: [G; 6] = [G::NumericString, G::Lexical, G::Syntactic, G::RegExp, G::AnnexB, G::Json];
    pub fn name(self) -> &'static str {
        match self {
            G::NumericString => "NumericString",
            G::Lexical => "Lexical",
            G::Syntactic => "Syntactic",
            G::RegExp => "RegExp",
            G::AnnexB => "AnnexB",
            G::Json => "JSON",
        }
    }
    pub fn doc(self) -> &'static str {
        match self {
            G::NumericString => "the numeric string grammar (`:::`; §7.1.4.1, §7.1.4.1.3, §21.4.1.33.1)",
            G::Lexical => "the lexical grammar (`::`; §11, §12)",
            G::Syntactic => "the syntactic grammar (`:`; §13–§16, §20.2.3.5) with its supplemental grammars",
            G::RegExp => "the RegExp grammar (`::`; §22.2.1)",
            G::AnnexB => "Annex B's overlays (B.1.1, B.1.2, B.3.3, B.3.5)",
            G::Json => "the JSON text grammar (`::`; ECMA-404, spec/formal/json.emu)",
        }
    }
}

pub struct Block {
    /// The file it is in: `spec.html`, or `json.emu` for the JSON grammar.
    pub file: &'static str,
    pub clause: String,
    pub line: usize,
    pub prose: Prose,
    pub g: G,
    pub rules: Vec<Rule>,
    /// The indentation of its rules (`grammar::layout`).
    pub indent: usize,
}

/// A written production: an alternative of a rule, or a terminal of a `one
/// of` rule (`alt` its index in the rule's flattened rows).
#[derive(Clone, Copy, Debug)]
pub struct At {
    pub block: usize,
    pub rule: usize,
    pub alt: usize,
}

/// A right-hand side: a written production and the presence of each of its
/// optional symbols, left to right.
#[derive(Clone, Debug)]
pub struct Prod {
    pub g: G,
    pub at: At,
    pub lhs: NtId,
    /// The written production's index in its grammar (its `Production` constructor).
    pub ctor: usize,
    pub mask: Vec<bool>,
}

pub struct Gl {
    pub spec: Spec,
    pub blocks: Vec<Block>,
    /// By `NtId`: the nonterminal's name.
    pub nts: Vec<String>,
    /// By `NtId`: whether the grammar has it.
    pub nt_live: Vec<bool>,
    /// By `ParamId`: the parameter's name.
    pub params: Vec<String>,
    /// By `ParamId`: whether the grammar has it.
    pub param_live: Vec<bool>,
    /// Each grammar's rules, in spec order: (block, rule).
    pub by_g: BTreeMap<G, Vec<(usize, usize)>>,
    pub prods: Vec<Prod>,
    /// By position in `prods`: the right-hand side's kept id.
    pub prod_ids: Vec<ProdId>,
    /// The kept numberings (`ids::Numbering`): of the right-hand sides by key (`prod_key`), the
    /// nonterminals and the parameters by name.
    pub prod_numbering: Numbering,
    pub nt_numbering: Numbering,
    pub param_numbering: Numbering,
    /// json.emu's goal symbol ("its goal symbol is |X|"), with its line.
    pub json_goal: Option<(String, usize)>,
}

/// The presence masks of `k` optional symbols, in ProdId order.
pub fn masks(k: usize) -> Vec<Vec<bool>> {
    if k == 0 {
        return vec![Vec::new()];
    }
    let rest = masks(k - 1);
    let mut out = Vec::new();
    for first in [false, true] {
        for m in &rest {
            let mut v = vec![first];
            v.extend(m);
            out.push(v);
        }
    }
    out
}

/// `0`/`1` per optional symbol, or `-` for none.
pub fn mask_text(m: &[bool]) -> String {
    if m.is_empty() {
        "-".into()
    } else {
        m.iter().map(|&b| if b { '1' } else { '0' }).collect()
    }
}

pub fn opt_count(a: &grammar::Alt) -> usize {
    a.rhs.iter().filter(|i| matches!(i, Item::Sym(_, true))).count()
}

fn colons_text(c: Colons) -> &'static str {
    match c {
        Colons::One => ":",
        Colons::Two => "::",
        Colons::Three => ":::",
    }
}

/// A symbol as a key writes it: its name, without arguments.
fn sym_key(s: &Sym) -> String {
    match s {
        Sym::T(t) => grammar::terminal_text(t),
        Sym::Nt(n, _) => n.clone(),
    }
}

/// An item of one right-hand side as a key writes it (§5.2.2: without the
/// "[ ]" annotations), or none for an annotation.
pub fn item_key(i: &Item, present: bool) -> Option<String> {
    match i {
        Item::Sym(s, _) => present.then(|| sym_key(s)),
        Item::ButNot(b, e) => Some(format!(
            "{} but not {}",
            sym_key(b),
            match e {
                Exclusion::Sym(s) => sym_key(s),
                Exclusion::OneOf(ss, _) =>
                    format!("one of {}", ss.iter().map(sym_key).collect::<Vec<_>>().join(" ")),
            }
        )),
        Item::Phrase(p) => Some(format!("> {p}")),
        Item::Look(_) | Item::NoLT | Item::Empty | Item::OnlyIf(_) => None,
    }
}

/// The symbols of a right-hand side of `items` with optional symbols present
/// per `mask`, as a key writes them.
pub fn shape(items: &[Item], mask: &[bool]) -> Vec<String> {
    let mut k = 0;
    let mut out = Vec::new();
    for i in items {
        let present = match i {
            Item::Sym(_, true) => {
                k += 1;
                mask[k - 1]
            }
            _ => true,
        };
        out.extend(item_key(i, present));
    }
    out
}

impl Gl {
    /// spec.html's grammars, and json.emu's JSON grammar if given (its
    /// nonterminals and productions met after spec.html's), numbered in the
    /// order met (no kept tables).
    pub fn load(text: &str, json: Option<&str>) -> Result<Gl, String> {
        Gl::load_with(text, json, &KeptIds::default())
    }

    /// As `load`, numbered by the kept tables `kept`.
    pub fn load_with(text: &str, json: Option<&str>, kept: &KeptIds) -> Result<Gl, String> {
        let spec = spec::scan(text)?;
        let mut blocks = Vec::new();
        for b in &spec.blocks {
            let first = if b.text.starts_with('\n') { b.line } else { b.line - 1 };
            let rules = grammar::parse_block(&b.text, first)?;
            let colons: BTreeSet<_> = rules.iter().map(|r| r.colons as u8).collect();
            if colons.len() != 1 {
                return Err(format!("spec.html:{}: a block mixing grammars", b.line));
            }
            let g = match (&b.prose, rules[0].colons) {
                (Prose::Overlay { .. }, _) => G::AnnexB,
                (_, Colons::Three) => G::NumericString,
                (_, Colons::One) => G::Syntactic,
                (Prose::Supplemental { .. }, _) => {
                    return Err(format!(
                        "spec.html:{}: a supplemental grammar outside the syntactic grammar",
                        b.line
                    ))
                }
                (_, Colons::Two) if b.clause == "sec-patterns" => G::RegExp,
                (_, Colons::Two) => G::Lexical,
            };
            let indent = grammar::layout(&b.text, &rules)
                .ok_or_else(|| format!("spec.html:{}: a block laid out in a way this generator does not know", b.line))?;
            blocks.push(Block {
                file: "spec.html",
                clause: b.clause.clone(),
                line: b.line,
                prose: b.prose.clone(),
                g,
                rules,
                indent,
            });
        }

        let main = blocks.len();
        let mut json_goal = None;
        if let Some(jt) = json {
            const GOAL: &str = "its goal symbol is |";
            let at = jt.find(GOAL).ok_or("json.emu: no \"its goal symbol is |X|\"")?;
            let rest = &jt[at + GOAL.len()..];
            let n = &rest[..rest.find('|').ok_or("json.emu: an unclosed goal symbol")?];
            json_goal = Some((n.to_string(), jt[..at].matches('\n').count() + 1));
            for b in spec::scan(jt)?.blocks {
                let first = if b.text.starts_with('\n') { b.line } else { b.line - 1 };
                let at = |e: String| format!("json.emu:{}: {}", b.line, e.strip_prefix("spec.html:").unwrap_or(&e));
                let rules = grammar::parse_block(&b.text, first).map_err(at)?;
                if !matches!(b.prose, Prose::Main) || rules.iter().any(|r| r.colons != Colons::Two || !r.params.is_empty()) {
                    return Err(at("a JSON block that is not lexical (`::`, no parameters)".into()));
                }
                let indent = grammar::layout(&b.text, &rules)
                    .ok_or_else(|| at("a block laid out in a way this generator does not know".into()))?;
                blocks.push(Block {
                    file: "json.emu",
                    clause: b.clause.clone(),
                    line: b.line,
                    prose: b.prose.clone(),
                    g: G::Json,
                    rules,
                    indent,
                });
            }
        }

        let mut nts: Vec<String> = Vec::new();
        let mut params: Vec<String> = Vec::new();
        let add = |v: &mut Vec<String>, n: &str| {
            if !v.iter().any(|x| x == n) {
                v.push(n.to_string());
            }
        };
        // spec.html's, then json.emu's: each one's definitions, then the nonterminals it only references.
        for part in [&blocks[..main], &blocks[main..]] {
            for b in part {
                for r in &b.rules {
                    add(&mut nts, &r.lhs);
                    for p in &r.params {
                        add(&mut params, p);
                    }
                }
            }
            let mut referenced = Vec::new();
            for b in part {
                for r in &b.rules {
                    if let Body::Alts(alts) = &r.body {
                        for a in alts {
                            a.rhs.iter().for_each(|i| item_nts(i, &mut referenced));
                        }
                    }
                }
            }
            for n in &referenced {
                add(&mut nts, n);
            }
        }

        let renumber = |names: &[String], k: Option<&crate::ids::Kept>, what: &str| -> Result<Numbering, String> {
            let mut n = Numbering::new(k);
            for x in names {
                n.number(x);
            }
            match n.names.iter().position(String::is_empty) {
                Some(i) => Err(format!("{what} {i} has no name in the kept table")),
                None => Ok(n),
            }
        };
        let nt_numbering = renumber(&nts, kept.nts.as_ref(), "nonterminal id")?;
        let param_numbering = renumber(&params, kept.params.as_ref(), "parameter id")?;
        let (nts, nt_live) = (nt_numbering.names.clone(), nt_numbering.met.clone());
        let (params, param_live) = (param_numbering.names.clone(), param_numbering.met.clone());

        let mut by_g: BTreeMap<G, Vec<(usize, usize)>> = BTreeMap::new();
        for (bi, b) in blocks.iter().enumerate() {
            for ri in 0..b.rules.len() {
                by_g.entry(b.g).or_default().push((bi, ri));
            }
        }
        for (g, rs) in &by_g {
            let mut seen = BTreeSet::new();
            for &(bi, ri) in rs {
                let r = &blocks[bi].rules[ri];
                if !seen.insert(&r.lhs) {
                    return Err(format!(
                        "{}:{}: {} is defined twice in the {} grammar",
                        blocks[bi].file,
                        r.line,
                        r.lhs,
                        g.name()
                    ));
                }
            }
        }

        let mut prods = Vec::new();
        for (g, rs) in &by_g {
            let mut ctor = 0;
            for &(bi, ri) in rs {
                let r = &blocks[bi].rules[ri];
                let lhs = nts.iter().zip(&nt_live).position(|(n, &l)| l && *n == r.lhs).unwrap();
                let opts: Vec<usize> = match &r.body {
                    Body::Alts(alts) => alts.iter().map(opt_count).collect(),
                    Body::OneOf(rows) => vec![0; rows.iter().map(|r| r.len()).sum()],
                };
                for (alt, k) in opts.into_iter().enumerate() {
                    for mask in masks(k) {
                        prods.push(Prod {
                            g: *g,
                            at: At { block: bi, rule: ri, alt },
                            lhs,
                            ctor,
                            mask,
                        });
                    }
                    ctor += 1;
                }
            }
        }

        let mut gl = Gl {
            spec,
            blocks,
            nts,
            nt_live,
            params,
            param_live,
            by_g,
            prods,
            prod_ids: Vec::new(),
            prod_numbering: Numbering::new(kept.prods.as_ref()),
            nt_numbering,
            param_numbering,
            json_goal,
        };
        gl.check_prodrefs()?;
        let keys: Vec<String> = gl.prods.iter().map(|p| gl.prod_key(p)).collect();
        gl.prod_ids = keys.iter().map(|k| gl.prod_numbering.number(k)).collect();
        if let Some(i) = gl.prod_numbering.names.iter().position(String::is_empty) {
            return Err(format!("production id {i} has no name in the kept table"));
        }
        Ok(gl)
    }

    /// Annex A's `<emu-prodref>`s name definitions (and their labels).
    fn check_prodrefs(&self) -> Result<(), String> {
        for p in &self.spec.prodrefs {
            let mut found = None;
            for b in self.blocks.iter().filter(|b| b.g != G::AnnexB && b.g != G::Json) {
                for r in b.rules.iter().filter(|r| r.lhs == p.name) {
                    found = Some(r);
                }
            }
            let r = found
                .ok_or_else(|| format!("spec.html:{}: emu-prodref {} names no definition", p.line, p.name))?;
            if let Some(l) = &p.label {
                let ok = match &r.body {
                    Body::Alts(a) => a.iter().any(|a| a.label.as_deref() == Some(l)),
                    Body::OneOf(_) => false,
                };
                if !ok {
                    return Err(format!(
                        "spec.html:{}: emu-prodref {} names no alternative #{l}",
                        p.line, p.name
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn rule(&self, at: At) -> &Rule {
        &self.blocks[at.block].rules[at.rule]
    }

    /// The written alternative, or none for a `one of` terminal.
    pub fn alt(&self, at: At) -> Option<&grammar::Alt> {
        match &self.rule(at).body {
            Body::Alts(a) => Some(&a[at.alt]),
            Body::OneOf(_) => None,
        }
    }

    /// A `one of` terminal.
    pub fn terminal(&self, at: At) -> Option<&Terminal> {
        match &self.rule(at).body {
            Body::OneOf(rows) => rows.iter().flatten().nth(at.alt),
            Body::Alts(_) => None,
        }
    }

    /// The written production's name: `Lhs : alternative` (without its label),
    /// as the `Production` constructors are named.
    pub fn name(&self, at: At) -> String {
        let r = self.rule(at);
        let rhs = match self.alt(at) {
            Some(a) => a.text.clone(),
            None => grammar::terminal_text(self.terminal(at).unwrap()),
        };
        format!("{} {} {rhs}", r.lhs, colons_text(r.colons))
    }

    /// A right-hand side's symbols, as a key writes them.
    pub fn shape(&self, p: &Prod) -> Vec<String> {
        match self.alt(p.at) {
            Some(a) => shape(&a.rhs, &p.mask),
            None => vec![grammar::terminal_text(self.terminal(p.at).unwrap())],
        }
    }

    /// A right-hand side's key in the kept table: `GRAMMAR MASK NAME`.
    pub fn prod_key(&self, p: &Prod) -> String {
        format!("{} {} {}", p.g.name(), mask_text(&p.mask), self.name(p.at))
    }

    /// The kept id of the right-hand side at position `pos` of `prods`.
    pub fn kept_id(&self, pos: usize) -> ProdId {
        self.prod_ids[pos]
    }

    /// The index lines of the numbering, in `prods`' order: `ID GRAMMAR MASK NAME`, the kept id.
    pub fn prod_lines(&self) -> Vec<String> {
        self.prods.iter().zip(&self.prod_ids).map(|(p, id)| format!("{id} {}", self.prod_key(p))).collect()
    }

    /// The right-hand sides' keys by kept id, up to the last this grammar has ("" for a number no
    /// entry has): the names a table of the ids lists.
    pub fn prod_names(&self) -> Vec<String> {
        let last = self.prod_ids.iter().max().map_or(0, |m| m + 1);
        self.prod_numbering.names[..last].to_vec()
    }

    /// The nonterminals by kept id, up to the last this grammar has.
    pub fn live_nts(&self) -> &[String] {
        &self.nts[..self.nt_live.iter().rposition(|&l| l).map_or(0, |i| i + 1)]
    }

    /// The parameters by kept id, up to the last this grammar has.
    pub fn live_params(&self) -> &[String] {
        &self.params[..self.param_live.iter().rposition(|&l| l).map_or(0, |i| i + 1)]
    }

    /// Whether `clause` is `ancestor` or inside it.
    pub fn within(&self, clause: &str, ancestor: &str) -> bool {
        let mut c = clause;
        loop {
            if c == ancestor {
                return true;
            }
            match self.spec.parents.get(c) {
                Some(p) => c = p,
                None => return false,
            }
        }
    }
}

/// The nonterminals an item names.
pub fn item_nts(i: &Item, out: &mut Vec<String>) {
    let mut sym = |s: &Sym| {
        if let Sym::Nt(n, _) = s {
            out.push(n.clone());
        }
    };
    match i {
        Item::Sym(s, _) => sym(s),
        Item::ButNot(b, e) => {
            sym(b);
            match e {
                Exclusion::Sym(s) => sym(s),
                Exclusion::OneOf(ss, _) => ss.iter().for_each(sym),
            }
        }
        Item::Look(grammar::Lookahead::NotMemNT(n)) => out.push(n.clone()),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPEC: &str = "<emu-clause id=\"sec-a\">\n<emu-grammar type=\"definition\">\n  P[Yield] :\n    `x` Q?\n    [+Yield] `y`\n\n  Q :\n    `q`\n</emu-grammar>\n</emu-clause>\n";

    #[test]
    fn kept_ids_keep_numbers_and_retire() {
        let plain = Gl::load(SPEC, None).unwrap();
        assert_eq!(plain.prod_ids, vec![0, 1, 2, 3]);
        assert_eq!(plain.prod_lines()[1], "1 Syntactic 1 P : `x` Q?");
        // a table from an older text: `y` was 0, a gone `z` 1, a gone nonterminal R 1
        let k = |s: &str| Some(crate::ids::parse("t", s).unwrap());
        let kept = KeptIds {
            prods: k("0\tSyntactic - P : [+Yield] `y`\n1\tSyntactic - P : `z`\n"),
            nts: k("0\tQ\n1\tR\n"),
            params: None,
        };
        let gl = Gl::load_with(SPEC, None, &kept).unwrap();
        assert_eq!(gl.prod_ids, vec![2, 3, 0, 4]);
        assert!(gl.prod_numbering.retired(1) && gl.prod_numbering.next() == 5);
        assert_eq!(gl.nts, vec!["Q", "R", "P"]);
        assert_eq!(gl.nt_live, vec![true, false, true]);
        assert_eq!(gl.nt("R"), None);
        assert_eq!(gl.prods[0].lhs, 2);
        assert_eq!(gl.live_nts(), ["Q", "R", "P"]);
        assert_eq!(gl.prod_names()[1], "Syntactic - P : `z`");
    }

    #[test]
    fn mask_order() {
        assert_eq!(masks(0), vec![Vec::<bool>::new()]);
        assert_eq!(
            masks(2),
            vec![vec![false, false], vec![false, true], vec![true, false], vec![true, true]]
        );
    }
}
