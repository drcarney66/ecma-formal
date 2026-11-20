//! The key resolver: the productions a non-definition `<emu-grammar>` block
//! names (an SDO row's key, an early-error rule's, a production in a step or
//! in prose), as positions in GL's `prods` (`Gl::kept_id` gives their ids).
//!
//! A key line is `Lhs : rhs` (or `::`, `:::`), or a heading `Lhs :` with its
//! alternatives on the lines below, or a whole `Lhs :: one of …` definition.
//! It is written without the "[ ]" annotations as a rule (§5.2.2), and its
//! optional symbols stand for both of their presences, so it names every
//! right-hand side of its left-hand side whose symbols, as a key writes them,
//! are one of the key's expansions; each expansion must name at least one.
//! The grammar is the one the colons and the clause give: an Annex B
//! overlay's definition of the left-hand side inside that overlay's section,
//! else the main grammar's (`::` in the RegExp chapter or B.1.2 is RegExp's
//! where both define it). A main grammar key also names the right-hand sides
//! of the same shape in an overlay that redefines its left-hand side: the
//! overlays modify and extend the main grammar (§B.1.1, §B.1.2), whose rules
//! apply to the productions they keep.

use crate::gl::{masks, shape, Gl, Prod, ProdId, G};
use crate::grammar::{self, Colons, Item};
use std::collections::BTreeSet;

/// The RegExp chapter and Annex B's RegExp section.
const REGEXP_CLAUSES: &[&str] = &["sec-regexp-regular-expression-objects", "sec-regular-expressions-patterns"];

/// One production line of a key block, and what it names.
#[derive(Clone, Debug)]
pub struct KeyLine {
    pub lhs: String,
    pub colons: Colons,
    /// The right-hand sides it names, in id order.
    pub ids: Vec<ProdId>,
}

/// `Name[…] :` with what follows the colons: (lhs, colons, rest).
fn heading(line: &str) -> Option<(String, Colons, &str)> {
    let n = line.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))?;
    if n == 0 || !line.starts_with(|c: char| c.is_ascii_alphabetic()) {
        return None;
    }
    let lhs = &line[..n];
    let mut rest = &line[n..];
    if rest.starts_with('[') {
        rest = &rest[rest.find(']')? + 1..];
    }
    let (colons, rest) = if let Some(r) = rest.strip_prefix(" :::") {
        (Colons::Three, r)
    } else if let Some(r) = rest.strip_prefix(" ::") {
        (Colons::Two, r)
    } else if let Some(r) = rest.strip_prefix(" :") {
        (Colons::One, r)
    } else {
        return None;
    };
    if !(rest.is_empty() || rest.starts_with(' ')) {
        return None;
    }
    Some((lhs.to_string(), colons, rest.trim_start()))
}

/// The terminals of a `one of` row: `` `a` `b` ``.
fn one_of_row(s: &str) -> Result<Vec<String>, String> {
    let a = grammar::parse_alt(s)?;
    a.rhs
        .iter()
        .map(|i| match i {
            Item::Sym(grammar::Sym::T(t), false) => Ok(grammar::terminal_text(t)),
            _ => Err(format!("not a `one of` row: {s}")),
        })
        .collect()
}

/// A key line's expansions: the symbol lists it names.
fn expansions(rhs: &str) -> Result<BTreeSet<Vec<String>>, String> {
    let a = grammar::parse_alt(rhs)?;
    let k = crate::gl::opt_count(&a);
    Ok(masks(k).iter().map(|m| shape(&a.rhs, m)).collect())
}

impl Gl {
    /// The right-hand sides of `lhs` with `colons` that satisfy `pred`.
    fn of(&self, lhs: &str, colons: Colons, pred: impl Fn(&Prod) -> bool) -> Vec<ProdId> {
        (0..self.prods.len())
            .filter(|&i| {
                let p = &self.prods[i];
                let r = self.rule(p.at);
                r.lhs == lhs && r.colons == colons && pred(p)
            })
            .collect()
    }

    /// The right-hand sides of `lhs` with `colons` that a key in `clause` may
    /// name, and whether they are the main grammar's.
    fn candidates(&self, lhs: &str, colons: Colons, clause: &str) -> (Vec<ProdId>, bool) {
        let overlay = self.of(lhs, colons, |p| {
            p.g == G::AnnexB && self.within(clause, &self.blocks[p.at.block].clause)
        });
        if !overlay.is_empty() {
            return (overlay, false);
        }
        (self.main_candidates(lhs, colons, clause), true)
    }

    /// The right-hand sides of `lhs` with `colons` in the overlays of main grammar `base`
    /// (B.1.2 overlays RegExp's, B.1.1 the lexical grammar's).
    fn overlay_of(&self, lhs: &str, colons: Colons, base: G) -> Vec<ProdId> {
        self.of(lhs, colons, |p| {
            p.g == G::AnnexB && (base == G::RegExp) == REGEXP_CLAUSES.iter().any(|c| self.within(&self.blocks[p.at.block].clause, c))
        })
    }

    /// The main grammar's right-hand sides of `lhs` with `colons` for a key in `clause`.
    fn main_candidates(&self, lhs: &str, colons: Colons, clause: &str) -> Vec<ProdId> {
        let main = |g: G| self.of(lhs, colons, |p| p.g == g);
        match colons {
            Colons::One => main(G::Syntactic),
            Colons::Three => main(G::NumericString),
            Colons::Two => {
                let (lex, re) = (main(G::Lexical), main(G::RegExp));
                if lex.is_empty() || re.is_empty() {
                    if lex.is_empty() {
                        re
                    } else {
                        lex
                    }
                } else if REGEXP_CLAUSES.iter().any(|c| self.within(clause, c)) {
                    re
                } else {
                    lex
                }
            }
        }
    }

    /// The right-hand sides among `cands` whose symbols are one of `exps`;
    /// every expansion must name one.
    fn matching(&self, cands: &[ProdId], exps: &BTreeSet<Vec<String>>) -> Result<Vec<ProdId>, String> {
        let mut ids = Vec::new();
        let mut hit = BTreeSet::new();
        for &id in cands {
            let s = self.shape(&self.prods[id]);
            if exps.contains(&s) {
                ids.push(id);
                hit.insert(s);
            }
        }
        if let Some(e) = exps.iter().find(|e| !hit.contains(*e)) {
            return Err(format!("no right-hand side `{}`", e.join(" ")));
        }
        Ok(ids)
    }

    /// The production lines of the key block `text` in `clause`, resolved.
    pub fn resolve_lines(&self, text: &str, clause: &str) -> Result<Vec<KeyLine>, String> {
        let mut out = Vec::new();
        // The heading the following alternative lines belong to.
        let mut cur: Option<(String, Colons, bool)> = None;
        for l in text.split('\n') {
            let t = l.trim();
            if t.is_empty() || t.starts_with("// ") {
                continue;
            }
            if t.ends_with(' ') {
                return Err(format!("trailing white space in `{t}`"));
            }
            let (lhs, colons, rhs, one_of) = match heading(t) {
                Some((lhs, colons, rest)) => {
                    let (one_of, rest) = match rest.strip_prefix("one of") {
                        Some(r) if r.is_empty() || r.starts_with(' ') => (true, r.trim_start()),
                        _ => (false, rest),
                    };
                    cur = Some((lhs.clone(), colons, one_of));
                    if rest.is_empty() {
                        continue;
                    }
                    (lhs, colons, rest, one_of)
                }
                None => {
                    let (lhs, colons, one_of) = cur.clone().ok_or_else(|| format!("an alternative before any heading: `{t}`"))?;
                    (lhs, colons, t, one_of)
                }
            };
            let (mut cands, mut main) = self.candidates(&lhs, colons, clause);
            // a nonterminal only an overlay defines: its productions in the overlay of the clause's main grammar
            if cands.is_empty() && colons == Colons::Two {
                let base = if REGEXP_CLAUSES.iter().any(|c| self.within(clause, c)) { G::RegExp } else { G::Lexical };
                (cands, main) = (self.overlay_of(&lhs, colons, base), false);
            }
            if cands.is_empty() {
                return Err(format!("no definition of {lhs} with these colons for clause {clause}"));
            }
            let exps: BTreeSet<Vec<String>> = if one_of {
                one_of_row(rhs)?.into_iter().map(|t| vec![t]).collect()
            } else {
                expansions(rhs)?
            };
            let mut ids = self.matching(&cands, &exps).map_err(|e| format!("{lhs} {e}"))?;
            if main {
                let base = self.prods[cands[0]].g;
                ids.extend(self.overlay_of(&lhs, colons, base).into_iter().filter(|&id| exps.contains(&self.shape(&self.prods[id]))));
            }
            out.push(KeyLine { lhs, colons, ids });
        }
        if out.is_empty() {
            return Err("an empty key".into());
        }
        Ok(out)
    }

    /// The right-hand sides a key block names, in the order of its lines.
    pub fn resolve(&self, text: &str, clause: &str) -> Result<Vec<ProdId>, String> {
        let mut ids = Vec::new();
        for l in self.resolve_lines(text, clause)? {
            for id in l.ids {
                if !ids.contains(&id) {
                    ids.push(id);
                }
            }
        }
        Ok(ids)
    }

    /// The nonterminal named `n`, if the grammar has it.
    pub fn nt(&self, n: &str) -> Option<usize> {
        self.nts.iter().zip(&self.nt_live).position(|(x, &l)| l && x == n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPEC: &str = "<emu-clause id=\"sec-a\">\n<emu-grammar type=\"definition\">\n  P[Yield] :\n    `[` E? R[?Yield]? `]`\n    [+Yield] `x`\n</emu-grammar>\n</emu-clause>\n";

    #[test]
    fn keys_name_opt_expansions() {
        let gl = Gl::load(SPEC, None).unwrap();
        // `[` E? R? `]` is ids 0..4 (masks 00, 01, 10, 11), `x` is 4.
        assert_eq!(gl.resolve("P : `[` E? `]`", "sec-a").unwrap(), vec![0, 2]);
        assert_eq!(gl.resolve("P : `[` E? R `]`", "sec-a").unwrap(), vec![1, 3]);
        assert_eq!(gl.resolve("\n  P :\n    `x`\n    `[` `]`\n", "sec-a").unwrap(), vec![4, 0]);
        assert!(gl.resolve("P : `[` R R `]`", "sec-a").is_err());
        assert!(gl.resolve("Q : `x`", "sec-a").is_err());
    }
}
