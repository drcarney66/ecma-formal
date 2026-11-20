//! The kept grammar ids (`spec/formal/prod-ids.txt`, `nt-ids.txt`, `param-ids.txt`): a number per
//! production, nonterminal and parameter, so that a change to the grammar renumbers nothing it does not
//! change.
//!
//! A table is `#` comment lines, then a line `N<TAB>name` per id in id order, as crates/spec-gen's kept
//! tables (its `ids.rs`); one the grammar no longer has keeps its number, marked `<TAB>retired`. A
//! production's name is its key `GRAMMAR MASK Lhs : rhs` (the index's `prod` lines without the id): an
//! edited right-hand side is a new production, the old one retired. `Gl::load_with` gives each name met
//! its number and each new name the next unused number, in the order GL meets them (so with no table the
//! numbering is GL's own order), and `jsgrammar --out` writes the tables back (`scripts/jsgrammar.py
//! --write`).

use std::collections::HashMap;

pub const PROD_IDS: &str = "prod-ids.txt";
pub const NT_IDS: &str = "nt-ids.txt";
pub const PARAM_IDS: &str = "param-ids.txt";

pub fn header(file: &str) -> &'static str {
    match file {
        PROD_IDS => "# The production ids (`ProdId`; `Ecma.Grammar.Gen.prodIds`, `Ecma.Gen.prods`), by the right-hand side's key
# `GRAMMAR MASK Lhs : rhs` (tests/parser/grammar_index.txt's `prod` lines): its grammar, the presences of its
# optional symbols, its written production. An edited right-hand side is a new production.
# The generator gives a right-hand side met its number here and a new one the next unused number, and writes
# this file (scripts/jsgrammar.py --write); one the grammar no longer has keeps its number, marked retired.
# Do not renumber or reuse a line by hand.",
        NT_IDS => "# The nonterminal ids (`NtId`: the constructor index of `Ecma.Grammar.NT`; `Ecma.Gen.nts`), by name.
# The generator gives a nonterminal met its number here and a new one the next unused number, and writes this
# file (scripts/jsgrammar.py --write); one the grammar no longer has keeps its number, marked retired, and its
# constructor (`NT.retired_Name`). Do not renumber or reuse a line by hand.",
        PARAM_IDS => "# The grammatical parameter ids (`ParamId`: the constructor index of `Ecma.Grammar.Param`; `Ecma.Gen.params`),
# by name. The generator gives a parameter met its number here and a new one the next unused number, and writes
# this file (scripts/jsgrammar.py --write); one the grammar no longer has keeps its number, marked retired, and
# its constructor (`Param.retired_Name`). Do not renumber or reuse a line by hand.",
        _ => "",
    }
}

/// A kept table as read: each entry's number and name, in id order.
#[derive(Clone, Debug, Default)]
pub struct Kept {
    pub entries: Vec<(usize, String)>,
}

/// The three grammar tables, each if it exists.
#[derive(Clone, Debug, Default)]
pub struct KeptIds {
    pub prods: Option<Kept>,
    pub nts: Option<Kept>,
    pub params: Option<Kept>,
}

/// The table `text` (named `path` in errors).
pub fn parse(path: &str, text: &str) -> Result<Kept, String> {
    let mut k = Kept::default();
    let mut names = std::collections::HashSet::new();
    for (n, l) in text.lines().enumerate() {
        if l.starts_with('#') || l.is_empty() {
            continue;
        }
        let bad = |why: &str| format!("{path}:{}: {why}: {l}", n + 1);
        let mut f = l.split('\t');
        let id: usize = f.next().and_then(|x| x.parse().ok()).ok_or_else(|| bad("not `N<TAB>name`"))?;
        let name = f.next().filter(|x| !x.is_empty()).ok_or_else(|| bad("no name"))?.to_string();
        if f.any(|x| x != "retired") {
            return Err(bad("a third field other than `retired`"));
        }
        if k.entries.last().is_some_and(|e| e.0 >= id) {
            return Err(bad("not in increasing id order"));
        }
        if !names.insert(name.clone()) {
            return Err(bad("a second line for the name"));
        }
        k.entries.push((id, name));
    }
    Ok(k)
}

/// The tables in directory `dir` (absent ones none).
pub fn read_dir(dir: &std::path::Path) -> Result<KeptIds, String> {
    let read = |f: &str| -> Result<Option<Kept>, String> {
        let p = dir.join(f);
        match std::fs::read_to_string(&p) {
            Ok(s) => parse(&p.display().to_string(), &s).map(Some),
            Err(_) => Ok(None),
        }
    };
    Ok(KeptIds { prods: read(PROD_IDS)?, nts: read(NT_IDS)?, params: read(PARAM_IDS)? })
}

/// A numbering by a kept table: a name in it keeps its number, a new name takes the next number after
/// every number the table has.
#[derive(Clone, Debug, Default)]
pub struct Numbering {
    /// By id: the name ("" for a number no entry has).
    pub names: Vec<String>,
    /// By id: whether this run met the name.
    pub met: Vec<bool>,
    index: HashMap<String, usize>,
}

impl Numbering {
    pub fn new(kept: Option<&Kept>) -> Numbering {
        let mut n = Numbering::default();
        for (id, name) in kept.map(|k| k.entries.as_slice()).unwrap_or_default() {
            if n.names.len() <= *id {
                n.names.resize(id + 1, String::new());
            }
            n.names[*id] = name.clone();
            n.index.insert(name.clone(), *id);
        }
        n.met = vec![false; n.names.len()];
        n
    }

    /// The number of `name`, met.
    pub fn number(&mut self, name: &str) -> usize {
        if let Some(&i) = self.index.get(name) {
            self.met[i] = true;
            return i;
        }
        self.names.push(name.to_string());
        self.met.push(true);
        self.index.insert(name.to_string(), self.names.len() - 1);
        self.names.len() - 1
    }

    /// The number past every id.
    pub fn next(&self) -> usize {
        self.names.len()
    }

    /// Whether `i` is a number the table has that this run did not meet: a name the grammar no longer has.
    pub fn retired(&self, i: usize) -> bool {
        !self.met[i] && !self.names[i].is_empty()
    }

    /// The table's text: every number with a name, retired where this run did not meet it.
    pub fn render(&self, file: &str) -> String {
        let mut o = String::new();
        o.push_str(header(file));
        o.push('\n');
        for (i, n) in self.names.iter().enumerate().filter(|(_, n)| !n.is_empty()) {
            o.push_str(&format!("{i}\t{n}"));
            if self.retired(i) {
                o.push_str("\tretired");
            }
            o.push('\n');
        }
        o
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kept_new_and_retired() {
        let k = parse("t", "# h\n0\ta\n1\tb\n3\tc\tretired\n").unwrap();
        let mut n = Numbering::new(Some(&k));
        assert_eq!(n.number("b"), 1);
        assert_eq!(n.number("d"), 4);
        assert_eq!(n.number("c"), 3);
        assert_eq!(n.next(), 5);
        assert!(n.retired(0) && !n.retired(1) && !n.retired(2) && !n.retired(3));
        let out = n.render(NT_IDS);
        let body: Vec<&str> = out.lines().filter(|l| !l.starts_with('#')).collect();
        assert_eq!(body, ["0\ta\tretired", "1\tb", "3\tc", "4\td"]);
        let again = parse("t", &out).unwrap();
        assert_eq!(again.entries.len(), 4);
    }

    #[test]
    fn no_table_is_the_order_met() {
        let mut n = Numbering::new(None);
        assert_eq!((n.number("x"), n.number("y"), n.number("x")), (0, 1, 0));
    }

    #[test]
    fn bad_tables_are_refused() {
        for bad in ["1\tx\n0\ty\n", "0\tx\n1\tx\n", "0\n", "x\ty\n", "0\tx\tgone\n"] {
            assert!(parse("t", bad).is_err(), "{bad:?}");
        }
    }
}
