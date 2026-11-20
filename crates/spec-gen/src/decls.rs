//! The declaration tables: every name the data refers to, interned to an id
//! (`Ecma.Notation.Decls`), and the phrase table.

use crate::ast::{Hole, Id, TyExpr};
use std::collections::HashMap;

#[derive(Default, Clone)]
pub struct Table {
    pub names: Vec<String>,
    index: HashMap<String, Id>,
    /// the ids a kept table (`seed`) reserved, and whether this run interned each since
    kept: Vec<bool>,
}

impl Table {
    pub fn intern(&mut self, s: &str) -> Id {
        if let Some(&i) = self.index.get(s) {
            if let Some(m) = self.kept.get_mut(i) {
                *m = true;
            }
            return i;
        }
        self.names.push(s.to_string());
        self.index.insert(s.to_string(), self.names.len() - 1);
        self.names.len() - 1
    }

    /// Reserves a kept table's ids (`crate::ids`): each name at its number, a number no entry has
    /// an empty name. A name interned later takes its number; a new name the next number after them.
    pub fn seed(&mut self, kept: &crate::ids::Kept) {
        for e in &kept.entries {
            if self.names.len() <= e.id {
                self.names.resize(e.id + 1, String::new());
            }
            self.names[e.id] = e.name.clone();
            self.index.insert(e.name.clone(), e.id);
        }
        self.kept = vec![false; self.names.len()];
    }

    /// Gives the reserved id of `old` to `new`, which no entry has (`oldids`): its id, if `old` was reserved
    /// and not interned yet.
    pub fn rename(&mut self, old: &str, new: &str) -> Option<Id> {
        let i = *self.index.get(old)?;
        if self.kept.get(i) != Some(&false) || self.index.contains_key(new) {
            return None;
        }
        self.index.remove(old);
        self.index.insert(new.to_string(), i);
        self.names[i] = new.to_string();
        self.kept[i] = true;
        Some(i)
    }

    /// Whether `i` is a reserved id this run did not intern: a name the text no longer has.
    pub fn retired(&self, i: Id) -> bool {
        self.kept.get(i) == Some(&false) && !self.names[i].is_empty()
    }

    pub fn get(&self, s: &str) -> Option<Id> {
        self.index.get(s).copied()
    }

    pub fn name(&self, i: Id) -> &str {
        &self.names[i]
    }
}

/// A template piece of a phrase row.
#[derive(Clone, Debug, PartialEq)]
pub enum Piece {
    Word(String),
    /// a hole of a kind (`HoleKind`)
    Hole(HoleKind),
    /// a choice among piece sequences, selected by a `Hole::W`
    Choice(Vec<Vec<Piece>>),
    /// no space before the next piece
    Glue,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum HoleKind {
    E,
    C,
    T,
    B,
    S,
    L,
    Text,
}

/// An argument of a phrase's meaning.
#[derive(Clone, Debug, PartialEq)]
pub enum PArg {
    /// the phrase's `i`th hole
    Hole(usize),
    /// the phrase's `i`th hole, its last and only list hole: its elements, as the last arguments
    Spread(usize),
    Enum(Id),
    /// a predicate phrase's subject
    Subject,
    /// the Parse Node the SDO row runs at
    ThisNode,
    /// a sort, as a type hole of that sort is
    Sort(Id),
    /// a field or internal slot name
    Field(Id),
    /// an alternative of the primitive's choice, fixed
    Choice(usize),
}

/// What a phrase means: a primitive applied to arguments, possibly negated; or an
/// overlay algorithm (by its clause) applied to the holes, then the subject.
#[derive(Clone, Debug, PartialEq)]
pub enum Meaning {
    Prim { prim: Id, args: Vec<PArg>, neg: bool },
    Alg(Id),
}

/// A data sort's definition: its supersorts, its test on a value (the subject), whether
/// its values are the Records of its kind, and its context phrase.
#[derive(Clone, Debug)]
pub struct SortDef {
    pub sup: Vec<Id>,
    pub test: Option<Meaning>,
    pub record: bool,
    pub ctx: Option<Id>,
}

#[derive(Clone, Debug)]
pub struct Phrase {
    /// the grammar category (Step, P, CA, PRED, T, …)
    pub cat: &'static str,
    pub name: &'static str,
    pub template: Vec<Piece>,
    pub meaning: Option<Meaning>,
}

#[derive(Default, Clone)]
pub struct Decls {
    /// clause ids: the kept table's (`clause-ids.txt`), then new ones in document order
    pub clauses: Table,
    /// each of spec.html's clauses' id here, by its index in `Spec::clauses`, and the reverse
    pub cids: Vec<Id>,
    pub cpos: HashMap<Id, usize>,
    /// the clause ids `oldids` renamed: the names each had before
    pub clause_was: std::collections::BTreeMap<Id, Vec<String>>,
    /// per clause, the operation it defines (`aoid`, or its title), or ""
    pub ops: Vec<String>,
    pub fields: Table,
    pub enums: Table,
    pub sdos: Table,
    pub nts: Table,
    /// GL's grammatical parameters, by ParamId
    pub params: Table,
    /// GL's right-hand sides' keys, by kept id (prod-ids.txt)
    pub prods: Table,
    /// each of GL's right-hand sides' kept id, by its position in `Gl::prods` (the index the data
    /// carries; `crate::lean` prints the id)
    pub prod_ids: Vec<Id>,
    /// the tables' Lean names, by kept table id (`table-ids.txt`)
    pub tables: Table,
    /// each `emu-table`'s kept id, by its index among the scanned tables (the index the data carries;
    /// `crate::lean` prints the id)
    pub table_ids: Vec<Id>,
    pub prims: Table,
    pub sorts: Table,
    pub methods: Table,
    pub phrases: Vec<Phrase>,
    /// the declared sorts' names (`Known`'s and the overlay's), and other forms of them
    /// (plurals, "X event") with the name each folds to
    pub sort_names: std::collections::HashSet<String>,
    pub sort_folds: HashMap<String, String>,
    /// each sort's definition (`spec/formal/sorts.emu`), by SortId; none for the
    /// `Known` sorts, which the value decides
    pub sort_defs: Vec<Option<SortDef>>,
    /// each context sort's context phrase (`<emu-sort context=…>`), by SortId
    pub sort_ctx: HashMap<Id, Id>,
    /// channel (a)'s spec-issue reasons
    pub reasons: Table,
    /// channel (c)'s kinds
    pub notes: Table,
    /// the errata, by name, in the overlay's order (their ids: `erratum_ids`)
    pub errata: Vec<String>,
    /// per erratum, the reading today's model applies
    pub parity: Vec<crate::ast::Reading>,
    /// the errata's overlay ids, in the overlay's order (their ids: `erratum_ids`)
    pub errata_ids: Vec<String>,
    /// per erratum, the readings its overlay or parser defines
    pub erratum_readings: Vec<Vec<crate::ast::Reading>>,
    /// the erratum ids: the kept table's (`erratum-ids.txt`), then new ones in the overlay's order
    pub errata_table: Table,
    /// each overlay erratum's id there, by its index in the overlay (the index the data's nodes carry;
    /// `crate::lean` prints the id)
    pub erratum_ids: Vec<Id>,
    /// where the literal errata stop a run: erratum, clause id, step path (`-`: outside any step),
    /// innermost caller's clause id if named
    pub erratum_stops: Vec<(Id, String, String, Option<String>)>,
    /// the literal errata whose text stops at the job loop's check for a Job the clause makes: clause, erratum
    pub job_errata: Vec<(Id, Id)>,
    /// the residue steps given no meaning on purpose (`<emu-permanent>`): clause or overlay id, step, class
    pub permanent: Vec<(String, String, &'static str)>,
    phrase_ix: HashMap<(&'static str, &'static str), Id>,
    /// primitive calls that do not fit the primitive's signature (`sig::call`): where, and why
    pub sig_errors: Vec<String>,
    /// each `Expr.extreme` emitted: its clause id and its step's text
    pub extremes: Vec<(String, String)>,
    /// each step whose prose a call frame slot replaced: its clause id and text
    pub framed: Vec<(String, String)>,
    /// each SDO's implicit default definition, by SDO: the keyless algorithm of its clause
    pub sdo_defaults: Vec<(Id, Id, usize)>,
    /// each prose fragment's primitive: the primitive, the step, and why it is not applied, if not
    pub wiring: Vec<(Id, String, Option<String>)>,
    /// the clauses a production-in phrase names
    pub prod_clauses: std::collections::BTreeSet<Id>,
    /// each type phrase's bound: the type its test admits only values of, a hole `k` as `Var(_, k)`
    pub type_bounds: HashMap<Id, TyExpr>,
    /// each expression phrase's result typing (`<emu-result-type>`), a hole `k` as `Var(_, k)`
    pub phrase_typings: HashMap<Id, TyExpr>,
    /// each `<emu-result-type>` that does not parse as a header type without declaring a name
    pub typing_errors: Vec<String>,
}

/// `t` with each `Var(_, k)` the type hole `hs[k]`, where that is one.
fn at_holes(t: &TyExpr, hs: &[Hole]) -> TyExpr {
    match t {
        TyExpr::Var(a, k) => match hs.get(*k) {
            Some(Hole::T(x)) => x.clone(),
            _ => TyExpr::Var(a.clone(), *k),
        },
        TyExpr::ListOf(a, x) => TyExpr::ListOf(a.clone(), Box::new(at_holes(x, hs))),
        TyExpr::Union(f, c, ts) => TyExpr::Union(*f, *c, ts.iter().map(|t| at_holes(t, hs)).collect()),
        TyExpr::Completion(x) => TyExpr::Completion(x.as_ref().map(|x| Box::new(at_holes(x, hs)))),
        t => t.clone(),
    }
}

impl Decls {
    /// The clause id of `Spec::clauses[c]`.
    pub fn cid(&self, c: usize) -> Id {
        self.cids[c]
    }

    /// The index in `Spec::clauses` of the clause with id `c`, if spec.html has it.
    pub fn pos(&self, c: Id) -> Option<usize> {
        self.cpos.get(&c).copied()
    }

    /// Records each of spec.html's clauses' id (`cids`).
    pub fn set_cids(&mut self, cids: Vec<Id>) {
        self.cpos = cids.iter().enumerate().map(|(k, &c)| (c, k)).collect();
        self.cids = cids;
    }

    /// Sets clause `c`'s operation.
    pub fn set_op(&mut self, c: Id, op: String) {
        if self.ops.len() <= c {
            self.ops.resize(c + 1, String::new());
        }
        self.ops[c] = op;
    }

    /// Interns a clause id: its kept number, else the kept number of an id it had before (`oldids`) that
    /// no clause has, else the next number.
    pub fn intern_clause(&mut self, id: &str, oldids: &[String]) -> Id {
        if self.clauses.get(id).is_none() {
            for o in oldids {
                if let Some(i) = self.clauses.rename(o, id) {
                    self.clause_was.entry(i).or_default().push(o.clone());
                    return i;
                }
            }
        }
        let i = self.clauses.intern(id);
        if self.ops.len() <= i {
            self.ops.resize(i + 1, String::new());
        }
        i
    }

    /// The bound of the type phrase `p` at the holes `hs`.
    pub fn type_bound(&self, p: Id, hs: &[Hole]) -> Option<TyExpr> {
        self.type_bounds.get(&p).map(|t| at_holes(t, hs))
    }

    /// The result typing of the expression phrase `p` at the holes `hs`.
    pub fn phrase_typing(&self, p: Id, hs: &[Hole]) -> Option<TyExpr> {
        self.phrase_typings.get(&p).map(|t| at_holes(t, hs))
    }

    /// Declares sort names: each one's plural, and "X event(s)" for X, fold to it
    /// unless declared themselves.
    pub fn declare_sorts<'s>(&mut self, names: impl IntoIterator<Item = &'s str>) {
        let names: Vec<&str> = names.into_iter().collect();
        self.sort_names.extend(names.iter().map(|n| n.to_string()));
        for n in names {
            let (stem, last) = n.rsplit_once(' ').map_or(("", n), |(a, b)| (a, b));
            let pre = if stem.is_empty() { String::new() } else { format!("{stem} ") };
            let mut forms = vec![format!("{pre}{last}s"), format!("{n} event"), format!("{n} events")];
            if ["s", "x", "ch", "sh"].iter().any(|e| last.ends_with(e)) {
                forms.push(format!("{pre}{last}es"));
            }
            if let Some(b) = last.strip_suffix('y').filter(|b| !b.ends_with(['a', 'e', 'o', 'u'])) {
                forms.push(format!("{pre}{b}ies"));
            }
            for f in forms {
                if !self.sort_names.contains(&f) {
                    self.sort_folds.entry(f).or_insert_with(|| n.to_string());
                }
            }
        }
    }

    /// The sort a type's words name, and the words as written where they fold to another
    /// name: a declared sort's other form, or `X Records` to `X Record`.
    pub fn sort_of(&mut self, words: &str) -> (Id, String) {
        let fold = self.sort_folds.get(words).cloned().or_else(|| words.strip_suffix(" Records").map(|x| format!("{x} Record")));
        match fold {
            Some(n) => (self.sorts.intern(&n), words.to_string()),
            None => (self.sorts.intern(words), String::new()),
        }
    }

    /// Reserves the frozen phrase ids, in order: a phrase met later takes its id; one
    /// never met stays a row with no template, and a phrase not listed is numbered after them.
    pub fn freeze_phrases(&mut self, ids: &[(String, String)]) {
        for (c, n) in ids {
            let (cat, name): (&'static str, &'static str) = (Box::leak(c.clone().into_boxed_str()), Box::leak(n.clone().into_boxed_str()));
            self.phrases.push(Phrase { cat, name, template: Vec::new(), meaning: None });
            self.phrase_ix.insert((cat, name), self.phrases.len() - 1);
        }
    }

    /// Whether `t that p rest` is a context sort's refinement by its context phrase, which prints as `t`.
    pub fn is_context(&self, t: &crate::ast::TyExpr, p: &crate::ast::Pred, rest: &[(crate::ast::Conj, crate::ast::Pred)]) -> bool {
        match (t, p) {
            (crate::ast::TyExpr::Sort(_, _, s, _), crate::ast::Pred::Phrase(q, _)) => rest.is_empty() && self.sort_ctx.get(s) == Some(q),
            _ => false,
        }
    }

    /// The phrase index: `cat name` per id.
    pub fn phrase_index(&self) -> String {
        self.phrases.iter().map(|p| format!("{} {}\n", p.cat, p.name)).collect()
    }

    pub fn phrase(&mut self, cat: &'static str, name: &'static str, template: impl FnOnce() -> Vec<Piece>) -> Id {
        if let Some(&i) = self.phrase_ix.get(&(cat, name)) {
            if self.phrases[i].template.is_empty() {
                self.phrases[i].template = template();
            }
            return i;
        }
        self.phrases.push(Phrase { cat, name, template: template(), meaning: None });
        self.phrase_ix.insert((cat, name), self.phrases.len() - 1);
        self.phrases.len() - 1
    }
}
