//! Every step of every algorithm parsed and classed: fully structured (S),
//! NOTE, skeleton with prose holes (K), or unrecognized (U).

use crate::engine::{emit, visit, Node, Parser};
use crate::grammar::Grammar;
use crate::spec::{Alg, Spec, Step};
use crate::token::{join, tokenize, Tok};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Class {
    S,
    Note,
    K,
    U,
}

pub struct Row<'a> {
    pub alg: &'a Alg,
    pub step: &'a Step,
    pub path: String,
    pub toks: Vec<Tok>,
    pub class: Class,
    pub tree: Option<Rc<Node>>,
    /// the bullet items' trees (continuation `* ` lines), if any
    pub bullets: Vec<(String, Vec<Tok>, Option<Rc<Node>>)>,
}

/// An equation bullet parsed.
pub struct EqRow<'a> {
    pub eq: &'a crate::spec::Eq,
    pub toks: Vec<Tok>,
    pub class: Class,
    pub tree: Option<Rc<Node>>,
}

pub fn classify_eqs<'a>(spec: &'a Spec, g: &Grammar) -> Vec<EqRow<'a>> {
    let mut strict = Parser::new(g, 99, false);
    let mut skel = Parser::new(g, 99, true);
    spec.eqs
        .iter()
        .map(|e| {
            let toks = tokenize(&e.text);
            let (class, tree) = match strict.parse(&toks, "EQ") {
                Some(t) => (Class::S, Some(t)),
                None => match skel.parse(&toks, "EQ") {
                    Some(t) => (Class::K, Some(t)),
                    None => (Class::U, None),
                },
            };
            EqRow { eq: e, toks, class, tree }
        })
        .collect()
}

/// The bullet items of a step's continuation lines.
pub fn bullets(s: &Step) -> Vec<String> {
    s.cont.iter().filter_map(|c| c.trim().strip_prefix("* ").map(str::to_string)).collect()
}

pub fn classify<'a>(spec: &'a Spec, g: &Grammar) -> Vec<Row<'a>> {
    let mut rows = Vec::new();
    for a in spec.algs.iter().filter(|a| !a.example() && !a.tmpl) {
        rows.extend(classify_steps(g, a, &a.steps));
    }
    rows
}

/// The steps of a tree parsed and classed, as steps of `alg`.
pub fn classify_steps<'a>(g: &Grammar, alg: &'a Alg, steps: &'a [Step]) -> Vec<Row<'a>> {
    let mut strict = Parser::new(g, 99, false);
    let mut skel = Parser::new(g, 99, true);
    let mut rows = Vec::new();
    for (path, s) in crate::spec::labelled(steps) {
        let toks = tokenize(&s.text);
        let mut row = Row { alg, step: s, path, toks: toks.clone(), class: Class::U, tree: None, bullets: Vec::new() };
        if let Some(t) = strict.parse(&toks, "Step") {
            row.class = if t.name == "note" { Class::Note } else { Class::S };
            for b in bullets(s) {
                let bt = tokenize(&b);
                let tr = strict.parse(&bt, "E");
                if tr.is_none() {
                    row.class = Class::K;
                }
                row.bullets.push((b, bt, tr));
            }
            row.tree = Some(t);
        } else if let Some(t) = skel.parse(&toks, "Step") {
            row.class = Class::K;
            row.tree = Some(t);
        }
        rows.push(row);
    }
    rows
}

/// A tree printed by the canonical printer.
pub fn print(t: &Node, toks: &[Tok], text: &str) -> String {
    let mut parts = Vec::new();
    emit(t, toks, &mut parts);
    join(&parts, toks, text)
}

/// Whether any node of the tree lost a tie on declaration order only.
pub fn has_tie(t: &Node) -> bool {
    let mut tie = false;
    visit(t, &mut |n| tie |= n.tie);
    tie
}

/// Whether any node of the tree had a competing reading for its span.
pub fn has_alts(t: &Node) -> bool {
    let mut a = false;
    visit(t, &mut |n| a |= n.alts);
    a
}
