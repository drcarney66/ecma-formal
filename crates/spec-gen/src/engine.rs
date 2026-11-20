//! The template engine: every parse of a category at a position, memoized,
//! with one tree kept per end position by the disambiguation rules:
//!
//! 1. maximal munch: an operator never takes as its left operand a phrase whose
//!    template ends in a hole that could itself have absorbed the operator
//!    (postfix `.[[F]]`, `[i]`, application bind tighter than any phrase);
//! 2. specificity: of two trees for the same span, the one matching more
//!    literal words wins;
//! 3. economy: of two such trees, the one with fewer nodes wins (a template's
//!    own words over the same words matched by a nested phrase);
//! 4. a declared synonym (`sem`) loses to the rule it names.
//!
//! A tie that none of these decides is recorded on the winning node (`tie`),
//! and the report counts them.

use crate::token::{lit_canon, K, Tok};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

pub type Cat = &'static str;

/// A template element.
#[derive(Clone, Debug)]
pub enum El {
    Lit(String),
    Kind(Kc),
    /// a token of a kind and value, and its printed form
    KindV(K, String, String),
    Hole(Cat),
    Opt(Vec<(El, bool)>),
    Alt(Vec<Vec<(El, bool)>>),
}

/// A token-kind constraint.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kc {
    K(K),
    Cap,
    Low,
    Up,
}

pub struct Rule {
    pub idx: usize,
    pub cat: Cat,
    pub name: &'static str,
    pub tier: u8,
    pub sem: Option<&'static str>,
    pub elems: Vec<(El, bool)>,
    first: Option<String>,
    firstkind: Option<Kc>,
}

/// A parse-tree item.
#[derive(Clone, Debug)]
pub enum Item {
    /// a literal of the template (or of a built-in), and its glue
    L(String, bool),
    /// a token, by index
    T(usize, bool),
    N(Rc<Node>, bool),
    /// an optional part: present or absent
    O(Option<Vec<Item>>, bool),
    /// a choice: the alternative taken
    A(usize, Vec<Item>, bool),
    /// a prose span of tokens `[i, j)`
    P(usize, usize, bool),
}

/// What made a node: a template rule, or a built-in production.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rid {
    R(usize),
    B(&'static str),
}

#[derive(Debug)]
pub struct Node {
    pub rid: Rid,
    pub name: &'static str,
    pub items: Vec<Item>,
    /// the tokens covered: `[s, e)`
    pub s: usize,
    pub e: usize,
    /// tokens inside prose spans
    pub prose: u32,
    /// literal words matched
    pub lits: u32,
    /// nodes in the tree
    pub size: u32,
    /// another tree for the same span lost on declaration order only
    pub tie: bool,
    /// some tree for the same span lost (any rule)
    pub alts: bool,
}

fn item_counts(it: &Item) -> (u32, u32, u32) {
    match it {
        Item::L(..) => (0, 1, 0),
        Item::T(..) => (0, 0, 0),
        Item::N(n, _) => (n.prose, n.lits, n.size),
        Item::O(None, _) => (0, 0, 0),
        Item::O(Some(v), _) | Item::A(_, v, _) => v.iter().map(item_counts).fold((0, 0, 0), add3),
        Item::P(i, j, _) => ((j - i) as u32, 0, 0),
    }
}

fn add3(a: (u32, u32, u32), b: (u32, u32, u32)) -> (u32, u32, u32) {
    (a.0 + b.0, a.1 + b.1, a.2 + b.2)
}

pub fn mk(rid: Rid, name: &'static str, items: Vec<Item>, s: usize, e: usize) -> Rc<Node> {
    let (prose, lits, size) = items.iter().map(item_counts).fold((0, 0, 0), add3);
    Rc::new(Node { rid, name, items, s, e, prose, lits, size: size + 1, tie: false, alts: false })
}

/// Template mini-syntax: words; `'x'` a quoted literal; `{Cat}` a hole; `$KIND`
/// a token kind; `$KIND=v` a token of a kind and value; `[ … ]` optional;
/// `( a | b )` a choice; `^` before an element: no space before it.
pub fn compile(s: &str) -> Vec<(El, bool)> {
    let toks = lex_template(s);
    let mut pos = 0;
    let out = seq(&toks, &mut pos, &[]);
    assert!(pos == toks.len(), "template {s:?}: stray {:?}", toks.get(pos));
    out
}

fn lex_template(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let cs: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if "^[]()|".contains(c) {
            out.push(c.to_string());
            i += 1;
        } else if c == '\'' && cs[i + 1..].contains(&'\'') {
            let j = i + 1 + cs[i + 1..].iter().position(|&d| d == '\'').unwrap();
            out.push(cs[i..=j].iter().collect());
            i = j + 1;
        } else if c == '{' {
            let j = i + cs[i..].iter().position(|&d| d == '}').unwrap();
            out.push(cs[i..=j].iter().collect());
            i = j + 1;
        } else {
            let j = (i..cs.len()).find(|&j| cs[j].is_whitespace() || "[]()|{}^".contains(cs[j])).unwrap_or(cs.len());
            out.push(cs[i..j].iter().collect());
            i = j;
        }
    }
    out
}

fn kind_of(s: &str) -> K {
    match s {
        "VAR" => K::Var,
        "VAL" => K::Val,
        "ENUM" => K::Enum,
        "INTR" => K::Intr,
        "NUM" => K::Num,
        "NT" => K::Nt,
        "FIELD" => K::Field,
        "XREF" => K::Xref,
        "WORD" => K::Word,
        "CODE" => K::Code,
        "GRAM" => K::Gram,
        "ALG" => K::Alg,
        "METAO" => K::MetaO,
        "METAC" => K::MetaC,
        "TAG" => K::Tag,
        "PARAM" => K::Param,
        "NOTREFO" => K::NotRefO,
        "NOTREFC" => K::NotRefC,
        _ => panic!("unknown token kind {s}"),
    }
}

fn seq(toks: &[String], pos: &mut usize, stop: &[&str]) -> Vec<(El, bool)> {
    let mut out = Vec::new();
    let mut glue = false;
    while *pos < toks.len() {
        let t = toks[*pos].as_str();
        if stop.contains(&t) {
            return out;
        }
        *pos += 1;
        let el = match t {
            "^" => {
                glue = true;
                continue;
            }
            "[" => {
                let inner = seq(toks, pos, &["]"]);
                *pos += 1;
                El::Opt(inner)
            }
            "(" => {
                let mut alts = vec![seq(toks, pos, &["|", ")"])];
                while toks[*pos] == "|" {
                    *pos += 1;
                    alts.push(seq(toks, pos, &["|", ")"]));
                }
                *pos += 1;
                El::Alt(alts)
            }
            _ if t.starts_with('{') => El::Hole(Box::leak(t[1..t.len() - 1].to_string().into_boxed_str())),
            _ if t.starts_with('$') => match t[1..].split_once('=') {
                Some((k, v)) => {
                    let k = kind_of(k);
                    let text = crate::token::canon(&Tok { k, v: v.to_string(), raw: v.to_string(), sub: None, s: 0, e: 0 });
                    El::KindV(k, v.to_string(), text)
                }
                None => El::Kind(match &t[1..] {
                    "CAP" => Kc::Cap,
                    "LOW" => Kc::Low,
                    "UP" => Kc::Up,
                    k => Kc::K(kind_of(k)),
                }),
            },
            _ if t.len() >= 2 && t.starts_with('\'') && t.ends_with('\'') => El::Lit(t[1..t.len() - 1].to_string()),
            _ => El::Lit(t.to_string()),
        };
        out.push((el, glue));
        glue = false;
    }
    out
}

impl Rule {
    pub fn new(idx: usize, cat: Cat, name: &'static str, tmpl: &str, tier: u8, sem: Option<&'static str>) -> Rule {
        Rule::from_elems(idx, cat, name, compile(tmpl), tier, sem)
    }

    pub fn from_elems(idx: usize, cat: Cat, name: &'static str, elems: Vec<(El, bool)>, tier: u8, sem: Option<&'static str>) -> Rule {
        let first = match elems.first() {
            Some((El::Lit(l), _)) => Some(l.clone()),
            _ => None,
        };
        let firstkind = match elems.first() {
            Some((El::Kind(k), _)) => Some(*k),
            _ => None,
        };
        Rule { idx, cat, name, tier, sem, elems, first, firstkind }
    }
}

pub fn kind_ok(t: &Tok, k: Kc) -> bool {
    match k {
        Kc::K(k) => t.k == k,
        Kc::Cap => t.k == K::Word && t.v.starts_with(|c: char| c.is_uppercase()),
        Kc::Low => t.k == K::Word && t.v.starts_with(|c: char| c.is_lowercase()),
        Kc::Up => {
            let up = |s: &str| s.chars().any(|c| c.is_alphabetic()) && !s.chars().any(|c| c.is_lowercase());
            t.k == K::Word && ((up(&t.v) && t.v.chars().count() > 1) || (t.v.contains('-') && up(&t.v.replace('-', ""))))
        }
    }
}

pub fn lit_ok(t: &Tok, l: &str) -> bool {
    t.v == l && matches!(t.k, K::Word | K::Punct | K::Poss)
}

/// Which operators a hole category absorbs at its right edge.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add,
    Mul,
    Post,
    /// a connective between conditions
    Conj,
    /// a connective between relational conditions
    Conn,
}

fn absorbs(c: Cat, op: Op) -> bool {
    if op == Op::Conj {
        return c == "C";
    }
    if op == Op::Conn {
        return c == "MC";
    }
    match c {
        "E" | "EL" | "ALT" | "Args" => true,
        "Prod" => op != Op::Add,
        "A" | "Post" => op == Op::Post,
        _ => false,
    }
}

/// Whether `nd`'s right edge is a phrase hole that absorbs `op` (maximal munch).
pub fn open_to(g: &crate::grammar::Grammar, nd: &Node, op: Op) -> bool {
    fn items_open(g: &crate::grammar::Grammar, items: &[Item], els: Option<&[(El, bool)]>, op: Op) -> bool {
        let Some(last) = items.last() else { return false };
        let el = els.and_then(|e| e.get(items.len() - 1)).map(|e| &e.0);
        match last {
            Item::N(n, _) => {
                if let Some(El::Hole(c)) = el {
                    if absorbs(c, op) {
                        return true;
                    }
                }
                open_to(g, n, op)
            }
            Item::O(None, _) => items_open(g, &items[..items.len() - 1], els.map(|e| &e[..e.len() - 1]), op),
            Item::O(Some(v), _) => {
                let inner = match el {
                    Some(El::Opt(x)) => Some(x.as_slice()),
                    _ => None,
                };
                items_open(g, v, inner, op)
            }
            Item::A(k, v, _) => {
                let inner = match el {
                    Some(El::Alt(x)) => Some(x[*k].as_slice()),
                    _ => None,
                };
                items_open(g, v, inner, op)
            }
            _ => false,
        }
    }
    match nd.rid {
        Rid::R(r) => items_open(g, &nd.items, Some(&g.rules[r].elems), op),
        Rid::B(_) => {
            // built-ins: through their last child (operands are already precedence-correct)
            match nd.items.last() {
                Some(Item::N(n, _)) => open_to(g, n, op),
                _ => false,
            }
        }
    }
}

/// The categories whose holes may be prose in skeleton mode, for templates of
/// these categories (the statement forms).
pub const PROSE_OK: &[Cat] = &["E", "C", "A", "T", "TN", "Args", "EL"];
const PROSE_OWNERS: &[Cat] = &["Step", "SI", "SIn", "EQ", "ER", "ERI"];

pub type Res = Rc<Vec<(usize, Rc<Node>)>>;

pub struct Parser<'g> {
    pub g: &'g crate::grammar::Grammar,
    pub maxtier: u8,
    pub skeleton: bool,
    /// maximal munch on (off only to find the attachment sites)
    pub munch: bool,
    pub t: Vec<Tok>,
    pub n: usize,
    memo: HashMap<(Cat, usize), Res>,
}

/// Whether `a` beats `b` for the same span, and whether only order decided.
fn better(g: &crate::grammar::Grammar, a: &Node, b: &Node) -> (bool, bool) {
    if a.prose != b.prose {
        return (a.prose < b.prose, false);
    }
    if a.lits != b.lits {
        return (a.lits > b.lits, false);
    }
    if a.size != b.size {
        return (a.size < b.size, false);
    }
    let syn = |x: &Node, y: &Node| match (x.rid, y.rid) {
        (Rid::R(i), Rid::R(_)) => g.rules[i].sem == Some(y.name) || (g.rules[i].sem.is_some() && g.rules[i].sem == sem_of(g, y)),
        _ => false,
    };
    if syn(b, a) {
        return (true, false);
    }
    if syn(a, b) {
        return (false, false);
    }
    if a.name == b.name && same_shape(a, b) {
        return (false, false);
    }
    (false, true)
}

fn sem_of(g: &crate::grammar::Grammar, n: &Node) -> Option<&'static str> {
    match n.rid {
        Rid::R(i) => g.rules[i].sem,
        _ => None,
    }
}

/// Same rule and same item structure (two derivations of one reading).
fn same_shape(a: &Node, b: &Node) -> bool {
    fn items(a: &[Item], b: &[Item]) -> bool {
        a.len() == b.len()
            && a.iter().zip(b).all(|(x, y)| match (x, y) {
                (Item::L(p, _), Item::L(q, _)) => p == q,
                (Item::T(p, _), Item::T(q, _)) => p == q,
                (Item::N(p, _), Item::N(q, _)) => p.name == q.name && p.s == q.s && p.e == q.e && same_shape(p, q),
                (Item::O(None, _), Item::O(None, _)) => true,
                (Item::O(Some(p), _), Item::O(Some(q), _)) => items(p, q),
                (Item::A(i, p, _), Item::A(j, q, _)) => i == j && items(p, q),
                (Item::P(i, j, _), Item::P(k, l, _)) => i == k && j == l,
                _ => false,
            })
    }
    a.rid == b.rid && items(&a.items, &b.items)
}

impl<'g> Parser<'g> {
    pub fn new(g: &'g crate::grammar::Grammar, maxtier: u8, skeleton: bool) -> Parser<'g> {
        Parser { g, maxtier, skeleton, munch: true, t: Vec::new(), n: 0, memo: HashMap::new() }
    }

    /// The parse of all of `toks` as `c`, if any.
    pub fn parse(&mut self, toks: &[Tok], c: Cat) -> Option<Rc<Node>> {
        self.t = toks.to_vec();
        self.n = toks.len();
        self.memo.clear();
        let r = self.cat(c, 0);
        r.iter().find(|(j, _)| *j == self.n).map(|(_, n)| n.clone())
    }

    /// Candidates collected into one tree per end.
    pub fn select(&self, cands: Vec<(usize, Rc<Node>)>) -> Vec<(usize, Rc<Node>)> {
        let mut best: BTreeMap<usize, (Rc<Node>, bool, bool)> = BTreeMap::new();
        for (j, nd) in cands {
            match best.get_mut(&j) {
                None => {
                    best.insert(j, (nd, false, false));
                }
                Some(cur) => {
                    let (win, order) = better(self.g, &nd, &cur.0);
                    let (_, rev_order) = better(self.g, &cur.0, &nd);
                    cur.2 = true;
                    if win {
                        cur.0 = nd;
                        cur.1 = false;
                    } else if order && rev_order {
                        cur.1 = true;
                    }
                }
            }
        }
        best.into_iter()
            .map(|(j, (nd, tie, alts))| {
                if tie || alts {
                    let mut n = Rc::try_unwrap(nd).unwrap_or_else(|rc| clone_node(&rc));
                    n.tie |= tie;
                    n.alts |= alts;
                    (j, Rc::new(n))
                } else {
                    (j, nd)
                }
            })
            .collect()
    }

    pub fn cat(&mut self, c: Cat, i: usize) -> Res {
        if let Some(m) = self.memo.get(&(c, i)) {
            return m.clone();
        }
        self.memo.insert((c, i), Rc::new(Vec::new()));
        let mut out: Vec<(usize, Rc<Node>)> = Vec::new();
        if let Some(b) = crate::grammar::builtin(c) {
            out.extend(b(self, i));
        }
        let g = self.g;
        if let Some(rs) = g.by_cat.get(c) {
            for &ri in rs {
                let r = &g.rules[ri];
                if r.tier > self.maxtier {
                    continue;
                }
                if let Some(f) = &r.first {
                    if i >= self.n || !lit_ok(&self.t[i], f) {
                        continue;
                    }
                } else if let Some(k) = r.firstkind {
                    if i >= self.n || !kind_ok(&self.t[i], k) {
                        continue;
                    }
                }
                for (items, j) in self.seq(&r.elems, i, r.cat) {
                    out.push((j, mk(Rid::R(ri), r.name, items, i, j)));
                }
            }
        }
        let res: Res = Rc::new(self.select(out));
        self.memo.insert((c, i), res.clone());
        res
    }

    fn seq(&mut self, els: &[(El, bool)], i: usize, owner: Cat) -> Vec<(Vec<Item>, usize)> {
        let Some((first, rest)) = els.split_first() else {
            return vec![(Vec::new(), i)];
        };
        let mut out = Vec::new();
        for (item, j) in self.elem(first, i, owner) {
            for (mut tr, k) in self.seq(rest, j, owner) {
                tr.insert(0, item.clone());
                out.push((tr, k));
            }
        }
        out
    }

    fn elem(&mut self, (el, glue): &(El, bool), i: usize, owner: Cat) -> Vec<(Item, usize)> {
        let glue = *glue;
        match el {
            El::Lit(l) => {
                if i < self.n && lit_ok(&self.t[i], l) {
                    vec![(Item::L(l.clone(), glue), i + 1)]
                } else {
                    vec![]
                }
            }
            El::Kind(k) => {
                if i < self.n && kind_ok(&self.t[i], *k) {
                    vec![(Item::T(i, glue), i + 1)]
                } else {
                    vec![]
                }
            }
            El::KindV(k, v, _) => {
                if i < self.n && self.t[i].k == *k && self.t[i].v == *v {
                    vec![(Item::T(i, glue), i + 1)]
                } else {
                    vec![]
                }
            }
            El::Hole(c) => {
                let mut out: Vec<(Item, usize)> = self.cat(c, i).iter().map(|(j, n)| (Item::N(n.clone(), glue), *j)).collect();
                if self.skeleton && PROSE_OWNERS.contains(&owner) && PROSE_OK.contains(c) {
                    for j in i + 1..=self.n {
                        out.push((Item::P(i, j, glue), j));
                    }
                }
                out
            }
            El::Opt(inner) => {
                let mut out: Vec<(Item, usize)> =
                    self.seq(inner, i, owner).into_iter().map(|(tr, j)| (Item::O(Some(tr), glue), j)).collect();
                out.push((Item::O(None, glue), i));
                out
            }
            El::Alt(alts) => {
                let mut out = Vec::new();
                for (k, alt) in alts.iter().enumerate() {
                    for (tr, j) in self.seq(alt, i, owner) {
                        out.push((Item::A(k, tr, glue), j));
                    }
                }
                out
            }
        }
    }
}

fn clone_node(n: &Node) -> Node {
    Node { rid: n.rid, name: n.name, items: n.items.clone(), s: n.s, e: n.e, prose: n.prose, lits: n.lits, size: n.size, tie: n.tie, alts: n.alts }
}

pub fn walk_items(it: &Item, f: &mut dyn FnMut(&Node)) {
    match it {
        Item::N(n, _) => f(n),
        Item::O(Some(v), _) | Item::A(_, v, _) => {
            for x in v {
                walk_items(x, f);
            }
        }
        _ => {}
    }
}

/// Visit every node of a tree.
pub fn visit(n: &Node, f: &mut dyn FnMut(&Node)) {
    f(n);
    for it in &n.items {
        walk_items(it, &mut |c| visit(c, f));
    }
}

/// The printed parts of a tree.
pub fn emit(n: &Node, toks: &[Tok], out: &mut Vec<crate::token::Part>) {
    for it in &n.items {
        emit_item(it, toks, out);
    }
}

fn set_glue(out: &mut [crate::token::Part], first: usize) {
    if let Some(p) = out.get_mut(first) {
        match p {
            crate::token::Part::Text(_, g) | crate::token::Part::Span(_, _, g) | crate::token::Part::Raw(_, g) => *g = true,
        }
    }
}

fn emit_item(it: &Item, toks: &[Tok], out: &mut Vec<crate::token::Part>) {
    use crate::token::Part;
    match it {
        Item::L(l, g) => out.push(Part::Text(lit_canon(l).to_string(), *g)),
        Item::T(i, g) => out.push(Part::Text(crate::token::canon(&toks[*i]), *g)),
        Item::N(n, g) => {
            let first = out.len();
            emit(n, toks, out);
            if *g {
                set_glue(out, first);
            }
        }
        Item::O(None, _) => {}
        Item::O(Some(v), g) | Item::A(_, v, g) => {
            let first = out.len();
            for x in v {
                emit_item(x, toks, out);
            }
            if *g {
                set_glue(out, first);
            }
        }
        Item::P(i, j, g) => out.push(Part::Span(*i, *j, *g)),
    }
}
