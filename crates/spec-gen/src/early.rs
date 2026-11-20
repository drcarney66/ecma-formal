//! Early Errors clauses: each `<emu-grammar>` block and the bullets of the
//! `<ul>` after it (rule rows keyed by its productions), each bullet's
//! sentences parsed by the rule grammar (category EB).

use crate::ast::{Channel, LiLayout};
use crate::classify::Class;
use crate::decls::Decls;
use crate::engine::{Node, Parser};
use crate::grammar::Grammar;
use crate::spec::{line_of, Clause, Spec};
use crate::token::{tokenize, Tok};
use std::rc::Rc;

/// A production block of an Early Errors clause.
pub struct Block {
    pub line: usize,
    /// the content of `<emu-grammar>`
    pub raw: String,
}

/// One `<li>` of a block's list.
pub struct Bullet {
    pub line: usize,
    pub clause: usize,
    /// its position after its clause's emu-algs and equations
    pub idx: usize,
    /// index into `Early::blocks`
    pub block: usize,
    /// the column of `<li>`
    pub indent: usize,
    /// the content between the tags
    pub raw: String,
    pub layout: LiLayout,
    /// the sentences: for a raw layout, its content on one line (`flatten`), or the whole
    /// content when it has none
    pub text: String,
}

impl Bullet {
    /// Whether a raw layout's content is read as sentences on one line.
    pub fn flat(&self) -> bool {
        self.layout == LiLayout::Raw && self.text != self.raw
    }
}

#[derive(Default)]
pub struct Early {
    pub clauses: Vec<usize>,
    pub blocks: Vec<Block>,
    pub bullets: Vec<Bullet>,
}

/// Whether a clause is an Early Errors clause.
pub fn is_early(c: &Clause) -> bool {
    c.h1_text() == "Static Semantics: Early Errors"
}

/// The column of offset `p`.
fn column(s: &str, p: usize) -> usize {
    p - s[..p].rfind('\n').map(|x| x + 1).unwrap_or(0)
}

/// The earliest of `pats` in `s` from `i`: its offset and index.
fn earliest(s: &str, i: usize, pats: &[&str]) -> Option<(usize, usize)> {
    pats.iter().enumerate().filter_map(|(k, p)| s[i..].find(p).map(|o| (i + o, k))).min()
}

/// A bullet's layout and sentences from its content.
fn layout(raw: &str, indent: usize) -> (LiLayout, String) {
    if !raw.contains('\n') {
        return (LiLayout::Inline, raw.to_string());
    }
    let lead = format!("\n{}", " ".repeat(indent + 2));
    let trail = format!("\n{}", " ".repeat(indent));
    match raw.strip_prefix(&lead).and_then(|r| r.strip_suffix(&trail)) {
        Some(t) if !t.contains('\n') && !t.starts_with(' ') && !t.starts_with('<') => (LiLayout::Block, t.to_string()),
        _ => (LiLayout::Raw, flatten(raw).unwrap_or_else(|| raw.to_string())),
    }
}

/// An item of a folded list without its full stop, its first word lower-cased unless it
/// has another capital or a parenthesis.
fn fold_item(li: &str) -> Option<String> {
    let t = li.trim().strip_suffix('.')?;
    let w = t.split(' ').next()?;
    let mut cs = t.chars();
    let c = cs.next()?;
    Some(if w.chars().skip(1).any(|c| c.is_uppercase() || c == '(') { t.to_string() } else { c.to_lowercase().chain(cs).collect() })
}

/// A raw layout's sentences on one line: `<p>`, `</p>` and `<br>` dropped, whitespace runs as
/// one space; a `<ul normative-optional>` after a sentence ending `:</span>` folded into the
/// span as `A and b`, the sentence's full stop after it; a `<p>` ending `:` and the
/// `<emu-alg>` after it as `…: <emu-alg>…</emu-alg>.`. None for any other block markup.
pub fn flatten(raw: &str) -> Option<String> {
    if let Some(a) = raw.find("<emu-alg") {
        let e = raw.find("</emu-alg>")? + "</emu-alg>".len();
        let head = raw[..a].trim_end().strip_suffix("</p>")?;
        if !head.ends_with(':') || !raw[e..].trim().is_empty() {
            return None;
        }
        return Some(format!("{} {}.", flatten(head)?, &raw[a..e]));
    }
    let mut s = raw.to_string();
    if let Some(u) = s.find("<ul normative-optional>") {
        let (head, list) = s.split_at(u);
        let tail = list.find("</ul>")? + "</ul>".len();
        let (list, rest) = list.split_at(tail);
        let items = list["<ul normative-optional>".len()..list.len() - "</ul>".len()]
            .split("</li>")
            .filter(|x| !x.trim().is_empty())
            .map(|x| x.trim().strip_prefix("<li>").and_then(fold_item))
            .collect::<Option<Vec<_>>>()?;
        let head = head.trim_end().strip_suffix("</p>")?.strip_suffix(":</span>")?;
        let joined = match items.len() {
            0 | 1 => return None,
            2 => items.join(" and "),
            n => format!("{}, and {}", items[..n - 1].join(", "), items[n - 1]),
        };
        s = format!("{head}: {joined}</span>.{rest}");
    }
    let s = s.replace("<p>", " ").replace("</p>", " ").replace("<br>", " ");
    let s = s.split_whitespace().collect::<Vec<_>>().join(" ");
    (!["<p", "<ul", "<li", "<emu-alg", "<emu-note"].iter().any(|t| s.contains(t))).then_some(s)
}

/// The blocks and bullets of every Early Errors clause: a line at the
/// clause's own column opening `<emu-grammar` starts a block, one that is
/// `<ul>` holds the block's bullets (its top-level `<li>`s).
pub fn scan(s: &str, clauses: &[Clause], used: &[usize]) -> Result<Early, String> {
    let mut out = Early::default();
    for (ci, c) in clauses.iter().enumerate().filter(|(_, c)| is_early(c)) {
        out.clauses.push(ci);
        let h1 = c.start + s[c.start..c.end].find("<h1>").ok_or("an Early Errors clause without a heading")?;
        let col = column(s, h1);
        let mut idx = used[ci];
        let mut cur: Option<usize> = None;
        let mut p = h1;
        while let Some(nl) = s[p..c.end].find('\n') {
            let ls = p + nl + 1;
            p = ls;
            let rest = &s[ls..c.end];
            let t = rest.trim_start_matches(' ');
            if rest.len() - t.len() != col {
                continue;
            }
            let at = ls + col;
            if t.starts_with("<emu-grammar") {
                let gt = at + t.find('>').ok_or("unclosed emu-grammar")? + 1;
                let close = gt + s[gt..].find("</emu-grammar>").ok_or("unclosed emu-grammar")?;
                out.blocks.push(Block { line: line_of(s, at), raw: s[gt..close].to_string() });
                cur = Some(out.blocks.len() - 1);
            } else if t.starts_with("<ul>") {
                let block = cur.ok_or_else(|| format!("spec.html:{}: an early-error list without its productions", line_of(s, at)))?;
                let mut depth = 0;
                let mut open = None;
                let mut q = at + "<ul>".len();
                loop {
                    let (o, k) = earliest(s, q, &["<li>", "</li>", "<ul", "</ul>"]).ok_or("unclosed ul")?;
                    q = o + 1;
                    match (k, depth) {
                        (0, 0) => open = Some(o),
                        (1, 0) => {
                            let a = open.take().ok_or("a stray </li>")?;
                            let raw = s[a + "<li>".len()..o].to_string();
                            let indent = column(s, a);
                            let (layout, text) = layout(&raw, indent);
                            out.bullets.push(Bullet { line: line_of(s, a), clause: ci, idx, block, indent, raw, layout, text });
                            idx += 1;
                        }
                        (2, _) => depth += 1,
                        (3, 0) => break,
                        (3, _) => depth -= 1,
                        _ => {}
                    }
                }
                p = q;
            }
        }
    }
    Ok(out)
}

/// Channel (c)'s kind for a bullet in a raw layout.
pub const RAW_KIND: &str = "layout residue: an early-error bullet in a raw layout, kept verbatim";

/// The residue channel of a bullet's prose: (c) for a raw layout, else none
/// (any prose left is a stop).
pub fn channel(d: &mut Decls, b: &Bullet) -> Channel {
    if b.layout == LiLayout::Raw {
        Channel::Annotated(d.notes.intern(RAW_KIND), None)
    } else {
        Channel::Pending
    }
}

/// A bullet parsed.
pub struct Row {
    pub toks: Vec<Tok>,
    pub class: Class,
    pub tree: Option<Rc<Node>>,
}

/// Every bullet parsed: fully structured (S), with prose holes (K), or
/// unrecognized or in a raw layout (U).
pub fn classify(sp: &Spec, g: &Grammar) -> Vec<Row> {
    let mut strict = Parser::new(g, 99, false);
    let mut skel = Parser::new(g, 99, true);
    sp.early
        .bullets
        .iter()
        .map(|b| {
            if b.layout == LiLayout::Raw && !b.flat() {
                return Row { toks: vec![], class: Class::U, tree: None };
            }
            let toks = tokenize(&b.text);
            let (class, tree) = match strict.parse(&toks, "EB") {
                Some(t) => (Class::S, Some(t)),
                None => match skel.parse(&toks, "EB") {
                    Some(t) => (Class::K, Some(t)),
                    None => (Class::U, None),
                },
            };
            if b.flat() && class != Class::S {
                return Row { toks: vec![], class: Class::U, tree: None };
            }
            Row { toks, class, tree }
        })
        .collect()
}

/// The sentences of a bullet's tree (category ER nodes), in order.
pub fn sentences(t: &Rc<Node>) -> Vec<Rc<Node>> {
    let mut out = Vec::new();
    let mut cur = t.clone();
    loop {
        let kids: Vec<Rc<Node>> = cur.items.iter().filter_map(|it| if let crate::engine::Item::N(n, _) = it { Some(n.clone()) } else { None }).collect();
        out.push(kids[0].clone());
        match kids.get(1) {
            Some(n) => cur = n.clone(),
            None => return out,
        }
    }
}

/// How a bullet begins.
pub fn lead(text: &str) -> &'static str {
    const LEADS: &[(&str, &str)] = &[
        ("It is a Syntax Error if ", "It is a Syntax Error if …"),
        ("It is an early Syntax Error if ", "It is an early Syntax Error if …"),
        ("If ", "If …, …"),
        ("For each ", "For each …: …"),
        ("<p>", "<p>…"),
    ];
    LEADS.iter().find(|(p, _)| text.trim_start().starts_with(p)).map(|x| x.1).unwrap_or("other")
}
