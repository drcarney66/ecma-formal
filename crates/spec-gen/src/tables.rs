//! The `<emu-table>`s: each table's skeleton printed from its column, each
//! cell parsed by its column's role (field names, type phrases, method
//! signatures), prose and data cells kept as text.

use crate::ast::{Attr, Expr, Id, Stmt, TyExpr};
use crate::conv::{Conv, Vars};
use crate::data::Data;
use crate::engine::Parser;
use crate::grammar::Grammar;
use crate::spec::Spec;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    /// a Record's fields: Field Name / Value / Meaning
    Fields,
    /// an object's internal slots: Internal Slot / Type / Description
    Slots,
    /// essential internal methods: signature / Description / Definitions
    InternalMethods,
    /// a record type's abstract methods: signature / Purpose / Definitions
    AbstractMethods,
    /// execution-context state components
    Components,
    /// an interface's properties: Property / Value / Requirements
    Properties,
    /// well-known intrinsics
    Intrinsics,
    /// a conversion by argument type: Argument Type / Result (a step)
    Conversion,
    /// any other table: data rows
    Data,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// a header cell
    Head,
    Name,
    Type,
    Sig,
    Step,
    Prose,
    Data,
}

/// A table's type phrase: a header type, or `a List of Records with fields …`.
#[derive(Clone, Debug, PartialEq)]
pub enum TTy {
    Ty(TyExpr),
    /// `a List of Records with fields [[F]] (T) and …`
    Records(Vec<(Id, TyExpr)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    /// the table's variable slot
    pub x: Id,
    pub ty: TTy,
    pub optional: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SigName {
    /// `[[M]]`: a field id, as `Expr::IMethod` names it
    Internal(Id),
    /// `M`: a method id, as `Expr::CMethod` names it
    Method(Id),
}

/// `[[M]] ( _p_: T, … ): R` or `M ( … ): R`; no parameters: on one line.
#[derive(Clone, Debug, PartialEq)]
pub struct Sig {
    pub name: SigName,
    pub params: Vec<Param>,
    pub ret: TTy,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Body {
    /// `[[F]]`
    Field(Id),
    Ty(TTy),
    Sig(Sig),
    Stmt(Stmt),
    /// an `<emu-alg>`, by its index in `Spec::algs` (printed from its data)
    Alg(usize),
    Expr(Expr),
    /// an operation's name, by its defining clause: `ToInt8`, `Number::add`
    Op(usize),
    /// an execution-context component's name: `Realm`
    Component(Id),
    /// a global binding's name: `Int8Array`
    Name(String),
    /// `a<br>` lines
    Lines(Vec<Body>),
    /// `<dfn>…</dfn>`
    Dfn(Box<Body>),
    /// a code point in code: `` `U+0009` ``
    Code(Box<Body>),
    /// `<a href="h">…</a>`
    Link(String, Box<Body>),
    /// a data cell no form fits, by its residue kind (`Decls.notes`)
    Kept(Id, String),
    /// verbatim: a header, or a description
    Text(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Cell {
    /// blank lines before it
    pub gap: usize,
    /// `<th>` rather than `<td>`
    pub head: bool,
    pub attrs: Vec<Attr>,
    /// the content on its own lines, two columns in; else between the tags
    pub block: bool,
    pub role: Role,
    pub body: Body,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    /// blank lines before it
    pub gap: usize,
    pub attrs: Vec<Attr>,
    pub cells: Vec<Cell>,
}

pub struct Table {
    /// offset of `<emu-table`
    pub pos: usize,
    pub line: usize,
    pub clause: Option<usize>,
    /// its index among its clause's tables
    pub idx: usize,
    /// the column of `<emu-table`
    pub col: usize,
    pub attrs: Vec<Attr>,
    /// its `<emu-caption>`, if it has one
    pub caption: Option<String>,
    /// the `<table>` element's attributes
    pub table_attrs: Vec<Attr>,
    /// the file it is imported from by an `<emu-import>`
    pub import: Option<String>,
    /// a step's own table (`<figure>` in an `<emu-alg>`), printed with its step
    pub figure: bool,
    pub kind: Kind,
    /// the first row is in `<thead>`
    pub thead: bool,
    pub rows: Vec<Row>,
    pub vars: Vars,
    /// the source, `<emu-table` to `</emu-table>`
    pub raw: String,
}

impl Table {
    /// Its `id` attribute.
    pub fn id(&self) -> Option<String> {
        self.attrs.iter().find(|a| a.key == "id").and_then(|a| a.value.clone())
    }

    pub fn attr(&self, k: &str) -> Option<&str> {
        self.attrs.iter().find(|a| a.key == k).and_then(|a| a.value.as_deref())
    }
}

/// ` k="v" k2` as attributes, if written canonically.
fn parse_attrs(s: &str) -> Option<Vec<Attr>> {
    let mut out = Vec::new();
    let mut r = s;
    while !r.is_empty() {
        r = r.strip_prefix(' ')?;
        let e = r.find([' ', '=']).unwrap_or(r.len());
        let key = r[..e].to_string();
        if key.is_empty() {
            return None;
        }
        r = &r[e..];
        let value = match r.strip_prefix("=\"") {
            Some(v) => {
                let q = v.find('"')?;
                r = &v[q + 1..];
                Some(v[..q].to_string())
            }
            None => None,
        };
        out.push(Attr { key, value });
    }
    Some(out)
}

fn attrs_text(a: &[Attr]) -> String {
    let mut s = String::new();
    for x in a {
        s.push(' ');
        s.push_str(&x.key);
        if let Some(v) = &x.value {
            s.push_str(&format!("=\"{v}\""));
        }
    }
    s
}

/// `<name attrs>` at `i`: its attributes and end.
fn open(s: &str, i: usize, name: &str) -> Result<(Vec<Attr>, usize), String> {
    let r = &s[i..];
    let t = format!("<{name}");
    if !r.starts_with(&t) || !r[t.len()..].starts_with([' ', '>']) {
        return Err(format!("expected <{name}> at {:?}", &r[..r.len().min(30)]));
    }
    let gt = r.find('>').ok_or("unclosed tag")?;
    let a = parse_attrs(&r[t.len()..gt]).ok_or_else(|| format!("attributes {:?}", &r[t.len()..gt]))?;
    Ok((a, i + gt + 1))
}

fn lit(s: &str, i: usize, l: &str) -> Result<usize, String> {
    if s[i..].starts_with(l) {
        Ok(i + l.len())
    } else {
        Err(format!("expected {l} at {:?}", &s[i..s.len().min(i + 30)]))
    }
}

fn ws(s: &str, i: usize) -> usize {
    i + s[i..].len() - s[i..].trim_start().len()
}

/// Blank lines in the white space at `i`.
fn gap(s: &str, i: usize) -> usize {
    s[i..ws(s, i)].matches('\n').count().saturating_sub(1)
}

/// A cell's content at a column: dedented lines (block; none if empty), or verbatim.
fn layout(content: &str, col: usize) -> (bool, String) {
    let tail = format!("\n{}", " ".repeat(col));
    let pad = " ".repeat(col + 2);
    if content == tail {
        return (true, String::new());
    }
    if let Some(mid) = content.strip_prefix('\n').and_then(|c| c.strip_suffix(&tail)).filter(|m| !m.is_empty()) {
        let lines: Option<Vec<&str>> = mid.split('\n').map(|l| if l.is_empty() { Some(l) } else { l.strip_prefix(&pad) }).collect();
        if let Some(ls) = lines {
            return (true, ls.join("\n"));
        }
    }
    (false, content.to_string())
}

type RawCell = (usize, bool, Vec<Attr>, String);

/// A row at `i` (white space first), raw: gap, attributes, cells (gap, head, attributes, content).
fn row(s: &str, i: usize) -> Result<(usize, Vec<Attr>, Vec<RawCell>, usize), String> {
    let rg = gap(s, i);
    let (attrs, mut i) = open(s, ws(s, i), "tr")?;
    let mut cells = Vec::new();
    loop {
        let g = gap(s, i);
        i = ws(s, i);
        if s[i..].starts_with("</tr>") {
            return Ok((rg, attrs, cells, i + 5));
        }
        let head = s[i..].starts_with("<th");
        let name = if head { "th" } else { "td" };
        let (a, j) = open(s, i, name)?;
        let close = format!("</{name}>");
        let k = j + s[j..].find(&close).ok_or("unclosed cell")?;
        cells.push((g, head, a, s[j..k].to_string()));
        i = k + close.len();
    }
}

fn kind_of(h: &[String]) -> Kind {
    let h: Vec<&str> = h.iter().map(String::as_str).collect();
    match h.as_slice() {
        ["Field Name", "Value" | "Value Type", "Meaning" | "Usage"] | ["Field Name", _, "Value", "Meaning"] => Kind::Fields,
        ["Internal Slot", "Type", "Description"] => Kind::Slots,
        ["Internal Method", "Description", "Definitions"] => Kind::InternalMethods,
        ["Method", "Purpose", "Definitions"] => Kind::AbstractMethods,
        ["Component", "Purpose"] => Kind::Components,
        ["Property", "Value", "Requirements"] => Kind::Properties,
        ["Intrinsic Name", "Global Name", "ECMAScript Language Association"] => Kind::Intrinsics,
        ["Argument Type", "Result"] => Kind::Conversion,
        _ => Kind::Data,
    }
}

fn role_of(k: Kind, header: &str, col: usize) -> Role {
    match (k, header) {
        (Kind::InternalMethods | Kind::AbstractMethods, _) if col == 0 => Role::Sig,
        (_, "Field Name" | "Internal Slot" | "Internal Method") if col == 0 => Role::Name,
        (Kind::Fields | Kind::Slots | Kind::Properties, "Value" | "Value Type" | "Type") | (Kind::Conversion, "Argument Type") => Role::Type,
        (Kind::Conversion, "Result") => Role::Step,
        (Kind::Data, "Result" | "Value Domain") => Role::Type,
        (
            _,
            "Meaning" | "Usage" | "Description" | "Purpose" | "Requirements" | "Definitions" | "Value and Purpose" | "ECMAScript Language Association"
            | "Name" | "Unicode Name" | "Unicode Character Name" | "Abbreviation" | "Symbol" | "Types of property for which it is present"
            | "Invoked by the Evaluation semantics of ...",
        ) => Role::Prose,
        _ => Role::Data,
    }
}

/// A cell's role: its column's, except that a String literal in a prose column is data.
fn cell_role(k: Kind, header: &str, col: usize, text: &str) -> Role {
    match role_of(k, header, col) {
        Role::Prose if is_string_literal(text) => Role::Data,
        r => r,
    }
}

/// Whether `text` is one String literal, `*"…"*`.
fn is_string_literal(text: &str) -> bool {
    text.strip_prefix("*\"").and_then(|t| t.strip_suffix("\"*")).is_some_and(|t| !t.contains('"'))
}

/// The column of each cell of each row, through `rowspan` and `colspan`.
fn columns(rows: &[Vec<RawCell>]) -> Vec<Vec<usize>> {
    let num = |a: &[Attr], k: &str| a.iter().find(|x| x.key == k).and_then(|x| x.value.as_ref()?.parse::<usize>().ok()).unwrap_or(1);
    let mut busy: Vec<usize> = Vec::new();
    let mut out = Vec::new();
    for r in rows {
        let mut cols = Vec::new();
        let mut c = 0;
        for (_, _, a, _) in r {
            while busy.get(c).is_some_and(|&n| n > 0) {
                c += 1;
            }
            cols.push(c);
            let (rs, cs) = (num(a, "rowspan"), num(a, "colspan"));
            for k in c..c + cs {
                if busy.len() <= k {
                    busy.resize(k + 1, 0);
                }
                busy[k] = rs;
            }
            c += cs;
        }
        for b in busy.iter_mut() {
            *b = b.saturating_sub(1);
        }
        out.push(cols);
    }
    out
}

/// Type phrases and signatures parsed with the header-type category.
struct Typer<'a, 'b> {
    hp: Parser<'a>,
    cv: Conv<'a, 'b>,
    /// cells whose tree has a tie left on declaration order
    ties: Vec<String>,
}

impl<'a, 'b> Typer<'a, 'b> {
    /// The one-line `text` parsed as `cat`, its tokens left with the converter.
    fn parse(&mut self, text: &str, cat: crate::engine::Cat) -> Option<std::rc::Rc<crate::engine::Node>> {
        let toks = crate::token::tokenize(text);
        if text.contains('\n') || toks.is_empty() {
            return None;
        }
        let tree = self.hp.parse(&toks, cat)?;
        if crate::classify::has_tie(&tree) {
            self.ties.push(text.to_string());
        }
        self.cv.toks = toks;
        self.cv.text = text.to_string();
        Some(tree)
    }

    /// The type phrase `text`, if it parses and prints back as written.
    fn ty(&mut self, text: &str) -> Option<TyExpr> {
        let tree = self.parse(text, "HT")?;
        let t = self.cv.ht(&tree).ok()?;
        let ok = crate::print::ty_text(self.cv.d, &self.cv.vars.names, &t) == text && !crate::lean::ty(&t).contains("(.prose ");
        ok.then_some(t)
    }

    /// The type phrase `text`, or `a List of Records with fields …`.
    fn tty(&mut self, text: &str) -> Option<TTy> {
        if let Some(fs) = text.strip_prefix("a List of Records with fields ") {
            return match self.ty(&format!("a Record with fields {fs}"))? {
                TyExpr::Record(fs) => Some(TTy::Records(fs)),
                _ => None,
            };
        }
        self.ty(text).map(TTy::Ty)
    }

    /// A data cell: an expression, an operation or component name, `<dfn>`, or `<br>` lines.
    fn data(&mut self, text: &str) -> Option<Body> {
        if text.contains("<br>\n") {
            let ls: Vec<&str> = text.split("<br>\n").collect();
            if let [n, d] = ls.as_slice() {
                if !n.is_empty() && n.chars().all(|c| c.is_ascii_alphanumeric()) && *d == format!("<dfn>%{n}%</dfn>") {
                    return Some(Body::Lines(vec![Body::Name(n.to_string()), self.data(d)?]));
                }
            }
            return ls.iter().map(|x| self.data(x)).collect::<Option<Vec<_>>>().map(Body::Lines);
        }
        if let Some(x) = text.strip_prefix("<dfn>").and_then(|x| x.strip_suffix("</dfn>")) {
            return self.data(x).map(|b| Body::Dfn(Box::new(b)));
        }
        if let Some((h, x)) = text.strip_prefix("<a href=\"").and_then(|x| x.strip_suffix("</a>")).and_then(|x| x.split_once("\">")) {
            if !h.contains(['"', '<', '>']) {
                return self.data(x).map(|b| Body::Link(h.to_string(), Box::new(b)));
            }
        }
        if let Some(x) = text.strip_prefix('`').and_then(|x| x.strip_suffix('`')) {
            let hex = |p: &str, n: std::ops::RangeInclusive<usize>| x.strip_prefix(p).is_some_and(|h| n.contains(&h.len()) && h.chars().all(|c| c.is_ascii_hexdigit()));
            // a code point `U+0009`, or a code unit's value `0x0008`
            if hex("U+", 4..=6) || hex("0x", 4..=4) {
                return self.data(x).map(|b| Body::Code(Box::new(b)));
            }
        }
        if let Some(e) = self.expr(text) {
            return Some(Body::Expr(e));
        }
        if let Some(&c) = self.cv.env.ops.get(text) {
            return Some(Body::Op(c));
        }
        if self.cv.env.components.iter().any(|c| c == text) {
            return Some(Body::Component(self.cv.d.fields.intern(text)));
        }
        None
    }

    /// The expression `text`, if it parses and prints back as written.
    fn expr(&mut self, text: &str) -> Option<Expr> {
        let tree = self.parse(text, "E")?;
        let e = self.cv.expr(&tree).ok()?;
        let ok = crate::print::expr_text(self.cv.d, &self.cv.vars.names, &e) == text && !crate::lean::expr(&e).contains("(.prose ");
        ok.then_some(e)
    }

    /// The step `text`, if it parses and prints back as written.
    fn stmt(&mut self, text: &str) -> Option<Stmt> {
        let tree = self.parse(text, "Step")?;
        let s = self.cv.stmt(&tree, &[]).ok()?;
        let ok = crate::print::stmt_text(self.cv.d, &self.cv.vars.names, &s).as_deref() == Some(text) && !crate::lean::stmt(&s).contains("(.prose ");
        ok.then_some(s)
    }

    /// The signature `text`, if it parses and prints back as written.
    fn sig(&mut self, text: &str) -> Option<Sig> {
        let (head, params, ret) = match text.split_once(" ( ): ") {
            Some((h, r)) if !r.contains('\n') => (h, vec![], r),
            _ => {
                let mut ls: Vec<&str> = text.split('\n').collect();
                let first = ls.remove(0).strip_suffix(" (")?;
                let ret = ls.pop()?.strip_prefix("): ")?;
                (first, ls, ret)
            }
        };
        let (internal, name) = match head.strip_prefix("[[").and_then(|h| h.strip_suffix("]]")) {
            Some(n) => (true, n),
            None => (false, head),
        };
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric()) {
            return None;
        }
        let mut ps = Vec::new();
        for l in params {
            let l = l.strip_prefix("  ")?.strip_suffix(',')?;
            let (optional, l) = match l.strip_prefix("optional ") {
                Some(r) => (true, r),
                None => (false, l),
            };
            let (v, t) = l.strip_prefix('_')?.split_once("_: ")?;
            let x = self.cv.vars.slot(v);
            ps.push(Param { x, ty: self.tty(t)?, optional });
        }
        let name = if internal { SigName::Internal(self.cv.d.fields.intern(name)) } else { SigName::Method(self.cv.d.methods.intern(name)) };
        let s = Sig { name, params: ps, ret: self.tty(ret)? };
        (sig_text(self.cv.d, &self.cv.vars.names, &s) == text).then_some(s)
    }
}

pub fn tty_text(d: &crate::decls::Decls, vars: &[String], t: &TTy) -> String {
    match t {
        TTy::Ty(t) => crate::print::ty_text(d, vars, t),
        TTy::Records(fs) => {
            let r = crate::print::ty_text(d, vars, &TyExpr::Record(fs.clone()));
            format!("a List of Records with fields {}", r.strip_prefix("a Record with fields ").unwrap_or(&r))
        }
    }
}

/// Why a cell of a role has no form: its residue kind (`Decls.notes`).
fn why(role: Role, text: &str) -> &'static str {
    match role {
        Role::Type if text.ends_with(')') => "table cell: a type phrase with a remark in parentheses",
        Role::Type => "table cell: a type phrase no form covers",
        Role::Step => "table cell: a step no form covers",
        Role::Sig => "table cell: a signature no form covers",
        Role::Name => "table cell: a name that is not [[F]]",
        _ if text.ends_with('.') => "table cell: a sentence in a data column",
        _ if text.starts_with('_') || text.contains(" (_") => "table cell: an example's value described in words",
        _ => "table cell: words in a data column",
    }
}

fn sig_text(d: &crate::decls::Decls, vars: &[String], s: &Sig) -> String {
    let mut out = match s.name {
        SigName::Internal(f) => format!("[[{}]]", d.fields.name(f)),
        SigName::Method(m) => d.methods.name(m).to_string(),
    };
    if s.params.is_empty() {
        out.push_str(" ( )");
    } else {
        out.push_str(" (");
        for p in &s.params {
            let o = if p.optional { "optional " } else { "" };
            out.push_str(&format!("\n  {o}_{}_: {},", vars[p.x], tty_text(d, vars, &p.ty)));
        }
        out.push('\n');
        out.push(')');
    }
    out.push_str(": ");
    out.push_str(&tty_text(d, vars, &s.ret));
    out
}

fn field_of(text: &str) -> Option<&str> {
    let f = text.strip_prefix("[[")?.strip_suffix("]]")?;
    (!f.is_empty() && f.chars().all(|c| c.is_ascii_alphanumeric() || c == '%' || c == '.')).then_some(f)
}

/// The `<emu-table>` at `pos` of `s`; `at`: its offset in spec.html (an imported table's `<emu-import>`).
fn parse_table(s: &str, pos: usize, at: usize, sp: &Spec) -> Result<Table, String> {
    let (attrs, mut i) = open(s, pos, "emu-table")?;
    let ls = s[..pos].rfind('\n').map_or(0, |n| n + 1);
    let col = pos - ls;
    let end = i + s[i..].find("</emu-table>").ok_or("unclosed emu-table")?;
    let raw = s[pos..end + "</emu-table>".len()].to_string();
    let mut caption = None;
    if s[ws(s, i)..].starts_with("<emu-caption>") {
        let a = ws(s, i) + "<emu-caption>".len();
        let b = a + s[a..].find("</emu-caption>").ok_or("unclosed emu-caption")?;
        caption = Some(s[a..b].to_string());
        i = b + "</emu-caption>".len();
    }
    let (table_attrs, j) = open(s, ws(s, i), "table")?;
    i = j;
    let thead = s[ws(s, i)..].starts_with("<thead>");
    let mut raws = Vec::new();
    if thead {
        let (g, a, c, j) = row(s, ws(s, i) + 7)?;
        raws.push((g, a, c, col + 8));
        i = lit(s, ws(s, j), "</thead>")?;
    }
    while s[ws(s, i)..].starts_with("<tr") {
        let (g, a, c, j) = row(s, i)?;
        raws.push((g, a, c, col + 6));
        i = j;
    }
    i = ws(s, lit(s, ws(s, i), "</table>")?);
    if i != end {
        return Err("text after </table>".into());
    }
    let header: Vec<String> = raws.first().map(|r| r.2.iter().map(|c| crate::text::squash(&c.3)).collect()).unwrap_or_default();
    let kind = kind_of(&header);
    let cols = columns(&raws.iter().map(|r| r.2.clone()).collect::<Vec<_>>());
    let mut rows = Vec::new();
    for (ri, (rgap, rattrs, cells, ccol)) in raws.into_iter().enumerate() {
        let mut out = Vec::new();
        for (ci, (cgap, head, a, content)) in cells.into_iter().enumerate() {
            let (block, text) = layout(&content, ccol);
            let c = cols[ri][ci];
            let role = if head { Role::Head } else { cell_role(kind, header.get(c).map_or("", String::as_str), c, &text) };
            out.push(Cell { gap: cgap, head, attrs: a, block, role, body: Body::Text(text) });
        }
        rows.push(Row { gap: rgap, attrs: rattrs, cells: out });
    }
    let clause = sp.clauses.iter().enumerate().filter(|(_, c)| c.inst.is_none() && c.start <= at && at < c.end).max_by_key(|(_, c)| c.start).map(|(k, _)| k);
    let line = crate::spec::line_of(s, pos);
    Ok(Table { pos: at, line, clause, idx: 0, col, attrs, caption, table_attrs, import: None, figure: false, kind, thead, rows, vars: Vars::default(), raw })
}

/// The `<figure>` at `pos` of `html`, a step's table: its header row, then its rows, each cell's
/// content trimmed (its step prints it).
fn parse_figure(html: &str, pos: usize, sp: &Spec) -> Result<Table, String> {
    let ls = html[..pos].rfind('\n').map_or(0, |n| n + 1);
    let col = pos - ls;
    let end = html[pos..].find("</figure>").map(|k| pos + k).ok_or("unclosed figure")?;
    let raw = html[pos..end + "</figure>".len()].to_string();
    let mut i = ws(html, lit(html, pos, "<figure>")?);
    if html[i..].starts_with("<!--") {
        i = ws(html, html[i..].find("-->").map(|k| i + k + 3).ok_or("unclosed comment")?);
    }
    let (table_attrs, j) = open(html, i, "table")?;
    i = ws(html, j);
    let thead = html[i..].starts_with("<thead>");
    let mut raws = Vec::new();
    if thead {
        let (g, a, c, j) = row(html, i + 7)?;
        raws.push((g, a, c));
        i = ws(html, lit(html, ws(html, j), "</thead>")?);
    }
    let tbody = html[i..].starts_with("<tbody>");
    if tbody {
        i += 7;
    }
    while html[ws(html, i)..].starts_with("<tr") {
        let (g, a, c, j) = row(html, i)?;
        raws.push((g, a, c));
        i = j;
    }
    i = ws(html, i);
    if tbody {
        i = ws(html, lit(html, i, "</tbody>")?);
    }
    i = ws(html, lit(html, i, "</table>")?);
    if i != end {
        return Err("text after </table> in a figure".into());
    }
    let header: Vec<String> = raws.first().map(|r| r.2.iter().map(|c| crate::text::squash(&c.3)).collect()).unwrap_or_default();
    let kind = kind_of(&header);
    let cols = columns(&raws.iter().map(|r| r.2.clone()).collect::<Vec<_>>());
    let mut rows = Vec::new();
    for (ri, (rgap, rattrs, cells)) in raws.into_iter().enumerate() {
        let mut out = Vec::new();
        for (ci, (cgap, head, a, content)) in cells.into_iter().enumerate() {
            let c = cols[ri][ci];
            let role = if head { Role::Head } else { cell_role(kind, header.get(c).map_or("", String::as_str), c, content.trim()) };
            out.push(Cell { gap: cgap, head, attrs: a, block: false, role, body: Body::Text(content.trim().to_string()) });
        }
        rows.push(Row { gap: rgap, attrs: rattrs, cells: out });
    }
    let clause = sp.clauses.iter().enumerate().filter(|(_, c)| c.inst.is_none() && c.start <= pos && pos < c.end).max_by_key(|(_, c)| c.start).map(|(k, _)| k);
    let line = crate::spec::line_of(html, pos);
    Ok(Table { pos, line, clause, idx: 0, col, attrs: vec![], caption: None, table_attrs, import: None, figure: true, kind, thead, rows, vars: Vars::default(), raw })
}

/// The `<figure>`s inside an `<emu-alg>`: the tables of steps (`… in the following table:`).
fn figures(html: &str, sp: &Spec) -> Vec<Result<Table, String>> {
    let mut out = Vec::new();
    for (pos, _) in html.match_indices("<figure>") {
        let inside = html[..pos].rfind("<emu-alg").is_some_and(|a| html[..pos].rfind("</emu-alg>").is_none_or(|b| b < a));
        if inside {
            out.push(parse_figure(html, pos, sp).map_err(|e| format!("spec.html:{}: {e}", crate::spec::line_of(html, pos))));
        }
    }
    out
}

/// The tables `<emu-import href="F.html">` brings in, from the files beside spec.html: each with its error.
fn imports(html: &str, sp: &Spec) -> Vec<Result<Table, String>> {
    let dir = std::path::PathBuf::from(crate::spec_path()).parent().map(|p| p.to_path_buf()).unwrap_or_default();
    let mut out = Vec::new();
    for (at, _) in html.match_indices("<emu-import href=\"") {
        let f = html[at + 18..].split('"').next().unwrap_or("");
        let t = std::fs::read_to_string(dir.join(f)).map_err(|e| format!("{f}: {e}")).and_then(|s| {
            let pos = s.find("<emu-table").ok_or_else(|| format!("{f}: no emu-table"))?;
            let mut t = parse_table(&s, pos, at, sp).map_err(|e| format!("{f}:{}: {e}", crate::spec::line_of(&s, pos)))?;
            t.import = Some(f.to_string());
            Ok(t)
        });
        out.push(t);
    }
    out
}

/// Every `<emu-table>`: its skeleton, cell roles and texts; a table that does not parse is an error with its line.
pub fn scan(html: &str, sp: &Spec) -> Vec<Result<Table, String>> {
    let mut out = Vec::new();
    let mut count: HashMap<Option<usize>, usize> = HashMap::new();
    for (pos, _) in html.match_indices("<emu-table") {
        if html[pos + 10..].starts_with([' ', '>']) {
            out.push(parse_table(html, pos, pos, sp).map_err(|e| format!("spec.html:{}: {e}", crate::spec::line_of(html, pos))));
        }
    }
    // imported tables after the document's own, so that their indices follow, then the steps' tables
    out.extend(imports(html, sp));
    out.extend(figures(html, sp));
    for t in out.iter_mut().flatten() {
        let k = count.entry(t.clause).or_default();
        t.idx = *k;
        *k += 1;
    }
    out
}

/// A table's Lean name, without guillemets: its `id`, else its clause's id and its index there; the key
/// of its kept id (`table-ids.txt`).
pub fn lean_name(sp: &Spec, t: &Table) -> String {
    match t.attr("id") {
        Some(id) => id.to_string(),
        None => format!("{}-table-{}", t.clause.map_or("", |c| sp.clauses[c].id.as_str()), t.idx),
    }
}

/// The first column's texts of the tables of a kind.
pub fn first_column(ts: &[Result<Table, String>], k: Kind) -> Vec<String> {
    let mut out = Vec::new();
    for t in ts.iter().flatten().filter(|t| t.kind == k) {
        for r in t.rows.iter().skip(1) {
            if let Some(Cell { body: Body::Text(x), .. }) = r.cells.first() {
                out.push(crate::text::squash(&crate::text::strip_tags(x)));
            }
        }
    }
    out
}

pub struct Tables {
    pub tables: Vec<Result<Table, String>>,
    /// cells whose tree has a tie left on declaration order
    pub ties: Vec<String>,
    /// the overlay's declared types: a type, or the text that does not parse
    pub declared: Declared,
}

/// A declared type phrase, parsed, or its text.
pub type DTy = Result<TTy, String>;

#[derive(Default)]
pub struct Declared {
    /// `<emu-sort type=…>`: sort name and type
    pub sorts: Vec<(String, DTy)>,
    /// `<emu-fields>`: of, slots, each row's field and type
    pub fields: Vec<(String, bool, Vec<(Id, DTy)>)>,
    /// `<emu-guard>`: operation and type
    pub guards: Vec<(String, DTy)>,
}

/// Every `<emu-table>`, its cells parsed by role: names, type phrases, signatures, steps, expressions.
pub fn build(html: &str, sp: &Spec, g: &Grammar, dt: &mut Data) -> Tables {
    build_with(html, sp, g, dt, false)
}

/// As `build`, and with `declare`, the overlay's declared types (`Tables.declared`).
pub fn build_with(html: &str, sp: &Spec, g: &Grammar, dt: &mut Data, declare: bool) -> Tables {
    let mut ts = scan(html, sp);
    let rows = HashMap::new();
    let anchors = crate::conv::Anchors::new();
    let cv = Conv {
        open: Vec::new(),
        rhs: Default::default(),
            lhs: Default::default(),
            narrow: Vec::new(),
            symbols: false,
        channel: crate::ast::Channel::Pending,
        clause: String::new(),
        anchors: &anchors,
        stops: None,
        readings: Vec::new(),
        g,
        d: &mut dt.decls,
        env: &dt.env,
        vars: Vars::default(),
        rows: &rows,
        toks: Vec::new(),
        text: String::new(),
        unresolved: Vec::new(),
        exceptions: Vec::new(),
        closures: Vec::new(),
        base: 0,
    };
    let mut ty = Typer { hp: Parser::new(g, 99, false), cv, ties: Vec::new() };
    let mut referrers = std::collections::HashMap::new();
    for a in &dt.algs {
        for t in crate::checks::table_steps(&a.body) {
            referrers.insert(t, a.vars.names.clone());
        }
    }
    for (ti, t) in ts.iter_mut().enumerate().filter_map(|(i, t)| Some((i, t.as_mut().ok()?))) {
        ty.cv.vars = Vars::default();
        // a table a step refers to: numbered after its referrer
        for n in referrers.get(&ti).into_iter().flatten() {
            ty.cv.vars.slot(n);
        }
        let span = if t.import.is_some() { 0..0 } else { t.pos..t.pos + t.raw.len() };
        let mut algs = sp.algs.iter().enumerate().filter(|(_, a)| span.contains(&a.pos)).map(|(k, _)| k);
        for c in t.rows.iter_mut().flat_map(|r| r.cells.iter_mut()) {
            let Body::Text(text) = &c.body else { continue };
            let body = match c.role {
                Role::Step if text.starts_with("<emu-alg") => algs.next().map(Body::Alg),
                Role::Name => field_of(text).map(|f| Body::Field(ty.cv.d.fields.intern(f))),
                Role::Type => ty.tty(text).map(Body::Ty),
                Role::Sig => ty.sig(text).map(Body::Sig),
                Role::Step => ty.stmt(text).map(Body::Stmt),
                Role::Data => ty.data(text),
                Role::Prose | Role::Head => continue,
            };
            c.body = match body {
                Some(b) => b,
                None if text.is_empty() => continue,
                None => Body::Kept(ty.cv.d.notes.intern(why(c.role, text)), text.clone()),
            };
        }
        t.vars = std::mem::take(&mut ty.cv.vars);
    }
    if !declare {
        return Tables { tables: ts, ties: ty.ties, declared: Declared::default() };
    }
    let ov = &g.overlay;
    let dty = |ty: &mut Typer, x: &str| {
        ty.cv.vars = Vars::default();
        ty.tty(x).ok_or_else(|| x.to_string())
    };
    let mut declared = Declared::default();
    for s in &ov.sorts {
        if let Some(x) = &s.ty {
            declared.sorts.push((s.name.clone(), dty(&mut ty, x)));
        }
    }
    for x in &ov.guards {
        declared.guards.push((x.op.clone(), dty(&mut ty, &x.ty)));
    }
    for f in &ov.fields {
        let rows = f.rows.iter().map(|(n, t)| (ty.cv.d.fields.intern(n), dty(&mut ty, t))).collect();
        declared.fields.push((f.of.clone(), f.slots, rows));
    }
    Tables { tables: ts, ties: ty.ties, declared }
}

/// A schema table's record sort, from its caption (singular), and whether it adds to an inherited schema.
pub fn schema(t: &Table) -> Option<(String, bool)> {
    if !matches!(t.kind, Kind::Fields | Kind::Slots) {
        return None;
    }
    let c = t.attr("caption")?;
    let sing = |x: &str| x.strip_suffix('s').unwrap_or(x).to_string();
    if let Some(x) = c.strip_prefix("Additional Fields of ") {
        return Some((sing(x), true));
    }
    if let Some(x) = c.strip_prefix("Internal Slots of ") {
        return Some((sing(x), false));
    }
    c.strip_suffix(" Fields").map(|x| (x.to_string(), false))
}

/// The sort the algorithms name for a schema whose own name is not a sort: the same words in
/// another case, without its ` Instance`, ` Record` or ` Event`, or `X Object Instance`.
pub fn sort_alias(d: &crate::decls::Decls, x: &str) -> Option<String> {
    if d.sorts.get(x).is_some() {
        return None;
    }
    let mut cands = vec![x.to_string()];
    for suf in [" Instance", " Record", " Event"] {
        if let Some(b) = x.strip_suffix(suf) {
            cands.push(b.to_string());
        }
    }
    if let Some(b) = x.strip_suffix(" Instance") {
        cands.push(format!("{b} Object Instance"));
    }
    cands.iter().find_map(|c| d.sorts.names.iter().find(|n| n.eq_ignore_ascii_case(c)).cloned())
}

/// The printing context: declarations, and each `<emu-alg>` body printed from the data.
pub struct Pr<'a> {
    pub d: &'a crate::decls::Decls,
    pub alg: &'a dyn Fn(usize) -> String,
}

/// A cell's text; an algorithm's lines dedented by `pad`.
fn body_text(p: &Pr, vars: &[String], b: &Body, pad: usize) -> String {
    let d = p.d;
    match b {
        Body::Op(c) => d.ops[*c].clone(),
        Body::Component(f) => d.fields.name(*f).to_string(),
        Body::Name(x) | Body::Kept(_, x) => x.clone(),
        Body::Lines(bs) => bs.iter().map(|x| body_text(p, vars, x, pad)).collect::<Vec<_>>().join("<br>\n"),
        Body::Dfn(x) => format!("<dfn>{}</dfn>", body_text(p, vars, x, pad)),
        Body::Code(x) => format!("`{}`", body_text(p, vars, x, pad)),
        Body::Link(h, x) => format!("<a href=\"{h}\">{}</a>", body_text(p, vars, x, pad)),
        Body::Alg(k) => {
            let pre = " ".repeat(pad);
            let s = (p.alg)(*k);
            let body: Vec<&str> = s.split('\n').map(|l| l.strip_prefix(&pre).unwrap_or(l)).collect();
            format!("<emu-alg>{}</emu-alg>", body.join("\n"))
        }
        Body::Field(f) => format!("[[{}]]", d.fields.name(*f)),
        Body::Ty(t) => tty_text(d, vars, t),
        Body::Sig(s) => sig_text(d, vars, s),
        Body::Stmt(s) => crate::print::stmt_text(d, vars, s).unwrap_or_default(),
        Body::Expr(e) => crate::print::expr_text(d, vars, e),
        Body::Text(t) => t.clone(),
    }
}

fn nl(out: &mut String, col: usize) {
    out.push('\n');
    out.push_str(&" ".repeat(col));
}

fn print_row(p: &Pr, vars: &[String], r: &Row, col: usize, out: &mut String) {
    out.push_str(&"\n".repeat(r.gap));
    nl(out, col);
    out.push_str(&format!("<tr{}>", attrs_text(&r.attrs)));
    for c in &r.cells {
        let tag = if c.head { "th" } else { "td" };
        out.push_str(&"\n".repeat(c.gap));
        nl(out, col + 2);
        out.push_str(&format!("<{tag}{}>", attrs_text(&c.attrs)));
        let text = body_text(p, vars, &c.body, col + 4);
        if c.block {
            for l in text.split('\n').filter(|_| !text.is_empty()) {
                out.push('\n');
                if !l.is_empty() {
                    out.push_str(&" ".repeat(col + 4));
                }
                out.push_str(l);
            }
            nl(out, col + 2);
        } else {
            out.push_str(&text);
        }
        out.push_str(&format!("</{tag}>"));
    }
    nl(out, col);
    out.push_str("</tr>");
}

/// A table printed from its parsed form.
pub fn print(p: &Pr, t: &Table) -> String {
    let c = t.col;
    let v = &t.vars.names;
    let mut out = format!("<emu-table{}>", attrs_text(&t.attrs));
    if let Some(x) = &t.caption {
        nl(&mut out, c + 2);
        out.push_str(&format!("<emu-caption>{x}</emu-caption>"));
    }
    nl(&mut out, c + 2);
    out.push_str(&format!("<table{}>", attrs_text(&t.table_attrs)));
    let mut rows = t.rows.iter();
    if t.thead {
        nl(&mut out, c + 4);
        out.push_str("<thead>");
        if let Some(r) = rows.next() {
            print_row(p, v, r, c + 6, &mut out);
        }
        nl(&mut out, c + 4);
        out.push_str("</thead>");
    }
    for r in rows {
        print_row(p, v, r, c + 4, &mut out);
    }
    nl(&mut out, c + 2);
    out.push_str("</table>");
    nl(&mut out, c);
    out.push_str("</emu-table>");
    out
}

/// Tables printed back, by kind and role: the figures and the tables that differ.
pub fn report(sp: &Spec, p: &Pr, all: &Tables, verbose: bool) -> bool {
    let ts = &all.tables;
    let mut by_kind: std::collections::BTreeMap<Kind, (usize, usize)> = Default::default();
    let mut by_role: std::collections::BTreeMap<&str, (usize, usize)> = Default::default();
    let (mut bad, mut verbatim, mut kept) = (0, 0, 0);
    let mut distinct: HashMap<String, bool> = HashMap::new();
    for t in ts {
        let t = match t {
            Ok(t) => t,
            Err(e) => {
                bad += 1;
                eprintln!("table does not parse: {e}");
                continue;
            }
        };
        let id = t.attr("id").or(t.attr("caption")).unwrap_or("-");
        if verbose {
            let num = t.clause.map_or("-", |c| sp.clauses[c].number.as_str());
            println!("table\t{}\t§{num}\t{:?}\t{}\t{id}", t.line, t.kind, t.rows.len() - 1);
        }
        let e = by_kind.entry(t.kind).or_default();
        e.0 += 1;
        e.1 += t.rows.len() - 1;
        let out = print(p, t);
        if !t.figure && out != t.raw {
            bad += 1;
            let (x, y) = t.raw.lines().zip(out.lines()).find(|(x, y)| x != y).unwrap_or(("", ""));
            eprintln!("table differs at spec.html:{}:\n  src: {x}\n  out: {y}", t.line);
        }
        for c in t.rows.iter().flat_map(|r| &r.cells) {
            let text = body_text(p, &t.vars.names, &c.body, 0);
            if text.is_empty() {
                continue;
            }
            if !c.block && text.contains('\n') && matches!(c.body, Body::Text(_)) {
                verbatim += 1;
            }
            let ok = !matches!(c.body, Body::Text(_) | Body::Kept(..));
            let role = match c.role {
                Role::Name => "names as [[F]]",
                Role::Type => "type phrases",
                Role::Sig => "signatures",
                Role::Step => "steps",
                Role::Data => "data cells as expressions",
                Role::Prose | Role::Head => continue,
            };
            let e = by_role.entry(role).or_default();
            e.0 += usize::from(ok);
            e.1 += 1;
            if c.role == Role::Type {
                distinct.insert(text.clone(), ok);
            }
            if let Body::Kept(k, _) = c.body {
                kept += 1;
                if verbose {
                    println!("kept\t{}\t{id}\t{text}", p.d.notes.name(k));
                }
            }
        }
    }
    let pct = |a: usize, b: usize| format!("{:.1}%", 100.0 * a as f64 / b.max(1) as f64);
    println!("tables {} differ {}", ts.len(), bad);
    for (k, (n, r)) in &by_kind {
        println!("  {k:?}: {n} tables, {r} rows");
    }
    for (r, (ok, n)) in &by_role {
        println!("{r}: {ok} of {n} cells parsed ({})", pct(*ok, *n));
    }
    let dok = distinct.values().filter(|&&v| v).count();
    println!("type phrases, distinct: {dok} of {}; cells kept verbatim (irregular layout): {verbatim}", distinct.len());
    println!("cells without a data shape (residue channel (c), by kind): {kept}");
    let schemas: Vec<(String, bool)> = ts.iter().flatten().filter_map(schema).collect();
    let known = schemas.iter().filter(|(x, _)| p.d.sorts.get(x).is_some()).count();
    let aliased = schemas.iter().filter(|(x, _)| sort_alias(p.d, x).is_some()).count();
    println!(
        "record schemas: {} ({} additional), {known} of them sorts the algorithms name, {aliased} aliases of one",
        schemas.len(),
        schemas.iter().filter(|x| x.1).count()
    );
    if verbose {
        for (x, add) in &schemas {
            let k = if p.d.sorts.get(x).is_some() { "known".to_string() } else { sort_alias(p.d, x).map(|a| format!("alias of {a}")).unwrap_or_default() };
            println!("    schema\t{x}\t{}\t{k}", if *add { "additional" } else { "" });
        }
    }
    println!("cells with a tie left on declaration order: {}", all.ties.len());
    for x in &all.ties {
        println!("    tie: {x}");
    }
    bad == 0
}
