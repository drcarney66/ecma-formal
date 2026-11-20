//! The realm's built-in objects, read from the clause tree of clauses 19-28, B.2, %ThrowTypeError%
//! and %ForInIteratorPrototype% under §18's conventions: each object's names, kind, [[Prototype]],
//! slots, behaviour (CreateBuiltinFunction's arguments) and its function and accessor properties.
//! Every container bullet and heading form is read or explicitly ignored; any other is an error.

use crate::overlay::Op;
use crate::spec::{Clause, Spec};
use crate::text::{squash, strip_tags, unescape};
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Clone, Debug, PartialEq)]
pub enum Key {
    Str(String),
    /// a well-known symbol by its description: `Symbol.iterator`
    Sym(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Val {
    Undefined,
    Bool(bool),
    Str(String),
    /// a Number by its IEEE 754 bits
    Number(u64),
    Obj(usize),
    /// a well-known symbol by its description
    Sym(String),
    /// _realm_.[[GlobalEnv]].[[GlobalThisValue]], of the realm being created
    GlobalThis,
    /// the object a clause's algorithm creates
    Created(usize, usize),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Attrs {
    pub writable: bool,
    pub enumerable: bool,
    pub configurable: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum PVal {
    Data(Val),
    Accessor { get: Option<usize>, set: Option<usize> },
}

#[derive(Clone, Debug)]
pub struct Prop {
    pub key: Key,
    pub val: PVal,
    pub attrs: Attrs,
    pub clause: usize,
    pub annex_b: bool,
    /// a `normative-optional` clause's
    pub optional: bool,
    /// one a host may omit ("may omit the *"K"* property of the global object")
    pub omittable: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Behaviour {
    /// a spec clause's algorithm: clause index, index among its algorithms
    Alg(usize, usize),
    /// an overlay operation, by clause id
    Overlay(String),
}

/// CreateBuiltinFunction's arguments, and the attributes of "length" and "name".
#[derive(Clone, Debug)]
pub struct Fun {
    /// none: a behaviour given in prose
    pub alg: Option<Behaviour>,
    pub length: u64,
    pub name: Key,
    pub prefix: Option<String>,
    pub ctor: bool,
    /// CreateIntrinsics' _async_: described as async ("This async function")
    pub is_async: bool,
    pub length_attrs: Attrs,
    pub name_attrs: Attrs,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Ordinary,
    /// an exotic object, by the clause of its `<dfn>`
    Exotic(usize),
}

#[derive(Clone, Debug)]
pub struct Obj {
    /// intrinsic names without `%`: `Array.prototype`
    pub names: Vec<String>,
    pub path: String,
    pub clause: usize,
    pub kind: Kind,
    /// none: *null*
    pub proto: Option<usize>,
    pub extensible: bool,
    pub slots: Vec<(String, Val)>,
    pub fun: Option<Fun>,
    pub props: Vec<Prop>,
    pub annex_b: bool,
    pub optional: bool,
}

/// The objects in creation order (each after its [[Prototype]]), the global object's
/// properties, and those of every Module Namespace Object (§28.3).
pub struct Realm {
    pub objs: Vec<Obj>,
    pub globals: Vec<Prop>,
    pub namespace: Vec<Prop>,
}

impl Realm {
    pub fn by_name(&self, n: &str) -> Option<usize> {
        self.objs.iter().position(|o| o.names.iter().any(|x| x == n))
    }
    pub fn by_path(&self, p: &str) -> Option<usize> {
        self.objs.iter().position(|o| o.path == p)
    }
    /// The functions whose behaviour is prose.
    pub fn prose(&self) -> Vec<usize> {
        (0..self.objs.len()).filter(|&o| self.objs[o].fun.as_ref().is_some_and(|f| f.alg.is_none())).collect()
    }
}

/// §18 ¶ "Unless otherwise specified every built-in function and every built-in constructor has
/// the Function prototype object … as the value of its [[Prototype]] internal slot"; ¶ "Unless
/// otherwise specified every built-in prototype object has the Object prototype object …".
pub fn default_proto(is_fun: bool) -> &'static str {
    if is_fun {
        "Function.prototype"
    } else {
        "Object.prototype"
    }
}

/// §18 ¶ "Unless specified otherwise, the [[Extensible]] internal slot of a built-in object
/// initially has the value *true*."
pub const DEFAULT_EXTENSIBLE: bool = true;

/// §18 ¶ "Unless otherwise specified, the *"length"* property of a built-in function object has
/// the attributes { [[Writable]]: *false*, [[Enumerable]]: *false*, [[Configurable]]: *true* }"
/// (the same for *"name"*).
pub const FUN_PROP_ATTRS: Attrs = Attrs { writable: false, enumerable: false, configurable: true };

/// §18 ¶ "Every other data property described in clauses 19 through 28 and in Annex B.2 has the
/// attributes { [[Writable]]: *true*, [[Enumerable]]: *false*, [[Configurable]]: *true* } unless
/// otherwise specified."
pub const DATA_ATTRS: Attrs = Attrs { writable: true, enumerable: false, configurable: true };

/// §18 ¶ "Every accessor property described in clauses 19 through 28 and in Annex B.2 has the
/// attributes { [[Enumerable]]: *false*, [[Configurable]]: *true* } unless otherwise specified."
pub const ACCESSOR_ATTRS: Attrs = Attrs { writable: false, enumerable: false, configurable: true };

/// §18 ¶ "Unless otherwise specified, the *"length"* property … is the largest number of named
/// arguments shown in the subclause heading for the function description. Optional parameters
/// and rest parameters are not included"; where the heading shows none, the parameters the
/// description's prose names.
pub fn default_length(c: &Clause, own: &str) -> u64 {
    let h = crate::header::parse(c);
    let ps = if h.params.is_empty() && !c.h1_text().contains('(') { crate::header::prose_params(own) } else { h.params };
    ps.iter().filter(|p| !p.optional && !p.rest).count() as u64
}

/// §18 ¶ "the value of the *"name"* property is a String … For functions that are specified as
/// properties of objects, the name value is the property name string used to access the
/// function. Functions that are specified as get or set accessor functions of built-in properties
/// have *"get"* or *"set"* … passed to the _prefix_ parameter"; a Symbol key's description in
/// brackets.
pub fn name_string(prefix: &Option<String>, name: &Key) -> String {
    let n = match name {
        Key::Str(s) => s.clone(),
        Key::Sym(d) => format!("[{d}]"),
    };
    match prefix {
        Some(p) => format!("{p} {n}"),
        None => n,
    }
}

/// Container bullets that state nothing the table holds: defaults, negatives, descriptions of
/// behaviour, global names (the global object's), and value properties (with their values).
const IGNORED: &[&str] = &[
    "is an ordinary object",
    "is itself an ordinary object",
    "has the following",
    "has properties that are",
    "may be used as the value",
    "may have host-defined properties",
    "is not ",
    "does not have",
    "is a subclass of",
    "is a standard built-in function object that inherits",
    "is never directly accessible",
    "is a function whose behaviour",
    "is the initial value of the",
    "is created before control",
    "is an intrinsic object that has the structure",
    "is designed to be subclassable",
    "creates ",
    "also creates ",
    "acts as ",
    "along with ",
    "contains two functions",
    "will throw an error when invoked",
    "when called as a function",
    "returns ",
    "performs a type conversion",
];

/// The B.2 subtree: its objects and properties are optional (B.2's own status).
const ANNEX_B: &str = "sec-additional-built-in-properties";
/// The clauses whose function and value clauses are properties of the global object.
const GLOBAL: &[&str] = &["sec-global-object", "sec-additional-properties-of-the-global-object"];
/// The tables whose Global Name column names the global object's intrinsic-valued properties.
const GLOBAL_TABLES: &[&str] = &["table-well-known-intrinsic-objects", "table-additional-well-known-intrinsic-objects"];

/// The Numbers the text describes instead of writing: the Number value (§6.1.6.1) of each
/// described quantity, pinned as IEEE 754 binary64 bits (no real arithmetic here).
pub const DESCRIBED: &[(&str, u64)] = &[
    ("the Number value for the magnitude of the difference between 1 and the smallest value greater than 1 that is representable as a Number value, which is approximately 2.2204460492503130808472633361816 × 10^-16", 0x3CB0_0000_0000_0000),
    ("the largest positive finite Number, which is approximately 1.7976931348623157 × 10^308", 0x7FEF_FFFF_FFFF_FFFF),
    ("the smallest positive value of the Number type, which is approximately 5 × 10^-324", 0x0000_0000_0000_0001),
    ("the Number value for e, the base of the natural logarithms, which is approximately 2.7182818284590452354", 0x4005_BF0A_8B14_5769),
    ("the Number value for the natural logarithm of 10, which is approximately 2.302585092994046", 0x4002_6BB1_BBB5_5516),
    ("the Number value for the natural logarithm of 2, which is approximately 0.6931471805599453", 0x3FE6_2E42_FEFA_39EF),
    ("the Number value for the base-10 logarithm of e, the base of the natural logarithms; this value is approximately 0.4342944819032518", 0x3FDB_CB7B_1526_E50E),
    ("the Number value for the base-2 logarithm of e, the base of the natural logarithms; this value is approximately 1.4426950408889634", 0x3FF7_1547_652B_82FE),
    ("the Number value for π, the ratio of the circumference of a circle to its diameter, which is approximately 3.1415926535897932", 0x4009_21FB_5444_2D18),
    ("the Number value for the square root of ½, which is approximately 0.7071067811865476", 0x3FE6_A09E_667F_3BCD),
    ("the Number value for the square root of 2, which is approximately 1.4142135623730951", 0x3FF6_A09E_667F_3BCD),
];
/// Clauses outside 19-28 that specify a Table 6 object.
const EXTRA: &[&str] = &["sec-%throwtypeerror%", "sec-%foriniteratorprototype%-object", ANNEX_B];

fn plain(raw: &str) -> String {
    squash(&unescape(&strip_tags(raw)))
}

/// The clause tree: each clause's parent (an instance's: the instance of its template's parent
/// if that is a template) and whether it is a template.
struct Tree {
    parent: Vec<Option<usize>>,
    tmpl: Vec<bool>,
}

fn tree(sp: &Spec) -> Tree {
    let n = sp.clauses.len();
    let (mut parent, mut tmpl) = (vec![None; n], vec![false; n]);
    let mut stack: Vec<usize> = Vec::new();
    for c in 0..n {
        let cl = &sp.clauses[c];
        if let Some(i) = &cl.inst {
            tmpl[i.of] = true;
            continue;
        }
        while stack.last().is_some_and(|&p| sp.clauses[p].end < cl.start) {
            stack.pop();
        }
        parent[c] = stack.last().copied();
        stack.push(c);
    }
    for c in 0..n {
        if let Some(i) = &sp.clauses[c].inst {
            parent[c] = parent[i.of].map(|p| if tmpl[p] { instance(sp, p, &i.name).unwrap_or(p) } else { p });
        }
    }
    Tree { parent, tmpl }
}

fn instance(sp: &Spec, of: usize, name: &str) -> Option<usize> {
    sp.clauses.iter().position(|c| c.inst.as_ref().is_some_and(|i| i.of == of && i.name == name))
}

/// The clause's own text: its body before its first subclause.
fn own(html: &str, c: &Clause) -> String {
    let b = c.body(html);
    let h = b.find("</h1>").map_or(0, |i| i + 5);
    let stop = ["<emu-clause", "<emu-annex"].iter().filter_map(|x| b[h..].find(x)).min().map_or(b.len(), |i| h + i);
    b[..stop].to_string()
}

/// The top-level `<li>` contents of the `<ul>` opened just before `from`, and the offset after it.
fn items(s: &str, from: usize) -> (Vec<String>, usize) {
    let (mut depth, mut out, mut i, mut cur) = (1, Vec::new(), from, None);
    while let Some(k) = s[i..].find('<') {
        let p = i + k;
        let r = &s[p..];
        if r.starts_with("<ul>") || r.starts_with("<ul ") {
            depth += 1;
        } else if r.starts_with("</ul>") {
            depth -= 1;
            if depth == 0 {
                return (out, p + 5);
            }
        } else if depth == 1 && (r.starts_with("<li>") || r.starts_with("<li ")) {
            cur = Some(p + r.find('>').unwrap_or(0) + 1);
        } else if depth == 1 && r.starts_with("</li>") {
            if let Some(a) = cur.take() {
                out.push(s[a..p].to_string());
            }
        }
        i = p + 1;
    }
    (out, s.len())
}

/// The object descriptions of a clause's own text: `<p>The|Each … constructor|object:</p>` and
/// the bullets of the `<ul>` after it.
fn containers(own: &str) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(k) = own[i..].find(":</p>") {
        let end = i + k;
        i = end + 5;
        let Some(p) = own[..end].rfind("<p>").map(|x| x + 3).filter(|&p| !own[p..end].contains("</p>")) else { continue };
        let subject = plain(&own[p..end]);
        let rest = own[i..].trim_start();
        let shaped = (subject.starts_with("The ") || subject.starts_with("Each ")) && (subject.ends_with(" constructor") || subject.ends_with(" object"));
        if !shaped || !rest.starts_with("<ul>") {
            continue;
        }
        let (bullets, after) = items(own, own.len() - rest.len() + 4);
        out.push((subject, bullets));
        i = after;
    }
    out
}

/// `{ [[Writable]]: *b*, [[Enumerable]]: *b*, [[Configurable]]: *b* }` after `lead`.
fn attrs_after(s: &str, lead: &str) -> Option<Attrs> {
    let i = s.find(lead)? + lead.len();
    let body = &s[i..i + s[i..].find('}')?];
    let get = |f: &str| body.find(&format!("[[{f}]]: *")).map(|k| body[k + f.len() + 7..].starts_with("true"));
    Some(Attrs { writable: get("Writable").unwrap_or(false), enumerable: get("Enumerable")?, configurable: get("Configurable")? })
}

/// The text between `lead` and the next `stop`.
fn between<'a>(s: &'a str, lead: &str, stop: &str) -> Option<&'a str> {
    let i = s.find(lead)? + lead.len();
    Some(&s[i..i + s[i..].find(stop)?])
}

/// A Number literal of the text, `*N*𝔽` / `*+0*𝔽`.
fn number(t: &str) -> Option<u64> {
    let n = t.strip_prefix('*')?.strip_suffix("*𝔽").or_else(|| t.strip_prefix('*')?.strip_suffix('*'))?;
    if n == "+0" {
        return Some(0);
    }
    n.parse::<u64>().ok()
}

fn number_bits(n: u64) -> u64 {
    (n as f64).to_bits()
}

/// A Number literal of a value sentence: `*NaN*`, `*±∞*𝔽`, or an integer `*N*𝔽` whose
/// magnitude is at most 2^53 (so its Number value is exact).
fn number_value(t: &str) -> Option<u64> {
    match t {
        "*NaN*" => return Some(0x7FF8_0000_0000_0000),
        "*+∞*𝔽" => return Some(f64::INFINITY.to_bits()),
        "*-∞*𝔽" => return Some(f64::NEG_INFINITY.to_bits()),
        _ => {}
    }
    let n = t.strip_prefix('*')?.strip_suffix("*𝔽")?;
    let (neg, m) = match n.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, n.strip_prefix('+').unwrap_or(n)),
    };
    let m: u64 = m.parse().ok().filter(|&m| m <= 1 << 53)?;
    let x = m as f64;
    Some(if neg { (-x).to_bits() } else { x.to_bits() })
}

/// The `<p>` paragraphs of a text outside its notes: plain (`<sup>` as `^`, no backticks), raw.
fn paragraphs(s: &str) -> Vec<(String, String)> {
    let mut t = s.to_string();
    while let Some(a) = t.find("<emu-note") {
        let e = t[a..].find("</emu-note>").map_or(t.len(), |e| a + e + 11);
        t.replace_range(a..e, "");
    }
    t.match_indices("<p>")
        .filter_map(|(a, _)| {
            let r = &t[a + 3..];
            let raw = &r[..r.find("</p>")?];
            Some((plain(&raw.replace("<sup>", "^")).replace('`', ""), raw.to_string()))
        })
        .collect()
}

/// The text without a trailing parenthetical: `X (see …)` → `X`.
fn unparen(t: &str) -> &str {
    if !t.ends_with(')') {
        return t;
    }
    let mut depth = 0;
    for (i, ch) in t.char_indices().rev() {
        match ch {
            ')' => depth += 1,
            '(' => {
                depth -= 1;
                if depth == 0 {
                    return t[..i].trim_end();
                }
            }
            _ => {}
        }
    }
    t
}

/// The cells of the rows of the table with the id: (header texts, rows of raw cells).
fn table(html: &str, id: &str) -> Option<(Vec<String>, Vec<Vec<String>>)> {
    let a = html.find(&format!("<emu-table id=\"{id}\""))?;
    let t = &html[a..a + html[a..].find("</emu-table>")?];
    let cells = |row: &str, tag: &str| -> Vec<String> {
        row.match_indices(&format!("<{tag}")).filter_map(|(i, _)| between(&row[i..], ">", &format!("</{tag}>")).map(str::to_string)).collect()
    };
    let mut rows = t.split("<tr>").skip(1);
    let head = cells(rows.next()?, "th").iter().map(|c| plain(c)).collect();
    Some((head, rows.map(|r| cells(r, "td")).collect()))
}

/// The well-known symbols' descriptions (`Symbol.iterator`), in the rows' order of their table.
pub fn well_known_symbols(html: &str) -> Result<Vec<String>, String> {
    let (_, rows) = table(html, "table-well-known-symbols").ok_or("realm: no table of well-known symbols")?;
    rows.iter()
        .filter_map(|r| r.first())
        .map(|c| plain(c).strip_prefix('%').and_then(|x| x.strip_suffix('%')).map(str::to_string).ok_or_else(|| format!("realm: a well-known symbol not of the form %Symbol.x%: {c}")))
        .collect()
}

/// A heading's property target: `P.k`, `P [ %Symbol.x% ]`, or a bare name.
enum Target {
    Bare(String),
    Path(String, Key),
}

fn target(t: &str) -> Result<Target, String> {
    if let Some((p, k)) = t.split_once(" [ ") {
        let k = k.strip_suffix(" ]").and_then(|k| k.strip_prefix('%')).and_then(|k| k.strip_suffix('%')).ok_or_else(|| format!("a symbol key not of the form [ %Symbol.x% ]: {t}"))?;
        return Ok(Target::Path(p.to_string(), Key::Sym(k.to_string())));
    }
    match t.rfind('.') {
        Some(i) if !t.ends_with('%') => Ok(Target::Path(t[..i].to_string(), Key::Str(t[i + 1..].to_string()))),
        _ => Ok(Target::Bare(t.to_string())),
    }
}

/// Every `%name%` written in the text.
fn percent_names(s: &str) -> HashSet<String> {
    let mut out = HashSet::new();
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' && i + 1 < b.len() && b[i + 1].is_ascii_alphabetic() {
            let mut j = i + 1;
            while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_' || b[j] == b'.') {
                j += 1;
            }
            if j < b.len() && b[j] == b'%' {
                out.insert(s[i + 1..j].to_string());
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    out
}

/// The `%Name%`s of the text that name no object of the realm (well-known symbols aside; the
/// lower-case ones are ids and §6.1.7.4's placeholders).
pub fn unresolved(html: &str, r: &Realm) -> Vec<String> {
    let mut v: Vec<String> = percent_names(html).into_iter().filter(|n| n.starts_with(|c: char| c.is_ascii_uppercase()) && !n.starts_with("Symbol.") && r.by_name(n).is_none()).collect();
    v.sort();
    v
}

/// The `<dfn>%X%</dfn>` names of a text.
fn dfn_names(s: &str) -> Vec<String> {
    s.match_indices("<dfn>%").filter_map(|(a, _)| between(&s[a..], "<dfn>%", "%</dfn>")).filter(|n| !n.contains('<')).map(str::to_string).collect()
}

struct Builder<'a> {
    html: &'a str,
    sp: &'a Spec,
    ops: &'a [Op],
    tree: Tree,
    objs: Vec<Obj>,
    /// per object: the [[Prototype]] a bullet names (`Some(None)`: *null*)
    protos: Vec<Option<Option<String>>>,
    /// per object: a constructor's description
    ctors: Vec<bool>,
    names: HashMap<String, usize>,
    subjects: HashMap<String, usize>,
    /// clause → the object its container describes
    described: HashMap<usize, usize>,
    /// (object, clause, bullet)
    bullets: Vec<(usize, usize, String)>,
    /// (owner, key, value, clause)
    props: Vec<(Owner, Key, PropVal, usize)>,
    /// attributes a sentence outside the property's own clause states: (owner, key, attributes, clause)
    stated: Vec<(Owner, Key, Attrs, usize)>,
    /// the global properties a host may omit, with the clause that says so
    omittable: Vec<(String, usize)>,
    used_ops: BTreeSet<String>,
    percents: HashSet<String>,
}

#[derive(Clone, PartialEq)]
enum Owner {
    Name(String),
    Obj(usize),
    Global,
    /// every Module Namespace Object (§28.3)
    Namespace,
}

/// Where a property goes: an object's properties, the global object's, a namespace's.
enum Dest {
    Obj(usize),
    Global,
    Namespace,
}

/// The clause whose subclauses specify a Module Namespace Object's own properties.
pub const NAMESPACE: &str = "sec-module-namespace-objects";

enum PropVal {
    /// a function object, and the accessor half it is
    Fun(usize, Option<String>),
    /// the object an intrinsic name names
    Alias(String),
    Value(Val),
    /// the object a container subject describes
    Subject(String),
    /// the object a clause's container describes
    Described(usize),
    /// a global name's intrinsic (Table 6), which the clause the text refers to describes
    See(String, usize),
}

impl<'a> Builder<'a> {
    fn err(&self, c: usize, m: impl std::fmt::Display) -> String {
        format!("realm: {} (spec.html:{}): {m}", self.sp.clauses[c].id, crate::spec::line_of(self.html, self.sp.clauses[c].start))
    }

    fn in_scope(&self, c: usize) -> bool {
        let mut k = Some(self.sp.home(c));
        let mut top = c;
        while let Some(x) = k {
            if EXTRA.contains(&self.sp.clauses[x].id.as_str()) {
                return true;
            }
            top = x;
            k = self.tree.parent[x];
        }
        self.sp.clauses[top].number.parse::<u32>().is_ok_and(|n| (19..=28).contains(&n))
    }

    /// Whether the clause or an ancestor has one of the ids.
    fn under(&self, c: usize, ids: &[&str]) -> bool {
        let mut k = Some(self.sp.home(c));
        while let Some(x) = k {
            if ids.contains(&self.sp.clauses[x].id.as_str()) {
                return true;
            }
            k = self.tree.parent[x];
        }
        false
    }

    /// Whether the clause or an ancestor is `normative-optional`.
    fn optional(&self, c: usize) -> bool {
        let mut k = Some(self.sp.home(c));
        while let Some(x) = k {
            let st = self.sp.clauses[x].start;
            let tag = &self.html[self.html[..st].rfind('<').unwrap_or(st)..st];
            if tag.contains(" normative-optional") {
                return true;
            }
            k = self.tree.parent[x];
        }
        false
    }

    fn annex_b(&self, c: usize) -> bool {
        let mut k = Some(self.sp.home(c));
        while let Some(x) = k {
            if self.sp.clauses[x].id == ANNEX_B {
                return true;
            }
            k = self.tree.parent[x];
        }
        false
    }

    fn add(&mut self, c: usize, names: Vec<String>, path: String, fun: Option<Fun>) -> Result<usize, String> {
        let o = self.objs.len();
        for n in &names {
            if let Some(&p) = self.names.get(n) {
                return Err(self.err(c, format!("%{n}% names two objects ({} and {path})", self.objs[p].path)));
            }
            self.names.insert(n.clone(), o);
        }
        let (annex_b, optional) = (self.annex_b(c), self.optional(c));
        self.objs.push(Obj { names, path, clause: c, kind: Kind::Ordinary, proto: None, extensible: DEFAULT_EXTENSIBLE, slots: vec![], fun, props: vec![], annex_b, optional });
        self.protos.push(None);
        self.ctors.push(false);
        Ok(o)
    }

    /// The object a container describes: its "is %X%" bullet, a `%X%` subject, an earlier
    /// container's subject, an instance's "Each N constructor", or an instance's "Each N
    /// prototype object" (the value of the N.prototype clause that refers to this clause).
    fn identity(&mut self, c: usize, subject: &str, bullets: &[String]) -> Result<usize, String> {
        let mut named: Vec<String> = bullets
            .iter()
            .map(|b| plain(b))
            .filter_map(|b| {
                let r = b.strip_prefix("is %")?;
                let e = r.find('%')?;
                (r[e..] == *"%." || r[e..].starts_with("% (see ")).then(|| r[..e].to_string())
            })
            .collect();
        let from_subject = subject.strip_prefix("The %").and_then(|r| {
            let e = r.find('%')?;
            matches!(&r[e..], "% object" | "% intrinsic object").then(|| r[..e].to_string())
        });
        named.extend(from_subject.filter(|n| !named.contains(n)));
        if !named.is_empty() {
            let o = match named.iter().find_map(|n| self.names.get(n).copied()).or_else(|| self.subjects.get(subject).copied()) {
                Some(o) => o,
                None => return self.add(c, named.clone(), named[0].clone(), None),
            };
            for n in named {
                match self.names.get(&n) {
                    Some(&p) if p != o => return Err(self.err(c, format!("%{n}% names two objects ({} and {})", self.objs[p].path, self.objs[o].path))),
                    Some(_) => {}
                    None => {
                        self.names.insert(n.clone(), o);
                        self.objs[o].names.push(n);
                    }
                }
            }
            return Ok(o);
        }
        if let Some(&o) = self.subjects.get(subject) {
            return Ok(o);
        }
        let inst = self.sp.clauses[c].inst.as_ref().map(|i| i.name.clone());
        if let Some(n) = inst {
            if subject == format!("Each {n} constructor") {
                return self.add(c, vec![n.clone()], n, None);
            }
            if subject == format!("Each {n} prototype object") {
                let href = format!("href=\"#{}\"", self.sp.clauses[self.sp.home(c)].id);
                let path = format!("{n}.prototype");
                let v = (0..self.sp.clauses.len()).find(|&k| {
                    let kc = &self.sp.clauses[k];
                    kc.inst.as_ref().is_some_and(|i| i.name == n) && kc.ty.is_none() && kc.title() == path && own(self.html, kc).contains(&href)
                });
                if v.is_some() {
                    return self.add(c, vec![path.clone()], path, None);
                }
            }
        }
        Err(self.err(c, format!("a description whose object has no name: {subject}")))
    }

    fn container_pass(&mut self, c: usize) -> Result<(), String> {
        for (subject, bullets) in containers(&own(self.html, &self.sp.clauses[c])) {
            if subject.contains("global object") {
                continue;
            }
            let o = self.identity(c, &subject, &bullets)?;
            self.subjects.insert(subject.clone(), o);
            self.described.insert(c, o);
            if subject.ends_with(" constructor") {
                self.ctors[o] = true;
            }
            self.bullets.extend(bullets.into_iter().map(|b| (o, c, b)));
        }
        Ok(())
    }

    fn function_pass(&mut self, c: usize) -> Result<(), String> {
        let cl = &self.sp.clauses[c];
        let own = own(self.html, cl);
        let h = cl.h1_text();
        let (prefix, t) = match h.split_once(' ') {
            Some((p @ ("get" | "set"), rest)) => (Some(p.to_string()), rest.to_string()),
            _ => (None, h.split_once(" (").map(|x| x.0.to_string()).ok_or_else(|| self.err(c, format!("a built-in function heading without parameters: {h}")))?),
        };
        let alg = self.sp.algs.iter().find(|a| a.clause == Some(c) && !a.example() && !a.tmpl).map(|a| Behaviour::Alg(c, a.idx));
        let ops = self.ops;
        let prose = ops.iter().find(|x| x.behaviour_of.as_deref() == Some(cl.id.as_str()));
        let alg = match (alg, prose) {
            (Some(_), Some(op)) => return Err(self.err(c, format!("overlay {} gives a behaviour to a function with an algorithm", op.id))),
            (None, Some(op)) => {
                self.used_ops.insert(op.id.clone());
                Some(Behaviour::Overlay(op.id.clone()))
            }
            (a, None) => a,
        };
        let tg = target(&t).map_err(|e| self.err(c, e))?;
        let name = match (&tg, own.contains("anonymous built-in function")) {
            (_, true) => Key::Str(String::new()),
            (Target::Path(_, k), _) => k.clone(),
            (Target::Bare(n), _) => Key::Str(n.replace('%', "")),
        };
        let mut f = Fun { alg, length: default_length(cl, &own), name, prefix: prefix.clone(), ctor: false, is_async: own.contains("<p>This async function ") || own.contains("<p>This async method "), length_attrs: FUN_PROP_ATTRS, name_attrs: FUN_PROP_ATTRS };
        for lead in ["The *\"length\"* property of this function is ", "The *\"length\"* property of this method is "] {
            if let Some(n) = between(&own, lead, ".</p>") {
                f.length = number(&plain(n)).ok_or_else(|| self.err(c, format!("a \"length\" sentence: {n}")))?;
            }
        }
        for lead in [
            "The value of the *\"name\"* property of this function is ",
            "The value of the *\"name\"* property of this method is ",
            "The initial value of the *\"name\"* property of this function is ",
        ] {
            if let Some(n) = between(&own, lead, ".</p>") {
                let want = format!("*\"{}\"*", name_string(&f.prefix, &f.name));
                if n != want {
                    return Err(self.err(c, format!("a \"name\" sentence {n} where §18 gives {want}")));
                }
            }
        }
        if let Some(a) = attrs_after(&own, "The *\"length\"* property of this function has the attributes { ") {
            f.length_attrs = a;
        }
        if let Some(a) = attrs_after(&own, "The *\"name\"* property of this function has the attributes { ") {
            f.name_attrs = a;
        }
        let extensible = !own.contains("The value of the [[Extensible]] internal slot of this function is *false*.");
        let o = match &tg {
            Target::Bare(n) if prefix.is_none() => match self.tree.parent[c].and_then(|p| self.described.get(&p).copied()) {
                Some(o) => {
                    if self.objs[o].fun.is_some() {
                        return Err(self.err(c, format!("a second behaviour for {}", self.objs[o].path)));
                    }
                    self.objs[o].fun = Some(f);
                    o
                }
                None => {
                    let names = dfn_names(&own);
                    if names.is_empty() {
                        return Err(self.err(c, format!("a built-in function {n} that is no property and has no <dfn>%name%</dfn>")));
                    }
                    let o = self.add(c, names, n.replace('%', ""), Some(f))?;
                    if self.under(c, GLOBAL) {
                        self.props.push((Owner::Global, Key::Str(n.clone()), PropVal::Fun(o, None), c));
                    }
                    o
                }
            },
            Target::Bare(n) => return Err(self.err(c, format!("an accessor of no property: {n}"))),
            Target::Path(p, k) => {
                let mut names = dfn_names(&own);
                let dotted = t.replace('%', "");
                if matches!(k, Key::Str(_)) && self.percents.contains(&dotted) && !names.contains(&dotted) {
                    names.push(dotted);
                }
                let path = match &prefix {
                    Some(x) => format!("{x} {t}"),
                    None => t.clone(),
                };
                let o = self.add(c, names, path, Some(f))?;
                self.props.push((Owner::Name(p.replace('%', "")), k.clone(), PropVal::Fun(o, prefix.clone()), c));
                o
            }
        };
        self.objs[o].extensible &= extensible;
        Ok(())
    }

    /// The key and value text of the clause's "The initial value of the K property is %Y%".
    fn alias(&self, c: usize) -> Option<(String, String)> {
        let own = own(self.html, &self.sp.clauses[c]);
        let s = plain(between(&own, "<p>The initial value of the ", "</p>")?);
        let (k, v) = s.split_once(" property is %")?;
        Some((k.to_string(), v.to_string()))
    }

    /// "The initial value of the K property is %Y%": the property K of the heading's object is
    /// the object Y.
    fn alias_pass(&mut self, c: usize) -> Result<(), String> {
        let Some((k, v)) = self.alias(c) else { return Ok(()) };
        let v = v.split(['%']).next().unwrap_or("").to_string();
        let k = k.trim_matches('`');
        let cl = &self.sp.clauses[c];
        let key = if let Some(x) = k.strip_prefix("*\"").and_then(|x| x.strip_suffix("\"*")) {
            Key::Str(x.to_string())
        } else if let Some(x) = k.strip_prefix('%').and_then(|x| x.strip_suffix('%')) {
            Key::Sym(x.to_string())
        } else {
            return Err(self.err(c, format!("an alias of an unread key: {k}")));
        };
        let Target::Path(p, hk) = target(&cl.title()).map_err(|e| self.err(c, e))? else {
            return Err(self.err(c, "an alias whose heading is no property"));
        };
        if hk != key {
            return Err(self.err(c, format!("an alias of {key:?} under the heading of {hk:?}")));
        }
        self.props.push((Owner::Name(p.replace('%', "")), key, PropVal::Alias(v), c));
        Ok(())
    }

    /// A value property's clause (a typeless clause whose heading is a property, or a name under
    /// the global object): its value sentence, or its accessor sentence; "may omit" sentences.
    fn value_pass(&mut self, c: usize) -> Result<(), String> {
        let cl = &self.sp.clauses[c];
        let own = own(self.html, cl);
        let ps = paragraphs(&own);
        for (p, _) in &ps {
            if let Some(k) = between(p, "may omit the *\"", "\"* property of the global object") {
                self.omittable.push((k.to_string(), c));
            }
        }
        let title = cl.title();
        let global = self.under(c, GLOBAL);
        let title = title.strip_suffix(" ( . . . )").filter(|_| global).unwrap_or(&title).to_string();
        let (owner, key) = match target(&title) {
            Ok(Target::Path(p, k)) if !p.contains(' ') && !matches!(&k, Key::Str(x) if x.contains(' ')) => (Owner::Name(p.replace('%', "")), k),
            Ok(Target::Bare(n)) if global && !n.contains(' ') => (Owner::Global, Key::Str(n)),
            Ok(Target::Bare(n)) if self.under(c, &[NAMESPACE]) && n.starts_with("%Symbol.") => (Owner::Namespace, Key::Sym(n.trim_matches('%').to_string())),
            _ => return Ok(()),
        };
        if self.alias(c).is_some() {
            return self.alias_pass(c);
        }
        let heading = title.replace(' ', "");
        if let Some((p, raw)) = ps.iter().find(|(p, _)| p.contains(" is an accessor property with attributes {")) {
            if p.split(" is an accessor").next().map(|x| x.replace(' ', "")) != Some(heading.clone()) {
                return Err(self.err(c, format!("an accessor sentence of another property: {p}")));
            }
            let a = attrs_after(raw, "is an accessor property with attributes { ").ok_or_else(|| self.err(c, format!("accessor attributes: {p}")))?;
            self.stated.push((owner, key, a, c));
            return Ok(());
        }
        if let [(p, raw)] = &ps[..] {
            if p == "See ." && owner == Owner::Global {
                let href = between(raw, "href=\"#", "\"").ok_or_else(|| self.err(c, "a See without a reference"))?;
                let to = self.sp.clauses.iter().position(|x| x.id == href).ok_or_else(|| self.err(c, format!("See {href}: no such clause")))?;
                let Key::Str(k) = &key else { unreachable!() };
                self.props.push((owner, key.clone(), PropVal::See(k.clone(), to), c));
                return Ok(());
            }
        }
        let leads = ["The initial value of ", "The value of ", "The Number value for "];
        let vs: Vec<&(String, String)> = ps.iter().filter(|(p, _)| leads.iter().any(|l| p.starts_with(l))).collect();
        let [(p, raw)] = &vs[..] else {
            return Err(self.err(c, format!("a value property with {} value sentences", vs.len())));
        };
        let p = p.strip_suffix('.').unwrap_or(p);
        let v = if p.starts_with("The Number value for ") {
            format!("the{}", &p[3..])
        } else {
            let (subj, v) = p.split_once(" is ").ok_or_else(|| self.err(c, format!("a value sentence: {p}")))?;
            let subj = subj.strip_prefix("The initial value of ").or_else(|| subj.strip_prefix("The value of ")).unwrap_or(subj);
            let k = match &key {
                Key::Str(k) => format!("*\"{k}\"*"),
                Key::Sym(d) => format!("%{d}%"),
            };
            let ok = subj.replace(' ', "") == heading
                || [format!("the {k} property"), format!("the {k} data property")].contains(&subj.to_string())
                || (owner == Owner::Global && subj.starts_with(&format!("the {k} property of the global object")))
                || self.sp.clauses[c].inst.as_ref().is_some_and(|i| subj == format!("the {k} property of the prototype for a given {} constructor", i.name));
            if !ok {
                return Err(self.err(c, format!("a value sentence of another property: {subj}")));
            }
            if subj.ends_with(" in a Realm Record _realm_") {
                if v != "_realm_.[[GlobalEnv]].[[GlobalThisValue]]" {
                    return Err(self.err(c, format!("a realm-relative value: {v}")));
                }
                self.props.push((owner, key, PropVal::Value(Val::GlobalThis), c));
                return Ok(());
            }
            v.to_string()
        };
        let val = self.value(c, &v, raw)?;
        self.props.push((owner, key, val, c));
        Ok(())
    }

    /// The value a value sentence's predicate names.
    fn value(&self, c: usize, v: &str, raw: &str) -> Result<PropVal, String> {
        let inst = self.sp.clauses[c].inst.as_ref().map(|i| i.name.as_str());
        if let Some(&(_, bits)) = DESCRIBED.iter().find(|(d, _)| *d == v) {
            return Ok(PropVal::Value(Val::Number(bits)));
        }
        if v == "an object created by the following steps:" {
            let a = self.sp.algs.iter().find(|a| a.clause == Some(c) && !a.example()).ok_or_else(|| self.err(c, "a value created by steps without an algorithm"))?;
            return Ok(PropVal::Value(Val::Created(c, a.idx)));
        }
        if let Some(n) = inst {
            if v == "the constructor itself" {
                return Ok(PropVal::Alias(n.to_string()));
            }
            if v == format!("the String value consisting of the name of the constructor (the name used instead of {n})") {
                return Ok(PropVal::Value(Val::Str(n.to_string())));
            }
            let own_proto = [format!("a {n} prototype object (). Each {n} constructor has a distinct prototype object"), format!("the corresponding {n} prototype intrinsic object ()")];
            if own_proto.contains(&v.to_string()) {
                let href = between(raw, "href=\"#", "\"").ok_or_else(|| self.err(c, "a prototype object without its clause"))?;
                let of = self.sp.clauses.iter().position(|x| x.id == href && x.inst.is_none()).ok_or_else(|| self.err(c, format!("no clause {href}")))?;
                let to = instance(self.sp, of, n).ok_or_else(|| self.err(c, format!("{href} has no {n} instance")))?;
                return Ok(PropVal::Described(to));
            }
            if v == format!("the Element Size value specified in for {n}") {
                let id = between(raw, "href=\"#", "\"").ok_or_else(|| self.err(c, "a table value without its table"))?;
                return Ok(PropVal::Value(Val::Number(self.cell_number(c, id, n, "Element Size")?)));
            }
        }
        if let Some(x) = v.strip_prefix("the ").and_then(|x| x.strip_suffix(" prototype object")) {
            return Ok(PropVal::Subject(format!("The {x} prototype object")));
        }
        let v = unparen(v);
        if let Some(n) = v.strip_prefix('%').and_then(|x| x.strip_suffix('%')).filter(|n| !n.contains(' ')) {
            return Ok(PropVal::Alias(n.to_string()));
        }
        if let Some(d) = v.strip_prefix("the well-known symbol %").and_then(|x| x.strip_suffix('%')) {
            let wk = table(self.html, "table-well-known-symbols").ok_or_else(|| self.err(c, "no table of well-known symbols"))?;
            if !wk.1.iter().any(|r| r.first().is_some_and(|x| plain(x) == format!("%{d}%"))) {
                return Err(self.err(c, format!("%{d}% is no well-known symbol")));
            }
            return Ok(PropVal::Value(Val::Sym(d.to_string())));
        }
        if v == "the empty String" {
            return Ok(PropVal::Value(Val::Str(String::new())));
        }
        if let Some(x) = v.strip_prefix("the String value ").unwrap_or(v).strip_prefix("*\"").and_then(|x| x.strip_suffix("\"*")) {
            return Ok(PropVal::Value(Val::Str(x.to_string())));
        }
        if v == "*undefined*" {
            return Ok(PropVal::Value(Val::Undefined));
        }
        if let Some(b) = number_value(v) {
            return Ok(PropVal::Value(Val::Number(b)));
        }
        Err(self.err(c, format!("an unread value: {v}")))
    }

    /// The Number in the column of the table's row whose first cell has `<dfn>%n%</dfn>`.
    fn cell_number(&self, c: usize, id: &str, n: &str, col: &str) -> Result<u64, String> {
        let (head, rows) = table(self.html, id).ok_or_else(|| self.err(c, format!("no table {id}")))?;
        let k = head.iter().position(|h| h == col).ok_or_else(|| self.err(c, format!("{id} has no column {col}")))?;
        let row = rows.iter().find(|r| r.first().is_some_and(|x| x.contains(&format!("<dfn>%{n}%</dfn>")))).ok_or_else(|| self.err(c, format!("{id} has no row for %{n}%")))?;
        let cell = row.get(k).map(|x| plain(x)).unwrap_or_default();
        Ok(number_bits(cell.parse().map_err(|_| self.err(c, format!("{id} {col} of %{n}%: {cell}")))?))
    }

    /// The owner's object (none: the global object).
    fn owner(&self, c: usize, o: &Owner) -> Result<Dest, String> {
        match o {
            Owner::Global => Ok(Dest::Global),
            Owner::Namespace => Ok(Dest::Namespace),
            Owner::Name(n) => self.lookup(c, n).map(Dest::Obj),
            Owner::Obj(o) => Ok(Dest::Obj(*o)),
        }
    }

    fn lookup(&self, c: usize, n: &str) -> Result<usize, String> {
        self.names.get(n).copied().ok_or_else(|| self.err(c, format!("%{n}% names no object")))
    }

    /// The clause of `<dfn …>name</dfn>`.
    fn dfn_clause(&self, c: usize, name: &str) -> Result<usize, String> {
        let at = self
            .html
            .match_indices(&format!(">{name}</dfn>"))
            .map(|(a, _)| a)
            .find(|&a| self.html[..a].rfind('<').is_some_and(|l| self.html[l..].starts_with("<dfn")))
            .ok_or_else(|| self.err(c, format!("no <dfn>{name}</dfn>")))?;
        (0..self.sp.clauses.len())
            .filter(|&k| self.sp.clauses[k].inst.is_none() && self.sp.clauses[k].start <= at && at < self.sp.clauses[k].end)
            .max_by_key(|&k| self.sp.clauses[k].start)
            .ok_or_else(|| self.err(c, format!("<dfn>{name}</dfn> outside every clause")))
    }

    fn bullet(&mut self, o: usize, c: usize, raw: &str) -> Result<(), String> {
        let b = plain(raw);
        if let Some(v) = b.strip_prefix("has a [[Prototype]] internal slot whose value is ") {
            let p = match v {
                "*null*." => None,
                _ => Some(v.strip_prefix('%').and_then(|x| x.strip_suffix("%.")).ok_or_else(|| self.err(c, format!("a [[Prototype]] bullet: {b}")))?.to_string()),
            };
            self.protos[o] = Some(p);
            return Ok(());
        }
        if b.strip_prefix("is %").is_some_and(|r| r.ends_with("%.") || r.contains("% (see ")) {
            return Ok(());
        }
        let exotic = b
            .strip_prefix("is an ")
            .or_else(|| b.strip_prefix("is a "))
            .and_then(|r| r.strip_suffix(" and has the internal methods specified for such objects."))
            .or_else(|| b.split_once("(Thus, it is an ").and_then(|x| x.1.strip_suffix(".)")))
            .filter(|x| x.ends_with(" exotic object"));
        if let Some(x) = exotic {
            self.objs[o].kind = Kind::Exotic(self.dfn_clause(c, x)?);
            return Ok(());
        }
        let slot = b
            .split_once("; it has a [[")
            .filter(|x| x.0.starts_with("is itself a"))
            .and_then(|x| x.1.split_once("]] internal slot with the value "))
            .or_else(|| b.strip_prefix("has a [[").or_else(|| b.strip_prefix("has an [[")).and_then(|r| r.split_once("]] internal slot whose value is ")));
        if let Some((f, v)) = slot {
            let v = v.strip_suffix('.').unwrap_or(v);
            let val = match v {
                "*true*" => Val::Bool(true),
                "*false*" => Val::Bool(false),
                "the empty String" => Val::Str(String::new()),
                _ => Val::Number(number_bits(number(v).ok_or_else(|| self.err(c, format!("a slot value: {b}")))?)),
            };
            match (f, &val) {
                ("Extensible", Val::Bool(x)) => self.objs[o].extensible = *x,
                _ => self.objs[o].slots.push((f.to_string(), val)),
            }
            return Ok(());
        }
        if let Some(v) = b.strip_prefix("has a *\"length\"* property whose initial value is ") {
            let (n, _) = v.split_once(" and whose attributes are ").ok_or_else(|| self.err(c, format!("a \"length\" property bullet: {b}")))?;
            let n = number_value(n).ok_or_else(|| self.err(c, format!("a \"length\" value: {b}")))?;
            let a = attrs_after(raw, "and whose attributes are { ").ok_or_else(|| self.err(c, format!("\"length\" attributes: {b}")))?;
            self.props.push((Owner::Obj(o), Key::Str("length".into()), PropVal::Value(Val::Number(n)), c));
            self.stated.push((Owner::Obj(o), Key::Str("length".into()), a, c));
            return Ok(());
        }
        if let Some(v) = b.strip_prefix("has a *\"length\"* property whose value is ").and_then(|v| v.strip_suffix('.')) {
            let n = number(v).ok_or_else(|| self.err(c, format!("a \"length\" bullet: {b}")))?;
            self.fun_mut(o, c)?.length = n;
            return Ok(());
        }
        if let Some(v) = b.strip_prefix("has a *\"name\"* property whose value is ").and_then(|v| v.strip_suffix('.')) {
            let n = if v == "the empty String" {
                String::new()
            } else if let Some(x) = v.strip_prefix("*\"").and_then(|x| x.strip_suffix("\"*")) {
                x.to_string()
            } else if let Some(x) = v.strip_prefix("the String value \"").and_then(|x| x.strip_suffix('"')) {
                x.to_string()
            } else if v.starts_with("the String value of the constructor name specified for it in") {
                self.table_name(o, c, raw)?
            } else {
                return Err(self.err(c, format!("a \"name\" bullet: {b}")));
            };
            self.fun_mut(o, c)?.name = Key::Str(n);
            return Ok(());
        }
        if b == "accepts any arguments and returns *undefined* when invoked." || b == "is itself a built-in function object." {
            if self.objs[o].fun.is_none() {
                let home = &self.sp.clauses[self.sp.home(c)].id;
                let op = self.ops.iter().find(|x| x.behaviour_of.as_deref() == Some(home.as_str())).ok_or_else(|| self.err(c, "a function object with no algorithm: needs an overlay built-in function with behaviour-of"))?;
                let oc = Clause { id: op.id.clone(), ty: Some(op.ty.clone()), h1: op.h1.clone(), dl: op.dl.clone(), ..Default::default() };
                self.used_ops.insert(op.id.clone());
                let name = Key::Str(oc.title().replace('%', ""));
                let f = Fun { alg: Some(Behaviour::Overlay(op.id.clone())), length: default_length(&oc, ""), name, prefix: None, ctor: false, is_async: false, length_attrs: FUN_PROP_ATTRS, name_attrs: FUN_PROP_ATTRS };
                self.objs[o].fun = Some(f);
            }
            return Ok(());
        }
        if b.starts_with("is a constructor function object") {
            self.ctors[o] = true;
            return Ok(());
        }
        if b.starts_with("does not have a [[Construct]] internal method") {
            self.ctors[o] = false;
            return Ok(());
        }
        if IGNORED.iter().any(|p| b.starts_with(p)) {
            return Ok(());
        }
        Err(self.err(c, format!("an unread bullet: {b}")))
    }

    fn fun_mut(&mut self, o: usize, c: usize) -> Result<&mut Fun, String> {
        let e = self.err(c, format!("a function property of {}, which is no function", self.objs[o].path));
        self.objs[o].fun.as_mut().ok_or(e)
    }

    /// The first cell's name (before `<br>`) of the row of the bullet's table whose
    /// `<dfn>%N%</dfn>` names the object.
    fn table_name(&self, o: usize, c: usize, raw: &str) -> Result<String, String> {
        let id = between(raw, "href=\"#", "\"").ok_or_else(|| self.err(c, "a name bullet without its table"))?;
        let a = self.html.find(&format!("<emu-table id=\"{id}\"")).ok_or_else(|| self.err(c, format!("no table {id}")))?;
        let t = &self.html[a..a + self.html[a..].find("</emu-table>").unwrap_or(0)];
        let n = &self.objs[o].names[0];
        let at = t.find(&format!("<dfn>%{n}%</dfn>")).ok_or_else(|| self.err(c, format!("{id} has no row for %{n}%")))?;
        let row = t[..at].rfind("<td>").ok_or_else(|| self.err(c, "a row without cells"))?;
        Ok(squash(&t[row + 4..at].replace("<br>", "")))
    }
}

/// The realm table: every object of the scope, each after its [[Prototype]].
pub fn build(html: &str, sp: &Spec, ops: &[Op]) -> Result<Realm, String> {
    let mut b = Builder {
        html,
        sp,
        ops,
        tree: tree(sp),
        objs: vec![],
        protos: vec![],
        ctors: vec![],
        names: HashMap::new(),
        subjects: HashMap::new(),
        described: HashMap::new(),
        bullets: vec![],
        props: vec![],
        stated: vec![],
        omittable: vec![],
        used_ops: BTreeSet::new(),
        percents: percent_names(html),
    };
    let scope: Vec<usize> = (0..sp.clauses.len()).filter(|&c| !b.tree.tmpl[c] && b.in_scope(c)).collect();
    for &c in &scope {
        b.container_pass(c)?;
        match sp.clauses[c].ty.as_deref() {
            Some("built-in function") if b.alias(c).is_some() && !sp.algs.iter().any(|a| a.clause == Some(c)) => b.alias_pass(c)?,
            Some("built-in function") => b.function_pass(c)?,
            None => b.value_pass(c)?,
            _ => {}
        }
    }
    for (o, c, raw) in std::mem::take(&mut b.bullets) {
        b.bullet(o, c, &raw)?;
    }
    for op in ops.iter().filter(|x| x.ty == "built-in function") {
        if !b.used_ops.contains(&op.id) {
            return Err(format!("realm: overlay {}: behaviour-of {} describes no function object", op.id, op.behaviour_of.as_deref().unwrap_or("")));
        }
    }
    for o in 0..b.objs.len() {
        let ctor = b.ctors[o];
        if let Some(f) = b.objs[o].fun.as_mut() {
            f.ctor = ctor;
        }
    }
    let mut props = std::mem::take(&mut b.props);
    props.sort_by_key(|p| sp.clauses[p.3].start);
    let mut globals: Vec<Prop> = Vec::new();
    let mut namespace: Vec<Prop> = Vec::new();
    for (owner, key, v, c) in props {
        let (annex_b, optional) = (b.annex_b(c), b.optional(c));
        let attrs = attrs_after(&own(html, &sp.clauses[c]), "This property has the attributes { ");
        let (f, half) = match v {
            PropVal::Fun(f, half) => (f, half),
            PropVal::Alias(n) => (b.lookup(c, &n)?, None),
            PropVal::Subject(x) => (b.subjects.get(&x).copied().ok_or_else(|| b.err(c, format!("no container describes {x}")))?, None),
            PropVal::Described(k) => (b.described.get(&k).copied().ok_or_else(|| b.err(c, format!("{} describes no object", sp.clauses[k].id)))?, None),
            PropVal::See(name, to) => {
                let o = b.lookup(c, &global_intrinsic(html, &name).ok_or_else(|| b.err(c, format!("no Table 6 row has the Global Name {name}")))?)?;
                let to = if b.tree.tmpl[to] { instance(sp, to, &name).unwrap_or(to) } else { to };
                let defines = dfn_names(&sp.clauses[to].body(html)).iter().any(|n| b.objs[o].names.contains(n));
                if b.described.get(&to) != Some(&o) && !defines {
                    return Err(b.err(c, format!("See {}: not the %{}% of the Global Name {name}", sp.clauses[to].id, b.objs[o].names[0])));
                }
                (o, None)
            }
            PropVal::Value(x) => {
                let p = Prop { key, val: PVal::Data(x), attrs: attrs.unwrap_or(DATA_ATTRS), clause: c, annex_b, optional, omittable: false };
                let e = b.err(c, format!("a second property {:?}", p.key));
                let to = match b.owner(c, &owner)? {
                    Dest::Global => &mut globals,
                    Dest::Namespace => &mut namespace,
                    Dest::Obj(o) => &mut b.objs[o].props,
                };
                if to.iter().any(|q| q.key == p.key) {
                    return Err(e);
                }
                to.push(p);
                continue;
            }
        };
        let props = match b.owner(c, &owner)? {
            Dest::Global => &mut globals,
            Dest::Namespace => &mut namespace,
            Dest::Obj(o) => &mut b.objs[o].props,
        };
        let i = props.iter().position(|p| p.key == key);
        let Some(half) = half else {
            if i.is_some() {
                return Err(format!("realm: {}: a second property {key:?}", sp.clauses[c].id));
            }
            props.push(Prop { key, val: PVal::Data(Val::Obj(f)), attrs: attrs.unwrap_or(DATA_ATTRS), clause: c, annex_b, optional, omittable: false });
            continue;
        };
        let i = i.unwrap_or_else(|| {
            props.push(Prop { key: key.clone(), val: PVal::Accessor { get: None, set: None }, attrs: ACCESSOR_ATTRS, clause: c, annex_b, optional, omittable: false });
            props.len() - 1
        });
        if let Some(a) = attrs {
            props[i].attrs = a;
        }
        let slot = match (&mut props[i].val, half.as_str()) {
            (PVal::Accessor { get, .. }, "get") => Some(get),
            (PVal::Accessor { set, .. }, _) => Some(set),
            _ => None,
        };
        let clash = match slot {
            Some(s) => s.replace(f).is_some(),
            None => true,
        };
        if clash {
            return Err(format!("realm: {}: a second {half} half or a data property {key:?}", sp.clauses[c].id));
        }
    }
    for (owner, key, a, c) in std::mem::take(&mut b.stated) {
        let e = b.err(c, format!("attributes of no property {key:?}"));
        let props = match b.owner(c, &owner)? {
            Dest::Global => &mut globals,
            Dest::Namespace => &mut namespace,
            Dest::Obj(o) => &mut b.objs[o].props,
        };
        props.iter_mut().find(|p| p.key == key).ok_or(e)?.attrs = a;
    }
    for (k, c) in std::mem::take(&mut b.omittable) {
        let e = b.err(c, format!("a host may omit {k}, which is no global property"));
        globals.iter_mut().find(|p| p.key == Key::Str(k.clone())).ok_or(e)?.omittable = true;
    }
    for o in 0..b.objs.len() {
        let c = b.objs[o].clause;
        let p = match b.protos[o].clone() {
            Some(p) => p,
            None => Some(default_proto(b.objs[o].fun.is_some()).to_string()),
        };
        b.objs[o].proto = p.map(|n| b.lookup(c, &n)).transpose()?;
    }
    for id in GLOBAL_TABLES {
        for row in table(html, id).map(|t| t.1).unwrap_or_default() {
            let cell = row.first().map(|x| plain(x)).unwrap_or_default();
            let n = cell.trim_matches('%');
            let o = b.names.get(n).copied().ok_or_else(|| format!("realm: {id}'s {cell} names no object"))?;
            let g = row.get(1).map(|x| plain(x)).unwrap_or_default();
            if let Some(g) = g.strip_prefix("*\"").and_then(|x| x.strip_suffix("\"*")) {
                if !globals.iter().any(|p| p.key == Key::Str(g.to_string()) && p.val == PVal::Data(Val::Obj(o))) {
                    return Err(format!("realm: {id}'s Global Name {g} is no global property whose value is {cell}"));
                }
            }
        }
    }
    let r = order(b.objs, globals, namespace)?;
    match unresolved(html, &r).first() {
        Some(n) => Err(format!("realm: %{n}% names no object")),
        None => Ok(r),
    }
}

/// The intrinsic name of the Table 6 (or B.2 table) row with the Global Name.
fn global_intrinsic(html: &str, name: &str) -> Option<String> {
    GLOBAL_TABLES.iter().filter_map(|id| table(html, id)).flat_map(|t| t.1).find(|r| r.get(1).is_some_and(|g| plain(g) == format!("*\"{name}\"*"))).and_then(|r| r.first().map(|x| plain(x).trim_matches('%').to_string()))
}

/// The objects in creation order: each after its [[Prototype]], else in reading order.
fn order(objs: Vec<Obj>, mut globals: Vec<Prop>, namespace: Vec<Prop>) -> Result<Realm, String> {
    let n = objs.len();
    let mut kids: Vec<Vec<usize>> = vec![vec![]; n];
    let mut ready: BTreeSet<usize> = BTreeSet::new();
    for (o, x) in objs.iter().enumerate() {
        match x.proto {
            Some(p) => kids[p].push(o),
            None => {
                ready.insert(o);
            }
        }
    }
    let mut seq = Vec::new();
    while let Some(o) = ready.pop_first() {
        seq.push(o);
        ready.extend(kids[o].iter().copied());
    }
    if seq.len() != n {
        let stuck: Vec<&str> = (0..n).filter(|o| !seq.contains(o)).map(|o| objs[o].path.as_str()).collect();
        return Err(format!("realm: a [[Prototype]] cycle among {}", stuck.join(", ")));
    }
    let mut at = vec![0; n];
    for (k, &o) in seq.iter().enumerate() {
        at[o] = k;
    }
    let re = |v: &mut Val| {
        if let Val::Obj(x) = v {
            *x = at[*x];
        }
    };
    for p in &mut globals {
        if let PVal::Data(v) = &mut p.val {
            re(v);
        }
    }
    let mut objs: Vec<Option<Obj>> = objs.into_iter().map(Some).collect();
    let mut out = Vec::with_capacity(n);
    for &o in &seq {
        let mut x = objs[o].take().unwrap();
        x.proto = x.proto.map(|p| at[p]);
        for (_, v) in &mut x.slots {
            re(v);
        }
        for p in &mut x.props {
            match &mut p.val {
                PVal::Data(v) => re(v),
                PVal::Accessor { get, set } => {
                    *get = get.map(|g| at[g]);
                    *set = set.map(|s| at[s]);
                }
            }
        }
        out.push(x);
    }
    Ok(Realm { objs: out, globals, namespace })
}
