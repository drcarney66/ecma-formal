//! The token layer of a step: ecmarkup's inline markup, then words and
//! punctuation. Each token prints from its kind and value alone (`canon`).

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum K {
    Xref,
    Gram,
    /// an `emu-alg` element
    Alg,
    MetaO,
    MetaC,
    NotRefO,
    NotRefC,
    SupO,
    SupC,
    SubO,
    SubC,
    Link,
    Tag,
    Code,
    Val,
    Var,
    Enum,
    Nt,
    Intr,
    Field,
    /// a grammar parameter, `<sub>[Yield]</sub>`
    Param,
    Num,
    Poss,
    Word,
    Punct,
}

#[derive(Clone, Debug)]
pub struct Tok {
    pub k: K,
    /// The value: the text inside the markup, or the character an entity names.
    pub v: String,
    /// The source text (with a value's subscript).
    pub raw: String,
    /// `𝔽` or `ℤ` from a `<sub>` after a value or number.
    pub sub: Option<char>,
    /// Byte offsets in the step text.
    pub s: usize,
    pub e: usize,
}

fn is_w(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn at(t: &str, i: usize) -> Option<char> {
    t[i..].chars().next()
}

/// End of `<name ...>...</name>` (lazy) from `i`, where `t[i..]` starts with `<name`.
fn element(t: &str, i: usize, name: &str) -> Option<usize> {
    let open = format!("<{name}");
    if !t[i..].starts_with(&open) {
        return None;
    }
    let after = i + open.len();
    if at(t, after).is_some_and(is_w) {
        return None;
    }
    let gt = t[after..].find('>')? + after + 1;
    let close = format!("</{name}>");
    Some(t[gt..].find(&close)? + gt + close.len())
}

/// End of `<name ...>` from `i`.
fn open_tag(t: &str, i: usize, name: &str) -> Option<usize> {
    let open = format!("<{name}");
    if !t[i..].starts_with(&open) {
        return None;
    }
    let after = i + open.len();
    if at(t, after).is_some_and(is_w) {
        return None;
    }
    Some(t[after..].find('>')? + after + 1)
}

fn lit(t: &str, i: usize, s: &str) -> Option<usize> {
    t[i..].starts_with(s).then(|| i + s.len())
}

/// `c` then chars satisfying `rest`, as long as possible.
fn run(t: &str, i: usize, rest: impl Fn(char) -> bool) -> usize {
    let mut j = i;
    while let Some(c) = at(t, j) {
        if !rest(c) {
            break;
        }
        j += c.len_utf8();
    }
    j
}

fn delimited(t: &str, i: usize, d: char, first: impl Fn(char) -> bool, rest: impl Fn(char) -> bool) -> Option<usize> {
    if at(t, i)? != d {
        return None;
    }
    let c = at(t, i + 1)?;
    if !first(c) {
        return None;
    }
    let j = run(t, i + 1 + c.len_utf8(), rest);
    (at(t, j)? == d).then(|| j + 1)
}

fn code(t: &str, i: usize) -> Option<usize> {
    if at(t, i)? != '`' {
        return None;
    }
    let j = t[i + 1..].find('`')? + i + 1;
    (j > i + 1).then(|| j + 1)
}

fn val(t: &str, i: usize) -> Option<usize> {
    if at(t, i)? != '*' {
        return None;
    }
    let b = t.as_bytes();
    let mut j = i + 1;
    let mut n = 0;
    while j < b.len() {
        match b[j] {
            b'*' => return (n > 0).then(|| j + 1),
            b'\\' => {
                let c = at(t, j + 1)?;
                j += 1 + c.len_utf8();
            }
            _ => j += at(t, j)?.len_utf8(),
        }
        n += 1;
    }
    None
}

fn nt(t: &str, i: usize) -> Option<usize> {
    if at(t, i)? != '|' || !at(t, i + 1)?.is_ascii_alphabetic() {
        return None;
    }
    let mut j = run(t, i + 2, is_w);
    if at(t, j) == Some('[') {
        let k = run(t, j + 1, |c| c != ']' && c != '|');
        if at(t, k) == Some(']') {
            j = k + 1;
        }
    }
    if let Some(k) = lit(t, j, "_opt") {
        j = k;
    }
    (at(t, j)? == '|').then(|| j + 1)
}

fn num(t: &str, i: usize) -> Option<usize> {
    if t[i..].starts_with("U+") {
        let j = run(t, i + 2, |c| c.is_ascii_digit() || ('A'..='F').contains(&c));
        let n = j - (i + 2);
        if n >= 4 {
            return Some(i + 2 + n.min(6));
        }
    }
    if t[i..].starts_with("0x") {
        let j = run(t, i + 2, |c| c.is_ascii_hexdigit());
        if j > i + 2 {
            return Some(j);
        }
    }
    if at(t, i)?.is_ascii_digit() {
        let j = run(t, i, |c| c.is_ascii_digit());
        if at(t, j) == Some('.') && at(t, j + 1).is_some_and(|c| c.is_ascii_digit()) {
            return Some(run(t, j + 1, |c| c.is_ascii_digit()));
        }
        return Some(j);
    }
    None
}

fn entity(t: &str, i: usize) -> Option<usize> {
    if at(t, i)? != '&' {
        return None;
    }
    if at(t, i + 1)? == '#' {
        let j = run(t, i + 2, |c| c.is_ascii_digit());
        return (j > i + 2 && at(t, j)? == ';').then(|| j + 1);
    }
    let j = run(t, i + 1, |c| c.is_ascii_lowercase());
    (j > i + 1 && at(t, j)? == ';').then(|| j + 1)
}

fn word(t: &str, i: usize) -> Option<usize> {
    if !at(t, i)?.is_ascii_alphabetic() {
        return None;
    }
    let mut j = run(t, i + 1, |c| c.is_ascii_alphanumeric());
    if at(t, j) == Some('/') && at(t, j + 1).is_some_and(|c| c.is_ascii_uppercase()) {
        j = run(t, j + 2, |c| c.is_ascii_alphanumeric());
    }
    if t[j..].starts_with("::") && at(t, j + 2).is_some_and(|c| c.is_ascii_alphabetic()) {
        j = run(t, j + 3, is_w);
    }
    while at(t, j) == Some('-') && at(t, j + 1).is_some_and(|c| c.is_ascii_alphanumeric()) {
        j = run(t, j + 1, |c| c.is_ascii_alphanumeric());
    }
    Some(j)
}

/// `<sub>[Name]</sub>` at `i`: a grammar parameter.
fn param(t: &str, i: usize) -> Option<usize> {
    let j = lit(t, i, "<sub>[")?;
    let k = run(t, j, |c| c.is_ascii_alphabetic());
    if k == j {
        return None;
    }
    lit(t, k, "]</sub>")
}

/// The character an entity names, if it is one a step writes.
fn unescape(e: &str) -> Option<String> {
    let c = match e {
        "&lt;" => '<',
        "&gt;" => '>',
        "&amp;" => '&',
        "&quot;" => '"',
        "&nbsp;" => '\u{a0}',
        _ => {
            let n: u32 = e.strip_prefix("&#")?.strip_suffix(';')?.parse().ok()?;
            char::from_u32(n)?
        }
    };
    Some(c.to_string())
}

/// The kind and end of the token at `i` (first alternative that matches).
fn next(t: &str, i: usize) -> (K, usize) {
    let c = at(t, i).unwrap();
    if c == '<' {
        if let Some(e) = element(t, i, "emu-xref") {
            return (K::Xref, e);
        }
        if let Some(e) = element(t, i, "emu-grammar") {
            return (K::Gram, e);
        }
        if let Some(e) = element(t, i, "emu-alg") {
            return (K::Alg, e);
        }
        if let Some(e) = param(t, i) {
            return (K::Param, e);
        }
        if let Some(e) = open_tag(t, i, "emu-meta") {
            return (K::MetaO, e);
        }
        for (s, k) in [
            ("</emu-meta>", K::MetaC),
            ("<emu-not-ref>", K::NotRefO),
            ("</emu-not-ref>", K::NotRefC),
            ("<sup>", K::SupO),
            ("</sup>", K::SupC),
            ("<sub>", K::SubO),
            ("</sub>", K::SubC),
        ] {
            if let Some(e) = lit(t, i, s) {
                return (k, e);
            }
        }
        if let Some(e) = element(t, i, "a") {
            return (K::Link, e);
        }
        let j = i + 1 + usize::from(at(t, i + 1) == Some('/'));
        if at(t, j).is_some_and(|c| c.is_ascii_lowercase()) {
            if let Some(g) = t[j..].find('>') {
                return (K::Tag, j + g + 1);
            }
        }
    }
    if let Some(e) = code(t, i) {
        return (K::Code, e);
    }
    if let Some(e) = val(t, i) {
        return (K::Val, e);
    }
    if let Some(e) = delimited(t, i, '_', |c| c.is_ascii_alphabetic(), |c| c.is_ascii_alphanumeric()) {
        return (K::Var, e);
    }
    if let Some(e) = delimited(t, i, '~', |c| c.is_ascii_alphanumeric(), |c| is_w(c) || c == '+' || c == '-') {
        return (K::Enum, e);
    }
    if let Some(e) = nt(t, i) {
        return (K::Nt, e);
    }
    if let Some(e) = delimited(t, i, '%', |c| c.is_ascii_alphabetic(), |c| is_w(c) || c == '.') {
        return (K::Intr, e);
    }
    if t[i..].starts_with("[[") && at(t, i + 2).is_some_and(|c| c.is_ascii_alphabetic() || c == '%') {
        let j = run(t, i + 3, |c| is_w(c) || c == '.' || c == '%');
        if t[j..].starts_with("]]") {
            return (K::Field, j + 2);
        }
    }
    if let Some(e) = num(t, i) {
        return (K::Num, e);
    }
    if let Some(e) = entity(t, i) {
        return (K::Punct, e);
    }
    if t[i..].starts_with("'s") && !at(t, i + 2).is_some_and(is_w) {
        return (K::Poss, i + 2);
    }
    if let Some(e) = word(t, i) {
        return (K::Word, e);
    }
    (K::Punct, i + c.len_utf8())
}

/// `<sub>𝔽</sub>` or `<sub>ℤ</sub>` at `i`.
fn subscript(t: &str, i: usize) -> Option<(char, usize)> {
    for c in ['𝔽', 'ℤ'] {
        let s = format!("<sub>{c}</sub>");
        if t[i..].starts_with(&s) {
            return Some((c, i + s.len()));
        }
    }
    None
}

fn attr(tag: &str, name: &str) -> Option<String> {
    let key = format!("{name}=\"");
    let i = tag.find(&key)? + key.len();
    let j = tag[i..].find('"')? + i;
    Some(tag[i..j].to_string())
}

/// The tokens of a step's text; whitespace is dropped (the printer restores it).
pub fn tokenize(t: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < t.len() {
        let c = at(t, i).unwrap();
        if c.is_whitespace() {
            i += c.len_utf8();
            continue;
        }
        let (mut k, mut e) = next(t, i);
        let raw = &t[i..e];
        let mut sub = None;
        let v = match k {
            K::Var | K::Enum | K::Nt | K::Intr | K::Code => raw[1..raw.len() - 1].to_string(),
            K::Field => raw[2..raw.len() - 2].to_string(),
            K::Param => raw["<sub>[".len()..raw.len() - "]</sub>".len()].to_string(),
            K::Val | K::Num => {
                let v = if k == K::Val { raw[1..raw.len() - 1].to_string() } else { raw.to_string() };
                if let Some((c, e2)) = subscript(t, e) {
                    sub = Some(c);
                    e = e2;
                }
                v
            }
            K::Xref => attr(raw, "href").map(|h| h.trim_start_matches('#').to_string()).unwrap_or_else(|| raw.to_string()),
            K::Punct if raw.len() > 1 && raw.starts_with('&') => match unescape(raw) {
                Some(v) => v,
                None => {
                    k = K::Tag;
                    raw.to_string()
                }
            },
            _ => raw.to_string(),
        };
        out.push(Tok { k, v, raw: t[i..e].to_string(), sub, s: i, e });
        i = e;
    }
    out
}

/// The printed form of a token from its kind and value.
pub fn canon(t: &Tok) -> String {
    let sub = |s: String| match t.sub {
        Some(c) => format!("{s}<sub>{c}</sub>"),
        None => s,
    };
    match t.k {
        K::Var => format!("_{}_", t.v),
        K::Val => sub(format!("*{}*", t.v)),
        K::Num => sub(t.v.clone()),
        K::Enum => format!("~{}~", t.v),
        K::Nt => format!("|{}|", t.v),
        K::Intr => format!("%{}%", t.v),
        K::Field => format!("[[{}]]", t.v),
        K::Param => format!("<sub>[{}]</sub>", t.v),
        K::Code => format!("`{}`", t.v),
        K::Punct => lit_canon(&t.v).to_string(),
        K::Word | K::Poss => t.v.clone(),
        _ => t.raw.clone(),
    }
}

/// A literal's printed form: `<` and `&` as entities.
pub fn lit_canon(v: &str) -> &str {
    match v {
        "<" => "&lt;",
        "&" => "&amp;",
        _ => v,
    }
}

const NOSP_BEFORE: &[&str] = &[",", ".", ":", ";", ")", "]", "'s", "</sup>", "</sub>", "</emu-meta>", "</emu-not-ref>"];
const NOSP_AFTER: &[&str] = &["(", "[", "<sup>", "<sub>", "<emu-not-ref>"];

/// A printed part: text with its glue (no space before it), or a verbatim
/// span of the source tokens.
pub enum Part {
    Text(String, bool),
    Span(usize, usize, bool),
    /// verbatim text (prose), as a span is printed
    Raw(String, bool),
}

/// The parts joined by the canonical spacing rules.
pub fn join(parts: &[Part], toks: &[Tok], text: &str) -> String {
    let mut s = String::new();
    let mut prev = String::new();
    for p in parts {
        match p {
            Part::Span(i, j, glue) => {
                let seg = &text[toks[*i].s..toks[*j - 1].e];
                if !s.is_empty() && !glue && !NOSP_AFTER.contains(&prev.as_str()) && !prev.starts_with("<emu-meta") {
                    s.push(' ');
                }
                s.push_str(seg);
                prev = toks[*j - 1].raw.clone();
            }
            Part::Raw(seg, glue) => {
                if !s.is_empty() && !glue && !NOSP_AFTER.contains(&prev.as_str()) && !prev.starts_with("<emu-meta") {
                    s.push(' ');
                }
                s.push_str(seg);
                prev = seg.clone();
            }
            Part::Text(t, glue) => {
                if !s.is_empty()
                    && !glue
                    && !NOSP_BEFORE.contains(&t.as_str())
                    && !NOSP_AFTER.contains(&prev.as_str())
                    && !prev.starts_with("<emu-meta")
                    && !(t.starts_with("<sub>") && !t.starts_with("<sub>["))
                {
                    s.push(' ');
                }
                s.push_str(t);
                prev = t.clone();
            }
        }
    }
    s
}
