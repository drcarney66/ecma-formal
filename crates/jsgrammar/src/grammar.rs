//! The grammar notation of ECMA-262 §5.1.6, as spec.html writes it
//! (grammarkdown), parsed into the forms of `lean/Ecma/Grammar/Core.lean`.
//! Any form this parser does not know is an error: it never guesses.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Colons {
    One,
    Two,
    Three,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Arg {
    /// `+`, `~` or `?`.
    pub sign: char,
    pub param: String,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Terminal {
    /// The text, and whether spec.html spells it the other way (`spell`).
    Text(String, bool),
    Cp(String),
}

/// A terminal's text as spec.html spells it between its backticks: `<`, `&`,
/// the backtick and non-ASCII characters by reference, `>` by reference
/// unless `alt`; the lone backtick is ``` ``` ```, or `` `&grave;` `` if `alt`.
pub fn spell(text: &str, alt: bool) -> String {
    if text == "`" {
        return if alt { "`&grave;`" } else { "```" }.into();
    }
    let mut out = String::from("`");
    for c in text.chars() {
        match c {
            '>' if alt => out.push('>'),
            c => out.push_str(&spell_char(c)),
        }
    }
    out.push('`');
    out
}

/// A character as spec.html's grammar text spells it: by its named reference,
/// a non-ASCII or control one without a name by its number (`&#x200C;`), else itself.
pub fn spell_char(c: char) -> String {
    match ENTITIES.iter().find(|(_, d)| d.chars().eq(std::iter::once(c))) {
        Some((e, _)) => e.to_string(),
        None if !c.is_ascii() || c.is_ascii_control() => format!("&#x{:04X};", c as u32),
        None => c.to_string(),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Sym {
    T(Terminal),
    Nt(String, Vec<Arg>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LookItem {
    T(Terminal),
    NoLT,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Lookahead {
    Eq(Vec<LookItem>),
    Ne(Vec<LookItem>),
    Mem(Vec<Vec<LookItem>>),
    NotMem(Vec<Vec<LookItem>>),
    NotMemNT(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Exclusion {
    Sym(Sym),
    OneOf(Vec<Sym>, bool),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Item {
    Sym(Sym, bool),
    Look(Lookahead),
    NoLT,
    Empty,
    ButNot(Sym, Exclusion),
    OnlyIf(&'static str),
    Phrase(&'static str),
}

#[derive(Clone, Debug)]
pub struct Alt {
    /// `[+P, ~Q]`: every one must hold.
    pub guard: Vec<(bool, String)>,
    pub rhs: Vec<Item>,
    pub label: Option<String>,
    /// The alternative as spec.html writes it, character references decoded,
    /// without its label: the name of its production.
    pub text: String,
}

#[derive(Clone, Debug)]
pub enum Body {
    Alts(Vec<Alt>),
    OneOf(Vec<Vec<Terminal>>),
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub lhs: String,
    pub params: Vec<String>,
    pub colons: Colons,
    pub body: Body,
    /// The rule's lines as spec.html has them, less the block's indentation.
    pub raw: Vec<String>,
    /// The 1-based spec.html line of its heading.
    pub line: usize,
    /// Whether a `// emu-format ignore` line precedes it.
    pub fmt_ignore: bool,
}

/// The code point names (§12.2 Table 34, §12.3 Table 35) that `<NAME>` may
/// write: `Grammar.CodePointName`'s constructors.
const CODE_POINTS: &[&str] = &["TAB", "VT", "FF", "ZWNBSP", "USP", "LF", "CR", "LS", "PS"];

/// The descriptive phrases (`> …`) and `[> but only if …]` conditions:
/// their text, and `Grammar.Phrase`'s constructor.
const PHRASES: &[(&str, &str)] = &[
    ("any Unicode code point", "anyCodePoint"),
    (
        "any Unicode code point with the Unicode property \u{201c}ID_Start\u{201d}",
        "idStart",
    ),
    (
        "any Unicode code point with the Unicode property \u{201c}ID_Continue\u{201d}",
        "idContinue",
    ),
    (
        "any Unicode code point in the inclusive interval from U+D800 to U+DBFF",
        "leadSurrogate",
    ),
    (
        "any Unicode code point in the inclusive interval from U+DC00 to U+DFFF",
        "trailSurrogate",
    ),
];
const CONDITIONS: &[(&str, &str)] = &[
    ("the MV of |HexDigits| > 0x10FFFF", "mvAbove10FFFF"),
    ("the MV of |HexDigits| \u{2264} 0x10FFFF", "mvAtMost10FFFF"),
    ("the MV of |Hex4Digits| is in the inclusive interval from 0xD800 to 0xDBFF", "mvLead"),
    ("the MV of |Hex4Digits| is in the inclusive interval from 0xDC00 to 0xDFFF", "mvTrail"),
    ("the MV of |Hex4Digits| is not in the inclusive interval from 0xD800 to 0xDFFF", "mvNonSurrogate"),
    (
        "the CapturingGroupNumber of |DecimalEscape| is \u{2264} CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)",
        "groupNumberAtMostCount",
    ),
];

/// The character references spec.html's grammar text uses.
const ENTITIES: &[(&str, &str)] = &[
    ("&lt;", "<"),
    ("&gt;", ">"),
    ("&amp;", "&"),
    ("&grave;", "`"),
    ("&notin;", "\u{2209}"),
    ("&isin;", "\u{2208}"),
    ("&le;", "\u{2264}"),
    ("&ldquo;", "\u{201c}"),
    ("&rdquo;", "\u{201d}"),
];

/// `s` with its character references decoded; an unknown one is an error.
pub fn decode(s: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find('&') {
        out.push_str(&rest[..i]);
        let t = &rest[i..];
        if let Some(h) = t.strip_prefix("&#x") {
            let n = h.find(';').ok_or_else(|| format!("an unclosed character reference at {t:.20}"))?;
            let c = u32::from_str_radix(&h[..n], 16)
                .ok()
                .and_then(char::from_u32)
                .filter(|c| (!c.is_ascii() || c.is_ascii_control()) && spell_char(*c) == t[..n + 4])
                .ok_or_else(|| format!("a character reference this generator does not know at {t:.20}"))?;
            out.push(c);
            rest = &h[n + 1..];
            continue;
        }
        let (e, d) = ENTITIES
            .iter()
            .find(|(e, _)| t.starts_with(e))
            .ok_or_else(|| format!("an unknown character reference at {t:.20}"))?;
        out.push_str(d);
        rest = &t[e.len()..];
    }
    out.push_str(rest);
    Ok(out)
}

fn is_ident(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

struct Cur<'a> {
    s: &'a str,
    i: usize,
}

impl<'a> Cur<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.i..]
    }
    fn at(&self, p: &str) -> bool {
        self.rest().starts_with(p)
    }
    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.i += p.len();
            true
        } else {
            false
        }
    }
    fn end(&self) -> bool {
        self.i >= self.s.len()
    }
    fn ident(&mut self) -> Option<String> {
        let n = self.rest().find(|c: char| !is_ident(c)).unwrap_or(self.rest().len());
        if n == 0 {
            return None;
        }
        let id = self.rest()[..n].to_string();
        self.i += n;
        Some(id)
    }
    fn err<T>(&self, what: &str) -> Result<T, String> {
        Err(format!("{what} at `{}` in `{}`", self.rest(), self.s))
    }
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) {
            Ok(())
        } else {
            self.err(&format!("expected `{p}`"))
        }
    }

    /// A terminal: `` `text` `` (``` ``` ``` is the backtick), or `<NAME>`.
    fn terminal(&mut self) -> Result<Option<Terminal>, String> {
        if self.eat("```") {
            return Ok(Some(Terminal::Text("`".into(), false)));
        }
        if self.eat("`") {
            let n = self
                .rest()
                .find('`')
                .ok_or_else(|| format!("an unclosed terminal in `{}`", self.s))?;
            let raw = &self.rest()[..n];
            if raw.is_empty() {
                return self.err("an empty terminal");
            }
            let text = decode(raw)?;
            let alt = if text == "`" { raw == "&grave;" } else { raw.contains('>') };
            if spell(&text, alt) != format!("`{raw}`") {
                return self.err(&format!("a spelling of `{text}` this generator does not know"));
            }
            self.i += n + 1;
            return Ok(Some(Terminal::Text(text, alt)));
        }
        if self.eat("&lt;") {
            let n = self
                .rest()
                .find("&gt;")
                .ok_or_else(|| format!("an unclosed code point name in `{}`", self.s))?;
            let name = self.rest()[..n].to_string();
            if !CODE_POINTS.contains(&name.as_str()) {
                return self.err(&format!("an unknown code point name <{name}>"));
            }
            self.i += n + "&gt;".len();
            return Ok(Some(Terminal::Cp(name)));
        }
        Ok(None)
    }

    /// `Name[args]` or a terminal.
    fn sym(&mut self) -> Result<Option<Sym>, String> {
        if let Some(t) = self.terminal()? {
            return Ok(Some(Sym::T(t)));
        }
        if !self.rest().starts_with(|c: char| c.is_ascii_alphabetic()) {
            return Ok(None);
        }
        let name = self.ident().unwrap();
        let mut args = Vec::new();
        if self.eat("[") {
            loop {
                let sign = match self.rest().chars().next() {
                    Some(c @ ('+' | '~' | '?')) => c,
                    _ => return self.err("expected an argument `+P`, `~P` or `?P`"),
                };
                self.i += 1;
                let param = self
                    .ident()
                    .ok_or_else(|| format!("expected a parameter in `{}`", self.s))?;
                args.push(Arg { sign, param });
                if self.eat("]") {
                    break;
                }
                self.expect(", ")?;
            }
        }
        Ok(Some(Sym::Nt(name, args)))
    }

    /// A lookahead token sequence: terminals and `[no LineTerminator here]`.
    fn look_seq(&mut self) -> Result<Vec<LookItem>, String> {
        let mut seq = Vec::new();
        loop {
            if self.eat("[no LineTerminator here]") {
                seq.push(LookItem::NoLT);
            } else if let Some(t) = self.terminal()? {
                seq.push(LookItem::T(t));
            } else {
                break;
            }
            if !(self.at(" `") || self.at(" [no LineTerminator here]") || self.at(" &lt;")) {
                break;
            }
            self.i += 1;
        }
        if seq.is_empty() {
            return self.err("an empty lookahead sequence");
        }
        Ok(seq)
    }

    /// `{ seq, seq, … }`.
    fn look_set(&mut self) -> Result<Vec<Vec<LookItem>>, String> {
        self.expect("{ ")?;
        let mut set = vec![self.look_seq()?];
        while self.eat(", ") {
            set.push(self.look_seq()?);
        }
        self.expect(" }")?;
        Ok(set)
    }

    /// After `[lookahead `: the restriction, through its `]`.
    fn lookahead(&mut self) -> Result<Lookahead, String> {
        let l = if self.eat("== ") {
            Lookahead::Eq(self.look_seq()?)
        } else if self.eat("!= ") {
            Lookahead::Ne(self.look_seq()?)
        } else if self.eat("&isin; ") {
            Lookahead::Mem(self.look_set()?)
        } else if self.eat("&notin; ") {
            if self.at("{") {
                Lookahead::NotMem(self.look_set()?)
            } else {
                Lookahead::NotMemNT(
                    self.ident()
                        .ok_or_else(|| format!("expected a nonterminal in `{}`", self.s))?,
                )
            }
        } else {
            return self.err("a lookahead form this generator does not know");
        };
        self.expect("]")?;
        Ok(l)
    }

    /// After `but not `: the exclusion, through the end of the line.
    fn exclusion(&mut self) -> Result<Exclusion, String> {
        if self.eat("one of ") {
            let mut syms = vec![self
                .sym()?
                .ok_or_else(|| format!("expected a symbol after `one of` in `{}`", self.s))?];
            let mut or_sep = None;
            while !self.end() {
                let o = if self.eat(" or ") {
                    true
                } else if self.eat(" ") {
                    false
                } else {
                    return self.err("expected `or` or a space between excluded symbols");
                };
                if or_sep.is_some_and(|x| x != o) {
                    return self.err("both `or` and spaces between excluded symbols");
                }
                or_sep = Some(o);
                syms.push(
                    self.sym()?
                        .ok_or_else(|| format!("expected an excluded symbol in `{}`", self.s))?,
                );
            }
            Ok(Exclusion::OneOf(syms, or_sep.unwrap_or(true)))
        } else {
            let s = self
                .sym()?
                .ok_or_else(|| format!("expected an excluded symbol in `{}`", self.s))?;
            Ok(Exclusion::Sym(s))
        }
    }
}

fn find_phrase(table: &[(&str, &'static str)], text: &str) -> Result<&'static str, String> {
    table
        .iter()
        .find(|(t, _)| *t == text)
        .map(|(_, c)| *c)
        .ok_or_else(|| format!("a phrase this generator does not know: `{text}`"))
}

/// One alternative (a right-hand side line, without its indentation).
pub fn parse_alt(line: &str) -> Result<Alt, String> {
    let mut c = Cur { s: line, i: 0 };
    let mut label = None;
    let text_end;
    if let Some(k) = line.rfind(" #") {
        let l = &line[k + 2..];
        if !l.is_empty() && l.chars().all(is_ident) {
            label = Some(l.to_string());
            text_end = k;
        } else {
            text_end = line.len();
        }
    } else {
        text_end = line.len();
    }
    let body = &line[..text_end];
    let text = decode(body)?;
    c.s = body;
    if c.eat("&gt; ") {
        let p = find_phrase(PHRASES, &decode(c.rest())?)?;
        return Ok(Alt {
            guard: Vec::new(),
            rhs: vec![Item::Phrase(p)],
            label,
            text,
        });
    }
    let mut guard = Vec::new();
    if c.at("[+") || c.at("[~") {
        c.i += 1;
        loop {
            let plus = c.eat("+");
            if !plus && !c.eat("~") {
                return c.err("expected `+P` or `~P` in a guard");
            }
            let p = c
                .ident()
                .ok_or_else(|| format!("expected a parameter in a guard in `{line}`"))?;
            guard.push((plus, p));
            if c.eat("] ") {
                break;
            }
            c.expect(", ")?;
        }
    }
    let mut rhs = Vec::new();
    loop {
        if c.end() {
            break;
        }
        if !rhs.is_empty() {
            c.expect(" ")?;
        }
        if c.eat("[empty]") {
            rhs.push(Item::Empty);
        } else if c.eat("[no LineTerminator here]") {
            rhs.push(Item::NoLT);
        } else if c.eat("[lookahead ") {
            rhs.push(Item::Look(c.lookahead()?));
        } else if c.eat("[> but only if ") || c.eat("[&gt; but only if ") {
            let n = c
                .rest()
                .find(']')
                .ok_or_else(|| format!("an unclosed condition in `{line}`"))?;
            let cond = find_phrase(CONDITIONS, &decode(&c.rest()[..n])?)?;
            c.i += n + 1;
            rhs.push(Item::OnlyIf(cond));
        } else if let Some(s) = c.sym()? {
            if c.eat(" but not ") {
                rhs.push(Item::ButNot(s, c.exclusion()?));
            } else {
                let opt = c.eat("?");
                rhs.push(Item::Sym(s, opt));
            }
        } else {
            return c.err("a form this generator does not know");
        }
    }
    if rhs.is_empty() {
        return c.err("an empty right-hand side");
    }
    Ok(Alt {
        guard,
        rhs,
        label,
        text,
    })
}

/// A rule's heading: `Name[Params] :` (or `::`, `:::`), maybe `one of`.
fn parse_heading(line: &str) -> Result<(String, Vec<String>, Colons, bool), String> {
    let mut c = Cur { s: line, i: 0 };
    let name = c
        .ident()
        .ok_or_else(|| format!("expected a nonterminal heading `{line}`"))?;
    let mut params = Vec::new();
    if c.eat("[") {
        loop {
            params.push(c.ident().ok_or_else(|| format!("expected a parameter in `{line}`"))?);
            if c.eat("]") {
                break;
            }
            c.expect(", ")?;
        }
    }
    let colons = if c.eat(" :::") {
        Colons::Three
    } else if c.eat(" ::") {
        Colons::Two
    } else if c.eat(" :") {
        Colons::One
    } else {
        return c.err("expected `:`, `::` or `:::`");
    };
    let one_of = c.eat(" one of");
    if !c.end() {
        return c.err("unexpected text after a heading");
    }
    Ok((name, params, colons, one_of))
}

/// The rules of a definition block whose text starts on spec.html line
/// `first_line` (the line of its opening tag).
pub fn parse_block(text: &str, first_line: usize) -> Result<Vec<Rule>, String> {
    let lines: Vec<&str> = text.split('\n').collect();
    let indent = |l: &str| l.len() - l.trim_start().len();
    // `// emu-format ignore`: an instruction to spec.html's formatter, not grammar.
    let skip = |l: &str| l.trim().is_empty() || l.trim_start().starts_with("// ");
    let base = lines
        .iter()
        .filter(|l| !skip(l))
        .map(|l| indent(l))
        .min()
        .ok_or("an empty block")?;
    let mut rules: Vec<Rule> = Vec::new();
    let mut fmt_ignore = false;
    for (k, l) in lines.iter().enumerate() {
        let line = first_line + k;
        if l.trim_start().starts_with("// ") {
            if l.trim() != "// emu-format ignore" {
                return Err(format!(
                    "spec.html:{line}: a comment this generator does not know: {}",
                    l.trim()
                ));
            }
            fmt_ignore = true;
            continue;
        }
        if l.trim().is_empty() {
            continue;
        }
        if l.ends_with(' ') || l.ends_with('\t') {
            return Err(format!("spec.html:{line}: trailing white space"));
        }
        let ind = indent(l);
        let t = l.trim_start();
        let at = |e: String| format!("spec.html:{line}: {e}");
        if ind == base {
            let (lhs, params, colons, one_of) = parse_heading(t).map_err(at)?;
            let body = if one_of {
                Body::OneOf(Vec::new())
            } else {
                Body::Alts(Vec::new())
            };
            rules.push(Rule {
                lhs,
                params,
                colons,
                body,
                raw: vec![l[base..].to_string()],
                line,
                fmt_ignore,
            });
            fmt_ignore = false;
            continue;
        }
        if fmt_ignore {
            return Err(at("a formatter comment before an alternative".into()));
        }
        let r = rules
            .last_mut()
            .ok_or_else(|| at("an alternative before any heading".into()))?;
        if ind != base + 2 {
            return Err(at(format!(
                "an alternative indented {} past its heading, not 2",
                ind - base
            )));
        }
        r.raw.push(l[base..].to_string());
        match &mut r.body {
            Body::Alts(alts) => alts.push(parse_alt(t).map_err(at)?),
            Body::OneOf(rows) => {
                let mut c = Cur { s: t, i: 0 };
                let mut row = Vec::new();
                loop {
                    row.push(
                        c.terminal()
                            .map_err(at)?
                            .ok_or_else(|| at(format!("expected a terminal in `{t}`")))?,
                    );
                    if c.end() {
                        break;
                    }
                    c.expect(" ").map_err(at)?;
                }
                rows.push(row);
            }
        }
    }
    for r in &rules {
        let empty = match &r.body {
            Body::Alts(a) => a.is_empty(),
            Body::OneOf(rows) => rows.is_empty(),
        };
        if empty {
            return Err(format!("spec.html:{}: {} has no alternatives", r.line, r.lhs));
        }
    }
    Ok(rules)
}

/// The block's indentation, if `text` is its rules laid out as spec.html
/// lays out a definition block: a newline, each rule's lines (after its
/// formatter comment, if any) at that indentation, a blank line between rules,
/// and the closing tag's indentation, two less.
pub fn layout(text: &str, rules: &[Rule]) -> Option<usize> {
    let indent = text.split('\n').filter(|l| !l.trim().is_empty()).map(|l| l.len() - l.trim_start().len()).min()?;
    let ind = " ".repeat(indent);
    let mut out = String::from("\n");
    for (k, r) in rules.iter().enumerate() {
        if k > 0 {
            out.push('\n');
        }
        if r.fmt_ignore {
            out.push_str(&format!("{ind}// emu-format ignore\n"));
        }
        for l in &r.raw {
            out.push_str(&format!("{ind}{l}\n"));
        }
    }
    out.push_str(&" ".repeat(indent.checked_sub(2)?));
    (out == text).then_some(indent)
}

/// The production text of a `one of` terminal (its name), as an alternative.
pub fn terminal_text(t: &Terminal) -> String {
    match t {
        Terminal::Text(s, _) if s == "`" => "```".to_string(),
        Terminal::Text(s, _) => format!("`{}`", s.chars().map(|c| if c.is_ascii_control() { spell_char(c) } else { c.to_string() }).collect::<String>()),
        Terminal::Cp(n) => format!("<{n}>"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(s: &str) -> Sym {
        Sym::T(Terminal::Text(s.into(), false))
    }

    #[test]
    fn lookahead_with_a_nested_no_line_terminator() {
        let a = parse_alt("[lookahead &notin; { `{`, `async` [no LineTerminator here] `function`, `let` `[` }] Expression[+In, ?Yield] `;`").unwrap();
        let tt = |s: &str| LookItem::T(Terminal::Text(s.into(), false));
        assert_eq!(
            a.rhs[0],
            Item::Look(Lookahead::NotMem(vec![
                vec![tt("{")],
                vec![tt("async"), LookItem::NoLT, tt("function")],
                vec![tt("let"), tt("[")]
            ]))
        );
        assert_eq!(
            a.rhs[1],
            Item::Sym(
                Sym::Nt(
                    "Expression".into(),
                    vec![
                        Arg {
                            sign: '+',
                            param: "In".into()
                        },
                        Arg {
                            sign: '?',
                            param: "Yield".into()
                        }
                    ]
                ),
                false
            )
        );
        assert_eq!(a.rhs[2], Item::Sym(t(";"), false));
    }

    #[test]
    fn backticks_guards_labels_and_exclusions() {
        let a = parse_alt("``` TemplateCharacters? `${`").unwrap();
        assert_eq!(a.rhs[0], Item::Sym(t("`"), false));
        assert_eq!(a.rhs[1], Item::Sym(Sym::Nt("TemplateCharacters".into(), vec![]), true));
        let a = parse_alt("[+Using, +Await] `await` ForBinding #x").unwrap();
        assert_eq!(a.guard, vec![(true, "Using".into()), (true, "Await".into())]);
        assert_eq!(a.label.as_deref(), Some("x"));
        assert_eq!(a.text, "[+Using, +Await] `await` ForBinding");
        let a = parse_alt("SourceCharacter but not one of `^` `$` `&grave;&grave;`").unwrap();
        assert_eq!(
            a.rhs[0],
            Item::ButNot(
                Sym::Nt("SourceCharacter".into(), vec![]),
                Exclusion::OneOf(vec![t("^"), t("$"), t("``")], false)
            )
        );
        let a = parse_alt("HexDigits[~Sep] [> but only if the MV of |HexDigits| &le; 0x10FFFF]").unwrap();
        assert_eq!(a.rhs[1], Item::OnlyIf("mvAtMost10FFFF"));
    }

    #[test]
    fn spellings() {
        assert_eq!(parse_alt("`=>`").unwrap().rhs[0], Item::Sym(Sym::T(Terminal::Text("=>".into(), true)), false));
        assert_eq!(parse_alt("`=&gt;`").unwrap().rhs[0], Item::Sym(t("=>"), false));
        assert_eq!(parse_alt("`&grave;`").unwrap().rhs[0], Item::Sym(Sym::T(Terminal::Text("`".into(), true)), false));
        assert_eq!(spell("&&", false), "`&amp;&amp;`");
        assert_eq!(spell("``", false), "`&grave;&grave;`");
        assert_eq!(parse_alt("`&#x200C;`").unwrap().rhs[0], Item::Sym(t("\u{200C}"), false));
        assert!(parse_alt("`&#x41;`").is_err());
        // `<` has one spelling.
        assert!(parse_alt("`<`").is_err());
    }

    #[test]
    fn unknown_forms_fail() {
        assert!(parse_alt("X [lookahead &lt; `a`]").is_err());
        assert!(parse_alt("&gt; any code point at all").is_err());
        assert!(parse_alt("&lt;NBSP&gt;").is_err());
        assert!(parse_alt("X &foo; Y").is_err());
        assert!(parse_block("\n  A :\n     B\n", 1).is_err());
    }
}
