//! Bidirectional bijection between `spec.html` `<emu-grammar type="definition">` blocks
//! and `spec/spectec/01..07-grammar-*.spectec`.

use crate::html_scan::{HtmlBlock, HtmlSpec};
use crate::meta::{BlockLayout, GrammarMeta, ItemKey, RuleOverride};
use spectec::ast::{
    Alt, BlockDef, Colons, Exclusion, GrammarId, GrammarItem, GrammarSym, LookItem, Lookahead,
    NtArg, ParamArg, ParamSign, Rule, RuleBody, Spec, Terminal, TopItem,
};
use spectec::parse::parse_str;
use spectec::print::print_rule;
use std::collections::{BTreeMap, BTreeSet};

const CODE_POINTS: &[&str] = &["TAB", "VT", "FF", "ZWNBSP", "USP", "LF", "CR", "LS", "PS"];

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
    (
        "the MV of |Hex4Digits| is in the inclusive interval from 0xD800 to 0xDBFF",
        "mvLead",
    ),
    (
        "the MV of |Hex4Digits| is in the inclusive interval from 0xDC00 to 0xDFFF",
        "mvTrail",
    ),
    (
        "the MV of |Hex4Digits| is not in the inclusive interval from 0xD800 to 0xDFFF",
        "mvNonSurrogate",
    ),
    (
        "the CapturingGroupNumber of |DecimalEscape| is \u{2264} CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)",
        "groupNumberAtMostCount",
    ),
];

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

pub fn spell_char(c: char) -> String {
    match ENTITIES.iter().find(|(_, d)| d.chars().eq(std::iter::once(c))) {
        Some((e, _)) => (*e).to_string(),
        None if !c.is_ascii() || c.is_ascii_control() => format!("&#x{:04X};", c as u32),
        None => c.to_string(),
    }
}

pub fn spell_chars(keep_gt: bool, s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        if keep_gt && c == '>' {
            out.push('>');
        } else {
            out.push_str(&spell_char(c));
        }
    }
    out
}

pub fn render_terminal(t: &Terminal) -> String {
    match t {
        Terminal::Text { text, alt } => {
            if text == "`" {
                if *alt { "`&grave;`".into() } else { "```".into() }
            } else {
                format!("`{}`", spell_chars(*alt, text))
            }
        }
        Terminal::Cp(name) => format!("&lt;{name}&gt;"),
    }
}

fn sign_str(s: ParamSign) -> &'static str {
    match s {
        ParamSign::Plus => "+",
        ParamSign::Tilde => "~",
        ParamSign::Quest => "?",
    }
}

fn render_sym(s: &GrammarSym) -> String {
    match s {
        GrammarSym::T(t) => render_terminal(t),
        GrammarSym::Nt(n, args) => {
            if args.is_empty() {
                n.clone()
            } else {
                let xs: Vec<_> = args
                    .iter()
                    .map(|a| format!("{}{}", sign_str(a.sign), a.param))
                    .collect();
                format!("{n}[{}]", xs.join(", "))
            }
        }
    }
}

fn render_look_item(i: &LookItem) -> String {
    match i {
        LookItem::T(t) => render_terminal(t),
        LookItem::NoLT => "[no LineTerminator here]".into(),
    }
}

fn render_look_seq(xs: &[LookItem]) -> String {
    xs.iter().map(render_look_item).collect::<Vec<_>>().join(" ")
}

fn render_look_set(ss: &[Vec<LookItem>]) -> String {
    let inner: Vec<_> = ss.iter().map(|s| render_look_seq(s)).collect();
    format!("{{ {} }}", inner.join(", "))
}

fn render_lookahead(l: &Lookahead) -> String {
    match l {
        Lookahead::Eq(s) => format!("[lookahead == {}]", render_look_seq(s)),
        Lookahead::Ne(s) => format!("[lookahead != {}]", render_look_seq(s)),
        Lookahead::Mem(ss) => format!("[lookahead &isin; {}]", render_look_set(ss)),
        Lookahead::NotMem(ss) => format!("[lookahead &notin; {}]", render_look_set(ss)),
        Lookahead::NotMemNt(n) => format!("[lookahead &notin; {n}]"),
    }
}

fn phrase_text(key: &str) -> Result<&'static str, String> {
    PHRASES
        .iter()
        .chain(CONDITIONS.iter())
        .find(|(_, k)| *k == key)
        .map(|(t, _)| *t)
        .ok_or_else(|| format!("unknown grammar phrase key `{key}`"))
}

fn render_item(i: &GrammarItem) -> Result<String, String> {
    Ok(match i {
        GrammarItem::Sym(s, opt) => format!("{}{}", render_sym(s), if *opt { "?" } else { "" }),
        GrammarItem::Lookahead(l) => render_lookahead(l),
        GrammarItem::NoLT => "[no LineTerminator here]".into(),
        GrammarItem::Empty => "[empty]".into(),
        GrammarItem::ButNot(b, Exclusion::Sym(ex)) => {
            format!("{} but not {}", render_sym(b), render_sym(ex))
        }
        GrammarItem::ButNot(b, Exclusion::OneOf { syms, or_sep }) => {
            let sep = if *or_sep { " or " } else { " " };
            let xs: Vec<_> = syms.iter().map(render_sym).collect();
            format!("{} but not one of {}", render_sym(b), xs.join(sep))
        }
        GrammarItem::OnlyIf(c) => format!("[> but only if {}]", spell_chars(true, phrase_text(c)?)),
        GrammarItem::Phrase(p) => format!("&gt; {}", spell_chars(false, phrase_text(p)?)),
    })
}

pub fn render_rule_lines(r: &Rule) -> Result<Vec<String>, String> {
    let params = if r.params.is_empty() {
        String::new()
    } else {
        format!("[{}]", r.params.join(", "))
    };
    let col = match r.colons {
        Colons::One => ":",
        Colons::Two => "::",
        Colons::Three => ":::",
    };
    let one_of = match r.body {
        RuleBody::OneOf(_) => " one of",
        RuleBody::Alts(_) => "",
    };
    let mut lines = vec![format!("{}{} {col}{one_of}", r.lhs, params)];
    match &r.body {
        RuleBody::Alts(alts) => {
            for a in alts {
                let mut ln = String::from("  ");
                if !a.guard.is_empty() {
                    let gs: Vec<_> = a
                        .guard
                        .iter()
                        .map(|g| format!("{}{}", if g.plus { "+" } else { "~" }, g.param))
                        .collect();
                    ln.push('[');
                    ln.push_str(&gs.join(", "));
                    ln.push_str("] ");
                }
                let rhs: Vec<_> = a.rhs.iter().map(render_item).collect::<Result<_, _>>()?;
                ln.push_str(&rhs.join(" "));
                if let Some(l) = &a.label {
                    ln.push_str(" #");
                    ln.push_str(l);
                }
                lines.push(ln);
            }
        }
        RuleBody::OneOf(rows) => {
            for row in rows {
                let ts: Vec<_> = row.iter().map(render_terminal).collect();
                lines.push(format!("  {}", ts.join(" ")));
            }
        }
    }
    Ok(lines)
}

pub fn render_rule_exact(r: &Rule) -> Result<String, String> {
    Ok(render_rule_lines(r)?.join("\n"))
}

pub fn format_block(indent: usize, fmt_ignore: &[usize], rule_texts: &[String]) -> Result<String, String> {
    if indent < 2 {
        return Err(format!("grammar block indent {indent} < 2"));
    }
    let ind = " ".repeat(indent);
    let mut parts = Vec::with_capacity(rule_texts.len());
    for (k, rtxt) in rule_texts.iter().enumerate() {
        let mut s = String::new();
        if fmt_ignore.contains(&k) {
            s.push_str(&ind);
            s.push_str("// emu-format ignore\n");
        }
        for ln in rtxt.split('\n') {
            s.push_str(&ind);
            s.push_str(ln);
            s.push('\n');
        }
        parts.push(s);
    }
    Ok(format!("\n{}{}", parts.join("\n"), " ".repeat(indent - 2)))
}

// --- Grammarkdown parser (port of HEAD~1:crates/jsgrammar/src/grammar.rs) ---

pub fn decode_entities(s: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find('&') {
        out.push_str(&rest[..i]);
        let t = &rest[i..];
        if let Some(h) = t.strip_prefix("&#x") {
            let n = h.find(';').ok_or_else(|| format!("unclosed character ref at {t:.20}"))?;
            let c = u32::from_str_radix(&h[..n], 16)
                .ok()
                .and_then(char::from_u32)
                .filter(|c| (!c.is_ascii() || c.is_ascii_control()) && spell_char(*c) == t[..n + 4])
                .ok_or_else(|| format!("unknown character ref at {t:.20}"))?;
            out.push(c);
            rest = &h[n + 1..];
            continue;
        }
        let (e, d) = ENTITIES
            .iter()
            .find(|(e, _)| t.starts_with(e))
            .ok_or_else(|| format!("unknown entity at {t:.20}"))?;
        out.push_str(d);
        rest = &t[e.len()..];
    }
    out.push_str(rest);
    Ok(out)
}

fn is_g_ident(c: char) -> bool {
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
        let n = self.rest().find(|c: char| !is_g_ident(c)).unwrap_or(self.rest().len());
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

    fn terminal(&mut self) -> Result<Option<Terminal>, String> {
        if self.eat("```") {
            return Ok(Some(Terminal::Text { text: "`".into(), alt: false }));
        }
        if self.eat("`") {
            let n = self.rest().find('`').ok_or_else(|| format!("unclosed terminal in `{}`", self.s))?;
            let raw = &self.rest()[..n];
            if raw.is_empty() {
                return self.err("empty terminal");
            }
            let text = decode_entities(raw)?;
            let alt = if text == "`" { raw == "&grave;" } else { raw.contains('>') };
            let t = Terminal::Text { text: text.clone(), alt };
            if render_terminal(&t) != format!("`{raw}`") {
                return self.err(&format!("unknown terminal spelling `{raw}` for `{text}`"));
            }
            self.i += n + 1;
            return Ok(Some(t));
        }
        if self.eat("&lt;") {
            let n = self
                .rest()
                .find("&gt;")
                .ok_or_else(|| format!("unclosed code point name in `{}`", self.s))?;
            let name = self.rest()[..n].to_string();
            if !CODE_POINTS.contains(&name.as_str()) {
                return self.err(&format!("unknown code point <{name}>"));
            }
            self.i += n + 4;
            return Ok(Some(Terminal::Cp(name)));
        }
        Ok(None)
    }

    fn sym(&mut self) -> Result<Option<GrammarSym>, String> {
        if let Some(t) = self.terminal()? {
            return Ok(Some(GrammarSym::T(t)));
        }
        if !self.rest().starts_with(|c: char| c.is_ascii_alphabetic()) {
            return Ok(None);
        }
        let name = self.ident().unwrap();
        let mut args = Vec::new();
        if self.eat("[") {
            loop {
                let sign = match self.rest().chars().next() {
                    Some('+') => ParamSign::Plus,
                    Some('~') => ParamSign::Tilde,
                    Some('?') => ParamSign::Quest,
                    _ => return self.err("expected `+P`, `~P`, or `?P`"),
                };
                self.i += 1;
                let param = self.ident().ok_or_else(|| format!("expected param in `{}`", self.s))?;
                args.push(NtArg { param, sign });
                if self.eat("]") {
                    break;
                }
                self.expect(", ")?;
            }
        }
        Ok(Some(GrammarSym::Nt(name, args)))
    }

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
            return self.err("empty lookahead sequence");
        }
        Ok(seq)
    }

    fn look_set(&mut self) -> Result<Vec<Vec<LookItem>>, String> {
        self.expect("{ ")?;
        let mut set = vec![self.look_seq()?];
        while self.eat(", ") {
            set.push(self.look_seq()?);
        }
        self.expect(" }")?;
        Ok(set)
    }

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
                Lookahead::NotMemNt(self.ident().ok_or_else(|| format!("expected NT in `{}`", self.s))?)
            }
        } else {
            return self.err("unknown lookahead form");
        };
        self.expect("]")?;
        Ok(l)
    }

    fn exclusion(&mut self) -> Result<Exclusion, String> {
        if self.eat("one of ") {
            let mut syms = vec![self
                .sym()?
                .ok_or_else(|| format!("expected symbol after `one of` in `{}`", self.s))?];
            let mut or_sep = None;
            while !self.end() {
                let o = if self.eat(" or ") {
                    true
                } else if self.eat(" ") {
                    false
                } else {
                    return self.err("expected `or` or space in exclusion");
                };
                if or_sep.is_some_and(|x| x != o) {
                    return self.err("mixed `or` and space in exclusion");
                }
                or_sep = Some(o);
                syms.push(
                    self.sym()?
                        .ok_or_else(|| format!("expected excluded symbol in `{}`", self.s))?,
                );
            }
            Ok(Exclusion::OneOf { syms, or_sep: or_sep.unwrap_or(true) })
        } else {
            let s = self
                .sym()?
                .ok_or_else(|| format!("expected excluded symbol in `{}`", self.s))?;
            Ok(Exclusion::Sym(s))
        }
    }
}

fn find_phrase_key(table: &[(&str, &str)], text: &str) -> Result<String, String> {
    table
        .iter()
        .find(|(t, _)| *t == text)
        .map(|(_, k)| (*k).to_string())
        .ok_or_else(|| format!("unknown grammar phrase `{text}`"))
}

pub fn parse_alt(line: &str) -> Result<Alt, String> {
    let mut label = None;
    let text_end = if let Some(k) = line.rfind(" #") {
        let l = &line[k + 2..];
        if !l.is_empty() && l.chars().all(is_g_ident) {
            label = Some(l.to_string());
            k
        } else {
            line.len()
        }
    } else {
        line.len()
    };
    let body = &line[..text_end];
    let mut c = Cur { s: body, i: 0 };
    if c.eat("&gt; ") {
        let p = find_phrase_key(PHRASES, &decode_entities(c.rest())?)?;
        return Ok(Alt {
            guard: Vec::new(),
            rhs: vec![GrammarItem::Phrase(p)],
            label,
        });
    }
    let mut guard = Vec::new();
    if c.at("[+") || c.at("[~") {
        c.i += 1;
        loop {
            let plus = c.eat("+");
            if !plus && !c.eat("~") {
                return c.err("expected `+P` or `~P`");
            }
            let param = c.ident().ok_or_else(|| format!("expected guard param in `{line}`"))?;
            guard.push(ParamArg { param, plus });
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
            rhs.push(GrammarItem::Empty);
        } else if c.eat("[no LineTerminator here]") {
            rhs.push(GrammarItem::NoLT);
        } else if c.eat("[lookahead ") {
            rhs.push(GrammarItem::Lookahead(c.lookahead()?));
        } else if c.eat("[> but only if ") || c.eat("[&gt; but only if ") {
            let n = c.rest().find(']').ok_or_else(|| format!("unclosed onlyIf in `{line}`"))?;
            let cond = find_phrase_key(CONDITIONS, &decode_entities(&c.rest()[..n])?)?;
            c.i += n + 1;
            rhs.push(GrammarItem::OnlyIf(cond));
        } else if let Some(s) = c.sym()? {
            if c.eat(" but not ") {
                rhs.push(GrammarItem::ButNot(s, c.exclusion()?));
            } else {
                let opt = c.eat("?");
                rhs.push(GrammarItem::Sym(s, opt));
            }
        } else {
            return c.err("unknown grammar item");
        }
    }
    if rhs.is_empty() {
        return c.err("empty alternative RHS");
    }
    Ok(Alt { guard, rhs, label })
}

fn parse_heading(line: &str) -> Result<(String, Vec<String>, Colons, bool), String> {
    let mut c = Cur { s: line, i: 0 };
    let name = c.ident().ok_or_else(|| format!("expected LHS heading in `{line}`"))?;
    let mut params = Vec::new();
    if c.eat("[") {
        loop {
            params.push(c.ident().ok_or_else(|| format!("expected param in `{line}`"))?);
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
        return c.err("expected `:`, `::`, or `:::`");
    };
    let one_of = c.eat(" one of");
    if !c.end() {
        return c.err("trailing text after rule heading");
    }
    Ok((name, params, colons, one_of))
}

#[derive(Clone, Debug)]
pub struct ParsedHtmlBlock {
    pub indent: usize,
    pub fmt_ignore: Vec<usize>,
    pub rules: Vec<(Rule, String)>,
}

pub fn parse_html_block(b: &HtmlBlock, grammar: GrammarId) -> Result<ParsedHtmlBlock, String> {
    let lines: Vec<&str> = b.text.split('\n').collect();
    let indent_of = |l: &str| l.len() - l.trim_start().len();
    let skip = |l: &str| l.trim().is_empty() || l.trim_start().starts_with("// ");
    let base = lines
        .iter()
        .filter(|l| !skip(l))
        .map(|l| indent_of(l))
        .min()
        .ok_or_else(|| format!("spec.html:{}: empty grammar block", b.line))?;
    let mut rules: Vec<(Rule, Vec<String>)> = Vec::new();
    let mut fmt_ignore_vec = Vec::new();
    let mut next_fmt_ignore = false;
    for (k, ln) in lines.iter().enumerate() {
        let line_no = b.line + k;
        if ln.trim_start().starts_with("// ") {
            if ln.trim() != "// emu-format ignore" {
                return Err(format!("spec.html:{line_no}: unknown comment {}", ln.trim()));
            }
            next_fmt_ignore = true;
            continue;
        }
        if ln.trim().is_empty() {
            continue;
        }
        if ln.ends_with(' ') || ln.ends_with('\t') {
            return Err(format!("spec.html:{line_no}: trailing whitespace"));
        }
        let ind = indent_of(ln);
        let t = ln.trim_start();
        if ind == base {
            let (lhs, params, colons, is_one_of) = parse_heading(t).map_err(|e| format!("spec.html:{line_no}: {e}"))?;
            if next_fmt_ignore {
                fmt_ignore_vec.push(rules.len());
                next_fmt_ignore = false;
            }
            let body = if is_one_of {
                RuleBody::OneOf(Vec::new())
            } else {
                RuleBody::Alts(Vec::new())
            };
            rules.push((
                Rule { grammar, lhs, params, colons, body },
                vec![ln[base..].to_string()],
            ));
            continue;
        }
        if next_fmt_ignore {
            return Err(format!("spec.html:{line_no}: formatter comment before alternative"));
        }
        let (r, raw) = rules
            .last_mut()
            .ok_or_else(|| format!("spec.html:{line_no}: alternative before rule heading"))?;
        if ind != base + 2 {
            return Err(format!("spec.html:{line_no}: alt indent {} != 2", ind - base));
        }
        raw.push(ln[base..].to_string());
        match &mut r.body {
            RuleBody::Alts(alts) => alts.push(parse_alt(t).map_err(|e| format!("spec.html:{line_no}: {e}"))?),
            RuleBody::OneOf(rows) => {
                let mut c = Cur { s: t, i: 0 };
                let mut row = Vec::new();
                loop {
                    row.push(
                        c.terminal()
                            .map_err(|e| format!("spec.html:{line_no}: {e}"))?
                            .ok_or_else(|| format!("spec.html:{line_no}: expected terminal in `{t}`"))?,
                    );
                    if c.end() {
                        break;
                    }
                    c.expect(" ").map_err(|e| format!("spec.html:{line_no}: {e}"))?;
                }
                rows.push(row);
            }
        }
    }
    let out_rules: Vec<(Rule, String)> = rules.into_iter().map(|(r, ls)| (r, ls.join("\n"))).collect();
    let rule_texts: Vec<String> = out_rules.iter().map(|(_, s)| s.clone()).collect();
    if format_block(base, &fmt_ignore_vec, &rule_texts)? != b.text {
        return Err(format!("spec.html:{}: irregular blank lines or closing tag indent in block", b.line));
    }
    Ok(ParsedHtmlBlock { indent: base, fmt_ignore: fmt_ignore_vec, rules: out_rules })
}

// --- Bootstrap & Bidirectional Check ---

pub struct GrammarStats {
    pub html_blocks: usize,
    pub spectec_blocks: usize,
    pub spectec_only_blocks: usize,
    pub total_rules: usize,
    pub rule_overrides: usize,
}

pub fn bootstrap_grammar(spec: &Spec, html: &HtmlSpec) -> Result<(GrammarMeta, GrammarStats), String> {
    let mut rules_by_key: BTreeMap<(GrammarId, String), &Rule> = BTreeMap::new();
    let mut blocks: Vec<&BlockDef> = Vec::new();
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Rule(r) => {
                    if rules_by_key.insert((r.grammar, r.lhs.clone()), r).is_some() {
                        return Err(format!("duplicate rule {:?} {}", r.grammar, r.lhs));
                    }
                }
                TopItem::Block(b) => blocks.push(b),
                _ => {}
            }
        }
    }

    let mut meta = GrammarMeta::default();
    let mut cnt: BTreeMap<String, usize> = BTreeMap::new();
    let mut total_rules = 0usize;
    let mut html_blocks = 0usize;
    let mut spectec_only_blocks = 0usize;

    for b in &blocks {
        let k = *cnt.entry(b.clause.clone()).or_insert(0);
        cnt.insert(b.clause.clone(), k + 1);
        let key = ItemKey::new(&b.clause, k);
        if b.grammar == GrammarId::Json {
            meta.spectec_only_blocks.insert(key, b.grammar);
            spectec_only_blocks += 1;
            total_rules += b.rules.len();
            continue;
        }
        let hb = html
            .block_by_clause_k(&b.clause, k)
            .ok_or_else(|| format!("missing HTML <emu-grammar type=\"definition\"> for {}", key.fmt_ref()))?;
        let parsed = parse_html_block(hb, b.grammar)?;
        html_blocks += 1;
        meta.blocks.insert(
            key.clone(),
            BlockLayout {
                key: key.clone(),
                grammar: b.grammar,
                indent: parsed.indent,
                fmt_ignore: parsed.fmt_ignore.clone(),
            },
        );
        if parsed.rules.len() != b.rules.len() {
            return Err(format!("{} rule count mismatch: html {} vs spectec {}", key.fmt_ref(), parsed.rules.len(), b.rules.len()));
        }
        for (lhs, (hr, raw_hr)) in b.rules.iter().zip(parsed.rules.iter()) {
            if &hr.lhs != lhs {
                return Err(format!("{} rule LHS mismatch: html {} vs spectec {lhs}", key.fmt_ref(), hr.lhs));
            }
            let sr = *rules_by_key
                .get(&(b.grammar, lhs.clone()))
                .ok_or_else(|| format!("SpecTec missing rule {} |{lhs}|", b.grammar.as_str()))?;
            total_rules += 1;
            let rendered = render_rule_exact(sr)?;
            if &rendered != raw_hr || hr != sr {
                let st_text = print_rule(sr).trim_end().to_string();
                meta.overrides.insert(
                    (key.clone(), lhs.clone()),
                    RuleOverride {
                        key: key.clone(),
                        grammar: b.grammar,
                        lhs: lhs.clone(),
                        spectec_rule: st_text,
                        html_rule: raw_hr.clone(),
                    },
                );
            }
        }
    }
    let stats = GrammarStats {
        html_blocks,
        spectec_blocks: blocks.len(),
        spectec_only_blocks,
        total_rules,
        rule_overrides: meta.overrides.len(),
    };
    Ok((meta, stats))
}

pub fn render_grammar_splices(spec: &Spec, html: &HtmlSpec, meta: &GrammarMeta) -> Result<(Vec<(usize, usize, String, String)>, BTreeSet<ItemKey>, BTreeSet<(ItemKey, String)>, BTreeSet<ItemKey>), String> {
    let mut rules_by_key: BTreeMap<(GrammarId, String), &Rule> = BTreeMap::new();
    let mut blocks: Vec<&BlockDef> = Vec::new();
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Rule(r) => {
                    rules_by_key.insert((r.grammar, r.lhs.clone()), r);
                }
                TopItem::Block(b) => blocks.push(b),
                _ => {}
            }
        }
    }
    let mut used_blocks = BTreeSet::new();
    let mut used_overrides = BTreeSet::new();
    let mut used_spectec_only = BTreeSet::new();
    let mut splices = Vec::new();
    let mut cnt: BTreeMap<String, usize> = BTreeMap::new();

    for b in blocks {
        let k = *cnt.entry(b.clause.clone()).or_insert(0);
        cnt.insert(b.clause.clone(), k + 1);
        let key = ItemKey::new(&b.clause, k);
        if let Some(&og) = meta.spectec_only_blocks.get(&key) {
            if og != b.grammar {
                return Err(format!("{} spectec_only grammar mismatch", key.fmt_ref()));
            }
            for lhs in &b.rules {
                if !rules_by_key.contains_key(&(b.grammar, lhs.clone())) {
                    return Err(format!("{} missing rule |{lhs}|", key.fmt_ref()));
                }
            }
            used_spectec_only.insert(key);
            continue;
        }
        let layout = meta
            .blocks
            .get(&key)
            .ok_or_else(|| format!("grammar-meta missing block {}", key.fmt_ref()))?;
        if layout.grammar != b.grammar {
            return Err(format!("grammar-meta {} grammar mismatch", key.fmt_ref()));
        }
        used_blocks.insert(key.clone());
        let hb = html
            .block_by_clause_k(&b.clause, k)
            .ok_or_else(|| format!("spec.html missing grammar block {}", key.fmt_ref()))?;
        let mut rtexts = Vec::with_capacity(b.rules.len());
        for lhs in &b.rules {
            let sr = *rules_by_key
                .get(&(b.grammar, lhs.clone()))
                .ok_or_else(|| format!("SpecTec missing rule {} |{lhs}|", b.grammar.as_str()))?;
            if let Some(ov) = meta.overrides.get(&(key.clone(), lhs.clone())) {
                if ov.grammar != b.grammar {
                    return Err(format!("rule override {} |{lhs}| grammar mismatch", key.fmt_ref()));
                }
                let actual_st = print_rule(sr).trim_end().to_string();
                if actual_st != ov.spectec_rule {
                    return Err(format!(
                        "rule override {} |{lhs}| stale: SpecTec differs from @@spectec",
                        key.fmt_ref()
                    ));
                }
                used_overrides.insert((key.clone(), lhs.clone()));
                rtexts.push(ov.html_rule.clone());
            } else {
                rtexts.push(render_rule_exact(sr)?);
            }
        }
        let body = format_block(layout.indent, &layout.fmt_ignore, &rtexts)?;
        splices.push((hb.span.0, hb.span.1, body, format!("grammar {}", key.fmt_ref())));
    }
    Ok((splices, used_blocks, used_overrides, used_spectec_only))
}

pub fn check_grammar_backward(spec: &Spec, html: &HtmlSpec, meta: &GrammarMeta) -> Result<GrammarStats, String> {
    let mut spectec_rules: BTreeMap<(GrammarId, String), &Rule> = BTreeMap::new();
    let mut spectec_blocks: Vec<&BlockDef> = Vec::new();
    for f in &spec.files {
        for item in &f.items {
            match item {
                TopItem::Rule(r) => {
                    spectec_rules.insert((r.grammar, r.lhs.clone()), r);
                }
                TopItem::Block(b) => spectec_blocks.push(b),
                _ => {}
            }
        }
    }

    // 1. Parse all 90 HTML blocks back into Rules using grammar-meta.
    let mut recon_rules: BTreeMap<(GrammarId, String), Rule> = BTreeMap::new();
    let mut cnt: BTreeMap<String, usize> = BTreeMap::new();
    let mut used_blocks = BTreeSet::new();
    let mut used_overrides = BTreeSet::new();
    for hb in &html.blocks {
        let key = ItemKey::new(&hb.clause, hb.clause_k);
        let k = *cnt.entry(hb.clause.clone()).or_insert(0);
        cnt.insert(hb.clause.clone(), k + 1);
        assert_eq!(k, hb.clause_k);
        let layout = meta
            .blocks
            .get(&key)
            .ok_or_else(|| format!("grammar-meta missing HTML block {}", key.fmt_ref()))?;
        used_blocks.insert(key.clone());
        let parsed = parse_html_block(hb, layout.grammar)?;
        if parsed.indent != layout.indent || parsed.fmt_ignore != layout.fmt_ignore {
            return Err(format!("{} block layout differs between spec.html and grammar-meta", key.fmt_ref()));
        }
        for (hr, raw_hr) in parsed.rules {
            let lhs = hr.lhs.clone();
            let final_rule = if let Some(ov) = meta.overrides.get(&(key.clone(), lhs.clone())) {
                if ov.grammar != layout.grammar {
                    return Err(format!("override {} |{lhs}| grammar mismatch", key.fmt_ref()));
                }
                if raw_hr != ov.html_rule {
                    return Err(format!("{} |{lhs}| in spec.html differs from @@html in override", key.fmt_ref()));
                }
                let src = format!("grammar {}\n\n{}\n\n", ov.grammar.as_str(), ov.spectec_rule);
                let sf = parse_str("override.spectec", &src)?;
                let mut found = None;
                for it in sf.items {
                    if let TopItem::Rule(r) = it {
                        found = Some(r);
                    }
                }
                used_overrides.insert((key.clone(), lhs.clone()));
                found.ok_or_else(|| format!("override {} |{lhs}| failed to parse rule", key.fmt_ref()))?
            } else {
                // Non-overridden rule MUST roundtrip purely through SpecTec -> exact HTML too.
                let ser = render_rule_exact(&hr)?;
                if ser != raw_hr {
                    return Err(format!(
                        "{} |{lhs}| non-overridden rule failed grammarkdown roundtrip:\n  html: {raw_hr:?}\n  prnt: {ser:?}",
                        key.fmt_ref()
                    ));
                }
                hr
            };
            if recon_rules.insert((layout.grammar, lhs.clone()), final_rule).is_some() {
                return Err(format!("duplicate reconstructed rule {} |{lhs}|", layout.grammar.as_str()));
            }
        }
    }

    // 2. Compare reconstructed rules against non-json SpecTec rules.
    let mut non_json_count = 0usize;
    for ((g, lhs), sr) in &spectec_rules {
        if *g == GrammarId::Json {
            continue;
        }
        non_json_count += 1;
        let rr = recon_rules
            .get(&(*g, lhs.clone()))
            .ok_or_else(|| format!("SpecTec rule {} |{lhs}| not found in spec.html", g.as_str()))?;
        if rr != *sr {
            return Err(format!(
                "rule {} |{lhs}| reconstructed from spec.html differs from SpecTec AST",
                g.as_str()
            ));
        }
    }
    for (g, lhs) in recon_rules.keys() {
        if !spectec_rules.contains_key(&(*g, lhs.clone())) {
            return Err(format!("spec.html rule {} |{lhs}| not found in SpecTec", g.as_str()));
        }
    }

    // 3. Forward splice check & byte-for-byte comparison with spec.html blocks.
    let (splices, fwd_blocks, fwd_overrides, fwd_only) = render_grammar_splices(spec, html, meta)?;
    let defined_blocks: BTreeSet<_> = meta.blocks.keys().cloned().collect();
    let defined_overrides: BTreeSet<_> = meta.overrides.keys().cloned().collect();
    let defined_only: BTreeSet<_> = meta.spectec_only_blocks.keys().cloned().collect();
    crate::meta::check_all_used(&defined_blocks, &used_blocks, "grammar block (backward)")?;
    crate::meta::check_all_used(&defined_blocks, &fwd_blocks, "grammar block (forward)")?;
    crate::meta::check_all_used(&defined_overrides, &used_overrides, "grammar override (backward)")?;
    crate::meta::check_all_used(&defined_overrides, &fwd_overrides, "grammar override (forward)")?;
    crate::meta::check_all_used(&defined_only, &fwd_only, "spectec_only grammar block")?;

    if splices.len() != html.blocks.len() {
        return Err(format!("forward rendered {} blocks, spec.html has {}", splices.len(), html.blocks.len()));
    }
    for ((s, e, txt, lbl), hb) in splices.iter().zip(html.blocks.iter()) {
        if (*s, *e) != hb.span || txt != &hb.text {
            return Err(format!("{lbl} (spec.html:{}) forward text differs from spec.html", hb.line));
        }
    }
    let _ = non_json_count;
    Ok(GrammarStats {
        html_blocks: html.blocks.len(),
        spectec_blocks: spectec_blocks.len(),
        spectec_only_blocks: meta.spectec_only_blocks.len(),
        total_rules: spectec_rules.len(),
        rule_overrides: meta.overrides.len(),
    })
}
