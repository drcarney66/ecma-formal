//! Lexer for ECMA-262 SpecTec `.spectec` files.

use crate::ast::{NtArg, ParamSign};

pub const KEYWORDS: &[&str] = &[
    "alg", "and", "annot", "anyCodePoint", "assert", "assert_if", "block", "butnot", "by", "call_at",
    "captures", "checked_jobs", "child", "child_of", "children", "choice", "clause", "clause_prods",
    "clause_props", "closure", "cmethod", "code", "completion", "component", "cover", "cp", "cu", "data",
    "def", "default", "defined", "desc", "dfn", "do", "doc", "early", "early_syntax_error", "either", "else",
    "else_if", "empty", "enum", "eq", "err", "excl", "extern", "fails", "false", "field", "fields",
    "for_children", "for_children_of", "for_each", "for_each_rec", "for_index", "for_keys", "for_range",
    "form", "frac", "from", "goal", "grammar", "grammar_alt", "groupNumberAtMostCount", "header", "hex",
    "idContinue", "idStart", "if", "if_else", "if_inline", "imethod", "in", "incl", "info", "init",
    "interval", "intrinsic", "is", "keys", "kind", "leadSurrogate", "let", "lines", "link", "list",
    "lookahead", "many", "math", "method", "modulo", "must_cover", "mvAbove10FFFF", "mvAtMost10FFFF",
    "mvLead", "mvNonSurrogate", "mvTrail", "nan", "nan_f", "nan_z", "neg", "neither", "new",
    "new_target", "no", "noLT", "none", "not", "not_applied", "not_in", "note", "nt", "null", "num",
    "num_f", "num_n", "num_z", "obj", "of", "one", "one_of", "onlyIf", "op", "opt", "or", "order",
    "param", "params", "pass", "perform", "plain", "plus", "pred", "prods", "props", "push", "raw",
    "realm", "record", "ref", "remove", "remove_restore", "repeat", "repeat_n", "repeat_until",
    "repeat_while", "rest", "resume", "resume_let", "resume_top", "resumed_with", "ret", "retired",
    "return", "rev", "row", "rows", "rule", "rules_applied", "sat", "schema", "sdo", "sdo_row", "semi", "seq",
    "set", "set_code_state", "sig", "slot", "slots", "some", "sort", "sort_alias", "step", "steps", "stmt", "subject", "super", "supplemental", "suspend", "symbols", "syntax", "syntax_error",
    "syntax_error_ins", "table", "table_step", "test", "text", "that", "thead", "then", "this",
    "this_node", "this_value", "throw", "times", "to", "trailSurrogate", "true", "ty", "undefined",
    "unless", "unreachable", "val", "var", "vars", "where",
];

pub fn is_keyword(s: &str) -> bool {
    KEYWORDS.binary_search(&s).is_ok()
}

pub fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

pub fn is_ident_cont(c: char) -> bool {
    is_ident_start(c) || c.is_ascii_digit()
}

pub fn is_prim_start(c: char) -> bool {
    is_ident_start(c) || c == '𝔽' || c == 'ℝ' || c == 'ℤ'
}

pub fn is_prim_cont(c: char) -> bool {
    is_ident_cont(c) || c == '𝔽' || c == 'ℝ' || c == 'ℤ'
}

pub fn is_clause_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '-' | '.' | '%' | '/')
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokKind {
    Ident { name: String, quoted: bool },
    Prim(String),
    Clause(String),
    Field(String),
    Enum(String),
    Prod(String),
    Table(String),
    Nt(String, Vec<NtArg>),
    Bnd(String),
    Str(String),
    Int(u64),
    HashIdx(usize),
    HashLabel,
    Arrow,
    DotDot,
    Colons3,
    Colons2,
    Le,
    Ge,
    EqEq,
    Ne,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Semi,
    Comma,
    Dot,
    Eq,
    Lt,
    Gt,
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Quest,
    Bang,
    Tilde,
    Pipe,
    Amp,
    Inf,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokKind,
    pub line: usize,
    pub col: usize,
}

pub struct LexOut {
    pub header_comment: Option<String>,
    pub tokens: Vec<Token>,
}

struct Scanner<'a> {
    src: &'a str,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Scanner<'a> {
    fn new(src: &'a str) -> Self {
        Self { src, pos: 0, line: 1, col: 1 }
    }

    fn rest(&self) -> &'a str {
        &self.src[self.pos..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }

    fn err(&self, msg: &str) -> String {
        format!("line {}:{}: {msg}", self.line, self.col)
    }

    fn skip_ws_and_comments(&mut self, leading_comment: &mut Option<String>, at_start: bool) {
        let mut first = at_start;
        loop {
            while let Some(c) = self.peek() {
                if c.is_ascii_whitespace() {
                    self.bump();
                } else {
                    break;
                }
            }
            if self.rest().starts_with("--") {
                let start = self.pos;
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        break;
                    }
                    self.bump();
                }
                let text = self.src[start..self.pos].trim_end_matches('\r').to_string();
                if first && leading_comment.is_none() {
                    *leading_comment = Some(text);
                }
                first = false;
            } else {
                break;
            }
        }
    }

    fn read_string(&mut self) -> Result<String, String> {
        if self.bump() != Some('"') {
            return Err(self.err("expected '\"'"));
        }
        let mut out = String::new();
        loop {
            let c = self.bump().ok_or_else(|| self.err("unterminated string literal"))?;
            if c == '"' {
                return Ok(out);
            }
            if c != '\\' {
                out.push(c);
                continue;
            }
            let esc = self.bump().ok_or_else(|| self.err("unterminated escape"))?;
            match esc {
                '\\' => out.push('\\'),
                '"' => out.push('"'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'u' => {
                    if self.bump() != Some('{') {
                        return Err(self.err("expected '{' in \\u{...}"));
                    }
                    let mut hex = String::new();
                    loop {
                        let hc = self.bump().ok_or_else(|| self.err("unclosed \\u{...}"))?;
                        if hc == '}' {
                            break;
                        }
                        hex.push(hc);
                    }
                    let cp = u32::from_str_radix(&hex, 16)
                        .map_err(|_| self.err("invalid hex in \\u{...}"))?;
                    let ch = char::from_u32(cp)
                        .ok_or_else(|| self.err("invalid Unicode scalar in \\u{...}"))?;
                    out.push(ch);
                }
                _ => return Err(self.err(&format!("unknown escape \\{esc}"))),
            }
        }
    }

    fn read_bare_ident(&mut self) -> String {
        let start = self.pos;
        self.bump();
        while let Some(c) = self.peek() {
            if is_ident_cont(c) {
                self.bump();
            } else {
                break;
            }
        }
        self.src[start..self.pos].to_string()
    }

    fn try_lex_field(&mut self) -> Option<String> {
        let bytes = self.rest().as_bytes();
        if !bytes.starts_with(b"[[") {
            return None;
        }
        // Must have >= 1 char without '[', ']', '\n' closed immediately by "]]".
        let after = &self.rest()[2..];
        let mut end = None;
        for (i, ch) in after.char_indices() {
            if ch == '[' || ch == '\n' || ch == '\r' {
                return None;
            }
            if ch == ']' {
                if after[i..].starts_with("]]") && i > 0 {
                    end = Some(i);
                }
                break;
            }
        }
        let end_idx = end?;
        let name = after[..end_idx].to_string();
        for _ in 0..(2 + name.chars().count() + 2) {
            self.bump();
        }
        Some(name)
    }

    fn try_lex_enum(&mut self) -> Option<String> {
        let rest = self.rest();
        if !rest.starts_with('~') {
            return None;
        }
        let after = &rest[1..];
        let mut end = None;
        for (i, ch) in after.char_indices() {
            if ch == '~' {
                if i > 0 {
                    end = Some(i);
                }
                break;
            }
            if !(ch.is_alphanumeric() || ch == '_' || ch == '-' || ch == '+') {
                return None;
            }
        }
        let end_idx = end?;
        let name = after[..end_idx].to_string();
        for _ in 0..(1 + name.chars().count() + 1) {
            self.bump();
        }
        Some(name)
    }

    fn lex_nt(&mut self) -> Result<(String, Vec<NtArg>), String> {
        self.bump(); // opening '|'
        let name = if self.rest().starts_with("#\"") {
            self.bump();
            self.read_string()?
        } else {
            let start = self.pos;
            while let Some(c) = self.peek() {
                if is_ident_cont(c) {
                    self.bump();
                } else {
                    break;
                }
            }
            if self.pos == start {
                return Err(self.err("expected nonterminal name after '|'"));
            }
            self.src[start..self.pos].to_string()
        };
        let mut args = Vec::new();
        if self.peek() == Some('[') {
            self.bump();
            loop {
                while matches!(self.peek(), Some(' ')) {
                    self.bump();
                }
                let sgn = match self.bump() {
                    Some('+') => ParamSign::Plus,
                    Some('~') => ParamSign::Tilde,
                    Some('?') => ParamSign::Quest,
                    _ => return Err(self.err("expected +, ~, or ? in nonterminal args")),
                };
                let arg_name = if self.rest().starts_with("#\"") {
                    self.bump();
                    self.read_string()?
                } else if matches!(self.peek(), Some(c) if is_ident_start(c)) {
                    self.read_bare_ident()
                } else {
                    return Err(self.err("expected param name in nonterminal args"));
                };
                args.push(NtArg { param: arg_name, sign: sgn });
                while matches!(self.peek(), Some(' ')) {
                    self.bump();
                }
                match self.bump() {
                    Some(',') => continue,
                    Some(']') => break,
                    _ => return Err(self.err("expected ',' or ']' in nonterminal args")),
                }
            }
        }
        if self.bump() != Some('|') {
            return Err(self.err("expected closing '|' for nonterminal"));
        }
        Ok((name, args))
    }

    fn lex_all(mut self) -> Result<LexOut, String> {
        let mut header_comment = None;
        let mut tokens = Vec::new();
        let mut at_start = true;
        loop {
            self.skip_ws_and_comments(&mut header_comment, at_start);
            at_start = false;
            let line = self.line;
            let col = self.col;
            let Some(ch) = self.peek() else {
                tokens.push(Token { kind: TokKind::Eof, line, col });
                return Ok(LexOut { header_comment, tokens });
            };
            let kind = match ch {
                '"' => TokKind::Str(self.read_string()?),
                '[' => {
                    if let Some(f) = self.try_lex_field() {
                        TokKind::Field(f)
                    } else {
                        self.bump();
                        TokKind::LBracket
                    }
                }
                ']' => {
                    self.bump();
                    TokKind::RBracket
                }
                '{' => { self.bump(); TokKind::LBrace }
                '}' => { self.bump(); TokKind::RBrace }
                '(' => { self.bump(); TokKind::LParen }
                ')' => { self.bump(); TokKind::RParen }
                ';' => { self.bump(); TokKind::Semi }
                ',' => { self.bump(); TokKind::Comma }
                '+' => { self.bump(); TokKind::Plus }
                '*' => { self.bump(); TokKind::Star }
                '/' => { self.bump(); TokKind::Slash }
                '^' => { self.bump(); TokKind::Caret }
                '?' => {
                    self.bump();
                    if self.rest().starts_with("#\"") {
                        self.bump();
                        TokKind::Bnd(self.read_string()?)
                    } else if matches!(self.peek(), Some(c) if is_ident_start(c)) {
                        TokKind::Bnd(self.read_bare_ident())
                    } else {
                        TokKind::Quest
                    }
                }
                '&' => { self.bump(); TokKind::Amp }
                '∞' => { self.bump(); TokKind::Inf }
                '-' => {
                    if self.rest().starts_with("->") {
                        self.bump(); self.bump();
                        TokKind::Arrow
                    } else {
                        self.bump();
                        TokKind::Minus
                    }
                }
                '.' => {
                    if self.rest().starts_with("..") {
                        self.bump(); self.bump();
                        TokKind::DotDot
                    } else {
                        self.bump();
                        TokKind::Dot
                    }
                }
                ':' => {
                    if self.rest().starts_with(":::") {
                        self.bump(); self.bump(); self.bump();
                        TokKind::Colons3
                    } else if self.rest().starts_with("::") {
                        self.bump(); self.bump();
                        TokKind::Colons2
                    } else {
                        self.bump();
                        TokKind::Colon
                    }
                }
                '<' => {
                    if self.rest().starts_with("<=") {
                        self.bump(); self.bump();
                        TokKind::Le
                    } else {
                        self.bump();
                        TokKind::Lt
                    }
                }
                '>' => {
                    if self.rest().starts_with(">=") {
                        self.bump(); self.bump();
                        TokKind::Ge
                    } else {
                        self.bump();
                        TokKind::Gt
                    }
                }
                '=' => {
                    if self.rest().starts_with("==") {
                        self.bump(); self.bump();
                        TokKind::EqEq
                    } else {
                        self.bump();
                        TokKind::Eq
                    }
                }
                '!' => {
                    if self.rest().starts_with("!=") {
                        self.bump(); self.bump();
                        TokKind::Ne
                    } else {
                        self.bump();
                        TokKind::Bang
                    }
                }
                '~' => {
                    if let Some(e) = self.try_lex_enum() {
                        TokKind::Enum(e)
                    } else {
                        self.bump();
                        TokKind::Tilde
                    }
                }
                '|' => {
                    let next = self.rest().chars().nth(1);
                    if next.is_none() || next.unwrap().is_whitespace() {
                        self.bump();
                        TokKind::Pipe
                    } else {
                        let (n, args) = self.lex_nt()?;
                        TokKind::Nt(n, args)
                    }
                }
                '$' => {
                    self.bump();
                    if self.peek() == Some('"') {
                        TokKind::Prim(self.read_string()?)
                    } else if matches!(self.peek(), Some(c) if is_prim_start(c)) {
                        let start = self.pos;
                        self.bump();
                        while let Some(c) = self.peek() {
                            if is_prim_cont(c) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                        TokKind::Prim(self.src[start..self.pos].to_string())
                    } else {
                        return Err(self.err("expected primitive name after '$'"));
                    }
                }
                '@' => {
                    self.bump();
                    if self.peek() == Some('"') {
                        TokKind::Clause(self.read_string()?)
                    } else {
                        let start = self.pos;
                        while let Some(c) = self.peek() {
                            if is_clause_char(c) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                        if self.pos == start {
                            return Err(self.err("expected clause name after '@'"));
                        }
                        TokKind::Clause(self.src[start..self.pos].to_string())
                    }
                }
                '#' => {
                    self.bump();
                    if self.peek() == Some('"') {
                        TokKind::Ident { name: self.read_string()?, quoted: true }
                    } else if self.rest().starts_with("label")
                        && !self.rest()[5..].chars().next().is_some_and(is_ident_cont)
                    {
                        for _ in 0..5 {
                            self.bump();
                        }
                        TokKind::HashLabel
                    } else if matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                        let start = self.pos;
                        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                            self.bump();
                        }
                        let idx: usize = self.src[start..self.pos]
                            .parse()
                            .map_err(|_| self.err("invalid #index"))?;
                        TokKind::HashIdx(idx)
                    } else {
                        return Err(self.err("unexpected token starting with '#'"));
                    }
                }
                'p' if self.rest().starts_with("p\"") => {
                    self.bump();
                    TokKind::Prod(self.read_string()?)
                }
                't' if self.rest().starts_with("t\"") => {
                    self.bump();
                    TokKind::Table(self.read_string()?)
                }
                c if c.is_ascii_digit() => {
                    let start = self.pos;
                    while matches!(self.peek(), Some(d) if d.is_ascii_digit()) {
                        self.bump();
                    }
                    let n: u64 = self.src[start..self.pos]
                        .parse()
                        .map_err(|_| self.err("integer overflow"))?;
                    TokKind::Int(n)
                }
                c if is_ident_start(c) => {
                    let name = self.read_bare_ident();
                    TokKind::Ident { name, quoted: false }
                }
                other => return Err(self.err(&format!("unexpected character `{other}`"))),
            };
            tokens.push(Token { kind, line, col });
        }
    }
}

pub fn lex(src: &str) -> Result<LexOut, String> {
    Scanner::new(src).lex_all()
}
