//! Lexer and recursive-descent parser for `spec/spectec/prose/*.spectec`.

use crate::ast::{SpecFile, TopItem};
use crate::spec_model::ast::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokKind {
    Doc(String),
    ModDoc(String),
    Ident(String),
    Str(String),
    Char(char),
    Int(u64),
    Hex(String),
    Arrow,
    FatArrow,
    Iff,
    Bind,
    Turnstile,
    Le,
    Ge,
    EqEq,
    Ne,
    PropNe,
    Append,
    Cons,
    Assign,
    LogicAnd,
    LogicOr,
    BoolAnd,
    BoolOr,
    DotDot,
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
    Percent,
    Caret,
    Bang,
    Pipe,
    At,
    Quest,
    Eof,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokKind,
    line: usize,
    col: usize,
}

fn is_id_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || matches!(c, 'α'..='ω' | 'Α'..='Ω')
}

fn is_id_cont(c: char) -> bool {
    is_id_start(c)
        || c.is_ascii_digit()
        || c == '\''
        || c == '?'
        || matches!(c, '\u{2080}'..='\u{209C}')
}

struct Lexer<'a> {
    src: &'a str,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src,
            pos: 0,
            line: 1,
            col: 1,
        }
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

    fn read_line_text(&mut self) -> String {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
        }
        let s = &self.src[start..self.pos];
        if self.peek() == Some('\r') {
            self.bump();
        }
        if self.peek() == Some('\n') {
            self.bump();
        }
        s.strip_prefix(' ').unwrap_or(s).to_string()
    }

    fn lex_all(mut self) -> Result<(Option<String>, Vec<Token>), String> {
        let mut header_comment = None;
        let mut tokens = Vec::new();
        let mut at_file_start = true;

        loop {
            while let Some(c) = self.peek() {
                if c.is_ascii_whitespace() {
                    self.bump();
                } else {
                    break;
                }
            }
            if self.pos >= self.src.len() {
                tokens.push(Token {
                    kind: TokKind::Eof,
                    line: self.line,
                    col: self.col,
                });
                return Ok((header_comment, tokens));
            }
            let r = self.rest();
            let line = self.line;
            let col = self.col;

            if r.starts_with("---!") {
                at_file_start = false;
                let mut lines = Vec::new();
                while self.rest().starts_with("---!") {
                    self.pos += 4;
                    self.col += 4;
                    lines.push(self.read_line_text());
                    while let Some(c) = self.peek() {
                        if c == ' ' || c == '\t' {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                tokens.push(Token {
                    kind: TokKind::ModDoc(lines.join("\n")),
                    line,
                    col,
                });
                continue;
            }

            if r.starts_with("---") {
                at_file_start = false;
                let mut lines = Vec::new();
                while self.rest().starts_with("---") && !self.rest().starts_with("---!") {
                    self.pos += 3;
                    self.col += 3;
                    lines.push(self.read_line_text());
                    while let Some(c) = self.peek() {
                        if c == ' ' || c == '\t' {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                tokens.push(Token {
                    kind: TokKind::Doc(lines.join("\n")),
                    line,
                    col,
                });
                continue;
            }

            if r.starts_with("--") {
                if at_file_start {
                    let mut hlines = Vec::new();
                    while self.rest().starts_with("--")
                        && !self.rest().starts_with("---")
                    {
                        let start = self.pos;
                        while let Some(c) = self.peek() {
                            if c == '\n' || c == '\r' {
                                break;
                            }
                            self.bump();
                        }
                        hlines.push(self.src[start..self.pos].to_string());
                        if self.peek() == Some('\r') {
                            self.bump();
                        }
                        if self.peek() == Some('\n') {
                            self.bump();
                        }
                        while matches!(self.peek(), Some(' ' | '\t')) {
                            self.bump();
                        }
                    }
                    header_comment = Some(hlines.join("\n"));
                    at_file_start = false;
                } else {
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            self.bump();
                            break;
                        }
                        self.bump();
                    }
                }
                continue;
            }
            at_file_start = false;

            if let Some(tok) = self.lex_op_or_punct(r, line, col) {
                tokens.push(tok);
                continue;
            }

            let ch = self.peek().unwrap();
            if ch == '"' {
                self.bump();
                let mut s = String::new();
                loop {
                    match self.bump() {
                        Some('"') => break,
                        Some('\\') => match self.bump() {
                            Some('n') => s.push('\n'),
                            Some('r') => s.push('\r'),
                            Some('t') => s.push('\t'),
                            Some('\\') => s.push('\\'),
                            Some('"') => s.push('"'),
                            Some(other) => {
                                return Err(self.err(&format!("unknown escape \\{other}")));
                            }
                            None => return Err(self.err("unterminated string")),
                        },
                        Some(c) => s.push(c),
                        None => return Err(self.err("unterminated string")),
                    }
                }
                tokens.push(Token {
                    kind: TokKind::Str(s),
                    line,
                    col,
                });
            } else if ch == '\'' {
                self.bump();
                let val = match self.bump() {
                    Some('\\') => match self.bump() {
                        Some('n') => '\n',
                        Some('r') => '\r',
                        Some('t') => '\t',
                        Some('\\') => '\\',
                        Some('\'') => '\'',
                        Some(other) => {
                            return Err(self.err(&format!("unknown char escape \\{other}")));
                        }
                        None => return Err(self.err("unterminated char")),
                    },
                    Some(c) => c,
                    None => return Err(self.err("unterminated char")),
                };
                if self.bump() != Some('\'') {
                    return Err(self.err("expected closing `'` in char literal"));
                }
                tokens.push(Token {
                    kind: TokKind::Char(val),
                    line,
                    col,
                });
            } else if ch.is_ascii_digit() {
                if r.starts_with("0x") || r.starts_with("0X") {
                    let start = self.pos;
                    self.bump();
                    self.bump();
                    while matches!(self.peek(), Some(c) if c.is_ascii_hexdigit()) {
                        self.bump();
                    }
                    tokens.push(Token {
                        kind: TokKind::Hex(self.src[start..self.pos].to_string()),
                        line,
                        col,
                    });
                } else {
                    let start = self.pos;
                    while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                        self.bump();
                    }
                    let n: u64 = self.src[start..self.pos]
                        .parse()
                        .map_err(|_| self.err("invalid integer"))?;
                    tokens.push(Token {
                        kind: TokKind::Int(n),
                        line,
                        col,
                    });
                }
            } else if is_id_start(ch) {
                let start = self.pos;
                self.bump();
                while matches!(self.peek(), Some(c) if is_id_cont(c)) {
                    self.bump();
                }
                tokens.push(Token {
                    kind: TokKind::Ident(self.src[start..self.pos].to_string()),
                    line,
                    col,
                });
            } else {
                return Err(self.err(&format!("unexpected character `{ch}`")));
            }
        }
    }

    fn lex_op_or_punct(&mut self, r: &str, line: usize, col: usize) -> Option<Token> {
        let multi: &[(&str, TokKind)] = &[
            ("<=>", TokKind::Iff),
            ("<-", TokKind::Bind),
            ("<=", TokKind::Le),
            (">=", TokKind::Ge),
            ("==", TokKind::EqEq),
            ("!=", TokKind::Ne),
            ("<>", TokKind::PropNe),
            ("++", TokKind::Append),
            ("::", TokKind::Cons),
            (":=", TokKind::Assign),
            (":-", TokKind::Turnstile),
            ("->", TokKind::Arrow),
            ("=>", TokKind::FatArrow),
            ("/\\", TokKind::LogicAnd),
            ("\\/", TokKind::LogicOr),
            ("&&", TokKind::BoolAnd),
            ("||", TokKind::BoolOr),
            ("..", TokKind::DotDot),
        ];
        for (sym, kind) in multi {
            if r.starts_with(sym) {
                self.pos += sym.len();
                self.col += sym.len();
                return Some(Token {
                    kind: kind.clone(),
                    line,
                    col,
                });
            }
        }
        let single = match r.as_bytes()[0] {
            b'{' => TokKind::LBrace,
            b'}' => TokKind::RBrace,
            b'(' => TokKind::LParen,
            b')' => TokKind::RParen,
            b'[' => TokKind::LBracket,
            b']' => TokKind::RBracket,
            b':' => TokKind::Colon,
            b';' => TokKind::Semi,
            b',' => TokKind::Comma,
            b'.' => TokKind::Dot,
            b'=' => TokKind::Eq,
            b'<' => TokKind::Lt,
            b'>' => TokKind::Gt,
            b'+' => TokKind::Plus,
            b'-' => TokKind::Minus,
            b'*' => TokKind::Star,
            b'/' => TokKind::Slash,
            b'%' => TokKind::Percent,
            b'^' => TokKind::Caret,
            b'!' => TokKind::Bang,
            b'|' => TokKind::Pipe,
            b'@' => TokKind::At,
            b'?' => TokKind::Quest,
            _ => return None,
        };
        self.bump();
        Some(Token {
            kind: single,
            line,
            col,
        })
    }
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }

    fn cur(&self) -> &Token {
        &self.toks[self.pos]
    }

    fn peek(&self) -> &TokKind {
        &self.cur().kind
    }

    fn peek_at(&self, off: usize) -> &TokKind {
        self.toks
            .get(self.pos + off)
            .map(|t| &t.kind)
            .unwrap_or(&TokKind::Eof)
    }

    fn err<T>(&self, msg: &str) -> Result<T, String> {
        let t = self.cur();
        Err(format!("line {}:{}: {msg} (found {:?})", t.line, t.col, t.kind))
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if !matches!(t.kind, TokKind::Eof) {
            self.pos += 1;
        }
        t
    }

    fn at_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), TokKind::Ident(s) if s == kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect_kw(&mut self, kw: &str) -> Result<(), String> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(&format!("expected `{kw}`"))
        }
    }

    fn expect(&mut self, want: &TokKind) -> Result<(), String> {
        if self.peek() == want {
            self.bump();
            Ok(())
        } else {
            self.err(&format!("expected {want:?}"))
        }
    }

    fn eat(&mut self, want: &TokKind) -> bool {
        if self.peek() == want {
            self.bump();
            true
        } else {
            false
        }
    }

    fn parse_ident(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Ident(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn parse_qname(&mut self) -> Result<String, String> {
        let mut s = self.parse_ident()?;
        while *self.peek() == TokKind::Dot {
            self.bump();
            s.push('.');
            s.push_str(&self.parse_ident()?);
        }
        Ok(s)
    }

    fn take_doc(&mut self) -> Option<String> {
        if let TokKind::Doc(d) = self.peek().clone() {
            self.bump();
            Some(d)
        } else {
            None
        }
    }

    fn parse_module(&mut self) -> Result<SpecModule, String> {
        self.expect_kw("spec_module")?;
        let target_module = self.parse_qname()?;
        let mut imports = Vec::new();
        while self.eat_kw("import") {
            imports.push(self.parse_qname()?);
        }
        let mut items = Vec::new();
        while *self.peek() != TokKind::Eof {
            items.push(self.parse_item()?);
        }
        Ok(SpecModule {
            target_module,
            imports,
            items,
        })
    }

    fn parse_block_items(&mut self) -> Result<Vec<MItem>, String> {
        self.expect(&TokKind::LBrace)?;
        let mut items = Vec::new();
        while *self.peek() != TokKind::RBrace {
            if *self.peek() == TokKind::Eof {
                return self.err("unclosed `{`");
            }
            items.push(self.parse_item()?);
        }
        self.bump();
        Ok(items)
    }

    fn parse_item(&mut self) -> Result<MItem, String> {
        if let TokKind::ModDoc(d) = self.peek().clone() {
            self.bump();
            return Ok(MItem::ModDoc(d));
        }
        let doc = self.take_doc();
        if doc.is_none() {
            if self.eat_kw("namespace") {
                let name = self.parse_qname()?;
                let items = self.parse_block_items()?;
                return Ok(MItem::Namespace { name, items });
            }
            if self.eat_kw("section") {
                let name = if *self.peek() == TokKind::LBrace {
                    None
                } else {
                    Some(self.parse_ident()?)
                };
                let items = self.parse_block_items()?;
                return Ok(MItem::Section { name, items });
            }
            if self.eat_kw("mutual") {
                let items = self.parse_block_items()?;
                return Ok(MItem::Mutual { items });
            }
            if self.eat_kw("open") {
                let mut ns = Vec::new();
                while let TokKind::Ident(_) = self.peek() {
                    if self.is_item_start() {
                        break;
                    }
                    ns.push(self.parse_qname()?);
                }
                return Ok(MItem::Open(ns));
            }
            if self.eat_kw("var") {
                let bs = self.parse_decl_binders()?;
                return Ok(MItem::Var(bs));
            }
        }
        if self.eat_kw("syntax") {
            return Ok(MItem::Syntax(self.parse_syntax(doc)?));
        }
        if self.eat_kw("relation") {
            return Ok(MItem::Relation(self.parse_relation(doc)?));
        }
        if self.eat_kw("laws") {
            return Ok(MItem::Laws(self.parse_laws(doc)?));
        }
        if self.eat_kw("inline") {
            self.expect_kw("def")?;
            return Ok(MItem::Def(self.parse_def(doc, true, false)?));
        }
        if self.eat_kw("def") {
            return Ok(MItem::Def(self.parse_def(doc, false, false)?));
        }
        self.err("expected specification item")
    }

    fn is_item_start(&self) -> bool {
        matches!(
            self.peek(),
            TokKind::Ident(s) if matches!(
                s.as_str(),
                "namespace" | "section" | "mutual" | "open" | "var" | "syntax" | "relation"
                    | "laws" | "inline" | "def"
            )
        ) || matches!(self.peek(), TokKind::Doc(_) | TokKind::ModDoc(_))
    }

    fn parse_decl_binders(&mut self) -> Result<Vec<MBinder>, String> {
        let mut bs = Vec::new();
        loop {
            match self.peek() {
                TokKind::LParen => {
                    self.bump();
                    let mut names = Vec::new();
                    while !matches!(self.peek(), TokKind::Colon | TokKind::RParen) {
                        names.push(self.parse_ident()?);
                    }
                    let ty = if self.eat(&TokKind::Colon) {
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    self.expect(&TokKind::RParen)?;
                    bs.push(MBinder::Explicit { names, ty });
                }
                TokKind::LBrace => {
                    let save = self.pos;
                    if *self.peek_at(1) == TokKind::RBrace || !matches!(self.peek_at(1), TokKind::Ident(_)) {
                        break;
                    }
                    self.bump();
                    let mut names = Vec::new();
                    let mut ok = true;
                    while !matches!(self.peek(), TokKind::Colon | TokKind::RBrace) {
                        if let TokKind::Ident(s) = self.peek().clone() {
                            self.bump();
                            names.push(s);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if !ok || names.is_empty() {
                        self.pos = save;
                        break;
                    }
                    let ty = if self.eat(&TokKind::Colon) {
                        match self.parse_expr() {
                            Ok(t) => Some(t),
                            Err(_) => {
                                self.pos = save;
                                break;
                            }
                        }
                    } else {
                        None
                    };
                    if !self.eat(&TokKind::RBrace) {
                        self.pos = save;
                        break;
                    }
                    bs.push(MBinder::Implicit { names, ty });
                }
                _ => break,
            }
        }
        Ok(bs)
    }

    fn parse_def_field_binders(&mut self) -> Result<Vec<MBinder>, String> {
        let mut bs = Vec::new();
        loop {
            match self.peek() {
                TokKind::LParen | TokKind::LBrace => {
                    let before = self.pos;
                    let mut more = self.parse_decl_binders()?;
                    if more.is_empty() {
                        self.pos = before;
                        break;
                    }
                    bs.append(&mut more);
                }
                TokKind::Ident(_) => {
                    bs.push(MBinder::Bare(self.parse_ident()?));
                }
                _ => break,
            }
        }
        Ok(bs)
    }

    fn parse_syntax(&mut self, doc: Option<String>) -> Result<MSyntax, String> {
        let name = self.parse_qname()?;
        let binders = self.parse_decl_binders()?;
        let body = if self.eat(&TokKind::Eq) {
            MSyntaxBody::Alias(self.parse_expr()?)
        } else if self.eat_kw("record") {
            self.expect(&TokKind::LBrace)?;
            let mut fields = Vec::new();
            while *self.peek() != TokKind::RBrace {
                let fdoc = self.take_doc();
                let fname = self.parse_ident()?;
                let fbs = self.parse_decl_binders()?;
                self.expect(&TokKind::Colon)?;
                let ty = self.parse_expr()?;
                let default = if self.eat(&TokKind::Assign) {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                self.expect(&TokKind::Semi)?;
                fields.push(MRecordField {
                    doc: fdoc,
                    name: fname,
                    binders: fbs,
                    ty,
                    default,
                });
            }
            self.bump();
            MSyntaxBody::Record(fields)
        } else {
            self.expect(&TokKind::LBrace)?;
            let mut cases = Vec::new();
            while *self.peek() != TokKind::RBrace {
                let cdoc = self.take_doc();
                self.expect(&TokKind::Pipe)?;
                let cname = self.parse_ident()?;
                let cbs = self.parse_decl_binders()?;
                cases.push(MVariantCase {
                    doc: cdoc,
                    name: cname,
                    binders: cbs,
                });
            }
            self.bump();
            MSyntaxBody::Variant(cases)
        };
        let deriving = if self.eat_kw("deriving") {
            self.expect(&TokKind::LBracket)?;
            let mut ds = Vec::new();
            while *self.peek() != TokKind::RBracket {
                ds.push(self.parse_qname()?);
                if !self.eat(&TokKind::Comma) {
                    break;
                }
            }
            self.expect(&TokKind::RBracket)?;
            ds
        } else {
            Vec::new()
        };
        let default_inhabited = if self.eat_kw("inhabited") {
            let ty = self.parse_expr()?;
            self.expect(&TokKind::Assign)?;
            let val = self.parse_expr()?;
            Some((ty, val))
        } else {
            None
        };
        Ok(MSyntax {
            doc,
            name,
            binders,
            body,
            deriving,
            default_inhabited,
        })
    }

    fn parse_relation(&mut self, doc: Option<String>) -> Result<MRel, String> {
        let name = self.parse_qname()?;
        let binders = self.parse_decl_binders()?;
        self.expect(&TokKind::Colon)?;
        let sig = self.parse_expr()?;
        self.expect(&TokKind::LBrace)?;
        let mut rules = Vec::new();
        while *self.peek() != TokKind::RBrace {
            let rdoc = self.take_doc();
            self.expect_kw("rule")?;
            let rname = self.parse_ident()?;
            let rbs = self.parse_decl_binders()?;
            self.expect(&TokKind::Colon)?;
            let conclusion = self.parse_expr()?;
            let mut premises = Vec::new();
            if self.eat(&TokKind::Turnstile) {
                loop {
                    premises.push(self.parse_expr()?);
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
            }
            self.expect(&TokKind::Semi)?;
            rules.push(MRelRule {
                doc: rdoc,
                name: rname,
                binders: rbs,
                conclusion,
                premises,
            });
        }
        self.bump();
        Ok(MRel {
            doc,
            name,
            binders,
            sig,
            rules,
        })
    }

    fn parse_laws(&mut self, doc: Option<String>) -> Result<MLaws, String> {
        let name = self.parse_qname()?;
        let binders = self.parse_decl_binders()?;
        let mut extends = Vec::new();
        if self.eat_kw("extends") {
            self.expect(&TokKind::LBracket)?;
            while *self.peek() != TokKind::RBracket {
                extends.push(self.parse_expr()?);
                if !self.eat(&TokKind::Comma) {
                    break;
                }
            }
            self.expect(&TokKind::RBracket)?;
        }
        self.expect(&TokKind::LBrace)?;
        let mut laws = Vec::new();
        while *self.peek() != TokKind::RBrace {
            let ldoc = self.take_doc();
            self.expect_kw("law")?;
            let lname = self.parse_ident()?;
            self.expect(&TokKind::Colon)?;
            let prop = self.parse_expr()?;
            self.expect(&TokKind::Semi)?;
            laws.push(MLaw {
                doc: ldoc,
                name: lname,
                prop,
            });
        }
        self.bump();
        Ok(MLaws {
            doc,
            name,
            binders,
            extends,
            laws,
        })
    }

    fn parse_def(&mut self, doc: Option<String>, inline: bool, is_where: bool) -> Result<MDef, String> {
        let name = self.parse_qname()?;
        let binders = self.parse_decl_binders()?;
        let ty = if self.eat(&TokKind::Colon) {
            Some(self.parse_expr()?)
        } else {
            None
        };
        let body = if self.eat(&TokKind::Assign) {
            MDefBody::Expr(self.parse_expr()?)
        } else if *self.peek() == TokKind::LBrace {
            self.bump();
            let mut fields = Vec::new();
            while *self.peek() != TokKind::RBrace {
                let fname = self.parse_ident()?;
                let fbs = self.parse_def_field_binders()?;
                if self.eat(&TokKind::Assign) {
                    let val = self.parse_expr()?;
                    self.expect(&TokKind::Semi)?;
                    fields.push(MStructDefField::Val {
                        name: fname,
                        binders: fbs,
                        val,
                    });
                } else {
                    if !fbs.is_empty() {
                        return self.err("unexpected binders before clause match");
                    }
                    let mut arms = Vec::new();
                    while *self.peek() == TokKind::Pipe {
                        arms.push(self.parse_arm()?);
                    }
                    self.expect_kw("end")?;
                    self.expect(&TokKind::Semi)?;
                    fields.push(MStructDefField::Clauses { name: fname, arms });
                }
            }
            self.bump();
            MDefBody::Struct(fields)
        } else if *self.peek() == TokKind::Pipe {
            let mut arms = Vec::new();
            while *self.peek() == TokKind::Pipe {
                arms.push(self.parse_arm()?);
            }
            self.expect_kw("end")?;
            MDefBody::Clauses(arms)
        } else {
            return self.err("expected `:=`, `{`, or `|` in def body");
        };

        let where_defs = if !is_where && self.eat_kw("where") {
            self.expect(&TokKind::LBrace)?;
            let mut wds = Vec::new();
            while *self.peek() != TokKind::RBrace {
                let wdoc = self.take_doc();
                wds.push(self.parse_def(wdoc, false, true)?);
            }
            self.bump();
            wds
        } else {
            Vec::new()
        };

        Ok(MDef {
            doc,
            inline,
            name,
            binders,
            ty,
            body,
            where_defs,
        })
    }

    fn parse_arm(&mut self) -> Result<MMatchArm, String> {
        self.expect(&TokKind::Pipe)?;
        let mut alts = Vec::new();
        loop {
            let mut row = Vec::new();
            loop {
                row.push(self.parse_pat(false)?);
                if !self.eat(&TokKind::Comma) {
                    break;
                }
            }
            alts.push(row);
            if !self.eat(&TokKind::Pipe) {
                break;
            }
        }
        self.expect(&TokKind::FatArrow)?;
        let rhs = self.parse_expr()?;
        Ok(MMatchArm { alts, rhs })
    }

    fn parse_pat(&mut self, allow_or: bool) -> Result<MPat, String> {
        let mut lhs = self.parse_pat_cons()?;
        if allow_or && *self.peek() == TokKind::Pipe {
            let mut ps = vec![lhs];
            while self.eat(&TokKind::Pipe) {
                ps.push(self.parse_pat_cons()?);
            }
            lhs = MPat::Or(ps);
        }
        Ok(lhs)
    }

    fn parse_pat_cons(&mut self) -> Result<MPat, String> {
        let mut h = self.parse_pat_add()?;
        if self.eat(&TokKind::Cons) {
            let t = self.parse_pat_cons()?;
            h = MPat::Cons(Box::new(h), Box::new(t));
        }
        Ok(h)
    }

    fn parse_pat_add(&mut self) -> Result<MPat, String> {
        let p = self.parse_pat_atom()?;
        if *self.peek() == TokKind::Plus {
            if let MPat::Var(v) = &p {
                if let TokKind::Int(n) = *self.peek_at(1) {
                    let v = v.clone();
                    self.bump();
                    self.bump();
                    return Ok(MPat::AddNat(v, n));
                }
            }
        }
        Ok(p)
    }

    fn parse_pat_atom(&mut self) -> Result<MPat, String> {
        match self.peek().clone() {
            TokKind::Ident(s) if s == "_" => {
                self.bump();
                Ok(MPat::Wild)
            }
            TokKind::DotDot => {
                self.bump();
                Ok(MPat::Dots)
            }
            TokKind::Int(n) => {
                self.bump();
                Ok(MPat::Lit(MLit::Int(n)))
            }
            TokKind::Hex(h) => {
                self.bump();
                Ok(MPat::Lit(MLit::Hex(h)))
            }
            TokKind::Str(s) => {
                self.bump();
                Ok(MPat::Lit(MLit::Str(s)))
            }
            TokKind::Char(c) => {
                self.bump();
                Ok(MPat::Lit(MLit::Char(c)))
            }
            TokKind::Ident(s) if s == "true" => {
                self.bump();
                Ok(MPat::Lit(MLit::Bool(true)))
            }
            TokKind::Ident(s) if s == "false" => {
                self.bump();
                Ok(MPat::Lit(MLit::Bool(false)))
            }
            TokKind::Dot => {
                self.bump();
                let tag = self.parse_ident()?;
                let args = self.parse_pat_args()?;
                Ok(MPat::Tag(tag, args))
            }
            TokKind::LParen => {
                self.bump();
                if self.eat(&TokKind::RParen) {
                    return Ok(MPat::Lit(MLit::Unit));
                }
                let first = self.parse_pat(true)?;
                if self.eat(&TokKind::Comma) {
                    let mut ps = vec![first];
                    while *self.peek() != TokKind::RParen {
                        ps.push(self.parse_pat(true)?);
                        if !self.eat(&TokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokKind::RParen)?;
                    Ok(MPat::Tuple(ps))
                } else {
                    self.expect(&TokKind::RParen)?;
                    Ok(first)
                }
            }
            TokKind::LBracket => {
                self.bump();
                let mut ps = Vec::new();
                while *self.peek() != TokKind::RBracket {
                    ps.push(self.parse_pat(true)?);
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokKind::RBracket)?;
                Ok(MPat::List(ps))
            }
            TokKind::Ident(s) if s == "ctor" && *self.peek_at(1) == TokKind::LParen => {
                self.bump();
                self.bump();
                let mut ps = Vec::new();
                while *self.peek() != TokKind::RParen {
                    ps.push(self.parse_pat(true)?);
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokKind::RParen)?;
                Ok(MPat::AnonCtor(ps))
            }
            TokKind::Ident(_) => {
                let first = self.parse_ident()?;
                if self.eat(&TokKind::At) {
                    self.expect(&TokKind::LParen)?;
                    let inner = self.parse_pat(true)?;
                    self.expect(&TokKind::RParen)?;
                    return Ok(MPat::As(first, Box::new(inner)));
                }
                let mut name = first;
                let mut dotted = false;
                while *self.peek() == TokKind::Dot {
                    self.bump();
                    name.push('.');
                    name.push_str(&self.parse_ident()?);
                    dotted = true;
                }
                if *self.peek() == TokKind::LParen && !self.peek_paren_has_top_colon() {
                    let args = self.parse_pat_args()?;
                    Ok(MPat::Ctor(name, args))
                } else if dotted {
                    Ok(MPat::Ctor(name, Vec::new()))
                } else {
                    Ok(MPat::Var(name))
                }
            }
            _ => self.err("expected pattern"),
        }
    }

    fn peek_paren_has_top_colon(&self) -> bool {
        if *self.peek() != TokKind::LParen {
            return false;
        }
        let mut depth = 0usize;
        let mut i = self.pos;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokKind::LParen | TokKind::LBracket | TokKind::LBrace => depth += 1,
                TokKind::RParen | TokKind::RBracket | TokKind::RBrace => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return false;
                    }
                }
                TokKind::Colon if depth == 1 => return true,
                TokKind::Eof => return false,
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn parse_pat_args(&mut self) -> Result<Vec<MPat>, String> {
        if *self.peek() != TokKind::LParen {
            return Ok(Vec::new());
        }
        self.bump();
        let mut args = Vec::new();
        while *self.peek() != TokKind::RParen {
            args.push(self.parse_pat(true)?);
            if !self.eat(&TokKind::Comma) {
                break;
            }
        }
        self.expect(&TokKind::RParen)?;
        Ok(args)
    }

    pub fn parse_expr(&mut self) -> Result<MExpr, String> {
        self.parse_expr_prec(0)
    }

    fn parse_expr_prec(&mut self, min_prec: u8) -> Result<MExpr, String> {
        let mut lhs = self.parse_prefix_or_atom()?;
        loop {
            if self.at_kw("matches") && 50 > min_prec {
                self.bump();
                let pat = self.parse_pat(false)?;
                lhs = MExpr::Matches(Box::new(lhs), pat);
                continue;
            }
            if *self.peek() == TokKind::Arrow && 25 >= min_prec {
                self.bump();
                let cod = self.parse_expr_prec(25)?;
                lhs = MExpr::Arrow {
                    binder: None,
                    dom: Some(Box::new(lhs)),
                    cod: Box::new(cod),
                };
                continue;
            }
            let Some((op, prec, right)) = self.peek_binop() else {
                break;
            };
            if prec < min_prec {
                break;
            }
            self.bump();
            let next_min = if right { prec } else { prec + 1 };
            let rhs = if matches!(op, MBinOp::Eq | MBinOp::Ne | MBinOp::And | MBinOp::Or | MBinOp::Iff) {
                self.parse_expr_prec(next_min.min(next_min))?
            } else {
                self.parse_expr_prec(next_min)?
            };
            lhs = MExpr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn peek_binop(&self) -> Option<(MBinOp, u8, bool)> {
        let res = match self.peek() {
            TokKind::Caret => (MBinOp::Pow, 80, true),
            TokKind::Star => (MBinOp::Mul, 70, false),
            TokKind::Slash => (MBinOp::Div, 70, false),
            TokKind::Percent => (MBinOp::Mod, 70, false),
            TokKind::Cons => (MBinOp::Cons, 67, true),
            TokKind::Plus => (MBinOp::Add, 65, false),
            TokKind::Minus => (MBinOp::Sub, 65, false),
            TokKind::Append => (MBinOp::Append, 65, false),
            TokKind::EqEq => (MBinOp::BoolEq, 50, false),
            TokKind::Ne => (MBinOp::BoolNe, 50, false),
            TokKind::Lt => (MBinOp::Lt, 50, false),
            TokKind::Le => (MBinOp::Le, 50, false),
            TokKind::Gt => (MBinOp::Gt, 50, false),
            TokKind::Ge => (MBinOp::Ge, 50, false),
            TokKind::Eq => (MBinOp::Eq, 50, false),
            TokKind::PropNe => (MBinOp::Ne, 50, false),
            TokKind::Ident(s) if s == "mem" => (MBinOp::In, 50, false),
            TokKind::Ident(s) if s == "notmem" => (MBinOp::NotIn, 50, false),
            TokKind::BoolAnd => (MBinOp::BoolAnd, 35, false),
            TokKind::LogicAnd => (MBinOp::And, 35, true),
            TokKind::Ident(s) if s == "times" => (MBinOp::Times, 35, true),
            TokKind::BoolOr => (MBinOp::BoolOr, 30, false),
            TokKind::LogicOr => (MBinOp::Or, 30, true),
            TokKind::Ident(s) if s == "sum" => (MBinOp::Sum, 30, true),
            TokKind::Iff => (MBinOp::Iff, 20, false),
            _ => return None,
        };
        Some(res)
    }

    fn parse_prefix_or_atom(&mut self) -> Result<MExpr, String> {
        match self.peek() {
            TokKind::Ident(s) if s == "forall" => return self.parse_quant(MQuant::Forall),
            TokKind::Ident(s) if s == "exists" => return self.parse_quant(MQuant::Exists),
            TokKind::Ident(s) if s == "fun" => return self.parse_fun(),
            TokKind::Ident(s) if s == "let" => return self.parse_let(),
            TokKind::Ident(s) if s == "if" => return self.parse_if(),
            TokKind::Ident(s) if s == "match" => return self.parse_match(),
            TokKind::Ident(s) if s == "do" => return self.parse_do(),
            TokKind::Ident(s) if s == "not" => {
                self.bump();
                if self.at_kw("forall") || self.at_kw("exists") {
                    let q = self.parse_prefix_or_atom()?;
                    return Ok(MExpr::UnOp(MUnOp::PropNot, Box::new(q)));
                }
                let e = self.parse_expr_prec(41)?;
                return Ok(MExpr::UnOp(MUnOp::PropNot, Box::new(e)));
            }
            TokKind::Minus => {
                self.bump();
                let e = self.parse_expr_prec(76)?;
                return Ok(MExpr::UnOp(MUnOp::Neg, Box::new(e)));
            }
            TokKind::Bang => {
                self.bump();
                let e = self.parse_expr_prec(76)?;
                return Ok(MExpr::UnOp(MUnOp::BoolNot, Box::new(e)));
            }
            TokKind::Bind => {
                self.bump();
                let e = self.parse_expr_prec(76)?;
                return Ok(MExpr::UnOp(MUnOp::Bind, Box::new(e)));
            }
            _ => {}
        }

        // Dependent arrow binder: `{α : Type} -> ...` or `(x : T) -> ...`
        if let Some(arrow) = self.try_parse_binder_arrow()? {
            return Ok(arrow);
        }

        let mut e = self.parse_atom()?;
        loop {
            match self.peek() {
                TokKind::Dot => {
                    self.bump();
                    let field = match self.peek().clone() {
                        TokKind::Ident(s) => {
                            self.bump();
                            s
                        }
                        TokKind::Int(n) => {
                            self.bump();
                            n.to_string()
                        }
                        _ => return self.err("expected field name or tuple index after `.`"),
                    };
                    e = MExpr::Proj(Box::new(e), field);
                }
                TokKind::LParen => {
                    self.bump();
                    let mut args = Vec::new();
                    while *self.peek() != TokKind::RParen {
                        if let TokKind::Ident(k) = self.peek().clone() {
                            if *self.peek_at(1) == TokKind::Assign {
                                self.bump();
                                self.bump();
                                args.push(MArg::Named(k, self.parse_expr()?));
                                if !self.eat(&TokKind::Comma) {
                                    break;
                                }
                                continue;
                            }
                        }
                        args.push(MArg::Pos(self.parse_expr()?));
                        if !self.eat(&TokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokKind::RParen)?;
                    e = MExpr::Call(Box::new(e), args);
                }
                TokKind::LBracket => {
                    self.bump();
                    let idx = self.parse_expr()?;
                    self.expect(&TokKind::RBracket)?;
                    if self.eat(&TokKind::Quest) {
                        e = MExpr::IndexOpt(Box::new(e), Box::new(idx));
                    } else {
                        e = MExpr::Index(Box::new(e), Box::new(idx));
                    }
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn try_parse_binder_arrow(&mut self) -> Result<Option<MExpr>, String> {
        let save = self.pos;
        if *self.peek() == TokKind::LBrace {
            if matches!(self.peek_at(1), TokKind::Ident(_)) {
                // Distinguish struct literal `{ a := ... }` / `{ a with ... }` / `{ a, ... }`
                if !matches!(self.peek_at(2), TokKind::Assign)
                    && !matches!(self.peek_at(2), TokKind::Ident(s) if s == "with")
                {
                    self.bump();
                    let mut names = Vec::new();
                    let mut ok = true;
                    while !matches!(self.peek(), TokKind::Colon | TokKind::RBrace) {
                        if let TokKind::Ident(s) = self.peek().clone() {
                            self.bump();
                            names.push(s);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if ok && !names.is_empty() {
                        let ty = if self.eat(&TokKind::Colon) {
                            self.parse_expr().ok()
                        } else {
                            None
                        };
                        if self.eat(&TokKind::RBrace) && self.eat(&TokKind::Arrow) {
                            let cod = self.parse_expr_prec(25)?;
                            return Ok(Some(MExpr::Arrow {
                                binder: Some(Box::new(MBinder::Implicit { names, ty })),
                                dom: None,
                                cod: Box::new(cod),
                            }));
                        }
                    }
                }
            }
            self.pos = save;
        } else if *self.peek() == TokKind::LParen {
            self.bump();
            let mut names = Vec::new();
            while let TokKind::Ident(s) = self.peek().clone() {
                self.bump();
                names.push(s);
            }
            if !names.is_empty() && self.eat(&TokKind::Colon) {
                if let Ok(ty) = self.parse_expr() {
                    if self.eat(&TokKind::RParen) && self.eat(&TokKind::Arrow) {
                        let cod = self.parse_expr_prec(25)?;
                        return Ok(Some(MExpr::Arrow {
                            binder: Some(Box::new(MBinder::Explicit {
                                names,
                                ty: Some(ty),
                            })),
                            dom: None,
                            cod: Box::new(cod),
                        }));
                    }
                }
            }
            self.pos = save;
        }
        Ok(None)
    }

    fn parse_atom(&mut self) -> Result<MExpr, String> {
        match self.peek().clone() {
            TokKind::Int(n) => {
                self.bump();
                Ok(MExpr::Lit(MLit::Int(n)))
            }
            TokKind::Hex(h) => {
                self.bump();
                Ok(MExpr::Lit(MLit::Hex(h)))
            }
            TokKind::Str(s) => {
                self.bump();
                Ok(MExpr::Lit(MLit::Str(s)))
            }
            TokKind::Char(c) => {
                self.bump();
                Ok(MExpr::Lit(MLit::Char(c)))
            }
            TokKind::Ident(s) if s == "true" => {
                self.bump();
                Ok(MExpr::Lit(MLit::Bool(true)))
            }
            TokKind::Ident(s) if s == "false" => {
                self.bump();
                Ok(MExpr::Lit(MLit::Bool(false)))
            }
            TokKind::Dot => {
                self.bump();
                let t = self.parse_ident()?;
                Ok(MExpr::Tag(t))
            }
            TokKind::Ident(s) if s == "ctor" && *self.peek_at(1) == TokKind::LParen => {
                self.bump();
                self.bump();
                let mut xs = Vec::new();
                while *self.peek() != TokKind::RParen {
                    xs.push(self.parse_expr()?);
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokKind::RParen)?;
                Ok(MExpr::AnonCtor(xs))
            }
            TokKind::Ident(s) => {
                self.bump();
                Ok(MExpr::Ident(s))
            }
            TokKind::LParen => {
                self.bump();
                if self.eat(&TokKind::RParen) {
                    return Ok(MExpr::Lit(MLit::Unit));
                }
                let first = self.parse_expr()?;
                if self.eat(&TokKind::Colon) {
                    let ty = self.parse_expr()?;
                    self.expect(&TokKind::RParen)?;
                    return Ok(MExpr::Ascribe(Box::new(first), Box::new(ty)));
                }
                if self.eat(&TokKind::Comma) {
                    let mut xs = vec![first];
                    while *self.peek() != TokKind::RParen {
                        xs.push(self.parse_expr()?);
                        if !self.eat(&TokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokKind::RParen)?;
                    Ok(MExpr::Tuple(xs))
                } else {
                    self.expect(&TokKind::RParen)?;
                    Ok(first)
                }
            }
            TokKind::LBracket => {
                self.bump();
                let mut xs = Vec::new();
                while *self.peek() != TokKind::RBracket {
                    xs.push(self.parse_expr()?);
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokKind::RBracket)?;
                Ok(MExpr::List(xs))
            }
            TokKind::LBrace => {
                self.bump();
                if self.eat(&TokKind::RBrace) {
                    return Ok(MExpr::StructLit {
                        base: None,
                        fields: Vec::new(),
                    });
                }
                let mut base = None;
                // Check for `<expr> with ...`
                let save = self.pos;
                if let Ok(b) = self.parse_expr() {
                    if self.eat_kw("with") {
                        base = Some(Box::new(b));
                    } else {
                        self.pos = save;
                    }
                } else {
                    self.pos = save;
                }
                let mut fields = Vec::new();
                while *self.peek() != TokKind::RBrace {
                    let fname = self.parse_ident()?;
                    let val = if self.eat(&TokKind::Assign) {
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    fields.push((fname, val));
                    if !self.eat(&TokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokKind::RBrace)?;
                Ok(MExpr::StructLit { base, fields })
            }
            _ => self.err("expected expression"),
        }
    }

    fn parse_quant(&mut self, q: MQuant) -> Result<MExpr, String> {
        self.bump();
        let mut bs = Vec::new();
        while *self.peek() != TokKind::Comma {
            match self.peek() {
                TokKind::LParen | TokKind::LBrace => {
                    bs.extend(self.parse_decl_binders()?);
                }
                TokKind::Ident(_) => {
                    let name = self.parse_ident()?;
                    if self.eat_kw("mem") {
                        let coll = self.parse_expr_prec(51)?;
                        bs.push(MBinder::In { name, coll });
                    } else if self.eat(&TokKind::Lt) {
                        let bound = self.parse_expr_prec(51)?;
                        bs.push(MBinder::Rel {
                            name,
                            op: MRelBoundOp::Lt,
                            bound,
                        });
                    } else if self.eat(&TokKind::Le) {
                        let bound = self.parse_expr_prec(51)?;
                        bs.push(MBinder::Rel {
                            name,
                            op: MRelBoundOp::Le,
                            bound,
                        });
                    } else {
                        bs.push(MBinder::Bare(name));
                    }
                }
                _ => return self.err("expected quantifier binder or `,`"),
            }
        }
        self.expect(&TokKind::Comma)?;
        let body = self.parse_expr()?;
        Ok(MExpr::Quant(q, bs, Box::new(body)))
    }

    fn parse_fun(&mut self) -> Result<MExpr, String> {
        self.bump();
        if *self.peek() == TokKind::Pipe {
            let mut arms = Vec::new();
            while *self.peek() == TokKind::Pipe {
                arms.push(self.parse_arm()?);
            }
            self.expect_kw("end")?;
            return Ok(MExpr::FunCases(arms));
        }
        let mut ps = Vec::new();
        while *self.peek() != TokKind::FatArrow {
            if *self.peek() == TokKind::LBrace {
                let bs = self.parse_decl_binders()?;
                for b in bs {
                    if let MBinder::Implicit { names, ty } = b {
                        ps.push(MFunParam::Implicit { names, ty });
                    }
                }
                continue;
            }
            if *self.peek() == TokKind::LParen {
                let save = self.pos;
                self.bump();
                let mut names = Vec::new();
                while let TokKind::Ident(s) = self.peek().clone() {
                    self.bump();
                    names.push(s);
                }
                if !names.is_empty() && self.eat(&TokKind::Colon) {
                    let ty = self.parse_expr()?;
                    self.expect(&TokKind::RParen)?;
                    ps.push(MFunParam::Explicit { names, ty });
                    continue;
                }
                self.pos = save;
            }
            ps.push(MFunParam::Pat(self.parse_pat(true)?));
        }
        self.expect(&TokKind::FatArrow)?;
        let body = self.parse_expr()?;
        Ok(MExpr::Fun(ps, Box::new(body)))
    }

    fn parse_let(&mut self) -> Result<MExpr, String> {
        self.bump();
        let pat = self.parse_pat(false)?;
        let binders = self.parse_decl_binders()?;
        let ty = if self.eat(&TokKind::Colon) {
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };
        self.expect(&TokKind::Assign)?;
        let val = Box::new(self.parse_expr()?);
        self.expect_kw("in")?;
        let body = Box::new(self.parse_expr()?);
        Ok(MExpr::Let {
            pat,
            binders,
            ty,
            val,
            body,
        })
    }

    fn parse_if(&mut self) -> Result<MExpr, String> {
        self.bump();
        let c = self.parse_expr()?;
        self.expect_kw("then")?;
        let t = self.parse_expr()?;
        self.expect_kw("else")?;
        let f = self.parse_expr()?;
        Ok(MExpr::If(Box::new(c), Box::new(t), Box::new(f)))
    }

    fn parse_match(&mut self) -> Result<MExpr, String> {
        self.bump();
        let mut scrs = Vec::new();
        loop {
            scrs.push(self.parse_expr()?);
            if !self.eat(&TokKind::Comma) {
                break;
            }
        }
        self.expect_kw("with")?;
        let mut arms = Vec::new();
        while *self.peek() == TokKind::Pipe {
            arms.push(self.parse_arm()?);
        }
        self.expect_kw("end")?;
        Ok(MExpr::Match(scrs, arms))
    }

    fn parse_do(&mut self) -> Result<MExpr, String> {
        self.bump();
        let stmts = self.parse_do_block()?;
        Ok(MExpr::Do(stmts))
    }

    fn parse_do_block(&mut self) -> Result<Vec<MDoStmt>, String> {
        self.expect(&TokKind::LBrace)?;
        let mut stmts = Vec::new();
        while *self.peek() != TokKind::RBrace {
            stmts.push(self.parse_do_stmt()?);
        }
        self.bump();
        Ok(stmts)
    }

    fn parse_do_stmt(&mut self) -> Result<MDoStmt, String> {
        if self.eat_kw("let") {
            let pat = self.parse_pat(false)?;
            let ty = if self.eat(&TokKind::Colon) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            if self.eat(&TokKind::Bind) {
                let val = self.parse_expr()?;
                self.expect(&TokKind::Semi)?;
                return Ok(MDoStmt::LetBind { pat, ty, val });
            } else {
                self.expect(&TokKind::Assign)?;
                let val = self.parse_expr()?;
                self.expect(&TokKind::Semi)?;
                return Ok(MDoStmt::LetPure { pat, ty, val });
            }
        }
        if self.eat_kw("return") {
            let e = self.parse_expr()?;
            self.expect(&TokKind::Semi)?;
            return Ok(MDoStmt::Return(e));
        }
        if self.eat_kw("if") {
            let cond = self.parse_expr()?;
            self.expect_kw("then")?;
            let then_branch = self.parse_do_block()?;
            let else_branch = if self.eat_kw("else") {
                Some(self.parse_do_block()?)
            } else {
                None
            };
            self.expect(&TokKind::Semi)?;
            return Ok(MDoStmt::If {
                cond,
                then_branch,
                else_branch,
            });
        }
        let e = self.parse_expr()?;
        self.expect(&TokKind::Semi)?;
        Ok(MDoStmt::Expr(e))
    }
}

pub fn starts_with_spec_module(rel_path: &str, src: &str) -> bool {
    if rel_path.starts_with("prose/") {
        return true;
    }
    for line in src.lines() {
        let s = line.trim();
        if s.is_empty() || s.starts_with("--") {
            continue;
        }
        return s.starts_with("spec_module ") || s == "spec_module";
    }
    false
}

pub fn parse_spec_file(rel_path: &str, src: &str) -> Result<SpecFile, String> {
    let (header_comment, toks) = Lexer::new(src)
        .lex_all()
        .map_err(|e| format!("{rel_path}: {e}"))?;
    let mut p = Parser::new(toks);
    let m = p.parse_module().map_err(|e| format!("{rel_path}: {e}"))?;
    Ok(SpecFile {
        rel_path: rel_path.to_string(),
        header_comment,
        grammar_decl: None,
        items: vec![TopItem::SpecModule(m)],
    })
}
