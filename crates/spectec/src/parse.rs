//! Recursive-descent parser for ECMA-262 SpecTec `.spectec` files.

use crate::ast::*;
use crate::lexer::{lex, TokKind, Token};

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }

    fn cur(&self) -> &Token {
        &self.toks[self.pos]
    }

    fn peek(&self) -> &TokKind {
        &self.cur().kind
    }

    fn peek_at(&self, offset: usize) -> &TokKind {
        self.toks
            .get(self.pos + offset)
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
        matches!(self.peek(), TokKind::Ident { name, quoted: false } if name == kw)
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
            self.err(&format!("expected keyword `{kw}`"))
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

    fn parse_ident(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Ident { name, .. } => {
                self.bump();
                Ok(name)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn parse_str(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Str(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.err("expected string literal"),
        }
    }

    fn parse_int(&mut self) -> Result<u64, String> {
        match self.peek().clone() {
            TokKind::Int(n) => {
                self.bump();
                Ok(n)
            }
            _ => self.err("expected integer"),
        }
    }

    fn parse_usize(&mut self) -> Result<usize, String> {
        Ok(self.parse_int()? as usize)
    }

    fn parse_bool(&mut self) -> Result<bool, String> {
        if self.eat_kw("true") {
            Ok(true)
        } else if self.eat_kw("false") {
            Ok(false)
        } else {
            self.err("expected boolean")
        }
    }

    fn parse_field(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Field(f) => {
                self.bump();
                Ok(f)
            }
            _ => self.err("expected field token [[...]]"),
        }
    }

    fn parse_enum(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Enum(e) => {
                self.bump();
                Ok(e)
            }
            _ => self.err("expected enum token ~...~"),
        }
    }

    fn parse_prim(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Prim(p) => {
                self.bump();
                Ok(p)
            }
            _ => self.err("expected primitive token $..."),
        }
    }

    fn parse_clause(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Clause(c) => {
                self.bump();
                Ok(c)
            }
            _ => self.err("expected clause token @..."),
        }
    }

    fn parse_alg_ref(&mut self) -> Result<AlgRef, String> {
        let clause = self.parse_clause()?;
        let idx = match self.peek().clone() {
            TokKind::HashIdx(i) => {
                self.bump();
                i
            }
            _ => 0,
        };
        Ok(AlgRef { clause, idx })
    }

    fn parse_prod(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Prod(p) => {
                self.bump();
                Ok(p)
            }
            _ => self.err("expected prod token p\"...\""),
        }
    }

    fn parse_table_tok(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            TokKind::Table(t) => {
                self.bump();
                Ok(t)
            }
            _ => self.err("expected table token t\"...\""),
        }
    }

    fn parse_comma_list<T>(&mut self, mut item: impl FnMut(&mut Self) -> Result<T, String>) -> Result<Vec<T>, String> {
        self.expect(&TokKind::LBracket)?;
        let mut out = Vec::new();
        if self.peek() == &TokKind::RBracket {
            self.bump();
            return Ok(out);
        }
        loop {
            out.push(item(self)?);
            if self.peek() == &TokKind::Comma {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(&TokKind::RBracket)?;
        Ok(out)
    }

    fn parse_paren_args(&mut self) -> Result<Vec<Expr>, String> {
        self.expect(&TokKind::LParen)?;
        let mut out = Vec::new();
        if self.peek() == &TokKind::RParen {
            self.bump();
            return Ok(out);
        }
        loop {
            out.push(self.parse_expr()?);
            if self.peek() == &TokKind::Comma {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(&TokKind::RParen)?;
        Ok(out)
    }

    // --- Literals ---

    fn parse_sign(&mut self) -> Sign {
        if matches!(self.peek(), TokKind::Plus) {
            self.bump();
            Sign::Plus
        } else if matches!(self.peek(), TokKind::Minus) {
            self.bump();
            Sign::Minus
        } else {
            Sign::None
        }
    }

    fn parse_numeral(&mut self) -> Result<Numeral, String> {
        if self.eat_kw("hex") {
            self.expect(&TokKind::LParen)?;
            let n = self.parse_int()?;
            self.expect(&TokKind::Comma)?;
            let d = self.parse_str()?;
            self.expect(&TokKind::RParen)?;
            Ok(Numeral::Hex(n, d))
        } else if self.eat_kw("frac") {
            self.expect(&TokKind::LParen)?;
            let w = self.parse_int()?;
            self.expect(&TokKind::Comma)?;
            let f = self.parse_int()?;
            self.expect(&TokKind::Comma)?;
            let p = self.parse_int()? as u32;
            self.expect(&TokKind::RParen)?;
            Ok(Numeral::Frac(w, f, p))
        } else {
            Ok(Numeral::Dec(self.parse_int()?))
        }
    }

    fn parse_mag(&mut self) -> Result<Mag, String> {
        if matches!(self.peek(), TokKind::Inf) {
            self.bump();
            Ok(Mag::Inf)
        } else {
            Ok(Mag::Num(self.parse_numeral()?))
        }
    }

    // --- Expressions ---

    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_add()
    }

    fn parse_add(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_mul()?;
        loop {
            let op = if matches!(self.peek(), TokKind::Plus) {
                BinOp::Add
            } else if matches!(self.peek(), TokKind::Minus) {
                BinOp::Sub
            } else if self.at_kw("plus") {
                BinOp::Plus
            } else {
                break;
            };
            self.bump();
            let rhs = self.parse_mul()?;
            e = Expr::Bin(op, Box::new(e), Box::new(rhs));
        }
        Ok(e)
    }

    fn parse_mul(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_pow()?;
        loop {
            let op = if matches!(self.peek(), TokKind::Star) {
                BinOp::Mul
            } else if matches!(self.peek(), TokKind::Slash) {
                BinOp::Div
            } else if self.at_kw("modulo") {
                BinOp::Modulo
            } else if self.at_kw("times") {
                BinOp::Times
            } else {
                break;
            };
            self.bump();
            let rhs = self.parse_pow()?;
            e = Expr::Bin(op, Box::new(e), Box::new(rhs));
        }
        Ok(e)
    }

    fn parse_pow(&mut self) -> Result<Expr, String> {
        let e = self.parse_unary()?;
        if matches!(self.peek(), TokKind::Caret) {
            self.bump();
            let rhs = self.parse_pow()?;
            Ok(Expr::Bin(BinOp::Pow, Box::new(e), Box::new(rhs)))
        } else {
            Ok(e)
        }
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        if matches!(self.peek(), TokKind::Quest) {
            self.bump();
            Ok(Expr::Q(Box::new(self.parse_unary()?)))
        } else if matches!(self.peek(), TokKind::Bang) {
            self.bump();
            Ok(Expr::Bang(Box::new(self.parse_unary()?)))
        } else if self.eat_kw("neg") {
            Ok(Expr::Un(UnOp::Neg, Box::new(self.parse_unary()?)))
        } else if self.eat_kw("not") {
            Ok(Expr::Un(UnOp::Not, Box::new(self.parse_unary()?)))
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_atom()?;
        loop {
            if let TokKind::Field(f) = self.peek().clone() {
                self.bump();
                if self.peek() == &TokKind::LParen {
                    let args = self.parse_paren_args()?;
                    e = Expr::IMethod(Box::new(e), f, args);
                } else {
                    e = Expr::Field(Box::new(e), f);
                }
            } else if self.peek() == &TokKind::Dot {
                self.bump();
                let m = self.parse_ident()?;
                let args = self.parse_paren_args()?;
                e = Expr::CMethod(Box::new(e), m, args);
            } else if self.peek() == &TokKind::LParen {
                let args = self.parse_paren_args()?;
                e = Expr::Apply(Box::new(e), args);
            } else if self.peek() == &TokKind::LBracket {
                self.bump();
                let idx = self.parse_expr()?;
                self.expect(&TokKind::RBracket)?;
                e = Expr::Index(Box::new(e), Box::new(idx));
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn parse_atom(&mut self) -> Result<Expr, String> {
        if self.peek() == &TokKind::LBrace {
            self.bump();
            let e = self.parse_expr()?;
            self.expect(&TokKind::RBrace)?;
            return Ok(e);
        }
        if self.peek() == &TokKind::LParen {
            self.bump();
            let e = self.parse_expr()?;
            self.expect(&TokKind::RParen)?;
            return Ok(Expr::Paren(Box::new(e)));
        }
        if self.peek() == &TokKind::LBracket {
            let es = self.parse_comma_list(|p| p.parse_expr())?;
            return Ok(Expr::List(es));
        }
        match self.peek().clone() {
            TokKind::Bnd(v) => { self.bump(); Ok(Expr::Bnd(v)) }
            TokKind::Str(s) => { self.bump(); Ok(Expr::Val(ValLit::Str(s))) }
            TokKind::Int(n) => { self.bump(); Ok(Expr::Math(Sign::None, Mag::Num(Numeral::Dec(n)))) }
            TokKind::Enum(e) => { self.bump(); Ok(Expr::Enum(e)) }
            TokKind::Field(f) => { self.bump(); Ok(Expr::FieldName(f)) }
            TokKind::Nt(n, args) => {
                self.bump();
                let mut pargs = Vec::with_capacity(args.len());
                for a in args {
                    pargs.push(ParamArg { param: a.param, plus: a.sign == ParamSign::Plus });
                }
                Ok(Expr::Nt(n, pargs))
            }
            TokKind::Clause(_) => {
                let r = self.parse_alg_ref()?;
                let args = self.parse_paren_args()?;
                Ok(Expr::Call(Callee::Alg(r), args))
            }
            TokKind::Prim(p) => {
                self.bump();
                let args = self.parse_paren_args()?;
                Ok(Expr::Call(Callee::Prim(p), args))
            }
            TokKind::Ident { name, quoted: true } => {
                self.bump();
                Ok(Expr::Var(name))
            }
            TokKind::Ident { name, quoted: false } => match name.as_str() {
                "undefined" => { self.bump(); Ok(Expr::Val(ValLit::Undefined)) }
                "null" => { self.bump(); Ok(Expr::Val(ValLit::Null)) }
                "true" => { self.bump(); Ok(Expr::Val(ValLit::Bool(true))) }
                "false" => { self.bump(); Ok(Expr::Val(ValLit::Bool(false))) }
                "this" => { self.bump(); Ok(Expr::Val(ValLit::This)) }
                "nan" => { self.bump(); Ok(Expr::Val(ValLit::Nan(Sub::None))) }
                "nan_f" => { self.bump(); Ok(Expr::Val(ValLit::Nan(Sub::F))) }
                "nan_z" => { self.bump(); Ok(Expr::Val(ValLit::Nan(Sub::Z))) }
                "err" => { self.bump(); Ok(Expr::Val(ValLit::Err(self.parse_field()?))) }
                "bign" if self.peek_at(1) == &TokKind::LParen => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let n = self.parse_numeral()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::Val(ValLit::BigN(n)))
                }
                "num_n" | "num_f" | "num_z" => {
                    let sub = match name.as_str() {
                        "num_n" => Sub::None,
                        "num_f" => Sub::F,
                        _ => Sub::Z,
                    };
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let sg = self.parse_sign();
                    let m = self.parse_mag()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::Val(ValLit::Num(sg, m, sub)))
                }
                "math" => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let sg = self.parse_sign();
                    let m = self.parse_mag()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::Math(sg, m))
                }
                "param" => { self.bump(); Ok(Expr::Param(self.parse_ident()?)) }
                "intrinsic" => { self.bump(); Ok(Expr::Intrinsic(self.parse_field()?)) }
                "prods" => { self.bump(); Ok(Expr::Prod(self.parse_comma_list(|p| p.parse_prod())?)) }
                "cu" | "cp" => {
                    let is_cp = name == "cp";
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let n = self.parse_int()?;
                    self.expect(&TokKind::Comma)?;
                    let d = self.parse_str()?;
                    self.expect(&TokKind::Comma)?;
                    let nm = if self.eat_kw("none") { None } else { Some(self.parse_str()?) };
                    self.expect(&TokKind::RParen)?;
                    Ok(if is_cp { Expr::CodePoint(n, d, nm) } else { Expr::CodeUnit(n, d, nm) })
                }
                "code" if matches!(self.peek_at(1), TokKind::Str(_)) => {
                    self.bump();
                    Ok(Expr::Code(self.parse_str()?))
                }
                "term" if matches!(self.peek_at(1), TokKind::Str(_)) => {
                    self.bump();
                    Ok(Expr::Term(self.parse_str()?))
                }
                "call_at" => {
                    self.bump();
                    let a = self.parse_alg_ref()?;
                    let args = self.parse_paren_args()?;
                    Ok(Expr::CallAt(a, args))
                }
                "sdo" => {
                    self.bump();
                    let sdo = self.parse_ident()?;
                    self.expect(&TokKind::LParen)?;
                    let sub = self.parse_expr()?;
                    let mut args = Vec::new();
                    if self.peek() == &TokKind::Semi {
                        self.bump();
                        loop {
                            args.push(self.parse_expr()?);
                            if self.peek() == &TokKind::Comma {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::Sdo(sdo, Box::new(sub), args))
                }
                "component" => {
                    self.bump();
                    let f = self.parse_field()?;
                    self.expect_kw("of")?;
                    let sub = self.parse_unary()?;
                    Ok(Expr::Component(f, Box::new(sub)))
                }
                "record" => {
                    self.bump();
                    let sort = if self.peek() == &TokKind::LBrace { None } else { Some(self.parse_ident()?) };
                    self.expect(&TokKind::LBrace)?;
                    let mut fs = Vec::new();
                    if self.peek() != &TokKind::RBrace {
                        loop {
                            let f = self.parse_field()?;
                            self.expect(&TokKind::Colon)?;
                            let e = self.parse_expr()?;
                            fs.push((f, e));
                            if self.peek() == &TokKind::Comma {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                    }
                    self.expect(&TokKind::RBrace)?;
                    Ok(Expr::Record(sort, fs))
                }
                "resumed_with" => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let e = self.parse_expr()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::ResumedWith(Box::new(e)))
                }
                "this_node" => { self.bump(); Ok(Expr::ThisNode) }
                "this_value" => { self.bump(); Ok(Expr::ThisValue) }
                "new_target" => { self.bump(); Ok(Expr::NewTarget) }
                "child" => {
                    self.bump();
                    let k = self.parse_usize()?;
                    let TokKind::Nt(nt, args) = self.peek().clone() else {
                        return self.err("expected |NT| after child index");
                    };
                    if !args.is_empty() {
                        return self.err("unexpected args on child |NT|");
                    }
                    self.bump();
                    Ok(Expr::Child(k, nt))
                }
                "child_of" => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let e = self.parse_expr()?;
                    self.expect(&TokKind::Comma)?;
                    let TokKind::Nt(nt, args) = self.peek().clone() else {
                        return self.err("expected |NT| in child_of");
                    };
                    if !args.is_empty() {
                        return self.err("unexpected args on child_of |NT|");
                    }
                    self.bump();
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::ChildOf(Box::new(e), nt))
                }
                "clause" => { self.bump(); Ok(Expr::Xref(self.parse_clause()?)) }
                "ref" => { self.bump(); Ok(Expr::Definition(self.parse_clause()?)) }
                "closure" => { self.bump(); Ok(Expr::Closure(self.parse_usize()?)) }
                "table" => { self.bump(); Ok(Expr::Table(self.parse_table_tok()?)) }
                "table_step" => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let t = self.parse_table_tok()?;
                    self.expect(&TokKind::Comma)?;
                    let k = self.parse_expr()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::TableStep(t, Box::new(k)))
                }
                "data" => {
                    self.bump();
                    if self.eat_kw("sort") {
                        Ok(Expr::Data(DataLit::Sort(self.parse_ident()?)))
                    } else if self.eat_kw("choice") {
                        Ok(Expr::Data(DataLit::Choice(self.parse_usize()?)))
                    } else if self.eat_kw("absent") {
                        Ok(Expr::Data(DataLit::Absent))
                    } else {
                        self.err("expected sort, choice, or absent after data")
                    }
                }
                "bool" if self.peek_at(1) == &TokKind::LParen => {
                    self.bump();
                    self.expect(&TokKind::LParen)?;
                    let c = self.parse_cond()?;
                    self.expect(&TokKind::RParen)?;
                    Ok(Expr::OfCond(Box::new(c)))
                }
                _ => {
                    self.bump();
                    Ok(Expr::Var(name))
                }
            },
            _ => self.err("expected expression"),
        }
    }

    // --- Predicates & Conditions & Types ---

    fn at_pred_start(&self) -> bool {
        self.at_kw("is") || self.at_kw("sat") || self.at_kw("fails")
    }

    fn parse_pred(&mut self) -> Result<Pred, String> {
        if self.eat_kw("is") {
            let neg = self.eat_kw("not");
            let neither = self.eat_kw("neither");
            if self.eat_kw("val") {
                self.expect(&TokKind::LBrace)?;
                let mut vs = Vec::new();
                if self.peek() != &TokKind::RBrace {
                    loop {
                        vs.push(self.parse_expr()?);
                        if self.peek() == &TokKind::Semi {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&TokKind::RBrace)?;
                Ok(Pred::IsVal { neg, neither, vals: vs })
            } else if self.eat_kw("ty") {
                self.expect(&TokKind::LBrace)?;
                let mut ts = Vec::new();
                if self.peek() != &TokKind::RBrace {
                    loop {
                        ts.push(self.parse_ty()?);
                        if self.peek() == &TokKind::Semi {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                self.expect(&TokKind::RBrace)?;
                Ok(Pred::IsTy { neg, neither, tys: ts })
            } else {
                self.err("expected val or ty in is predicate")
            }
        } else if self.at_kw("sat") || self.at_kw("fails") {
            let neg = self.eat_kw("fails");
            if !neg {
                self.expect_kw("sat")?;
            }
            let callee = match self.peek().clone() {
                TokKind::Clause(_) => Callee::Alg(self.parse_alg_ref()?),
                TokKind::Prim(p) => { self.bump(); Callee::Prim(p) }
                _ => return self.err("expected @clause or $prim after sat/fails"),
            };
            let args = self.parse_paren_args()?;
            Ok(Pred::Call { callee, args, neg })
        } else {
            self.err("expected predicate (is/sat/fails)")
        }
    }

    fn parse_pred_chain(&mut self) -> Result<(Pred, Vec<(Conj, Pred)>), String> {
        let p = self.parse_pred()?;
        let mut rest = Vec::new();
        loop {
            let conj = if self.at_kw("and") { Conj::And } else if self.at_kw("or") { Conj::Or } else { break };
            let next_starts_pred = matches!(self.peek_at(1), TokKind::Ident { name, quoted: false } if matches!(name.as_str(), "is" | "sat" | "fails"));
            if !next_starts_pred {
                break;
            }
            self.bump();
            rest.push((conj, self.parse_pred()?));
        }
        Ok((p, rest))
    }

    pub fn parse_cond(&mut self) -> Result<Cond, String> {
        let mut cs = vec![self.parse_cond_and()?];
        while self.eat_kw("or") {
            cs.push(self.parse_cond_and()?);
        }
        if cs.len() == 1 {
            Ok(cs.pop().unwrap())
        } else {
            Ok(Cond::Or(cs))
        }
    }

    fn parse_cond_and(&mut self) -> Result<Cond, String> {
        let mut cs = vec![self.parse_cond_atom()?];
        while self.eat_kw("and") {
            cs.push(self.parse_cond_atom()?);
        }
        if cs.len() == 1 {
            Ok(cs.pop().unwrap())
        } else {
            Ok(Cond::And(cs))
        }
    }

    fn token_after_matching_brace(&self) -> Option<&TokKind> {
        let mut depth = 0usize;
        let mut i = self.pos;
        while i < self.toks.len() {
            match &self.toks[i].kind {
                TokKind::LBrace => depth += 1,
                TokKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return self.toks.get(i + 1).map(|t| &t.kind);
                    }
                }
                TokKind::Eof => return None,
                _ => {}
            }
            i += 1;
        }
        None
    }

    fn is_rel_tok(k: &TokKind) -> Option<RelOp> {
        match k {
            TokKind::Lt => Some(RelOp::Lt),
            TokKind::Le => Some(RelOp::Le),
            TokKind::Gt => Some(RelOp::Gt),
            TokKind::Ge => Some(RelOp::Ge),
            TokKind::EqEq => Some(RelOp::Eq),
            TokKind::Ne => Some(RelOp::Ne),
            _ => None,
        }
    }

    fn parse_cond_atom(&mut self) -> Result<Cond, String> {
        if self.peek() == &TokKind::LBrace {
            let after = self.token_after_matching_brace();
            let is_expr_lhs = after.is_some_and(|k| {
                Self::is_rel_tok(k).is_some()
                    || matches!(k, TokKind::Ident { name, quoted: false } if matches!(name.as_str(), "is" | "sat" | "fails"))
            });
            if !is_expr_lhs {
                self.bump();
                let c = self.parse_cond()?;
                self.expect(&TokKind::RBrace)?;
                return Ok(c);
            }
        }
        if self.at_kw("all") && self.peek_at(1) == &TokKind::LBracket {
            self.bump();
            self.expect(&TokKind::LBracket)?;
            self.expect(&TokKind::RBracket)?;
            return Ok(Cond::And(vec![]));
        }
        if self.at_kw("any") && self.peek_at(1) == &TokKind::LBracket {
            self.bump();
            self.expect(&TokKind::LBracket)?;
            self.expect(&TokKind::RBracket)?;
            return Ok(Cond::Or(vec![]));
        }
        if self.peek() == &TokKind::LParen {
            // Careful: could `( ... )` be `Cond::Paren` or `Expr::Paren` as LHS of `rel`/`preds`?
            // Check token after matching `)`!
            let mut depth = 0usize;
            let mut i = self.pos;
            let mut after = None;
            while i < self.toks.len() {
                match &self.toks[i].kind {
                    TokKind::LParen => depth += 1,
                    TokKind::RParen => {
                        depth -= 1;
                        if depth == 0 {
                            after = self.toks.get(i + 1).map(|t| &t.kind);
                            break;
                        }
                    }
                    TokKind::Eof => break,
                    _ => {}
                }
                i += 1;
            }
            let is_expr_lhs = after.is_some_and(|k| {
                Self::is_rel_tok(k).is_some()
                    || matches!(k, TokKind::Ident { name, quoted: false } if matches!(name.as_str(), "is" | "sat" | "fails"))
                    || matches!(k, TokKind::Plus | TokKind::Minus | TokKind::Star | TokKind::Slash | TokKind::Caret | TokKind::Field(_) | TokKind::Dot | TokKind::LBracket)
                    || matches!(k, TokKind::Ident { name, quoted: false } if matches!(name.as_str(), "plus" | "modulo" | "times"))
            });
            if !is_expr_lhs {
                self.bump();
                let c = self.parse_cond()?;
                self.expect(&TokKind::RParen)?;
                return Ok(Cond::Paren(Box::new(c)));
            }
        }
        if self.at_kw("alg") && matches!(self.peek_at(1), TokKind::Clause(_)) {
            self.bump();
            return Ok(Cond::Alg(self.parse_alg_ref()?));
        }
        if self.at_kw("pass") && matches!(self.peek_at(1), TokKind::Str(_)) {
            self.bump();
            return Ok(Cond::Pass(self.parse_str()?));
        }
        if self.at_kw("expr") {
            let save = self.pos;
            if let Ok(lhs) = self.parse_expr() {
                if let Some(op) = Self::is_rel_tok(self.peek()) {
                    self.bump();
                    let rhs = self.parse_expr()?;
                    return Ok(Cond::Rel(op, lhs, rhs));
                } else if self.at_pred_start() {
                    let (p, rest) = self.parse_pred_chain()?;
                    return Ok(Cond::Preds(lhs, p, rest));
                }
            }
            self.pos = save;
            self.bump();
            return Ok(Cond::Expr(self.parse_expr()?));
        }
        let lhs = self.parse_expr()?;
        if let Some(op) = Self::is_rel_tok(self.peek()) {
            self.bump();
            let rhs = self.parse_expr()?;
            Ok(Cond::Rel(op, lhs, rhs))
        } else if self.at_pred_start() {
            let (p, rest) = self.parse_pred_chain()?;
            Ok(Cond::Preds(lhs, p, rest))
        } else {
            self.err("expected relational op or predicate in condition")
        }
    }

    pub fn parse_ty(&mut self) -> Result<TyExpr, String> {
        let mut ts = vec![self.parse_ty2()?];
        while self.peek() == &TokKind::Pipe {
            self.bump();
            ts.push(self.parse_ty2()?);
        }
        if ts.len() == 1 {
            Ok(ts.pop().unwrap())
        } else {
            Ok(TyExpr::Union(ts))
        }
    }

    fn parse_ty2(&mut self) -> Result<TyExpr, String> {
        let mut t = if self.peek() == &TokKind::LBrace {
            self.bump();
            let inner = self.parse_ty()?;
            self.expect(&TokKind::RBrace)?;
            inner
        } else if self.eat_kw("sort") {
            let mods = self.parse_comma_list(|p| p.parse_ident())?;
            let sort = self.parse_ident()?;
            TyExpr::Sort { mods, sort }
        } else if self.eat_kw("list") {
            self.expect(&TokKind::Lt)?;
            let inner = self.parse_ty()?;
            self.expect(&TokKind::Gt)?;
            TyExpr::ListOf(Box::new(inner))
        } else if self.eat_kw("seq") {
            self.expect(&TokKind::Lt)?;
            let inner = self.parse_ty()?;
            self.expect(&TokKind::Gt)?;
            TyExpr::SeqOf(Box::new(inner))
        } else if self.eat_kw("butnot") {
            self.expect(&TokKind::LParen)?;
            let a = self.parse_ty()?;
            self.expect(&TokKind::Comma)?;
            let b = self.parse_ty()?;
            self.expect(&TokKind::RParen)?;
            TyExpr::ButNot(Box::new(a), Box::new(b))
        } else if self.eat_kw("doc") {
            TyExpr::Doc(self.parse_str()?)
        } else if self.eat_kw("completion") {
            self.expect(&TokKind::Lt)?;
            let inner = if self.eat_kw("none") { None } else { Some(Box::new(self.parse_ty()?)) };
            self.expect(&TokKind::Gt)?;
            TyExpr::Completion(inner)
        } else if self.eat_kw("interval") {
            let base = self.parse_ty2()?;
            self.expect(&TokKind::LBracket)?;
            let lo = self.parse_expr()?;
            self.expect(&TokKind::Comma)?;
            let hi = self.parse_expr()?;
            self.expect(&TokKind::RBracket)?;
            TyExpr::Interval(Box::new(base), lo, hi)
        } else if self.eat_kw("val") {
            self.expect(&TokKind::LParen)?;
            let e = self.parse_expr()?;
            self.expect(&TokKind::RParen)?;
            TyExpr::Value(e)
        } else if self.eat_kw("var") {
            TyExpr::Var(self.parse_ident()?)
        } else if let TokKind::Nt(nt, args) = self.peek().clone() {
            if !args.is_empty() {
                return self.err("unexpected args on type |NT|");
            }
            self.bump();
            TyExpr::Nt(nt)
        } else if self.eat_kw("record") {
            self.expect(&TokKind::LBrace)?;
            let mut fs = Vec::new();
            if self.peek() != &TokKind::RBrace {
                loop {
                    let f = self.parse_field()?;
                    self.expect(&TokKind::Colon)?;
                    let ft = self.parse_ty()?;
                    fs.push((f, ft));
                    if self.peek() == &TokKind::Comma {
                        self.bump();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&TokKind::RBrace)?;
            TyExpr::Record(fs)
        } else if self.eat_kw("pred") {
            self.expect(&TokKind::LParen)?;
            let p = self.parse_pred()?;
            self.expect(&TokKind::RParen)?;
            TyExpr::Pred(p)
        } else {
            let sort = self.parse_ident()?;
            TyExpr::Sort { mods: vec![], sort }
        };
        while self.eat_kw("that") {
            let (p, rest) = self.parse_pred_chain()?;
            t = TyExpr::That(Box::new(t), p, rest);
        }
        Ok(t)
    }

    // --- Statements & Bodies ---

    fn parse_body(&mut self) -> Result<Body, String> {
        if self.peek() == &TokKind::Arrow {
            self.bump();
            Ok(Body::Inline(Box::new(self.parse_stmt()?)))
        } else if self.peek() == &TokKind::LBrace {
            self.bump();
            let mut ns = Vec::new();
            while self.peek() != &TokKind::RBrace {
                ns.push(self.parse_stmt()?);
            }
            self.bump();
            Ok(Body::Block(ns))
        } else {
            self.err("expected '->' or '{' for body")
        }
    }

    fn parse_braced_stmts(&mut self) -> Result<Vec<Stmt>, String> {
        self.expect(&TokKind::LBrace)?;
        let mut ns = Vec::new();
        while self.peek() != &TokKind::RBrace {
            ns.push(self.parse_stmt()?);
        }
        self.bump();
        Ok(ns)
    }

    pub fn parse_stmt(&mut self) -> Result<Stmt, String> {
        let TokKind::Ident { name, quoted: false } = self.peek().clone() else {
            return self.err("expected statement keyword");
        };
        self.bump();
        match name.as_str() {
            "let" => {
                let x = self.parse_ident()?;
                self.expect(&TokKind::Eq)?;
                let e = self.parse_expr()?;
                Ok(Stmt::Let(x, e))
            }
            "set" => {
                let place = if self.eat_kw("var") {
                    Place::Var(self.parse_ident()?)
                } else if self.eat_kw("field") {
                    let o = self.parse_postfix()?;
                    // Note: `printStmt` writes `{printChild cx vars 5 o}{tokField f} = ...`.
                    // Because `parse_postfix` eagerly parses `o[[f]]` as `Expr::Field(o, f)`, unwrap final `.Field`!
                    match o {
                        Expr::Field(obj, f) => Place::Field(*obj, f),
                        _ => return self.err("expected object[[field]] in set field"),
                    }
                } else if self.eat_kw("expr") {
                    Place::Expr(self.parse_postfix()?)
                } else {
                    return self.err("expected var, field, or expr after set");
                };
                self.expect(&TokKind::Eq)?;
                let rhs = self.parse_expr()?;
                Ok(Stmt::Set(place, rhs))
            }
            "return" => {
                // Only `return` without value occurs at end of line / block (`}` or `else` / `else_if` or next stmt keyword)!
                // Wait: can an expression start with `return`? No! What can follow `return` WITHOUT an expr?
                // Either `}`, `else`, `else_if`, or a stmt keyword! Notice variables starting statements are NEVER bare keywords;
                // Wait: what if `return x` is at line 1 and next stmt on line 2 is `let y = 1`?
                // Check line number OR token: even simpler, check `self.cur().line == prev_line` vs next token!
                // Actually let's check: in SpecTec, every statement is 1+ lines and `return <expr>` ALWAYS has `<expr>` on the same line,
                // whereas bare `return` NEVER has an expr on its line! Checking line equality handles EVERY case including `return x`!
                let ret_line = self.toks[self.pos - 1].line;
                if self.cur().line != ret_line || matches!(self.peek(), TokKind::RBrace | TokKind::Eof) {
                    Ok(Stmt::Ret(None))
                } else {
                    Ok(Stmt::Ret(Some(self.parse_expr()?)))
                }
            }
            "perform" => Ok(Stmt::Perform(self.parse_expr()?)),
            "if" => {
                let c = self.parse_cond()?;
                let bd = self.parse_body()?;
                let mut arms = Vec::new();
                while self.eat_kw("else_if") {
                    let ac = self.parse_cond()?;
                    let abd = self.parse_body()?;
                    arms.push(Arm { cond: Some(ac), body: abd });
                }
                let els = if self.eat_kw("else") {
                    Some(Arm { cond: None, body: self.parse_body()? })
                } else {
                    None
                };
                Ok(Stmt::If(c, bd, arms, els))
            }
            "if_else" => {
                let c = self.parse_cond()?;
                self.expect(&TokKind::LBrace)?;
                let s1 = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                self.expect_kw("else")?;
                self.expect(&TokKind::LBrace)?;
                let s2 = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(Stmt::IfElse(c, Box::new(s1), Box::new(s2)))
            }
            "assert" => {
                if matches!(self.peek(), TokKind::Bang) {
                    self.bump();
                    Ok(Stmt::AssertAlways(self.parse_cond()?))
                } else {
                    Ok(Stmt::Assert(self.parse_cond()?))
                }
            }
            "assert_if" => {
                let c = self.parse_cond()?;
                self.expect_kw("then")?;
                let d = self.parse_cond()?;
                Ok(Stmt::AssertIf(c, d))
            }
            "unreachable" => Ok(Stmt::Unreachable(self.parse_int()?)),
            "throw" => Ok(Stmt::ThrowVal(self.parse_expr()?)),
            "note" => Ok(Stmt::Note(self.parse_str()?)),
            "repeat" => Ok(Stmt::Repeat(self.parse_braced_stmts()?)),
            "repeat_while" => {
                let c = self.parse_cond()?;
                let ns = self.parse_braced_stmts()?;
                Ok(Stmt::RepeatWhile(c, ns))
            }
            "repeat_until" => {
                let c = self.parse_cond()?;
                let ns = self.parse_braced_stmts()?;
                Ok(Stmt::RepeatUntil(c, ns))
            }
            "for_each" => {
                let x = self.parse_ident()?;
                let ty = if self.peek() == &TokKind::Colon { self.bump(); Some(self.parse_ty()?) } else { None };
                let rev = self.eat_kw("rev");
                self.expect_kw("in")?;
                let list = self.parse_expr()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForEach { x, ty, list, rev, body })
            }
            "for_each_rec" => {
                let fields = self.parse_comma_list(|p| p.parse_field())?;
                let x = self.parse_ident()?;
                self.expect_kw("in")?;
                let list = self.parse_expr()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForEachRec { fields, x, list, body })
            }
            "for_range" => {
                let x = self.parse_ident()?;
                let lo_incl = if self.eat_kw("incl") { true } else { self.expect_kw("excl")?; false };
                let lo = self.parse_expr()?;
                self.expect(&TokKind::DotDot)?;
                let hi_incl = if self.eat_kw("incl") { true } else { self.expect_kw("excl")?; false };
                let hi = self.parse_expr()?;
                let desc = self.eat_kw("desc");
                let body = self.parse_body()?;
                Ok(Stmt::ForRange { x, lo, lo_incl, hi, hi_incl, desc, body })
            }
            "for_keys" => {
                let x = self.parse_ident()?;
                self.expect_kw("of")?;
                let obj = self.parse_expr()?;
                self.expect_kw("where")?;
                let cond = self.parse_cond()?;
                self.expect_kw("order")?;
                let order = self.parse_int()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForKeys { x, obj, cond, order, body })
            }
            "for_index" => {
                let x = self.parse_ident()?;
                self.expect_kw("of")?;
                let list = self.parse_expr()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForIndex { x, list, body })
            }
            "for_children" => {
                let x = self.parse_ident()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForChildren { x, body })
            }
            "for_children_of" => {
                let x = self.parse_ident()?;
                self.expect_kw("in")?;
                let expr = self.parse_expr()?;
                let body = self.parse_body()?;
                Ok(Stmt::ForChildrenOf { x, expr, body })
            }
            "repeat_n" => {
                let e = self.parse_expr()?;
                let ns = self.parse_braced_stmts()?;
                Ok(Stmt::RepeatN(e, ns))
            }
            "suspend" => {
                let e = self.parse_expr()?;
                self.expect_kw("kind")?;
                let v = self.parse_int()?;
                Ok(Stmt::Suspend(e, v))
            }
            "push" => {
                let e = self.parse_expr()?;
                self.expect_kw("kind")?;
                let v = self.parse_int()?;
                Ok(Stmt::Push(e, v))
            }
            "remove" => {
                let e = self.parse_expr()?;
                self.expect_kw("kind")?;
                let v = self.parse_int()?;
                Ok(Stmt::Remove(e, v))
            }
            "remove_restore" => {
                let e = self.parse_expr()?;
                self.expect_kw("with")?;
                let r = self.parse_expr()?;
                Ok(Stmt::RemoveRestore(e, r))
            }
            "resume_top" => Ok(Stmt::ResumeTop),
            "resume_let" => {
                let ctx = self.parse_expr()?;
                self.expect_kw("with")?;
                let val = self.parse_expr()?;
                self.expect(&TokKind::Arrow)?;
                let x = self.parse_ident()?;
                Ok(Stmt::ResumeLet { ctx, val, x })
            }
            "resume" => {
                let e = self.parse_expr()?;
                self.expect_kw("with")?;
                let v = self.parse_expr()?;
                Ok(Stmt::Resume(e, v))
            }
            "set_code_state" => {
                let e = self.parse_expr()?;
                self.expect_kw("to")?;
                let f = self.parse_expr()?;
                Ok(Stmt::SetCodeState(e, f))
            }
            "block" => Ok(Stmt::Block(self.parse_braced_stmts()?)),
            _ => self.err(&format!("unknown statement `{name}`")),
        }
    }

    // --- Headers, Closures, Algorithms, SDO Rows ---

    fn parse_alg_kind(&mut self) -> Result<AlgKind, String> {
        let s = self.parse_ident()?;
        match s.as_str() {
            "ao" => Ok(AlgKind::Ao),
            "sdo" => Ok(AlgKind::Sdo),
            "builtin" => Ok(AlgKind::Builtin),
            "internal_method" => Ok(AlgKind::InternalMethod),
            "concrete_method" => Ok(AlgKind::ConcreteMethod),
            "numeric_method" => Ok(AlgKind::NumericMethod),
            "host_defined" => Ok(AlgKind::HostDefined),
            "impl_defined" => Ok(AlgKind::ImplDefined),
            "untyped" => Ok(AlgKind::Untyped),
            _ => self.err(&format!("unknown alg kind `{s}`")),
        }
    }

    fn parse_header(&mut self) -> Result<Header, String> {
        self.expect(&TokKind::LParen)?;
        self.expect_kw("kind")?;
        let kind = self.parse_alg_kind()?;
        let recv = if self.eat_kw("recv") {
            let x = self.parse_ident()?;
            self.expect(&TokKind::Colon)?;
            let ty = self.parse_ty()?;
            Some((x, ty))
        } else {
            None
        };
        self.expect_kw("params")?;
        let params = self.parse_comma_list(|p| {
            let x = p.parse_ident()?;
            let ty = if p.peek() == &TokKind::Colon { p.bump(); Some(p.parse_ty()?) } else { None };
            let optional = p.eat_kw("opt");
            let rest = p.eat_kw("rest");
            Ok(ParamDecl { x, ty, optional, rest })
        })?;
        let ret = if self.peek() == &TokKind::Arrow {
            self.bump();
            Some(self.parse_ty()?)
        } else {
            None
        };
        self.expect(&TokKind::RParen)?;
        Ok(Header { kind, recv, params, ret })
    }

    fn parse_sdo_header(&mut self) -> Result<SdoHeader, String> {
        self.expect(&TokKind::LParen)?;
        self.expect_kw("kind")?;
        let kind = self.parse_alg_kind()?;
        let recv = if self.eat_kw("recv") {
            self.expect_kw("slot")?;
            let sl = self.parse_usize()?;
            self.expect(&TokKind::Colon)?;
            let ty = self.parse_ty()?;
            Some((sl, ty))
        } else {
            None
        };
        self.expect_kw("params")?;
        let params = self.parse_comma_list(|p| {
            p.expect_kw("slot")?;
            let slot = p.parse_usize()?;
            let ty = if p.peek() == &TokKind::Colon { p.bump(); Some(p.parse_ty()?) } else { None };
            let optional = p.eat_kw("opt");
            let rest = p.eat_kw("rest");
            Ok(HeaderSlot { slot, ty, optional, rest })
        })?;
        let ret = if self.peek() == &TokKind::Arrow {
            self.bump();
            Some(self.parse_ty()?)
        } else {
            None
        };
        self.expect(&TokKind::RParen)?;
        Ok(SdoHeader { kind, recv, params, ret })
    }

    fn parse_closure(&mut self) -> Result<CloLit, String> {
        self.expect_kw("closure")?;
        let ks = self.parse_ident()?;
        let kind = match ks.as_str() {
            "abstract" => CloKind::Abstract,
            "job" => CloKind::Job,
            "matcher" => CloKind::Matcher,
            "matcher_continuation" => CloKind::MatcherContinuation,
            "read_modify_write" => CloKind::ReadModifyWrite,
            _ => return self.err(&format!("unknown closure kind `{ks}`")),
        };
        let atomic = self.eat_kw("atomic");
        self.expect_kw("params")?;
        let params = if self.eat_kw("none") {
            None
        } else {
            Some(self.parse_comma_list(|p| p.parse_ident())?)
        };
        self.expect_kw("captures")?;
        let captures = self.parse_comma_list(|p| p.parse_ident())?;
        let frame = if self.eat_kw("frame") {
            self.expect(&TokKind::LParen)?;
            let a = self.parse_ident()?;
            self.expect(&TokKind::Comma)?;
            let b = self.parse_ident()?;
            self.expect(&TokKind::Comma)?;
            let c = self.parse_ident()?;
            self.expect(&TokKind::RParen)?;
            Some((a, b, c))
        } else {
            None
        };
        let body = self.parse_braced_stmts()?;
        Ok(CloLit { kind, atomic, params, captures, frame, body })
    }

    fn parse_def(&mut self) -> Result<AlgDef, String> {
        self.expect_kw("def")?;
        let id = self.parse_alg_ref()?;
        let name = self.parse_str()?;
        let header = self.parse_header()?;
        self.expect_kw("vars")?;
        let vars = self.parse_comma_list(|p| p.parse_ident())?;
        self.expect(&TokKind::LBrace)?;
        let mut body = Vec::new();
        let mut closures = Vec::new();
        while self.peek() != &TokKind::RBrace {
            if self.at_kw("closure") {
                closures.push(self.parse_closure()?);
            } else if closures.is_empty() {
                body.push(self.parse_stmt()?);
            } else {
                return self.err("statement after closure inside def");
            }
        }
        self.bump();
        Ok(AlgDef { id, name, header, vars, body, closures })
    }

    fn parse_sdo_row(&mut self) -> Result<SdoRowDef, String> {
        self.expect_kw("sdo_row")?;
        let id = self.parse_alg_ref()?;
        let sdo = self.parse_ident()?;
        self.expect_kw("form")?;
        let form = if self.eat_kw("alg") {
            RowForm::Alg
        } else {
            self.expect_kw("equation")?;
            RowForm::Equation
        };
        let annex = self.eat_kw("annex");
        self.expect(&TokKind::LBrace)?;
        self.expect_kw("prods")?;
        let prods = self.parse_comma_list(|p| p.parse_prod())?;
        self.expect_kw("keys")?;
        let keys = self.parse_comma_list(|p| p.parse_str())?;
        self.expect_kw("vars")?;
        let vars = self.parse_comma_list(|p| p.parse_ident())?;
        self.expect_kw("steps")?;
        let steps = self.parse_braced_stmts()?;
        let mut closures = Vec::new();
        while self.at_kw("closure") {
            closures.push(self.parse_closure()?);
        }
        self.expect(&TokKind::RBrace)?;
        Ok(SdoRowDef { id, sdo, form, annex, prods, keys, vars, steps, closures })
    }

    // --- Declarations ---

    fn parse_sort_test(&mut self) -> Result<SortTest, String> {
        if self.eat_kw("none") {
            Ok(SortTest::None)
        } else if self.eat_kw("alg") {
            Ok(SortTest::Alg(self.parse_alg_ref()?))
        } else {
            let neg = self.eat_kw("not");
            let name = self.parse_prim()?;
            self.expect(&TokKind::LParen)?;
            let mut args = Vec::new();
            if self.peek() != &TokKind::RParen {
                loop {
                    if self.eat_kw("subject") {
                        args.push(SortTestArg::Subject);
                    } else {
                        args.push(SortTestArg::Enum(self.parse_enum()?));
                    }
                    if self.peek() == &TokKind::Comma {
                        self.bump();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&TokKind::RParen)?;
            Ok(SortTest::Prim { name, args, neg })
        }
    }

    // --- Grammar ---

    fn parse_terminal(&mut self) -> Result<Terminal, String> {
        if self.eat_kw("alt") {
            Ok(Terminal::Text { text: self.parse_str()?, alt: true })
        } else if self.eat_kw("cp") {
            Ok(Terminal::Cp(self.parse_ident()?))
        } else {
            Ok(Terminal::Text { text: self.parse_str()?, alt: false })
        }
    }

    fn parse_g_sym(&mut self) -> Result<GrammarSym, String> {
        if let TokKind::Nt(n, args) = self.peek().clone() {
            self.bump();
            Ok(GrammarSym::Nt(n, args))
        } else {
            Ok(GrammarSym::T(self.parse_terminal()?))
        }
    }

    fn parse_look_item(&mut self) -> Result<LookItem, String> {
        if self.eat_kw("noLT") {
            Ok(LookItem::NoLT)
        } else {
            Ok(LookItem::T(self.parse_terminal()?))
        }
    }

    fn parse_look_seq(&mut self) -> Result<Vec<LookItem>, String> {
        let mut out = Vec::new();
        while !matches!(self.peek(), TokKind::Comma | TokKind::RBrace | TokKind::RBracket | TokKind::Eof) {
            out.push(self.parse_look_item()?);
        }
        Ok(out)
    }

    fn parse_grammar_item(&mut self) -> Result<GrammarItem, String> {
        if matches!(self.peek(), TokKind::Gt) {
            self.bump();
            return Ok(GrammarItem::Phrase(self.parse_ident()?));
        }
        if self.peek() == &TokKind::LBracket {
            self.bump();
            if self.eat_kw("noLT") {
                self.expect(&TokKind::RBracket)?;
                return Ok(GrammarItem::NoLT);
            }
            if self.eat_kw("empty") {
                self.expect(&TokKind::RBracket)?;
                return Ok(GrammarItem::Empty);
            }
            if self.eat_kw("onlyIf") {
                let p = self.parse_ident()?;
                self.expect(&TokKind::RBracket)?;
                return Ok(GrammarItem::OnlyIf(p));
            }
            self.expect_kw("lookahead")?;
            let la = if matches!(self.peek(), TokKind::EqEq) {
                self.bump();
                Lookahead::Eq(self.parse_look_seq()?)
            } else if matches!(self.peek(), TokKind::Ne) {
                self.bump();
                Lookahead::Ne(self.parse_look_seq()?)
            } else if self.eat_kw("in") {
                self.expect(&TokKind::LBrace)?;
                let mut sets = Vec::new();
                loop {
                    sets.push(self.parse_look_seq()?);
                    if self.peek() == &TokKind::Comma {
                        self.bump();
                    } else {
                        break;
                    }
                }
                self.expect(&TokKind::RBrace)?;
                Lookahead::Mem(sets)
            } else if self.eat_kw("not_in") {
                if self.peek() == &TokKind::LBrace {
                    self.bump();
                    let mut sets = Vec::new();
                    loop {
                        sets.push(self.parse_look_seq()?);
                        if self.peek() == &TokKind::Comma {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokKind::RBrace)?;
                    Lookahead::NotMem(sets)
                } else if let TokKind::Nt(nt, args) = self.peek().clone() {
                    if !args.is_empty() {
                        return self.err("unexpected args in lookahead not_in |NT|");
                    }
                    self.bump();
                    Lookahead::NotMemNt(nt)
                } else {
                    return self.err("expected { or |NT| after lookahead not_in");
                }
            } else {
                return self.err("expected ==, !=, in, or not_in after lookahead");
            };
            self.expect(&TokKind::RBracket)?;
            return Ok(GrammarItem::Lookahead(la));
        }
        let s = self.parse_g_sym()?;
        if self.eat_kw("butnot") {
            let ex = if self.eat_kw("one_of") {
                let or_sep = if self.eat_kw("or") { true } else { self.expect_kw("plain")?; false };
                let syms = self.parse_comma_list(|p| p.parse_g_sym())?;
                Exclusion::OneOf { syms, or_sep }
            } else {
                Exclusion::Sym(self.parse_g_sym()?)
            };
            Ok(GrammarItem::ButNot(s, ex))
        } else {
            let opt = matches!(self.peek(), TokKind::Quest);
            if opt {
                self.bump();
            }
            Ok(GrammarItem::Sym(s, opt))
        }
    }

    fn parse_guard(&mut self) -> Result<Vec<ParamArg>, String> {
        if self.peek() != &TokKind::LBracket {
            return Ok(vec![]);
        }
        self.parse_comma_list(|p| {
            let plus = if matches!(p.peek(), TokKind::Plus) {
                p.bump();
                true
            } else if matches!(p.peek(), TokKind::Tilde) {
                p.bump();
                false
            } else {
                return p.err("expected + or ~ in guard");
            };
            let param = p.parse_ident()?;
            Ok(ParamArg { param, plus })
        })
    }

    fn parse_rule(&mut self) -> Result<Rule, String> {
        self.expect_kw("rule")?;
        let grammar = GrammarId::parse(&self.parse_ident()?)?;
        let TokKind::Nt(lhs, nt_args) = self.peek().clone() else {
            return self.err("expected |LHS| after grammar id");
        };
        if !nt_args.is_empty() {
            return self.err("unexpected args on rule |LHS|");
        }
        self.bump();
        let params = self.parse_comma_list(|p| p.parse_ident())?;
        let colons = match self.peek() {
            TokKind::Colon => { self.bump(); Colons::One }
            TokKind::Colons2 => { self.bump(); Colons::Two }
            TokKind::Colons3 => { self.bump(); Colons::Three }
            _ => return self.err("expected :, ::, or :::"),
        };
        let body = if self.eat_kw("one_of") {
            self.expect(&TokKind::LBrace)?;
            let mut rows = Vec::new();
            while self.eat_kw("row") {
                rows.push(self.parse_comma_list(|p| p.parse_terminal())?);
            }
            self.expect(&TokKind::RBrace)?;
            RuleBody::OneOf(rows)
        } else {
            self.expect(&TokKind::LBrace)?;
            let mut alts = Vec::new();
            while self.peek() == &TokKind::Pipe {
                let alt_line = self.cur().line;
                self.bump();
                let guard = if self.peek() == &TokKind::LBracket
                    && matches!(self.peek_at(1), TokKind::Plus | TokKind::Tilde)
                {
                    self.parse_guard()?
                } else {
                    vec![]
                };
                let mut rhs = Vec::new();
                while self.cur().line == alt_line
                    && !matches!(self.peek(), TokKind::HashLabel | TokKind::Pipe | TokKind::RBrace | TokKind::Eof)
                {
                    rhs.push(self.parse_grammar_item()?);
                }
                let label = if matches!(self.peek(), TokKind::HashLabel) {
                    self.bump();
                    Some(self.parse_str()?)
                } else {
                    None
                };
                alts.push(Alt { guard, rhs, label });
            }
            self.expect(&TokKind::RBrace)?;
            RuleBody::Alts(alts)
        };
        Ok(Rule { grammar, lhs, params, colons, body })
    }

    // --- Early Errors ---

    fn parse_early_sent(&mut self) -> Result<EarlySent, String> {
        let TokKind::Ident { name, quoted: false } = self.peek().clone() else {
            return self.err("expected early error sentence keyword");
        };
        self.bump();
        match name.as_str() {
            "syntax_error" | "early_syntax_error" => {
                let early = name == "early_syntax_error";
                let cond = self.parse_cond()?;
                let unless = if self.eat_kw("unless") {
                    let uf = if self.eat_kw("plain") {
                        UnlessForm::Plain
                    } else if self.eat_kw("comma") {
                        UnlessForm::Comma
                    } else {
                        self.expect_kw("opt")?;
                        UnlessForm::Optional
                    };
                    Some((uf, self.parse_cond()?))
                } else {
                    None
                };
                Ok(EarlySent::SyntaxError { early, cond, unless })
            }
            "syntax_error_ins" => {
                let a = self.parse_cond()?;
                self.expect(&TokKind::Amp)?;
                let b = self.parse_cond()?;
                Ok(EarlySent::SyntaxErrorIns(a, b))
            }
            "must_cover" => {
                let e = self.parse_expr()?;
                self.expect(&TokKind::Colon)?;
                let t = self.parse_ty()?;
                Ok(EarlySent::MustCover(e, t))
            }
            "rules_applied" => {
                let ps = self.parse_comma_list(|p| p.parse_prod())?;
                let raw = self.parse_str()?;
                Ok(EarlySent::RulesApplied(ps, raw))
            }
            "if_inline" => {
                let c = self.parse_cond()?;
                self.expect(&TokKind::Arrow)?;
                let s = self.parse_early_sent()?;
                Ok(EarlySent::IfInline(c, Box::new(s)))
            }
            "info" => {
                self.expect(&TokKind::LBrace)?;
                let s = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(EarlySent::Info(s))
            }
            "not_applied" => {
                let c = self.parse_cond()?;
                self.expect(&TokKind::LBrace)?;
                let s = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(EarlySent::NotApplied(c, s))
            }
            "for_each_in" => {
                let x = self.parse_ident()?;
                self.expect(&TokKind::Colon)?;
                let ty = self.parse_ty()?;
                self.expect_kw("in")?;
                let list = self.parse_expr()?;
                self.expect_kw("where")?;
                let cond = self.parse_cond()?;
                self.expect(&TokKind::LBrace)?;
                let stmt = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(EarlySent::ForEachIn { x, ty, list, cond, stmt })
            }
            "stmt" => {
                self.expect(&TokKind::LBrace)?;
                let s = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(EarlySent::Stmt(s))
            }
            _ => self.err(&format!("unknown early sentence `{name}`")),
        }
    }

    fn parse_early(&mut self) -> Result<EarlyRow, String> {
        self.expect_kw("early")?;
        let id = self.parse_alg_ref()?;
        let sdo = self.parse_ident()?;
        let modifies = self.eat_kw("modifies");
        self.expect(&TokKind::LBrace)?;
        self.expect_kw("prods")?;
        let prods = self.parse_comma_list(|p| p.parse_prod())?;
        self.expect_kw("keys")?;
        let keys = self.parse_comma_list(|p| p.parse_str())?;
        self.expect_kw("vars")?;
        let vars = self.parse_comma_list(|p| p.parse_ident())?;
        self.expect_kw("sentences")?;
        self.expect(&TokKind::LBrace)?;
        let mut sentences = Vec::new();
        while self.peek() != &TokKind::RBrace {
            sentences.push(self.parse_early_sent()?);
        }
        self.bump();
        self.expect(&TokKind::RBrace)?;
        Ok(EarlyRow { id, sdo, modifies, prods, keys, vars, sentences })
    }

    // --- Tables ---

    fn parse_tty(&mut self) -> Result<TTy, String> {
        if self.eat_kw("records") {
            let fs = self.parse_comma_list(|p| {
                let f = p.parse_field()?;
                p.expect(&TokKind::Colon)?;
                let t = p.parse_ty()?;
                Ok((f, t))
            })?;
            Ok(TTy::Records(fs))
        } else {
            Ok(TTy::Ty(self.parse_ty()?))
        }
    }

    fn parse_sig(&mut self) -> Result<Sig, String> {
        let (kind, name) = if self.eat_kw("field") {
            (SigKind::Field, self.parse_field()?)
        } else {
            self.expect_kw("method")?;
            (SigKind::Method, self.parse_ident()?)
        };
        self.expect(&TokKind::LParen)?;
        let mut params = Vec::new();
        if self.peek() != &TokKind::RParen {
            loop {
                let x = self.parse_ident()?;
                self.expect(&TokKind::Colon)?;
                let ty = self.parse_tty()?;
                let optional = self.eat_kw("opt");
                params.push(SigParam { x, ty, optional });
                if self.peek() == &TokKind::Comma {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        self.expect(&TokKind::RParen)?;
        self.expect(&TokKind::Arrow)?;
        let ret = self.parse_tty()?;
        Ok(Sig { kind, name, params, ret })
    }

    fn parse_cell_body(&mut self) -> Result<CellBody, String> {
        let TokKind::Ident { name, quoted: false } = self.peek().clone() else {
            return self.err("expected table cell body tag");
        };
        self.bump();
        match name.as_str() {
            "field" => Ok(CellBody::Field(self.parse_field()?)),
            "ty" => {
                self.expect(&TokKind::LParen)?;
                let t = self.parse_tty()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Ty(t))
            }
            "sig" => {
                self.expect(&TokKind::LParen)?;
                let g = self.parse_sig()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Sig(g))
            }
            "stmt" => {
                self.expect(&TokKind::LBrace)?;
                let s = self.parse_stmt()?;
                self.expect(&TokKind::RBrace)?;
                Ok(CellBody::Stmt(s))
            }
            "alg" => Ok(CellBody::Alg(self.parse_alg_ref()?)),
            "expr" => {
                self.expect(&TokKind::LParen)?;
                let e = self.parse_expr()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Expr(e))
            }
            "op" => Ok(CellBody::Op(self.parse_clause()?)),
            "component" => Ok(CellBody::Component(self.parse_field()?)),
            "name" => Ok(CellBody::Name(self.parse_str()?)),
            "lines" => Ok(CellBody::Lines(self.parse_comma_list(|p| p.parse_cell_body())?)),
            "dfn" => {
                self.expect(&TokKind::LParen)?;
                let inner = self.parse_cell_body()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Dfn(Box::new(inner)))
            }
            "code" => {
                self.expect(&TokKind::LParen)?;
                let inner = self.parse_cell_body()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Code(Box::new(inner)))
            }
            "link" => {
                let href = self.parse_str()?;
                self.expect(&TokKind::LParen)?;
                let inner = self.parse_cell_body()?;
                self.expect(&TokKind::RParen)?;
                Ok(CellBody::Link(href, Box::new(inner)))
            }
            "raw" => Ok(CellBody::Raw(self.parse_str()?)),
            "text" => Ok(CellBody::Text(self.parse_str()?)),
            _ => self.err(&format!("unknown cell body `{name}`")),
        }
    }

    fn parse_table(&mut self) -> Result<TableDef, String> {
        self.expect_kw("table")?;
        let name = self.parse_table_tok()?;
        if self.eat_kw("retired") {
            return Ok(TableDef { name, body: None });
        }
        let clause = self.parse_clause()?;
        let TokKind::HashIdx(idx) = self.peek().clone() else {
            return self.err("expected #idx after table clause");
        };
        self.bump();
        self.expect(&TokKind::LBrace)?;
        self.expect_kw("kind")?;
        let ks = self.parse_ident()?;
        let kind = match ks.as_str() {
            "fields" => TableKind::Fields,
            "slots" => TableKind::Slots,
            "internal_methods" => TableKind::InternalMethods,
            "abstract_methods" => TableKind::AbstractMethods,
            "components" => TableKind::Components,
            "properties" => TableKind::Properties,
            "intrinsics" => TableKind::Intrinsics,
            "conversion" => TableKind::Conversion,
            "data" => TableKind::Data,
            _ => return self.err(&format!("unknown table kind `{ks}`")),
        };
        self.expect_kw("thead")?;
        let thead = self.parse_bool()?;
        let caption = if self.eat_kw("caption") { Some(self.parse_str()?) } else { None };
        let schema = if self.eat_kw("schema") {
            self.expect(&TokKind::LParen)?;
            let s = self.parse_str()?;
            self.expect(&TokKind::Comma)?;
            let b = self.parse_bool()?;
            self.expect(&TokKind::RParen)?;
            Some((s, b))
        } else {
            None
        };
        self.expect_kw("vars")?;
        let vars = self.parse_comma_list(|p| p.parse_ident())?;
        self.expect_kw("rows")?;
        self.expect(&TokKind::LBracket)?;
        let mut rows = Vec::new();
        while self.eat_kw("row") {
            self.expect(&TokKind::LBracket)?;
            let mut cells = Vec::new();
            while self.eat_kw("cell") {
                let (rowspan, colspan) = if self.eat_kw("span") {
                    self.expect(&TokKind::LParen)?;
                    let r = self.parse_usize()?;
                    self.expect(&TokKind::Comma)?;
                    let c = self.parse_usize()?;
                    self.expect(&TokKind::RParen)?;
                    (r, c)
                } else {
                    (1, 1)
                };
                self.expect(&TokKind::LBrace)?;
                let body = self.parse_cell_body()?;
                self.expect(&TokKind::RBrace)?;
                cells.push(TableCell { rowspan, colspan, body });
            }
            self.expect(&TokKind::RBracket)?;
            rows.push(cells);
        }
        self.expect(&TokKind::RBracket)?;
        self.expect(&TokKind::RBrace)?;
        Ok(TableDef {
            name,
            body: Some(TableBody { clause, idx, kind, thead, caption, schema, vars, rows }),
        })
    }

    // --- Realm ---

    fn parse_rkey(&mut self) -> Result<RKey, String> {
        if self.eat_kw("str") {
            Ok(RKey::Str(self.parse_str()?))
        } else {
            self.expect_kw("sym")?;
            Ok(RKey::Sym(self.parse_str()?))
        }
    }

    fn parse_rval(&mut self) -> Result<RVal, String> {
        if self.eat_kw("undefined") { Ok(RVal::Undefined) }
        else if self.eat_kw("null") { Ok(RVal::Null) }
        else if self.eat_kw("true") { Ok(RVal::Bool(true)) }
        else if self.eat_kw("false") { Ok(RVal::Bool(false)) }
        else if matches!(self.peek(), TokKind::Str(_)) { Ok(RVal::Str(self.parse_str()?)) }
        else if self.eat_kw("number") { Ok(RVal::Number(self.parse_int()?)) }
        else if self.eat_kw("obj") { Ok(RVal::Obj(self.parse_usize()?)) }
        else if self.eat_kw("sym") { Ok(RVal::Sym(self.parse_str()?)) }
        else if self.eat_kw("global_this") { Ok(RVal::GlobalThis) }
        else if self.eat_kw("created") { Ok(RVal::Created(self.parse_alg_ref()?)) }
        else { self.err("expected RVal") }
    }

    fn parse_rattrs(&mut self) -> Result<RAttrs, String> {
        self.expect(&TokKind::LBrace)?;
        let wk = self.parse_ident()?;
        if wk != "w" { return self.err("expected w:"); }
        self.expect(&TokKind::Colon)?;
        let w = self.parse_bool()?;
        self.expect(&TokKind::Comma)?;
        let ek = self.parse_ident()?;
        if ek != "e" { return self.err("expected e:"); }
        self.expect(&TokKind::Colon)?;
        let e = self.parse_bool()?;
        self.expect(&TokKind::Comma)?;
        let ck = self.parse_ident()?;
        if ck != "c" { return self.err("expected c:"); }
        self.expect(&TokKind::Colon)?;
        let c = self.parse_bool()?;
        self.expect(&TokKind::RBrace)?;
        Ok(RAttrs { w, e, c })
    }

    fn parse_opt_usize(&mut self) -> Result<Option<usize>, String> {
        if self.eat_kw("some") {
            Ok(Some(self.parse_usize()?))
        } else {
            self.expect_kw("none")?;
            Ok(None)
        }
    }

    fn parse_rprop(&mut self) -> Result<RProp, String> {
        self.expect_kw("prop")?;
        let key = self.parse_rkey()?;
        self.expect(&TokKind::Eq)?;
        let val = if self.eat_kw("data") {
            self.expect(&TokKind::LParen)?;
            let v = self.parse_rval()?;
            self.expect(&TokKind::RParen)?;
            RPVal::Data(v)
        } else {
            self.expect_kw("accessor")?;
            self.expect(&TokKind::LParen)?;
            let g = self.parse_opt_usize()?;
            self.expect(&TokKind::Comma)?;
            let s = self.parse_opt_usize()?;
            self.expect(&TokKind::RParen)?;
            RPVal::Accessor(g, s)
        };
        self.expect_kw("attrs")?;
        let attrs = self.parse_rattrs()?;
        let clause = self.parse_clause()?;
        let annex_b = self.eat_kw("annexB");
        let opt = self.eat_kw("opt");
        let omittable = self.eat_kw("omittable");
        Ok(RProp { key, val, attrs, clause, annex_b, opt, omittable })
    }

    fn parse_robj(&mut self) -> Result<RObj, String> {
        self.expect_kw("obj")?;
        let idx = self.parse_usize()?;
        let path = self.parse_str()?;
        let clause = self.parse_clause()?;
        let annex_b = self.eat_kw("annexB");
        let opt = self.eat_kw("opt");
        self.expect(&TokKind::LBrace)?;
        self.expect_kw("names")?;
        let names = self.parse_comma_list(|p| p.parse_field())?;
        self.expect_kw("keys")?;
        let keys = self.parse_comma_list(|p| p.parse_field())?;
        self.expect_kw("kind")?;
        let kind = if self.eat_kw("ordinary") {
            RKind::Ordinary
        } else {
            self.expect_kw("exotic")?;
            RKind::Exotic(self.parse_clause()?)
        };
        self.expect_kw("proto")?;
        let proto = self.parse_opt_usize()?;
        self.expect_kw("extensible")?;
        let extensible = self.parse_bool()?;
        self.expect_kw("slots")?;
        let slots = self.parse_comma_list(|p| {
            p.expect(&TokKind::LParen)?;
            let f = p.parse_field()?;
            p.expect(&TokKind::Comma)?;
            let v = p.parse_rval()?;
            p.expect(&TokKind::RParen)?;
            Ok((f, v))
        })?;
        let fn_ = if self.eat_kw("fn") {
            self.expect(&TokKind::LBrace)?;
            self.expect_kw("alg")?;
            let alg = if self.eat_kw("some") {
                Some(self.parse_alg_ref()?)
            } else {
                self.expect_kw("none")?;
                None
            };
            let lk = self.parse_ident()?;
            if lk != "len" { return self.err("expected len in fn"); }
            let len = self.parse_usize()?;
            let nk = self.parse_ident()?;
            if nk != "name" { return self.err("expected name in fn"); }
            let name = self.parse_rkey()?;
            let pk = self.parse_ident()?;
            if pk != "pfx" { return self.err("expected pfx in fn"); }
            let pfx = if self.eat_kw("some") { Some(self.parse_str()?) } else { self.expect_kw("none")?; None };
            let ck = self.parse_ident()?;
            if ck != "ctor" { return self.err("expected ctor in fn"); }
            let ctor = self.parse_bool()?;
            let ak = self.parse_ident()?;
            if ak != "async" { return self.err("expected async in fn"); }
            let is_async = self.parse_bool()?;
            let lak = self.parse_ident()?;
            if lak != "len_attrs" { return self.err("expected len_attrs in fn"); }
            let len_attrs = self.parse_rattrs()?;
            let nak = self.parse_ident()?;
            if nak != "name_attrs" { return self.err("expected name_attrs in fn"); }
            let name_attrs = self.parse_rattrs()?;
            self.expect(&TokKind::RBrace)?;
            Some(RFn { alg, len, name, pfx, ctor, is_async, len_attrs, name_attrs })
        } else {
            None
        };
        self.expect_kw("props")?;
        self.expect(&TokKind::LBracket)?;
        let mut props = Vec::new();
        while self.at_kw("prop") {
            props.push(self.parse_rprop()?);
        }
        self.expect(&TokKind::RBracket)?;
        self.expect(&TokKind::RBrace)?;
        Ok(RObj { idx, path, clause, annex_b, opt, names, keys, kind, proto, extensible, slots, fn_, props })
    }

    fn parse_clause_props(&mut self) -> Result<ClauseProps, String> {
        self.expect_kw("clause_props")?;
        let clause = self.parse_clause()?;
        self.expect(&TokKind::LBracket)?;
        let mut props = Vec::new();
        while self.at_kw("prop") {
            props.push(self.parse_rprop()?);
        }
        self.expect(&TokKind::RBracket)?;
        Ok(ClauseProps { clause, props })
    }

    fn parse_goal_args(&mut self) -> Result<Vec<ParamArg>, String> {
        if self.peek() != &TokKind::LBracket {
            return Ok(vec![]);
        }
        self.parse_comma_list(|p| {
            let plus = if matches!(p.peek(), TokKind::Plus) {
                p.bump();
                true
            } else if matches!(p.peek(), TokKind::Tilde) {
                p.bump();
                false
            } else {
                return p.err("expected + or ~ in goal arg");
            };
            let param = p.parse_ident()?;
            Ok(ParamArg { param, plus })
        })
    }

    fn parse_decl(&mut self) -> Result<Decl, String> {
        let TokKind::Ident { name, quoted: false } = self.peek().clone() else {
            return self.err("expected declaration keyword");
        };
        self.bump();
        match name.as_str() {
            "clause" => {
                let id = self.parse_clause()?;
                let op = if self.eat_kw("op") { Some(self.parse_str()?) } else { None };
                Ok(Decl::Clause { id, op })
            }
            "field" => Ok(Decl::Field(self.parse_field()?)),
            "enum" => Ok(Decl::Enum(self.parse_enum()?)),
            "method" => Ok(Decl::Method(self.parse_ident()?)),
            "extern" => {
                self.expect_kw("def")?;
                let pname = self.parse_prim()?;
                let (sig, meaning) = if self.peek() == &TokKind::LBrace {
                    self.bump();
                    self.expect_kw("sig")?;
                    let s = self.parse_str()?;
                    self.expect_kw("meaning")?;
                    let m = self.parse_str()?;
                    self.expect(&TokKind::RBrace)?;
                    (Some(s), Some(m))
                } else {
                    (None, None)
                };
                Ok(Decl::ExternDef { name: pname, sig, meaning })
            }
            "syntax" => {
                let sname = self.parse_ident()?;
                let def = if self.eat_kw("defined") {
                    self.expect(&TokKind::LBrace)?;
                    if self.peek() == &TokKind::RBrace {
                        self.bump();
                        Some(SortDef { super_sorts: vec![], record: false, test: SortTest::None })
                    } else {
                        self.expect_kw("super")?;
                        let super_sorts = self.parse_comma_list(|p| p.parse_ident())?;
                        self.expect_kw("record")?;
                        let record = self.parse_bool()?;
                        self.expect_kw("test")?;
                        let test = self.parse_sort_test()?;
                        self.expect(&TokKind::RBrace)?;
                        Some(SortDef { super_sorts, record, test })
                    }
                } else {
                    None
                };
                Ok(Decl::Syntax { name: sname, def })
            }
            "sdo" => {
                let sname = self.parse_ident()?;
                let (header, default) = if self.peek() == &TokKind::LBrace {
                    self.bump();
                    let h = if self.eat_kw("header") { Some(self.parse_sdo_header()?) } else { None };
                    let d = if self.eat_kw("default") { Some(self.parse_alg_ref()?) } else { None };
                    self.expect(&TokKind::RBrace)?;
                    (h, d)
                } else {
                    (None, None)
                };
                Ok(Decl::Sdo { name: sname, header, default })
            }
            "checked_jobs" => Ok(Decl::CheckedJobs(self.parse_comma_list(|p| p.parse_clause())?)),
            "sort_alias" => {
                let from = self.parse_str()?;
                self.expect(&TokKind::Arrow)?;
                let to = self.parse_ident()?;
                Ok(Decl::SortAlias { from, to })
            }
            "grammar_alt" => {
                let TokKind::Nt(nt, args) = self.peek().clone() else {
                    return self.err("expected |NT| in grammar_alt");
                };
                if !args.is_empty() {
                    return self.err("unexpected args on grammar_alt |NT|");
                }
                self.bump();
                self.expect(&TokKind::Eq)?;
                let items = self.parse_comma_list(|p| {
                    if p.eat_kw("cp") {
                        Ok(GrammarAltItem::Cp(p.parse_str()?))
                    } else {
                        Ok(GrammarAltItem::Text(p.parse_str()?))
                    }
                })?;
                Ok(Decl::GrammarAlt { nt, items })
            }
            "clause_prods" => {
                let clause = self.parse_clause()?;
                self.expect(&TokKind::Eq)?;
                let prods = self.parse_comma_list(|p| p.parse_prod())?;
                Ok(Decl::ClauseProds { clause, prods })
            }
            _ => self.err(&format!("unknown declaration keyword `{name}`")),
        }
    }

    pub fn parse_file(&mut self, rel_path: String, header_comment: Option<String>) -> Result<SpecFile, String> {
        let mut grammar_decl = None;
        if self.eat_kw("grammar") {
            grammar_decl = Some(GrammarId::parse(&self.parse_ident()?)?);
        }
        let mut items = Vec::new();
        while self.peek() != &TokKind::Eof {
            let TokKind::Ident { name, quoted: false } = self.peek().clone() else {
                return self.err("expected top-level declaration");
            };
            match name.as_str() {
                "clause" | "field" | "enum" | "method" | "extern" | "syntax" | "sdo"
                | "checked_jobs" | "sort_alias" | "grammar_alt" | "clause_prods" => {
                    items.push(TopItem::Decl(self.parse_decl()?));
                }
                "param" => { self.bump(); items.push(TopItem::Param(self.parse_ident()?)); }
                "nt" => { self.bump(); items.push(TopItem::Nt(self.parse_ident()?)); }
                "block" => {
                    self.bump();
                    let grammar = GrammarId::parse(&self.parse_ident()?)?;
                    let clause = self.parse_clause()?;
                    let kind = if self.eat_kw("main") {
                        BlockKind::Main
                    } else if self.eat_kw("supplemental") {
                        let TokKind::Nt(nt, args) = self.peek().clone() else {
                            return self.err("expected |NT| in supplemental block");
                        };
                        if !args.is_empty() { return self.err("unexpected args on block |NT|"); }
                        self.bump();
                        BlockKind::Supplemental(nt)
                    } else {
                        self.expect_kw("overlay")?;
                        let section = self.parse_ident()?;
                        let mode = self.parse_ident()?;
                        let cond = self.parse_ident()?;
                        BlockKind::Overlay { section, mode, cond }
                    };
                    let rules = self.parse_comma_list(|p| {
                        let TokKind::Nt(nt, args) = p.peek().clone() else {
                            return p.err("expected |NT| in block rules");
                        };
                        if !args.is_empty() { return p.err("unexpected args in block rule list"); }
                        p.bump();
                        Ok(nt)
                    })?;
                    items.push(TopItem::Block(BlockDef { grammar, clause, kind, rules }));
                }
                "goal" => {
                    self.bump();
                    let TokKind::Nt(nt, args) = self.peek().clone() else {
                        return self.err("expected |NT| in goal");
                    };
                    self.bump();
                    let pargs = if args.is_empty() {
                        self.parse_goal_args()?
                    } else {
                        args.into_iter()
                            .map(|a| ParamArg { param: a.param, plus: a.sign == ParamSign::Plus })
                            .collect()
                    };
                    self.expect_kw("src")?;
                    let src = self.parse_ident()?;
                    items.push(TopItem::Goal(GoalDef { nt, args: pargs, src }));
                }
                "cover" => {
                    self.bump();
                    let context = self.parse_prod()?;
                    self.expect_kw("cover")?;
                    let TokKind::Nt(cover, args1) = self.peek().clone() else {
                        return self.err("expected |NT| in cover");
                    };
                    if !args1.is_empty() { return self.err("unexpected args in cover"); }
                    self.bump();
                    self.expect_kw("refined")?;
                    let TokKind::Nt(refined, args2) = self.peek().clone() else {
                        return self.err("expected |NT| in refined");
                    };
                    if !args2.is_empty() { return self.err("unexpected args in refined"); }
                    self.bump();
                    items.push(TopItem::Cover(CoverDef { context, cover, refined }));
                }
                "semi" => {
                    self.bump();
                    let prod = self.parse_prod()?;
                    let pk = self.parse_ident()?;
                    if pk != "pos" { return self.err("expected pos in semi"); }
                    let pos = self.parse_usize()?;
                    let kind = self.parse_ident()?;
                    items.push(TopItem::Semi(SemiDef { prod, pos, kind }));
                }
                "rule" => items.push(TopItem::Rule(self.parse_rule()?)),
                "early" => items.push(TopItem::Early(self.parse_early()?)),
                "table" => items.push(TopItem::Table(self.parse_table()?)),
                "symbols" => {
                    self.bump();
                    let syms = self.parse_comma_list(|p| p.parse_str())?;
                    items.push(TopItem::Symbols(syms));
                }
                "obj" => items.push(TopItem::RObj(self.parse_robj()?)),
                "clause_props" => items.push(TopItem::ClauseProps(self.parse_clause_props()?)),
                "def" => items.push(TopItem::Def(self.parse_def()?)),
                "sdo_row" => items.push(TopItem::SdoRow(self.parse_sdo_row()?)),
                _ => return self.err(&format!("unexpected top-level item `{name}`")),
            }
        }
        Ok(SpecFile { rel_path, header_comment, grammar_decl, items })
    }
}

pub fn parse_str(rel_path: &str, src: &str) -> Result<SpecFile, String> {
    let lex_out = lex(src).map_err(|e| format!("{rel_path}: {e}"))?;
    Parser::new(lex_out.tokens)
        .parse_file(rel_path.to_string(), lex_out.header_comment)
        .map_err(|e| format!("{rel_path}: {e}"))
}

pub fn load_spec_dir(dir: &std::path::Path) -> Result<Spec, String> {
    let mut paths = Vec::new();
    collect_spectec_paths(dir, dir, &mut paths)?;
    paths.sort();
    let mut files = Vec::with_capacity(paths.len());
    for (rel, full) in paths {
        let src = std::fs::read_to_string(&full)
            .map_err(|e| format!("reading {}: {e}", full.display()))?;
        files.push(parse_str(&rel, &src)?);
    }
    Ok(Spec { files })
}

fn collect_spectec_paths(root: &std::path::Path, dir: &std::path::Path, out: &mut Vec<(String, std::path::PathBuf)>) -> Result<(), String> {
    let rd = std::fs::read_dir(dir).map_err(|e| format!("reading {}: {e}", dir.display()))?;
    for entry in rd {
        let entry = entry.map_err(|e| format!("{}: {e}", dir.display()))?;
        let p = entry.path();
        if p.is_dir() {
            collect_spectec_paths(root, &p, out)?;
        } else if p.extension().is_some_and(|e| e == "spectec") {
            let rel = p.strip_prefix(root).unwrap_or(&p).to_string_lossy().replace('\\', "/");
            out.push((rel, p));
        }
    }
    Ok(())
}

