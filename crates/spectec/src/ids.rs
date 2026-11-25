//! Alphabetically derived ID tables from parsed SpecTec specifications.

use crate::ast::*;
use crate::emit_grammar::collect_rule_prods;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct IdTable {
    pub kind: &'static str,
    pub names: Vec<String>,
    pub by_name: BTreeMap<String, usize>,
}

impl IdTable {
    pub fn from_set(kind: &'static str, set: BTreeSet<String>) -> Self {
        let mut names = Vec::with_capacity(set.len());
        let mut by_name = BTreeMap::new();
        for (id, name) in set.into_iter().enumerate() {
            by_name.insert(name.clone(), id);
            names.push(name);
        }
        Self { kind, names, by_name }
    }

    pub fn get(&self, name: &str) -> Result<usize, String> {
        self.by_name
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown entry `{name}` in {} table", self.kind))
    }
}

#[derive(Clone, Debug)]
pub struct Ids {
    pub clause: IdTable,
    pub enum_: IdTable,
    pub field: IdTable,
    pub method: IdTable,
    pub nt: IdTable,
    pub param: IdTable,
    pub prim: IdTable,
    pub prod: IdTable,
    pub sdo: IdTable,
    pub sort: IdTable,
    pub table: IdTable,
}

#[derive(Default)]
struct Collector {
    clause: BTreeSet<String>,
    enum_: BTreeSet<String>,
    field: BTreeSet<String>,
    method: BTreeSet<String>,
    nt: BTreeSet<String>,
    param: BTreeSet<String>,
    prim: BTreeSet<String>,
    prod: BTreeSet<String>,
    sdo: BTreeSet<String>,
    sort: BTreeSet<String>,
    table: BTreeSet<String>,
}

impl Collector {
    fn visit_alg_ref(&mut self, a: &AlgRef) {
        self.clause.insert(a.clause.clone());
    }

    fn visit_callee(&mut self, c: &Callee) {
        match c {
            Callee::Alg(a) => self.visit_alg_ref(a),
            Callee::Prim(p) => {
                if !p.is_empty() {
                    self.prim.insert(p.clone());
                }
            }
        }
    }

    fn visit_val(&mut self, v: &ValLit) {
        if let ValLit::Err(f) = v {
            self.field.insert(f.clone());
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Var(_) | Expr::Bnd(_) | Expr::Math(_, _) | Expr::CodeUnit(_, _, _) | Expr::CodePoint(_, _, _)
            | Expr::Code(_) | Expr::Term(_) | Expr::ThisNode | Expr::ThisValue | Expr::NewTarget | Expr::Closure(_) => {}
            Expr::Val(v) => self.visit_val(v),
            Expr::Enum(en) => {
                self.enum_.insert(en.clone());
            }
            Expr::Param(p) => {
                self.param.insert(p.clone());
            }
            Expr::Intrinsic(f) | Expr::FieldName(f) => {
                self.field.insert(f.clone());
            }
            Expr::Nt(n, args) => {
                self.nt.insert(n.clone());
                for a in args {
                    self.param.insert(a.param.clone());
                }
            }
            Expr::Prod(ps) => {
                for p in ps {
                    self.prod.insert(p.clone());
                }
            }
            Expr::Call(c, args) => {
                self.visit_callee(c);
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::CallAt(a, args) => {
                self.visit_alg_ref(a);
                for ar in args {
                    self.visit_expr(ar);
                }
            }
            Expr::Sdo(sd, sub, args) => {
                self.sdo.insert(sd.clone());
                self.visit_expr(sub);
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Component(f, sub) => {
                self.field.insert(f.clone());
                self.visit_expr(sub);
            }
            Expr::Field(o, f) => {
                self.visit_expr(o);
                self.field.insert(f.clone());
            }
            Expr::IMethod(o, f, args) => {
                self.visit_expr(o);
                self.field.insert(f.clone());
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::CMethod(o, m, args) => {
                self.visit_expr(o);
                self.method.insert(m.clone());
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Apply(f, args) => {
                self.visit_expr(f);
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Index(o, i) => {
                self.visit_expr(o);
                self.visit_expr(i);
            }
            Expr::Q(x) | Expr::Bang(x) | Expr::Un(_, x) | Expr::Paren(x) | Expr::ResumedWith(x) => {
                self.visit_expr(x);
            }
            Expr::Bin(_, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Expr::List(es) => {
                for x in es {
                    self.visit_expr(x);
                }
            }
            Expr::Record(so, fs) => {
                if let Some(s) = so {
                    self.sort.insert(s.clone());
                }
                for (f, v) in fs {
                    self.field.insert(f.clone());
                    self.visit_expr(v);
                }
            }
            Expr::Child(_, n) => {
                self.nt.insert(n.clone());
            }
            Expr::ChildOf(o, n) => {
                self.visit_expr(o);
                self.nt.insert(n.clone());
            }
            Expr::Xref(c) | Expr::Definition(c) => {
                self.clause.insert(c.clone());
            }
            Expr::Table(t) => {
                self.table.insert(t.clone());
            }
            Expr::TableStep(t, k) => {
                self.table.insert(t.clone());
                self.visit_expr(k);
            }
            Expr::Data(DataLit::Sort(s)) => {
                self.sort.insert(s.clone());
            }
            Expr::Data(_) => {}
            Expr::OfCond(c) => self.visit_cond(c),
        }
    }

    fn visit_pred(&mut self, p: &Pred) {
        match p {
            Pred::IsVal { vals, .. } => {
                for v in vals {
                    self.visit_expr(v);
                }
            }
            Pred::IsTy { tys, .. } => {
                for t in tys {
                    self.visit_ty(t);
                }
            }
            Pred::Call { callee, args, .. } => {
                self.visit_callee(callee);
                for a in args {
                    self.visit_expr(a);
                }
            }
        }
    }

    fn visit_cond(&mut self, c: &Cond) {
        match c {
            Cond::Preds(e, p, rest) => {
                self.visit_expr(e);
                self.visit_pred(p);
                for (_, pr) in rest {
                    self.visit_pred(pr);
                }
            }
            Cond::Rel(_, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Cond::And(cs) | Cond::Or(cs) => {
                for x in cs {
                    self.visit_cond(x);
                }
            }
            Cond::Paren(x) => self.visit_cond(x),
            Cond::Alg(a) => self.visit_alg_ref(a),
            Cond::Expr(e) => self.visit_expr(e),
            Cond::Pass(_) => {}
        }
    }

    fn visit_ty(&mut self, t: &TyExpr) {
        match t {
            TyExpr::Sort { mods, sort } => {
                for m in mods {
                    self.sort.insert(m.clone());
                }
                self.sort.insert(sort.clone());
            }
            TyExpr::ListOf(inner) | TyExpr::SeqOf(inner) => self.visit_ty(inner),
            TyExpr::Union(ts) => {
                for x in ts {
                    self.visit_ty(x);
                }
            }
            TyExpr::Completion(o) => {
                if let Some(inner) = o {
                    self.visit_ty(inner);
                }
            }
            TyExpr::Interval(base, lo, hi) => {
                self.visit_ty(base);
                self.visit_expr(lo);
                self.visit_expr(hi);
            }
            TyExpr::Value(e) => self.visit_expr(e),
            TyExpr::Var(_) | TyExpr::Doc(_) => {}
            TyExpr::Nt(n) => {
                self.nt.insert(n.clone());
            }
            TyExpr::Record(fs) => {
                for (f, v) in fs {
                    self.field.insert(f.clone());
                    self.visit_ty(v);
                }
            }
            TyExpr::That(base, p, rest) => {
                self.visit_ty(base);
                self.visit_pred(p);
                for (_, pr) in rest {
                    self.visit_pred(pr);
                }
            }
            TyExpr::Pred(p) => self.visit_pred(p),
            TyExpr::ButNot(a, b) => {
                self.visit_ty(a);
                self.visit_ty(b);
            }
        }
    }

    fn visit_body(&mut self, b: &Body) {
        match b {
            Body::Inline(st) => self.visit_stmt(st),
            Body::Block(ns) => self.visit_stmts(ns),
        }
    }

    fn visit_stmts(&mut self, ns: &[Stmt]) {
        for st in ns {
            self.visit_stmt(st);
        }
    }

    fn visit_stmt(&mut self, st: &Stmt) {
        match st {
            Stmt::Let(_, e) | Stmt::Perform(e) | Stmt::ThrowVal(e) => self.visit_expr(e),
            Stmt::Set(pl, e) => {
                match pl {
                    Place::Var(_) => {}
                    Place::Field(o, f) => {
                        self.visit_expr(o);
                        self.field.insert(f.clone());
                    }
                    Place::Expr(lhs) => self.visit_expr(lhs),
                }
                self.visit_expr(e);
            }
            Stmt::Ret(oe) => {
                if let Some(e) = oe {
                    self.visit_expr(e);
                }
            }
            Stmt::If(c, bd, arms, els) => {
                self.visit_cond(c);
                self.visit_body(bd);
                for a in arms.iter().chain(els.iter()) {
                    if let Some(ac) = &a.cond {
                        self.visit_cond(ac);
                    }
                    self.visit_body(&a.body);
                }
            }
            Stmt::IfElse(c, s1, s2) => {
                self.visit_cond(c);
                self.visit_stmt(s1);
                self.visit_stmt(s2);
            }
            Stmt::Assert(c) | Stmt::AssertAlways(c) => self.visit_cond(c),
            Stmt::AssertIf(c, d) => {
                self.visit_cond(c);
                self.visit_cond(d);
            }
            Stmt::Unreachable(_) | Stmt::Note(_) | Stmt::ResumeTop => {}
            Stmt::Repeat(ns) | Stmt::Block(ns) => self.visit_stmts(ns),
            Stmt::RepeatWhile(c, ns) | Stmt::RepeatUntil(c, ns) => {
                self.visit_cond(c);
                self.visit_stmts(ns);
            }
            Stmt::ForEach { ty, list, body, .. } => {
                if let Some(t) = ty {
                    self.visit_ty(t);
                }
                self.visit_expr(list);
                self.visit_body(body);
            }
            Stmt::ForEachRec { fields, list, body, .. } => {
                for f in fields {
                    self.field.insert(f.clone());
                }
                self.visit_expr(list);
                self.visit_body(body);
            }
            Stmt::ForRange { lo, hi, body, .. } => {
                self.visit_expr(lo);
                self.visit_expr(hi);
                self.visit_body(body);
            }
            Stmt::ForKeys { obj, cond, body, .. } => {
                self.visit_expr(obj);
                self.visit_cond(cond);
                self.visit_body(body);
            }
            Stmt::ForIndex { list, body, .. } => {
                self.visit_expr(list);
                self.visit_body(body);
            }
            Stmt::ForChildren { body, .. } => self.visit_body(body),
            Stmt::ForChildrenOf { expr, body, .. } => {
                self.visit_expr(expr);
                self.visit_body(body);
            }
            Stmt::RepeatN(e, ns) => {
                self.visit_expr(e);
                self.visit_stmts(ns);
            }
            Stmt::Suspend(e, _) | Stmt::Push(e, _) | Stmt::Remove(e, _) => self.visit_expr(e),
            Stmt::RemoveRestore(a, b) | Stmt::Resume(a, b) | Stmt::SetCodeState(a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            Stmt::ResumeLet { ctx, val, .. } => {
                self.visit_expr(ctx);
                self.visit_expr(val);
            }
        }
    }

    fn visit_header(&mut self, h: &Header) {
        if let Some((_, t)) = &h.recv {
            self.visit_ty(t);
        }
        for p in &h.params {
            if let Some(t) = &p.ty {
                self.visit_ty(t);
            }
        }
        if let Some(t) = &h.ret {
            self.visit_ty(t);
        }
    }

    fn visit_closures(&mut self, cs: &[CloLit]) {
        for c in cs {
            self.visit_stmts(&c.body);
        }
    }

    fn visit_gsym(&mut self, s: &GrammarSym) {
        if let GrammarSym::Nt(n, args) = s {
            self.nt.insert(n.clone());
            for a in args {
                self.param.insert(a.param.clone());
            }
        }
    }

    fn visit_early_sent(&mut self, es: &EarlySent) {
        match es {
            EarlySent::SyntaxError { cond, unless, .. } => {
                self.visit_cond(cond);
                if let Some((_, d)) = unless {
                    self.visit_cond(d);
                }
            }
            EarlySent::SyntaxErrorIns(a, b) => {
                self.visit_cond(a);
                self.visit_cond(b);
            }
            EarlySent::MustCover(e, t) => {
                self.visit_expr(e);
                self.visit_ty(t);
            }
            EarlySent::RulesApplied(ps, _) => {
                for p in ps {
                    self.prod.insert(p.clone());
                }
            }
            EarlySent::IfInline(c, inner) => {
                self.visit_cond(c);
                self.visit_early_sent(inner);
            }
            EarlySent::Info(st) | EarlySent::Stmt(st) => self.visit_stmt(st),
            EarlySent::NotApplied(c, st) => {
                self.visit_cond(c);
                self.visit_stmt(st);
            }
            EarlySent::ForEachIn { ty, list, cond, stmt, .. } => {
                self.visit_ty(ty);
                self.visit_expr(list);
                self.visit_cond(cond);
                self.visit_stmt(stmt);
            }
        }
    }

    fn visit_tty(&mut self, tt: &TTy) {
        match tt {
            TTy::Ty(t) => self.visit_ty(t),
            TTy::Records(fs) => {
                for (f, t) in fs {
                    self.field.insert(f.clone());
                    self.visit_ty(t);
                }
            }
        }
    }

    fn visit_cell_body(&mut self, cb: &CellBody) {
        match cb {
            CellBody::Field(f) | CellBody::Component(f) => {
                self.field.insert(f.clone());
            }
            CellBody::Ty(t) => self.visit_tty(t),
            CellBody::Sig(g) => {
                match g.kind {
                    SigKind::Field => {
                        self.field.insert(g.name.clone());
                    }
                    SigKind::Method => {
                        self.method.insert(g.name.clone());
                    }
                }
                for p in &g.params {
                    self.visit_tty(&p.ty);
                }
                self.visit_tty(&g.ret);
            }
            CellBody::Stmt(st) => self.visit_stmt(st),
            CellBody::Alg(a) => self.visit_alg_ref(a),
            CellBody::Expr(e) => self.visit_expr(e),
            CellBody::Op(c) => {
                self.clause.insert(c.clone());
            }
            CellBody::Lines(cs) => {
                for c in cs {
                    self.visit_cell_body(c);
                }
            }
            CellBody::Dfn(c) | CellBody::Code(c) | CellBody::Link(_, c) => self.visit_cell_body(c),
            CellBody::Name(_) | CellBody::Raw(_) | CellBody::Text(_) => {}
        }
    }

    fn visit_rval(&mut self, v: &RVal) {
        if let RVal::Created(a) = v {
            self.visit_alg_ref(a);
        }
    }

    fn visit_rprop(&mut self, p: &RProp) {
        self.clause.insert(p.clause.clone());
        if let RPVal::Data(v) = &p.val {
            self.visit_rval(v);
        }
    }

    fn visit_decl(&mut self, d: &Decl) {
        match d {
            Decl::Clause { id, .. } => {
                self.clause.insert(id.clone());
            }
            Decl::Field(f) => {
                self.field.insert(f.clone());
            }
            Decl::Enum(e) => {
                self.enum_.insert(e.clone());
            }
            Decl::Method(m) => {
                self.method.insert(m.clone());
            }
            Decl::ExternDef { name, .. } => {
                if !name.is_empty() {
                    self.prim.insert(name.clone());
                }
            }
            Decl::Syntax { name, def } => {
                self.sort.insert(name.clone());
                if let Some(sd) = def {
                    for s in &sd.super_sorts {
                        self.sort.insert(s.clone());
                    }
                    match &sd.test {
                        SortTest::None => {}
                        SortTest::Alg(a) => self.visit_alg_ref(a),
                        SortTest::Prim { name, args, .. } => {
                            if !name.is_empty() {
                                self.prim.insert(name.clone());
                            }
                            for arg in args {
                                if let SortTestArg::Enum(e) = arg {
                                    self.enum_.insert(e.clone());
                                }
                            }
                        }
                    }
                }
            }
            Decl::Sdo { name, header, default } => {
                self.sdo.insert(name.clone());
                if let Some(h) = header {
                    if let Some((_, t)) = &h.recv {
                        self.visit_ty(t);
                    }
                    for p in &h.params {
                        if let Some(t) = &p.ty {
                            self.visit_ty(t);
                        }
                    }
                    if let Some(t) = &h.ret {
                        self.visit_ty(t);
                    }
                }
                if let Some(a) = default {
                    self.visit_alg_ref(a);
                }
            }
            Decl::CheckedJobs(cs) => {
                for c in cs {
                    self.clause.insert(c.clone());
                }
            }
            Decl::SortAlias { to, .. } => {
                self.sort.insert(to.clone());
            }
            Decl::GrammarAlt { nt, .. } => {
                self.nt.insert(nt.clone());
            }
            Decl::ClauseProds { clause, prods } => {
                self.clause.insert(clause.clone());
                for p in prods {
                    self.prod.insert(p.clone());
                }
            }
        }
    }

    fn visit_item(&mut self, item: &TopItem) {
        match item {
            TopItem::Decl(d) => self.visit_decl(d),
            TopItem::Param(p) => {
                self.param.insert(p.clone());
            }
            TopItem::Nt(n) => {
                self.nt.insert(n.clone());
            }
            TopItem::Block(b) => {
                self.clause.insert(b.clause.clone());
                if let BlockKind::Supplemental(n) = &b.kind {
                    self.nt.insert(n.clone());
                }
                for r in &b.rules {
                    self.nt.insert(r.clone());
                }
            }
            TopItem::Goal(g) => {
                self.nt.insert(g.nt.clone());
                for a in &g.args {
                    self.param.insert(a.param.clone());
                }
            }
            TopItem::Cover(c) => {
                self.prod.insert(c.context.clone());
                self.nt.insert(c.cover.clone());
                self.nt.insert(c.refined.clone());
            }
            TopItem::Semi(s) => {
                self.prod.insert(s.prod.clone());
            }
            TopItem::Rule(r) => {
                self.nt.insert(r.lhs.clone());
                for p in &r.params {
                    self.param.insert(p.clone());
                }
                collect_rule_prods(r, &mut self.prod);
                if let RuleBody::Alts(alts) = &r.body {
                    for a in alts {
                        for g in &a.guard {
                            self.param.insert(g.param.clone());
                        }
                        for it in &a.rhs {
                            match it {
                                GrammarItem::Sym(s, _) => self.visit_gsym(s),
                                GrammarItem::Lookahead(Lookahead::NotMemNt(n)) => {
                                    self.nt.insert(n.clone());
                                }
                                GrammarItem::ButNot(s, ex) => {
                                    self.visit_gsym(s);
                                    match ex {
                                        Exclusion::Sym(e) => self.visit_gsym(e),
                                        Exclusion::OneOf { syms, .. } => {
                                            for e in syms {
                                                self.visit_gsym(e);
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            TopItem::Early(er) => {
                self.visit_alg_ref(&er.id);
                self.sdo.insert(er.sdo.clone());
                for p in &er.prods {
                    self.prod.insert(p.clone());
                }
                for es in &er.sentences {
                    self.visit_early_sent(es);
                }
            }
            TopItem::Table(t) => {
                self.table.insert(t.name.clone());
                if let Some(b) = &t.body {
                    self.clause.insert(b.clause.clone());
                    for row in &b.rows {
                        for cell in row {
                            self.visit_cell_body(&cell.body);
                        }
                    }
                }
            }
            TopItem::Symbols(_) => {}
            TopItem::RObj(o) => {
                self.clause.insert(o.clause.clone());
                for n in &o.names {
                    self.field.insert(n.clone());
                }
                for k in &o.keys {
                    self.field.insert(k.clone());
                }
                if let RKind::Exotic(c) = &o.kind {
                    self.clause.insert(c.clone());
                }
                for (f, v) in &o.slots {
                    self.field.insert(f.clone());
                    self.visit_rval(v);
                }
                if let Some(fn_) = &o.fn_ {
                    if let Some(a) = &fn_.alg {
                        self.visit_alg_ref(a);
                    }
                }
                for p in &o.props {
                    self.visit_rprop(p);
                }
            }
            TopItem::ClauseProps(cp) => {
                self.clause.insert(cp.clause.clone());
                for p in &cp.props {
                    self.visit_rprop(p);
                }
            }
            TopItem::Def(a) => {
                self.visit_alg_ref(&a.id);
                self.visit_header(&a.header);
                self.visit_stmts(&a.body);
                self.visit_closures(&a.closures);
            }
            TopItem::SdoRow(r) => {
                self.visit_alg_ref(&r.id);
                self.sdo.insert(r.sdo.clone());
                for p in &r.prods {
                    self.prod.insert(p.clone());
                }
                self.visit_stmts(&r.steps);
                self.visit_closures(&r.closures);
            }
            TopItem::SpecModule(_) => {}
        }
    }
}

impl Ids {
    pub fn from_spec(spec: &Spec) -> Self {
        let mut c = Collector::default();
        for f in &spec.files {
            for item in &f.items {
                c.visit_item(item);
            }
        }
        Self {
            clause: IdTable::from_set("clause", c.clause),
            enum_: IdTable::from_set("enum", c.enum_),
            field: IdTable::from_set("field", c.field),
            method: IdTable::from_set("method", c.method),
            nt: IdTable::from_set("nt", c.nt),
            param: IdTable::from_set("param", c.param),
            prim: IdTable::from_set("prim", c.prim),
            prod: IdTable::from_set("prod", c.prod),
            sdo: IdTable::from_set("sdo", c.sdo),
            sort: IdTable::from_set("sort", c.sort),
            table: IdTable::from_set("table", c.table),
        }
    }
}
