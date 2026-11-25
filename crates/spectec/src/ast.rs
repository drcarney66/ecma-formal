//! Core AST types for the ECMA-262 SpecTec DSL and clean Ecma model.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgRef {
    pub clause: String,
    pub idx: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamArg {
    pub param: String,
    pub plus: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamSign {
    Plus,
    Tilde,
    Quest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NtArg {
    pub param: String,
    pub sign: ParamSign,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    None,
    Plus,
    Minus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Numeral {
    Dec(u64),
    Hex(u64, String),
    Frac(u64, u64, u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mag {
    Num(Numeral),
    Inf,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sub {
    None,
    F,
    Z,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValLit {
    Undefined,
    Null,
    Bool(bool),
    This,
    Str(String),
    Nan(Sub),
    Num(Sign, Mag, Sub),
    Err(String),
    BigN(Numeral),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Plus,
    Mul,
    Div,
    Modulo,
    Times,
    Pow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conj {
    And,
    Or,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AltForm {
    Or,
    Neither,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    Alg(AlgRef),
    Prim(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DataLit {
    Sort(String),
    Choice(usize),
    Absent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    Bnd(String),
    Val(ValLit),
    Math(Sign, Mag),
    Enum(String),
    Param(String),
    Intrinsic(String),
    FieldName(String),
    Nt(String, Vec<ParamArg>),
    Prod(Vec<String>),
    CodeUnit(u64, String, Option<String>),
    CodePoint(u64, String, Option<String>),
    Code(String),
    Term(String),
    Call(Callee, Vec<Expr>),
    CallAt(AlgRef, Vec<Expr>),
    Sdo(String, Box<Expr>, Vec<Expr>),
    Component(String, Box<Expr>),
    Field(Box<Expr>, String),
    IMethod(Box<Expr>, String, Vec<Expr>),
    CMethod(Box<Expr>, String, Vec<Expr>),
    Apply(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Q(Box<Expr>),
    Bang(Box<Expr>),
    Un(UnOp, Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Paren(Box<Expr>),
    List(Vec<Expr>),
    Record(Option<String>, Vec<(String, Expr)>),
    ResumedWith(Box<Expr>),
    ThisNode,
    Child(usize, String),
    ChildOf(Box<Expr>, String),
    ThisValue,
    NewTarget,
    Xref(String),
    Closure(usize),
    Table(String),
    Definition(String),
    TableStep(String, Box<Expr>),
    Data(DataLit),
    OfCond(Box<Cond>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pred {
    IsVal { neg: bool, neither: bool, vals: Vec<Expr> },
    IsTy { neg: bool, neither: bool, tys: Vec<TyExpr> },
    Call { callee: Callee, args: Vec<Expr>, neg: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    Preds(Expr, Pred, Vec<(Conj, Pred)>),
    Rel(RelOp, Expr, Expr),
    And(Vec<Cond>),
    Or(Vec<Cond>),
    Paren(Box<Cond>),
    Alg(AlgRef),
    Expr(Expr),
    Pass(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TyExpr {
    Sort { mods: Vec<String>, sort: String },
    ListOf(Box<TyExpr>),
    SeqOf(Box<TyExpr>),
    Union(Vec<TyExpr>),
    Completion(Option<Box<TyExpr>>),
    Interval(Box<TyExpr>, Expr, Expr),
    Value(Expr),
    Var(String),
    Nt(String),
    Record(Vec<(String, TyExpr)>),
    That(Box<TyExpr>, Pred, Vec<(Conj, Pred)>),
    Pred(Pred),
    ButNot(Box<TyExpr>, Box<TyExpr>),
    Doc(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    Var(String),
    Field(Expr, String),
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Body {
    Inline(Box<Stmt>),
    Block(Vec<Stmt>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub cond: Option<Cond>,
    pub body: Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let(String, Expr),
    Set(Place, Expr),
    Ret(Option<Expr>),
    Perform(Expr),
    If(Cond, Body, Vec<Arm>, Option<Arm>),
    IfElse(Cond, Box<Stmt>, Box<Stmt>),
    Assert(Cond),
    AssertAlways(Cond),
    AssertIf(Cond, Cond),
    Unreachable(u64),
    ThrowVal(Expr),
    Note(String),
    Repeat(Vec<Stmt>),
    RepeatWhile(Cond, Vec<Stmt>),
    RepeatUntil(Cond, Vec<Stmt>),
    ForEach { x: String, ty: Option<TyExpr>, list: Expr, rev: bool, body: Body },
    ForEachRec { fields: Vec<String>, x: String, list: Expr, body: Body },
    ForRange { x: String, lo: Expr, lo_incl: bool, hi: Expr, hi_incl: bool, desc: bool, body: Body },
    ForKeys { x: String, obj: Expr, cond: Cond, order: u64, body: Body },
    ForIndex { x: String, list: Expr, body: Body },
    ForChildren { x: String, body: Body },
    ForChildrenOf { x: String, expr: Expr, body: Body },
    RepeatN(Expr, Vec<Stmt>),
    Suspend(Expr, u64),
    Push(Expr, u64),
    Remove(Expr, u64),
    RemoveRestore(Expr, Expr),
    ResumeTop,
    ResumeLet { ctx: Expr, val: Expr, x: String },
    Resume(Expr, Expr),
    SetCodeState(Expr, Expr),
    Block(Vec<Stmt>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgKind {
    Ao,
    Sdo,
    Builtin,
    InternalMethod,
    ConcreteMethod,
    NumericMethod,
    HostDefined,
    ImplDefined,
    Untyped,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamDecl {
    pub x: String,
    pub ty: Option<TyExpr>,
    pub optional: bool,
    pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub kind: AlgKind,
    pub recv: Option<(String, TyExpr)>,
    pub params: Vec<ParamDecl>,
    pub ret: Option<TyExpr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CloKind {
    Abstract,
    Job,
    Matcher,
    MatcherContinuation,
    ReadModifyWrite,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CloLit {
    pub kind: CloKind,
    pub atomic: bool,
    pub params: Option<Vec<String>>,
    pub captures: Vec<String>,
    pub frame: Option<(String, String, String)>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgDef {
    pub id: AlgRef,
    pub name: String,
    pub header: Header,
    pub vars: Vec<String>,
    pub body: Vec<Stmt>,
    pub closures: Vec<CloLit>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowForm {
    Alg,
    Equation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SdoRowDef {
    pub id: AlgRef,
    pub sdo: String,
    pub form: RowForm,
    pub annex: bool,
    pub prods: Vec<String>,
    pub keys: Vec<String>,
    pub vars: Vec<String>,
    pub steps: Vec<Stmt>,
    pub closures: Vec<CloLit>,
}

// --- Declarations ---

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SortArg {
    Subject,
    Enum, // carries index? Wait: Enum(String)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SortTestArg {
    Subject,
    Enum(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SortTest {
    None,
    Alg(AlgRef),
    Prim { name: String, args: Vec<SortTestArg>, neg: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortDef {
    pub super_sorts: Vec<String>,
    pub record: bool,
    pub test: SortTest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrammarAltItem {
    Text(String),
    Cp(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeaderSlot {
    pub slot: usize,
    pub ty: Option<TyExpr>,
    pub optional: bool,
    pub rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SdoHeader {
    pub kind: AlgKind,
    pub recv: Option<(usize, TyExpr)>,
    pub params: Vec<HeaderSlot>,
    pub ret: Option<TyExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Clause { id: String, op: Option<String> },
    Field(String),
    Enum(String),
    Method(String),
    ExternDef { name: String, sig: Option<String>, meaning: Option<String> },
    Syntax { name: String, def: Option<SortDef> },
    Sdo { name: String, header: Option<SdoHeader>, default: Option<AlgRef> },
    CheckedJobs(Vec<String>),
    SortAlias { from: String, to: String },
    GrammarAlt { nt: String, items: Vec<GrammarAltItem> },
    ClauseProds { clause: String, prods: Vec<String> },
}

// --- Grammar ---

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GrammarId {
    NumericString,
    Lexical,
    Syntactic,
    RegExp,
    AnnexB,
    Json,
}

impl GrammarId {
    pub fn as_str(self) -> &'static str {
        match self {
            GrammarId::NumericString => "numericString",
            GrammarId::Lexical => "lexical",
            GrammarId::Syntactic => "syntactic",
            GrammarId::RegExp => "regExp",
            GrammarId::AnnexB => "annexB",
            GrammarId::Json => "json",
        }
    }
    pub fn lean_title(self) -> &'static str {
        match self {
            GrammarId::NumericString => "NumericString",
            GrammarId::Lexical => "Lexical",
            GrammarId::Syntactic => "Syntactic",
            GrammarId::RegExp => "RegExp",
            GrammarId::AnnexB => "AnnexB",
            GrammarId::Json => "JSON",
        }
    }
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "numericString" => Ok(GrammarId::NumericString),
            "lexical" => Ok(GrammarId::Lexical),
            "syntactic" => Ok(GrammarId::Syntactic),
            "regExp" => Ok(GrammarId::RegExp),
            "annexB" => Ok(GrammarId::AnnexB),
            "json" => Ok(GrammarId::Json),
            _ => Err(format!("unknown grammar id `{s}`")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminal {
    Text { text: String, alt: bool },
    Cp(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrammarSym {
    T(Terminal),
    Nt(String, Vec<NtArg>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LookItem {
    T(Terminal),
    NoLT,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lookahead {
    Eq(Vec<LookItem>),
    Ne(Vec<LookItem>),
    Mem(Vec<Vec<LookItem>>),
    NotMem(Vec<Vec<LookItem>>),
    NotMemNt(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exclusion {
    Sym(GrammarSym),
    OneOf { syms: Vec<GrammarSym>, or_sep: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrammarItem {
    Sym(GrammarSym, bool),
    Lookahead(Lookahead),
    NoLT,
    Empty,
    ButNot(GrammarSym, Exclusion),
    OnlyIf(String),
    Phrase(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alt {
    pub guard: Vec<ParamArg>,
    pub rhs: Vec<GrammarItem>,
    pub label: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Colons {
    One,
    Two,
    Three,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleBody {
    Alts(Vec<Alt>),
    OneOf(Vec<Vec<Terminal>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub grammar: GrammarId,
    pub lhs: String,
    pub params: Vec<String>,
    pub colons: Colons,
    pub body: RuleBody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockKind {
    Main,
    Supplemental(String),
    Overlay { section: String, mode: String, cond: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockDef {
    pub grammar: GrammarId,
    pub clause: String,
    pub kind: BlockKind,
    pub rules: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoalDef {
    pub nt: String,
    pub args: Vec<ParamArg>,
    pub src: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverDef {
    pub context: String,
    pub cover: String,
    pub refined: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemiDef {
    pub prod: String,
    pub pos: usize,
    pub kind: String,
}

// --- Early Errors ---

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnlessForm {
    Plain,
    Comma,
    Optional,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EarlySent {
    SyntaxError { early: bool, cond: Cond, unless: Option<(UnlessForm, Cond)> },
    SyntaxErrorIns(Cond, Cond),
    MustCover(Expr, TyExpr),
    RulesApplied(Vec<String>, String),
    IfInline(Cond, Box<EarlySent>),
    Info(Stmt),
    NotApplied(Cond, Stmt),
    ForEachIn { x: String, ty: TyExpr, list: Expr, cond: Cond, stmt: Stmt },
    Stmt(Stmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EarlyRow {
    pub id: AlgRef,
    pub sdo: String,
    pub modifies: bool,
    pub prods: Vec<String>,
    pub keys: Vec<String>,
    pub vars: Vec<String>,
    pub sentences: Vec<EarlySent>,
}

// --- Tables ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TTy {
    Ty(TyExpr),
    Records(Vec<(String, TyExpr)>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SigKind {
    Field,
    Method,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigParam {
    pub x: String,
    pub ty: TTy,
    pub optional: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sig {
    pub kind: SigKind,
    pub name: String,
    pub params: Vec<SigParam>,
    pub ret: TTy,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellBody {
    Field(String),
    Ty(TTy),
    Sig(Sig),
    Stmt(Stmt),
    Alg(AlgRef),
    Expr(Expr),
    Op(String),
    Component(String),
    Name(String),
    Lines(Vec<CellBody>),
    Dfn(Box<CellBody>),
    Code(Box<CellBody>),
    Link(String, Box<CellBody>),
    Raw(String),
    Text(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableCell {
    pub rowspan: usize,
    pub colspan: usize,
    pub body: CellBody,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableKind {
    Fields,
    Slots,
    InternalMethods,
    AbstractMethods,
    Components,
    Properties,
    Intrinsics,
    Conversion,
    Data,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableDef {
    pub name: String,
    pub body: Option<TableBody>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableBody {
    pub clause: String,
    pub idx: usize,
    pub kind: TableKind,
    pub thead: bool,
    pub caption: Option<String>,
    pub schema: Option<(String, bool)>,
    pub vars: Vec<String>,
    pub rows: Vec<Vec<TableCell>>,
}

// --- Realm ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RKey {
    Str(String),
    Sym(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RVal {
    Undefined,
    Null,
    Bool(bool),
    Str(String),
    Number(u64),
    Obj(usize),
    Sym(String),
    GlobalThis,
    Created(AlgRef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RAttrs {
    pub w: bool,
    pub e: bool,
    pub c: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RPVal {
    Data(RVal),
    Accessor(Option<usize>, Option<usize>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RProp {
    pub key: RKey,
    pub val: RPVal,
    pub attrs: RAttrs,
    pub clause: String,
    pub annex_b: bool,
    pub opt: bool,
    pub omittable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RKind {
    Ordinary,
    Exotic(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RFn {
    pub alg: Option<AlgRef>,
    pub len: usize,
    pub name: RKey,
    pub pfx: Option<String>,
    pub ctor: bool,
    pub is_async: bool,
    pub len_attrs: RAttrs,
    pub name_attrs: RAttrs,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RObj {
    pub idx: usize,
    pub path: String,
    pub clause: String,
    pub annex_b: bool,
    pub opt: bool,
    pub names: Vec<String>,
    pub keys: Vec<String>,
    pub kind: RKind,
    pub proto: Option<usize>,
    pub extensible: bool,
    pub slots: Vec<(String, RVal)>,
    pub fn_: Option<RFn>,
    pub props: Vec<RProp>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClauseProps {
    pub clause: String,
    pub props: Vec<RProp>,
}

// --- File Items & Top-Level Container ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopItem {
    Decl(Decl),
    Param(String),
    Nt(String),
    Block(BlockDef),
    Goal(GoalDef),
    Cover(CoverDef),
    Semi(SemiDef),
    Rule(Rule),
    Early(EarlyRow),
    Table(TableDef),
    Symbols(Vec<String>),
    RObj(RObj),
    ClauseProps(ClauseProps),
    Def(AlgDef),
    SdoRow(SdoRowDef),
    SpecModule(crate::spec_model::ast::SpecModule),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecFile {
    pub rel_path: String,
    pub header_comment: Option<String>,
    pub grammar_decl: Option<GrammarId>,
    pub items: Vec<TopItem>,
}

#[derive(Clone, Debug, Default)]
pub struct Spec {
    pub files: Vec<SpecFile>,
}
