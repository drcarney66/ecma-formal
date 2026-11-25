//! Structured AST for SpecTec prose specification modules (`spec/spectec/prose/`).

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecModule {
    pub target_module: String,
    pub imports: Vec<String>,
    pub items: Vec<MItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MItem {
    ModDoc(String),
    Namespace { name: String, items: Vec<MItem> },
    Section { name: Option<String>, items: Vec<MItem> },
    Mutual { items: Vec<MItem> },
    Open(Vec<String>),
    Var(Vec<MBinder>),
    Syntax(MSyntax),
    Relation(MRel),
    Laws(MLaws),
    Def(MDef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MRelBoundOp {
    Lt,
    Le,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MBinder {
    Explicit { names: Vec<String>, ty: Option<MExpr> },
    Implicit { names: Vec<String>, ty: Option<MExpr> },
    Bare(String),
    In { name: String, coll: MExpr },
    Rel { name: String, op: MRelBoundOp, bound: MExpr },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MSyntax {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub body: MSyntaxBody,
    pub deriving: Vec<String>,
    pub default_inhabited: Option<(MExpr, MExpr)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MSyntaxBody {
    Variant(Vec<MVariantCase>),
    Record(Vec<MRecordField>),
    Alias(MExpr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MVariantCase {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MRecordField {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub ty: MExpr,
    pub default: Option<MExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MRel {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub sig: MExpr,
    pub rules: Vec<MRelRule>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MRelRule {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub conclusion: MExpr,
    pub premises: Vec<MExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MLaws {
    pub doc: Option<String>,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub extends: Vec<MExpr>,
    pub laws: Vec<MLaw>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MLaw {
    pub doc: Option<String>,
    pub name: String,
    pub prop: MExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MDef {
    pub doc: Option<String>,
    pub inline: bool,
    pub name: String,
    pub binders: Vec<MBinder>,
    pub ty: Option<MExpr>,
    pub body: MDefBody,
    pub where_defs: Vec<MDef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MDefBody {
    Expr(MExpr),
    Clauses(Vec<MMatchArm>),
    Struct(Vec<MStructDefField>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MStructDefField {
    Val {
        name: String,
        binders: Vec<MBinder>,
        val: MExpr,
    },
    Clauses {
        name: String,
        arms: Vec<MMatchArm>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MMatchArm {
    pub alts: Vec<Vec<MPat>>,
    pub rhs: MExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MLit {
    Int(u64),
    Hex(String),
    Str(String),
    Char(char),
    Bool(bool),
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MPat {
    Wild,
    Dots,
    Var(String),
    Lit(MLit),
    Tag(String, Vec<MPat>),
    Ctor(String, Vec<MPat>),
    Tuple(Vec<MPat>),
    AnonCtor(Vec<MPat>),
    List(Vec<MPat>),
    Cons(Box<MPat>, Box<MPat>),
    AddNat(String, u64),
    Or(Vec<MPat>),
    As(String, Box<MPat>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MUnOp {
    Neg,
    BoolNot,
    PropNot,
    Bind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MBinOp {
    Pow,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    Append,
    Cons,
    Times,
    Sum,
    BoolEq,
    BoolNe,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    In,
    NotIn,
    BoolAnd,
    BoolOr,
    And,
    Or,
    Iff,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MQuant {
    Forall,
    Exists,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MArg {
    Pos(MExpr),
    Named(String, MExpr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MFunParam {
    Pat(MPat),
    Explicit { names: Vec<String>, ty: MExpr },
    Implicit { names: Vec<String>, ty: Option<MExpr> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MDoStmt {
    LetBind {
        pat: MPat,
        ty: Option<MExpr>,
        val: MExpr,
    },
    LetPure {
        pat: MPat,
        ty: Option<MExpr>,
        val: MExpr,
    },
    Return(MExpr),
    If {
        cond: MExpr,
        then_branch: Vec<MDoStmt>,
        else_branch: Option<Vec<MDoStmt>>,
    },
    Expr(MExpr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MExpr {
    Ident(String),
    Tag(String),
    Lit(MLit),
    Proj(Box<MExpr>, String),
    Call(Box<MExpr>, Vec<MArg>),
    Index(Box<MExpr>, Box<MExpr>),
    IndexOpt(Box<MExpr>, Box<MExpr>),
    List(Vec<MExpr>),
    Tuple(Vec<MExpr>),
    AnonCtor(Vec<MExpr>),
    StructLit {
        base: Option<Box<MExpr>>,
        fields: Vec<(String, Option<MExpr>)>,
    },
    UnOp(MUnOp, Box<MExpr>),
    BinOp(MBinOp, Box<MExpr>, Box<MExpr>),
    Arrow {
        binder: Option<Box<MBinder>>,
        dom: Option<Box<MExpr>>,
        cod: Box<MExpr>,
    },
    Quant(MQuant, Vec<MBinder>, Box<MExpr>),
    Fun(Vec<MFunParam>, Box<MExpr>),
    FunCases(Vec<MMatchArm>),
    Let {
        pat: MPat,
        binders: Vec<MBinder>,
        ty: Option<Box<MExpr>>,
        val: Box<MExpr>,
        body: Box<MExpr>,
    },
    If(Box<MExpr>, Box<MExpr>, Box<MExpr>),
    Match(Vec<MExpr>, Vec<MMatchArm>),
    Matches(Box<MExpr>, MPat),
    Do(Vec<MDoStmt>),
    Ascribe(Box<MExpr>, Box<MExpr>),
}
