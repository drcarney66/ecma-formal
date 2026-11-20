//! The data: a mirror of `Ecma.Notation.Syntax` (lean/Ecma/Notation/Syntax.lean),
//! constructor for constructor. Names are interned ids into `Decls`.

pub type Id = usize;

#[derive(Clone, Debug, PartialEq)]
pub struct Attr {
    pub key: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum XrefForm {
    Plain,
    Title,
    Content(String),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sub {
    None,
    F,
    Z,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Numeral {
    Dec(u128),
    Hex(u128, String),
    /// whole part, fraction digits as a number, their count
    Frac(u128, u128, usize),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sign {
    None,
    Plus,
    Minus,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Mag {
    Num(Numeral),
    Inf,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ValLit {
    Undefined,
    Null,
    True,
    False,
    /// the text decoded, and as written where it is not the text re-escaped (`text::literal`)
    Str(String, String),
    NaN(Sub),
    Num(Sign, Mag, Sub),
    /// `*this*`
    This,
    /// an error constructor's name: `*TypeError*`
    Err(Id),
    /// a BigInt in ECMAScript source notation: `` `1n` ``
    BigN(Numeral),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Article {
    The,
    None,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AltForm {
    Either,
    OneOf,
    Or,
    Neither,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ConnForm {
    Plain,
    Comma,
    /// `c1, or if c2`
    OrIf,
    /// `both of the following conditions are true: c1 and c2` (`all`, `any` for more, for or)
    Following,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Conj {
    And,
    Or,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Modulo,
    Pow,
    /// `plus`, as an equation writes `+`
    Plus,
    /// `times`, as an equation writes `×`
    Times,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RelOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Callee {
    /// an operation, by the clause that defines it
    Alg(Id),
    Prim(Id),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Channel {
    Pending,
    /// (a) a spec-issue reason (`Decls.reasons`), and the primitive meaning it meanwhile
    Upstream(Id, Option<Id>),
    /// (b) a declared primitive, and whether the prose's holes are its arguments (`residue::unwired`)
    Prim(Id, bool),
    /// (c) annotated prose of a kind (`Decls.notes`), and its primitive
    Annotated(Id, Option<Id>),
}

/// A reading of an erratum's step.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Reading {
    Literal,
    Test262,
    Proposed,
    /// a reading the overlay gives for prose steps (`<emu-reading steps=…>`), always applied
    Definition,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CloKind {
    Abstract,
    Job,
    Matcher,
    MatcherContinuation,
    ReadModifyWrite,
}

/// How a list of expressions is written.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ListForm {
    /// `(a, b)`
    Paren,
    /// `a, b`
    Comma,
    /// `a and b`, `a, b, and c` (or `or`)
    English(Conj),
    /// continuation lines `* a`
    Bullets,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Var(Id),
    Val(ValLit),
    Math(Sign, Mag),
    Enum(Id),
    Intrinsic(Id),
    FieldName(Id),
    /// `|NT[+P, ~Q]|`: a grammar symbol and its parameters (ParamId, `+`)
    Nt(Id, Vec<(usize, bool)>),
    /// a grammatical parameter, `<sub>[Yield]</sub>`
    Param(Id),
    Prod(Vec<Id>, String),
    CodeUnit(u128, String, Option<String>),
    CodePoint(u128, String, Option<String>),
    /// the code decoded, and as written where it is not the code re-escaped (`text::literal`)
    Code(String, String),
    /// a code literal that stands for a terminal grammar symbol: `` `super` ``
    Term(String),
    Call(Callee, Vec<Expr>),
    Sdo(Id, Article, Box<Expr>, Vec<Expr>),
    Component(Id, Article, Box<Expr>),
    Field(Box<Expr>, Id),
    IMethod(Box<Expr>, Id, Vec<Expr>),
    CMethod(Box<Expr>, Id, Vec<Expr>),
    Apply(Box<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Q(Box<Expr>),
    Bang(Box<Expr>),
    /// `! e` at a site of the erratum (readings.emu `stops=`)
    BangAt(usize, Box<Expr>),
    /// an expression at a site of the erratum: its failed checks, and its sort errors when the flag is
    /// set (a field chain), stop as the erratum
    Erratum(usize, bool, Box<Expr>),
    Neg(Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Paren(Box<Expr>),
    List(Vec<Expr>),
    /// `[the] [Kind] { [[F]]: e, … }`
    Record(Article, Option<Id>, Vec<(Id, Expr)>),
    Annot(Vec<Attr>, Box<Expr>),
    /// href, form, the clause the href names
    Xref(String, XrefForm, Option<Id>),
    /// an Abstract Closure literal: its index in the algorithm's closure table
    Closure(usize),
    /// an `emu-xref` to an `emu-table`: the table, by its index among the emitted tables, and the xref
    Table(usize, Box<Expr>),
    /// `the definition specified in <xref>`: the algorithm of the clause the xref names; true when
    /// written `Set _p_ as specified in <xref>`
    Definition(Box<Expr>, bool),
    /// `the value that _x_ corresponds to in <table>`: the table, the key, the xref
    TableStep(usize, Box<Expr>, Box<Expr>),
    /// `the largest T _x_ (closest to +∞) such that c` (true), or `the smallest … (closest to -∞) …`
    Extreme(bool, Id, Box<TyExpr>, Box<Cond>),
    /// `the Completion Record with which _ctx_ was just resumed`
    ResumedWith(Box<Expr>),
    /// `the *this* value` (true: `*this* value`)
    ThisValue(bool),
    NewTarget,
    /// `this Parse Node`
    ThisNode,
    /// `the first |X|` … (0–2), `the derived |X|` (3), `the |X|` (4)
    Child(usize, Id, String),
    /// a bare `|X|` inside `If |Y| is <emu-grammar>P</emu-grammar>`, `X` on P's right-hand
    /// side: the child of `|Y|`'s node
    ChildOf(Box<Expr>, Id, String),
    Phrase(Id, Vec<Hole>),
    Prose(Channel, Vec<Part>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pred {
    IsVal(bool, AltForm, Vec<Expr>),
    IsTy(bool, AltForm, Vec<TyExpr>),
    Phrase(Id, Vec<Hole>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cond {
    /// a subject and predicates sharing it: `e is finite and is not v`
    Preds(Expr, Pred, Vec<(Conj, Pred)>),
    Rel(RelOp, Expr, Expr),
    And(ConnForm, Vec<Cond>),
    Or(ConnForm, Vec<Cond>),
    Paren(Box<Cond>),
    /// `the following algorithm returns *true*: <emu-alg>…</emu-alg>`: the algorithm by
    /// clause and index, and its element as written
    Alg(Id, usize, String),
    Phrase(Id, Vec<Hole>),
    Prose(Channel, Vec<Part>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr {
    /// article (as written, possibly empty), modifiers, sort, and the sort's words as
    /// written where they are another form of its name (a plural), else empty
    Sort(String, Vec<Id>, Id, String),
    ListOf(String, Box<TyExpr>),
    Union(AltForm, ConnForm, Vec<TyExpr>),
    Completion(Option<Box<TyExpr>>),
    Interval(Box<TyExpr>, Expr, Expr),
    Value(Expr),
    /// `a _t_`: the type a type hole holds; the article as written
    Var(String, Id),
    Nt(String, Id, String),
    Record(Vec<(Id, TyExpr)>),
    /// `a T that P and Q`
    That(Box<TyExpr>, Pred, Vec<(Conj, Pred)>),
    Phrase(Id, Vec<Hole>),
    Prose(Vec<Part>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Hole {
    E(Expr),
    C(Cond),
    T(TyExpr),
    B(Id),
    /// a condition over the variables the phrase binds, in the template's order
    Bc(Vec<Id>, Cond),
    W(usize),
    L(ListForm, Vec<Expr>),
    Text(String),
    /// words naming a field or component, as written
    Field(Id),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Part {
    Text(String),
    Hole(Hole),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Place {
    Var(Id),
    Field(Expr, Id),
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Body {
    Inline(Box<Stmt>),
    Block(Vec<Node>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Arm {
    pub attrs: Vec<Attr>,
    pub cond: Option<Cond>,
    pub body: Body,
}

/// How an early-error rule writes its exception.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnlessForm {
    /// ` unless c`
    Plain,
    /// `, unless c`
    Comma,
    /// `<span normative-optional>, unless c</span>`
    Optional,
}

/// How an Early Errors bullet sits in its `<li>`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LiLayout {
    /// `<li>R</li>`
    Inline,
    /// `<li>`, R on its own line two columns in, `</li>` at the `<li>`'s column
    Block,
    /// any other layout: the content is one prose statement, verbatim
    Raw,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Let(Id, Expr),
    Set(Place, Expr),
    Ret(Option<Expr>),
    Perform(Expr),
    If(Cond, Body, Vec<Arm>, Option<Arm>),
    IfElse(Cond, Box<Stmt>, Box<Stmt>),
    Assert(Cond),
    /// `Assert: c` at a site of the erratum
    AssertAt(Option<usize>, Cond),
    AssertIf(Cond, Cond),
    Unreachable(usize),
    ThrowErr(Id),
    ThrowVal(Expr),
    Note(Vec<Part>),
    Repeat(Vec<Node>),
    RepeatWhile(Cond, Vec<Node>),
    RepeatUntil(Cond, Vec<Node>),
    /// variable, type (typed form), list, reverse, body
    ForEach(Id, Option<TyExpr>, Expr, bool, Body),
    ForEachRec(Vec<Id>, Id, Expr, Body),
    Mutate(Id, Vec<Hole>),
    /// variable, type, condition, order (0 ascending, 1 descending), body
    ForSuchThat(Id, TyExpr, Cond, Option<usize>, Body),
    /// variable, object, condition, order, body
    ForKeys(Id, Expr, Cond, usize, Body),
    ForIndex(Id, Expr, Body),
    ForChildren(Id, Body),
    /// `For each child node _x_ of E, do`
    ForChildrenOf(Id, Expr, Body),
    RepeatN(Expr, Vec<Node>),
    /// variable, lo, lo inclusive, hi, hi inclusive, descending, body
    ForRange(Id, Expr, bool, Expr, bool, bool, Body),
    /// `Return e (see xref).`
    RetSee(Expr, Expr),
    Macro(Id, Vec<Expr>),
    Suspend(Expr, usize),
    Push(Expr, usize),
    Remove(Expr, usize),
    RemoveRestore(Expr, Expr),
    ResumeTop,
    ResumeLet(Expr, Expr, Id, Vec<Attr>),
    Resume(Expr, Expr),
    SetCodeState(Expr, Expr),
    /// a step with an erratum: the erratum, the pinned step, the other readings' steps
    Readings(usize, Box<Stmt>, Vec<(Reading, Vec<Node>)>),
    /// `Find T _x_ such that c; but if this is not possible (reason), s.`
    FindSuchThat(Id, TyExpr, Cond, String, Box<Stmt>),
    /// `Let _x_, …, and _z_ be integers such that c, choosing them so that e is as small as
    /// possible, then so that …`: the variables, the condition, the objectives (true: large)
    LetSuchThat(Vec<Id>, Cond, Vec<(bool, Expr)>),
    /// `It is a Syntax Error if c` (`true`: "It is an early Syntax Error if c"), and its exception
    SyntaxError(bool, Cond, Option<(UnlessForm, Cond)>),
    Phrase(Id, Vec<Hole>),
    Prose(Channel, Vec<Part>),
    /// a phrase, mutation or prose step and its nested steps, which its form does not take
    WithSteps(Box<Stmt>, Vec<Node>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    pub attrs: Vec<Attr>,
    pub stmt: Stmt,
}

/// An Abstract Closure literal of an algorithm's table.
#[derive(Clone, Debug, PartialEq)]
pub struct CloLit {
    pub kind: CloKind,
    pub atomic: bool,
    /// None: "with no parameters"
    pub params: Option<Vec<Id>>,
    pub caps: Vec<Id>,
    pub body: Vec<Node>,
    /// the call's *this* value, NewTarget and arguments List slots, when the body reads them
    pub frame: Option<(Id, Id, Id)>,
}
