module

public import Ecma.State
public import Ecma.Prims.Strings
public import Ecma.Grammar.StrictCode

@[expose] public section

/-!
# Notation primitives: Parse Nodes and grammar symbols

The primitives `Known.pChild` … `Known.pInstanceOf` (`Known.pNodeContains` is the SDO Contains,
not a primitive; `Known.pChildOf`, through unit productions, is `progPrim`'s). A Parse Node is
seen only through `nodeProd`, `nodeChild` and `nodeKids`; what needs the grammar
itself (a production's left-hand side) or the Parse Node an SDO row runs at, which
no argument carries, stops with `.residue`; reparsing a cover (`Known.pCoveredBy`)
is `progPrim`'s. StrictModeCode and HasUseStrictDirective are §11.2.2's function (`Grammar.strictCode`) over
the nodes' nonterminals, children, spans and source text (`strictView`). `prim` dispatches by id.
-/

namespace Ecma.Prims.Nodes

variable {M : Model}

/-- §5.2.2: `the first |NT|`, `the second |NT|`, …: the child of the current production's Parse Node; a residue, the current Parse Node not being an argument. -/
def child : List (Val M) → Run M (Val M)
  | [_, _] => Run.stop .residue
  | _ => Run.stop .sortError

/-- §5.2.2: `this Parse Node`: the Parse Node the SDO row runs at; a residue, the current Parse Node not being an argument. -/
def thisNode : List (Val M) → Run M (Val M)
  | [] => Run.stop .residue
  | _ => Run.stop .sortError

/-- §5.1.2: `the grammar symbol |NT|`: the nonterminal itself, as a value. -/
def grammarSymbol : List (Val M) → Run M (Val M)
  | [.nt k as] => Run.pure (.nt k as)
  | _ => Run.stop .sortError

/-- §5.1.2: `node is an instance of S`: for a nonterminal S, node's own nonterminal is S (no unit
productions followed); for a terminal S, node is a terminal's Parse Node of S; `node is an
instance of the production P`: node's production is P; a Parse Node S (Contains of a Parse Node, B.3.2):
node is S. -/
def instanceOf : List (Val M) → Run M (Val M)
  | [.node n, .prod ps] => Run.pure (.bool (ps.contains (M.nodeProd n)))
  | [.node n, .nt k _] => Run.pure (.bool (M.nodeNt n == k))
  | [.node _, .term _] => Run.pure (.bool false)
  | [.leaf _ _ t, .term s] => Run.pure (.bool (t == s))
  | [.leaf .., .nt ..] | [.leaf .., .prod _] => Run.pure (.bool false)
  | [.node n, .node m] => Run.pure (.bool (Val.same (.node n) (.node m)))
  | [.leaf .., .node _] => Run.pure (.bool false)
  | [.node _, _] | [.leaf .., _] => Run.stop .residue
  | _ => Run.stop .sortError

/-- The grammar symbol a Parse Node is an instance of: its nonterminal, or its terminal. -/
def symbolOf : Val M → Option (Val M)
  | .node n => some (.nt (M.nodeNt n) [])
  | .leaf _ _ t => some (.term t)
  | _ => none

/-- §25.5.1: whether the Parse Node `n` lies in a Script being parsed for ParseJSON: its parser
invocation was ParseJSON's. -/
def inParseJSONScript : List (Val M) → Run M (Val M)
  | [.node n] => do return .bool ((← Run.get).jsonParses.contains (M.nodeStamp n))
  | _ => Run.stop .sortError

/-- §11.2.2: whether the Parse Node `n` is in source text that is strict mode code from outside (eval
code of a direct eval contained in strict mode code): its parser invocation was so. -/
def strictFromOutside : List (Val M) → Run M (Val M)
  | [.node n] => do return .bool ((← Run.get).strictParses.contains (M.nodeStamp n))
  | _ => Run.stop .sortError

/-- §5.1.6: whether the grammar parameter `p` was set when the Parse Node `n` was parsed. -/
def hasParam : List (Val M) → Run M (Val M)
  | [.node n, .param p] => return .bool ((M.nodeArgs n).any (·.ctorIdx == p))
  | _ => Run.stop .sortError

/-- The covering nodes around the parser invocation `k`, the nearest first: the node its parse was a reparse of
(§5.1.5), the node that node's parse was a reparse of, and so on. `cs` is the state's covers, the latest first: a
covering node's own invocation is earlier than the reparse of it. -/
def coversOf : List (Nat × M.Node) → Nat → List M.Node
  | [], _ => []
  | (st, c) :: cs, k => if st == k then c :: coversOf cs (M.nodeStamp c) else coversOf cs k

/-- The covering nodes around `n`'s parse (`coversOf`). -/
def coversAround (n : M.Node) : Run M (List M.Node) := do
  return coversOf (← Run.get).covers (M.nodeStamp n)

/-- The root of `n`'s parser invocation; a residue where that invocation recorded no root. -/
def rootOf (n : M.Node) : Run M M.Node := do
  match (← Run.get).roots[M.nodeStamp n]? with
  | some r => return r
  | none => Run.stop .residue

/-- §5.1.5: the goal symbol of the parse `n` is in: a cover's reparse is in the parse of its covering node; any
other invocation's, its root's nonterminal. -/
def goalOf (n : M.Node) : Run M (Val M) := do
  let r ← rootOf (((← coversAround n).getLast?).getD n)
  return .nt (M.nodeNt r) []

/-- GoalSymbolOf(n): `goalOf`. -/
def goalSymbolOf : List (Val M) → Run M (Val M)
  | [.node n] => goalOf n
  | _ => Run.stop .sortError

/-- §19.2.1.1: whether the Parse Node `n` is in eval code processed by a direct eval: its parser
invocation was PerformEval's with direct *true*. -/
def inDirectEval : List (Val M) → Run M (Val M)
  | [.node n] => do return .bool ((← Run.get).directParses.contains (M.nodeStamp n))
  | _ => Run.stop .sortError

/-- `src` with its code points `i` to `j` replaced by `rep`. -/
def splicePoints (src rep : M.Seq M.Math) (i j : Nat) : M.Seq M.Math :=
  let (k, acc) := M.seqFoldl (fun (st : Nat × M.Seq M.Math) x =>
      let acc := if st.1 == i then M.seqFoldl M.seqPush st.2 rep else st.2
      (st.1 + 1, if st.1 < i || j ≤ st.1 then M.seqPush acc x else acc)) (0, M.seqNil) src
  if k ≤ i then M.seqFoldl M.seqPush acc rep else acc

/-- B.3.3: the spans of `n`'s child |FunctionDeclaration|s, from `n`'s start. -/
def asIfSpans (n : M.Node) : List (Nat × Nat) :=
  let o := (M.nodeSpan n).1
  ((seqList (M.nodeKids n)).filter (M.nodeNt · == Grammar.NT.FunctionDeclaration.ctorIdx)).map
    fun c => ((M.nodeSpan c).1 - o, (M.nodeSpan c).2 - o)

/-- The point of `n`'s source at the point `p` of its B.3.3 source (`asIfSource`, a `{` before and a `}`
after each of `asIfSpans n`): `p` less the braces before it; `p` where `n` has no child |FunctionDeclaration|. -/
def asIfPoint (n : M.Node) (p : Nat) : Nat :=
  p - (asIfSpans n).zipIdx.foldl (fun d ((a, b), k) =>
    d + (if a + 2 * k < p then 1 else 0) + (if b + 2 * k + 1 < p then 1 else 0)) 0

/-- The source text of the root of `n`'s parser invocation, its code points `i` to `j` replaced by
`rep`: a cover's reparse is the covering node's source text in its own parse, without the braces of B.3.3's
processing as an |IfStatement| (`asIfPoint`; no covering node of another cover has a child |FunctionDeclaration|),
so the points are carried out through the covering nodes. -/
def replacedIn (rep : M.Seq M.Math) (n : M.Node) (i j : Nat) : Run M (Val M) := do
  let (m, i, j) := (← coversAround n).foldl (fun (_, i, j) c =>
    (c, (M.nodeSpan c).1 + asIfPoint c i, (M.nodeSpan c).1 + asIfPoint c j)) (n, i, j)
  let r ← rootOf m
  if (M.nodeSpan r).1 ≤ i && i ≤ j && j ≤ (M.nodeSpan r).2 then
    return .ref (← alloc (.list (M.seqFoldl (fun acc x => M.seqPush acc (.math x)) M.seqNil
      (splicePoints (M.nodeSource r) rep (i - (M.nodeSpan r).1) (j - (M.nodeSpan r).1))) 0))
  else Run.stop .residue

/-- ReplacedSourceText(n, t): a new List of the code points of the source text of the parse that
made `n`, through every cover, with the source text `n` matched replaced by the String `t`'s. -/
def replacedSourceText : List (Val M) → Run M (Val M)
  | [.node n, .str t] =>
    replacedIn (Prims.Strings.strPoints t) n (M.nodeSpan n).1 (M.nodeSpan n).2
  | _ => Run.stop .sortError

/-- The Parse Node the first of the covering nodes `cs` that is no root is a child of; none where each is the
root of its parse. -/
def parentAmong : List M.Node → Run M (Option M.Node)
  | [] => return none
  | c :: cs => do
    let r ← rootOf c
    if Val.same (.node r) (.node c) then parentAmong cs
    else match M.nodeParent r c with
      | some p => return some p
      | none => Run.stop .residue

/-- The Parse Node of which `n` is a child: in the tree of the parser invocation that made `n`; for the root of
a cover's reparse, the covering node's parent, which it stands in place of; none for the root of any other
parse; a residue where that invocation recorded no root or its tree lacks `n`. -/
def parentOf (n : M.Node) : Run M (Option M.Node) := do
  let r ← rootOf n
  if Val.same (.node r) (.node n) then parentAmong (← coversAround n)
  else match M.nodeParent r n with
    | some p => return some p
    | none => Run.stop .residue

/-- The nearest node of the nonterminals `ks` that contains `n` in the tree of `n`'s parse; a residue where
that tree lacks `n`. -/
def enclosingIn (ks : List NtId) (n : M.Node) : Run M (Option M.Node) := do
  let r ← rootOf n
  if Val.same (.node r) (.node n) then return none
  match M.nodeAncestors r n with
  | [] => Run.stop .residue
  | ps => return ps.find? fun p => ks.contains (M.nodeNt p)

/-- The nearest node of the nonterminals `ks` that contains the first of the covering nodes `cs`, else the
next. -/
def enclosingAmong (ks : List NtId) : List M.Node → Run M (Val M)
  | [] => return .enum Known.eEmpty
  | c :: cs => do
    match ← enclosingIn ks c with
    | some p => return .node p
    | none => enclosingAmong ks cs

/-- Parent(n): the Parse Node of which `n` is a child node; `n` has one. A terminal's Parse Node is
a child of the node it was read from. -/
def parent : List (Val M) → Run M (Val M)
  | [.node n] => do
    match ← parentOf n with
    | some p => return .node p
    | none => Run.stop .assertFailed
  | [.leaf p _ _] => return .node p
  | _ => Run.stop .sortError

/-- NearestEnclosing(n, ss): the nearest Parse Node that contains `n` and is an instance of one of
the nonterminals of the List `ss`; ~empty~ if there is none. -/
def nearestEnclosing : List (Val M) → Run M (Val M)
  | [.node n, .ref a] => do
    match ← readCell a with
    | .list ss _ =>
      let ks := M.seqFoldl (fun acc v => match v with | .nt k _ => k :: acc | _ => acc) [] ss
      match ← enclosingIn ks n with
      | some p => return .node p
      | none => enclosingAmong ks (← coversAround n)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The model's Parse Nodes as §11.2.2 reads them (`Grammar.NodeView`). -/
def strictView (M : Model) : Grammar.NodeView M.Node where
  isA n k := M.nodeNt n == k.ctorIdx
  kids n := seqList (M.nodeKids n)
  span := M.nodeSpan
  textIs n cs := M.seqFoldl (fun (rest : Option (List Nat)) x => match rest with
    | some (c :: r) => if M.eq x (M.ofNat c) then some r else none
    | _ => none) (some cs) (M.nodeSource n) == some []
  height := M.nodeHeight

/-- The Parse Nodes that contain `n` in the tree of its parse, the nearest first; none for its root; a residue
where that tree lacks `n`. -/
def ancestorsIn (n : M.Node) : Run M (List M.Node) := do
  let r ← rootOf n
  if Val.same (.node r) (.node n) then return []
  match M.nodeAncestors r n with
  | [] => Run.stop .residue
  | ps => return ps

/-- The Parse Nodes that contain the covering nodes `cs`, each in the tree of its parse, the first's nearest
first. -/
def ancestorsAmong : List M.Node → Run M (List M.Node)
  | [] => return []
  | c :: cs => do return (← ancestorsIn c) ++ (← ancestorsAmong cs)

/-- The Parse Nodes that contain `n`, the nearest first, through every cover: those in the tree of its parse, then
those that contain the covering node its parse is a reparse of (in whose place its root stands), and so on. -/
def ancestorsOf (n : M.Node) : Run M (List M.Node) := do
  return (← ancestorsIn n) ++ (← ancestorsAmong (← coversAround n))

/-- StrictModeCode(n): §11.2.2, the source text `n` matched is strict mode code: from outside, its parser
invocation having been so, or by the tree it is in, through every cover (`Grammar.strictCode` over the model's
Parse Nodes). -/
def strictModeCode : List (Val M) → Run M (Val M)
  | [.node n] => do
    if (← Run.get).strictParses.contains (M.nodeStamp n) then return .bool true
    return .bool (Grammar.strictCode (strictView M) (← ancestorsOf n) n)
  | _ => Run.stop .sortError

/-- HasUseStrictDirective(body): §11.2.1, the Directive Prologue of `body` contains a Use Strict Directive
(`Grammar.prologueStrict` over the model's Parse Nodes). -/
def hasUseStrictDirective : List (Val M) → Run M (Val M)
  | [.node n] => return .bool (Grammar.prologueStrict (strictView M) n)
  | _ => Run.stop .sortError

/-- ParseNodesWithin(node): a new List of `node` and its descendants (`nodeDescendants`, the Parse Nodes of
nonterminals it contains, a node before its children); « node » for a terminal's Parse Node. -/
def parseNodesWithin : List (Val M) → Run M (Val M)
  | [.node n] => listOf (.node n :: (M.seqFoldl (fun acc d => .node d :: acc) [] (M.nodeDescendants n)).reverse)
  | [v@(.leaf ..)] => listOf [v]
  | _ => Run.stop .sortError

/-- §5.1: whether `v` is a nonterminal symbol. -/
def isNonterminal : List (Val M) → Run M (Val M)
  | [v] => Run.pure (.bool (v matches .nt ..))
  | _ => Run.stop .sortError

/-- §5.1: whether `v` is a terminal or nonterminal symbol. -/
def isGrammarSymbol : List (Val M) → Run M (Val M)
  | [v] => Run.pure (.bool (v matches .nt .. | .term _))
  | _ => Run.stop .sortError

/-- The primitives of Parse Nodes and grammar symbols, by id; `none` for any other id. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pChild then some (child vs)
  else if p == Known.pThisNode then some (thisNode vs)
  else if p == Known.pGrammarSymbol then some (grammarSymbol vs)
  else if p == Known.pInstanceOf then some (instanceOf vs)
  else if p == Known.pIsNonterminal then some (isNonterminal vs)
  else if p == Known.pInParseJSONScript then some (inParseJSONScript vs)
  else if p == Known.pStrictFromOutside then some (strictFromOutside vs)
  else if p == Known.pHasParam then some (hasParam vs)
  else if p == Known.pGoalSymbolOf then some (goalSymbolOf vs)
  else if p == Known.pInDirectEval then some (inDirectEval vs)
  else if p == Known.pReplacedSourceText then some (replacedSourceText vs)
  else if p == Known.pParent then some (parent vs)
  else if p == Known.pNearestEnclosing then some (nearestEnclosing vs)
  else if p == Known.pIsGrammarSymbol then some (isGrammarSymbol vs)
  else if p == Known.pStrictModeCode then some (strictModeCode vs)
  else if p == Known.pHasUseStrictDirective then some (hasUseStrictDirective vs)
  else if p == Known.pParseNodesWithin then some (parseNodesWithin vs)
  else none

end Ecma.Prims.Nodes
