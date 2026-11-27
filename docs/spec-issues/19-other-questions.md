# 19. Smaller questions: clarifications, editorial items, grammar

Each item below is an editorial error, a sentence that needs clarifying, or a grammar question that a parser
following the specification's grammar literally meets. None changes the behaviour of a program on the engines
tried.

- **Model erratum:** none; the model reads each sentence as the section says where it matters.
- **Upstream:** Checked 2026-11-19: none found for these questions (searched for "HostLoadImportedModule" with "same
  result", "ShallowestContainedJSONValue", "ECMA-404", "HostEnqueueTimeoutJob", "WeakRef" with "Execution", and
  "LR(1)").

## 19.2 HostLoadImportedModule's "the same result each time"

§16.2.1.10 / `#sec-HostLoadImportedModule`: "If this operation is called
multiple times with two (_referrer_, _moduleRequest_) pairs such that … and it
performs FinishLoadingImportedModule(_referrer_, _moduleRequest_, _payload_,
_result_) where _result_ is a normal completion, then it must perform
FinishLoadingImportedModule(…, _result_) with the same _result_ each time."
It does not say whether "each time" covers the calls made before the first
one that performed a normal completion (which may have performed a throw
completion). The formal model reads "each time" as every call. **Fix:** say
"each later time" (or "every time").

## 19.3 ShallowestContainedJSONValue and cover grammars

§25.5.2.5 ShallowestContainedJSONValue (`#sec-shallowestcontainedjsonvalue`) searches "the parse tree" of the Script
`(text);` breadth first. `(text)` is a
CoverParenthesizedExpressionAndArrowParameterList whose refinement is a
ParenthesizedExpression (§13.2.9.1, a separate parse of the same tokens). The
text does not say whether the search goes through the cover's own children or
through the refined Parse Node. The two find nodes of the same shape, so no
result differs today, but a later use of the node's identity would. **Fix:** a
note that the search descends into the refined ParenthesizedExpression.

## 19.4 ECMA-404 and surrogate code points

JSON.parse (§25.5.2) validates its text against ECMA-404 in ParseJSON
(§25.5.2.1, `#sec-ParseJSON`) step 1, after StringToCodePoints, which produces
lone surrogates as code points. ECMA-404 speaks of "code points", which by
Unicode's definition include surrogate code points, so a lone surrogate inside
a JSON string is accepted (the model accepts it: `JSON.parse('"\uD800"')` is a
String of the one code unit 0xD800). No test262 test decides it. **Fix:** a note that lone surrogates are
allowed in JSON strings.

## 19.6 A timeout that ends after the last time value

HostEnqueueTimeoutJob (§9.5.6) takes any "non-negative finite Number" of
milliseconds, up to 1.7976931348623157 × 10³⁰⁸, and §9.5 requires the Job to
be performed "At some future point in time". `Atomics.waitAsync(ia, 0, 0,
9e15)` asks for one 9 × 10¹⁵ ms later. When it runs,
EnqueueAtomicsWaitAsyncTimeoutJob (§25.4.3.15) step 1.b.i reads "the time
value (UTC) identifying the current time", but a time value supports only the
range up to 8.64 × 10¹⁵ ms (§21.4.1.1: "A time value supports a slightly
smaller range of -8,640,000,000,000,000 to 8,640,000,000,000,000
milliseconds"; see [10](10-utc-large-local-time.md)'s question on MakeDay
step 8 on what "supports" admits), so there is no supported time value; the
Job's Assert (1.b.ii) and Date.now() then have nothing to read. Engines simply
never get there. **Fix:** a note that a host need not perform a timeout Job
whose time is past the last time value (or that the current time is not
bounded by the time-value range). The formal model stops at its
implementation limit when its clock would pass the last time value:
`tests/run/clock_end_of_time.js` prints `stop: implLimit ? ?`.

## 19.7 Execution (§9.9.3, `#sec-weakref-execution`) step 1.b: which cell

> 1. For each element _value_ of _objSet_, do
>    b. For each FinalizationRegistry _finalizationRegistry_ such that _finalizationRegistry_.[[Cells]] contains a
>       Record _cell_ such that _cell_.[[WeakRefTarget]] is _value_, do
>       i. Set _cell_.[[WeakRefTarget]] to ~empty~.

A FinalizationRegistry can hold several cells with the same target (`fr.register(o, 1); fr.register(o, 2)`). Step 1.b
iterates over registries and binds one _cell_ in each, so read literally it empties one of the matching cells, and
which one is not said. The intent is every matching cell, which is how the model reads it. **Fix:** editorial: a For
each over the Records _cell_ of _finalizationRegistry_.[[Cells]] whose [[WeakRefTarget]] is _value_, around step
1.b.i.

## 19.8 Grammar questions

1. **`[no LineTerminator here]` inside a lookahead set.** ExpressionStatement's
   and ExportDeclaration's lookahead restrictions contain
   `` `async` [no LineTerminator here] `function` ``, but §5.1.6 defines the
   annotation only on the right-hand side of productions. The intended meaning
   (the restriction applies only when no line terminator separates the two
   tokens) is clear; it should be defined.
2. **§B.1.2 ordered choice.** "considered only if previous production
   alternatives do not match" does not say whether it means a complete Pattern
   parse or a local prefix match.
3. **§B.1.2 circular condition.** "but only if … ≤
   CountLeftCapturingParensWithin(…)" depends on the parse it constrains.
4. **§12 "permitted".** That the Div and RegExp goals (and `}` and
   TemplateTail) never both apply is stated only in the emu-note at the start of
   §12, which is not normative. Should it be? The model (`GoalsAt`) reads each
   token under the lexical goal its node in the derivation implies, evaluated
   after any inserted semicolon (`spec/DECISIONS.md`, `lexical-goal-parse-position`).
5. **Unambiguity.** ParseText (§11.1.6) step 4 ("the Parse Node") and §5.1.5's "unique
   for a given _p_" presume that the grammar is unambiguous, which the
   specification never states.
6. **§5.1.5 "must cover".** It does not say whether a semicolon inserted by
   ASI inside _p_ belongs to the "sequence of tokens originally matched by _p_".
   `GrammarCtx.CoverIs` keeps the virtual semicolons inside _p_ (`cover-matched-tokens`).
7. **Lexical goals of the other ParseText goals.** §12 does not state the
   starting lexical goal for CreateDynamicFunction's FormalParameters, body and
   expression goals; `GoalsAt` uses `InputElementHashbangOrRegExp` at offset 0
   only for |Script| and |Module|.
8. **§12.10 rules 1 and 3.** No input was found where rule 3 and a
   restriction-aware rule 1 differ (`ValidASI`, `asi-left-to-right`); not a
   defect as far as is known.
9. **Three places that are LR(2), not LR(1).** Each of these is a grammar-class
   question or an editorial one, not a defect: the grammar is unambiguous at
   all three, and the token after the next one always picks the parse.
   `spec-gen lr1` (`crates/spec-gen/src/lr1.rs`) builds the canonical LR(1)
   automaton of the syntactic grammar. In the goals that program text is
   parsed with, these are its only conflicts (shift/reduce, in 7 states);
   Annex B adds none.
   - **9a. `for ( using · of`** (Script, Module, generator bodies). When the
     parser has read `for ( using` and sees `of`, `using` can be two things:
     - an IdentifierReference, the LeftHandSideExpression of ForInOfStatement :
       `for` `(` [lookahead ∉ { `let`, `async` `of` }] LeftHandSideExpression
       `of` AssignmentExpression `)` Statement (§14.7.5,
       `#sec-for-in-and-for-of-statements`);
     - the start of UsingDeclaration : `using` BindingList `;` (§14.3.1,
       `#sec-let-and-const-declarations`), declaring `of`, in ForStatement :
       `for` `(` LexicalDeclaration … (§14.7.4, `#sec-for-statement`).

     The token after `of` decides: `=`, `,` or `;` means the declaration, and
     the start of an AssignmentExpression means the for-of.
     `for (using of = null;;) {}` declares `of`; `for (using of []) {}` assigns
     to `using`. The `[lookahead ≠ using of]` before ForDeclaration in §14.7.5 removes only the for-of
     ForDeclaration path (so that `for (using of of [0])` has one parse).
     *Fix:* no lookahead restriction keeps the language. On the
     LeftHandSideExpression path it would reject `for (using of []) {}`, and on
     the LexicalDeclaration path `for (using of = null;;) {}`, and both are
     valid today. One rewrite does keep the language and is LR(1) (checked with
     `spec-gen lr1`): add `using` `of` to that path's lookahead set, and add a
     production ForInOfStatement : `for` `(` `using` `of` AssignmentExpression
     `)` Statement. The cost is high, though. In the new production `using` is
     a token, not an IdentifierReference, so the production needs its own row
     in each of the 9 places that name `for` `(` LeftHandSideExpression `of`
     AssignmentExpression `)` Statement, and its own evaluation of the binding
     *"using"*. It is unlikely to be wanted.
   - **9b. `for ( await using · x`** (Module and async generator bodies, where
     [+Await] holds). Here x is any binding identifier: an IdentifierName that
     is not reserved, one of the 13 non-reserved words that the grammar names
     (`of`, `using`, `let`, …), or `await` or `yield`. The two readings are:
     - for(;;)'s AwaitUsingDeclaration : CoverAwaitExpressionAndAwaitUsingDeclarationHead
       BindingList `;` (§14.3.1). It reads `await using` as the cover `await`
       UnaryExpression (§13.5, `#sec-unary-operators`), so `using` is reduced to a UnaryExpression
       before x;
     - ForDeclaration : `await` `using` ForBinding (§14.7.5), the for-of path. It
       shifts x at once.

     The token after x decides: `=`, `,` or `;` against `of`.
     `for (await using x = null;;) {}` against `for (await using x of []) {}`.
     *Fix:* one rewrite keeps the language. Write that ForDeclaration
     alternative as [+Using, +Await]
     CoverAwaitExpressionAndAwaitUsingDeclarationHead [no LineTerminator here]
     ForBinding. Give it the refinement to AwaitUsingDeclarationHead (§14.3.1)
     and the early error "|CoverAwaitExpressionAndAwaitUsingDeclarationHead| must
     cover an |AwaitUsingDeclarationHead|" (§14.3.1.1,
     `#sec-let-and-const-declarations-static-semantics-early-errors`) that
     AwaitUsingDeclaration has. Both paths then reduce `using` the same
     way, and the grammar is LR(1) there (checked). The valid programs are the
     same; a text such as `for (await x y of z) {}` becomes an early error
     instead of failing to parse, which is a SyntaxError either way. The rows
     that name ForDeclaration : `await` `using` ForBinding (IsUsingDeclaration
     §8.2.4, IsAwaitUsingDeclaration §8.2.5, ForDeclarationBindingInitialization
     §14.7.5.3, ForDeclarationBindingInstantiation §14.7.5.4) take the cover
     form.
   - **9c. WithEntries' trailing comma** (Module; §16.2.2, `#sec-imports`). In
     `import "m" with { type: "json" ·,` the `,` either continues WithEntries :
     AttributeKey `:` StringLiteral `,` WithEntries (shift), or ends
     WithEntries before WithClause's optional `,` (reduce). The token after the
     `,` decides: an AttributeKey against `}`. `with { type: "json", }` against
     `with { type: "json", a: "b" }`. WithEntries is the only right-recursive
     comma list followed by an optional trailing comma. *Fix:* editorial, with
     the same language. Make it left-recursive, WithEntries : WithEntries `,`
     AttributeKey `:` StringLiteral, like BindingList (§14.3.1). This is LR(1)
     (checked). WithClauseToAttributes' two rows (§16.2.2.4) change to
     match.

   With all three rewrites, `spec-gen lr1` finds no conflict left in those goals,
   and each rewrite on its own removes only its own conflicts (the rewrites
   are proposed; each was applied to a copy of the pinned spec.html and
   checked).
