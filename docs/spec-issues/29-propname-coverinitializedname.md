# 29. `({a = 1});`: the `__proto__` early error asks for the PropName of a CoverInitializedName, which has none

- **Location:** §13.2.5.1 Static Semantics: Early Errors (`#sec-object-initializer-static-semantics-early-errors`),
  the `__proto__` rule; §13.2.5.4 Static Semantics: PropertyNameList (`#sec-static-semantics-propertynamelist`),
  step 1 of the first row and step 2 of the second; §8.6.5 Static Semantics: PropName (`#sec-static-semantics-propname`).
- **Kind:** missing case (an operation applied to a production it does not define). Not observable: every text that
  reaches it has another early error.
- **Model erratum:** `PropNameCoverInitializedName`, baked-in SpecTec reading proposed (`spec/spectec/clauses/Helpers.spectec`,
  `@row-propname-coverinitializedname`, `@formal-protopropertycount`; `spec/spectec/08-early-errors.spectec`). Rather
  than leaving `PropName` undefined on `CoverInitializedName` (which stops with `sortError`), SpecTec adds the missing
  `PropName` row for `CoverInitializedName : IdentifierReference Initializer`, evaluates duplicate-`__proto__` counts via
  `@formal-protopropertycount`, and runs child early errors before parent rules.
- **Upstream:** Checked 2026-11-19: none found (searched for "CoverInitializedName" and "PropName"). Issue #2607
  (open, 2022-01), "Editorial: missing syntax error (involving CoverCallExpressionAndAsyncArrowHead)", is about
  another case of the CoverInitializedName rule, `f({x = 0})`.

## Text

§13.2.5.1:

> ObjectLiteral : `{` PropertyDefinitionList `,`? `}`
> - It is a Syntax Error if the PropertyNameList of |PropertyDefinitionList| contains any duplicate entries for
>   *"__proto__"* and at least two of those entries were obtained from productions of the form PropertyDefinition :
>   PropertyName `:` AssignmentExpression. …
>
> PropertyDefinition : CoverInitializedName
> - It is a Syntax Error if any source text is matched by this production.

PropertyNameList:

> PropertyDefinitionList : PropertyDefinition
> 1. Let _propertyName_ be the PropName of |PropertyDefinition|.

PropName has rows for `PropertyDefinition : IdentifierReference`, `PropertyDefinition : ... AssignmentExpression` and
`PropertyDefinition : PropertyName : AssignmentExpression`, and reaches MethodDefinition's rows through the chain
production `PropertyDefinition : MethodDefinition`. `PropertyDefinition : CoverInitializedName` is a chain production
too, but `CoverInitializedName : IdentifierReference Initializer` has two nonterminals and no row.

## Problem

An ObjectLiteral that contains a CoverInitializedName and is not reparsed as an ObjectAssignmentPattern, such as
`({a = 1});` as an ExpressionStatement, is subject to both rules above. The `__proto__` rule evaluates
PropertyNameList and with it the PropName of every PropertyDefinition, including the CoverInitializedName, whose
PropName the text does not define. Early errors are not ordered, so the rule's evaluation cannot be skipped because
the other rule already applies. The program is a SyntaxError by the CoverInitializedName rule in any case, so no output shows the gap, but the
`__proto__` rule has no value for it.

## Examples

[examples/29-propname-coverinitializedname.js](examples/29-propname-coverinitializedname.js) (outputs:
[RESULTS.md](examples/RESULTS.md#29-propname-coverinitializednamejs)) parses each source as a Script:

```js
var sources = ["({a = 1});", "({__proto__: 1, __proto__ = 2});", "({a = 1} = {});"];
for (var s of sources) {
  try { (0, eval)(s); print(JSON.stringify(s) + ": no error"); }
  catch (e) { print(JSON.stringify(s) + ": " + e.constructor.name); }
}
```

| | `({a = 1});` | `({__proto__: 1, __proto__ = 2});` | `({a = 1} = {});` |
|---|---|---|---|
| literal text | `SyntaxError`; the `__proto__` rule is undefined | likewise | no error (a pattern) |
| V8, SpiderMonkey, JavaScriptCore | `SyntaxError` | `SyntaxError` | no error |
| formal model (the row proposed below) | `SyntaxError` | `SyntaxError` | no error |

## Proposed wording

CoverInitializedName gets the name of its IdentifierReference, as the shorthand form does:

```diff
--- a/spec.html
+++ b/spec.html
@@ -10112,7 +10112,11 @@
       <h1>Static Semantics: PropName ( ): a String or ~empty~</h1>
       <dl class="header">
       </dl>
-      <emu-grammar>PropertyDefinition : IdentifierReference</emu-grammar>
+      <emu-grammar>
+        PropertyDefinition : IdentifierReference
+
+        CoverInitializedName : IdentifierReference Initializer
+      </emu-grammar>
       <emu-alg>
         1. Return the StringValue of |IdentifierReference|.
       </emu-alg>
```

Returning ~empty~, as for a spread, would do equally well: the name is never compared, because a
CoverInitializedName is not of the form the rule counts.

## test262

`language/expressions/object/cover-initialized-name.js`, a negative parse test of `({ a = 1 });`, reaches the gap; it
requires the SyntaxError, which the text gives through the CoverInitializedName rule whatever the `__proto__` rule
yields.
