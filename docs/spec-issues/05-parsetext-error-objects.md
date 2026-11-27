# 05. ParseText creates *SyntaxError* objects without a realm

- **Location:** §11.1.6 Static Semantics: ParseText (`#sec-parsetext`), step 5; §22.2.3.4 Static Semantics:
  ParsePattern (`#sec-parsepattern`), step 1.a, and its §B.1.2.9 version (`#sec-parsepattern-annexb`).
- **Kind:** missing context and undefined sort (`error`).
- **Model erratum:** `ParseTextErrorObjects`, baked-in SpecTec reading proposed (`spec/spectec/clauses/Helpers.spectec`,
  `@formal-parsetextin`, `@ph-syntax-errors`, `@sort-error`; `lean/Ecma/Lower/LinEarly.lean`, `newSyntaxError`).
  Rather than following the literal text (which leaves the Realm Record unspecified when creating *SyntaxError* objects
  and tests an undefined sort `error` in ten caller steps), SpecTec bakes in three choices: (1) `@formal-parsetextin`,
  `ParsePattern` and early-error rules allocate a singleton *SyntaxError* object in `currentRealm`; (2) the test host
  (`lean/Engine/Host/Opts.lean`) pushes an execution context for the target realm before top-level `ParseScript` and
  `ParseModule` so `currentRealm` is defined on an otherwise empty stack; and (3) `@sort-error` defines `"error"` as an
  `Object` with an `[[ErrorData]]` internal slot (`tc39/ecma262#3868`) so `ToNumber("x")`, `BigInt("x")` and other
  `ParseText` callers do not stop on an undefined sort.
- **Upstream:** Checked 2026-11-19: none found that reports it (searched for "ParseText" with realm and with
  SyntaxError). Issue #3868 (open, 2026-05), "How should ParseText results be consumed?", asks how callers test the
  result, not where its objects are created; issue #1462 (open, 2019-03), "Current Realm record when creating new
  objects in [[Construct]]", asks the same realm question of the objects [[Construct]] creates. ParseText's NOTE, now
  step 3, came with PR #3956 (merged 2026-10, commit 21e4774e4).

## Text

> 5. Return a List of one or more *SyntaxError* objects representing the parsing errors and/or early errors. If more
>    than one parsing error or early error is present, the number and ordering of error objects in the list is
>    implementation-defined, but at least one must be present.

ParsePattern:

> 1. If _v_ is *true* and _u_ is *true*, then
>    a. Let _parseResult_ be a List containing one or more *SyntaxError* objects.

## Problem

ParseText is a static semantics, but creating an object changes an agent's state, and a *SyntaxError* object
belongs to a realm: its [[Prototype]] is some realm's %SyntaxError.prototype%. The text says neither which realm nor
when the objects come into existence. A host may call ParseScript or ParseModule while no execution context is
running, when there is no current Realm Record. ParseScript and ParseModule have a _realm_ parameter, but ParseText
is not given it.

ParseText also runs inside ordinary operations: StringToNumber (`Number("x")`), StringToBigInt, ParseHexOctet
(`decodeURI`), IsTimeZoneOffsetString, and, by ParsePattern, IsValidRegularExpressionLiteral. Read literally, each
failed parse there creates objects that nothing uses. No algorithm of the specification reads an object from the
List: PerformEval, CreateDynamicFunction and RegExpInitialize throw a new *SyntaxError* of their own, Decode throws a
*URIError*, and StringToNumber, StringToBigInt, IsTimeZoneOffsetString and IsValidRegularExpressionLiteral return
*NaN*, *undefined* or *false*. (parseFloat, ParseJSON and ParseTimeZoneOffsetString assert that their parse
succeeds.) Only ParseScript and ParseModule pass the List out, to the host, and the host needs objects
there: HTML's "create a classic script" and "create a JavaScript module script" store the List's first
element as the script's parse error and rethrow it.

So the objects matter only at ParseScript and ParseModule, which know their realm. The proposed change: ParseText and
ParsePattern return errors, and those two operations create the objects in _realm_.

## Examples

[examples/05-parsetext-error-objects.js](examples/05-parsetext-error-objects.js) (outputs:
[RESULTS.md](examples/RESULTS.md#05-parsetext-error-objectsjs)) shows the errors that are observable, each caller's
own *SyntaxError* from the current realm:

```js
try { eval("var x = ;"); } catch (e) { print(e instanceof SyntaxError); }
try { Function("a", "return a +;"); } catch (e) { print(e instanceof SyntaxError); }
try { new RegExp("("); } catch (e) { print(e instanceof SyntaxError); }
```

| | output |
|---|---|
| literal text | `true`, `true`, `true` |
| V8, SpiderMonkey, JavaScriptCore | `true`, `true`, `true` |
| formal model (proposed reading baked into SpecTec) | `true`, `true`, `true` |

A host hook such as test262's `$262.evalScript`, which throws the List's first element (INTERPRETING.md), is where
the objects' realm could show.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -16430,7 +16430,7 @@
         Static Semantics: ParseText (
           _sourceText_: a String or a sequence of Unicode code points,
           _goalSymbol_: a nonterminal in one of the ECMAScript grammars,
-        ): a Parse Node or a non-empty List of *SyntaxError* objects
+        ): a Parse Node or a non-empty List of errors
       </h1>
       <dl class="header">
       </dl>
@@ -16439,7 +16439,7 @@
         1. Attempt to <emu-xref href="#sec-parsing">parse</emu-xref> _sourceText_ using _goalSymbol_ as the goal symbol, and analyse the parse result for any early error conditions. Parsing and early error detection may be interleaved in an implementation-defined manner.
         1. NOTE: When _goalSymbol_ is a nonterminal of the syntactic grammar, parsing includes conversion of _sourceText_ from code points to a stream of input elements as described in <emu-xref href="#sec-syntactic-grammar"></emu-xref>.
         1. If the parse succeeded and no early errors were found, return the Parse Node (an instance of _goalSymbol_) at the root of the parse tree resulting from the parse.
-        1. Return a List of one or more *SyntaxError* objects representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-defined, but at least one must be present.
+        1. Return a List of one or more errors representing the parsing errors and/or early errors. If more than one parsing error or early error is present, the number and ordering of errors in the list is implementation-defined, but at least one must be present.
       </emu-alg>
       <emu-note>
         <p>Consider a text that has an early error at a particular point, and also a syntax error at a later point. An implementation that does a parse pass followed by an early errors pass might report the syntax error and not proceed to the early errors pass. An implementation that interleaves the two activities might report the early error and not proceed to find the syntax error. A third implementation might report both errors. All of these behaviours are conformant.</p>
@@ -26435,7 +26435,7 @@
 
       <emu-alg>
         1. Let _script_ be ParseText(_sourceText_, |Script|).
-        1. If _script_ is a List of errors, return _script_.
+        1. If _script_ is a List of errors, return a List of *SyntaxError* objects created in _realm_, one for each element of _script_, in the same order.
         1. Return Script Record { [[Realm]]: _realm_, [[ECMAScriptCode]]: _script_, [[LoadedModules]]: « », [[HostDefined]]: _hostDefined_ }.
       </emu-alg>
       <emu-note>
@@ -28730,7 +28730,7 @@
           </dl>
           <emu-alg>
             1. Let _body_ be ParseText(_sourceText_, |Module|).
-            1. If _body_ is a List of errors, return _body_.
+            1. If _body_ is a List of errors, return a List of *SyntaxError* objects created in _realm_, one for each element of _body_, in the same order.
             1. Let _requestedModules_ be the ModuleRequests of _body_.
             1. Let _importEntries_ be the ImportEntries of _body_.
             1. Let _importedBoundNames_ be ImportedLocalNames(_importEntries_).
@@ -30585,7 +30585,7 @@
           ParseHexOctet (
             _string_: a String,
             _position_: a non-negative integer,
-          ): either a non-negative integer or a non-empty List of *SyntaxError* objects
+          ): either a non-negative integer or a non-empty List of errors
         </h1>
         <dl class="header">
           <dt>description</dt>
@@ -39159,7 +39159,7 @@
           1. Else,
             1. Let _patternText_ be the result of interpreting each of _pattern_'s 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements.
           1. Let _parseResult_ be ParsePattern(_patternText_, _u_, _v_).
-          1. If _parseResult_ is a non-empty List of *SyntaxError* objects, throw a *SyntaxError* exception.
+          1. If _parseResult_ is a List of errors, throw a *SyntaxError* exception.
           1. Assert: _parseResult_ is a |Pattern| Parse Node.
           1. Set _obj_.[[OriginalSource]] to _pattern_.
           1. Set _obj_.[[OriginalFlags]] to _flags_.
@@ -39178,7 +39178,7 @@
             _patternText_: a sequence of Unicode code points,
             _u_: a Boolean,
             _v_: a Boolean,
-          ): a Parse Node or a non-empty List of *SyntaxError* objects
+          ): a Parse Node or a non-empty List of errors
         </h1>
         <dl class="header">
         </dl>
@@ -39187,7 +39187,7 @@
         </emu-note>
         <emu-alg>
           1. If _v_ is *true* and _u_ is *true*, then
-            1. Let _parseResult_ be a List containing one or more *SyntaxError* objects.
+            1. Let _parseResult_ be a List containing one or more errors.
           1. Else if _v_ is *true*, then
             1. Let _parseResult_ be ParseText(_patternText_, |Pattern[+UnicodeMode, +UnicodeSetsMode, +NamedCaptureGroups]|).
           1. Else if _u_ is *true*, then
@@ -54118,7 +54118,7 @@
         <p>The semantics of ParsePattern with arguments _patternText_, _u_, and _v_ is extended as follows, with modifications <ins>highlighted</ins>:</p>
         <emu-alg>
           1. If _v_ is *true* and _u_ is *true*, then
-            1. Let _parseResult_ be a List containing one or more *SyntaxError* objects.
+            1. Let _parseResult_ be a List containing one or more errors.
           1. Else if _v_ is *true*, then
             1. Let _parseResult_ be ParseText(_patternText_, |Pattern[+UnicodeMode, +UnicodeSetsMode, +NamedCaptureGroups]|).
           1. Else if _u_ is *true*, then
```

## test262

None: no test evaluates a script with a parse error through a host hook that exposes the List's objects.
