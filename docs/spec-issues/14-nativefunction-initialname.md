# 14. Function.prototype.toString has no conforming result for some [[InitialName]] values

- **Location:** §20.2.3.5 Function.prototype.toString (`#sec-function.prototype.tostring`), step 3, with §15.7.14
  ClassDefinitionEvaluation (`#sec-runtime-semantics-classdefinitionevaluation`), steps 14.b and 16.
- **Kind:** no result (two requirements no String meets together).
- **Model erratum:** `NativeFunctionInitialName`, baked-in SpecTec reading literal for non-PropertyName `[[InitialName]]`
  values such as `"a b"` (where no String meets both requirements and the run stops at `stop: residue`), paired with two
  non-literal choices: `S20.spectec` allows an empty `""` `[[InitialName]]` without requiring a `|PropertyName|` Parse Node
  (so anonymous built-ins such as `(() => {}).bind().toString()` succeed), and `NativeFunctionSource`
  (`spec/spectec/prose/20-host-laws-order.spectec`) narrows `.ok` representations to `function ` N `() { [native code] }`
  with N empty or an ASCII name (optionally after `get ` or `set `, or `[Symbol.` name `]`).
- **Upstream:** Checked 2026-11-19: related: PR #2695 (open, 2022-03), "Normative: Allow toString of a built-in
  function to output a computed property name", adds a `[` StringLiteral `]` form of NativeFunctionName, which every
  String can take; a comment there (2022-08-04) says that per the July 2022 meeting it should be replaced by
  tc39/proposal-stricter-function-tostring (stage 0 by its README, last pushed 2022-07).

## Text

> 2. If _func_ is an Object, _func_ has a [[SourceText]] internal slot, _func_.[[SourceText]] is a sequence of
>    Unicode code points, and HostHasSourceTextAvailable(_func_) is *true*, then
>    a. Return CodePointsToString(_func_.[[SourceText]]).
> 3. If _func_ is a built-in function object, return an implementation-defined String source code representation of
>    _func_. The representation must have the syntax of a |NativeFunction|. Additionally, if _func_ has an
>    [[InitialName]] internal slot and _func_.[[InitialName]] is a String, the portion of the returned String that
>    would be matched by |NativeFunctionAccessor?| |PropertyName| must be _func_.[[InitialName]].

with NativeFunction : `function` NativeFunctionAccessor? PropertyName? `(` FormalParameters `)` `{` `[` `native`
`code` `]` `}`.

## Problem

A class's default constructor is a built-in function object (ClassDefinitionEvaluation step 14.b,
CreateBuiltinFunction with the class's name as its [[InitialName]]), and NamedEvaluation names a class after the
property key it is defined under. That name can be a String that no NativeFunctionAccessor? PropertyName matches:

- `({ ["a b"]: class {} })`: `a b` (an IdentifierName has no space, a StringLiteral includes its quotes, a
  ComputedPropertyName its brackets);
- `class C { static #x = class {} }`: `#x` (a PrivateIdentifier is not a PropertyName);
- `({ [Symbol("a b")]: class {} })`: `[a b]`, which is not a ComputedPropertyName.

Step 16 gives the default constructor a [[SourceText]], so step 2 normally applies. But HostHasSourceTextAvailable
may return *false* (it exists for hosts that hide source), and then step 3 must return a NativeFunction whose
PropertyName portion is `a b`: there is none. Built-ins of the specification itself have names that a PropertyName
matches (`[Symbol.iterator]` is a ComputedPropertyName, `get [Symbol.species]` an accessor's); the model reads the
empty name of an anonymous built-in as met by a NativeFunction without a name.

## Examples

[examples/14-nativefunction-initialname.js](examples/14-nativefunction-initialname.js) (outputs:
[RESULTS.md](examples/RESULTS.md#14-nativefunction-initialnamejs)):

```js
var o = { ["a b"]: class {} };
print(JSON.stringify(o["a b"].name));
class C { static #x = class {}; static name2() { return C.#x.name; } }
print(JSON.stringify(C.name2()));
var s = { [Symbol("a b")]: class {} };
print(JSON.stringify(s[Object.getOwnPropertySymbols(s)[0]].name));
print(Function.prototype.toString.call(o["a b"]));
```

| | output |
|---|---|
| literal text, source text available | `"a b"`, `"#x"`, `"[a b]"`, `class {}` |
| literal text, source text hidden | the three names, then no String meets step 3 |
| V8, SpiderMonkey, JavaScriptCore | `"a b"`, `"#x"`, `"[a b]"`, `class {}` |
| formal model (literal and proposed readings) | `"a b"`, `"#x"`, `"[a b]"`, `class {}` |

Every engine's HostHasSourceTextAvailable is *true* for the class, so step 2 applies; no engine offers a way to hide
a class's source text, so the defect shows only in a host that does.

## Proposed wording

Ask for the name only when a NativeFunctionAccessor? PropertyName can match it:

```diff
--- a/spec.html
+++ b/spec.html
@@ -31666,7 +31666,7 @@
           1. Let _func_ be the *this* value.
           1. If _func_ is an Object, _func_ has a [[SourceText]] internal slot, _func_.[[SourceText]] is a sequence of Unicode code points, and HostHasSourceTextAvailable(_func_) is *true*, then
             1. Return CodePointsToString(_func_.[[SourceText]]).
-          1. If _func_ is a <emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>, return an implementation-defined String source code representation of _func_. The representation must have the syntax of a |NativeFunction|. Additionally, if _func_ has an [[InitialName]] internal slot and _func_.[[InitialName]] is a String, the portion of the returned String that would be matched by |NativeFunctionAccessor?| |PropertyName| must be _func_.[[InitialName]].
+          1. If _func_ is a <emu-xref href="#sec-built-in-function-objects">built-in function object</emu-xref>, return an implementation-defined String source code representation of _func_. The representation must have the syntax of a |NativeFunction|. Additionally, if _func_ has an [[InitialName]] internal slot, _func_.[[InitialName]] is a String, and _func_.[[InitialName]] is matched by |NativeFunctionAccessor?| |PropertyName|, the portion of the returned String that would be matched by |NativeFunctionAccessor?| |PropertyName| must be _func_.[[InitialName]].
           1. If _func_ is an Object and IsCallable(_func_) is *true*, return an implementation-defined String source code representation of _func_. The representation must have the syntax of a |NativeFunction|.
           1. Throw a *TypeError* exception.
         </emu-alg>
```

An empty [[InitialName]] is not matched either, so the requirement also lapses for anonymous built-ins, whose
portion is empty under either text.

An alternative, also proposed, is a `[` StringLiteral `]` form of NativeFunction's name, which every String can take:
`function ["a b"]() { [native code] }` would then meet the requirement for the first example.

## test262

`built-ins/Function/prototype/toString/` checks NativeFunction syntax only for functions whose names are
PropertyNames.
