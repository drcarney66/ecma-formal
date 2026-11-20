# 24. CompileToCharSet asks UnicodeMatchPropertyValue for a General_Category value before testing that it is one

- **Location:** §22.2.2.9 CompileToCharSet (`#sec-compiletocharset`), UnicodePropertyValueExpression ::
  LoneUnicodePropertyNameOrValue, step 2, with §22.2.2.9.8 UnicodeMatchPropertyValue
  (`#sec-runtime-semantics-unicodematchpropertyvalue-p-v`), step 2.
- **Kind:** failing Assert (for every lone binary property name), and a condition that is true whenever it is defined.
- **Model erratum:** `LonePropertyGeneralCategoryAssert`, default reading test262; its readings: literal, test262,
  proposed. The test262 and proposed readings are the same step 2, the proposed wording below; under the literal
  reading the model stops where UnicodeMatchPropertyValue's Assert fails.
- **Upstream:** Checked 2026-11-19: issue #3586 (open, 2025-05), "UnicodeMatchPropertyValue assertion fails by
  UnicodePropertyValueExpression", reports it for `/[\p{Hex}]/u`; PR #3587 (open, 2025-05), "Editorial: Fix incorrect
  use of UnicodeMatchPropertyValue", fixes it by testing _s_ first, with other changes (Script_Extensions), and is not
  merged.

## Text

CompileToCharSet, UnicodePropertyValueExpression :: LoneUnicodePropertyNameOrValue:

> 1. Let _s_ be the source text matched by |LoneUnicodePropertyNameOrValue|.
> 2. If UnicodeMatchPropertyValue(`General_Category`, _s_) is a Unicode property value or property value alias for
>    the General_Category (gc) property listed in PropertyValueAliases.txt, then
>    a. Return the CharSet containing all Unicode code points whose character database definition includes the
>       property “General_Category” with value _s_.
> 3. Let _p_ be UnicodeMatchProperty(_regexpRecord_, _s_).
> 4. Assert: _p_ is a binary Unicode property or binary property alias listed in the “Property name and aliases”
>    column of …, or a binary Unicode property of strings listed in the “Property name” column of ….

UnicodeMatchPropertyValue (_p_: ECMAScript source text, _v_: ECMAScript source text), returning a Unicode property
value:

> 2. Assert: _v_ is a property value or property value alias for the Unicode property _p_ listed in
>    PropertyValueAliases.txt.
> 3. Let _value_ be the canonical property value of _v_ as given in the “Canonical property value” column of the
>    corresponding row.

## Problem

Step 2 calls UnicodeMatchPropertyValue before it tests _s_. For a lone binary property name (`\p{ASCII}`, `\p{Any}`,
`\p{Hex}`, or a property of strings such as `\p{RGI_Emoji}` with the `v` flag), _s_ is no General_Category value, and
UnicodeMatchPropertyValue's Assert (step 2) fails. Steps 3–4, which handle exactly these names, are never reached.
Where the call does return, it returns a canonical General_Category value, so step 2's test is always true; and step
2.a uses _s_, which may be an alias (`Lu`), as the value, not the canonical value the call computed.

## Examples

[examples/24-lone-property-gc-assert.js](examples/24-lone-property-gc-assert.js) (outputs:
[RESULTS.md](examples/RESULTS.md#24-lone-property-gc-assertjs)):

```js
/\p{Lu}/u.test("A");          // a General_Category value
/\p{ASCII}/u.test("a");       // binary properties
/\p{Hex}/u.test("f");
/\p{Any}/u.test("\u{10FFFF}");
```

| | `\p{Lu}` | `\p{ASCII}`, `\p{Hex}`, `\p{Any}` |
|---|---|---|
| literal text | `true` | UnicodeMatchPropertyValue's Assert fails |
| V8, SpiderMonkey, JavaScriptCore | `true` | `true` |
| formal model (test262 reading) | `true` | `true` |
| formal model (literal reading) | `true` | `stop: erratum LonePropertyGeneralCategoryAssert sec-runtime-semantics-unicodematchpropertyvalue-p-v#0 2` |

Under the literal reading the example stops at its first binary property and prints only the stop line; `\p{Lu}` alone
prints `true`.

## Proposed wording

Proposed: test _s_ first, then take the canonical value from UnicodeMatchPropertyValue.

```diff
--- a/spec.html
+++ b/spec.html
@@ -38772,8 +38772,9 @@
         <emu-grammar>UnicodePropertyValueExpression :: LoneUnicodePropertyNameOrValue</emu-grammar>
         <emu-alg>
           1. Let _s_ be the source text matched by |LoneUnicodePropertyNameOrValue|.
-          1. If UnicodeMatchPropertyValue(`General_Category`, _s_) is a Unicode property value or property value alias for the General_Category (gc) property listed in <a href="https://unicode.org/Public/UCD/latest/ucd/PropertyValueAliases.txt"><code>PropertyValueAliases.txt</code></a>, then
-            1. Return the CharSet containing all Unicode code points whose character database definition includes the property “General_Category” with value _s_.
+          1. If _s_ is a Unicode property value or property value alias for the General_Category (gc) property listed in <a href="https://unicode.org/Public/UCD/latest/ucd/PropertyValueAliases.txt"><code>PropertyValueAliases.txt</code></a>, then
+            1. Let _v_ be UnicodeMatchPropertyValue(StringToCodePoints(*"General_Category"*), _s_).
+            1. Return the CharSet containing all Unicode code points whose character database definition includes the property “General_Category” with value _v_.
           1. Let _p_ be UnicodeMatchProperty(_regexpRecord_, _s_).
           1. Assert: _p_ is a binary Unicode property or binary property alias listed in the “<emu-not-ref>Property name and aliases</emu-not-ref>” column of <emu-xref href="#table-binary-unicode-properties"></emu-xref>, or a binary Unicode property of strings listed in the “<emu-not-ref>Property name</emu-not-ref>” column of <emu-xref href="#table-binary-unicode-properties-of-strings"></emu-xref>.
           1. Let _charSet_ be the CharSet containing all CharSetElements whose character database definition includes the property _p_ with value “True”.
```

## test262

The binary-property files of `built-ins/RegExp/property-escapes/generated/` (53 of them: `ASCII.js`, `Any.js`,
`Hex_Digit.js`, …) and those of its `strings/` directory (properties of strings, with the `v` flag) compile a lone
binary property name; under the literal text each reaches the Assert. An Assert has no observable effect, so none
fails.
