# 33. CreateIntrinsics passes _async_ in _prefix_'s position: every built-in gets a Boolean prefix

- **Location:** §9.3.2 CreateIntrinsics (`#sec-createintrinsics`), step 2, with §10.3.4 CreateBuiltinFunction
  (`#sec-createbuiltinfunction`), its header and steps 3, 7 and 13, §10.2.9 SetFunctionName (`#sec-setfunctionname`),
  step 5.a, and the *"name"* paragraphs of §18 ECMAScript Standard Built-in Objects
  (`#sec-ecmascript-standard-built-in-objects`).
- **Kind:** a call outside its parameter types (an argument in the wrong position).
- **Model erratum:** `CreateIntrinsicsAsyncArgument`, default reading test262; its readings: literal, test262,
  proposed. Read literally, the run stops at SetFunctionName step 5.a under CreateBuiltinFunction, where _async_ is
  concatenated as the prefix; the test262 and proposed readings pass _prefix_ as §18 gives it and set [[Async]] from
  the step's sentence.
- **Upstream:** Checked 2026-11-19: issue #3534 (open, 2025-02), "CreateIntrinsics isn't passing prefix to
  CreateBuiltinFunction for builtin getters/setters", reports the missing _prefix_; issue #4046 (open, 2026-10),
  "Editorial: CreateBuiltinFunction call in CreateIntrinsics passes wrong parameters", reports the argument position.
  PR #4022 (closed without merging, 2026-10) proposed six arguments and setting [[Async]] afterwards; PR #2833 (open,
  2022-07), "Editorial: Specify _prefix_ for non-specific uses of CreateBuiltinFunction", passes _prefix_ last and
  predates _async_, which came with PR #2942 (merged 2025-12, commit 7029ed1b2).

## Text

CreateIntrinsics, step 2:

> All values that are built-in function objects are created by performing CreateBuiltinFunction(_steps_, _length_,
> _name_, _slots_, _realmRecord_, _proto_, _async_) where _steps_ is the definition of that function provided by
> this specification, _name_ is the initial value of the function's *"name"* property, … and _async_ is *true* if the
> function is described as “async” and *false* otherwise.

CreateBuiltinFunction's header:

> CreateBuiltinFunction ( _behaviour_: an Abstract Closure, a set of algorithm steps, or some other definition of a
> function's behaviour provided in this specification, _length_: a non-negative integer or +∞, _name_: a property key
> or a Private Name, _additionalInternalSlotsList_: a List of names of internal slots, optional _realm_: a Realm
> Record, optional _proto_: an Object or *null*, optional _prefix_: a String, optional _async_: a Boolean, ): a
> built-in function object

and its steps:

> 3. If _async_ is not present, set _async_ to *false*.
>
> 7. Set _func_.[[Async]] to _async_.
>
> 13. If _prefix_ is not present, then
>     a. Perform SetFunctionName(_func_, _name_).
> 14. Else,
>     a. Perform SetFunctionName(_func_, _name_, _prefix_).

SetFunctionName:

> 5. If _prefix_ is present, then
>     a. Let _prefixedName_ be the string-concatenation of _prefix_, the code unit 0x0020 (SPACE), and _name_.

## Problem

The step passes seven arguments; the seventh parameter is _prefix_, a String. So every built-in function created
by CreateIntrinsics gets _prefix_ *false* (or *true*) and no _async_. CreateBuiltinFunction then calls
SetFunctionName with a Boolean prefix, whose step 5.a concatenates a Boolean with Strings, which is not defined;
and [[Async]] is *false* for every built-in, so `Array.fromAsync`, the one built-in described as "async", runs its
steps without AsyncFunctionStart (BuiltinCallOrConstruct, step 10) and its Await has no async function context. The
step's intent is clear from its own sentence and from §18: _async_ in its own position, and _prefix_ *"get"* or
*"set"* for an accessor, which the step does not pass at all. Since _async_ follows _prefix_, a call that passes _async_ must pass some _prefix_,
so the fix gives _prefix_ an ~empty~ case.

## Examples

[examples/33-createintrinsics-async-argument-position.js](examples/33-createintrinsics-async-argument-position.js)
(outputs: [RESULTS.md](examples/RESULTS.md#33-createintrinsics-async-argument-positionjs)):

```js
print(Object.getOwnPropertyDescriptor(Map.prototype, "size").get.name);
print(Object.getOwnPropertyDescriptor(RegExp.prototype, "flags").get.name);
var p = Array.fromAsync([1, 2]);
print(Object.prototype.toString.call(p));
p.then(function (v) { print("fromAsync fulfils with " + JSON.stringify(v)); });
```

| | output |
|---|---|
| literal text | none: creating the realm's first built-in function concatenates a Boolean (SetFunctionName 5.a) |
| proposed text | `get size`, `get flags`, `[object Promise]`, `fromAsync fulfils with [1,2]` |
| V8, SpiderMonkey, JavaScriptCore | `get size`, `get flags`, `[object Promise]`, `fromAsync fulfils with [1,2]` |
| formal model, literal reading | none: the run stops at SetFunctionName 5.a while the realm is created |
| formal model, test262 and proposed readings | `get size`, `get flags`, `[object Promise]`, `fromAsync fulfils with [1,2]` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -11854,7 +11854,7 @@
       </dl>
       <emu-alg>
         1. Set _realmRecord_.[[Intrinsics]] to a new Record.
-        1. [declared="steps,name,length,slots,proto,async"] Set fields of _realmRecord_.[[Intrinsics]] with the values listed in <emu-xref href="#table-well-known-intrinsic-objects"></emu-xref>. The field names are the names listed in the “Intrinsic Name” column of the table. The value of each field is a new object value fully and recursively populated with property values as defined by the specification of each object in clauses <emu-xref href="#sec-global-object"></emu-xref> through <emu-xref href="#sec-reflection"></emu-xref>. All object property values are newly created object values. All values that are built-in function objects are created by performing CreateBuiltinFunction(_steps_, _length_, _name_, _slots_, _realmRecord_, _proto_, _async_) where _steps_ is the definition of that function provided by this specification, _name_ is the initial value of the function's *"name"* property, _length_ is the initial value of the function's *"length"* property, _slots_ is a list of the names, if any, of the function's specified internal slots, _proto_ is the specified value of the function's [[Prototype]] internal slot, and _async_ is *true* if the function is described as “async” and *false* otherwise. The creation of the intrinsics and their properties must be ordered to avoid any dependencies upon objects that have not yet been created.
+        1. [declared="steps,name,length,slots,proto,prefix,async"] Set fields of _realmRecord_.[[Intrinsics]] with the values listed in <emu-xref href="#table-well-known-intrinsic-objects"></emu-xref>. The field names are the names listed in the “Intrinsic Name” column of the table. The value of each field is a new object value fully and recursively populated with property values as defined by the specification of each object in clauses <emu-xref href="#sec-global-object"></emu-xref> through <emu-xref href="#sec-reflection"></emu-xref>. All object property values are newly created object values. All values that are built-in function objects are created by performing CreateBuiltinFunction(_steps_, _length_, _name_, _slots_, _realmRecord_, _proto_, _prefix_, _async_) where _steps_ is the definition of that function provided by this specification, _name_ and _prefix_ are as given in <emu-xref href="#sec-ecmascript-standard-built-in-objects"></emu-xref> (_prefix_ is ~empty~ for a function that is not a get or set accessor function of a built-in property), _length_ is the initial value of the function's *"length"* property, _slots_ is a list of the names, if any, of the function's specified internal slots, _proto_ is the specified value of the function's [[Prototype]] internal slot, and _async_ is *true* if the function is described as “async” and *false* otherwise. The creation of the intrinsics and their properties must be ordered to avoid any dependencies upon objects that have not yet been created.
         1. Perform AddRestrictedFunctionProperties(_realmRecord_.[[Intrinsics]].[[%Function.prototype%]], _realmRecord_).
         1. Return ~unused~.
       </emu-alg>
@@ -14145,7 +14145,7 @@
           _additionalInternalSlotsList_: a List of names of internal slots,
           optional _realm_: a Realm Record,
           optional _proto_: an Object or *null*,
-          optional _prefix_: a String,
+          optional _prefix_: a String or ~empty~,
           optional _async_: a Boolean,
         ): a built-in function object
       </h1>
@@ -14166,7 +14166,7 @@
         1. Set _func_.[[Realm]] to _realm_.
         1. Set _func_.[[InitialName]] to *null*.
         1. Perform SetFunctionLength(_func_, _length_).
-        1. If _prefix_ is not present, then
+        1. If _prefix_ is not present or _prefix_ is ~empty~, then
           1. Perform SetFunctionName(_func_, _name_).
         1. Else,
           1. Perform SetFunctionName(_func_, _name_, _prefix_).
```

## test262

Every test needs the realm's built-ins. Those that observe the two arguments:
`built-ins/Array/fromAsync/returns-promise.js` and `built-ins/Array/fromAsync/asyncitems-null-undefined.js` (a
rejected promise, not a synchronous throw) need [[Async]] *true*; `built-ins/Map/prototype/size/name.js` and the
other accessor `name.js` tests need the *"get "* prefix.
