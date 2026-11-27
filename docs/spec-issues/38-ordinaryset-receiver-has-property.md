# 38. OrdinarySetWithOwnDescriptor asserts what a Proxy receiver's trap need not tell

- **Location:** §10.1.9.2 OrdinarySetWithOwnDescriptor (`#sec-ordinarysetwithowndescriptor`), step 2.d.i, against
  §10.5.5 [[GetOwnProperty]] of a Proxy exotic object
  (`#sec-proxy-object-internal-methods-and-internal-slots-getownproperty-p`), steps 10.a–e.
- **Kind:** failing Assert (or, read on the receiver's own properties only, a vacuous one).
- **Model erratum:** `OrdinarySetReceiverHasProperty`, baked-in SpecTec reading proposed (`spec/spectec/clauses/S10.spectec`,
  line 190). Literal step 2.d.i (`Assert: _receiver_ does not currently have a property _propertyKey_`) fails both when a
  Proxy receiver's `getOwnPropertyDescriptor` trap hides a configurable target property and when an ordinary `_receiver_`
  inherits `_propertyKey_` from its prototype chain; SpecTec silences step 2.d.i with `assert pass` instead of checking
  the literal `Assert:`.
- **Upstream:** Checked 2026-11-19: none found (searched for "OrdinarySetWithOwnDescriptor"). The Assert is in the
  first Ecmarkup version of the text (commit 7461eea82); PR #3789 (merged 2026-04, commit bab3fbf29) renamed its
  aliases.

## Text

OrdinarySetWithOwnDescriptor:

> 2. If IsDataDescriptor(_ownDesc_) is *true*, then
>    a. If _ownDesc_.[[Writable]] is *false*, return *false*.
>    b. If _receiver_ is not an Object, return *false*.
>    c. Let _existingDesc_ be ? _receiver_.[[GetOwnProperty]](_propertyKey_).
>    d. If _existingDesc_ is *undefined*, then
>       i. Assert: _receiver_ does not currently have a property _propertyKey_.
>       ii. Return ? CreateDataProperty(_receiver_, _propertyKey_, _value_).

[[GetOwnProperty]] of a Proxy exotic object, after its `getOwnPropertyDescriptor` trap returns *undefined*:

> 10. If _trapResultObj_ is *undefined*, then
>    a. If _targetDesc_ is *undefined*, return *undefined*.
>    b. If _targetDesc_.[[Configurable]] is *false*, throw a *TypeError* exception.
>    c. Let _extensibleTarget_ be ? IsExtensible(_target_).
>    d. If _extensibleTarget_ is *false*, throw a *TypeError* exception.
>    e. Return *undefined*.

## Problem

The Assert rests on the answer _receiver_.[[GetOwnProperty]] gave one step before. For an ordinary receiver that
answer is the receiver's own property, and the Assert holds. For a Proxy receiver it is the trap's answer, and step
10.e lets the trap report *undefined* for a configurable property of an extensible target. Then step 2.d.i either
reads "have a property" as the receiver's own properties, which a Proxy exotic object does not hold, so the Assert
holds for every Proxy and says nothing; or it looks through the Proxy to its target, which has the property, so the
Assert fails in a conforming execution. Neither reading makes it a useful invariant, and step 2.d.ii does not need
it: CreateDataProperty calls _receiver_.[[DefineOwnProperty]], which handles a property that exists.

## Examples

[examples/38-ordinaryset-receiver-has-property.js](examples/38-ordinaryset-receiver-has-property.js) (outputs:
[RESULTS.md](examples/RESULTS.md#38-ordinaryset-receiver-has-propertyjs)):

```js
var t = { x: 1 };
var p = new Proxy(t, { getOwnPropertyDescriptor() { return undefined; } });
print(Reflect.set({}, "x", 5, p));
print(t.x);
```

`Reflect.set` reaches step 2 with _ownDesc_ the default data descriptor of step 1.c (`{}` and its prototypes have
no `x`) and _receiver_ `p`; the trap answers *undefined* while `t` has `x`, and CreateDataProperty redefines `t.x`
through the Proxy.

| | `Reflect.set(...)` | `t.x` |
|---|---|---|
| literal step 2.d.i, read through the Proxy | the Assert fails | — |
| V8, SpiderMonkey, JavaScriptCore | `true` | `5` |
| formal model (the Assert not checked) | `true` | `5` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -13129,7 +13129,7 @@
             1. If _receiver_ is not an Object, return *false*.
             1. Let _existingDesc_ be ? <emu-meta effects="user-code">_receiver_.[[GetOwnProperty]](_propertyKey_)</emu-meta>.
             1. If _existingDesc_ is *undefined*, then
-              1. Assert: _receiver_ does not currently have a property _propertyKey_.
+              1. NOTE: If _receiver_ is a Proxy exotic object, its target may have a property _propertyKey_.
               1. Return ? CreateDataProperty(_receiver_, _propertyKey_, _value_).
             1. If IsAccessorDescriptor(_existingDesc_) is *true*, return *false*.
             1. If _existingDesc_.[[Writable]] is *false*, return *false*.
```

(Deleting the step, with no note, would do as well.)

## test262

None found makes a receiver's `getOwnPropertyDescriptor` trap hide a target property on this path
(`built-ins/Reflect/set` and `built-ins/Proxy/set` use ordinary receivers or a forwarding trap). An Assert has no
observable effect, so no test fails under either reading.
