# 47. A *null*-realm promise Job calls user code, which HostEnqueuePromiseJob's note says it does not

- **Location:** §9.5.5 HostEnqueuePromiseJob (`#sec-hostenqueuepromisejob`), its note and its first requirement,
  against §27.5.2.1 NewPromiseReactionJob (`#sec-newpromisereactionjob`), steps 1.h.i, 1.i and 2–3; with §9.5
  (`#sec-jobs`), its first paragraph.
- **Kind:** a note contradicted by an algorithm.
- **Model erratum:** none: a note states no requirement and nothing in the model reads it; the model follows the
  steps (the literal text).
- **Upstream:** Checked 2026-11-19: none found (searched for "HostEnqueuePromiseJob"). Issue #2222 (open, 2020-11),
  "Promise.prototype.finally should use onFinally's realm for newly creating functions", is about the realm of
  `finally`'s functions. The *null* realm of a handler-less reaction came with PR #1597 (merged 2020-03, commit
  c59502090), "Layering: Allow hosts to cleanly specify Promise Job semantics"; PR #1984 (merged 2020-08, commit
  a59a820d3), "Layering: Refine execution context requirements for Jobs", wrote the requirements' "If _realm_ is not
  *null*" and the note's present wording.

## Text

HostEnqueuePromiseJob:

> If _realm_ is not *null*, each time _job_ is invoked the implementation must perform implementation-defined steps
> such that execution is prepared to evaluate ECMAScript code at the time of _job_'s invocation.

Its note:

> … If the handler is *undefined*, _realm_ is *null*. … When the _realm_ is *null*, no user ECMAScript code will
> be evaluated and no new ECMAScript objects (e.g. Error objects) will be created. The WHATWG HTML specification …
> uses _realm_ to check for the ability to run script and for the entry concept.

NewPromiseReactionJob:

> 1. Let _job_ be a new Job Abstract Closure with no parameters that captures _reaction_ and _arg_ and performs the
>    following steps when called:
>     i. Return ? Call(_promiseCapability_.[[Resolve]], *undefined*, « _handlerResult_.[[Value]] »).
> 2. Let _handlerRealm_ be *null*.
> 3. If _reaction_.[[Handler]] is not ~empty~, then …

§9.5, of the hosts' own operations: "If *null* is provided instead for the realm, then the job does not evaluate
ECMAScript code."

## Problem

When a reaction has no handler (`q.then()`), steps 2–3 leave the Job's realm *null*, yet step 1.i still calls
_promiseCapability_.[[Resolve]] (or step 1.h.i [[Reject]]). That capability is the derived promise's, made by
NewPromiseCapability for the species constructor of `q`, which the program chooses, so its resolving functions can
be ECMAScript functions: the Job evaluates user code, which the note says it does not. They can also create objects:
a callable Proxy's [[Call]] creates _argArray_ in the current realm (§10.5.12 step 7), and a revoked one throws a
*TypeError* (step 1). Since the first requirement asks for no preparation when _realm_ is *null*, which realm is
current then, if any, is left to the host. The note is the only statement about this case: §9.5's sentence speaks of
the hosts' own operations ("Such operations"), and a note states no requirement.

## Examples

[examples/47-promise-job-null-realm-code.js](examples/47-promise-job-null-realm-code.js) (outputs:
[RESULTS.md](examples/RESULTS.md#47-promise-job-null-realm-codejs)):

```js
function Species(executor) {
  executor(function (v) { print("resolve(" + v + ") called by the null-realm Job"); }, function () {});
}
Species[Symbol.species] = Species;
var q = Promise.resolve(2);
q.constructor = Species;
q.then();
Promise.resolve(3).then(function () { print("a later Job runs"); });
```

| | output |
|---|---|
| literal text (the note) | no user code runs in the *null*-realm Job of `q.then()` |
| literal text (the steps) | `resolve(2) called by the null-realm Job`, `a later Job runs` |
| V8, SpiderMonkey, JavaScriptCore | `resolve(2) called by the null-realm Job`, `a later Job runs` |
| formal model | `resolve(2) called by the null-realm Job`, `a later Job runs` |

The model's test `tests/run/null_realm_job.js` shows the realm a callable Proxy sees: with the Proxy and the promise
in a second realm, _argArray_ is the first (host-created) realm's Array, the realm the model's host prepares for the
Job; it prints `false,true` (_argArray_'s prototype is not the second realm's `Array.prototype` and is the first's).

## Proposed wording

Proposed: make the note say what the steps do, by replacing its sentence "When the _realm_ is *null*, no user
ECMAScript code will be evaluated …" with:

<!-- quote: the proposed sentence, not the text of spec.html -->
> When the _realm_ is *null*, the Job evaluates no handler, but it still calls the resolving functions of the derived
> promise's PromiseCapability Record, which may be ECMAScript code or a Proxy when the promise's constructor was
> supplied by a program (see NewPromiseReactionJob); objects that such calls create, including Error objects, belong to
> the current Realm Record when the Job runs.

```diff
--- a/spec.html
+++ b/spec.html
@@ -12307,7 +12307,7 @@
       </ul>
 
       <emu-note>
-        <p>The _realm_ for Jobs returned by NewPromiseResolveThenableJob is usually the result of calling GetFunctionRealm on the _then_ function object. The _realm_ for Jobs returned by NewPromiseReactionJob is usually the result of calling GetFunctionRealm on the handler if the handler is not *undefined*. If the handler is *undefined*, _realm_ is *null*. For both kinds of Jobs, when GetFunctionRealm completes abnormally (i.e. called on a revoked Proxy), _realm_ is the current Realm Record at the time of the GetFunctionRealm call. When the _realm_ is *null*, no user ECMAScript code will be evaluated and no new ECMAScript objects (e.g. Error objects) will be created. The WHATWG HTML specification (<a href="https://html.spec.whatwg.org/">https://html.spec.whatwg.org/</a>), for example, uses _realm_ to check for the ability to run script and for the <a href="https://html.spec.whatwg.org/#entry">entry</a> concept.</p>
+        <p>The _realm_ for Jobs returned by NewPromiseResolveThenableJob is usually the result of calling GetFunctionRealm on the _then_ function object. The _realm_ for Jobs returned by NewPromiseReactionJob is usually the result of calling GetFunctionRealm on the handler if the handler is not *undefined*. If the handler is *undefined*, _realm_ is *null*. For both kinds of Jobs, when GetFunctionRealm completes abnormally (i.e. called on a revoked Proxy), _realm_ is the current Realm Record at the time of the GetFunctionRealm call. When the _realm_ is *null*, the Job evaluates no handler, but it still calls the resolving functions of the derived promise's PromiseCapability Record, which may be ECMAScript code or a Proxy when the promise's constructor was supplied by a program (see <emu-xref href="#sec-newpromisereactionjob"></emu-xref>); objects that such calls create, including Error objects, belong to the current Realm Record when the Job runs. The WHATWG HTML specification (<a href="https://html.spec.whatwg.org/">https://html.spec.whatwg.org/</a>), for example, uses _realm_ to check for the ability to run script and for the <a href="https://html.spec.whatwg.org/#entry">entry</a> concept.</p>
       </emu-note>
     </emu-clause>
 
```

The note alone leaves the current realm to the host. A normative fix would also drop "If _realm_ is not *null*" from
the first requirement, so that a *null*-realm Job too is prepared to evaluate ECMAScript code; that changes what a host
may do for such a Job (the note says HTML uses _realm_ to check for the ability to run script), so it is a question for
the committee and the hosts together.

## test262

`built-ins/Promise/prototype/then/deferred-is-resolved-value.js` (flags async) does what the example does: `p.then()`
on a promise whose species constructor `P` hands its executor a user function as the resolve function, which calls
`$DONE()`; the test finishes only if the handler-less reaction's Job calls that function. It requires the steps'
behaviour, not the note's.
