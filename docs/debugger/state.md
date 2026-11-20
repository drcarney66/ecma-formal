# The observable state of an ECMAScript execution

What a step debugger shows: the full state of an execution under the pinned
ECMA-262 (`external/ecma262/spec.html`), where each part lives in the model,
and how the [debugger](README.md) shows it. The spec-internal records are in
[state-internal.md](state-internal.md).

The model is the specification as data (`lean/Ecma`), its state `Ecma.State` (`lean/Ecma/State.lean`),
run by the machine (`lean/Ecma/Machine`); the debugger's base. Its state is one heap of cells
and a few fields beside it (§3); the "Model" columns below name where each
part is kept there.

## 0. The answer in brief

The state of an ECMAScript execution, as the specification defines it, has three layers:

1. **What ECMAScript code can observe.** Objects, their properties and prototypes, the values of bindings, the
   global object, the symbol registry, Data Blocks through views, the order in which jobs run, and what the host
   reports (time, randomness, output). Code observes these only through the language's operations, so it never
   sees identities, internal slots or the algorithms' progress directly.
2. **Spec-internal state.** The records the algorithms read and write that code cannot name: the Agent Record,
   the execution-context stack and suspended contexts, Realm, Environment, PrivateEnvironment, Script and Module
   Records (with each module's [[Status]] and its loading state), internal slots (a promise's reactions, a
   generator's state), the job queue, the candidate execution of the memory model, waiter lists, and Records and
   Lists that are shared by reference.
3. **The running algorithms' continuations.** At any instant some algorithms are part-way through their steps:
   which step each is at, the values of its aliases (`_x_`), an Abstract Closure's captured values, and a
   completion being propagated. The specification never names this state, but it is what "step 3.b of
   OrdinaryToPrimitive" means, and it is what a step debugger shows.

The model has **one agent**. Agent clusters (§9.7), other agents, `$262.agent` and an `Atomics.wait` woken by
another agent are not representable, so they are outside this catalogue ([state-internal.md](state-internal.md) §3.2).

Everything else is **not spec state**: host configuration and bookkeeping, parser internals, fuel and the
model's plumbing (§6). The debugger shows it in a collapsed "host / model" group.

## 1. Reading the catalogue

For each part: the spec's name and section; where the model keeps it; whether ECMAScript code can observe it
(and how); how it changes (identity and mutability); how the debugger shows it.

Identity in the model: every spec entity with identity is a **cell of the heap**, addressed by a reference; at
Fast the heap is an array and a reference its index, so an address is a stable link for the whole run and "new
since the last pause" is an address range (`Dbg.Heap.diff`). The heap never shrinks, but its cells are
**updated in place**. A List cell can lose elements ([[KeptAlive]] emptied, a module stack popped), and the
debugger compares a changed cell with its previous value.

## 2. Layer 1: what ECMAScript code can observe

| State | How code observes it | Model |
|---|---|---|
| Objects and their own properties (key order, attributes, values) | [[GetOwnProperty]], [[OwnPropertyKeys]], `Object.getOwnPropertyDescriptors`, `Reflect` | an `object` cell: its internal slots and its own properties, each an attribute Record |
| Prototype chains, extensibility | [[GetPrototypeOf]], [[IsExtensible]] | the object's [[Prototype]] and [[Extensible]] slots |
| Exotic behaviour (arrays, arguments, proxies, typed arrays, module namespaces, string wrappers) | through the internal methods only | the object's slots, its internal methods among them |
| Bindings and their values, TDZ | reading, writing, `typeof`; TDZ only by the ReferenceError it throws | `env` cells' bindings, each a binding Record |
| The global object and global bindings | `globalThis`, global code | the Realm Record's [[GlobalObject]] and [[GlobalEnv]] |
| Symbols, the registry | `Symbol.for`, `Symbol.keyFor`, `description` | Symbol values (`State.syms` counts them), the Agent Record's [[GlobalSymbolRegistry]] |
| Function source text | `Function.prototype.toString` | the function's [[SourceText]] slot, the host's text for built-ins |
| Data Blocks, shared or not | TypedArrays, DataView, Atomics | byte `list` cells; `State.shared` names the shared ones |
| The order of jobs | the order of observable effects in promise callbacks | the host-call log: HostEnqueue…Job calls and the host's `next` choices ([state-internal.md](state-internal.md) §3.8) |
| Liveness, indirectly | `WeakRef.prototype.deref`, FinalizationRegistry callbacks; the host chooses when | [[KeptAlive]], the host's `kept` and `collect` answers |
| Host-provided facts | `Date.now`, `Math.random`, locale methods, `print` output | the host's answers, in the host-call log (`State.hostLog`) |

Code cannot observe: ids and allocation order, internal slots except through methods, which algorithm or step is
running, the execution-context stack (beyond what errors and `new.target`/`this` reveal), a module's [[Status]]
(only its effects), or the job queue's contents.

## 3. In the model and the machine

`Ecma.State` has no per-kind stores. Everything with identity is a cell of one
heap, `heap : M.Heap (Cell M)`, addressed by a reference:

| Cell | Holds |
|---|---|
| `record kind fs` | a Record with identity (Realm, Script, Module, Agent, PromiseCapability, ...): its sort and fields |
| `list xs origin` | a List with identity |
| `object slots props` | an object: its internal slots, and its own properties, each an attribute Record of the heap |
| `env kind fs binds` | an Environment Record: its fields and its bindings by name, each a binding Record |

Beside the heap: `stack` (the execution context stack, the running context
last), `resumed` (the Completion Record the running computation was last
resumed with), `agent` (the Agent Record), `syms` (Symbols created), and the
parse bookkeeping: `parses`, `strictParses`, `jsonParses`, `directParses`,
`moduleParses`, `roots` (each parse's root Parse Node) and `covers` (each cover's reparse).

## 4. Layer 3: the running algorithms

The spec's own continuation: for each active algorithm, its current step, its
aliases and the completion in flight.

| Where | What exists |
|---|---|
| The machine | data: `Cfg` = the state, the frames (innermost first) and the control `ctl` (an expression, condition, statement, call, value, return or escape being processed). A `Frame` has its algorithm `alg`, its Abstract Closure literals, its Parse Node, numbered `slots`, its kind, its step `path` and its continuations |
| Suspended contexts | the contexts are Records on the heap; the state keeps each one's saved frames by its address (`State.frames`; [state-internal.md](state-internal.md) §3.3) |

What the machine's data lacks and the debugger supplies: slot names (from the
algorithm's aliases), the step's text (from the clause id and `path`), and
source spans.

**Dead slots.** A slot not yet bound reads `unbound`. The machine writes a slot only by
Let, Set or a binder, so it never clears one and nothing is shown as moved ([README](README.md), D11).

## 5. Transient values

Values that the spec defines but that live only in aliases or on the operand stack, never in a store: Reference
Records, Completion Records (including one being propagated), Property Descriptors, Iterator Records (their
[[Done]] is a shared cell, §3.9), Lists and Records without identity, ClassFieldDefinition and ClassElement
records during class evaluation, PromiseCapability Records before they are stored.

## 6. Not spec state

| Group | Contents |
|---|---|
| The host (`Ecma.Host`, `Engine.Host`) | its operations: the host-defined clauses (`hook`), the choices at primitives it decides, the next job, preparation and cleanup of jobs, ClearKeptObjects, collection, "such that" choices. The five fixed Agent Record fields it chooses are spec facts, shown in the Agent view |
| Host bookkeeping beside the heap | the host-call log `hostLog` (each call and its answer), the shape log `shapeLog`, `saved` |
| Parser | tokens, goals, cover grammars, fuel: ParseText is atomic (a Parse Node or errors); the parse bookkeeping beside the heap (§3) records each invocation |
| Model plumbing | fuel, the running SDO calls' memo (`memo`, `evalNodes`), the built-in calls' arguments (`passed`), a Model's representations (Fast's hash-indexed tables) |

## 7. Derived at a pause, never stored

The running execution context, the active function object, the current Realm Record, GetActiveScriptOrModule;
GetThisEnvironment and whether code is strict; the memory model's relations; "referenced by" (a reverse index,
built on request); whether a binding is in its TDZ (from its state); liveness is **not computable** (§9.9.2
defines it over all possible futures).
