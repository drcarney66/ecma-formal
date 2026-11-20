# Spec-internal state

Layer 2 of [state.md](state.md): the records the algorithms read and write
that code cannot name, and where the model (`lean/Ecma/State.lean`) keeps
each. All of them are cells of the one heap (state.md §3), each Record's
fields named as the spec names them; a few are fields of `Ecma.State` beside
the heap.

### 3.1 The Agent Record (§9.6)

The pinned spec's Agent Record has ten fields. Five are fixed for the agent's life ("cannot change") or never
changed by an algorithm: the host chooses them when it makes the Record (`Engine.Host.newAgent`). Five are
agent state. The Record is a `record` cell; `State.agent` is its reference.

| Field | Notes |
|---|---|
| [[LittleEndian]] | fixed |
| [[CanBlock]] | fixed for the agent's life: the host's choice |
| [[IsLockFree1]], [[IsLockFree2]], [[IsLockFree8]] | fixed |
| [[Signifier]] | fixed: the Record itself |
| [[CandidateExecution]] | the memory model's events (§3.10), appended |
| [[KeptAlive]] | a List: appended by AddToKeptObjects, emptied by ClearKeptObjects |
| [[ModuleAsyncEvaluationCount]] | a counter |
| [[GlobalSymbolRegistry]] | a List, append-only ("never reassigned") |

### 3.2 Agent clusters (§9.7): not modelled

An agent cluster is a set of agents that share memory. The model runs one agent, so these are not representable:
other agents and their Agent Records; a WaiterList shared with another agent (`Atomics.wait` can only time out
or be woken by its own agent's `Atomics.notify`, which cannot happen while it waits); `$262.agent` in test262;
the cluster-wide parts of the memory model (other agents' events). [[CanBlock]] is fixed by the Host.

### 3.3 Execution contexts (§9.4, Tables 20–22)

- **The contexts:** each execution context is a `record` cell, with its identity.
- **The stack:** `State.stack`, the running context last.
- **Off the stack:** a context made and not yet pushed, or suspended (a generator, an async function waiting at
  Await, a module body), is reached from what holds it: a generator's [[GeneratorContext]], a module's [[Context]],
  an Await's continuation closure. `State.suspended` is the context a transfer last suspended.
- **Components:** the cell's fields Function, Realm, ScriptOrModule, LexicalEnvironment, VariableEnvironment,
  PrivateEnvironment, Generator. The code evaluation state is no field: the running context's is the running
  algorithms' (layer 3, [state.md](state.md) §4); a suspended context's is the computation the run saved for it
  (its frames, kept by the context's address in `State.frames`).

### 3.4 Realms (§9.3)

`record` cells. Fields: [[Intrinsics]] (a Record of the intrinsics by name), [[GlobalObject]], [[GlobalEnv]],
[[TemplateMap]], [[LoadedModules]], [[AgentSignifier]], [[HostDefined]].

### 3.5 Environments (§9.1, §9.2)

- **Environment Records** (`env` cells: the kind, the fields, the bindings by name): Declarative, Function (with [[ThisValue]], [[ThisBindingStatus]],
  [[FunctionObject]], [[NewTarget]]), Object, Global (object record, declarative record, [[GlobalThisValue]]),
  Module (with indirect import bindings). Each has [[OuterEnv]]. Binding state includes "uninitialized" (TDZ),
  mutability and strictness.
- **PrivateEnvironment Records** (`record` cells): [[OuterPrivateEnvironment]], [[Names]].
- **Private Names** (`record` cells): [[Description]].

### 3.6 Scripts and modules (§16.1, §16.2)

All are `record` cells.

- **Script Records:** [[Realm]], [[ECMAScriptCode]], [[LoadedModules]], [[HostDefined]].
- **Module Records:** [[Realm]], [[Environment]], [[Namespace]], [[HostDefined]]; Source Text
  Module Records (Cyclic) or Synthetic Module Records.
  - **Cyclic fields** (Table 39): [[Status]] (`new`, `unlinked`, `linking`, `linked`, `evaluating`,
    `evaluating-async`, `evaluated`), [[EvaluationError]], [[DFSAncestorIndex]], [[RequestedModules]],
    [[LoadedModules]], [[CycleRoot]], [[HasTLA]], [[AsyncEvaluationOrder]] (unset, an integer, done),
    [[TopLevelCapability]], [[AsyncParentModules]], [[PendingAsyncDependencies]].
  - Source Text fields: [[ECMAScriptCode]], [[Context]] (the suspended module body), [[ImportMeta]], the
    import and export entries.
- **GraphLoadingState Records** (Table 41): [[PromiseCapability]], [[IsLoading]],
  [[PendingModulesCount]], [[Visited]], [[HostDefined]].
- **What the spec constrains of the host's module map.** HostLoadImportedModule must be idempotent: the same
  (referrer, request) must give the same Module Record each time (§16.2.1.10's requirements), and the result is
  recorded in the referrer's [[LoadedModules]]. Only [[LoadedModules]] is spec state. How the host meets that
  requirement is the host's: its answers are in the host-call log (`hook` calls), shown in the host group.
- **The loading state of a run** is the GraphLoadingStates plus the pending host loads (jobs and the host's
  pending `loadImportedModule` calls) plus each module's [[Status]].

### 3.7 Objects and internal slots

`object` cells: an object's internal slots, a Record of the slots the spec gives its kind (ordinary, array, error,
the primitive wrappers, ECMAScript, built-in and bound functions, proxy, arguments, typed array, module namespace,
promise, generator, ArrayBuffer, DataView, the iterators, ...), and its own properties.

- **Properties:** by key, each an attribute Record of the heap; a Model's table (Fast: hash-indexed in creation
  order) is representation ([state.md](state.md) §6).
- **Promises:** [[PromiseState]], [[PromiseResult]], [[PromiseFulfillReactions]], [[PromiseRejectReactions]]
  (PromiseReaction Records: capability, type, handler), [[PromiseIsHandled]].
- **Generators:** [[GeneratorState]], [[GeneratorContext]] (a context id, §3.3), [[GeneratorBrand]]; async
  generators add [[AsyncGeneratorQueue]].
- **FinalizationRegistry:** [[Cells]], [[CleanupCallback]]; **WeakRef:** [[WeakRefTarget]].

### 3.8 Jobs (§9.5)

The spec says only that hosts run jobs (HostEnqueuePromiseJob, HostEnqueueGenericJob, HostEnqueueTimeoutJob,
HostEnqueueFinalizationRegistryCleanupJob) with ordering requirements; the queue is the host's. The model keeps no
queue: each HostEnqueue…Job call is a `hook` entry of the host-call log (`State.hostLog`), with its Job Abstract
Closure and realm, and the host's `next` entry names the call whose job it runs. The jobs pending are those
scheduled and not yet taken. Their order is part of the spec's state in that it is observable (layer 1).

### 3.9 Records and Lists with identity

Spec Records and Lists that several algorithms share by reference are `record` and `list` cells: the
{ [[Value]] } records of CreateResolvingFunctions and PerformPromiseAllSettled, the remaining-elements counters,
resolving-function records, [[DisposableResourceStack]] lists, the promise combinators' value lists, Link and
Evaluate's module stacks, Iterator Records' [[Done]] cells and Iterator Record lists, Data Blocks, Shared Data
Blocks (`State.shared` names them), Waiter Records.

### 3.10 Shared memory and the memory model (§25.4, §29)

- **[[CandidateExecution]]:** the agent's Agent Events Record (its events: reads, writes, read-modify-writes, and
  synchronize events) and the chosen relations. Derived relations (agent-order, reads-bytes-from,
  happens-before, ...) are computed, not stored.
- **WaiterList Records** (`State.waiterLists`, the agent cluster's store: each Record by its Shared Data Block
  and byte offset), Waiter Records, and the critical sections the agent is in (`State.critical`).

### 3.11 Annex B bookkeeping

The steps that replace a FunctionDeclaration's Evaluation (§B.3.2): `State.evalSteps`, by Parse Node, the latest
first. The Environment Records created for a Catch clause (§B.3.4): a declarative `env` cell whose [[CreatedFor]]
the overlay sets to the |Catch| (spec/formal/env.emu). Both are state the Annex B algorithms consult, so they
are spec state when Annex B is enabled.
