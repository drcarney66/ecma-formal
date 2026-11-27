# 68. `WeakRef` execution single-cell loop, `SuspendThisAgent`'s `NotifyWaiter` argument, `"Canonical property value"` column, and metamodel sort gaps

- **Location:** §9.9.3 Execution (`#sec-weakref-execution`), step 1.b; §25.4.3.11 SuspendThisAgent
  (`#sec-suspendthisagent`), step 7, against §25.4.3.12 NotifyWaiter (`#sec-notifywaiter`); §22.2.2.9.8
  UnicodeMatchPropertyValue (`#sec-runtime-semantics-unicodematchpropertyvalue-p-v`), step 3; §16.2.1.5 Abstract Module
  Records (`#sec-abstract-module-records`).
- **Kind:** quantification bug, parameter-type mismatch, nonexistent UCD column header, and stale subclass/sort prose.
- **Model erratum:** `WeakRefAllCellsAndSuspendWaiter`, baked-in SpecTec reading proposed (`Collected` / `Cell.Emptied`
  in `spec/spectec/prose/25-host-laws-changes.spectec`, `$SuspendAgentUntil` in `00-decls.spectec`,
  `$CanonicalPropertyValue` in `S22.spectec`, and `super [#"Module Record"]` on `#"Synthetic Module Record"` in
  `00-decls.spectec`).
- **Upstream:** Checked 2026-11-19: issue #3328 (open, 2024-05), "Typo in step 7 of the SuspendThisAgent abstract
  operation", reports the `NotifyWaiter` parameter bug; none found for the `FinalizationRegistry` single-cell loop, the
  `"Canonical property value"` column, or `Abstract Module Records` omitting `Synthetic Module Record` (searched for
  "Canonical property value" and "sole concrete subclass Source Text Module Record").

## Text

§9.9.3 (`Execution`):

> 1.b. For each FinalizationRegistry _finalizationRegistry_ such that _finalizationRegistry_.[[Cells]] contains a Record _cell_ such that _cell_.[[WeakRefTarget]] is _value_, do
>      i. Set _cell_.[[WeakRefTarget]] to ~empty~.

`SuspendThisAgent`:

> 7. Perform LeaveCriticalSection(_waiterList_) and suspend the surrounding agent until the time is _waiterRecord_.[[TimeoutTime]], performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. The surrounding agent can only wake from suspension due to a timeout or due to another agent calling NotifyWaiter with arguments _waiterList_ and _thisAgent_ (i.e. via a call to `Atomics.notify`).

`UnicodeMatchPropertyValue`:

> 3. Let _value_ be the canonical property value of _v_ as given in the “Canonical property value” column of the corresponding row.

§16.2.1.5 (`Abstract Module Records`):

> This specification defines the abstract subclass named Cyclic Module Record and its concrete subclass named Source Text Module Record.

## Problem

Four prose-vs-signature defects where SpecTec bakes in a non-literal fix:

1. **`FinalizationRegistry` duplicate target cells (§9.9.3 step 1.b).** Step 1.b iterates once *per
   FinalizationRegistry* and binds a single `_cell_`, leaving duplicate registrations for the same target (`fr.register(o, 1);
   fr.register(o, 2)`) un-emptied! SpecTec's `Cell.Emptied` (`25-host-laws-changes.spectec`) empties *every* matching
   cell Record.
2. **`SuspendThisAgent` step 7 (#3328).** `_thisAgent_` is `AgentSignifier()`, whereas `NotifyWaiter` requires a
   `Waiter Record` (`_waiterRecord_`). SpecTec's `$SuspendAgentUntil` and `$WakeAgent` match via `Waiter Record`.
3. **Nonexistent `"Canonical property value"` column (§22.2.2.9.8 step 3).** UCD `PropertyValueAliases.txt` is a
   headerless semicolon-delimited file with no `"Canonical property value"` column (a copy-paste from
   `UnicodeMatchProperty` step 3's `"Canonical property name"` column), and both `UnicodeMatchProperty` and
   `UnicodeMatchPropertyValue` declare undefined return sorts while returning `a List of Unicode code points`. SpecTec's
   `$CanonicalPropertyValue` selects field 3 (the long property value name).
4. **Metamodel sort omissions.** §16.2.1.5 states `Cyclic Module Record` is the *only* `Module Record` subclass, omitting
   `Synthetic Module Record` (§16.2.1.8, used for JSON modules — `00-decls.spectec` declares `super [#"Module Record"]`
   on `#"Synthetic Module Record"`); §6.2.11 calls `Private Name`'s `[[Description]]` an *"internal slot"* on a
   non-Object (`00-decls.spectec` models it as a Record field); and §6.2.9 defines `block[i]` indexing only on `Data
   Block` before declaring `Shared Data Block` disjoint (`lean/Ecma` indexes both uniformly).

## Examples

```js
print(/\p{gc=Lu}/u.test("A"), /\p{General_Category=Uppercase_Letter}/u.test("A"));
```

| | `/\p{gc=Lu}/u.test("A")` |
|---|---|
| literal §22.2.2.9.8 step 3 | references nonexistent `"Canonical property value"` column |
| V8, SpiderMonkey, JavaScriptCore | `true` |
| formal model (proposed reading) | `true` |

## Proposed wording

In §9.9.3 step 1.b iterate over every matching `_cell_` in `_finalizationRegistry_.[[Cells]]`; in `SuspendThisAgent`
step 7 replace `_thisAgent_` with `_waiterRecord_`; in `UnicodeMatchPropertyValue` step 3 name the third (long value)
field of `PropertyValueAliases.txt` and return `a List of Unicode code points`; and in §16.2.1.5 list `Synthetic Module
Record` alongside `Cyclic Module Record`.

## test262

`built-ins/RegExp/property-escapes/` exercises `UnicodeMatchPropertyValue`, `language/import/import-attributes/` tests
JSON `Synthetic Module Record`s, and `built-ins/FinalizationRegistry/` tests multiple cell registrations.
