module

public import Ecma.Host.Laws.Basic

@[expose] public section

/-!
# The laws of the host hooks

What every host hook returns, and the hooks that must answer alike at every call (sec-hosts-and-implementations).
-/

namespace Ecma

variable {M : Model}

/-- The laws of the host hooks. -/
structure Host.HookLaws (H : Host M) : Prop where
  /-- sec-hosts-and-implementations:
  "A host hook must conform to at least the following requirements: It must return either a normal completion or a throw completion."
  Reading: a host hook's answer is no break, continue or return completion (a value that is no Completion Record
  is a normal completion's). -/
  hookCompletion : ∀ c xs s r s', H.answers c xs s r s' → compType r = Known.eNormal ∨ compType r = Known.eThrow
  /-- sec-hostensurecanaddprivateelement, the requirements:
  "Any two calls of this abstract operation with the same argument must return the same kind of Completion Record."
  Reading: the [[Type]] of HostEnsureCanAddPrivateElement's answer is one function of its argument, whatever the
  state of the call. -/
  privateElementSameKind : ∃ kind : List (Val M) → EnumId, ∀ c xs s r s',
    Gen.clauses[c]? = some "sec-hostensurecanaddprivateelement" → H.answers c xs s r s' → compType r = kind xs
  /-- sec-hostgetsupportedimportattributes, the requirements:
  "It must return a List of Strings, each indicating a supported attribute. Each time this operation is called, it must return the same List with the same contents in the same order."
  Reading: every call answers a List of the same Strings in the same order (the default's new empty List at each
  call conforms, so "the same List" is its contents). -/
  supportedImportAttributes : ∃ ids : List M.Str, ∀ c xs s r s',
    Gen.clauses[c]? = some "sec-hostgetsupportedimportattributes" → H.answers c xs s r s' →
    listElems s' r = some (ids.map .str)
  /-- sec-hostgetcodeforeval:
  "HostGetCodeForEval ( arg: an Object, ): a String or ~no-code~"
  Reading: HostGetCodeForEval answers a String or ~no-code~. -/
  getCodeForEval : ∀ c xs s r s', Gen.clauses[c]? = some "sec-hostgetcodeforeval" → H.answers c xs s r s' →
    (∃ e, r = .enum e ∧ Gen.enums[e]? = some "no-code") ∨ ∃ x, r = .str x
  /-- sec-hosthassourcetextavailable, the requirements:
  "It must be deterministic with respect to its parameters. Each time it is called with a specific func as its argument, it must return the same result."
  Reading: HostHasSourceTextAvailable's answer is one function of its argument, whatever the state of the call. -/
  hasSourceTextAvailable : ∃ f : List (Val M) → Val M, ∀ c xs s r s',
    Gen.clauses[c]? = some "sec-hosthassourcetextavailable" → H.answers c xs s r s' → r = f xs

end Ecma
