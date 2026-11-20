# Doubts: data sorts (sorts.emu)

Spec-issue candidates are marked **[spec issue]**.

## Records

- **Environment Record, PrivateEnvironment Record, Reference Record, Private Name, execution context, Realm Record, Script Record, WaiterList Record, ModuleRequest / LoadedModuleRequest / ImportAttribute Record** (their own clauses): the spec does not call these Records. It calls them a "specification type", "specification mechanism" or "specification device", or says one "consists of the following fields". They are Record kinds here because the spec makes them with "a new X" and reads their fields.
- **Private Name** (sec-private-names): [[Description]] is called an "internal slot", where every other specification type says "field". HasSlot cannot be used because the subject is often a String or Symbol. **[spec issue]**
- **Synthetic Module Record** (sec-synthetic-module-records): it is a subclass of Module Record only by implication ("In addition to the fields defined in Table Module Record Fields"). sec-abstract-module-records names only Cyclic Module Record and Source Text Module Record as subclasses. super="Module Record" is given. **[spec issue]** (editorial)
- **LoadedModuleRequest Record** (sec-modulerequest-record): it has ModuleRequest Record's fields plus [[Module]], but the spec does not make it a subtype and writes "a ModuleRequest Record or a LoadedModuleRequest Record" where both are allowed. The two are kept separate.
- **ResolvedBinding Record** (sec-abstract-module-records): it has no paragraph of its own. Its definition is the record-literal form in ResolveExport's row of the abstract-methods table.
- **ECMAScript code execution context** (sec-execution-contexts): it is a subtype of execution context only through "the additional state components". As a Record kind it is correct only if every such context comes from "a new ECMAScript code execution context" (lines 13871, 26804, 29257, 29503, 30492). The "a new execution context" sites (12166, 14456, 52023) are built-in, realm and host contexts, which is consistent.
- **Super Reference Record** (sec-reference-record-specification-type): it is defined by a field value ([[ThisValue]] is not ~empty~), not by a kind. The test is IsSuperReference, guarded by a Reference Record check because that is IsSuperReference's parameter type.
- **Memory event** (sec-memory-model-fundamentals): it includes "host-specific events", which have no definition. A host's event Records need a kind with super "Memory event". Otherwise they fail the test instead of stopping.
- **WriteSharedMemory / ReadModifyWriteSharedMemory** (sec-memory-model-fundamentals): the dfns are the bare names, and the Record literals use them, but the text also writes "X event".
  - ReadModifyWriteSharedMemory event (190) and its plural (191) must fold to the record sort ReadModifyWriteSharedMemory at data time.
  - WriteSharedMemory event (189) is an overlay test that delegates to WriteSharedMemory (35).
  - The literal "WriteSharedMemory { … }" must create kind 35.
- **implementation-defined Completion Record** (sec-debugger-statement-runtime-semantics-evaluation): its one use is the construction "Return a new implementation-defined Completion Record." That phrase needs its own meaning, a host choice. As a test the sort accepts any Completion Record.
- **fully / populated** (sec-property-descriptor-specification-type): the dfn is the compound "fully populated Property Descriptor", and the inventory splits it in two. "fully" carries the guarded definition and "populated" is *true*. Folding the compound into one adjective at data time would be cleaner.
- **possibly empty** (sec-list-and-record-specification-type): the inventory splits "possibly" (109) from "empty" (110), but "a possibly empty List" is a List of any length.
  - The entry is named "possibly empty". The data pass must fold the pair and drop the "empty | List" pairing for its use (line 20093, "_restSub_ is a possibly empty List"). Otherwise IsEmpty wrongly applies.

## Objects

- **extensible** (sec-ordinary-object-internal-methods-and-internal-slots): "extensible" has no dfn. Only the em-term "non-extensible" exists, and it is defined by observation (sec-invariants-of-the-essential-internal-methods).
  - The test reads [[Extensible]]. For an object without that slot (a Proxy, for example) the test reaches a prose step, which is residue.
  - All 5 uses are about ordinary objects or functions the spec creates.
  - **[spec issue]**: define "extensible", for example as [[Extensible]] for ordinary objects.
- **Array / String / arguments exotic object, TypedArray, module namespace exotic object** (sec-array-exotic-objects, sec-string-exotic-objects, sec-arguments-exotic-objects, sec-typedarray-exotic-objects, sec-module-namespace-exotic-objects): their dfns say "its other essential internal methods use the definitions in 10.1". That is read to cover Table 5's [[Call]]/[[Construct]], which 10.1 does not define, so the tests reject an object that has either method (HasMethod). It is unclear whether Table 5 counts as "other essential internal methods". **[spec issue]** (wording)
- **ordinary, ECMAScript function object, built-in, bound function / Proxy / exotic objects, immutable** (sec-object-internal-methods-and-internal-slots): the steps "is not the internal method defined in <clause>" use a new phrase in sorts.emu that maps to IsOrdinaryMethod (prim 22). Its meaning already compares the method's clause with any clause, but its doc in object.emu still says "ordinary object internal method" and should be generalized.
- **Proxy exotic object** (sec-proxy-object-internal-methods-and-internal-slots): the dfn works by internal methods, not by [[ProxyHandler]], and the test follows the dfn. The two agree in every reachable state, because only ProxyCreate installs those methods, and it also sets [[ProxyHandler]] and [[ProxyTarget]].
- **ECMAScript function object** (sec-ecmascript-function-objects): it has no dfn. The test is an ordinary object whose [[Call]] is the one in 10.2.1. Having [[ECMAScriptCode]] would be an equivalent reading.
- **built-in** (sec-built-in-function-objects): "built-in object" (4.4) is about where an object comes from, which state cannot decide. The adjective occurs only in "built-in function object", so the test is an ordinary object whose [[Call]] is the one in 10.3.1. That would be wrong if the adjective were ever used on a non-function.
- **immutable / prototype exotic object** (sec-immutable-prototype-exotic-objects): the inventory splits the single dfn immutable-prototype-exotic-object, and "prototype exotic object" is not a term on its own. Both entries carry the whole test. Folding them at data time would be cleaner.
- **initialized RegExp instance** (sec-properties-of-regexp-instances): RegExpBuiltinExec's parameter type is not defined anywhere. It is read as a RegExp instance whose [[RegExpMatcher]] is no longer *undefined*. Callers guarantee only RequireInternalSlot(R, [[RegExpMatcher]]). **[spec issue]** (undefined term)
- **iterator object** (sec-iterator-interface): conforming to the iterator interface is a requirement on how `next` behaves, not a property of state, so the sort is residue. Its one use is EnumerateObjectProperties' return type, which is implementation-defined.
- **Array Iterator Instance, RegExp String Iterator Object Instance, For-In Iterator instance** (sec-properties-of-array-iterator-instances, sec-properties-of-regexp-string-iterator-instances, sec-properties-of-for-in-iterator-instances): these are not defined terms. They occur only in "has all of the internal slots of a X", so each test is that clause's slot table. Capitalization and wording vary. **[spec issue]** (editorial)
- **Generator** (sec-properties-of-generator-instances): testing by [[GeneratorState]] also admits the objects CreateIteratorFromClosure makes (non-empty [[GeneratorBrand]]). That matches the spec's own return types ("a Generator" from CreateMapIterator and IteratorZip).
- **ArrayBuffer / SharedArrayBuffer** (sec-properties-of-the-arraybuffer-instances, sec-properties-of-the-sharedarraybuffer-instances): the slot tables do not separate the two. The tests inline IsSharedArrayBuffer's step ([[ArrayBufferData]] is a Shared Data Block). Calling IsSharedArrayBuffer would recurse once headers are checked, because its parameter type is these two sorts. [[ArrayBufferDetachKey]] would be an equivalent test for ArrayBuffer.
- **Uint8Array** (sec-validateuint8array): it has no dfn. The test is the Boolean form of ValidateUint8Array: [[TypedArrayName]] is *"Uint8Array"*.
- **Promise** (sec-properties-of-promise-instances): alg=IsPromise, whose parameter is "an ECMAScript language value". Once parameter headers are checked, testing a Record would stop instead of returning *false*. A guard would fix it: "If _v_ is not an ECMAScript language value, return *false*."
- **data property / accessor property** (sec-object-type): both dfns are prose. PropertyIsKind reads the kind given at OwnPropertyCreate and OwnPropertyReplace. The subject is an own property, as OwnPropertyLookup returns it.
- **(no entry)**: async iterator object, IteratorResult object, host-defined exotic object, callable, and "built-in function object" as a noun are not in the inventory.

## Values

- **code point / Unicode code point** (sec-source-text): ECMA-262 has no dfn; the term comes from the Unicode Standard. The test uses the U+0000–U+10FFFF range that sec-source-text states.
- **code unit** (sec-ecmascript-language-types-string-type): String elements are "16-bit unsigned integer values" treated as UTF-16 code units, yet the text writes "the numeric value of a code unit". The model identifies code units and code points with their numeric values, so code unit, code point, byte value and integer overlap.
- **surrogate** (sec-ecmascript-language-types-string-type): only "leading surrogate" and "trailing surrogate" are defined. The bare noun is tested as their union, [0xD800, 0xDFFF]. "leading" and "trailing" each carry their compound's full definition, including "is a code unit".
- **character** (sec-pattern-semantics): defined relative to its pattern (BMP: a code unit; Unicode: a code point). The sort's context phrase ph-character-of-pattern reads the pattern's mode from the _regexpRecord_ the steps or header name. A header or test that names none (CharacterRange, CharSetElement's test) leaves the pattern open, and the test there is the union, a code point.
- **CharSetElement** (sec-pattern-notation): defined relative to _regexpRecord_.[[UnicodeSets]], which its test does not receive, so the test is the union of the cases.
- **CharSet** (sec-pattern-notation): a mathematical set, held as a List. The test rejects duplicates and counts a one-character sequence as equal to its character.
- **single** (sec-pattern-notation): it has no dfn. Its one use is "Assert: _charSet_ contains only single code points", read as "one character".
  - Under the conjunctive meaning, a one-element List passes "single" but fails "code point", although the clause makes a character and a sequence of one character interchangeable.
  - **[spec issue]**: use the wording "consists of a single character".
- **empty** (sec-list-and-record-specification-type): its one standalone use is "an empty CharSet". IsEmpty covers CharSets only through their List representation. "Return the empty CharSet" (line 38959) is a construction, not a test.
- **time value** (sec-time-values-and-time-range): the dfn sentence (a finite integral Number, or *NaN*) gives no range, but the paragraph gives ±8.64 × 10^15. LocalTime's note says its input "may be any Number value".
  - The test follows the dfn sentence. If the range were part of the definition, "_tv_: a finite time value" checks near the boundary would fail.
  - **[spec issue]** (ambiguity)
- **epoch nanoseconds count** (sec-epoch-nanoseconds): the dfn includes the range MinEpochNanoseconds..MaxEpochNanoseconds, and the test keeps it.
  - GetUTCEpochNanoseconds and GetNamedTimeZoneEpochNanoseconds are reached from UTC(_t_) with _t_ deliberately not limited to the time value range. Their results can exceed the bound by up to a day, and return-type checks would then fail. **[spec issue]**
  - MinEpochNanoseconds and MaxEpochNanoseconds must resolve as emu-eqn constants. TimeConst covers only HoursPerDay … msPerDay.
- **non-negative / positive** (sec-mathematical-operations): neither has a definition in ECMA-262. sec-ecmascript-language-types-number-type counts +0𝔽 as positive and -0𝔽 as negative.
  - "non-negative" Number is tested as [+0𝔽, +∞𝔽], which excludes -0𝔽 and *NaN*.
  - "positive" is used only with integers, so only its mathematical sense (> 0) is given.
- **odd** (sec-mathematical-operations): not defined; only "odd significand" is. "an odd integral Number" is read as ℝ(_v_) being odd.
- **byte / byte value** (sec-data-blocks): "byte" has no dfn. Its one use, "For each byte _byte_ of _toEncode_", is over a List of byte values, so it delegates to "byte value". It is better folded as a variant at data time. The inventory has only the plural "byte values" (167), so the entry is the singular dfn under that id.
- **integer index / array index** (sec-object-type): CanonicalNumericIndexString is used inside an overlay body, not as alg=, because it returns a Number or *undefined*. The lower bound +0𝔽 excludes -0𝔽, so InInterval's Number case must honour -0𝔽 < +0𝔽.
- **sequence of Unicode code points** (sec-source-text): "sequence" is never defined. The List reading is the spec's own: ParseText uses StringToCodePoints' "List of code points", and UnicodeMatchProperty returns "the List of Unicode code points _p_". **[spec issue]**: say "List of code points" throughout.
- **Plurals of Known sorts** (46 ECMAScript language values, 51 property keys, 60 Strings, 152 integers) must fold to Known 14, 15, 2 and 9 at data time.

## Other

- **error** (sec-parsetext): never defined, so it is residue. ParseText returns "a non-empty List of *SyntaxError* objects", while its callers (StringToNumber, StringToBigInt, PerformEval, CreateDynamicFunction, … 10 uses) test "is a List of errors".
  - An [[ErrorData]] reading was rejected, because sec-properties-of-error-instances limits [[ErrorData]]'s only specified use to Object.prototype.toString and Error.isError.
  - The residue fires only once the value is a List, but that includes StringToNumber on any non-numeric string, so it blocks ToNumber's error path.
  - **[spec issue]**: write "a List of *SyntaxError* objects" at the call sites, as ParsePattern's caller does.
- **binding, strict, mutable, uninitialized** (sec-environment-records; sec-declarative-environment-records-createimmutablebinding-n-s; sec-declarative-environment-records-createmutablebinding-n-d): "binding" has no dfn, and there is no binding value yet. All four are residue, so every use ("a strict / mutable / uninitialized binding") stops.
  - Plan: an IsBinding test in the BindingLookup/BindingSet family, plus one prim, BindingIs(~strict~ | ~mutable~ | ~uninitialized~, _b_), in place of IsStrictBinding, IsMutableBinding and IsUninitializedBinding.
  - Its laws: CreateImmutableBinding(N, *true*) records strict; CreateMutableBinding gives mutable; Create*Binding records uninitialized; InitializeBinding and CreateImportBinding record initialized.
  - **[spec issue]**: "binding" is undefined.
- **internal slot name** (sec-object-internal-methods-and-internal-slots): the spec lists no closed set of slot names. Slot names, internal-method names and Record field names share the [[F]] notation and one name space in the model (FieldId), so IsInternalSlotName accepts any [[F]] name.
- **grammar symbol / nonterminal** (sec-context-free-grammars): Val has a nonterminal form (.nt) but no terminal-symbol form. Contains is called with terminals (Contains `await`, Contains `super`; lines 25301, 26660, 26962), so IsGrammarSymbol under-approximates until terminals become values and a phrase "the terminal `x`" exists.
- **nonterminal** (sec-context-free-grammars): 3 of its 5 uses are "If _child_ is an instance of a nonterminal". There the sort is InstanceOf's operand, not a test of a symbol value, and that phrase needs its own meaning.
- **Unicode property name / Unicode property value** (sec-runtime-semantics-unicodematchproperty-p, sec-runtime-semantics-unicodematchpropertyvalue-p-v): both are marked emu-not-ref and never defined. Membership comes from spec tables or from the versioned, external UCD files PropertyAliases.txt and PropertyValueAliases.txt, so both are residue.
  - The runtime uses at lines 39082 and 39334 are compound phrases that need their own meanings.
  - UnicodeMatchPropertyValue's return type does not say which property the value belongs to.
  - **[spec issue]**
- **Data Block / Shared Data Block** (sec-data-blocks): the clause calls a Shared Data Block "a data block", yet headers say "a Data Block or a Shared Data Block" and the text says the two "can be distinguished". They are read as disjoint (IsDataBlock, IsSharedDataBlock). **[spec issue]**: is a Shared Data Block a Data Block?
- **Matcher, MatcherContinuation, Job Abstract Closure, read-modify-write modification function** (sec-pattern-notation, sec-jobs, sec-arraybuffer-notation): each is defined by its signature, and read-modify-write also by purity and atomicity, none of which can be checked on a value.
  - ClosureKind reads the closure literal's kind instead. Every instance in the spec comes from "a new S with parameters …", and host Jobs are assumed to be such literals too.
  - "Job Abstract Closure" has no dfn of its own; the dfn is "Job".
- **Slot and method tests generally**: HasSlot and HasMethod take (slot, subject) and stop with sortError on a non-Object. Every slot or method test is therefore steps that begin "If _v_ is not an Object, return *false*."
