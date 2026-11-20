//! The residue: steps that keep prose (K: a statement form with a prose
//! hole; U: no statement form), each sent to one of three channels:
//! (a) an upstream regularization, with its reason; (b) a declared
//! primitive, by name; (c) annotated prose with an attached meaning. The
//! first kind that claims the step decides, in the order of `KINDS`.

#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub enum Channel {
    Upstream,
    Prim,
    Annotated,
}

impl Channel {
    pub fn label(self) -> &'static str {
        match self {
            Channel::Upstream => "(a) upstream regularization",
            Channel::Prim => "(b) declared primitive",
            Channel::Annotated => "(c) annotated prose",
        }
    }
}

/// A kind: its name, its channel, and the words that mark it (any of them).
pub struct Kind {
    pub name: &'static str,
    pub channel: Channel,
    words: &'static [&'static str],
}

/// The kinds, in the order they are tried.
pub const KINDS: &[Kind] = &[
    Kind { name: "prose Assert", channel: Channel::Annotated, words: &["Assert:"] },
    Kind { name: "spec-issue candidate", channel: Channel::Upstream, words: &[] },
    Kind {
        name: "choice: such that, as small as possible, implementation-defined",
        channel: Channel::Annotated,
        words: &["such that", "Choose", "choose", "nondeterministic", "as small as possible", "any such", "implementation-defined", "an implementation"],
    },
    Kind { name: "host-defined", channel: Channel::Annotated, words: &["host"] },
    Kind { name: "environment-record bindings (prose methods)", channel: Channel::Upstream, words: &["binding", "bound value"] },
    Kind { name: "declared primitive", channel: Channel::Prim, words: &[] },
];

/// The reason given for every environment-record binding step.
pub const ENV_REASON: &str = "Environment Record bindings described in prose; the Record needs a bindings map with declared operations";

/// The reason given to a multi-sentence step that no `REGS` entry names.
pub const MULTI_REASON: &str = "a second sentence: a step of its own or a NOTE";

/// A spec-issue candidate: its one-line reason and the words that mark its steps (all of them).
pub struct Reg {
    pub reason: &'static str,
    marks: &'static [&'static str],
}

/// The candidates whose first sentence is the whole meaning: its primitive, if declared, holds.
const FIRST_MEANS: &[&str] = &["a restatement after '; that is,' that belongs in a NOTE", "a second sentence stating the result's range; it belongs in an Assert or a NOTE"];

/// The spec-issue candidates, in the order they are tried.
pub const REGS: &[Reg] = &[
    Reg { reason: "a cross-reference sentence ('See … for a description') that belongs in a NOTE", marks: &["See <emu-xref", "for a description"] },
    Reg { reason: "an inline NOTE that belongs in a NOTE step of its own", marks: &["NOTE:"] },
    Reg { reason: "a second sentence stating the result's range; it belongs in an Assert or a NOTE", marks: &["exactly representable"] },
    Reg { reason: "a second sentence that is a step of its own (the allocation-failure throw)", marks: &["If it is impossible to create such"] },
    Reg { reason: "further sentences fixing the byte order and the NaN encoding latitude; they belong in the encoding's declared meaning", marks: &["The bytes are"] },
    Reg { reason: "a second sentence restating the join's definition; it belongs in a NOTE", marks: &["is not inserted either before"] },
    Reg { reason: "a tie-breaking second sentence; it is a step of its own (a choice rule)", marks: &["If there are"] },
    Reg { reason: "a 'Note that' sentence that belongs in a NOTE", marks: &["Note that"] },
    Reg { reason: "a clarifying second sentence that belongs in a NOTE", marks: &["UTF-16 decoding is not applied"] },
    Reg { reason: "a requirement on implementations stated inside a step; it belongs in the clause's prose", marks: &["The representation must have the syntax"] },
    Reg { reason: "an implementation latitude sentence that belongs in a NOTE", marks: &["may be interleaved"] },
    Reg { reason: "an implementation-defined detail sentence that belongs in a NOTE", marks: &["If more than one parsing error"] },
    Reg { reason: "a second sentence that is a step of its own (the no-prefix return)", marks: &["If there is no such prefix"] },
    Reg { reason: "a second sentence restating a consequence of the first; it belongs in a NOTE", marks: &["the empty String is returned"] },
    Reg { reason: "an iterator described in sentences; the description belongs in the clause's prose", marks: &["is never directly accessible"] },
    Reg { reason: "sentences describing the parameters' roles; they belong in the clause's prose", marks: &["provides the *this* value"] },
    Reg { reason: "a second sentence that completes the object's creation (its slots); it belongs in the phrase", marks: &["The new function object has internal slots"] },
    Reg { reason: "a paragraph of definitions inside a step; it belongs in the clause's prose or the table", marks: &["The field names are the names listed"] },
    Reg { reason: "a second sentence that is a special case of the first; it belongs in a step of its own", marks: &["For properties listed in"] },
    Reg { reason: "an atomicity requirement in a second sentence; it belongs in the declared meaning of a primitive", marks: &["performing the combined operation"] },
    Reg { reason: "a requirement paragraph inside a step; it belongs in the clause's prose", marks: &["escaped as described below"] },
    Reg { reason: "a requirement paragraph with examples inside a step; it belongs in the clause's prose and a NOTE", marks: &["shall be escaped in"] },
    Reg { reason: "a conditional second sentence that is an If step of its own", marks: &["record that the newly created binding"] },
    Reg { reason: "a second sentence about the result's type that belongs in a NOTE", marks: &["This may be of type Reference"] },
    Reg { reason: "a parenthetical sentence that belongs in a NOTE", marks: &["(It may be evaluated repeatedly.)"] },
    Reg { reason: "a restatement after '; that is,' that belongs in a NOTE", marks: &["; that is,"] },
    Reg { reason: "a rationale clause ('because …') that belongs in a NOTE", marks: &["because the structure is cyclical"] },
    Reg { reason: "an <ins> edit mark (Annex B's change to the main algorithm); the merged text belongs in the algorithm", marks: &["<ins>"] },
    Reg { reason: "an English list without the serial comma ('a, b and c'), unlike the spec's other lists", marks: &["_otherSet_ and _remainingSet_"] },
    Reg { reason: "a String literal glossed by its code units in parentheses; the gloss belongs in a NOTE", marks: &["*\"$'\"* ("] },
    Reg { reason: "a value literal glossed '(a comma)'; the gloss belongs in a NOTE", marks: &["(a comma)"] },
    Reg { reason: "an inline loop body ('For each …, set …'); elsewhere a loop body is a nested step", marks: &["For each integer", "in the inclusive interval", ", set "] },
    Reg { reason: "a second sentence that is an argument of the encoding (padding); it belongs in the call", marks: &["Padding is included if and only if"] },
];

/// A declared primitive: its name, signature, one-line meaning and group,
/// and the words that mark its steps (all the words of any one list).
pub struct Prim {
    pub name: &'static str,
    pub sig: &'static str,
    pub meaning: &'static str,
    pub group: &'static str,
    marks: &'static [&'static [&'static str]],
}

const NUM: &str = "numeric digits, bits, IEEE";
const GRAM: &str = "grammar, Parse Nodes";
const CHARS: &str = "RegExp CharSets, characters";
const CTX: &str = "execution contexts, agents";
const TAB: &str = "lists, tables";
const MEM: &str = "memory model, data blocks, bytes";
const OBJ: &str = "objects, properties, slots";
const MATH: &str = "Number rounding";
const TZ: &str = "time zones, dates";
const STR: &str = "code units, code points, strings";
const IMPL: &str = "implementation and host facts";

/// The declared primitives, in the order they are tried.
pub const PRIMS: &[Prim] = &[
    // numeric digits, bits, IEEE
    Prim { name: "IndexOfFirstNonDigit", sig: "(s: String, r: integer) → integer", meaning: "the index of the first code unit of s that is not a radix-r digit, or the length of s", group: NUM, marks: &[&["is not a radix-"]] },
    Prim { name: "LeadingOneBits", sig: "(b: byte) → integer", meaning: "the number of leading 1 bits of the byte b", group: NUM, marks: &[&["number of leading 1 bits"]] },
    Prim { name: "CountLeadingZeros32", sig: "(n: integer) → integer", meaning: "the number of leading zero bits of n as an unsigned 32-bit integer", group: NUM, marks: &[&["number of leading zero bits"]] },
    Prim { name: "StartsWithDollarDigits", sig: "(s: String, n: integer) → Boolean", meaning: "whether s starts with \"$\" followed by at least n decimal digits", group: NUM, marks: &[&["followed by", "or more decimal digits"]] },
    Prim { name: "HexValue", sig: "(s: String) → integer", meaning: "the integer that the hexadecimal digits of s denote", group: NUM, marks: &[&["base-16 notation"]] },
    Prim { name: "InCodeUnitRanges", sig: "(c: code unit, rs: List of code unit ranges) → Boolean", meaning: "whether c is one of the listed code units or lies in one of the listed ranges", group: NUM, marks: &[&["ASCII lowercase letter code unit"]] },
    Prim { name: "Int32FromBitString", sig: "(b: bit string) → integer", meaning: "the integer that a 32-bit two's complement bit string represents", group: NUM, marks: &[&["integer represented by the 32-bit two's complement bit string"]] },
    Prim { name: "Negative", sig: "(x: Number) → Number", meaning: "the Number with x's magnitude and the opposite sign", group: NUM, marks: &[&["the negation of"]] },
    Prim { name: "IntegerPower", sig: "(b: integer, e: integer) → integer", meaning: "b raised to the power e, for e ≥ 0", group: NUM, marks: &[&["raised to the power"]] },
    Prim { name: "SignificantDigitCount", sig: "(n: mathematical value) → integer", meaning: "the number of significant digits in the decimal representation of n", group: NUM, marks: &[&["or fewer significant digits"]] },
    Prim { name: "ReplaceDigitsAfter", sig: "(n: mathematical value, k: integer, up: Boolean) → mathematical value", meaning: "n with each significant decimal digit after the kth replaced by 0, and with up then incremented at the kth with carry", group: NUM, marks: &[&["replacing each significant digit"]] },
    // grammar, Parse Nodes
    Prim { name: "ParseTree", sig: "(text: source text, goal: nonterminal) → Parse Node", meaning: "the root Parse Node of a successful parse of text with goal and no early errors", group: GRAM, marks: &[&["If the parse succeeded and no early errors were found"]] },
    Prim { name: "IsStrictModeCode", sig: "(text: source text) → Boolean", meaning: "whether text is strict mode code (11.2.2)", group: GRAM, marks: &[&["is strict mode code"]] },
    Prim { name: "InParseJSONScript", sig: "(n: Parse Node) → Boolean", meaning: "whether n lies in a Script that ParseJSON is evaluating", group: GRAM, marks: &[&["being evaluated for ParseJSON"]] },
    Prim { name: "NearestEnclosing", sig: "(n: Parse Node, ss: List of nonterminal) → Parse Node or empty", meaning: "the nearest Parse Node containing n that is an instance of one of ss, if any", group: GRAM, marks: &[&["most closely contains"], &["is not contained within a |"]] },
    Prim { name: "ContainedInstances", sig: "(n: Parse Node, s: nonterminal) → List of Parse Node", meaning: "the instances of s that n contains, in source text order", group: GRAM, marks: &[&["For each |", "_ contains, do"]] },
    Prim { name: "RightHandSideCharacters", sig: "(ss: List of nonterminal) → CharSet", meaning: "the characters whose code points appear on the right-hand side of the productions of ss", group: GRAM, marks: &[&["on the right-hand side of the"]] },
    Prim { name: "CaptureGroupName", sig: "(r: Parse Node, i: integer) → Parse Node or empty", meaning: "the GroupName of the ith capturing group of the pattern r, if it has one", group: GRAM, marks: &[&["capture of _regexp_ was defined with"], &["CapturingGroupName of that"]] },
    Prim { name: "Parent", sig: "(n: Parse Node) → Parse Node", meaning: "the Parse Node of which n is a child node", group: GRAM, marks: &[&["the parent of"]] },
    Prim { name: "CurrentProduction", sig: "() → Parse Node", meaning: "the Parse Node whose evaluation is running", group: GRAM, marks: &[&["the syntactic production that is being evaluated"]] },
    // RegExp CharSets, characters
    Prim { name: "SoleElement", sig: "(c: List or CharSet) → value", meaning: "the one element of a one-element List or CharSet", group: CHARS, marks: &[&["that is the single CharSetElement of"], &["the single code point element of"]] },
    Prim { name: "PropertyCharSet", sig: "(p: Unicode property name, v: Unicode property value) → CharSet", meaning: "the CharSet of the characters whose Unicode Character Database property p has the value v", group: CHARS, marks: &[&["character database definition includes the property"]] },
    Prim { name: "DecimalDigitCharSet", sig: "() → CharSet", meaning: "the CharSet of the ten characters 0 through 9", group: CHARS, marks: &[&["ten-element CharSet"]] },
    Prim { name: "CharacterInterval", sig: "(i: integer, j: integer) → CharSet", meaning: "the CharSet of the characters whose character values lie in the inclusive interval from i to j", group: CHARS, marks: &[&["all characters with a character value in the inclusive interval"]] },
    Prim { name: "CharSetOf", sig: "(s: sequence of characters) → CharSet", meaning: "the CharSet of the characters of s", group: CHARS, marks: &[&["containing every character in"]] },
    Prim { name: "CaseFoldingFixedPoints", sig: "() → CharSet", meaning: "the CharSet of the code points c with scf(c) = c", group: CHARS, marks: &[&["Simple Case Folding"]] },
    Prim { name: "IthElement", sig: "(l: List, i: integer) → value", meaning: "the ith element of l, counting from 1", group: TAB, marks: &[&["<sup>th</sup> element of"]] },
    Prim { name: "InputIndexOf", sig: "(input: List of character, s: String, k: integer) → integer", meaning: "the index in input of the character decoded from the code unit of s at index k", group: CHARS, marks: &[&["the index into"]] },
    Prim { name: "IsSingleCharacter", sig: "(cs: CharSet) → Boolean", meaning: "whether cs has exactly one element and it is a single character", group: CHARS, marks: &[&["does not contain exactly one character"]] },
    // execution contexts, agents
    Prim { name: "DiscardContextResources", sig: "(c: execution context) → unused", meaning: "release the resources of c; no observable effect", group: CTX, marks: &[&["Discard all resources associated with"]] },
    Prim { name: "WakeAgent", sig: "(s: agent signifier) → unused", meaning: "resume the agent s from suspension", group: CTX, marks: &[&["Wake the agent whose signifier is"]] },
    Prim { name: "AcquireCriticalSection", sig: "(wl: WaiterList Record) → unused", meaning: "block until no agent is in wl's critical section, then enter it", group: CTX, marks: &[&["then enter the critical section for"]] },
    Prim { name: "ReleaseCriticalSection", sig: "(wl: WaiterList Record) → unused", meaning: "leave wl's critical section", group: CTX, marks: &[&["Leave the critical section for"]] },
    Prim { name: "ContextBelowTop", sig: "() → execution context or empty", meaning: "the execution context directly below the top of the execution context stack, if any", group: CTX, marks: &[&["the second to top element of the execution context stack"]] },
    Prim { name: "TopmostScriptOrModuleContext", sig: "() → execution context or empty", meaning: "the topmost execution context whose ScriptOrModule component is not null, if any", group: CTX, marks: &[&["whose ScriptOrModule component is not"], &["If no such execution context exists"]] },
    // lists, tables
    Prim { name: "PassedArguments", sig: "() → List of ECMAScript language values", meaning: "the arguments that the running built-in function was called with", group: TAB, marks: &[&["the List of arguments that was passed to this function"], &["If only one argument was passed"]] },
    Prim { name: "TableLookup", sig: "(t: table, valueColumn: String, keyColumn: String, key: value) → value", meaning: "the entry in valueColumn of the row of table t whose keyColumn entry is key", group: TAB, marks: &[&["value according to <emu-xref href=\"#table-"], &["named in the “"], &["corresponds to in <emu-xref"], &["column of the corresponding row"], &["column of the row whose"], &["Constructor Name value specified in"]] },
    Prim { name: "TableColumnHas", sig: "(t: table, column: String, v: value) → Boolean", meaning: "whether v appears in column of table t", group: TAB, marks: &[&["listed in the “"]] },
    Prim { name: "OneIndexedList", sig: "(n: integer, v: value) → List", meaning: "a List of n copies of v, indexed from 1", group: TAB, marks: &[&["indexed 1 through"]] },
    Prim { name: "WaiterListFor", sig: "(b: Shared Data Block, i: integer) → WaiterList Record", meaning: "the WaiterList Record of byte position i of b", group: TAB, marks: &[&["WaiterList Record that is referenced by the pair"]] },
    Prim { name: "ChildNodes", sig: "(n: Parse Node) → List of Parse Node", meaning: "the child nodes of n, in order", group: TAB, marks: &[&["each child node of"]] },
    Prim { name: "Pair", sig: "(a: value, b: value) → pair", meaning: "the ordered pair of a and b", group: TAB, marks: &[&["Append (_"]] },
    // memory model, data blocks, bytes
    Prim { name: "CanAllocate", sig: "(n: integer, shared: Boolean) → Boolean", meaning: "whether a Data Block (shared: a Shared Data Block) of n bytes can be created", group: MEM, marks: &[&["possible to create a Data Block"], &["impossible to create a new Shared Data Block"]] },
    Prim { name: "BlockBytes", sig: "(b: Data Block, i: integer, j: integer) → List of byte", meaning: "the bytes of b at the indices from i to j, j excluded", group: MEM, marks: &[&["elements are bytes from"]] },
    Prim { name: "SetDifference", sig: "(a: Set, b: Set) → Set", meaning: "the elements of a that are not elements of b", group: MEM, marks: &[&["that are not in"]] },
    Prim { name: "RangesOverlap", sig: "(e: Shared Data Block event, f: Shared Data Block event) → Boolean", meaning: "whether the memory ranges of e and f intersect", group: MEM, marks: &[&["disjoint memory ranges"], &["overlapping memory ranges"]] },
    Prim { name: "InRace", sig: "(e: Shared Data Block event, f: Shared Data Block event, x: candidate execution) → Boolean", meaning: "whether e and f are in a race in x (29.9)", group: MEM, marks: &[&["race</emu-xref> in"]] },
    Prim { name: "ZeroFill", sig: "(b: Data Block) → unused", meaning: "set every byte of b to 0", group: MEM, marks: &[&["Set all of the bytes of"]] },
    // objects, properties, slots
    Prim { name: "RemoveOwnProperty", sig: "(o: Object, p: property key) → unused", meaning: "delete o's own property whose key is p", group: OBJ, marks: &[&["Remove the own property with name"]] },
    Prim { name: "RealmIntrinsic", sig: "(r: Realm Record, n: String) → Object", meaning: "the intrinsic object that r records under the name n", group: OBJ, marks: &[&["intrinsic object named"]] },
    Prim { name: "IsOrdinaryInternalMethod", sig: "(m: internal method, n: internal method name) → Boolean", meaning: "whether m is the ordinary object internal method named n", group: OBJ, marks: &[&["is not the ordinary object internal method"]] },
    Prim { name: "OwnProperty", sig: "(o: Object, p: property key) → property or empty", meaning: "o's own property whose key is p, if any", group: OBJ, marks: &[&["own property whose key is"]] },
    Prim { name: "CreateOwnProperty", sig: "(o: Object, p: property key, k: data or accessor, d: Property Descriptor) → unused", meaning: "add to o a property p of kind k whose attributes are d's fields, or their defaults where d has none", group: OBJ, marks: &[&["Create an own "]] },
    Prim { name: "ConvertProperty", sig: "(o: Object, p: property key, k: data or accessor, c: Boolean, e: Boolean, d: Property Descriptor) → unused", meaning: "replace o's property p by one of kind k with [[Configurable]] c, [[Enumerable]] e, and its other attributes from d or their defaults", group: OBJ, marks: &[&["Replace the property named"]] },
    Prim { name: "SetPropertyAttribute", sig: "(o: Object, p: property key, f: attribute name, v: value) → unused", meaning: "set the attribute f of o's property p to v", group: OBJ, marks: &[&["set the attribute named"]] },
    Prim { name: "BuiltinFunctionSlots", sig: "() → List of internal slot names", meaning: "the internal slots that 10.3 requires of a built-in function object", group: OBJ, marks: &[&["requires for the built-in function object"]] },
    Prim { name: "ClauseProperties", sig: "(o: Object, c: clause) → List of property", meaning: "the own properties that clause c specifies for o", group: OBJ, marks: &[&["Create own properties of"], &["For each property of the Global Object specified in clause"]] },
    Prim { name: "SpecifiedPropertyName", sig: "(p: property) → String", meaning: "the name of a property that a clause specifies", group: OBJ, marks: &[&["String value of the property name"]] },
    Prim { name: "MakeObject", sig: "(slots: List of internal slot names) → Object", meaning: "a new object with exactly the internal slots named in slots", group: OBJ, marks: &[&["newly created object with an internal slot for each name"]] },
    // Number rounding
    Prim { name: "NumberCeil", sig: "(n: Number) → Number", meaning: "the smallest integral Number not less than n", group: MATH, marks: &[&["integral Number value that is not less than"]] },
    Prim { name: "NumberFloor", sig: "(n: Number) → Number", meaning: "the greatest integral Number not greater than n", group: MATH, marks: &[&["integral Number value that is not greater than"]] },
    Prim { name: "NumberRound", sig: "(n: Number) → Number", meaning: "the integral Number closest to n, a tie going toward +∞", group: MATH, marks: &[&["integral Number closest to"]] },
    Prim { name: "NumberTrunc", sig: "(n: Number) → Number", meaning: "the integral Number nearest n in the direction of +0", group: MATH, marks: &[&["in the direction of *+0*"]] },
    // time zones, dates
    Prim { name: "IsNonPrimaryTimeZoneId", sig: "(id: String) → Boolean", meaning: "whether id is a non-primary time zone identifier in this implementation", group: TZ, marks: &[&["is a non-primary time zone identifier in this implementation"]] },
    Prim { name: "HasTimeZoneRules", sig: "() → Boolean", meaning: "whether the implementation includes local political rules for any time zone", group: TZ, marks: &[&["local political rules"]] },
    Prim { name: "PrimaryTimeZoneId", sig: "(id: String) → String", meaning: "the primary time zone identifier of the time zone id names", group: TZ, marks: &[&["the primary time zone identifier associated with"]] },
    Prim { name: "SupportsOnlyUTC", sig: "() → Boolean", meaning: "whether the implementation supports only the UTC time zone", group: TZ, marks: &[&["only supports the UTC time zone"]] },
    Prim { name: "LastTransitionBefore", sig: "(id: String, t: Number) → integral Number or empty", meaning: "the largest integral Number less than t that is a local time of time zone id, the last local time before the transition at t", group: TZ, marks: &[&["is the largest integral Number"]] },
    Prim { name: "AvailableNamedTimeZoneIds", sig: "() → List of String", meaning: "the available named time zone identifiers, without duplicates, in code unit order", group: TZ, marks: &[&["available named time zone identifiers"]] },
    Prim { name: "ParseDateString", sig: "(s: String) → Number", meaning: "the time value that Date.parse gives for s", group: TZ, marks: &[&["parsing _primitive_ as a date"]] },
    Prim { name: "IsDateTimeRepresentable", sig: "(tv: Number) → Boolean", meaning: "whether the year of tv can be written in the Date Time String Format", group: TZ, marks: &[&["corresponds with a year that cannot be represented"]] },
    Prim { name: "DateTimeString", sig: "(tv: Number) → String", meaning: "tv in the Date Time String Format on the UTC time scale, with every element and the offset \"Z\"", group: TZ, marks: &[&["Return a String representation of _tv_ in the"]] },
    // implementation and host facts
    Prim { name: "SpinWaitHint", sig: "() → unused", meaning: "signal a spin-wait loop to the operating system or CPU where supported; no observable effect", group: IMPL, marks: &[&["spin-wait loop"]] },
    Prim { name: "IsJSONText", sig: "(cps: List of code point) → Boolean", meaning: "whether cps is a valid JSON text (ECMA-404)", group: IMPL, marks: &[&["valid JSON text"]] },
    Prim { name: "SomeIndex", sig: "(lo: integer, hi: integer, p: integer → Boolean) → Boolean", meaning: "whether p holds for some integer from lo to hi, hi excluded", group: IMPL, marks: &[&["for some integer"]] },
    // code units, code points, strings
    Prim { name: "UTF8Encode", sig: "(cp: code point) → List of byte", meaning: "the octets of the UTF-8 encoding of cp", group: STR, marks: &[&["octets resulting by applying the UTF-8 transformation"]] },
    Prim { name: "UTF8Decode", sig: "(os: List of byte) → code point", meaning: "the code point that the UTF-8 octets os encode", group: STR, marks: &[&["code point obtained by applying the UTF-8 transformation"]] },
    Prim { name: "IsUTF8", sig: "(os: List of byte) → Boolean", meaning: "whether os is a valid UTF-8 encoding of a code point", group: STR, marks: &[&["does not contain a valid UTF-8 encoding"]] },
    Prim { name: "UnicodeNormalize", sig: "(s: String, form: String) → String", meaning: "s normalized into the Unicode normalization form named form", group: STR, marks: &[&["into the normalization form"]] },
    Prim { name: "RepeatToLength", sig: "(s: String, n: integer) → String", meaning: "s repeated and truncated to length n", group: STR, marks: &[&["repeated concatenations of"]] },
    Prim { name: "RepeatString", sig: "(s: String, n: integer) → String", meaning: "n copies of s concatenated", group: STR, marks: &[&["copies of _string_ appended together"]] },
    Prim { name: "toLowercase", sig: "(cps: List of code point) → List of code point", meaning: "the lowercase mapping of the Unicode Default Case Conversion algorithm", group: STR, marks: &[&["toLowercase(", "Unicode Default Case Conversion"]] },
    Prim { name: "toUppercase", sig: "(cps: List of code point) → List of code point", meaning: "the uppercase mapping of the Unicode Default Case Conversion algorithm", group: STR, marks: &[&["toUppercase(", "Unicode Default Case Conversion"]] },
    Prim { name: "SimpleCaseFold", sig: "(c: character) → character or empty", meaning: "the simple or common case folding of c in CaseFolding.txt, if any", group: STR, marks: &[&["CaseFolding.txt"]] },
    Prim { name: "IsPropertyValueAlias", sig: "(p: Unicode property name, v: String) → Boolean", meaning: "whether v is a value or value alias of the Unicode property p in PropertyValueAliases.txt", group: STR, marks: &[&["PropertyValueAliases.txt"]] },
    Prim { name: "InBase64Alphabet", sig: "(c: code unit) → Boolean", meaning: "whether c is in the standard base64 alphabet", group: STR, marks: &[&["standard base64 alphabet"]] },
    Prim { name: "SameCodeUnits", sig: "(x: String, y: String) → Boolean", meaning: "whether x and y have the same length and the same code units at each index", group: STR, marks: &[&["the same code units in the same positions"]] },
    Prim { name: "ReplaceCodeUnit", sig: "(s: String, c: code unit, r: String) → String", meaning: "s with each occurrence of c replaced by r", group: STR, marks: &[&["except that each occurrence of"]] },
];

/// What claims a residual step: its channel, its kind, and its primitive or reason.
pub struct Claim {
    pub channel: Channel,
    pub kind: &'static str,
    pub prim: Option<&'static Prim>,
    pub reason: Option<&'static str>,
}

/// Whether a step has a second sentence: `. ` then a capital, outside a value literal.
fn multi_sentence(t: &str) -> bool {
    let b: Vec<char> = t.chars().collect();
    let mut in_val = false;
    for i in 0..b.len() {
        if b[i] == '*' {
            in_val = !in_val;
        }
        if !in_val && i + 2 < b.len() && b[i] == '.' && b[i + 1] == ' ' && b[i + 2].is_ascii_uppercase() && i > 0 {
            let p = b[i - 1];
            if p.is_ascii_lowercase() || p == ')' || p == '_' || p == '*' {
                return true;
            }
        }
    }
    false
}

fn marked(text: &str, marks: &[&str]) -> bool {
    marks.iter().all(|w| text.contains(w))
}

/// The primitive a step names, if any.
pub fn prim(text: &str) -> Option<&'static Prim> {
    PRIMS.iter().find(|p| p.marks.iter().any(|m| marked(text, m)))
}

/// The claim on a residual step.
pub fn kind(text: &str) -> Claim {
    for k in KINDS {
        let claim = |prim, reason| Claim { channel: k.channel, kind: k.name, prim, reason };
        match k.name {
            "prose Assert" if text.starts_with("Assert:") => return claim(None, None),
            "spec-issue candidate" => {
                if let Some(r) = REGS.iter().find(|r| marked(text, r.marks)) {
                    return claim(if FIRST_MEANS.contains(&r.reason) { prim(text) } else { None }, Some(r.reason));
                }
                if multi_sentence(text) {
                    return claim(None, Some(MULTI_REASON));
                }
            }
            "environment-record bindings (prose methods)" if k.words.iter().any(|w| text.contains(w)) => return claim(None, Some(ENV_REASON)),
            "declared primitive" => return claim(prim(text), None),
            "prose Assert" | "environment-record bindings (prose methods)" => {}
            _ if k.words.iter().any(|w| text.contains(w)) => return claim(if k.channel == Channel::Annotated { prim(text) } else { None }, None),
            _ => {}
        }
    }
    unreachable!()
}

/// Where a prose fragment stands: a whole step, a value, or a condition.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Pos {
    Stmt,
    Expr,
    Cond,
}

/// A signature's parameter sorts and result: `(a: A, b: B) → R` or `Name(_a_: A, _b_: B): R`.
pub fn sig_parts(sig: &str) -> Option<(Vec<String>, String)> {
    let open = sig.find('(')?;
    let (mut depth, mut params, mut cur) = (0usize, Vec::new(), String::new());
    for (i, c) in sig[open + 1..].char_indices() {
        match c {
            '(' | '«' | '[' => depth += 1,
            ')' if depth == 0 => {
                if !cur.trim().is_empty() {
                    params.push(cur.trim().to_string());
                }
                let rest = sig[open + 1 + i + 1..].trim_start();
                let res = rest.strip_prefix('→').or_else(|| rest.strip_prefix(':'))?.trim().to_string();
                let sort = |p: &String| p.split_once(':').map_or(p.as_str(), |x| x.1).trim().to_string();
                return Some((params.iter().map(sort).collect(), res));
            }
            ')' | '»' | ']' => depth -= 1,
            ',' if depth == 0 => {
                params.push(std::mem::take(&mut cur));
                continue;
            }
            _ => {}
        }
        cur.push(c);
    }
    None
}

/// The words that change what a primitive is applied to or what it means when they stay in the prose.
const OPERAND_WORDS: &[&str] = &["or", "and", "nor", "plus", "minus", "times", "first", "last", "next", "previous", "after", "before", "then"];

/// The negation words.
const NEGATIONS: &[&str] = &["not", "no", "neither", "nor", "never", "none", "cannot"];

fn has_word(text: &str, w: &str) -> bool {
    text.split(|c: char| !c.is_alphanumeric() && c != '-').any(|x| x == w)
}

/// Why a prose fragment's primitive is not applied to its holes, if it is not: as
/// many variables as parameters, at most one (an order needs an overlay phrase); no
/// literal, number, list, field, operand word or continuation left in the words;
/// the step's polarity the phrase meaning's; a result of the sort the position needs. `nested`: the
/// step has nested steps.
pub fn unwired(name: &str, parts: &[crate::ast::Part], nested: bool, pos: Pos) -> Option<String> {
    use crate::ast::{Expr, Hole, Part};
    let Some(p) = PRIMS.iter().find(|p| p.name == name) else { return Some("no declared signature".into()) };
    let Some((params, res)) = sig_parts(p.sig) else { return Some(format!("signature {} does not parse", p.sig)) };
    let (mut vars, mut text) = (Vec::new(), String::new());
    for x in parts {
        match x {
            Part::Text(t) => text.push_str(t),
            Part::Hole(Hole::E(Expr::Var(v))) => {
                if vars.contains(v) {
                    return Some("a variable passed twice".into());
                }
                vars.push(*v);
                text.push_str(" _ ");
            }
            Part::Hole(_) => return Some("continuation lines or nested steps outside the arguments".into()),
        }
    }
    if nested {
        return Some("continuation lines or nested steps outside the arguments".into());
    }
    if vars.len() != params.len() {
        return Some(format!("{} variable{} for {} parameter{}", vars.len(), if vars.len() == 1 { "" } else { "s" }, params.len(), if params.len() == 1 { "" } else { "s" }));
    }
    if vars.len() > 1 {
        return Some("two or more arguments: their order needs an overlay phrase".into());
    }
    let neg = |t: &str| NEGATIONS.iter().any(|w| has_word(t, w));
    if neg(&text) != neg(p.meaning) {
        return Some(if neg(&text) { "the step negates the phrase's meaning".into() } else { "the phrase's meaning negates the step".into() });
    }
    let mut rest = text.clone();
    if let Some(m) = p.marks.iter().find(|m| marked(&text, m)) {
        for w in m.iter() {
            rest = rest.replacen(w, " ", 1);
        }
    }
    if rest.contains(|c: char| c.is_ascii_digit()) {
        return Some("a number in the words".into());
    }
    if rest.contains('|') {
        return Some("a nonterminal in the words".into());
    }
    if let Some(c) = ['*', '«', '[', '%', '~'].iter().find(|c| rest.contains(**c)) {
        return Some(format!("'{c}' (a literal, list, field or intrinsic) in the words"));
    }
    if let Some(w) = OPERAND_WORDS.iter().find(|w| has_word(&rest, w)) {
        return Some(format!("'{w}' in the words"));
    }
    let boolean = res.contains("Boolean");
    match pos {
        Pos::Cond if !boolean => Some(format!("a condition, but the result is {res}")),
        Pos::Stmt if res != "unused" => Some(format!("a step, but the result is {res}")),
        Pos::Expr if res == "unused" => Some("a value, but the result is unused".into()),
        _ => None,
    }
}

/// What a declared primitive needs before it can leave the residue, by name.
const NEEDS: &[(&str, &[&str])] = &[
    ("expressible in the overlay (an algorithm or phrase)", &[
        "SoleElement", "DecimalDigitCharSet", "CharacterInterval", "CharSetOf", "InputIndexOf", "SomeIndex", "OneIndexedList", "Pair",
        "InRace", "RangesOverlap", "IndexOfFirstNonDigit", "IsDateTimeRepresentable", "DateTimeString",
    ]),
    ("grammar and Parse Nodes", &[
        "ParseTree", "InParseJSONScript", "NearestEnclosing", "ContainedInstances", "RightHandSideCharacters", "CaptureGroupName", "Parent",
        "CurrentProduction", "ChildNodes", "IsJSONText", "IsStrictModeCode",
    ]),
    ("tables (table data)", &["TableLookup", "TableColumnHas"]),
    ("Unicode data", &["PropertyCharSet", "CaseFoldingFixedPoints", "UnicodeNormalize", "toLowercase", "toUppercase", "SimpleCaseFold", "IsPropertyValueAlias", "CanonicalPropertyValue"]),
    ("host facts (Host.WF)", &[
        "CanAllocate", "IsNonPrimaryTimeZoneId", "HasTimeZoneRules", "PrimaryTimeZoneId", "SupportsOnlyUTC",
        "LastTransitionBefore", "AvailableNamedTimeZoneIds", "ParseDateString", "SpinWaitHint",
    ]),
    ("agents and the memory model", &["DiscardContextResources", "WakeAgent", "AcquireCriticalSection", "ReleaseCriticalSection", "WaiterListFor", "ZeroFill"]),
    ("execution contexts and objects (Model)", &[
        "ContextBelowTop", "TopmostScriptOrModuleContext", "PassedArguments", "RealmIntrinsic", "BuiltinFunctionSlots", "SpecifiedPropertyName", "MakeObject",
        "ClauseProperties",
    ]),
];

/// The need of the declared primitive `name`, or "unclassified".
pub fn need(name: &str) -> &'static str {
    NEEDS.iter().find(|(_, ps)| ps.contains(&name)).map_or("unclassified", |(n, _)| n)
}

/// For each residue step (its key, `sec-x#n` or an overlay id, and its path), the permanent
/// entry claiming it; an error per entry that claims no residue step, or a step another claims.
pub fn claim(steps: &[(String, String)], perms: &[crate::overlay::Permanent]) -> (Vec<Option<usize>>, Vec<String>) {
    let mut by: Vec<Option<usize>> = vec![None; steps.len()];
    let mut errs = Vec::new();
    for (i, p) in perms.iter().enumerate() {
        let mut hit = false;
        for (j, (key, path)) in steps.iter().enumerate() {
            if *path != p.step || !(*key == p.clause || key.split_once('#').is_some_and(|(c, _)| c == p.clause)) {
                continue;
            }
            hit = true;
            if let Some(k) = by[j] {
                errs.push(format!("{}: emu-permanent {} {} claims the step that {} {} claims", p.file, p.clause, p.step, perms[k].clause, perms[k].step));
            } else {
                by[j] = Some(i);
            }
        }
        if !hit {
            errs.push(format!("{}: emu-permanent {} {}: no residue step there (stale: it has a meaning, or no such step)", p.file, p.clause, p.step));
        }
    }
    (by, errs)
}
