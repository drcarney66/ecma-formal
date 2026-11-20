// The demo's scripts (docs/debugger/DEMO.md): per program of this directory, its title,
// the breakpoints, filters and line breakpoints set before its start, its stops in order and
// its outcome.
// A stop is reached by `do` (the first by the start) and names what it shows:
//   reason, alg, path   the stop (the status bar's "paused (reason) at alg path")
//   text                the step's text begins so (the step pane)
//   line, node          the JS position: the source's current line and its underlined node
//   frames              the spec stack's innermost frames, "Name path" each
//   js                  the JS stack's frames' names, the running one first
//   slots               frame 0's Slots by name: their values
//   cell                {slot: {part: value}}: the slot's heap cell, expanded
//   say                 what to say there
// Every stop's step is also the current step of its algorithm's listing. A value's "#*"
// matches any address.
// `do` is continue, next, in or out (spec steps), jsNext, jsIn or jsOut (statements).
// tools/dbg/demo/demo_test.mjs walks them on the model in node, tools/dbg/ui/demotest.mjs
// through the page.

export const DEMOS = [
  {
    program: "get.js",
    title: "A property get: [[Get]] and OrdinaryGet up the prototype chain",
    breakpoints: [{ alg: "sec-ordinaryget", path: "1" }],
    stops: [
      {
        do: "start",
        reason: "breakpoint",
        alg: "OrdinaryGet",
        path: "1",
        text: "Let propertyDesc be ? obj.[[GetOwnProperty]](propertyKey).",
        line: 3,
        node: "a = point.x",
        frames: ["OrdinaryGet 1", "[[Get]] 1", "GetValue 3.d"],
        js: ["(script)", "(host)"],
        slots: { propertyKey: '"x"', obj: "#*", receiver: "#*", propertyDesc: "unbound" },
        cell: { obj: { x: "3" } },
        say: "`point.x` is a Reference; GetValue 3.d calls point's [[Get]], an ordinary object's, which is OrdinaryGet. obj and receiver are both point: its cell has x: 3.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2",
        text: "If propertyDesc is undefined, then",
        slots: { propertyDesc: "#*" },
        cell: { propertyDesc: { sort: "Property Descriptor", "[[Value]]": "3", "[[Writable]]": "true" } },
        say: "[[GetOwnProperty]] found x: propertyDesc is a Property Descriptor record in the heap, [[Value]] 3. Step 2 is skipped.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "3",
        text: "If IsDataDescriptor(propertyDesc) is true, return propertyDesc.[[Value]].",
        say: "A data descriptor: OrdinaryGet returns its [[Value]], 3.",
      },
      {
        do: "continue",
        reason: "breakpoint",
        alg: "OrdinaryGet",
        path: "1",
        line: 4,
        node: "b = point.z",
        frames: ["OrdinaryGet 1", "[[Get]] 1", "GetValue 3.d"],
        slots: { propertyKey: '"z"' },
        say: "Continue: the same breakpoint, now for `point.z`. point has no own z.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2",
        slots: { propertyDesc: "undefined" },
        say: "This time [[GetOwnProperty]] returned undefined, so step 2 goes to the prototype.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2.a",
        text: "Let parent be ? obj.[[GetPrototypeOf]]().",
        slots: { parent: "unbound" },
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2.b",
        text: "If parent is null, return undefined.",
        slots: { parent: "#*" },
        cell: { parent: { z: "5" } },
        say: "parent is point's [[Prototype]], proto: its cell has z: 5.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2.c",
        text: "Return ? parent.[[Get]](propertyKey, receiver).",
        say: "The lookup recurses: parent's [[Get]], with the same receiver, point.",
      },
      {
        do: "in",
        reason: "step",
        alg: "[[Get]]",
        path: "1",
        text: "Return ? OrdinaryGet(obj, propertyKey, receiver).",
        frames: ["[[Get]] 1", "OrdinaryGet 2.c", "[[Get]] 1", "GetValue 3.d"],
        slots: { propertyKey: '"z"' },
        cell: { obj: { z: "5" }, receiver: { x: "3" } },
        say: "Step in: proto's [[Get]]. obj is now proto; receiver is still point.",
      },
      {
        do: "in",
        reason: "breakpoint",
        alg: "OrdinaryGet",
        path: "1",
        frames: ["OrdinaryGet 1", "[[Get]] 1", "OrdinaryGet 2.c", "[[Get]] 1"],
        say: "OrdinaryGet again, one level deeper: the spec stack shows the recursion. The JS stack is unchanged: no function was called.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "2",
        cell: { propertyDesc: { sort: "Property Descriptor", "[[Value]]": "5" } },
        say: "proto's own z: [[Value]] 5.",
      },
      {
        do: "next",
        reason: "step",
        alg: "OrdinaryGet",
        path: "3",
        say: "5 is returned through both OrdinaryGets. Continue ends the script: a + b is 8.",
      },
    ],
    end: "normal: 8",
  },
  {
    program: "call.js",
    title: "A call: EvaluateCall, Call, [[Call]] and OrdinaryCallEvaluateBody",
    breakpoints: [{ alg: "sec-evaluatecall", path: "7" }, { alg: "sec-ordinarycallevaluatebody", path: "1" }],
    stops: [
      {
        do: "start",
        reason: "breakpoint",
        alg: "EvaluateCall",
        path: "7",
        text: "Return ? Call(func, thisValue, argList).",
        line: 5,
        node: "add(2, 3)",
        frames: ["EvaluateCall 7"],
        js: ["(script)", "(host)"],
        slots: { func: "#*", thisValue: "undefined", argList: "#*" },
        cell: { func: { name: '"add"', length: "2" }, argList: { "[0]": "2", "[1]": "3" } },
        say: "EvaluateCall has evaluated `add` and the arguments: func is the function object (its cell: name \"add\", length 2), argList the List [2, 3], thisValue undefined.",
      },
      {
        do: "in",
        reason: "step",
        alg: "Call",
        path: "1",
        text: "If argList is not present, set argList to a new empty List.",
        frames: ["Call 1", "EvaluateCall 7"],
        say: "Step in: the abstract operation Call.",
      },
      {
        do: "next",
        reason: "step",
        alg: "Call",
        path: "2",
        text: "If IsCallable(func) is false, throw a TypeError exception.",
      },
      {
        do: "next",
        reason: "step",
        alg: "Call",
        path: "3",
        text: "Return ? func.[[Call]](thisValue, argList).",
        say: "Call dispatches to the object's own [[Call]] internal method.",
      },
      {
        do: "in",
        reason: "step",
        alg: "[[Call]]",
        path: "1",
        text: "Let callerContext be the running execution context.",
        frames: ["[[Call]] 1", "Call 3", "EvaluateCall 7"],
        js: ["(script)", "(host)"],
        slots: { thisArg: "undefined", callerContext: "unbound", result: "unbound" },
        say: "An ECMAScript function object's [[Call]]: step 2 will push a new execution context.",
      },
      {
        do: "continue",
        reason: "breakpoint",
        alg: "OrdinaryCallEvaluateBody",
        path: "1",
        text: "Return ? EvaluateBody of func.[[ECMAScriptCode]]",
        frames: ["OrdinaryCallEvaluateBody 1", "[[Call]] 6"],
        js: ["add", "(script)", "(host)"],
        say: "Continue to OrdinaryCallEvaluateBody, from [[Call]] 6: the JS stack now has add's execution context on top.",
      },
      {
        do: "jsIn",
        reason: "step",
        line: 2,
        node: "var s = a + b;",
        js: ["add", "(script)", "(host)"],
        say: "Step in by statement (F11): add's first statement.",
      },
      {
        do: "jsNext",
        reason: "step",
        line: 3,
        node: "return s;",
      },
      {
        do: "jsOut",
        reason: "step",
        alg: "[[Call]]",
        path: "8",
        text: "If result is a throw completion, return ? result.",
        line: 5,
        node: "add(2, 3)",
        js: ["(script)", "(host)"],
        slots: { result: "Completion { type: ~return~, value: 5, target: ~empty~ }", callerContext: "#*", calleeContext: "#*" },
        say: "Step out by statement: back in [[Call]] after step 7 popped add's context. result is a return completion with value 5; step 10 returns its [[Value]].",
      },
    ],
    end: "normal: 5",
  },
  {
    program: "forof.js",
    title: "A for-of loop: the iterator protocol in ForIn/OfBodyEvaluation",
    breakpoints: [{ alg: "ForIn/OfBodyEvaluation", path: "8.a" }],
    stops: [
      {
        do: "start",
        reason: "breakpoint",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.a",
        text: "Let nextResult be ? Call(iteratorRecord.[[NextMethod]], iteratorRecord.[[Iterator]]).",
        line: 2,
        node: "for (const v of [10, 20]) {\n  sum = sum + v;\n}",
        frames: ["ForIn/OfBodyEvaluation 8.a", "ForInOfLoopEvaluation 2"],
        js: ["(script)", "(host)"],
        slots: { iterationKind: "~iterate~", lhsKind: "~lexical-binding~", iteratorKind: "~sync~", nextResult: "unbound" },
        cell: { iteratorRecord: { sort: "Iterator Record", "[[Iterator]]": "#*", "[[NextMethod]]": "#*", "[[Done]]": "false" } },
        say: "The Repeat step of the loop. iteratorRecord is an Iterator Record: the array iterator, its next method, [[Done]] false.",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.b",
        text: "If iteratorKind is async",
        slots: { nextResult: "#*" },
        cell: { nextResult: { value: "10", done: "false" } },
        say: "next() returned an iterator result object: value 10, done false.",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.c",
        text: "If nextResult is not an Object, throw a TypeError exception.",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.d",
        text: "Let done be ? IteratorComplete(nextResult).",
      },
      {
        do: "in",
        reason: "step",
        alg: "IteratorComplete",
        path: "1",
        text: 'Return ToBoolean(? Get(iteratorResult, "done")).',
        frames: ["IteratorComplete 1", "ForIn/OfBodyEvaluation 8.d"],
        slots: { iteratorResult: "#*" },
        say: "IteratorComplete reads the result's done property, through [[Get]].",
      },
      {
        do: "out",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.e",
        text: "If done is true, return iterationResult.",
        slots: { done: "false" },
        say: "Step out: done is false, so the loop goes on.",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.f",
        text: "Let nextValue be ? IteratorValue(nextResult).",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.g",
        text: "If lhsKind is either assignment or var-binding, then",
        slots: { nextValue: "10" },
        say: "nextValue is 10; v is bound to it in a new declarative environment.",
      },
      {
        do: "jsNext",
        reason: "step",
        line: 3,
        node: "sum = sum + v;",
        frames: ["Evaluation 1", "Evaluation 5", "ForIn/OfBodyEvaluation 8.j"],
        say: "Step by statement: the loop body, evaluated from 8.j.",
      },
      {
        do: "continue",
        reason: "breakpoint",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.a",
        slots: { iterationResult: "10" },
        say: "Continue: the second iteration. iterationResult is the body's value so far, 10.",
      },
      {
        do: "continue",
        reason: "breakpoint",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.a",
        slots: { iterationResult: "30" },
        cell: { nextResult: { value: "20", done: "false" } },
        say: "The third call of next(): nextResult is still the second result, value 20.",
      },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.b",
        cell: { nextResult: { value: "undefined", done: "true" } },
        say: "The iterator is exhausted: value undefined, done true.",
      },
      { do: "next", reason: "step", alg: "ForIn/OfBodyEvaluation", path: "8.c" },
      { do: "next", reason: "step", alg: "ForIn/OfBodyEvaluation", path: "8.d" },
      {
        do: "next",
        reason: "step",
        alg: "ForIn/OfBodyEvaluation",
        path: "8.e",
        slots: { done: "true", iterationResult: "30" },
        say: "done is true: the loop returns iterationResult, 30.",
      },
      {
        do: "next",
        reason: "step",
        alg: "Completion",
        path: "1",
        text: "Assert: completionRecord is a Completion Record.",
        frames: ["Completion 1", "LabelledEvaluation 1"],
        slots: { completionRecord: "Completion { type: ~normal~, value: 30, target: ~empty~ }" },
        say: "The loop's result as a completion record: normal, 30. Continue ends the script with sum, 30.",
      },
    ],
    end: "normal: 30",
  },
  {
    program: "throw.js",
    title: "A throw: completion records from ThrowStatement to the catch clause",
    breakpoints: [{ alg: "sec-runtime-semantics-catchclauseevaluation", path: "1" }],
    filters: ["throw"],
    stops: [
      {
        do: "start",
        reason: "exception",
        alg: "Evaluation",
        path: "3",
        text: "Throw exprValue.",
        line: 2,
        node: 'throw new RangeError("negative");',
        js: ["check", "(script)", "(host)"],
        slots: { exprValue: "#*" },
        cell: { exprValue: { message: '"negative"' } },
        say: "The throw filter stops at ThrowStatement's Evaluation, step 3, inside check. exprValue is the new RangeError: its cell has message \"negative\".",
      },
      {
        do: "next",
        reason: "step",
        alg: "Completion",
        path: "1",
        text: "Assert: completionRecord is a Completion Record.",
        line: 2,
        node: 'if (n < 0) throw new RangeError("negative");',
        slots: { completionRecord: "Completion { type: ~throw~, value: #*, target: ~empty~ }" },
        say: "A throw is a completion record: type ~throw~, value the error. Nothing unwinds by magic: each algorithm passes it on.",
      },
      {
        do: "out",
        reason: "step",
        alg: "Evaluation",
        path: "5",
        text: "Return ? UpdateEmpty(stmtCompletion, undefined).",
        slots: { stmtCompletion: "Completion { type: ~throw~, value: #*, target: ~empty~ }" },
        say: "Out to the if statement's Evaluation: its `?` returns the throw completion to its caller.",
      },
      {
        do: "jsOut",
        reason: "breakpoint",
        alg: "CatchClauseEvaluation",
        path: "1",
        text: "Let oldEnv be the running execution context's LexicalEnvironment.",
        line: 8,
        node: "catch (e) {\n  msg = e.message;\n}",
        frames: ["CatchClauseEvaluation 1"],
        js: ["(script)", "(host)"],
        slots: { thrownValue: "#*" },
        cell: { thrownValue: { message: '"negative"' } },
        say: "Step out by statement: the completion went up through check's body and [[Call]] to TryStatement's Evaluation, and the catch clause's breakpoint stops with thrownValue the same error. check's context is gone from the JS stack.",
      },
      {
        do: "jsNext",
        reason: "step",
        line: 9,
        node: "msg = e.message;",
        frames: ["Evaluation 1", "Evaluation 5", "CatchClauseEvaluation 7"],
        say: "The catch block's statement, with e bound to the error.",
      },
      {
        do: "jsNext",
        reason: "step",
        line: 11,
        node: "msg;",
        say: "After the try statement. Continue ends the script with msg, \"negative\".",
      },
    ],
    end: 'normal: "negative"',
  },
];

// Whether `got` is `want`, a "#*" in `want` matching any address.
export function same(want, got) {
  if (typeof want !== "string" || !want.includes("#*")) return got === want;
  const re = want.split("#*").map((p) => p.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("#\\d+");
  return typeof got === "string" && new RegExp(`^${re}$`).test(got);
}

// The ways observation `o` (demo_test.mjs's, or the page's) differs from `stop`.
export function mismatches(stop, o) {
  const bad = [];
  const want = (what, ok, got) => ok || bad.push(`${what}: got ${JSON.stringify(got)}`);
  for (const k of ["reason", "alg", "path", "line", "node"]) {
    if (k in stop) want(k, o[k] === stop[k], o[k]);
  }
  want("the listing's current step", o.current === o.path, o.current);
  if ("text" in stop) want("text", o.text?.startsWith(stop.text), o.text);
  if (stop.frames) want("frames", stop.frames.every((f, i) => o.frames[i] === f), o.frames.slice(0, stop.frames.length));
  if (stop.js) want("js", JSON.stringify(o.js) === JSON.stringify(stop.js), o.js);
  for (const [k, v] of Object.entries(stop.slots ?? {})) want(`slot ${k}`, same(v, o.slots?.[k]), o.slots?.[k]);
  for (const [slot, parts] of Object.entries(stop.cell ?? {})) {
    for (const [k, v] of Object.entries(parts)) want(`${slot}'s ${k}`, same(v, o.cell?.[slot]?.[k]), o.cell?.[slot]?.[k]);
  }
  return bad;
}
