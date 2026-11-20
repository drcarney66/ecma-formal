// The spec issues' examples (spec-examples.json, scripts/dbg_spec_examples.py) against the model's
// run: what a debugger session's pauses and end do not match of an example's `filters` and
// `expect` ({exit, line, printed}). No DOM: spectest.mjs (the page) and spec_examples_test.mjs (node) share it.

// Whether the outcome line `got` is `want`: a `?` or `-` step in `want` matches any.
export function outcomeMatches(want, got) {
  if (want === got) return true;
  const w = want.split(" ");
  const g = got?.split(" ") ?? [];
  return w.length === g.length && w.every((x, i) => x === g[i] || (i === w.length - 1 && (x === "?" || x === "-")));
}

// The lines the program printed: the model's stdout output.
export function printedLines(model) {
  const lines = model.output.filter((o) => o.category === "stdout").map((o) => o.text).join("").split("\n");
  if (lines.at(-1) === "") lines.pop();
  return lines;
}

// What the session's end (`ending`: {outcome, exitCode}) and printed lines do not match of `expect`.
// ecma-run prints only the stop of a run that stops, so the lines are not compared then.
export function endMismatches(expect, ending, printed) {
  if (!ending) return ["no end"];
  const bad = [];
  if (!outcomeMatches(expect.line, ending.outcome)) bad.push(`outcome ${JSON.stringify(ending.outcome)}, not ${JSON.stringify(expect.line)}`);
  if (ending.exitCode !== expect.exit) bad.push(`exit code ${ending.exitCode}, not ${expect.exit}`);
  if (!expect.line.startsWith("stop: ") && JSON.stringify(printed) !== JSON.stringify(expect.printed))
    bad.push(`printed ${JSON.stringify(printed)}, not ${JSON.stringify(expect.printed)}`);
  return bad;
}

// What the pauses after the breakpoint (`stops`: the `stopped` bodies) do not match of the
// example: one at the model's stop if its `stop` filter is on, else none.
export function stopMismatches(e, stops) {
  const at = stops.map((s) => `${s.reason}${s.spec.filter ? ` (${s.spec.filter})` : ""} at ${s.spec.secId} ${s.spec.path}`);
  const filtered = stops.filter((s) => s.spec.filter === "stop").length;
  if (e.filters.includes("stop") ? filtered === 1 && stops.length === 1 : !stops.length) return [];
  return [`paused ${at.length ? at.join(", ") : "nowhere"}${e.filters.includes("stop") ? ", not once at the model's stop" : ""}`];
}
