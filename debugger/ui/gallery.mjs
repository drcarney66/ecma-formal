// The examples (the site's Examples page and the debugger's menu): gallery.json, as scripts/dbg_gallery.py
// compiles tools/dbg/gallery.json (each example with its source and arguments), and what an example's run
// must show under a build. No DOM: app.mjs and gallery_test.mjs (node) share it.
//
// An example: {id, group, title, line, name, source, args, module, breakpoints, lines, filters, demo?,
// builds: {BUILD: {pauses: [{alg, path, frames?}], end, printed?}}}. Opened, its breakpoints (spec, and
// line breakpoints by line number) and exception filters are set, stop on entry is cleared and it starts.
// Under BUILD, the run pauses first at each of `pauses` in order (`continue` between them; `frames`: the
// names that must be on the spec stack, innermost first, in that order, not necessarily adjacent), and,
// with the breakpoints and filters then cleared, ends with the result line `end` (a last step `?` matches
// any) and, if given, the printed lines `printed`.

import { outcomeMatches } from "./examples.mjs";

// The example `id` of the gallery, or null.
export function findExample(gallery, id) {
  return gallery?.examples?.find((e) => e.id === id) ?? null;
}

// The program an example runs: {name, source, args?}.
export function programOf(e) {
  return e.args?.length ? { name: e.name, source: e.source, args: e.args } : { name: e.name, source: e.source };
}

// The examples of the gallery by group, as the debugger's menu lists them: {groupTitle: [example]}.
export function menuGroups(gallery) {
  const out = {};
  for (const g of gallery?.groups ?? []) {
    const list = gallery.examples.filter((e) => e.group === g.id).map((e) => ({ ...e, key: e.id, label: e.title }));
    if (list.length) out[g.title] = list;
  }
  return out;
}

// What a pause (`stopped`, and the spec stack's frame names innermost first) does not match of `want`.
export function pauseMismatches(want, stopped, frames) {
  const bad = [];
  const s = stopped?.spec ?? {};
  if (want.alg !== s.alg && want.alg !== s.secId) bad.push(`paused at ${s.alg} (${s.secId}) ${s.path}, not ${want.alg} ${want.path}`);
  else if (want.path !== s.path) bad.push(`paused at ${s.alg} ${s.path}, not step ${want.path}`);
  if (want.frames) {
    let i = 0;
    for (const f of frames) if (i < want.frames.length && f === want.frames[i]) i++;
    if (i < want.frames.length) bad.push(`the spec stack ${JSON.stringify(frames.slice(0, 12))} has not ${JSON.stringify(want.frames)} in order`);
  }
  return bad;
}

// What a run's end (`ending`: {outcome, exitCode}, and the printed lines) does not match of `want`.
export function endMismatches(want, ending, printed) {
  if (!ending) return ["no end"];
  const bad = [];
  // An object's number (`[object #19131]`) changes with the realm's intrinsics: `#N` matches any.
  const plain = (t) => t?.replace(/#\d+/g, "#N");
  if (!outcomeMatches(plain(want.end), plain(ending.outcome))) bad.push(`ended ${JSON.stringify(ending.outcome)}, not ${JSON.stringify(want.end)}`);
  if (want.printed && JSON.stringify(printed) !== JSON.stringify(want.printed))
    bad.push(`printed ${JSON.stringify(printed)}, not ${JSON.stringify(want.printed)}`);
  return bad;
}

// One line on what an example shows under a build, from its check: "pauses at A 1, then B 2; ends normal: 8".
export function summary(check) {
  const at = check.pauses.map((p) => `${p.alg} ${p.path}`);
  return `${at.length ? `pauses at ${at.join(", then ")}; ` : ""}ends ${check.end}`;
}
