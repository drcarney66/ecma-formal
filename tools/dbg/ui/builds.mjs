// The debugger's builds: the selector's table (builds.json: tools/dbg/builds.json, or the site's, which
// scripts/build_site.py writes), which build a page runs (`?build=`), the arguments of a launch, the key
// a build's saved configuration is kept under, and the page's URL for another build or example. No DOM:
// app.mjs and the node tests (builds_test.mjs, gallery_test.mjs) share it.
//
// A build is {id, label, description, wasm, args}: `wasm` the Worker build's file (its .mjs beside it),
// relative to the debugger's directory; `args` ecma-dbg's launch arguments, before an example's own.

// The table when no builds.json is served: the specification's build alone.
export const FALLBACK = [
  { id: "spec", label: "The specification", description: "The machine with every erratum at its default reading.", wasm: "ecma-dbg-web.wasm", args: [] },
];

const ID = /^[a-z][a-z0-9-]{0,31}$/;

// The builds of a builds.json's parsed text: each well formed entry, in order, the first of an id kept.
// Throws if none is.
export function readBuilds(json) {
  const out = [];
  for (const b of Array.isArray(json?.builds) ? json.builds : []) {
    if (!b || typeof b !== "object" || !ID.test(b.id ?? "") || out.some((x) => x.id === b.id)) continue;
    if (typeof b.wasm !== "string" || !/^[A-Za-z0-9._-]+\.wasm$/.test(b.wasm)) continue;
    const args = Array.isArray(b.args) && b.args.every((a) => typeof a === "string") ? b.args : null;
    if (!args) continue;
    const entry = { id: b.id, label: String(b.label ?? b.id), description: String(b.description ?? ""), wasm: b.wasm, args };
    if (typeof b.wasmBytes === "number" && Number.isFinite(b.wasmBytes) && b.wasmBytes > 0) {
      entry.wasmBytes = Math.floor(b.wasmBytes);
    }
    out.push(entry);
  }
  if (!out.length) throw new Error("builds.json: no build");
  return out;
}

// The build `id` asks for, else the table's first.
export function chooseBuild(builds, id) {
  return builds.find((b) => b.id === id) ?? builds[0];
}

// The build to switch to when `example` is picked from the menu: a proposal example switches to its
// primary build (`Object.keys(example.builds)[0]` when not the default `builds[0]`), and any example
// whose `builds` omits `currentBuild.id` switches to its first available build in `builds`.
export function exampleBuild(example, currentBuild, builds) {
  if (!example?.builds || typeof example.builds !== "object" || !builds?.length) return currentBuild;
  const supported = Object.keys(example.builds).filter((id) => builds.some((b) => b.id === id));
  if (!supported.length) return currentBuild;
  const primary = supported[0];
  if (primary !== builds[0].id || !supported.includes(currentBuild?.id)) {
    return chooseBuild(builds, primary);
  }
  return currentBuild;
}

// A launch's arguments: the build's, then the program's (an example's own, then `?args=`).
export function launchArgs(build, programArgs = []) {
  return [...(build?.args ?? []), ...(programArgs ?? [])];
}

// `?args=`: arguments separated by spaces (a `+` in the query is one), at most 32 of them, each an option
// of ecma-run's or its value; null if there are none.
export function parseArgs(text) {
  if (!text) return null;
  const args = text.split(/\s+/).filter(Boolean);
  if (!args.length || args.length > 32 || args.some((a) => a.length > 200)) return null;
  return args;
}

// The key a build's configuration (program, breakpoints, filters, stop on entry) is saved under: the
// specification's keeps the key it had before builds existed, so that nothing saved is lost.
export function storageKey(buildId) {
  return !buildId || buildId === "spec" ? "ecma-dbg" : `ecma-dbg@${buildId}`;
}

// The page's URL (`href`) with its query changed: each key of `changes` set, or removed where null.
// A build that is the table's first is left out of the query.
export function pageURL(href, changes, builds = null) {
  const u = new URL(href);
  for (const [k, v] of Object.entries(changes)) {
    if (v === null || v === undefined || (k === "build" && builds && v === builds[0].id)) u.searchParams.delete(k);
    else u.searchParams.set(k, v);
  }
  return u.href;
}
