// A module that module_graph.js imports (not a test case).
export let counter = 0;
export function increment() { counter++; }
export default class Point { constructor(x) { this.x = x; } }
export * as self from "./lib.mjs";
