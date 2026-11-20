// What the debugger's WebAssembly build needs of a browser, checked before it is loaded. The build
// (scripts/build_wasm.py: emcc -m64 -fwasm-exceptions) uses 64-bit memory (Memory64), WebAssembly's
// exception handling (its first form: try, catch, rethrow) and bulk memory operations; it runs in a module
// Worker, which reads the page's requests from a SharedArrayBuffer and waits on it with Atomics.wait, and a
// SharedArrayBuffer needs the page cross-origin isolated. It uses no WebAssembly threads. Each check is a
// small module WebAssembly.validate accepts only with that feature.

const WASM = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
// A memory of 64-bit addresses: the memory section, one memory, limits flag 0x04 (i64, no maximum), 1 page.
const MEMORY64 = new Uint8Array([...WASM, 0x05, 0x03, 0x01, 0x04, 0x01]);
// A function `() -> ()` whose body is `try end`.
const EXCEPTIONS = new Uint8Array([...WASM, 0x01, 0x04, 0x01, 0x60, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
  0x0a, 0x07, 0x01, 0x05, 0x00, 0x06, 0x40, 0x0b, 0x0b]);
// A memory and a function whose body is `i32.const 0; i32.const 0; i32.const 0; memory.fill`.
const BULK = new Uint8Array([...WASM, 0x01, 0x04, 0x01, 0x60, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
  0x05, 0x03, 0x01, 0x00, 0x01, 0x0a, 0x0d, 0x01, 0x0b, 0x00, 0x41, 0x00, 0x41, 0x00, 0x41, 0x00, 0xfc, 0x0b, 0x00, 0x0b]);

function validates(W, bytes) {
  try {
    return W.validate(bytes);
  } catch {
    return false;
  }
}

// What the WebAssembly build needs and `g` (the page's global object) lacks, as phrases; none: [].
// Cross-origin isolation is not among them: the page may still get it from coi-serviceworker.js.
export function missing(g = globalThis) {
  const out = [];
  if (typeof g.WebAssembly?.validate !== "function") return ["WebAssembly"];
  if (!validates(g.WebAssembly, MEMORY64)) out.push("WebAssembly's 64-bit memory (Memory64)");
  if (!validates(g.WebAssembly, EXCEPTIONS)) out.push("WebAssembly's exception handling");
  if (!validates(g.WebAssembly, BULK)) out.push("WebAssembly's bulk memory operations");
  if (typeof g.Worker !== "function") out.push("Web Workers");
  if (typeof g.SharedArrayBuffer !== "function" && !g.isSecureContext) out.push("a secure context (https or localhost)");
  if (typeof g.Atomics?.wait !== "function") out.push("Atomics.wait");
  return out;
}

// The browsers whose current releases have all of it.
export const BROWSERS = "Chrome or Edge 133 or later, or Firefox 134 or later";

// For the tests: the modules, to check that each one fails without its feature.
export const MODULES = { MEMORY64, EXCEPTIONS, BULK };
