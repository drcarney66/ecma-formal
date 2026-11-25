// args: --bundle
// expect: normal: undefined
// print: esm-phase-imports-ok
// JS_BUNDLE_MODULE:dep.js
export let evaluated = 0;
evaluated++;
export const value = 42;

// JS_BUNDLE_MODULE_ENTRYPOINT:main.js
import source depSrc from "./dep.js";

const AbstractModuleSource = Object.getPrototypeOf(depSrc.constructor);
if (AbstractModuleSource.name !== "AbstractModuleSource") throw new Error("bad AbstractModuleSource");
if (depSrc.constructor.name !== "ModuleSource") throw new Error("bad ModuleSource");
if (depSrc[Symbol.toStringTag] !== "ModuleSource") throw new Error("bad toStringTag: " + depSrc[Symbol.toStringTag]);
if (!(depSrc instanceof AbstractModuleSource)) throw new Error("not instanceof AbstractModuleSource");

const depSrc2 = await import.source("./dep.js");
if (depSrc2 !== depSrc) throw new Error("import.source should return same ModuleSource object");

const ns1 = await import(depSrc);
const ns2 = await import("./dep.js");
if (ns1 !== ns2) throw new Error("import(depSrc) should coalesce to same namespace");
if (ns1.value !== 42 || ns1.evaluated !== 1) throw new Error("bad evaluation count: " + ns1.evaluated);

print("esm-phase-imports-ok");
