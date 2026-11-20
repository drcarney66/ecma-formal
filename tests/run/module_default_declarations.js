// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// R26: the [+Default] declarations bind "*default*" through their own constructors.
// InstantiateOrdinaryFunctionObject of `function () {}` names it "default" (§15.2.4), and
// ClassDefinitionEvaluation of `class {}` gets "default" (§15.7.15); a named default
// declaration binds its own name in its module.
import f from "./r26_default_function.mjs";
import C from "./r26_default_class.mjs";
import g from "./r26_named_default.mjs";
if (f() !== 1 || f.name !== "default") throw new Error("default function: " + f.name);
if (new C().m() !== 2 || C.name !== "default") throw new Error("default class: " + C.name);
if (g() !== "function" || g.name !== "g") throw new Error("named default: " + g.name);
