import { readJ } from "./main.mjs";
var print = globalThis.print || console.log;
print("probe sees " + JSON.stringify(readJ()));
