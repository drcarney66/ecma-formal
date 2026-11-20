import { readJ } from "./module_json_relink.js";
var v = readJ();
print("probe sees " + (v === undefined ? "undefined" : v.a));
