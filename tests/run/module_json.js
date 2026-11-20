// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: 1,2 x
// A JSON module (ParseJSONModule, §16.2.1.8.2): its default export is the
// value that ParseJSON (§25.5.2.1) gives for the file's text.
import data from "./data.json" with { type: "json" };
print(data.a.join(",") + " " + data.b);
