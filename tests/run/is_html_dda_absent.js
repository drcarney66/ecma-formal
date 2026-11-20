// expect: normal: "false,undefined"
// A host that is not a web browser and does not otherwise support §B.3.6 has
// no $262.IsHTMLDDA (test262 INTERPRETING.md: "present only in
// implementations that can provide it"; refactor R21).
["IsHTMLDDA" in $262, typeof $262.IsHTMLDDA].join();
