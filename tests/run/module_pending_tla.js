// A module whose top-level await never resumes (audit F040/F117/F293): when no
// Job is left, its evaluation Promise is still pending and never settles. The
// host ends the run there with that Promise as its result, and what the module
// printed is kept (before, the run stopped with `unsupported sec-jobs` and lost
// the output).
// module: yes
// expect: normal: [object #N]
// print: before
print("before");
await new Promise(function () {});
print("never");
