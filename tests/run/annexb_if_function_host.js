// §B.3.3 on a host that otherwise supports only it: `if (x) function f() {}`
// is the synthetic Block `{ function f() {} }`; without §B.3.2 its function is
// bound only in that Block.
// args: --annex-b sec-functiondeclarations-in-ifstatement-statement-clauses
// expect: normal: "undefined"
if (true) function f() {}
typeof f
