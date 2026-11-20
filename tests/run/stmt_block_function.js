// A function declaration in a block is instantiated by
// BlockDeclarationInstantiation before the block's statements run.
// expect: normal: "function"
{ typeof f; function f() {} }
