--> a comment: the first line is an HTMLCloseComment input element (B.1.1)
// With B.1.1 the line above is a comment; under §5.1.2 alone it would be a token no production has.
if (typeof print === "undefined") globalThis.print = console.log;
print("parsed");
