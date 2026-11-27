// expect: normal: "true,true"
[/\p{gc=Lu}/u.test("A"), /\p{General_Category=Uppercase_Letter}/u.test("A")].join(",");
