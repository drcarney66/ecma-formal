// expect: normal: "true,true,true,true"
[/\p{Lu}/u.test("A"), /\p{ASCII}/u.test("a"), /\p{Hex}/u.test("f"), /\p{Any}/u.test("\u{10FFFF}")].join(",");
