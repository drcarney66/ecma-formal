// PropertyDefinitionEvaluation (§13.2.5.6) and property access (§13.3.2).
// expect: normal: 5
({a: 1, "b": 2, 3: 3, ["c" + "d"]: 4}).cd + ({a: 1}).a
