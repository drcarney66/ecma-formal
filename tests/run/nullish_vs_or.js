// ?? only skips undefined and null; || skips every falsy value.
// expect: normal: "0,,2"
(0 ?? 1) + "," + ("" ?? 1) + "," + ("" || 2)
