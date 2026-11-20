// escape and unescape (§B.2.1) exist on a web-browser host.
// args: --web-browser
// expect: normal: "a%20%E4%u0100|a äĀ"
escape("a äĀ") + "|" + unescape("a%20%E4%u0100")
