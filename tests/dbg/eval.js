var a = 1;
var b = eval("var c = a + 1;\nc * 2");
var f = new Function("x", "var y = x + 1;\nreturn y * 2;");
var r = f(b);
print(r);
