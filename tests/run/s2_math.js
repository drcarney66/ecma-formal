// Math (§21.3): the value properties are non-writable, the exactly specified
// functions compute their results, and Object.prototype.toString sees the tag.
// expect: normal: "3.141592653589793,-1,-0,3,-2,1024,-5,31,1.100000023841858,false,[object Math]"
"use strict";
var d = Object.getOwnPropertyDescriptor(Math, "PI");
[Math.PI, Math.floor(-0.5), 1 / Math.ceil(-0.5) === -Infinity ? "-0" : "+0", Math.max(1, "3", 2),
 Math.round(-2.5), Math.pow(2, 10), Math.imul(0xffffffff, 5), Math.clz32(1), Math.fround(1.1),
 d.writable || d.configurable, Object.prototype.toString.call(Math)].join()
