// Template literals (§13.2.8), tagged templates with a cached, frozen template
// object (GetTemplateObject), spread in calls and arrays, and new.target.
// expect: normal: "a1b2c|a\\n,b,|true|true|9|4|true,false"
var x = 1;
var r = [`a${x}b${x + 1}c`];
function tag(s) { return s; }
function get() { return tag`a\n${1}b${2}`; }
var t1 = get(), t2 = get();
r.push(t1.raw.join());
r.push(t1 === t2);
r.push(Object.isFrozen(t1) && Object.isFrozen(t1.raw));
r.push(Math.max(...[1, 9, 3]));
r.push([0, ...[1, 2], 3].length);
function F() { return new.target === F; }
var made = new F();
r.push((made instanceof F) + "," + F());
r.join("|")
