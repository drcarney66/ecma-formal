// An array filled in descending index order: the keys are in ascending numeric
// order whatever the order of creation (OrdinaryOwnPropertyKeys step 2), and
// repeated pop keeps the length and the keys right.
// expect: normal: "0,1,2,3,4,5,6,7,8,9,10,11|3,4,5,6,7,8,9,10,11|8:0,1,2,3,4,5,6,7|0|"
var a = [];
for (var i = 11; i >= 0; i--) a[i] = i;
var r = Object.keys(a).join();
var b = [];
for (var i = 11; i >= 3; i--) b[i] = i;
r += '|' + Object.keys(b).join();
var c = a.slice();
for (var j = 0; j < 4; j++) c.pop();
r += '|' + c.length + ':' + Object.keys(c).join();
while (c.length) c.pop();
r + '|' + c.length + '|' + Object.keys(c).join()
