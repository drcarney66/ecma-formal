// ArraySetLength step 18: indices deleted in descending order, stopped by a
// non-configurable index; the length is that index + 1.
// expect: normal: "false|6|0,1,2,3,4,5"
var a = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
Object.defineProperty(a, 5, { value: 5, configurable: false });
var ok = Reflect.set(a, 'length', 2);
var r = String(Reflect.defineProperty(a, 'length', { value: 2 }));
r + '|' + a.length + '|' + Object.keys(a).join()
