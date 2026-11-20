// More than 8 String keys (the table's index), removed and created again:
// creation order, with the re-created keys last; for-in and JSON.stringify
// see the same order.
// expect: normal: "k1,k3,k5,k7,k9,k11,k0,k4|k1,k3,k5,k7,k9,k11,k0,k4|{\"k1\":1,\"k3\":3,\"k5\":5,\"k7\":7,\"k9\":9,\"k11\":11,\"k0\":0,\"k4\":4}"
var o = {};
for (var i = 0; i < 12; i++) o['k' + i] = i;
for (var i = 0; i < 12; i += 2) delete o['k' + i];
o.k0 = 0;
o.k4 = 4;
var forIn = [];
for (var k in o) forIn.push(k);
Object.keys(o).join() + '|' + forIn.join() + '|' + JSON.stringify(o)
