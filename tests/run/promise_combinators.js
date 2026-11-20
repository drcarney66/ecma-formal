// expect: normal: "ok"
// print: all 1|2|3
// print: allSettled fulfilled:1 rejected:2
// print: any AggregateError 1,2
// print: race 9
// print: withResolvers 5
// print: try 6 thrown
// print: finally 7 then 7
// print: catch x
// Promise.all, allSettled, any, race, withResolvers, try, finally and catch (§27.5.4, §27.5.5).
var out = [];
function report() { for (var i = 0; i < out.length; i++) print(out[i]); }
var ps = [
  Promise.all([1, Promise.resolve(2), 3]).then(function (vs) { out[0] = "all " + vs.join("|"); }),
  Promise.allSettled([1, Promise.reject(2)]).then(function (vs) {
    out[1] = "allSettled " + vs[0].status + ":" + vs[0].value + " " + vs[1].status + ":" + vs[1].reason; }),
  Promise.any([Promise.reject(1), Promise.reject(2)]).catch(function (e) {
    out[2] = "any " + e.constructor.name + " " + e.errors.join(","); }),
  Promise.race([new Promise(function () {}), Promise.resolve(9)]).then(function (v) { out[3] = "race " + v; }),
  (function () { var r = Promise.withResolvers(); r.resolve(5); return r.promise; })()
    .then(function (v) { out[4] = "withResolvers " + v; }),
  Promise.all([Promise.try(function () { return 6; }), Promise.try(function () { throw 0; })
    .catch(function () { return "thrown"; })]).then(function (vs) { out[5] = "try " + vs.join(" "); }),
  Promise.resolve(7).finally(function () { return 8; }).then(function (v) { out[6] = "finally 7 then " + v; }),
  Promise.reject(new Error("x")).catch(function (e) { out[7] = "catch " + e.message; })
];
Promise.all(ps).then(report);
"ok"
