// expect: normal: "1,2,3"
const v1 = (function () { let a
  return 1 })();
const v2 = ((x = function () { let b
  return 2 }) => x())();
let v3 = 0;
({ m() { let c = 3
  return c } }.m && (v3 = ({ m() { let c = 3
  return c } }).m()));
[v1, v2, v3].join(",");
