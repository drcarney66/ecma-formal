// args: --web-browser
// expect: normal: "function,0,function,function"
/* multi-line
   comment without --> */
function g() {
  { function f() { return 1; } }
  let y = 0;
  { function y() { return 2; } }
  if (true) function h() { return 3; }
  const k = (() => { if (true) function m() { return 4; } return typeof m; })();
  return [typeof f, y, typeof h, k].join(",");
}
g();
