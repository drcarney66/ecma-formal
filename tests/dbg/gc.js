var keep = { x: 42 };
for (var i = 0; i < 20; i++) {
  var tmp = { dead: i, arr: [i, i + 1] };
}
tmp = null;
debugger;
print(keep.x);
