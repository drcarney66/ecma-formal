// Time passes while the agent computes (audit F325): the host chooses, at each
// reading of the current time, how many milliseconds have passed
// (Host.elapsed; the default host, 1). A loop that waits for Date.now() to
// move by 100 ms ends, as test262's await-import-evaluation_FIXTURE.js needs
// (start is 1; the loop reads 2 to 102; the last reading is 103).
// expect: normal: undefined
// print: 100,102
var start = Date.now(), n = 0;
while (Date.now() - start <= 100) n++;
print([n, Date.now() - start].join());
