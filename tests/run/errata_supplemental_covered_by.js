// expect: normal: undefined
// print: 30
async function run() {
  let a, b;
  ({ x: { a }, y: [b] } = { x: { a: 10 }, y: [20] });
  return (await Promise.resolve(a)) + b;
}
void run().then(v => print(v));
