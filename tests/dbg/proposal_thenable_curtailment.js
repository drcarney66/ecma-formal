const events = [];
const thenable = {
  then(resolve) {
    events.push("then-called");
    resolve(42);
  }
};
const p = Promise.resolve(thenable);
Promise.resolve().then(() => events.push("microtask"));
p.then((v) => {
  events.push("resolved:" + v);
  print(events.join(" -> "));
});
void 0;
