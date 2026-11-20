// The imported module of await_using_module.js: its `await using` gives it
// [[HasTLA]] true (ExecuteModule step 4).
export const log = [];
await using r = {
  async [Symbol.asyncDispose]() {
    log.push("dispose");
    await 0;
    log.push("disposed");
  }
};
log.push("last");
