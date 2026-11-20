async function f() { await Promise.reject(2); }
f().catch(function () {});
