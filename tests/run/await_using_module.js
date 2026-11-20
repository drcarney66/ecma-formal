// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: last,dispose,disposed
// Erratum ExecuteModuleAsyncDisposeResources (refactor R22, finding F46): a
// module with top-level `await using` has [[HasTLA]] true, and ExecuteModule
// step 4.b's closure disposes module.[[Environment]]'s resources after the
// body (step 3.f's order): the module's last statement, then the disposal,
// awaited, and only then does its evaluation promise settle and this
// importing module run. The literal step 4.b never disposes: "last".
import { log } from "./r22_await_using.mjs";
print(log.join());
