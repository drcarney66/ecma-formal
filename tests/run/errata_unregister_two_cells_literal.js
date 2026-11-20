// expect: normal: "true|true"
// args: --erratum UnregisterIteratesCopy=literal
// Two cells with one unregister token, in a row (Erratum
// UnregisterIteratesCopy): the literal reading removes from the List it
// iterates and skips the second cell, so a second unregister finds it.
var fr = new FinalizationRegistry(function () {});
var token = {};
fr.register({}, 1, token);
fr.register({}, 2, token);
[fr.unregister(token), fr.unregister(token)].join("|");
