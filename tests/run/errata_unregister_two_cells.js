// expect: normal: "true|false"
// Two cells with one unregister token, in a row (Erratum
// UnregisterIteratesCopy): the test262 reading removes both.
var fr = new FinalizationRegistry(function () {});
var token = {};
fr.register({}, 1, token);
fr.register({}, 2, token);
[fr.unregister(token), fr.unregister(token)].join("|");
