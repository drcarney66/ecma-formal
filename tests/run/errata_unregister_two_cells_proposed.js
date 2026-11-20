// expect: normal: "true|false"
// args: --reading proposed
// The proposed readings, with the definition readings kept: the run gets past
// realm setup, and UnregisterIteratesCopy's proposed text removes both cells.
var fr = new FinalizationRegistry(function () {});
var token = {};
fr.register({}, 1, token);
fr.register({}, 2, token);
[fr.unregister(token), fr.unregister(token)].join("|");
