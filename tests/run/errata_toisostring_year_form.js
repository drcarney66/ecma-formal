// expect: normal: "1900-01-01T00:00:00.000Z,2026-01-01T00:00:00.000Z,+010000-01-01T00:00:00.000Z"
[
  new Date(Date.UTC(0, 0, 1)).toISOString(),
  new Date(Date.UTC(2026, 0, 1)).toISOString(),
  new Date(Date.UTC(10000, 0, 1)).toISOString(),
].join(",");
