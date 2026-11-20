var d = new Date(Date.UTC(2024, 1, 29, 12, 34, 56, 789));
print(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), d.toISOString());
print(new Date(-1e12).getUTCFullYear(), new Date(8.64e15).getUTCFullYear(), Date.UTC(1969, 11, 31));
print(new Date(2000, 0, 1).getTime() === new Date(2000, 0, 1).valueOf());
