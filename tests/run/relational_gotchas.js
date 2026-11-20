// null >= 0 but not null > 0 or null == 0; "10" < "9" but not "10" < 9; 3 > 2 > 1 is false.
// expect: normal: true
null >= 0 && !(null > 0) && !(null == 0) && "10" < "9" && !("10" < 9) && !(3 > 2 > 1)
