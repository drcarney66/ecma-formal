// expect: throw: RangeError
// Under default StringMaximumLength=proposed, String.prototype.repeat throws
// a RangeError when the requested length exceeds the host's maximum String
// length (2^28 code units) before forming the String.
'ab'.repeat(2 ** 52)
