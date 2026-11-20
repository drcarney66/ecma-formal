// GetValue of a property reference on undefined throws a TypeError from ToObject
// (object 9 is the new error, after the object literal at 8).
// expect: throw: TypeError
({}).x.y
