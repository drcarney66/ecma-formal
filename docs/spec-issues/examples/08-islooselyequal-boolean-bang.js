// IsLooselyEqual 9–10: "return ! IsLooselyEqual(! ToNumber(x), y)" when y is
// an Object whose ToPrimitive throws.
if (typeof print === "undefined") globalThis.print = console.log;
var dict = Object.create(null);           // no valueOf, no toString
try { print(dict == false); } catch (e) { print("dict == false: " + e.constructor.name); }
try { print(true == { valueOf() { throw new RangeError("v"); } }); }
catch (e) { print("true == {valueOf throws}: " + e.constructor.name); }
// Without a Boolean the same ToPrimitive throw propagates (step 11, `?`):
try { print(1 == dict); } catch (e) { print("1 == dict: " + e.constructor.name); }
