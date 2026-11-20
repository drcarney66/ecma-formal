// A DataView reads big-endian by default and little-endian on request
// (GetViewValue, §25.3.1.5); getFloat64 reads back the bits setFloat64 wrote.
// expect: normal: "64,24 ; 3.141592653589793 ; 258,513"
var dv = new DataView(new ArrayBuffer(8));
dv.setFloat64(0, Math.PI);
var s = [dv.getUint8(0) + "," + dv.getUint8(7), dv.getFloat64(0)];
dv.setUint16(0, 258);
s.push(dv.getUint16(0) + "," + dv.getUint16(0, true));
s.join(" ; ")
