// expect: normal: "Zm9vYmE= Zm9vYmE -_8 666f6f ; 102,111,111,98,97 ; 5,8 ; SyntaxError ; 10,255 ; SyntaxError"
// The base64 and hex methods of Uint8Array (§23.3): toBase64 with and without
// padding and with the base64url alphabet, toHex, fromBase64 (white space is
// skipped), setFromBase64 (its { read, written } result), and the SyntaxErrors
// of FromBase64 (strict: a partial last chunk) and FromHex (an odd length).
var bytes = new Uint8Array([102, 111, 111, 98, 97]);
var enc = [bytes.toBase64(), bytes.toBase64({ omitPadding: true }),
  new Uint8Array([0xFB, 0xFF]).toBase64({ alphabet: "base64url", omitPadding: true }),
  bytes.subarray(0, 3).toHex()].join(" ");
var dec = Array.from(Uint8Array.fromBase64("Zm9v\n YmE=")).join();
var target = new Uint8Array(8);
var r = target.setFromBase64("Zm9vYmE=");
var e1, e2;
try { Uint8Array.fromBase64("Zm9vYmE", { lastChunkHandling: "strict" }); } catch (e) { e1 = e.name; }
try { Uint8Array.fromHex("abc"); } catch (e) { e2 = e.name; }
[enc, dec, [r.written, r.read].join(), e1, Array.from(Uint8Array.fromHex("0aFF")).join(), e2].join(" ; ")
