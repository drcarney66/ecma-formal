// The debugger engine's Worker: runs the WebAssembly build of the debugger (ecma-dbg-web,
// NAME.mjs and .wasm, scripts/build_wasm.py) in a browser Worker or a node `worker_threads`
// Worker, its protocol on three devices. It moves bytes and lines only; the
// engine speaks the protocol (lean/Debugger/Protocol.lean). The page's side
// is tools/dbg/client.mjs.
//
// The one message in: {type: "start", glue, module, sab, program, argv}
//   glue     the URL of NAME.mjs
//   module   NAME.wasm compiled (a WebAssembly.Module)
//   sab      the ring (tools/dbg/ring.mjs)
//   program  {name, source}, written to /work/NAME in MEMFS, or null
//   argv     more arguments for the engine
// Messages out: {line} (one line the engine wrote, without its newline),
// {stdout} and {stderr} (lines it printed there), then {exit: status} or {trap: "Name: message"}.
//
// The devices: /dev/dbg-in reads the ring, waiting (`Atomics.wait`) while it is
// empty; /dev/dbg-out sends each line it is written; /dev/dbg-poll reads and
// writes the ring's pause byte (the engine reads it every 4096 transitions and
// writes it back to 0 when it resumes from a pause).

import { PROGRAM_DIR, RingReader } from "./ring.mjs";

const wt = typeof WorkerGlobalScope === "undefined" ? await import("node:worker_threads") : null;
const post = wt ? (m) => wt.parentPort.postMessage(m) : (m) => self.postMessage(m);
const onMessage = wt
  ? (fn) => wt.parentPort.once("message", fn)
  : (fn) => self.addEventListener("message", (e) => fn(e.data), { once: true });

// A character device at `path` with the stream operations `ops`.
function device(FS, path, minor, ops) {
  const dev = FS.makedev(200, minor);
  FS.registerDevice(dev, { open() {}, close() {}, llseek: () => 0, ...ops });
  FS.mkdev(path, dev);
}

function devices(FS, ring) {
  device(FS, "/dev/dbg-in", 0, {
    read: (_stream, buffer, offset, length) => ring.read(buffer, offset, length),
  });
  const decoder = new TextDecoder();
  let pending = [];
  device(FS, "/dev/dbg-out", 1, {
    write(_stream, buffer, offset, length) {
      for (let i = 0; i < length; i++) {
        const b = buffer[offset + i] & 0xff;
        if (b === 10) {
          post({ line: decoder.decode(new Uint8Array(pending)) });
          pending = [];
        } else pending.push(b);
      }
      return length;
    },
  });
  device(FS, "/dev/dbg-poll", 2, {
    read(_stream, buffer, offset, length) {
      if (length === 0) return 0;
      buffer[offset] = ring.pause();
      return 1;
    },
    write(_stream, buffer, offset, length) {
      if (length > 0) ring.setPause(buffer[offset] & 0xff);
      return length;
    },
  });
}

onMessage(async ({ glue, module, sab, program, argv = [] }) => {
  let done = false;
  const finish = (m) => {
    if (!done) {
      done = true;
      post(m);
    }
  };
  try {
    const { default: create } = await import(glue);
    const M = await create({
      instantiateWasm(imports, ready) {
        WebAssembly.instantiate(module, imports).then((inst) => ready(inst, module));
        return {};
      },
      print: (text) => post({ stdout: text }),
      printErr: (text) => post({ stderr: text }),
      onExit: (status) => finish({ exit: status }),
    });
    devices(M.FS, new RingReader(sab));
    if (program) {
      M.FS.mkdirTree(PROGRAM_DIR);
      M.FS.writeFile(`${PROGRAM_DIR}/${program.name}`, program.source);
    }
    const status = M.callMain(["--dbg-in", "/dev/dbg-in", "--dbg-out", "/dev/dbg-out", "--dbg-poll", "/dev/dbg-poll", ...argv]);
    finish({ exit: status });
  } catch (e) {
    if (e?.name === "ExitStatus") finish({ exit: e.status });
    else finish({ trap: e instanceof Error ? `${e.name}: ${e.message}` : String(e) });
  }
});
