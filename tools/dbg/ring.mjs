// The SharedArrayBuffer between a debugger client (tools/dbg/client.mjs) and its
// Worker (tools/dbg/engine-worker.mjs): a byte ring of requests, written by the
// client and read by the engine, which blocks in `Atomics.wait` while it is
// empty, and the pause flag the engine polls (`--dbg-poll`).
//
// Layout: Int32 [written, read, closed, pause], then CAPACITY bytes. `written` and
// `read` count bytes modulo 2^32; a byte's place is its count modulo CAPACITY.

export const CAPACITY = 1 << 20;

// Where the Worker writes the program it is given (`/work/NAME`, in MEMFS).
export const PROGRAM_DIR = "/work";

const WRITTEN = 0;
const READ = 1;
const CLOSED = 2;
const PAUSE = 3;
const HEADER = 16;

export function newRing() {
  return new SharedArrayBuffer(HEADER + CAPACITY);
}

const header = (sab) => new Int32Array(sab, 0, 4);
const data = (sab) => new Uint8Array(sab, HEADER, CAPACITY);

// The client's side: bytes in, never blocking (a page's main thread cannot wait);
// what does not fit waits in a backlog until the engine has read enough.
export class RingWriter {
  constructor(sab) {
    this.h = header(sab);
    this.d = data(sab);
    this.backlog = [];
    this.timer = null;
  }

  write(bytes) {
    this.backlog.push(bytes);
    this.flush();
  }

  flush() {
    this.timer = null;
    let w = Atomics.load(this.h, WRITTEN);
    while (this.backlog.length) {
      const free = CAPACITY - ((w - Atomics.load(this.h, READ)) | 0);
      if (free === 0) break;
      const b = this.backlog[0];
      const n = Math.min(free, b.length);
      for (let i = 0; i < n; i++) this.d[(w + i) & (CAPACITY - 1)] = b[i];
      w = (w + n) | 0;
      if (n === b.length) this.backlog.shift();
      else this.backlog[0] = b.subarray(n);
    }
    Atomics.store(this.h, WRITTEN, w);
    Atomics.notify(this.h, WRITTEN);
    if (this.backlog.length && !this.timer) this.timer = setTimeout(() => this.flush(), 1);
  }

  // The end of the input: the engine reads 0 bytes once the ring is empty.
  close() {
    Atomics.store(this.h, CLOSED, 1);
    Atomics.notify(this.h, WRITTEN);
  }

  setPause(v) {
    Atomics.store(this.h, PAUSE, v);
  }
}

// The engine's side.
export class RingReader {
  constructor(sab) {
    this.h = header(sab);
    this.d = data(sab);
  }

  // At most `length` bytes into `buffer` at `offset`, waiting while the ring is
  // empty; 0 at its end.
  read(buffer, offset, length) {
    if (length === 0) return 0;
    for (;;) {
      const w = Atomics.load(this.h, WRITTEN);
      const r = Atomics.load(this.h, READ);
      if (w !== r) {
        const n = Math.min(length, (w - r) | 0);
        for (let i = 0; i < n; i++) buffer[offset + i] = this.d[(r + i) & (CAPACITY - 1)];
        Atomics.store(this.h, READ, (r + n) | 0);
        return n;
      }
      if (Atomics.load(this.h, CLOSED)) return 0;
      Atomics.wait(this.h, WRITTEN, w);
    }
  }

  pause() {
    return Atomics.load(this.h, PAUSE) & 0xff;
  }

  setPause(v) {
    Atomics.store(this.h, PAUSE, v);
  }
}
