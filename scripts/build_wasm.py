#!/usr/bin/env python3
"""A Lean program as a wasm64 module, from the C that Lake emits.

    build_wasm.py [--name ecma-dbg-web] [--root Debugger.Main] [--exe ecma-dbg] [--node] [--out build/web]

Run in the flake's wasm shell (ECMA_WASM: leanWasm's lib/ and include/; emcc with its frozen cache).
It runs no Lean build: `lake build EXE` must have written each module's C (.lake/build/ir) already, and
the build stops if a module of ROOT's import closure has no C, or Lake's trace of it records another source
than the one there now (--stale-ok goes on with a warning). Each module of the closure is then compiled by emcc to build/wasm/obj/<Module>.o, when its C is newer, and the objects are linked
with leanWasm's archives into OUT/NAME.mjs and OUT/NAME.wasm: an ES module factory for a browser or
node Worker (tools/dbg/engine-worker.mjs), with MEMFS. With --node: OUT/NAME.js, a node program
(scripts/wasm_run.mjs runs it in a Worker with a large stack).
"""

import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "lean"
IR = ROOT / ".lake/build/ir"
LIB = ROOT / ".lake/build/lib/lean"
# Every object's flags (flake.nix's emCompileFlags, which the frozen cache is built for).
COPTS = ["-O2", "-m64", "-fwasm-exceptions"]
MEMORY = ["-sALLOW_MEMORY_GROWTH=1", "-sMAXIMUM_MEMORY=16GB", "-sSTACK_SIZE=16MB", "-sINITIAL_MEMORY=64MB"]
# The C stack lies below static data (--stack-first), so its overflow traps.
COMMON = ["-sEXIT_RUNTIME=1", "-sERROR_ON_UNDEFINED_SYMBOLS=1", "-Wl,--stack-first"]
NODE_LINKOPTS = MEMORY + ["-sNODERAWFS=1"] + COMMON
# The heap views stay on wasmMemory.buffer (GROWABLE_ARRAYBUFFERS=0): a browser's TextDecoder refuses
# a view of a resizable buffer.
WORKER_LINKOPTS = MEMORY + [
    "-sENVIRONMENT=worker,node",
    "-sMODULARIZE=1",
    "-sEXPORT_ES6=1",
    "-sINVOKE_RUN=0",
    "-sFORCE_FILESYSTEM=1",
    "-sEXPORTED_RUNTIME_METHODS=FS,callMain",
    "-sGROWABLE_ARRAYBUFFERS=0",
] + COMMON
LIBS = ["libleanrt.a", "libuv.a", "libInit.a", "libStd.a"]
IMPORT = re.compile(r"^(?:public\s+|private\s+)?import\s+(?:all\s+)?((?:Ecma|Engine|Debugger|Unicode)\.[\w.']+)", re.MULTILINE)


def closure(root: str) -> list[str]:
    """ROOT's import closure among this package's modules."""
    seen: set[str] = set()
    todo = [root]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += IMPORT.findall((SRC / (m.replace(".", "/") + ".lean")).read_text())
    return sorted(seen)


# Lake's hash of a text file (Lake's `Hash.ofText`: Lean's string hash, MurmurHash64A with seed 11, of the text
# with CRLF as LF, mixed into `Hash.nil`), which a module's .trace records for its source.
_M, _MASK = 0xC6A4A7935BD1E995, (1 << 64) - 1


def _murmur(b: bytes, seed: int = 11) -> int:
    h = (seed ^ (len(b) * _M)) & _MASK
    n = len(b) // 8 * 8
    for i in range(0, n, 8):
        k = (int.from_bytes(b[i : i + 8], "little") * _M) & _MASK
        k ^= k >> 47
        h = ((h ^ ((k * _M) & _MASK)) * _M) & _MASK
    if len(b) > n:
        for j, x in enumerate(b[n:]):
            h ^= x << (8 * j)
        h = (h * _M) & _MASK
    h ^= h >> 47
    h = (h * _M) & _MASK
    return h ^ (h >> 47)


def lake_text_hash(path: Path) -> str:
    k = (_murmur(path.read_bytes().replace(b"\r\n", b"\n")) * _M) & _MASK
    k = (k ^ (k >> 47)) ^ _M
    return f"{((1723 ^ k) * _M) & _MASK:016x}"


def stale_modules(mods: list[str]) -> list[str]:
    """The modules Lake has not built from their source as it is now: no C (.lake/build/ir), or a trace
    (.lake/build/lib/lean/M.trace) whose source hash is not the source's, or whose C is not the one there."""
    out = []
    for m in mods:
        rel = m.replace(".", "/")
        c, src, trace = IR / (rel + ".c"), SRC / (rel + ".lean"), LIB / (rel + ".trace")
        try:
            t = json.loads(trace.read_text())
            hashes = {k: v for k, v in t["inputs"] if isinstance(k, str) and isinstance(v, str)}
            ok = (hashes.get(str(src)) == lake_text_hash(src)
                  and (IR / (rel + ".c.hash")).read_text().strip() == t["outputs"]["c"].split(".")[0])
        except (OSError, KeyError, ValueError, TypeError):
            ok = False
        if not ok or not c.exists():
            out.append(m)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--name", default="ecma-dbg-web")
    ap.add_argument("--root", default="Debugger.Main")
    ap.add_argument("--exe", default="ecma-dbg", help="the Lake executable whose build emitted the closure's C")
    ap.add_argument("--stale-ok", action="store_true", help="build from C of another source than the one there, with a warning")
    ap.add_argument("--node", action="store_true", help="a node program, not a Worker module")
    ap.add_argument("--out", type=Path, default=ROOT / "build/web")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    a = ap.parse_args()
    wasm = os.environ.get("ECMA_WASM")
    if not wasm:
        sys.exit("build_wasm.py: no ECMA_WASM: run in the flake's wasm shell (flake.nix)")
    obj = ROOT / "build/wasm/obj"
    tmp = ROOT / "build/wasm/tmp"
    tmp.mkdir(parents=True, exist_ok=True)
    env = os.environ | {"HOME": str(tmp), "TMPDIR": str(tmp)}

    def compile_one(m: str) -> Path:
        c = IR / (m.replace(".", "/") + ".c")
        o = obj / (m + ".o")
        if not o.exists() or o.stat().st_mtime < c.stat().st_mtime:
            o.parent.mkdir(parents=True, exist_ok=True)
            r = subprocess.run(["emcc", *COPTS, "-DNDEBUG", f"-I{wasm}/include", "-c", str(c), "-o", str(o)],
                               env=env, capture_output=True, text=True, check=False)
            if r.returncode != 0:
                raise SystemExit(f"build_wasm.py: {m}:\n{r.stderr}")
        return o

    mods = closure(a.root)
    stale = stale_modules(mods)
    if stale:
        msg = (f"build_wasm.py: the Lean build's C is missing or of another source for {len(stale)} of "
               f"{len(mods)} modules ({', '.join(stale[:5])}{', ...' if len(stale) > 5 else ''}): "
               f"run `lake build {a.exe}` first")
        if not a.stale_ok:
            sys.exit(msg)
        print(f"warning: {msg}; building from it anyway (--stale-ok)", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        objects = list(ex.map(compile_one, mods))
    # What the program names of the Lean library, which the Worker build does not have (scripts/wasm_stubs.c).
    stubs = obj / "wasm_stubs.o"
    subprocess.run(["emcc", *COPTS, "-DNDEBUG", f"-I{wasm}/include", "-c", str(ROOT / "scripts/wasm_stubs.c"),
                    "-o", str(stubs)], env=env, check=True)
    objects.append(stubs)
    a.out.mkdir(parents=True, exist_ok=True)
    rsp = tmp / f"{a.name}.rsp"
    rsp.write_text("".join(f"{o}\n" for o in objects))
    out = a.out / (a.name + (".js" if a.node else ".mjs"))
    subprocess.run(["em++", *COPTS, *(NODE_LINKOPTS if a.node else WORKER_LINKOPTS), f"@{rsp}",
                    *(f"{wasm}/lib/{lib}" for lib in LIBS), "-o", str(out)], env=env, check=True)
    print(f"{out}: {len(mods)} modules, {out.with_suffix('.wasm').stat().st_size} B of wasm")
    return 0


if __name__ == "__main__":
    sys.exit(main())
