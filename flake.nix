{
  description = "ecma-formal: ECMA-262 formalized in Lean, steppable in its spec-step debugger";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  # Two dev shells:
  #   default  Lean (lean, lake, leanc), Rust, Python, node: the native build, the generators, the site script
  #   wasm     default, with emscripten and the Lean runtime as wasm64 archives (ECMA_WASM): the Worker build;
  #            and `chrome`, `firefox` for the debugger's browser tests
  # Make a profile of each once, and again after this file changes:
  #   nix develop --profile ~/.local/state/ecma-formal/devshell -c true
  #   nix develop .#wasm --profile ~/.local/state/ecma-formal/devshell-wasm -c true
  outputs =
    { self, nixpkgs }:
    let
      # Toolchain pins: evaluation fails if the locked nixpkgs provides another Lean.
      versions = {
        lean = "4.35.0";
      };
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      checkPin =
        name: want: drv:
        if drv.version == want then
          drv
        else
          throw "${name} pin drifted: flake.nix wants ${want}, locked nixpkgs provides ${drv.version}";

      perSystem =
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          lib = pkgs.lib;
          leanPackages = pkgs.leanPackages;
          lean = checkPin "lean" versions.lean leanPackages.lean4; # lean, lake, leanc
          python = pkgs.python3.withPackages (p: [ p.markdown ]);
          node =
            if lib.versionAtLeast pkgs.nodejs.version "22" then
              pkgs.nodejs
            else
              throw "node ${pkgs.nodejs.version} lacks Memory64 (wasm64): the locked nixpkgs must provide node 22 or later";

          # The Unicode Character Database of Unicode 17.0.0: the files the Unicode tables
          # (lean/Unicode) are generated from (scripts/unicode_data.py, unicode_properties.py).
          ucd =
            let
              files = {
                "UCD.zip" = {
                  url = "https://www.unicode.org/Public/17.0.0/ucd/UCD.zip";
                  sha256 = "2066d1909b2ea93916ce092da1c0ee4808ea3ef8407c94b4f14f5b7eb263d28e";
                };
                "emoji-sequences.txt" = {
                  url = "https://www.unicode.org/Public/17.0.0/emoji/emoji-sequences.txt";
                  sha256 = "12cc8267dc33cbd11ed32bcf6fc5dc2ad9c7a77bae1bdfba2f41b1b9b3ead8dd";
                };
                "emoji-zwj-sequences.txt" = {
                  url = "https://www.unicode.org/Public/17.0.0/emoji/emoji-zwj-sequences.txt";
                  sha256 = "5b25441daed2322b068c5e70cda522946a4f0274df864445a1965a92e5fc5cad";
                };
              };
            in
            pkgs.linkFarm "ucd-17.0.0" (
              lib.mapAttrsToList (name: f: {
                inherit name;
                path = pkgs.fetchurl f;
              }) files
            );

          # Lean rebuilt from source by the locked nixpkgs' recipe (the derivation `lean` wraps), with one
          # more output `c`: the stage-1 C that libInit and libStd were compiled from (`c/`), the build's
          # generated headers (`include/`) and the runtime sources (`src/`), for the wasm build.
          leanC =
            let
              wrapped = leanPackages.callPackage "${nixpkgs}/pkgs/development/lean-modules/lean4" {
                symlinkJoin = args: pkgs.symlinkJoin args // { unwrapped = builtins.head args.paths; };
              };
            in
            checkPin "leanC" versions.lean (
              wrapped.unwrapped.overrideAttrs (old: {
                outputs = [
                  "out"
                  "c"
                ];
                moveToDev = false; # `c` keeps its `include/`
                meta = old.meta // {
                  outputsToInstall = [
                    "out"
                    "c"
                  ];
                };
                postInstall = (old.postInstall or "") + ''
                  temp=stage1/lib/temp
                  test -f $temp/Init/Prelude.c
                  mkdir -p $c/c $c/include $c/src
                  (cd $temp && find Init Std Init.c Std.c -name '*.c' -exec cp --parents -t $c/c {} +)
                  cp -r stage1/include/lean stage1/githash.h $c/include/
                  cp -r ../src/runtime ../src/include ../src/util $c/src/
                '';
              })
            );

          # Emscripten's flags for the wasm64 build (scripts/build_wasm.py has the same): every object's,
          # and the links emCache is built for. (`-m64` is `-sMEMORY64=1`, which emcc's link deprecates.)
          emCompileFlags = "-O2 -m64 -fwasm-exceptions";
          emLinkFlags =
            "-sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=16GB -sSTACK_SIZE=16MB -sINITIAL_MEMORY=64MB"
            + " -sNODERAWFS=1 -sEXIT_RUNTIME=1";
          emStackFlags = "-Wl,--stack-first";

          # Emscripten's library cache (`EM_CACHE`) with every system library variant those flags link,
          # built by compiling and linking a C and a C++ program with them; used read-only
          # (`EM_FROZEN_CACHE=1`), so a variant it lacks fails the build.
          emCache = pkgs.stdenvNoCC.mkDerivation {
            name = "ecma-em-cache-${pkgs.emscripten.version}";
            nativeBuildInputs = [ pkgs.emscripten ];
            dontUnpack = true;
            buildPhase = ''
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/cache
              cp -R ${pkgs.emscripten}/share/emscripten/cache $EM_CACHE
              chmod -R u+w $EM_CACHE
              printf '#include <stdio.h>\nint main(void) { puts("c"); return 0; }\n' > c.c
              printf '#include <iostream>\n#include <stdexcept>\nint main() { try { throw std::runtime_error("c++"); } catch (const std::exception &e) { std::cout << e.what() << std::endl; } }\n' > cxx.cpp
              # (em++ links the C++ one: emcc no longer adds libc++ for an object.)
              both() {
                emcc ${emCompileFlags} -c c.c -o c.o
                emcc ${emCompileFlags} ${emLinkFlags} c.o -o c.js
                em++ ${emCompileFlags} -c cxx.cpp -o cxx.o
                em++ ${emCompileFlags} ${emLinkFlags} cxx.o -o cxx.js
              }
              both
              rm -f $EM_CACHE/cache.lock
              EM_FROZEN_CACHE=1 both
            '';
            installPhase = ''
              rm -f $EM_CACHE/cache.lock
              cp -R $EM_CACHE $out
            '';
          };

          libuvFiles = [
            "fs-poll.c"
            "idna.c"
            "inet.c"
            "random.c"
            "strscpy.c"
            "strtok.c"
            "thread-common.c"
            "threadpool.c"
            "timer.c"
            "uv-common.c"
            "uv-data-getter-setters.c"
            "version.c"
            "unix/async.c"
            "unix/core.c"
            "unix/fs.c"
            "unix/getaddrinfo.c"
            "unix/getnameinfo.c"
            "unix/loop-watcher.c"
            "unix/loop.c"
            "unix/no-proctitle.c"
            "unix/pipe.c"
            "unix/poll.c"
            "unix/posix-hrtime.c"
            "unix/process.c"
            "unix/random-devurandom.c"
            "unix/random-getentropy.c"
            "unix/signal.c"
            "unix/stream.c"
            "unix/tcp.c"
            "unix/thread.c"
            "unix/tty.c"
            "unix/udp.c"
          ];

          # The Lean runtime (`libleanrt.a`: leanC's sources with nix/lean-wasm/patches), the POSIX subset
          # of libuv its io.cpp needs (`libuv.a`), Init and Std (`libInit.a`, `libStd.a`: leanC's stage-1
          # C) as wasm64 archives, and the headers Lean's C compiles against (`include/`).
          leanWasm = pkgs.stdenvNoCC.mkDerivation {
            name = "lean-wasm-${versions.lean}";
            nativeBuildInputs = [
              pkgs.emscripten
              node
            ];
            dontUnpack = true;
            doCheck = true;
            dontFixup = true;
            buildPhase = ''
              export HOME=$TMPDIR EM_CACHE=${emCache} EM_FROZEN_CACHE=1
              cp -R ${leanC.c}/src ${leanC.c}/include .
              cp -R ${pkgs.libuv.src} uv
              chmod -R u+w src include uv
              for p in ${./nix/lean-wasm/patches}/*.patch; do patch -p1 -s < $p; done
              # no mimalloc in the wasm runtime
              grep -q '^#define LEAN_MIMALLOC$' include/lean/config.h
              sed -i '/^#define LEAN_MIMALLOC$/d' include/lean/config.h
              cp ${./nix/lean-wasm/shim_uv.c} uv/src/shim_uv.c
              # compile DIR ROOT CC FLAGS... < SOURCES: each ROOT-relative source to
              # DIR/<path, / as .>.o; prints only a failure.
              compile() {
                mkdir -p $1
                DIR=$1 ROOT=$2 CMD="''${*:3}" xargs -P $NIX_BUILD_CORES -n 1 sh -c '
                  o=$DIR/$(printf %s "$1" | sed -e "s/\.[a-z]*$//" -e "s|/|.|g").o
                  $CMD -c "$ROOT/$1" -o "$o" > "$o.log" 2>&1 || { cat "$o.log"; exit 255; }
                  rm "$o.log"' sh
              }
              mkdir lib
              sed -n '/^  RUNTIME_OBJS$/,/^)$/s/^  \(.*\.cpp\)$/\1/p' src/runtime/CMakeLists.txt > rt.list
              test "$(wc -l < rt.list)" -ge 30
              compile obj/rt src/runtime em++ -std=c++20 -O3 -DNDEBUG -DLEAN_EMSCRIPTEN ${emCompileFlags} \
                -Iinclude -Isrc -Iuv/include -Wno-deprecated < rt.list
              printf '%s\n' ${lib.concatStringsSep " " libuvFiles} shim_uv.c > uv.list
              compile obj/uv uv/src emcc ${emCompileFlags} -DNDEBUG -D_GNU_SOURCE -Iuv/include -Iuv/src < uv.list
              for m in Init Std; do
                (cd ${leanC.c}/c && find $m -name '*.c' && echo $m.c) > $m.list
                compile obj/$m ${leanC.c}/c emcc ${emCompileFlags} -DNDEBUG -Iinclude < $m.list
              done
              for a in rt:leanrt uv:uv Init:Init Std:Std; do
                emar rcs lib/lib''${a#*:}.a obj/''${a%:*}/*.o
              done
            '';
            checkPhase = ''
              nm=$(em-config LLVM_ROOT)/llvm-nm
              $nm --defined-only -g lib/libleanrt.a | grep ' T lean_initialize_runtime_module$' > /dev/null
            '';
            installPhase = ''
              mkdir -p $out
              cp -R lib include $out/
            '';
          };

          # nix/lean-wasm/smoke.c linked with leanWasm, warning-free and with no undefined symbol, and run
          # in node (`nix flake check`).
          leanWasmSmoke = pkgs.stdenvNoCC.mkDerivation {
            name = "lean-wasm-smoke";
            nativeBuildInputs = [
              pkgs.emscripten
              node
            ];
            dontUnpack = true;
            buildPhase = ''
              export HOME=$TMPDIR EM_CACHE=${emCache} EM_FROZEN_CACHE=1
              l=${leanWasm}/lib
              emcc ${emCompileFlags} -I${leanWasm}/include -c ${./nix/lean-wasm/smoke.c} -o smoke.o
              em++ ${emCompileFlags} ${emLinkFlags} ${emStackFlags} smoke.o $l/libleanrt.a $l/libuv.a $l/libInit.a $l/libStd.a \
                -o smoke.js > link.log 2>&1 || { cat link.log; exit 1; }
              if test -s link.log; then cat link.log; exit 1; fi
              node smoke.js
            '';
            installPhase = "touch $out";
          };

          # The browsers of the debugger's browser tests (scripts/dbg_browser_test.py), in the wasm shell:
          # `chrome` and `firefox`, each a script that runs the app's own executable (a link would not do:
          # the apps find their frameworks beside it). Darwin: the prebuilt downloads, the only unfree
          # packages allowed; Linux: chromium (its shared memory kept out of /dev/shm) and firefox, with a
          # font (Chrome aborts on a font fallback where a headless host has none).
          unfree = import nixpkgs {
            inherit system;
            config.allowUnfreePredicate =
              pkg:
              builtins.elem (lib.getName pkg) [
                "google-chrome"
                "firefox-bin-unwrapped"
              ];
          };
          browserFonts = pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; };
          browser =
            name: exe: flags:
            pkgs.writeShellScriptBin name (
              lib.optionalString pkgs.stdenv.hostPlatform.isLinux ''
                export FONTCONFIG_FILE="${browserFonts}"
              ''
              + ''
                exec "${exe}"${lib.concatMapStrings (f: " " + f) flags} "$@"
              ''
            );
          browsers =
            if pkgs.stdenv.hostPlatform.isDarwin then
              [
                (browser "chrome" "${unfree.google-chrome}/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" [ ])
                (browser "firefox" "${unfree.firefox-bin-unwrapped}/Applications/Firefox.app/Contents/MacOS/firefox" [ ])
              ]
            else
              [
                (browser "chrome" "${pkgs.chromium}/bin/chromium" [ "--disable-dev-shm-usage" ])
                (browser "firefox" "${pkgs.firefox}/bin/firefox" [ ])
              ];

          common = [
            lean
            pkgs.cargo
            pkgs.rustc
            pkgs.rustfmt
            pkgs.clippy
            pkgs.rust-analyzer
            python
            pkgs.ruff
            node
            pkgs.git
          ];
        in
        {
          packages = { inherit leanWasm ucd; };
          checks.lean-wasm = leanWasmSmoke;
          devShells.default = pkgs.mkShell {
            packages = common;
            UNICODE_UCD = "${ucd}";
          };
          devShells.wasm = pkgs.mkShell {
            packages = common ++ [ pkgs.emscripten ] ++ browsers;
            UNICODE_UCD = "${ucd}";
            # scripts/build_wasm.py reads these: leanWasm's lib/ and include/, and emcc's frozen cache.
            ECMA_WASM = "${leanWasm}";
            # Lean's C and runtime sources (leanC, built from source): named here so that the profile keeps
            # them through a garbage collection, and a change to nix/lean-wasm does not rebuild Lean.
            ECMA_LEAN_C = "${leanC.c}";
            EM_CACHE = "${emCache}";
            EM_FROZEN_CACHE = "1";
          };
        };
      all = nixpkgs.lib.genAttrs systems perSystem;
    in
    {
      packages = nixpkgs.lib.mapAttrs (_: s: s.packages) all;
      checks = nixpkgs.lib.mapAttrs (_: s: s.checks) all;
      devShells = nixpkgs.lib.mapAttrs (_: s: s.devShells) all;
    };
}
