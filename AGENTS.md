# Working in this repository

- Every tool comes from the flake's dev shell; run commands in a profile of it, never a plain
  `nix develop` and never a tool from outside it:
  `nix develop ~/.local/state/ecma-formal/devshell -c <command>` (the wasm build:
  `~/.local/state/ecma-formal/devshell-wasm`, made from `.#wasm`). A missing tool is added to
  `flake.nix`, then the profile is made again (README.md).
- Lean builds with Lake (`lake build`, `lake build <exe>`), Rust with Cargo.
- Every `Gen/` directory under `lean/` is generated (`lean/Ecma/Gen` and `lean/Ecma/Grammar/Gen`:
  `scripts/generate.py` via `crates/spectec` from `spec/spectec/` and `spec/ids/`; `lean/Unicode/Gen`:
  `scripts/unicode_*.py`; `lean/Ecma/Unicode/Gen`: `scripts/ecma_unicode_properties.py`): regenerate
  (README.md), do not edit.
- Four libraries: `Unicode`, `Ecma` (the specification, no concrete model), `Engine` (the one concrete
  model), `Debugger`. `Ecma` imports nothing from `Engine` or `Debugger`.
