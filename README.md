# ecma-formal

ECMA-262 formalized in Lean: the specification as data with an abstract model and its laws, one
concrete model of it, and a debugger that steps through the specification's algorithms as a
JavaScript program runs.

## Layout

Four Lean libraries under `lean/`, each depending only on those above it:

| Library | What |
|---|---|
| `Unicode` | the Unicode Character Database's tables (`Unicode/Gen`) and operations (case, normalization) |
| `Ecma` | the specification: no concrete model |
| `Engine` | one concrete model of the specification, with its parser, host and command line |
| `Debugger` | the spec-step debugger over the engine |

Outside them, `lean/SpecPrint.lean` is `ecma-print`: it imports only `Ecma`, and prints the specification's data
back as its text (`scripts/bijection.py` compares it with spec.html and the overlay).

Every generated file is in a `Gen/` directory and is never edited by hand. `Ecma` holds definitions and stated
laws only: no theorems, tactics, or `partial` or `unsafe` definitions (`scripts/quick_check.py` checks).

`Ecma`, the specification:

| Where | What |
|---|---|
| `Ecma/Grammar` | the grammar notation (§5.1.6) as data, its reading, and what it derives (`Derives`, `StrictCode`); `Grammar/Gen`: spec.html's grammars |
| `Ecma/Notation` | the algorithm notation (§5.2) as data: steps, expressions, conditions, tables, early-error rules, the realm table; `Print` prints it back as spec.html's text |
| `Ecma/Gen` | spec.html's algorithms, tables, early errors and realm in that notation, one module per clause |
| `Ecma/Model.lean`, `Ecma/Model` | the abstract model: a carrier and operations for each sort of the specification, and the laws a model must satisfy |
| `Ecma/State.lean` | values, the store, the state, and a leaf operation's result |
| `Ecma/Prims`, `Ecma/Ops` | the notation's primitives; parsing, leaf operations, early errors, table lookups |
| `Ecma/Program.lean` | the program as lookups: algorithms, SDO rows, sorts, tables, early-error rules |
| `Ecma/Lower` | the program the machine runs: macros expanded, phrases as calls, choices made constructive, then written as linear code (`Lin`) |
| `Ecma/Machine` | the step machine, generic in the model: its code (`Code`), configurations (`Config`), one transition (`Step`), and what a run is (`Run`: `Step`, `Steps`, `Runs`) |
| `Ecma/Host.lean`, `Ecma/Host` | the host: what the specification leaves to it, its laws, and the strategies the laws are stated over |
| `Ecma/MemoryModel` | §29's relations and the validity of a candidate execution |
| `Ecma/Spec` | the whole program as data, the built-ins by name, the starting realm |
| `Ecma/Unicode` | ECMA-262's choice of Unicode properties (`Gen/Properties`) |

`Engine`, the concrete model:

| Where | What |
|---|---|
| `Engine/Model.lean`, `Engine/Model` | `Impl`, the model: exact mathematical values, binary64 Numbers, UTF-16 Strings, arrays for Lists and the store |
| `Engine/Parse` | the parser over the grammar data: a checked kernel, a memoized search, the lexer, automatic semicolon insertion |
| `Engine/Host` | the host: host-defined operations, jobs, agents, modules and bundles, test262's `$262` |
| `Engine/Accel` | shortcuts for particular algorithms, each with what it owes to the algorithm's steps |
| `Engine/Machine.lean`, `Engine/Machine`, `Engine/Run.lean` | the machine at `Impl`, its run loop and step records; a whole program from the starting realm |
| `Engine/Claims.lean` | what the engine claims of itself: its model and host meet the laws, its step is the specification's (proved: Engine/Proofs/Model.lean) |
| `Engine/Cli` | `ecma-run`, `ecma-bundle` |

Outside `lean/`:

| Where | What |
|---|---|
| `external/ecma262`, `external/test262` | the pinned specification and its tests (submodules) |
| `spec/formal` | the formal reading's overlay (`*.emu`) and its reviewed records |
| `crates/spec-gen`, `crates/jsgrammar` | the generators of `lean/Ecma/Gen` and `lean/Ecma/Grammar/Gen` from spec.html |
| `crates/test262-runner` | test262 on `ecma-run` (`scripts/test262.py` drives it) |
| `scripts` | the generators' drivers, the wasm and site builds, tests |
| `tools/dbg` | the debugger's page, Worker host and UI |
| `site` | the landing pages |
| `nix/lean-wasm` | the Lean runtime's patches for wasm64 |

## Tools

Everything comes from the flake: Lean 4.35.0 (with Lake), Rust, Python, node; the `wasm` shell adds
emscripten and the Lean runtime as wasm64 archives. Make each profile once, and again after
`flake.nix` changes:

    nix develop --profile ~/.local/state/ecma-formal/devshell -c true
    nix develop .#wasm --profile ~/.local/state/ecma-formal/devshell-wasm -c true

Then run commands in a profile (`D=~/.local/state/ecma-formal/devshell`):

    nix develop $D -c python3 scripts/generate.py   # all gitignored Gen/ modules, build/ids, and formal reports
    nix develop $D -c lake build                    # ecma-dbg, ecma-run, ecma-bundle, ecma-print (.lake/build/bin)
    nix develop $D -c cargo test                    # the crates
    nix develop $D-wasm -c python3 scripts/build_site.py    # dist/: the site, with the debugger's Worker build

After cloning: `git submodule update --init --depth 1 external/ecma262 external/test262`.

## Generating

Every `Gen/` directory under `lean/` and the derived formal report files are gitignored and generated in one step:

    nix develop $D -c python3 scripts/generate.py

Under the hood this runs (skipping unchanged outputs so `lake build` stays incremental):

    nix develop $D -c cargo build --release
    nix develop $D -c python3 scripts/unicode_properties.py
    nix develop $D -c python3 scripts/unicode_data.py
    nix develop $D -c python3 scripts/ecma_unicode_properties.py
    nix develop $D -c python3 scripts/jsgrammar.py --write --gen target/release/jsgrammar --ids build/ids \
        --readings spec/formal/readings.emu --readings spec/formal/syntax.emu --json spec/formal/json.emu
    nix develop $D -c python3 scripts/gen_spec.py --write --gen target/release/spec-gen --ids build/ids

Both generators, the quick check, the laws' quotations and the site read *the text* (`scripts/spec_text.py`):
ECMA-262 as pinned, with the proposals `spec/proposals.txt` names applied in order by `scripts/apply_proposal.py`,
each with its answers file under `spec/proposals/`. With no proposal named it is `external/ecma262` itself; with one,
it is made into `build/text/` (git-ignored) whenever its inputs change, and `spec_text.py --report` says what each
merge did. `--spec` still reads another.

The ids the data numbers by name are kept in `spec/formal/*-ids.txt`: the phrase, primitive, sort, field and enum
ids, the clause (`ClauseId`, an `AlgId`'s first component), SDO, concrete-method, erratum, residue and table ids
(`gen_spec.py --write` writes these), and the production (`ProdId`, keyed `GRAMMAR MASK Lhs : rhs`), nonterminal
(`NtId`, `NT`'s constructor index) and parameter ids (`jsgrammar.py --write` writes these; spec-gen reads them). The
generators give each name met its number there and a new one the next unused number, and write the files back; a
name the text no longer has keeps its number (`retired`: a nonterminal or parameter keeps its constructor, as
`retired_Name`; a table's entry is `Table.retired`), and a clause whose `oldids` names an entry takes its number
(`was`). An edited right-hand side is a new production. So a change to spec.html renumbers nothing it does not
change, and the generated docstrings cite clauses, not spec.html's lines. Not kept, on purpose: the realm's object
numbers (allocation order, which outputs print as `#N`), the index within a clause of an algorithm, row or table,
the written production index (`Production`'s constructors), and the blocks' lines (`Gen.blockNNNN`, `Block.line`),
which only the index modules hold.

## The bijection

    nix develop $D -c python3 scripts/bijection.py [--json FILE]

runs `ecma-print` (`lean/SpecPrint.lean`), which prints every value of `lean/Ecma/Gen` and `lean/Ecma/Grammar/Gen`
that holds the specification's text, and finds each item again in the text and in `spec/formal` by the markup alone
(an algorithm as the `idx`th `emu-alg` of its clause, a reading by the SHA-256 of the step it reads), independently
of the generators. Every algorithm step, SDO equation, early-error rule, table and grammar production of spec.html
is a Lean value that prints back to its text, byte for byte, each exactly once, and so is each SDO row's grammar key,
which the data holds verbatim; every other such value prints back to one element of the overlay, each exactly once,
and every element of the overlay is printed or in a class that is not data, which the check names with its reason
(the notes, the host laws' dispositions, the permanent Asserts, the type check's fields and guards, the prose).
Headers, prose, notes, examples and the realm table are outside it: the check prints the characters of spec.html in
each class, and `--json FILE` writes them with the counts. A difference fails with what differs, where, and the two
lines. The other half, that the data is what the generators make of the text, is `gen_spec.py --roundtrip --gen
target/release/spec-gen --overlay spec/formal` (every step prints back from its parse and from its data, the data
regenerates byte for byte, the residue, Asserts, errata and type findings are their records) and `jsgrammar.py
--check-regen`. The quick check runs both halves' fast parts.

## Tests

    python3 scripts/quick_check.py

runs `tests/quick/*.js` on `ecma-run`, each within 5 s and 1 GiB, and compares its result and the steps it
entered with `tests/quick/*.expected` (`--update` rewrites them), then checks that `lean/Ecma` is plain, that the
kept ids number what the data has, that regenerating writes the data as it is and `spec-gen roundtrip` passes (with
the generators built and current), the bijection (`scripts/bijection.py`: it fails if `ecma-print` is not built),
the laws' quotations, and last runs the cases of `tests/run` that use the driver's options (a `// module:` or
`// args:` header) against their own expectations (about 55 s in all). Run it after every change; with `--all-run-tests` it runs all of
`tests/run` (about a minute more), which is due before a commit that changes the engine, the host or a case:

    nix develop $D -c python3 scripts/js_run_test.py --run .lake/build/bin/ecma-run --jobs 3

runs every `tests/run/*.js` and checks what it prints against its `// expect:` and `// print:` headers
(`scripts/js_run_test.py`'s docstring has the headers). A case with a `// needs: X` header asks for what the
driver lacks: it is reported as `not run: needs X` and counted apart, never as a pass (`--case NAME` runs it
anyway).

    nix develop $D -c python3 scripts/dbg_transcripts_test.py --node node \
        --dbg .lake/build/bin/ecma-dbg --run .lake/build/bin/ecma-run

runs the debugger's transcripts (`tests/dbg`) and checks that stepping pauses at exactly the steps
`JS_TRACE_STEPS=1 ecma-run` prints. The other `scripts/*_test.py` take their inputs as arguments and
have no runner here yet.

## The site

The pages that need no build (the reading pages generated from `lean/Ecma` by `scripts/render_lean.py`, the
pages of `site/`, the test262 page from a run's record by `scripts/test262_report.py`, and the errata page from
the overlay and its programs' runs by `scripts/errata_page.py`):

    nix develop $D -c python3 scripts/site_pages.py --out DIR \
        [--test262-record tests/test262/results/suite.tsv] [--errata-runs build/errata-runs.json]
    nix develop $D -c python3 scripts/site_pages.py --check DIR

The build checks what it writes: every law laid out with its quoted sentence, every clause id an element of
spec.html, every internal link and anchor resolved, nothing loaded from another origin.

The whole site, with the debugger as one of its tabs (its WebAssembly build, the build selector and the examples
page), from the Lean build's products already in `.lake/build` (it runs no Lean build and stops if they are
missing or older than their sources):

    nix develop $D-wasm -c python3 scripts/build_site.py                  # dist/
    nix develop $D -c python3 tools/dbg/serve.py --page index.html dist   # serve it, cross-origin isolated

A test262 run is recorded for the site, without its times, by `scripts/test262_report.py record --results
TSV --engine COMMIT --command 'CMD'` (into `tests/test262/results/<stage>.tsv`; with `--rerun TSV --rerun-command 'CMD'
--rerun-max-heap MB`, a second pass over the tests the first did not pass, both results kept); `build_site.py` makes the
test262 page from `tests/test262/results/suite.tsv` when it is there. Every program the errata page states an
outcome of is run on native `ecma-run` when the site is built (`scripts/errata_page.py run`). The page on applying a proposal is made from `site/proposal-defer-import-eval.json`, which
`scripts/proposal_record.py record --tree PATH --test262 TSV` writes from the proposal's branch and its working tree.

Every example of `tools/dbg/gallery.json` is run on the native debugger and on the wasm in node, under each
build it names, before it is listed. `--build NAME=PATH[,ARG...]` adds a debugger build made elsewhere (a
proposal's). The wasm shell has `chrome` and `firefox` for `scripts/dbg_browser_test.py`; the debugger needs
64-bit WebAssembly memory (Chrome or Edge 133, Firefox 134; not Safari), and says so where it is missing.

The spec-issue write-ups (`docs/spec-issues/NN-*.md`) are pages of the site, under `spec-issues/`
(`scripts/spec_issue_pages.py`), each block quotation of the text checked against the pinned spec.html when the
site is built (`python3 scripts/spec_issues.py check` does that check alone); their examples are in the debugger's
menu, each run on native `ecma-dbg` and on the WebAssembly build in node at build time.

### Publishing

The site is published to GitHub Pages on the `gh-pages` branch (`scripts/deploy_site.sh`): `.nojekyll` serves
`dist/` as it is, `coi-serviceworker.js` gives `/debugger/` the cross-origin isolation its Worker needs on a
static host, and an address with no page is answered with `dist/404.html` (`--base-path`, `/ecma-formal/` by
default). From a tree with everything committed:

    nix develop $D-wasm -c python3 scripts/build_site.py [--build defer=PATH]   # dist/
    scripts/deploy_site.sh [origin]                                             # dist/ to gh-pages

`scripts/deploy_site.sh` writes `dist/` as a single root commit with `dist/VERSION`'s line as its message and
force-pushes it to `gh-pages`; it refuses a `dist/` without `VERSION`, one built from a tree with uncommitted
changes, and one built with `--stale-ok`. In GitHub's repository settings (Settings → Pages), set Source to
"Deploy from a branch" and select `gh-pages` / `/ (root)`.
