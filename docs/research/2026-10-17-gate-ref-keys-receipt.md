# 2026-10-17 receipt: gate keys that stop at what a lane reads

Status: receipt (history, not authority). Base `22a46c6aa`, branch `refactor/phase1-phase3`.
Committed in `b27739d24`. `make check-full` passed at `3bc40ea3e`, with slice A's guard: 424 s, every
lane green (obligation 1).

**The one thing to know first.** The `Makefile` is an input of every lane's key, so this change reruns
every lane once. That rerun was taken once, with slice A's emission guard
(`docs/research/2026-10-17-proof-scout/README.md`, §7.0): `make check-full` passed at `3bc40ea3e`.

## Question

A lane's key hashes the source text of its whole Lean import closure (`scripts/gate-cache.py key
--lean`). Four lanes reached the `Effect4` root file `src/Effect4.lean`, and through it all 288 core
sources. Adding a module to the root therefore reran them, although nothing they compare changed. The
goal: a lane reruns only when something it reads changes, and no comparison is narrowed.

## What was measured before the change

| Lane | Root in the key | Core files in the key | How the root entered |
| --- | --- | --- | --- |
| truth | yes | 288 | `Test.Program.BoundsControls` imports `Effect4`, and `harness/truth/Truth.lean` imports it |
| corpus | yes | 288 | the same entry, `harness/truth/Truth.lean` |
| compiler | yes | 288 | `Conform.Effect4.LcnfMl` and `Conform.Effect4.LcnfSemantics` import `Effect4` |
| ocaml | yes | 288 | the rule lists `$(CORE_SOURCES)`, for one `grep` in `ocaml/engine/tools/gen-check.sh` (check C1) |

The other 17 recorded lanes had no root in their keys (`.lake/check/*.inputs.json`).

## The change

| File | Change |
| --- | --- |
| `Test/Program/BoundsControls.lean` | drops `import Effect4`; it compiles without it |
| `tools/Conform/Effect4/LcnfMl.lean`, `LcnfSemantics.lean` | `import Effect4` becomes `Effect4.Program.Ty` and `Effect4.Machine.Key`, which define `Ty`, `Ty.render` and `ServiceKey` |
| `tools/Conform/Effect4/CompilerControls.lean` | imports `Effect4.Program.Native` for `NativeOp`; it had reached the root through `LcnfMl` |
| `tools/Conform/Effect4/Normalization.lean` | imports `Effect4.Store.Carrier.Digest` for `sha256`, by the same route |
| `ocaml/engine/tools/gen-check.sh` | check C1's scan is one function; `--c1-hits` prints its hits, sorted and relative to the repository |
| `Makefile` | a rule writes `.lake/check/fiber-writes` from `--c1-hits`, rewritten only when its bytes differ; the ocaml lane keys on that file and the build pins, not on `$(CORE_SOURCES)` |

The ocaml lane reads no other core source. Its tests read the printed corpus, the fixtures and the
generated `.ml` files, and each of those has its own key upstream. History confirms that
`$(CORE_SOURCES)` was there for the scan alone (`370300fba`, the comment above the rule).

## Results

| Lane | Root in the key | Core files in the key |
| --- | --- | --- |
| truth | no | 232 |
| corpus | no | 232 |
| compiler | no | 63 |
| ocaml | no | 0, plus the scan's hits |

Each probe changed the tree, prepared the four keys and reverted the tree. A key is prepared by the
lane's own `gate-cache.py key` command, taken from `make -n`; no lane ran.

| Probe | Expected | Observed |
| --- | --- | --- |
| a new no-op module, imported by `src/Effect4.lean` | the four keys stay | all four stay |
| `Typed.print`'s body in `src/Effect4/Api/Codegen.lean`, parenthesized | the truth and corpus keys change | both change; compiler and ocaml stay |
| a file under `src/Effect4/` holding `fibers := m.fibers.filter p` | the ocaml key changes | it changes |

The ocaml key stays at a `Codegen` edit, because the lane reads the core only through the LCNF group's
outputs. When `make gen-lcnf` writes a changed engine file, that file changes the ocaml key.

## Commands and results

| Command | Result |
| --- | --- |
| `lake env lean -DwarningAsError=true` on each edited file, with the root import removed or replaced, from a scratch copy | exit 0; 14 s, 9 s, 5 s |
| `LEAN_NUM_THREADS=3 lake build Test.Program.BoundsControls Conform.Effect4.LcnfMl Conform.Effect4.LcnfSemantics Conform.Effect4.CompilerControls Conform.Effect4.Normalization Test.Audit.LetReturn` | first runs failed at `NativeOp` and at `sha256`; after the two imports, exit 0, 884 jobs, 7 s |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true harness/truth/Truth.lean` | exit 0, 61 s |
| `opam exec --switch=effect4 -- bash ocaml/engine/tools/gen-check.sh` | `gen-check: PASS` |
| `bash ocaml/engine/tools/gen-check.sh --c1-hits` | exit 0, no hit |
| the three probes above | as tabled |

## Axiom output

`#axiom_audit Test.Program.BoundsControls`: 20 declarations within `[propext, Quot.sound]`, 0 of them
modulo planned goals; 0 planned goals.

Over the four `Conform` modules, 34 of 307 declarations reach `Classical.choice`. The paths run
through `String.splitOn` in renderers such as `LcnfMl.tyT`. The axiom gate audits `Effect4.*` and
`Test.*` only, and this change edits no declaration of those modules. That the paths predate it is a
reading, not a run at the base.

## Open obligations

1. Done: `make check-full` passed at `3bc40ea3e`, with slice A's guard. The truth, corpus and compiler
   lanes compared the same programs through the narrowed imports.
2. The `Makefile` is in every lane's key (`CHECK_CACHE_SOURCES`). Any edit to it reruns every lane.
   Keying each lane on its own expanded recipe (`make -n _run-<lane>`) would confine a Makefile edit
   to the lanes it changes.
3. A key hashes source text. A docstring or comment edit inside a lane's closure reruns the lane. Keys
   from the compiled declarations a lane references would remove that, at the price of a Lean pass
   before each key.
4. The producers `$(GEN)/eff`, `wire`, `cas`, `ts`, `host-protocol`, `truth` and `schema-ts` take
   whole-tree prerequisites by file time. They run under `make gen` and `check-gen`, not `check-full`.

## Evidence

The key behaviour is tested: three probes on named edits. The narrowed imports are tested by
compilation, the truth harness's entry file included. Their behaviour against the outside implementations
is not yet tested; that is obligation 1.
