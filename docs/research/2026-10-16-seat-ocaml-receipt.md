# 2026-10-16 seat OCaml receipt: native hosts on the engine, where the time goes, and Rocq

**The one thing to know before merging:** the commit changes hand OCaml only: no generated file,
no Lean source and no recipe moved. Every OCaml lane passes on it. Each proposal that needs Lean
is written out below for the coordinator, and none is applied.

The research note is `docs/research/2026-10-16-ocaml-interop/README.md`.

## Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/ocaml-interop`, cut from the local `refactor/phase1-phase3` |
| Base | `81f9a4354` |
| Head of the code and the note | `b2f5cf07e` |
| This receipt | the commit after `b2f5cf07e` |
| Pushed | no |

## Changed files

| File | Change |
| --- | --- |
| `ocaml/engine/e4_host.ml`, `ocaml/engine/e4_host.mli` | the stops `Raised` (H5) and `Outside_profile` (H6); `stop_name`; the table read into an array once (H7) |
| `ocaml/engine/test/todo/native_todo.ml` | new: the module type `REPO`, its adapter `host`, `provider`, `catching`, and the hosts `Untyped`, `record`, `broken`, `Core` and `Table` |
| `ocaml/engine/test/todo/todo_core.ml` | new: the to-do repository as a pure module with no dependency, read by the Rocq example |
| `ocaml/engine/test/todo/todo_fixture.ml` | new: the fixture reader, moved out of `test_todo.ml` unchanged |
| `ocaml/engine/test/todo/test_todo.ml` | the hand hosts moved to `native_todo.ml`; T14 to T17 added; T8 matches its stop |
| `ocaml/engine/test/todo/bench_todo.ml` | new: the cost of a host call by host and by stage, an executable, not a test |
| `ocaml/engine/test/todo/dune` | the private library `todo_lane`, so the test and the bench compile `todo_gen.ml` once |
| `ocaml/eff/eff_frame.ml` | `emit_be64` in one 64-bit write; `emit_nat` writes its digits in place (F6) |
| `ocaml/eff/eff_val.ml` | `string_of_codes` in one pass (V4) |
| `ocaml/eff/test/test_frame.ml` | check group B: the new writers against the per-byte rule |
| `ocaml/engine/test/prop_fibers_view.ml` | FV6 compares values and renders only a failure |
| `ocaml/README.md` | the to-do lane's row of the map |
| `docs/research/2026-10-16-ocaml-interop/` | the note, `measurements.log`, `dune_trace.py`, `framebench/`, `rocq/` |

## Commands and results

Each dune command ran from `ocaml/`, through `opam exec --switch=effect4 --`.

| Command | Result |
| --- | --- |
| `dune build` | exit 0 |
| `E4_LEAN_CORPUS=/Users/pooks/Dev/lean4-effect4/.lake/corpus dune test --force eff gen clock engine` | exit 0, no line `FAIL`; the to-do lane 199 checks and 0 failures |
| `dune test --force eff` with `emit_be64` unmasked (a mutant, then restored) | check B fails: `FAIL B emit_be64 is the per-byte rule on 3956 ints` |
| `dune exec engine/test/todo/bench_todo.exe` | `measurements.log` §6 and §7 |
| `ocamlfind ocamlopt -package unix old_frame.ml landed_frame.ml pool_frame.ml bench.ml -o bench && ./bench` | `framebench/bench.log`: landed 1.62 to 1.79 times, pool 1.93 to 2.17 times |
| `opam switch create rocq ocaml-base-compiler.5.4.1 --no-switch -y -j 3` | exit 0, 17:31:59 to 17:37:07 |
| `opam pin add -n -y --switch=rocq rocq-of-ocaml git+https://github.com/formal-land/rocq-of-ocaml.git` | pinned at `1ac69a72ea1b09e22f14608032ee7ff4bfeea7d3` |
| `opam install --switch=rocq -y -j 3 rocq-of-ocaml` | exit 0, 17:37:45 to 17:48:17; Rocq 9.0.1 |
| `du -sh ~/.opam/rocq` | 1.0 GiB |
| the commands of `rocq/check.log` | each exit 0; every theorem `Closed under the global context` |
| the mutant of `rocq/mutant.log` | `insert_id` fails, exit 1 |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-ocaml-interop/README.md` | PASS, no finding |

Not run, by the brief: `lake build`, `make gen-lcnf`, `make check-*`, `make batteries-touched`.
Not run: `ocaml/engine/tools/gen-check.sh`. Its inputs are `api_engine.ml`, the prelude and
`gen/`, and none of them changed.

## Axiom output

No Lean declaration changed. The Rocq theorems print `Closed under the global context`.

## Evidence

| Claim | Evidence |
| --- | --- |
| A native host behind `REPO`, pure or imperative, gives Lean's result on the engine | tested, T14, finite over the fixture's seven requests and both instances |
| A raise is no answer, and leaves the engine as a decline does | tested, T15 and T16; H5 by construction |
| A raise named by `catching` crosses as the typed failure, as `Typed.broken` | tested, T16 |
| An out-of-profile answer is never applied | tested, T17; H6 by construction |
| The new writers write the old bytes | tested, check B on 3,956 ints; the goldens and 6,345 wire round trips of the eff battery |
| The landed writer is 1.6 to 1.8 times faster | tested, one machine under load, `framebench/bench.log` |
| `prop_fibers_view` costs 19.4 s of CPU at base and 4.7 s at head | tested, `measurements.log` §4 and §5 |
| `todo_core.ml`'s C1 to C4 | proved in Rocq 9.0.1, of rocq-of-ocaml's translation; the translator is assumed |

## Landed theorems and their placement

No Lean theorem landed. The Rocq theorems live in the research folder and join no gate.

## Open obligations

1. The coordinator runs `make check-ocaml` and merges.
2. The proposed decisions row below asks the owner for the exception default.
3. The switch `rocq` stays installed for the coordinator's review. Run
   `opam switch remove rocq -y` to free its 1.0 GiB. Disk had 9.6 GiB free after the install.

## The Lean-side changes the proposals need

Each item is for the coordinator. None is applied, and each is optional.

1. **A generated `.mli`.** In `OCaml5.Lcnf.Gen` (`src/OCaml5/Lcnf/Gen.lean`), write
   `<out>.mli` beside each artifact. List the type group as declared, and one `val` per root.
   Add `[@@@warning "-32"]` to the `.ml`'s header line. The to-do lane names functions that are no
   roots today, so the to-do artifact of `ocaml/gen/roots.json` gains these roots:
   `Test.Dogfood.Scenario.Todo.repository`, `Test.Dogfood.Scenario.Todo.forgetful`,
   `Test.Dogfood.Scenario.Todo.Host.resultVal` and `Test.Dogfood.Scenario.Todo.Typed.Host.reactor`.
   The bench also uses `Effect4.Store.Image.equiv`, `Effect4.Store.Image.list` and the three
   staged names of `Typed.Todo`. The `Makefile`'s outputs of `gen-lcnf` and `docs/GENERATED.md`
   then list the `.mli` files.
2. **One machine lowered by LCNF for every lane.** Give `OCaml5.Lcnf.Gen` a linked artifact.
   A declaration whose name and `declHash` appear in that artifact's closure file is referenced
   there, not lowered again. The machine's type group needs the same treatment as `--open Eff_types`.
3. **`REPO` from a typed host.** After P0.4 adds module types to `OCaml5.Ml`, emit a module type
   and the adapter for each structure that `ClockFlow.isHostRecordType` reads as a host record.
   Add one root per method's image, for example a Lean `Typed.todoImage := Modeled.image Todo`.
4. **A record's name frame built once.** In `Image.record`
   (`src/Effect4/Store/Carrier/Image/Record.lean`), bind `R.names.map .str` once outside
   `toVal` and `ofVal`. The lemmas `ofVal_toVal` and `ofVal_exact` then unfold the binding. Low
   priority: a derived to-do costs 0.03 µs to write.

## Proposed decisions rows (proposals only)

1. **A native host's exception.** The exception is no answer: the call stays outstanding, a live
   frontier, and the driver reports `Raised`. A host that means a failure answers it, or names the
   exception through `catching`. Effect's own default differs: `Effect.try` without `catch`
   fails with `Cause.UnknownError`, and a throw in `Effect.sync` is a defect.
2. **Rocq.** Rocq is not adopted in the estate. A handler whose laws matter is written in Lean and
   lowered (row 405). An optional rocq-of-ocaml check may cover a pure OCaml-only handler, in a
   research folder with its own switch. Iris waits for a consumer of the concurrent host code.
