# The coordinator's notes on Gemini's review of the LCNF lowering cleanup

Status: review notes (history, not authority). The review is `gemini-review.md` beside this note
(`d16f9c50d`, base `93d12486f`). The coordinator checked each concrete claim against the tree at
`d16f9c50d` with `ls`, `grep` and reading.

## 1. The one thing to know first

Seven findings hold, and the brief takes them in (§2). Most of the review's concrete paths and
names do not exist, despite its stated self-audit (§3). The brief's slices and order stand.

## 2. The findings that hold, and where the brief takes them

| Finding | Evidence | The brief's edit |
| --- | --- | --- |
| The byte entries cannot live in `src/Effect4/Run/Live.lean`. `src/Effect4/Api/RunnerBytes.lean` imports `Effect4.Api.RunnerDerived`, which imports `Effect4.Run`, which imports `Effect4.Run.Live` | `grep '^import'` of the three modules | LC-7: the entries go in a module above both |
| The generated codec group `Runner` (`tools/Effect4Gen/manifest.json`) ends at `Effect4.Run.Observation`. It holds no event, verdict or view | the group's 20 types, read by a script | LC-7: extend the group, then `python3 scripts/generate.py --only derived` |
| The CAS library depends on the engine. `ocaml/engine/cas/e4_checkpoint.ml` and its `.mli` name `E4_engine` | `ocaml/engine/cas/dune`; `grep -l E4_engine` | LC-3, LC-7: the checkpoint follows the engine's shape |
| `e4_be`, `e4_hex`, `e4_nat` and `e4_sha256` name no other engine module | `grep -o 'E4_[a-z_]*'` per file | LC-3: they move to a byte library below the CAS |
| `scripts/generate.py` starts one `lean --run src/OCaml5/Tools/LcnfGen.lean` per artifact, so each import of the environment is paid again | `scripts/generate.py` | LC-4: a candidate, one process for every artifact |
| Mapping `Char` to an `int` code point reaches the OCaml syntax: `Ml.Syntax` has a `char` type and a `char` pattern | `src/OCaml5/Ml/Syntax.lean` | LC-1: the row change carries the syntax's char forms |
| The C face needs its refusal frame and its handle ownership stated before code | design | LC-9: a status byte before each payload; the `Live` handle's reference counts; runtime initialization once |

The dead-model tests are confirmed by name: `test_due.ml`, `test_wake.ml`, `test_whatwg.ml` (it
calls `E4_wake`), `test_timers.ml`, `prop_store.ml`, `prop_fibers.ml` and `bench_timers.ml`.

The review's data-structure sketch is input to LC-8's design note, as candidates only:
- a trie over `Nat` for dense and sparse keyed tables;
- a pairing heap for the timers and the run queue;
- a two-list queue for the worklists.

Its file paths for the machine are wrong (§3).

## 3. The claims that do not hold

| Claim | What the tree has |
| --- | --- |
| A library `effect4_driver` in `ocaml/driver` | no such directory |
| `src/OCaml5/Ml/Print.lean`, `Ml/Runtime.lean`, `Lcnf/Closure.lean`, `Tools/Conform/Main.lean`, `Tools/Conform/SketchMain.lean`, `Test/OCaml5/Compiler.lean`, `Test/OCaml5/Effects.lean` | none exists |
| `ocaml/eff/e4_wire.ml` and a type `E4_eff.eff` | the files are `ocaml/eff/eff_*.ml` (`eff_wire.ml`, `eff_types.ml`) |
| The machine's modules `Machine/State.lean`, `Machine/Schedule.lean`, `Machine/Step/{Common,Wait,Async,Lifecycle,Pool}.lean` | none exists; `src/Effect4/Machine/` holds `Stores.lean`, `Fibers.lean`, `Wake.lean`, `Timer.lean` and others |
| The test table of §5: `ocaml/gen/test/` with ten files, and `test_nat`, `test_sha256`, `test_S0`, `test_program`, `test_step`, `test_differential`, `test_mutations`, `test_perf_gate` and others | `ocaml/gen/test/` does not exist, and those names are absent. The real tests include `test_diff`, `test_engine`, `test_host`, `test_sched`, `test_replay_steps` and the `prop_*` files |
| The prelude has 1,073 lines and twelve stateful modules | `ocaml/engine/tools/api_engine_prelude.ml` has 438 lines and no `module` declaration |
| `LcnfGen` translates twice on a `qualifyTypes` retry | no `qualifyTypes` exists under `src/OCaml5/` |
| The loop `for _ in [:16]` in `src/OCaml5/Lcnf/Translate.lean` runs past its fixed point | it breaks when no name is wanted and none clashes |
| Probe E lowered 860 declarations with four `ocamlc` errors | probe E stopped at the refusal of `Session`'s value parameter (`probes/session-lowering.log` of the collation) |
| F3 is default field calls, and F4 is rank-2 record fields | in `docs/research/2026-10-03-session-from-lean.md`, F3 is the generated algebras' type-family parameter, and F4 is the missing carrier rows |
| `apps/todo/Check.lean` holds `tsRecords`, ten contract checks and refusal cases such as `badTag` | none of these names occurs there |

## 4. For the next round with Gemini

Its self-audit fixed slice names and counts, but it checked neither file existence nor test names.
A next prompt asks it to run `ls` on every path it cites before it writes.
