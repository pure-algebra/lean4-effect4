The seat's central claim holds and is understated: under today's `StrongValue`, M5 `typedState_load`, the M6 capstone `typedState_reachable` and the per-command obligation `M6Ledger.step_loop` are each false as stated (kernel-proved, each matched to the ledger's own proposition) for programs that bind or return a fresh Ref or Deferred, while under the seat's `Fits` the M5 instance is true for both `Ref.make(5)` and `Ref.make(5).flatMap(r => Ref.get(r))`.

# Verification of seat MEMBERSHIP

Adversarial verifier, 2026-09-30 pass. Base `be15b062`. The checkout is at `48cd1de1`, which
changes nothing under `src/` or `Test/` (`git diff --stat be15b062 HEAD -- src Test` is empty).
I wrote only this file and six probes named `verify-*.lean` in this folder. I did not edit the
seat's files. I ran no git write, make, lake build or generator. Every Lean run went through
the lock (`serial.sh`).

Evidence words: **proved** means a kernel theorem at `[propext, Quot.sound]` or less;
**reproduced** means I reran the seat's probe and got the same output; **tested** means a
finite `#guard`; **reading** means I read code or text and nothing checks it.

## 1. Reruns of the seat's probes

| Probe | Exit | Compared with the seat's record |
| --- | --- | --- |
| `Fits.lean` | 0 | output byte-identical to `fits.log` (20 axiom lines, all `[propext, Quot.sound]` or none) |
| `Gaps.lean` | 0 | byte-identical to `gaps.log` (32 axiom lines; `pair_builds`, `fst_projects` at `[propext]`); the three `#guard`s pass |
| `Walk.lean` | 0 | byte-identical to `walk.log` (21 axiom lines) |
| `OldMono.lean` | 0 | byte-identical to `oldmono.log` (2 axiom lines) |
| `Inventory.lean` | 0 | byte-identical to `inventory.log` |
| `walk_baseline.py` + `diff -B` | 0, then diff 1 | my diff is byte-identical to `walk.diff`: baseline 882 non-blank lines, 58 removed, 20 added, 11 hunks |
| `prelude_check.py check Fits.lean Gaps.lean Walk.lean` | 0 | `c6f205c95f7f9cf7` three times |

So every number the seat reports from these runs is **reproduced**.

## 2. Verdicts, claim by claim

**The one thing** (`typedState_load` false at `Ref.make(5)`; `Fits` removes the obstruction;
the walk re-proves with 58 of 882 lines replaced by 20): **confirmed, and understated.**
`typedState_load_false` reproduces. My `typedState_load_refuted` (`verify-load.lean:161`)
refutes the obligation's whole proposition, and a meta check confirms that proposition is the
one the ledger reads from `M3bAssembly.typedState_load` (same `readGoal` rule, reducible
defeq), with a red control that refuses a mere instance. The obstruction is wider than the seat
says (section 3).

1. **`fits_hasTy`** (Fits implies the shape check, every reading, every `Ty`): **confirmed.**
   `Fits.lean:247`, reproduced. I compared `FitsInv`'s arms with `Val.hasTy`
   (`Program/Typed.lean:34-101`) one by one: same arms, same value shapes, with table checks
   added at the handle leaves, `Live` at `unknown` and at contexts (reading). `Ty` has 20
   constructors (`Program/Ty.lean:37-74`), all covered.
2. **The converse is false**: **confirmed.** `Gaps.lean:282`, `:287`, reproduced.
3. **Six value gaps G1–G6**: **confirmed.** 18 theorems reproduced. One wording note: each
   control keeps the value and changes the world (fiber 1 or cell 0 declared at the matching
   type), not the other way round. `HandlesFit`'s `.handle` arm types contexts only
   (`Typed/Admission.lean:57`), as G6 says.
4. **`Fits` closed under `Ty.sub`; `StrongValue` and `FitsEq` are not; the two are
   incomparable**: **confirmed.** `fits_sub` follows `Ty.sub`'s arms and uses the
   unconditional `Ty.sub_trans` (`Laws/Program/TypeAlgebra.lean:117`). The seat proves only one
   direction of "mutual subtypes" (`sub_ref_equiv`); I proved the other,
   `verify-sub.lean:20` `sub_ref_backward`, with a red control (`refOf nat` is not below
   `refOf bool`, `:24`). "Incomparable" rests on separations in two concrete worlds, both ways
   (`natCell_equiv_spelling`; G1–G6).
5. **`typedState_load` false at `Ref.make(5)`; under `Fits` the loaded code is typed at every
   world**: **confirmed and strengthened.** See section 3, items M1–M5. `loaded_root` shows only
   the root's code is `denoteR …`; I proved the code is literally the `refMake` step followed by
   returning the answer (`verify-load.lean:38`, `rfl`). `refProg_typedF` reproduces, and I
   re-proved it independently (`verify-fits.lean:936`).
6. **G8, generic cell (`refReturn_untypable`, `refReturn_fits`)**: **confirmed.** The program is a
   hand-written `RProgram`, not a checked source; the seat says so.
7. **Pair program: no `fst` step carries the declaration under `StrongValue`; for `Fits` the
   pair, `fst` and await steps M6 needs are proved**: **partly.** The separation
   (`strongValue_no_fst`) and the three value lemmas (`fits_pair`, `fits_fst`, `await_fits`) are
   proved and reproduce. That they are "the steps M6 needs" is a reading: no typed derivation
   of `pairProgram` was built, under either judgment.
8. **`pairProgram` checks at `nat`, runs to 7, pair type `prod (fiberOf nat never) unit`**:
   **confirmed** as finite evidence (three `#guard`s, tested; the rerun exits 0).
9. **Monotonicity**: **confirmed.** `fits_mono`, `fitsExit_mono` reproduce; `fitsExit_mono` is
   `fits_mono` at the exit type. The old obligations are true: I copied `OldMono.lean:19-113`
   and ran `#obligation_proved` against `M3bWorld.strongValue_mono` and `strongExit_mono`
   (`verify-oldmono.lean:125-128`). The ledger's own elaboration accepts both proofs, and a red
   control shows the exit proof is refused for the value obligation. So "unproved, not false"
   now holds against the ledger's exact propositions.
10. **`fits_live`, `live_iff_handlesLive`, `fitsEq_strongValue`**: **confirmed.** The `WorldValid`
    hypotheses are satisfiable (`initial_world_valid`), so nothing is vacuous.
11. **`fits_list_iff`**: **confirmed.** `Val.asList?` (`Machine/Alphabets.lean:239`) is the
    `.list` carrier or the snapshot read through `snapshot?`.
12. **`fold_of` accepts `FitsInv` and emits `FitsInv.eq_cata`**: **confirmed**, with two small
    gaps. The citation `Fits.lean:186` is wrong; `fold_of` is at `Fits.lean:226`. The seat never
    printed the connector's axioms; I did: `FitsInv.eq_cata` depends on `[propext, Quot.sound]`
    (`verify-fits.lean:1092-1094`).
13. **The slice-5 declarations restated over `Fits` all check; 58 of 882 lines replaced by 20,
    in 8 declarations**: **partly.** The diff is reproduced byte for byte. All 11 hunks change
    proof bodies only; every statement is renamed only. The walk theorems are proved. But the
    seven obligation namespaces "check" only as statements: `ProofGraph.Obligation P := ⟨⟩`
    elaborates for any well-typed `P`, so they carry no proof. The ledger lines
    (`#obligation_proved`, `#typed_state_obligations … ceiling`) were not carried over, so the
    "ceiling 3 to 1" change is a proposal, not a measurement.
14. **Three consumers re-proved; `fork_admitted` 11 lines to 1; the other two kept their
    length**: **partly.** All three are proved. `fork_admitted`'s value part did shrink from 11
    lines to 1. `lookup_typed` (16 to 14 non-blank lines) and `service_admitted` (17 to 15) each
    got two lines shorter. `service_admitted` now leans on a new 11-line helper,
    `fits_context_services` (`Walk.lean:1197`); `lookup_typed` reads its service through
    `flatFits_fitsInv` from the shared block.
15. **The `Effect4.TypedState` bank closes four goals; the heap-extension goal needs the bank**:
    **confirmed.** The `fail_if_success aesop` red control is in the file and the rerun exits 0.
    `search_fits_mono` closes only because `fitsInv_map` is handed to the call as a rule.
16. **Inventory counts** (39/16/38/56/21; migration set 150 = 90 src + 60 tests; 37 redefine,
    113 restate; 129 ValueOk-only; walk set 36): **confirmed** as a reading. The log
    reproduces, and my own tally of the log's sections gives the same per-module and per-role
    numbers. The 174 textual occurrences are whole-word counts (`grep -w`); a plain substring
    count gives 181, because of the file and binder names in `StrongExitDefect.lean` and one
    line of `Test/All.lean`.
17. **The estimate (about 1,000 lines; a mechanical cut-over; about 20 test edits; two or three
    slices)**: **unverified.** It is a forecast. `Fits.lean` is 1,239 lines; without the
    `FitsEq` parts and the search examples it is about 1,100. The placement it assumes has two
    layering faults (section 4).

## 3. What the seat missed

All items are **proved** unless marked. Theorems are in this folder.

- **M1. The M6 capstone is false as stated.** The empty tape reaches the loaded state
  (`replayEval`'s `[]` arm returns its machine; `replay_empty_ref`, `verify-load.lean:320`,
  `rfl`). So `M6Ledger.typedState_reachable` is false at `Ref.make(5)`
  (`typedState_reachable_refuted`, `:322`; meta-checked against the ledger proposition). So is
  every capstone that restricts the tape's decisions, whatever the restriction
  (`restricted_capstone_refuted`, `:334`). That includes the lift seat's repaired capstone over
  `RReachableNoAnswer` (`lift/Lift.lean:965-967`, reading). The lift seat's `m6_capstone` is a
  proved implication; for Ref programs its conclusion is false, so a premise must fail, and
  `typedState_load` does.
- **M2. A per-command M6 obligation is false.** `fork(Ref.make(5))` checks
  (`verify-step.lean:67`). After `evaluate root` its state is typed under `StrongValue`
  (`m1_typed`, `:151`; the root forks a body the checker admits and returns the handle,
  whose liveness the fiber table supplies). The next command, `loop root`, creates the child
  with the code "allocate, return" (`m2_child`, `:77`, `rfl`), and no typed state holds such a
  fiber. So `StepPreserves` fails for `.loop` (`loop_not_preserved`, `:190`), and the ledger's
  `M6Ledger.step_loop` proposition is false (`step_loop_refuted`, `:202`; meta-checked). The
  derivation "capstone from the 18 per-command obligations" therefore has a false premise under
  `StrongValue`. The lift folder holds another verifier's probe, `lift/verify-steppreserves.lean`,
  that reaches a conditional inconsistency by a different route (resumes queued for
  undeclared tokens); I read it and did not rerun it.
- **M3. The obstruction is not about returning a Ref.** `Ref.make(5).flatMap(r => Ref.get(r))`
  answers a number, and it refutes `typedState_load` too (`typedState_load_refuted_get`,
  `verify-load.lean:241`). The reason: `bind` wraps its first part in a guard
  (`Laws/Program/DenoteR.lean:604`), whose body `unguard`s the successful exit of the fresh
  cell; `TypedProg`'s `unguard` arm demands `StrongExit` of that payload
  (`Typed/Residual.lean:208-209`), hence heap-length liveness at the later world that declares
  the cell without growing the heap. The general lemmas hold at every world valid for any
  machine, whatever the heap holds, at every type: `refReturn_untypable_valid` (`:85`),
  `deferredReturn_untypable_valid` (`:101`), `refUnguard_untypable_valid` (`:208`), and
  `no_typedState_refReturn` (`:127`, any stack). The lemmas need a valid world (reading of
  why: at a world that is not valid, every key past the heap may already be declared at another
  type, and then the allocation's post admits only live keys). Reading: every checked program that binds or
  returns the result of `Ref.make` or `Deferred.make` has no typed state once that code is a
  fiber's current code, at load (M3, M4) or after a fork (M2); the guard shape is the same for
  every `bind`.
- **M4. The seat's open question about Deferreds is settled.** `Deferred.make()` checks at
  `Deferred.Deferred<number, number>` (`verify-load.lean:49`) and refutes `typedState_load`
  (`typedState_load_refuted_deferred`, `:172`).
- **M5. Green controls were missing.** Nobody in the tree had built the generated `RStateOk`
  for any state (a reading of a grep over `src/` and `Test/`: `Test/Program/TypedStack.lean:89-92`
  only states a `TypedState`, it does not build one). I built two.
  - Under `StrongValue`, `typedState_load` holds for `succeed(1)` (`typedState_load_one`,
    `verify-load.lean:268`). So the obligation is not false for every program; allocation is
    what separates the refuted instances.
  - Under the seat's `Fits`, the M5 instance itself holds, with the restated typed state, for
    `Ref.make(5)` and for the bind program (`typedStateF_load_ref`, `typedStateF_load_get`,
    `verify-fits.lean:1076`, `:1081`, through the generic `typedStateF_load`, `:1037`). The
    bind program's loaded code is typed at every world (`getProg_typedF`, `:955`): the guard
    picks `Ref.Ref<number>` as its middle type, the run arm reads the cell's declaration from
    the value's fit and reaches `nat` through `fits_sub`. This is stronger than the seat's
    `refProg_typedF`, which types only the code. The seat's definitions are copied verbatim by
    line range (`cmp` confirms each of the five ranges is byte-identical); no claim is made for
    every program.
- **M6. G6's cost, concretely.** At a checked point whose environment holds a cell declared
  `bool`, D13 admission `PointTyped` holds, because `StrongValue` at `Ref.Ref<number>` never
  reads the declaration; the point's loaded code has no `TypedProg` at the checker's type
  (`admitted_but_untypable`, `verify-g6.lean:71`). Red control: the same read is typed when the
  cell is declared `nat` (`read_typed_nat`, `:91`). So checker admission does not imply program
  typing under `StrongValue`, and M6 needs that implication whenever a step installs an admitted
  body (a fork, a scope). Whether a reachable typed state can carry this world is a reading:
  `TypedState` asks only `StrongValue` of environment values and heap cells, and both hold at
  `wBool`. This turns the seat's D2 reading into a theorem at the level of one point.
- **M7. The D3 alternative names the wrong post** (reading). `memoBuild`'s post answers a scope
  handle (`Typed/Residual.lean:80`), and `HandlesLive` puts no condition on scope handles
  (`Typed/Admission.lean:26`). The post that hands back a deferred is `memoGet`'s hit
  (`:78-79`); if the alternative is chosen, that is where a length fact may be needed. Not
  probed.

## 4. Corrections to the proposals

- **Proposal 1 places `fold_of` where it would make an import cycle.** `Laws/Program/Folds/Ty.lean`
  is already below the typed world: `Typed/World` imports `Laws.Program.Typed`, which imports
  `TypeAlgebra`, then `Admits`, then `TyView`, then `Folds/Ty` (traced from the `import` lines;
  reading). A `fold_of Effect4.Program.Typed.Fits` there would need `Folds/Ty` to import the new
  module, which imports `World`. Put the `fold_of` line in the new `Membership` module itself.
- **Proposal 1 also puts laws above their names.** `live_iff_handlesLive` mentions `HandlesLive`,
  and `fitsEq_handlesFit` and `fitsEq_strongValue` mention `HandlesFit` and `StrongValue`; all
  three are defined in `Typed/Admission.lean`. A module that `Admission` imports cannot state
  them. They belong in `Admission.lean` or later.
- **Proposal 3's ceiling change needs an adapter.** `fits_mono` takes its world order before the
  value; `M3bWorld.strongValue_mono`'s proposition takes `w w' ty v` first. `#obligation_audit`
  asks for a checked adapter when argument orders differ. Small, but not free.
- **D3 is supported.** M5 shows the table reading makes the M5 instance true for both allocation
  programs; M1–M3 show the store-length reading leaves M5 and M6 false for them.

## 5. My probes, commands and results

All runs: `bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/membership/<file>`.

| File | Exit | Axiom lines | Outside `[propext, Quot.sound]` | What it shows |
| --- | --- | --- | --- | --- |
| `verify-load.lean` (377 lines) | 0 | 25 | none | M1, M3, M4, the `succeed(1)` control; prints two statement checks and one red control |
| `verify-fits.lean` (1,096 lines, of which 893 copied verbatim) | 0 | 30 | none (six copied lemmas at `[propext]` or none) | M5 under `Fits`; `FitsInv.eq_cata`'s axioms |
| `verify-step.lean` (231 lines) | 0 | 11 | none | M2; prints its statement check |
| `verify-g6.lean` (112 lines) | 0 | 8 | none (`wBool_zero`, `wNat_zero`: no axioms) | M6 and its red control |
| `verify-oldmono.lean` (144 lines) | 0 | 8 | none | claim 9 against the ledger, with a red control |
| `verify-sub.lean` (31 lines) | 0 | 3 | none | claim 4's other direction, with a red control |

The messages the meta checks print, verbatim:

```
statement check: typedState_load_refuted : ¬ (ledger proposition of M3bAssembly.typedState_load), reducible defeq
red control: the same check refuses typedState_load_refuted_deferred (an instance)
statement check: typedState_reachable_refuted : ¬ (ledger proposition of M6Ledger.typedState_reachable), reducible defeq
statement check: step_loop_refuted : ¬ (ledger proposition of M6Ledger.step_loop), reducible defeq
red control: strongExit_mono's type is refused where strongValue_mono's is accepted
```

`verify-fits.lean` copies five exact ranges of the seat's files: `Fits.lean:24-218`, `:403-627`,
`:866-972` and `Walk.lean:219-543`, `:892-932`. Research files cannot import each other, so
copying is the only way to reuse them. The assembled copy hashes to `19e38861d0d5b919`
(sha256, first 16 hex digits), and `cmp` shows each range is byte-identical to its source.

Other commands: `python3 walk_baseline.py <repo> > baseline.lean`, then `diff -B` against
`Walk.lean:229-1174` (the restated section): exit 1, identical to `walk.diff`.
`python3 prelude_check.py check Fits.lean Gaps.lean Walk.lean`: exit 0. `grep -rowE` over
`src` and `Test` for the five names: 174 whole-word occurrences; without `-w`, 181.

## 6. What this verification proves, tests and reads

- **Reproduced:** every seat probe and script in section 1.
- **Proved** (new, this folder): the theorems cited in section 3 (M1–M6), the other direction of
  `sub_ref_equiv`, the ledger match of the `OldMono` proofs, and `FitsInv.eq_cata`'s axioms.
  The three statement checks and two red controls are meta-level checks run by Lean, not
  theorems; their messages are quoted in section 5.
- **Tested:** the seat's three `#guard`s (rerun).
- **Reading:** the arm-by-arm comparison of `FitsInv` with `Val.hasTy`; M3's extension to every
  program that binds a fresh cell; whether a reachable typed state can carry M6's world; M7;
  the import chain behind the proposal-1 correction; the inventory tallies; the lift folder's
  other verifier probe (not rerun).
- **Not attempted:** a typed derivation of `pairProgram`; `typedState_load` under `Fits` for every
  program; whether `step_loop` fails under `Fits` for some other reason; `M3bWorld.typedProg_mono`.
