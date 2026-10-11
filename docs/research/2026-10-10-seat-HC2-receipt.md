# 2026-10-10 Seat HC2 receipt: preloaded answers deleted (C5, DI-23)

**Know this before merging.** On the Lean face every host call now parks, and its answer is a
decision. Nine truth fixtures read their recorded answers through a host that answers from a
list. Their exits are unchanged. Their `run.schedule` gains a `parked`, `resumed` and `started`
row for each call, and their `runSync` exit is the `AsyncFiberError` defect. The pinned rc.112
host answers a package row inside the call, with no park. So `make check-truth` will refuse
these nine fixtures until they move to the keyed lane or the immediate-answer lowering (HC-6)
lands. The choice is the owner's (DI-23; "Decisions owed" below).

The nine fixtures: `pAcquireHandle`, `pJoinedFirstNumber`, `pJoinedFirstString`, `pSqlite`,
`pSqlFail`, `pSqlCatch`, `pSqlExit`, `pSqlOrDie`, `pKv`.

## Base and head

- Base: `26f29966` (`refactor/phase1-phase3`, the main checkout's HEAD at dispatch).
- Branch: `claude/hc2-no-preload`.
- Commits: `da26f6e9` (the Lean side), `6086bb39` (the OCaml regeneration), then this
  receipt and the semantics report (the head is in the final message).

## What moved where

| Before | After |
| --- | --- |
| `ExternalStore.answers`, `rejected`, `ofAnswers` (`src/Effect4/Machine/Stores.lean`) | deleted; `ExternalStore` holds `allocated` alone |
| the compile's registration arm at an external row (`src/Effect4/Program/Compile.lean`) | answers nothing: the catch-all arm |
| `registerExternalR` (`src/Effect4/Laws/Program/InterpR.lean`) | deleted; the reference's arm answers nothing |
| `Refusal.oracleType`, `oracleRefusal` (`src/Effect4/Program/Admit.lean`) | deleted; `replayCheckedFrom` loses `answers` |
| the `answers` parameter of `Api.load`, `replay`, `run`, `runSync`, `replayChecked`, `replaySteps`, `runAdmitted`, `replayAdmitted`, `Tape.Complete`, `TestClock.run`, `runSequential`, `runDilated`, `loadR`, `replayR` | deleted |
| `StoresOk.answers` (`src/Effect4/Laws/Program/Simulation/Hooks.lean`) | deleted; frame rules now 11 reused clauses, 3 premises |
| the premise `answers = []` of the segment law and of H8's machine half (`Agreement/Segment.lean`, `Agreement/Hosted.lean`) | deleted |
| `proof_goal run_eq_ref_table` and `theorem run_eq_ref_table_noPreload` | one theorem `run_eq_ref_table` at the amended `RunEqRefTable` |
| registry claims `run-eq-ref-table` (wanted) and `run-eq-ref-table-no-preload` (proved); R6's open part "DI-23: the preloaded answers are deleted" | one claim `run-eq-ref-table`, proved; the open part is gone |
| `Guard.Reachable p table compileFuel answers m` and its laws | `Guard.Reachable p table compileFuel m` |
| `external_registration_typed`, `externalAdmits_keys` | deleted: each read the deleted registration route and had no other consumer |
| `Profile.Scalar.observe` and `Profile.Choice.spec.observe`: every recorded answer consumed | the run minted no external handle |
| batteries that preloaded answers | the decision tape, or a host that answers from a list (`Test/Api/HostList.lean`) |
| `harness/truth/Truth.lean`'s host fixtures | the list host over the recorded tapes; `runSync` takes no answers; `harness/truth/corpus.json` regenerated |
| the session receipts' `oracleAnswers` (`harness/truth/session/*.lean`) and its assertion (`check-keyed.ts`) | deleted: no field is left to bypass |
| `E4-HOST-CE-001`, `E4-HOST-CE-002` | retired with their subject; `E4-HOST-CE-006`'s witness is the list host |

The list host is `Run.runWith` (`src/Effect4/Run/Basic.lean`) driven by `Run.Reactor.ofHost`
(`src/Effect4/Laws/Api/HostDrive.lean`) over `tapeHost` (`src/Effect4/Laws/Program/HostRuns.lean`).
It is the existing reply host, read as a reactor, and so no new representation. It answers
the calls in the order the session meets them, so it suits one fiber, as the preloaded list did.

## Placement of the changed theorems

- `run_eq_ref_table` (`src/Effect4/Laws/Program/Table/Agreement.lean`). Concept
  `translation-simulation`, required property: the frame machine and the reference agree.
  Claim `run-eq-ref-table`, role simulation, requirement R6. It was a planned goal; its proof
  is now the proof that `run_eq_ref_table_noPreload` had. Reach: every program, row table,
  decision tape and pair of budgets; the class and the observation `obs`. It does not
  establish reply admission, the typing of a reply, a host's conformance or the session's
  ledger. Its consumer is `session_eq_ref`.
- The registration lemmas lose their premise and are each `rfl`: `registerAsync_foreign`,
  `registerAsyncR_foreign`, `registerAsync_call`, `registerExternal_internal_state`. They are
  steps of `hooksAgree_of`, of the segment law and of the guard's state laws.
- No new theorem is stated. `Test/Api/HostList.lean` holds definitions only.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4` | passes, 278 jobs |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws` | three passes; the first refused `Guard/Core.lean` (a `try` proof that no longer closed), the second `Guard/MemoIds.lean` (a `split` on the deleted arm); the third passes, 878 jobs |
| `lake build` of the 21 touched batteries and `Test.Api.HostList` | passes after two arity fixes (`LoopCut.load`, `finished_mono_fuel`); the exit-type lane prints 8799 programs, 35196 runs, 32692 exited, 0 violations |
| `lake env lean -DwarningAsError=true` on `harness/truth/session/Session.lean`, `Keyed.lean` and `harness/truth/Truth.lean` | each passes, the truth driver's 240 guards included |
| `lake env lean -M4096 --run harness/truth/Truth.lean <out> --tapes harness/truth/tapes` | writes 88 programs; against the committed manifest exactly the nine host fixtures differ, in `run` and `runSync` alone, with the same exits |
| `python3 scripts/generate.py --only lcnf`, twice (the second after the prelude spelled the trivial store) | passes; no extern row went stale |
| `python3 scripts/generate.py --only eff` | passes; no file changed |
| `opam exec --switch=effect4 -- dune build` in `ocaml/` | passes |
| `make gen-semantics` | passes, 1311 jobs; `generated/semantics.md`: `run-eq-ref-table` proved, the no-preload claim merged, the next goals 15 to 14, the open parts 88 to 87 |

Not run, on the sprint's rule: `lake build Test`, every `make check-*`, `dune test`, the truth
runner on rc.112.

## `#axiom_audit`

Run with `lake env lean` over a scratch file that imports `ProofGraph.AxiomAudit` and the
modules.

| Modules | Result |
| --- | --- |
| the 7 touched core modules (`Machine.Stores`, `Program.Compile`, `Program.Admit`, `Program.HostBoundary`, `Program.Profile`, `Api`, `Api.TestClock`) | 4049 declarations within [propext, Quot.sound], none modulo planned goals; 0 planned goals |
| the 28 touched law modules | 4494 declarations within [propext, Quot.sound], none modulo planned goals; 0 planned goals |
| the 21 touched test modules and `Test.Api.HostList` | 3553 declarations within [propext, Quot.sound], none modulo planned goals; 0 planned goals |

## Decisions owed

1. **The truth lane's nine host fixtures** (owner; DI-23). DI-23's amendment deletes the list
   "after" the legacy truth programs move onto version-2 keyed tapes under DI-58's provenance.
   This slice deleted it on the brief's order. It moved the Lean face only: the fixtures read
   their legacy tapes through the list host, on one fiber, as before. Three options:
   - (a) sign the schedule and sync divergence of the nine fixtures until (b) or (c);
   - (b) move the nine fixtures to the keyed lane: the TypeScript host answers after a park
     (`KeyedRecorder`), and the session replays the keyed tape;
   - (c) land HC-6, the immediate-answer lowering, so that a synchronous binding has a law.
   **Recommendation:** (b), with (a) until it lands. (b) is DI-23's own precondition, and it
   keeps one route; (c) is the answer for synchronous bindings later.
2. **The scalar profile's observation** (meaning, small; decided here, reported once).
   `Profile.Scalar.observe` and `Profile.Choice.spec.observe` read that the run minted no
   external handle, in place of "every recorded answer was consumed". A pure row has no
   other state to agree on. The control in `Test/Program/HostSpecContract.lean` is a store
   with a minted handle.

## Proposed decisions row (not written into `docs/core/decisions.md`)

| Row | Subject | Ruling text | Basis | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| next free | Slice HC-2 (cleanup C5) is landed: the preloaded answers are deleted (DI-23, decisions rows 310 and 314) | (1) **The machine.** `ExternalStore` holds the external allocations alone. A host call's registration answers nothing on the frame machine and on the reference, at every row table. `Refusal.oracleType` and `oracleRefusal` are deleted. (2) **The run entries** and the reference's `loadR` and `replayR` take no list of answers. (3) **One raw statement.** `RunEqRefTable` loses its answers, and `run_eq_ref_table` is proved in place; `run_eq_ref_table_noPreload` and its claim merge into it, and R6 loses the open part that waited on DI-23. (4) **Premises cut.** `StoresOk` loses its clause `answers`; the segment law, H8's machine half and the guard's reachability lose the premise or the parameter. (5) **A preloaded list is a host that answers from a list.** `Test/Api/HostList.lean` drives a run with `Reactor.ofHost` over `tapeHost`; the batteries and the truth driver read their answers through it or through answer decisions. (6) **Register.** `E4-HOST-CE-001` and `-002` are retired; `-006`'s witness is the list host. (7) **The scalar profile's observation** reads that the run minted no external handle. (8) **Open.** The truth lane's nine host fixtures park on the Lean face and not on rc.112's synchronous host, so their schedules and sync exits differ until the keyed lane or HC-6 (owner) | `docs/research/2026-10-09-host-calls-and-cleanup.md` §4 C5, §8 item 2; this receipt | coordinator | landed on `claude/hc2-no-preload` |

Proposed text for DI-23's row in `docs/DESIGN-ISSUES.md`, one sentence each:

- "Landed 2026-10-10 (slice HC-2): the list, its rejection marker and every `answers`
  parameter are deleted."
- "The truth lane's host fixtures read their legacy tapes through a host that answers from a
  list; their keyed migration is owed."

DI-57's last sentence ("Its instance at no preloaded answer is the one to prove") is now the
whole statement, and is proved.

## What the coordinator must re-run

- `make check-truth`: it will refuse the nine host fixtures (schedule and `runSync`), and
  `harness/truth/result.{json,md}` stay stale until the decision above.
- `make check-host-protocol`: the keyed lane's receipts lost `oracleAnswers`;
  `harness/truth/session/check-keyed.ts` no longer asserts it.
- `make check-ocaml`, `check-native`, `check-compiler`: the engine face and the API cut are
  regenerated; `dune build` passes, `dune test` was not run.
- `lake build Test` and the axiom gate at the sweep. The planned goals drop by one: the
  library's own goals under `src/` go from one to none. No declaration rested on
  `run_eq_ref_table`, so the resting pin should not move.
- `make check-cases`: `interpOf`'s and `interpR`'s registration matches lost an arm.
- `make check-docs`, `make check-language` on the three documents edited.

## Open obligations

- The truth lane's keyed migration (decision 1).
- Two theorem names keep the old word: `external_oracle_typed` and
  `external_oracle_error_typed` (`src/Effect4/Laws/Program/Admit.lean`) state facts about the
  row's own admission (`externalAdmits`), which the row protocol still reads. A rename is
  cosmetic and touches the frozen contract's citations, so it is left.
- Two core docstrings still call the host "the external oracle": `Program/Eff.lean` and
  `Program/Native.lean`. Each edit would rebuild the whole tree, so they wait for a batch.
- The frozen packet `Test/contracts/machine-scheduler-core.contract.md` quotes scout B's
  `RunEqRefTableStatement` with answers; it is history and is not edited.
- `docs/STATE.md` is not edited (one page, rewritten at the merge).

## Evidence classes

- **Proved:** `run_eq_ref_table`, and every edited law (narrow builds; `#axiom_audit` above).
- **Tested (finite):** the batteries and the three harness drivers; the exit-type lane over its
  finite family.
- **Reproduced (Lean face only):** the truth manifest; its nine changed fixtures keep their
  exits. No host run on rc.112 was made, so nothing here is evidence about the TypeScript face.
- **Host-only and bounded:** nothing new.
