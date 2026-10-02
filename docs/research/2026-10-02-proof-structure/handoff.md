# Handoff: claude/proofs, 2026-10-02 (paused for quota)

**The one thing to know first.** M6 now has a general frame theorem (`configTyped_frame`) and a
design note (`note.md`, beside this file) that turns the remaining scheduler obligations into two
tables: what a step cannot touch, and how each token's answering role moves. `step_wake` was the
pilot and closed on its first build. Continue the remaining steps through that structure, not by
rebuilding records field by field. The owner asked for exactly this ("take advantage of
theoretical knowledge about structure ... clean and mechanical"), and for the host reply lane and
the host session contracts to be read as the same structure (`note.md` §5).

## Where

- Worktree `/Users/pooks/Dev/lean4-effect4-claude`, branch `claude/proofs`. Not pushed; not merged
  into `refactor/phase1-phase3`.
- Base of this stretch: `fbc25bfb`. Head: `a8767806` (plus the commit adding this file and
  `note.md`).
- Every commit below built narrowly (`lake build Effect4.Laws`, 554–555 jobs, and the batteries
  named in each message). No `make check-gen` or full battery was run (owner rule: not between
  merges; it is the agreed checkpoint sweep).

## Commits

| Commit | What landed |
| --- | --- |
| `a7294954` | Decisions row 134 (a), (b), (d), (e) as clauses of `J`: `WorldValid.timers`, `.waiters` (`WakeTyped` over `Guard.wakeKeys`, new `Laws/Machine/WakeKeys.lean`), `SchedulerState.raceObservers`, `.liveBelow`, `.targetsBelow`, `.observersBelow`, and the queued half of (d) in `QueueOk`/`HeadOk`. The 13 proved commands and 12 edits re-proved. |
| `ed50d19c` | `M6Edits.clockSome` proved (`edit_clockSome`); `E4-TYPED-CE-024` repaired; `decisionEdits` unconditional; `decisionKeeps_of_steps` and `typedState_reachable_of_steps` lose their `clockSome` premise. Shared: `wakeKeys_waiter_mem`, `wakeKeys_wakeBy_subset`, `Guard.timer_fireNext_keys`/`timer_clockStep_keys` (the guards' copies delegate), `internalKeys_state_subset` generic over the code alphabet. Battery `Test/Program/TimerColumn.lean`. |
| `179ee784` | Row 187 (c), the memo table: `MemoWorld.layerCells` and `syncOpStep_layerCells` (StoresLaws); `MemoTableTyped`; `StoreTyped root w` carries it; `memoGet_implements`, `memoComplete_implements` proved (M3bAdequacy 0 open). In `J`: `preds root`'s `PromiseTable` is `PromiseTableOk root w due memo`, two rows, parameterized by exactly the fields it reads. Battery `Test/Program/MemoTable.lean` (build, real hit, real completion, wrong error column refused twice). |
| `a8767806` | `StoreFrame` and `configTyped_frame` (the restate lemmas are now instances); the Deferred column's step proved once (`Guard.wakeBatch_cellAt`, `wakeBatch_due`, `wakeBatch_cells_length`, `cellAt_setCell`); the waiter → due implication (`completionStrong_await`); `M6Ledger.step_wake` proved (`wake_preserves`). |

Axioms, checked with `lake env lean` on `#print axioms`: `[propext, Quot.sound]` for
`edit_clockSome`, `wake_preserves`, `configTyped_frame`, `completionStrong_await`,
`wakeBatch_cellAt`, `wakeBatch_due`, `memoGet_implements`, `memoComplete_implements`,
`syncOpStep_layerCells`, and every theorem the two new batteries print.

## Ledger at the head

- M5 (`M3bAssembly`): closed.
- `M3bAdequacy`: 0 open (all 31 store rows).
- `M6Edits`: 0 open (13 of 13).
- `M6Ledger`: 6 open: `step_loop`, `step_deliver`, `step_launch`, `step_registrationDone`,
  `decision_preserves`, `typedState_reachable`. The last two are one line each once the four steps
  are in (`decisionKeeps_of_steps`, `typedState_reachable_of_steps` with `loadsTyped`, in a module
  that imports both `Typed/Edits.lean` and `Typed/LayerArm.lean`).
- `M7`: 4 open, conditional assembly `m7_of_ledger` in place; row 180 (a) owed for
  `exitHandles_valid`.

## Owed next, in order

1. **The CE-026 control battery** (not written): `Test/Program/WaiterColumn.lean`, adapted from
   seat D3's probe `docs/research/2026-10-01-landing/seat-D3/probes/Wake.lean`: its world (the
   batched waiter's token declared `number`, the cell `(void, never)`) refused by
   `WorldValid.waiters`; the same machine with the token declared `void` stepping typed through
   `wake_preserves`; the behaviour by `rfl` (the batch owed now with the completion; an
   uncompleted cell's batch rejoining the pending list). Then mark `E4-TYPED-CE-026` REPAIRED in
   `Test/Counterexamples/REGISTER.md` and register the file in `Test/All.lean` after
   `Test.Program.MemoTable`.
2. **The remaining steps through `note.md`.** §6's table places each: `loop`'s store arm as one
   theorem (`storeStep_typed` + a `StoreFrame` builder per row + `Guard.syncOpStep_storeKeys`);
   the fiber arms one transfer row at a time (registration → timer via `asyncPre`'s sleep clause,
   → waiter via its await clause); `launch` (fresh fiber at `nextId`, row 134 (e)) and
   `registrationDone` (race → the host's park, row 134 (d)) with fiber-edit guarantee builders for
   `ObsView`. `StoreFrame` still demands equal scopes and memo world through its callers' own
   `StoresOk`; the memo rows of `loop` will want a frame field for `layerCells` (the view exists).
3. **Cleanups the structure exposes.** `KeysTyped` as the one sender clause (`WakeTyped` and the
   due row through it; the due row could take the declared `∃` form); duplicate lemmas
   `exitOk_widen` (Seq) and `exitOk_subN` (Bookkeeping); the guard's inline rejoin proof in
   `deferredKeys_wakeBatch_subset` can use `wakeKeys_rejoin_subset`.
4. **The owner's list of 2026-10-02, untouched so far:** C.3 (the coupled key/length fold with
   exact connectors to `Ty.key`, a real ordering consumer, the import seam: `Ty.lean` cannot
   import its generated fold; measure before claiming speed); the OCaml `Nat.add` lowering leaf
   (63-bit model law for sums at most 2^62−1, emitted-code controls, the model proof kept apart
   from the reader and host evidence); the record field lookup at the coordinated append
   (`namedFit_required`/`namedFit_lookup`, `P5Fits.lean` near line 1800); the ProofMapSelection
   refresh with citation-key resolution (reconcile with Gemini's source-key task first); and
   integrating `codex/ocaml-idioms` (head `41bacc1f`, receipt
   `/Users/pooks/.codex/worktrees/ocaml-idioms/lean4-effect4/docs/research/2026-10-02-ocaml-idioms/receipt.md`;
   regenerate LCNF on the merged head, never hand-merge generated bodies).
5. **Records owed at the checkpoint.** Decisions rows 134 (landing notes for (a), (b), (d), (e)
   and the steps proved), 140 (the new reports), 187 (the memo table landed); STATE's ledger
   counts; the deferred sweep (`make check-gen`, `scripts/test-generators.py`, the semantics
   report and architecture page regenerated: `generated/semantics.{json,md}` quote the ledger and
   are stale after these commits).

## Evidence limits

- Everything above is kernel-checked Lean at the trust ceiling; no host run, no runtime timing.
- The `wake` proof is general; its counterexample's repair has no control battery yet (item 1).
- `note.md`'s claims about the remaining steps are a design, tested only by the `wake` pilot. Its
  citations are to the vendored copies under `docs/research/2026-10-01-semantics/sources/`, with
  PDF page numbers from the text extracts.
- Standing constraints honoured: one `lake` at a time in this worktree; commits by explicit paths;
  no `simp_all`, `first` or `try` in new proofs; Gemini's worktree and scratch untouched.
