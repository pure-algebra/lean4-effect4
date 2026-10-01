# Seat I brief: integrate seat C's split with seats B, E and F until the tree builds

Written 2026-10-01 by the coordinator. Worktree `/Users/pooks/Dev/lean4-effect4-seat-I`, branch
`seat/I`, created from `refactor/phase1-phase3` at `af3799f9` (seats E, F and B merged) with
`seat/C` (head `45281aed`) merged on top by the coordinator as a textual merge (no conflicts). The
`.lake` cache is current for `af3799f9`; seat C's modules rebuild. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then the two receipts in full:
`receipt-B.md` (its "For seat C" section) and `receipt-C.md` (its "The merge, not done", "Lines
for seat B", "`J` and `I` as printed", "The per-command table of `I`'s code lines"). Both are in
this worktree under `docs/research/2026-10-01-landing/`. Never edit or build outside this
worktree; read other worktrees by absolute path only if a receipt names a file there.

**The one thing.** Seat B closed frames under world growth and put every post at the machine's
answer with the handler rule proved; seat C split the typed state at the cut (`J = MachineTyped`,
`I = ConfigTyped`), declared M7 and made the ledger one list; each built green on its own base, and
their union does not build until the repairs both receipts foresaw are made. You make exactly
those repairs, keep every statement either seat landed (restating a proof is fine, weakening a
statement is not), keep every red control red against its historical definitions and every flipped
control positive against the current ones, and end with `LEAN_NUM_THREADS=6 lake build
Effect4.Laws Test.All` green with both gates.

## The repairs, in order

1. **`M6Capstone.lean`:** seat B's three-lambda hunk (the closed `answer` and `resume` arms) is
   applied textually by the merge; confirm it builds under seat C's restated sections.
2. **Seat B's batteries under the split** (`Test/Program/FramesNotKripke.lean`,
   `Test/Program/ProtocolPosts.lean`): `TypedState root rootTy w m` (no queue argument), the new
   `savedPosition_of_saved root w ty saved typed`, `QueueOk` with its `links` field (vacuous on a
   queue with no `link`: `fun _ _ _ _ _ h => nomatch h` after `cases` on membership, as
   `M6Capstone`'s `config_typed` does), the generated stores component's closed-exit arm
   `(preds root).ScopeExitOk`; where a construction is historical, the `H1Shapes` route
   (`StaleCode.lean`, `M6Capstone.lean`) is the model; every `Preds` instance gains the
   `ScopeExitOk` line. `Old.*` carries its own inert-code predicate already.
3. **Seat C's red controls that seat B's repairs flip:** `AwaitLoad.loadsTyped_false` and
   `capstone_false` (`Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`) rest on
   `root_code_refused`, which seat B's await-by-value post repaired. Keep the refutation over the
   old post as history (B's `oldFiberPost`/`OldTypedProg` are in `ProtocolPosts.lean`; import or
   restate locally) and add the positive control: `J` at the load of the typed corpus's
   `awaitFiber.value` through `machineTyped_load` with B's typed await code
   (`ProtocolPosts.AwaitValue.await_code_typed`). `RawOrderLoad.lean` (CE-009) stays red: seat A's
   `Fits` order is not merged yet.
4. **`M6Stack` against `M3bWorld`:** seat B proved `stackAccepts_mono` and `savedOk_mono` in
   `M3bWorld` (`Contracts.lean`, `Residual.lean`) and `preds_savedOk_mono` in
   `Test/Program/FramesNotKripke.lean`; seat C declared the three as `M6Stack` goals in
   `Assembly.lean` with `savedMono_of_stackMono`. One owner: close the `M6Stack` goals by
   `#obligation_proved` through argument-order adapters, and move `preds_savedOk_mono`'s proof
   from the battery into `src/` beside its declaration (the battery keeps a one-line use of it), or
   delete `M6Stack` in favour of `M3bWorld` and state `preds_savedOk_mono` there; say which and
   why in the receipt. No statement duplicated in two scopes.
5. **`fiberPre`'s halting arms (row 139; receipt-C "Lines for seat B" item 1):** seat B put scope
   liveness on the scope *store* rows' pres; the fiber rows that reach a halting site still have
   `True` pres, so `step_deliver` is refuted (`step_deliver_refuted_by_absent_scope`, proved by
   seat C). Apply seat C's exact hunk to `Residual.lean`'s `fiberPre` (`.interruptAs`, `.runIn`,
   `.forkIn`, `.scopeExit`, `.closeScope`, `.raceRegister := False`), re-prove `fiberPre_mono`'s
   affected arms (scope entries persist along `leHost`, `Γ` grows) and whatever in
   `Residual.lean`, `Stack.lean`, `Adequacy.lean` and the batteries reads those arms; then
   `step_deliver_refuted_by_absent_scope` stops compiling: replace it by its repaired form, the
   refusal of that input (`¬ ConfigTyped (rootProgram : ProgramSource) unitTy w machine (command ::
   rest)` at every `w`), with the old refutation retained over `H1Shapes`. If an arm's
   monotonicity or a consumer cannot be re-proved in a few lines, stop on that arm, record the
   exact obstacle, and leave the arm as it was with the control still red.
6. **`storeTyped_of_typedState`** (receipt-B "For seat C" item 3; receipt-C item 6): state
   `MachineTyped root rootTy w m → StoreTyped w` in `Assembly.lean` (or `Adequacy.lean`) and prove
   it from `WorldValid`'s coverage, the generated `HeapCell` column and `ScopeExitOk`; if it is not a
   few lines, declare it as a `#proof_wanted` goal in `M3bAssembly` with the obstacle named.
7. **Seats E and F against the union:** `Laws/Program/Typed/Seq.lean` (E) and
   `Laws/Program/Typed/ExitConnector.lean` (F) compile against the merged `Residual.lean` and
   `Admission.lean`; repair minimally if not.
8. **Then** `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All` (one compiler in this worktree):
   green, both gates; the ledger reports per scope (`M3bWorld`, `M3bAdequacy`, `M3bAssembly`,
   `M6Ledger`, `M6Edits`, `M6Stack` if kept, `M7`) in the receipt; `#print axioms` for every
   theorem you added or re-proved.

## Rules

Plan §4: no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern`, `implemented_by`; no
`simp_all`, `first | …`, `try` under `src/`; hand `simp` as `simp only [...]`; the trust ceiling
`[propext, Quot.sound]`; no case analysis on `Ty` outside `Membership.lean` (row 132); commits by
explicit paths on `seat/I`, one per repair, each after its narrow build; research files
force-added; no push; the coordinator's files (`docs/core/decisions.md`, `docs/STATE.md`,
`README.md`, `AGENTS.md`, `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md`) are not
yours: propose lines in the receipt. Plain words; evidence words on every claim; every number in
the receipt behind a command.

## Receipt

`docs/research/2026-10-01-landing/receipt-I.md` in this worktree (force-added): the one thing
first; base (`af3799f9` + `seat/C` at `45281aed`) and head; every changed path; per repair the
statements and proofs touched (name, file:line, axioms), the controls (red retained, positive
proved); the ledger before (receipt-B's and receipt-C's numbers) and after; what is owed, with
the exact obstacle for anything left red; the lines for the coordinator's files (register cells
for `E4-TYPED-CE-010`, `-011`, `-012`, `-014`, `E4-SCHED-CE-019`, `-020` as receipt-C proposes,
checked against what you landed).
