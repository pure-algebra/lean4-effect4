# Seat D5 brief: the five clauses of row 134 (a)–(e), the eight goals re-proved, M6b, M6c, row 180

Written 2026-10-01 by the coordinator after seat D3 merged (`7d50cfe6`) and its eight refutations
were ruled (decisions row 134, amendment (a)–(e); row 180). Dispatched after seats D4 (the
finalizer row in `Typed/Sources.lean`, a `Preds` field, row 117's closed-row premise) and D2 (rows
170 and 175 on `PointTyped`/`DenotesTyped`, M5) merge, so the shapes you build on are final; the
coordinator names the base at dispatch. Worktree `/Users/pooks/Dev/lean4-effect4-seat-D5`, branch
`seat/D5`; `.lake` cloned from the main checkout, current at the base. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then in full: receipt D3
(`receipt-D3.md`: the findings table F1–F6, "Commands left open, with the exact obstacle" (the
arm-by-arm reading of `loop`/`deliver`), the work log's entries for steps 4–6, "Integration with
D1"), the probes `seat-D3/probes/{ClockSome,LoopDeliver,Wake,MarkerStack,Races}.lean` (the
refutations you repair; they become the register's REPAIRED controls), receipts D4 and D2 (the
shapes as merged), decisions rows 134, 139, 140, 156, 170, 175, 180.

**The one thing.** Eight goals of the ledger are false as stated because `J`/`QueueOk` do not say
five things every reachable machine satisfies (row 134 (a)–(e), ruled: a timer column, a waiter
column, empty stacks under exit and a queued `finish`, race keys off stored observer keys,
fresh-bounded fiber ids). You add the five clauses where they belong, each with the step that
establishes it named in its docstring, re-prove the eight goals, and close M6b and M6c from
`decisionKeeps_of_steps` and `typedState_reachable_of_steps` (D3 proved both conditionally). Row
180 (a) closes `M7.exitHandles_valid`. If a clause as ruled is not what the step keeps, that is a
finding of the same kind as D3's: a checked refutation, a proposed amendment, the goal left open
with its exact obstacle; never a weakened statement.

## Step 1: the five clauses (one commit)

Each clause goes in the judgment D3 named (F1–F6's "proposed repair" column), as a field of the
generated bundle where the typed state is generated (`Typed/Sources.lean` rows and `Preds`,
following D4's finalizer row, which is the latest instance of the pattern) or as a clause of
`QueueOk`/`SchedulerState`/`MachineLive` where D3 put it:

- (a) timers: every sleeper `(fiber, token)` of `timers.wake` has `Θ fiber token` at a type `void`
  fits (what `asyncPre`'s `registerSleep` arm demands at registration; F1).
- (b) waiters: every waiter `(fiber, token)` of a Deferred cell's list, pending or batched, has
  `Θ fiber token` above the cell's declared columns (what `registerAwait` demands; F2, F3).
- (c) stacks: the saved stack of an exited fiber, and of a fiber a queued `finish` names, is empty
  (the loop queues `finish` only from the `finished` outcome, after the stack is exhausted; F4).
- (d) races: `(race.host, race.token) ∉ observerKeys o` for every stored observer (F5).
- (e) freshness: every fiber id the bookkeeping names (a race's live set, a countdown target, a
  stored observer's fiber) is below `nextId` (F6).

Each clause is monotone along the world order (one `*_mono` theorem in `M3bWorld`'s scope, S1) and
is established at the load (`machineTyped_load`, `typedState_load` if still open) and kept by the
sixteen goals D3 closed: re-run their proofs (a step that leaves a field alone leaves its clause
alone, the bundle's rule); where a closed goal touches a field a new clause reads, prove the
clause kept there too. The pinned count line of `Typed/State.lean` is re-pinned by you.

## Step 2: the eight goals

`M6Edits.clockSome` (F1), `M6Ledger.step_loop` and `step_deliver` (F2, through D3's arm-by-arm
reading in "Commands left open": the store arm by `storeStep_typed` and the waiter column at
`deferredCompleteWith`, the `async` registrations by `asyncPre`'s entries, every fork arm by (e),
`prepareScopedExitR` by `TypedProg.scopeExit`'s `ScopeLive`, the close rows by D4's finalizer
typing), `step_wake` (F3), `step_exitDone` and `step_finish` (F4), `step_registrationDone` (F5),
`step_launch` (F6). D3's refutation theorems flip to positive controls or stay as red controls of
the old statement in the probes (keep them compiling as history under the seat folder); the
register rows `E4-TYPED-CE-024`–`029` become REPAIRED (propose the lines).

## Step 2b: the field census (row 181, S8)

Beside the five clauses, the instrument that would have found them first: a census command
beside `#typed_state` (or a sibling of `#traversal_census`) that lists every field of `RState`,
`Stores`, `SchedulerState`, the queue, `Point` and `World` with the row of `Typed/Sources.lean`
(or the statement premise) that types it, and refuses a field with neither a row nor a named
exemption with its reason; run at the foot of `Typed/State.lean` like the other censuses, green
the day the five clauses land, every exemption listed by name in the receipt. System map §10.3's
S8 reads its output; propose its status line.

## Step 3: M6b, M6c, row 180

`M6Ledger.decision_preserves` by `decisionKeeps_of_steps`, `typedState_reachable` by
`typedState_reachable_of_steps` and M5's `LoadsTyped` (D2's, as merged; if `denoteR_typed` is still
open for a family, M6c is stated with that premise and the ledger line stays open with the exact
obstacle). Row 180 (a): the native invariant beside `handles_minted` (every value frame
registered, by construction through `HandleKind` images), and `M7.exitHandles_valid` from
`exitHandles_valid_of_registered`. Then `m7_of_ledger`'s three remaining lines if M5 and M6b both
closed; otherwise their exact premises.

## Builds and the testing rule

Narrow builds while landing (`lake build Effect4.Laws.Program.Typed.World` and the modules that
import it; the command modules one at a time), the roots once before the receipt
(`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`), no `make check`, no generator (the
typed-state bundle is a Lean elaborator, `#typed_state`, not a producer), no `check-full`. One
lake at a time in this worktree.

## Rules

Plan §4 (brief-G's "Rules" list applies verbatim). `LEAN_NUM_THREADS=4`. No `sorry`,
`native_decide`, `partial`, `unsafe`, `axiom`, `extern`, `implemented_by`; trust ceiling
`[propext, Quot.sound]` (`#print axioms` on every theorem); no `simp_all`, `first | …`, `try`
under `src/`; a hand `simp` is `simp only [...]`; no case analysis on `Ty` outside
`Laws/Program/Typed/Membership.lean`. Commits by explicit paths on `seat/D5`, one per step;
research files force-added; no push; never `git merge`/`checkout`/`reset`; a refused permission
is recorded, not worked around. `README.md`, `AGENTS.md`, `docs/core/decisions.md`,
`docs/STATE.md`, `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md` and
`lakefile.toml` are never edited: propose their lines in the receipt. Evidence words on every
claim (proved, tested, reading, assumed).

## Receipt

`docs/research/2026-10-01-landing/receipt-D5.md` (force-added, committed last): the one thing
first; base and head; every changed path; per clause its judgment, its `*_mono`, its establishing
step and the goals it reopened and re-closed; per goal the theorem (name, file:line, axioms) and
the halting arms excluded; the ledger before and after (`M6Ledger`, `M6Edits`, `M7`, the whole
tree); the goals left open with the exact obstacle and the checked refutation if one was found;
the proposed lines for rows 134, 140, 180 and the register.
