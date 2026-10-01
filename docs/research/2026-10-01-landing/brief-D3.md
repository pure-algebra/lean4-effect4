# Seat D3 brief: the eighteen command proofs, the six edits, M6c, and scope-handle validity

Written 2026-10-01 by the coordinator; dispatched after pass I2 merges (the coordinator names the
base commit at dispatch: main after I2, with row 156's `ScopeLive` landed). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-D3`, branch `seat/D3`; `.lake` cloned from the main
checkout, current at the base. Read `docs/research/2026-10-01-landing/plan.md` (§4 rules, §5
measure), then in full: receipt C ("`J` and `I` as printed", "The per-command table of `I`'s
code lines", step 4's halting-site census, "What is owed"), receipt I (repairs 2, 5, 6), receipt
I2 (row 156 and seat A's hunks), and `Assembly.lean`'s module docstring. Seat D1 runs in parallel
on the contract rows (`Residual.lean`'s posts and pres, `Membership.lean`, `Contracts.lean`,
`DenoteR.lean`, `Assembly.lean` at `preds` and `loadsTyped_of_denotesTyped`); you never touch
those sites. You own: new files `src/Effect4/Laws/Program/Typed/Commands/*.lean` (one per command
group, named below) and `Laws/Program/Typed/Edits.lean`; `Assembly.lean` only at the foot, the
`#obligation_proved` lines under `M6Ledger`, `M6Edits` and `M7` (each at its own anchor, after
the scope's last `#obligation_proved`); the root import `src/Effect4/Laws.lean` at the anchor
after `Typed.Seq`; `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` only to flip a
control a proof makes positive; and your receipt.

**The one thing.** The ledger's open count per scope is the number (plan §5 item 2):
`M6Ledger` 20 open (`LoadsTyped` is seat D2's; the eighteen `StepPreserves` goals and
`DecisionKeeps` are yours), `M6Edits` 6 open, `M7` 4 open (`exitHandles_valid` is yours now;
`exits_typed`, `stores_typed`, `never_halts` close by `m7_of_ledger` once M5 and M6 close, and
you write those three `#obligation_proved` lines only if `LoadsTyped` has closed on your base).
Every command proof shows its halting arms unreachable from `I` (row 139's census) and reads no
code a running fiber owns except through `ReadCode`.

## The shapes (as the tree states them, `Assembly.lean`)

`StepPreserves root rootTy cmd := ∀ w m rest, m.stuck = none → ConfigTyped root rootTy w m
(cmd :: rest) → ∃ w', w.leHost w' ∧ ConfigTyped root rootTy w' r.1 r.2` with `r := driveStep
(interpR root.program) m cmd rest` (`:352`); `ConfigTyped := MachineTyped ∧ ReadCode ∧ QueueOk`
(`:269`); `MachineTyped := TypedState ∧ LiveCode ∧ MachineLive` (`:261`); the queue facts in
`QueueOk` (`:182`); `DecisionKeeps` (`:811`); the edits `EditDrain` … `EditAnswer` (`:1053-1116`),
`SnapshotTyped := QueueOk` over the tasks' commands (`:394`); `ExitHandlesValid` (`:1264`). The
lift's bridge is `guarded_stepKeeps_of_stepPreserves` (`:629`): what you prove is exactly the
lift's `step` premise. The handler side you consume: `storeStep_typed`, `answerFrame_typed`,
`seqFrame_typed` (`Adequacy.lean`), with `StoreTyped` from `storeTyped_of_typedState`
(`Assembly.lean:294`); the stack laws `savedOk_mono`, `stackAccepts_mono`, `typedProg_mono`
(`M3bWorld`); the frame instances of seat B's `Adequacy`.

## The work, in order (one file and one commit per group; narrow build each)

1. **`Commands/Bookkeeping.lean`:** `trackChild`, `exitDone`, `wake`, `drainDue`, `link`,
   `observe` (read no code; the halting arms: `postTask` unknown owner by `MachineLive.dueOwners`;
   `linkScope` by `QueueOk.links`; `fireObserver` scope drop by `ObserverCommandOk`).
2. **`Commands/Finish.lean`:** `finish` (row 133's line: typed by `QueueOk.payload`; publishes
   the exit or installs the middleware program), `evaluate` (`EditEvaluate`'s shape: the flags; a
   no-op on a running fiber), `resume` (overwrites a parked fiber's code with the typed answer
   continuation: `ResumeOk`, `CompletionStrong`).
3. **`Commands/Race.lean`:** `launch`, `enrollRace`, `registrationDone`, `interruptTarget`,
   `afterInterrupt`, `raceCancel`, `closeParAwait` (typed by `RegistrationState`,
   `QueueOk.delivery`'s `AfterInterruptReply`/`StackReply`/`FiberListColumns`, the iterator
   protocol; `registerRace`'s halt by `RegistrationState`, `interruptRecord` only on an idle
   target).
4. **`Commands/Loop.lean` and `Commands/Deliver.lean`:** `loop` and `deliver` per evaluator arm
   (`EvaluateR.lean`): the store arm by `storeStep_typed`; the fiber arms by the row's pre and
   post and the frame instances; `prepareScopedExitR` by the `scopeExit` constructor's `ScopeLive`
   (row 156); `FiberAction.closeScope`/`interruptAs`/`join` by `fiberPre`; `forkScoped` by
   `MachineLive.ambientScopes`. An arm whose pre or post is seat D1's to change (the close rows,
   the presence clause) is proved against the base's statement if it holds there, else recorded
   with the exact obstacle and left for D1's merge; say which arms.
5. **`Edits.lean`:** `drain`, `yield`, `interrupt`, `clockNone`, `clockSome`, `answer`
   (`M6Edits`; `drain` and the clock steps move owed work into the snapshot and re-establish
   `QueueOk`; `answer` is the lift seat's `answer_of_split` shape, `AnswerDecision.lean:94-112`,
   over `I`). Then `DecisionKeeps` (M6b) from the eighteen and the edits through the lift's
   `DecisionLift` (`decision_preserves`, `:1467`, already stated over `J`).
6. **`exitHandles_valid`** (`M7`): from `J` with row 156's scope arm of `HandleFits` and
   `ExitOk` on recorded exits through `fits_live`/`Live` (receipt C "What is owed"; the native
   guard's handle facts through R4's bridge `replayR_bmeans_reachable` if `J` is not enough; say
   which). Then `typedState_reachable` (M6c, `:1493`) from `DecisionKeeps` and `LoadsTyped`,
   written as the proof it is even if `LoadsTyped` is still declared (a theorem with the ledger
   goal as its premise, consumed by `#obligation_proved` when D2 closes M5).
7. **Final:** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green with both gates; the
   ledger per scope (`M6Ledger`, `M6Edits`, `M7` open counts before and after); `#print axioms`
   for every theorem; the controls of `M6Capstone` that a proof flips, flipped with the old form
   kept as history.

Order inside a group: the command with the fewest halting arms first; measure a command whose
proof passes a few hundred lines and say so; a halting arm that `I` does not exclude is a
finding (a decisions row to propose, with a checked refutation), not a premise to add.

## Rules

Plan §4 (the list in brief-G's "Rules" applies verbatim). `LEAN_NUM_THREADS=4`, one lake at a
time in this worktree. No generator. Commits by explicit paths on `seat/D3`; research files
force-added; no push; never `git merge`/`checkout`/`reset`; a refused permission is recorded, not
worked around. Evidence words on every claim.

## Receipt

`docs/research/2026-10-01-landing/receipt-D3.md` (force-added, committed last): the one thing
first; base and head; every changed path; per command the theorem (name, file:line, axioms, the
halting arms and the clause that excludes each); the ledger before and after; the commands left
open with the exact obstacle; the proposed lines for rows 134, 139, 140 and the register.

## Amendments (2026-10-01, after pass I2)

- **Base:** main after I2's merge (`c898ad04`) and its record; the coordinator names the commit at
  dispatch. Read receipt I2 (`receipt-I2.md`, "The one thing first") before the Assembly
  definitions: `TypedProg.scopeExit` takes `live : ScopeLive w sc` first; `StoreTyped` has a
  `memo` field; `HandleFits`' scope arm reads `ScopeLive`; `handleFits_map`, `flatFits_map`,
  `servicesFit_map`, `fits_map` take `hscope` before `hsvc`; the five scope-handle posts read
  `Fits w' ans Ty.scope`; `MachineLive` lost `ambientScopes` (now the theorem `ambientScope_live`
  from `J`); `MachineTyped` has `services`; `initialWorld` takes the service table;
  `AdmitRefusal` has `emptyColumn`. The ledger at the base: 37 open, 447 proved, 484 total.
- **Step 0, before step 1: one name for scope presence at the machine's store** (ruled by the
  coordinator on row 156). Pass I2 landed `ScopeLive w sc` at the world (`World.lean`). Three
  clauses still spell the same fact at the machine's store, `(m.state.scopes.entryAt scope).isSome
  = true`: `QueueOk.links` (`Assembly.lean:200`) and the observer clauses' scope-finalizer drop
  arms (`Scheduler.lean:113`, `:132`). Give the store-level fact one definition (in the store
  module that owns `scopes.entryAt`, or `World.lean` if the store module must not grow), make
  `ScopeLive w sc` that definition at `w.state` (by definition, or by a proved equation if its body
  must stay for I2's consumers), and read it at the three clauses; `WorldValid.state` is the
  bridge where a proof moves between `m` and `w`. A few lines; narrow build of `Assembly`,
  `Scheduler` and their direct importers; the `M6Capstone` controls that construct `QueueOk` by
  hand follow. Its own commit.
