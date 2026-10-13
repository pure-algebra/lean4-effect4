# Seat FLOW receipt: the answer-flow history producer (2026-10-13)

Status: receipt (history, not authority). Seat FLOW, branch `seat/flow`, worktree
`~/Dev/lean4-effect4-flow`. The brief is `docs/research/2026-10-13-seat-flow-brief.md`. The
coordinator ended the seat early, at about four and a half hours.

## The one thing to know before merging

The producer is landed and proved, but no goal moved: all four goals are still goals (measured).
`AnswerFlow.Commands.step` carries any per-fiber frame predicate through every command, from
per-arm local facts. `PlaceFunding.NativeFlow.history` carries it through every admitted history.
`PlaceFunding.LocalOn.history_funded` funds a place ledger under it. What remains for the crews is
their answer-class model and its local facts, then the writer ledgers (§5). Commit `b8e78b0e2` is
merged; commit `66a9f0256` adds two instance lemmas on top of it.

## Base, head and evidence words

- Base: `cdcedb4b4` on `refactor/phase1-phase3`. Head: the commit that adds this receipt; the last
  code commit is `66a9f0256`.
- Evidence words: **proved** means the kernel checked it, audited at `[propext, Quot.sound]`.
  **Measured** means a tool's output at the named head. **Assumed** means read in the source, not
  checked.

## 1. What landed

### 1.1 Commit `b8e78b0e2`: the producer

`src/Effect4/Laws/Machine/AnswerFlowRun.lean` (new, generic in the machine, reached from
`Effect4.Laws`). Every declaration is proved.

| Declaration | What it states |
| --- | --- |
| `AnswerFlow.Flows G worldOf m` | each stored fiber's frame holds `G` at the world that fiber reads (`worldOf m.state f.id`) |
| `Flows.fields`, `update`, `update_same`, `update_found`, `update_emit`, `modify`, `state`, `append`, `found` | the structural writes: a write that keeps frames and store keeps the flow |
| `Flows.drainOwed`, `fiberEdit`, `fiberEdits`, `interruptEach`, `fireObserver`, `exitFiber`, `linkScope`, `launchEntrant` | the driver's helpers keep the flow, each from its one frame or store premise |
| `IterFlows`, `Flows.settle`, `Flows.settle_one` | settlement keeps the flow of an iteration's installed result |
| `AnswerFlow.Commands` | the local facts of the commands: iteration, delivery, interruption, reply, race entrant, race settlement and park, await, parallel close, exit children, publish, clear, and four store hooks |
| `Commands.step` | **every command keeps the flow** (all nineteen arms of `driveStep`) |
| `OutsideEdits`, `OutsideEdits.machineEdits` | the decision's outside edits keep the flow; clock and reply preparation are the store facts |
| `AnswerFlow.Local`, `Local.decision_lift` | **the producer**: any base `DecisionLift`, with the flow carried beside it (`Lift.DecisionLift.withMachineFact`) |

`src/Effect4/Laws/Program/PlaceFunding/Flow.lean` (new, native, reached from `Effect4.Laws`).

| Declaration | What it states |
| --- | --- |
| `PlaceFunding.SourceReady` | source ownership's facts at a command: configuration and the command's code |
| `PlaceFunding.NativeFlow` | the native flow facts: `Commands` at `SourceReady`, and `OutsideEdits` |
| `NativeFlow.decision_lift` | source ownership and the flow, through every decision, replies included |
| `NativeFlow.history` | the flow holds along every admitted history of a direct-fragment program, from a flowing load |
| `PlaceFunding.LocalOn`, `Local.on` | a place ledger's local facts with the evaluator debit read under a carried invariant `Q`; `Local` gives them for any `Q` that survives reply preparation |
| `LocalOn.command`, `LocalOn.decision_lift`, `LocalOn.history_funded` | the ledger funded along every admitted history, from a decision lift that carries `Q` |

### 1.2 Commit `66a9f0256`: the answer-flow instance lemmas

`AnswerFlow.FrameFlow`, in `AnswerFlowRun.lean`, reads a frame's `FamilyResult` at its fiber's
output class. `FrameFlow.fields` keeps it under writes outside the current code and stack.
`FrameFlow.replace` keeps it when the new code answers each class the old code answers. Both are
proved.

## 2. Placements (AGENTS.md, Trust)

| Theorem | Concept and question | Reach | What it does not establish | Unlock |
| --- | --- | --- | --- | --- |
| `Commands.step`, `Local.decision_lift` | store-typing R4 and scope-lifetime-finalization R11, with reactive-scheduling; proposed claim `answer-flow-history`, role preservation | every interpreter, evaluator, base lift, world order and per-fiber predicate | no answer class of a program; no progress; the local facts stay premises | the four goals' history step, once an instance proves `Commands` |
| `NativeFlow.decision_lift`, `NativeFlow.history` | the same claim, native | direct-fragment programs, every row table, compile budget and admitted history | as above; the host boundary is unchanged | the crews' instance owes only `NativeFlow` and its load |
| `LocalOn.history_funded` | scope-lifetime-finalization R11; the history step of the crews' writer ledgers | as `Local.history_funded`, with the debit under `Q` | progress, release order, host observation | a writer debit that reads the acquired value from the flow |
| `FrameFlow.fields`, `FrameFlow.replace` | steps of an answer-flow instance's `publish`, `interruption`, reply and await facts | every model and saved edge | the class facts themselves | fewer obligations per instance |

Consumers named in the docstrings: the crews' answer-class instance, then
`Workers.Assertions.logs_step` and `QueueWorkers.Assertions.logs_history`. No goal was planted. The
crews' model is not built, so a local-facts goal would be a statement nobody has checked.

## 3. Reused declarations

- `src/Effect4/Laws/Machine/Lift.lean`: `DecisionLift`, `Guarded`, `StepKeeps`, `MachineEdits`,
  `interruptEdit`, `unitOrder`, `stepDecisionState_lift`.
- `src/Effect4/Laws/Machine/LiftMachineFact.lean`: `DecisionLift.withMachineFact`, which is the
  producer's whole decision layer.
- `src/Effect4/Laws/Machine/AnswerFlowFamily.lean`: `FamilyResult` (the interpreter-free form the
  flow uses), `SavedFamily` (for instances).
- `src/Effect4/Laws/Machine/Ledger.lean`: `StackLedger.interruptRecord_key`,
  `StackLedger.interruptWithCause_key`.
- `src/Effect4/Laws/Machine/MaskRuns.lean`: `RunMachine.mem_of_fiber?`, `RunMachine.id_of_fiber?`.
- `src/Effect4/Laws/Program/NativeReplies.lean`: `reply_decision_lift`, `prepare_reply_at`.
- `src/Effect4/Laws/Program/NativeHistory.lean`: `load_at`.
- `src/Effect4/Laws/Program/PlaceFunding/Run.lean` and `History.lean`: `Local`, `zero_allowance`,
  `Holds`, `edits`; `src/Effect4/Laws/Program/PlaceFunding/Commands.lean`: `command_funded`.
- `src/Effect4/Laws/Run/Frame.lean`: `Run.history_keeps`, `Run.HistoryOf`.
- `src/Effect4/Laws/Machine/ForkLedgerInvariant.lean` (through `PlaceFunding`):
  `ForkLedger.Invariant.load_ok`, `Native.driveStep_ok`.
- The case structure of `Commands.step` follows `SourceScope.command_at`
  (`src/Effect4/Laws/Program/NativeCommands.lean`) and `MaskRuns.driveStep_keepsMask`. No lemma of
  theirs states a predicate generic in the fiber, so none could be reused as a term.

## 4. The coordinator's leads, checked

- **Codex's writer probe** (`docs/research/2026-10-11-machine-models/codex/place-writes/`, read):
  `append_debit` and `workers_debit` are local code-to-data exchanges at one fixed environment. They
  serve the writer ledgers' evaluator debit (step 3), not the producer. Its README lists the same
  missing history premises that `NativeFlow.history` now carries generically.
- **Codex's Workers research** (`docs/research/2026-10-10-goals-packet/codex/MachineWorkers*.lean`,
  `2026-10-11-codex-worker-entry-receipt.md`, read): `MachineWorkersSlots` holds a worked crew model.
  Its `World` is the owner and the store. Its `Kind` has the allocation, gate, connection and yield
  classes. Its `Phase` gives the root's initial exclusivity through the owner. It is the recommended
  start for the crews' instance (§5), and it is research, not library.
- **Commit `83a4234e4`** (`HostTimeoutNumberRaceEntry.lean`, not an ancestor of the base): superseded.
  Its own checkpoint note says not to integrate it as the numeric history producer. It was not used.
- **Gemini's reuse census**, section 3 (read): its reuse list matches §3. Its claim that `Lift.lean`
  holds per-arm frame transports does not hold (assumed, reading): it holds the decision fields
  only. `NativeHistory` is `src/Effect4/Laws/Program/NativeHistory.lean`.

## 5. The four goals: standing and what each still needs

Measured with `#plan_status` at `66a9f0256`. The three claims rest on the same goals as at the base.

| Goal | Standing (measured) | In reach? | What it still needs |
| --- | --- | --- | --- |
| `Workers.Assertions.logs_step` | goal | its history step is now generic | (1) the crew's answer-class model and `NativeFlow` facts; (2) the writer ledger and its `LocalOn` facts; (3) the reading from the funded ledger to `LogDebits` |
| `QueueWorkers.Assertions.logs_history` | goal | as Workers | the same three items, with three members and the queue's cells |
| `Timeout.cleanup_keeps` | goal | not yet | a numeric instance at `NativeFlow` (the existing `HostTimeoutNumberFlow.CodeAt` is a candidate model), then the ordered-log reading of `cleanupKeeps` |
| `Timeout.retries_declared` | goal | not yet | the same instance, then the completed-form reading of `retriesDeclared` |

The Workers route, in order (assumed, reading the crew and Codex's model):

1. Adapt `MachineWorkersSlots.World`, `Kind`, `CodeAt` and a saved `Edge` to `FrameFlow`; the
   world is `worldOf state id := ⟨id, state⟩`.
2. Prove `NativeFlow`: the iteration and delivery facts are the bulk (the native evaluator over the
   crew's codes). The structural facts reduce through `FrameFlow.fields` and `FrameFlow.replace`.
   The four store hooks keep the reference and deferred lengths the model reads.
3. The writer ledger `L i`: the count of `nat i` in the `released` cell, a reservation for each
   pending release of acquisition `i`, credits by `ReleaseTrace.releaseAt`. Its debit reuses
   `PlaceFunding.action_debit`, `countdown_debit`, `iteration_debit` and `Evaluation.of_debits`, and
   reads the acquired value and the cell from the flow (`LocalOn`, with `Q := Flows`). The
   `carry` fact follows from `OutsideEdits.prepare`.
4. `logs_step` then follows from `LocalOn.history_funded` with `NativeFlow.decision_lift`.

## 6. Commands and results

All through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh` (two threads), in the worktree.

| Command | Result (measured) |
| --- | --- |
| `lake build Test.Dogfood.Scenario.{Workers,QueueWorkers,Timeout} ProofGraph.{Plan,Why,AxiomAudit}` | passed, 1298 jobs, from the cache |
| `lake env lean <scratchpad>/Frontier.lean` (`#plan_status`, `#goal_impact`, `#why`) | the frontier at the base: the four goals are goals; each blocks no registry claim |
| `lake env lean src/Effect4/Laws/Machine/AnswerFlowRun.lean` | passed after repairs: multiline record syntax, `omit` placement, elaboration order of `_` fibers, a universe split for the world |
| first `lake build … Effect4.Laws` | failed: `fun_cases driveStep` made `driveStep.match_5.congr_eq_1._sparseCasesOn_2`, which `NativeCommands` also makes; the import clashed |
| the same, after `Commands.step` moved to `cases` and `split` | passed, 1071 jobs |
| `lake env lean src/Effect4/Laws/Program/PlaceFunding/Flow.lean` | passed |
| `lake build Effect4.Laws.Machine.AnswerFlowRun Effect4.Laws.Program.PlaceFunding.Flow` (final) | passed, 561 jobs |
| `lake env lean <scratchpad>/FrontierAfter.lean` | §5 |

## 7. Axiom output

`#axiom_audit Effect4.Laws.Machine.AnswerFlowRun Effect4.Laws.Program.PlaceFunding.Flow`, from a
scratchpad file run with `lake env lean`:

- at `b8e78b0e2`: `164 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`
- at `66a9f0256`: `167 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`

## 8. Open obligations, proposals and traps

Open obligations: §5, items 1 to 4, then the two Timeout instances.

Proposed for the coordinator (no register edited here):

- A registry claim `answer-flow-history`, role preservation, concept store-typing R4 with
  reactive-scheduling; pointer `PlaceFunding.NativeFlow.history`; consumers the four goals.
- The claim `place-ledger-history` that seats GOALS and GOALS-2 proposed can point at
  `LocalOn.history_funded`, which generalizes `Local.history_funded`.

Consolidation candidates (not done, to keep merged statements unchanged):

- `Local.decision_lift` and `LocalOn.decision_lift` share their proof shape. Restating `Local`'s at
  `Q := True` needs a decision-lift congruence that the tree lacks.
- `SourceScope.command_at`'s fiber part and `MaskRuns.driveStep_keepsMask` are both per-fiber
  command proofs. Each could become an instance of `Commands.step` with a world-free predicate.

Trap, for the tactic notes: a module outside `NativeCommands`'s import closure must not run
`fun_cases driveStep`. Its auxiliary declaration clashes on import with the one `NativeCommands`
makes. `cases` on the command, `simp only [driveStep]` and `split` avoid it.

Bounded or host-only evidence: none. Everything landed is proved; nothing ran a host.

## 9. Files changed

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Machine/AnswerFlowRun.lean` | new: the producer and the answer-flow instance lemmas |
| `src/Effect4/Laws/Program/PlaceFunding/Flow.lean` | new: the native producer and place funding over a carried invariant |
| `src/Effect4/Laws.lean` | two imports at the end |
| `docs/research/2026-10-13-seat-flow-receipt.md` | this receipt (force-added) |
