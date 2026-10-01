The generic lifts are proved (rerun at `[propext, Quot.sound]`) and the guard re-derivations are real, but the M6 instance says nothing about M6 as the ledger states it: M6's typed state and queue fact say nothing about a resume for a token that is not allocated yet, so `typedState_load` at the one-line program `perform sleep 1` contradicts both five of the 18 per-command obligations and `decision_preserves` at `fire` (both proved). The origin-ledger plan's withdrawal of the M6 claim should stand until M6 carries the guard's `keysBelow` bound.

# Verification of the LIFT seat

Adversarial verifier for the seat `lift`. Base `be15b062`. HEAD is `6f7f6601`, and nothing under
`src/`, `Test/` or `ocaml/` changed since the base (`git diff --name-only be15b062 HEAD` lists only
`AGENTS.md`, `tools/Tools/ArchitectureRoles.lean` and docs). I wrote this note and three probes in
this folder: `verify-steppreserves.lean`, `verify-decision.lean`, `verify-controls.lean`. The
seat's files are untouched. No build, commit or generator run.

Evidence words: **proved** is a kernel-checked theorem. **Finite check** is a `#guard`, or a
meta-level walk run once. **Reading** means I read the code and built no proof.

## 1. What the seat missed: M6's invariant is not an invariant

**The gap.** `QueueOk` types a queued `resume` through `ResumeOk`
(`Typed/Assembly.lean:86-90`). `ResumeOk w target token code` asks for typing only when the world
declares that token (`Typed/Contracts.lean:74-75`). The dispatcher clause of `TypedState` uses the
same `ResumeOk` (generated `TaskOk`; `preds.ResumeOk`, `Typed/Assembly.lean:55`). A world that types
a machine declares no token at or above `nextToken` (`WorldValid.tokenBound`,
`Typed/Validity.lean:25`). So a resume for a token that is not allocated yet is typed vacuously.
The next park allocates that token (`Machine/Fibers.lean:1069-1070`, `:1078-1080`,
`:1115-1116`). The resume then becomes live and delivers whatever code it carries.

The seat saw the other half of this (F4: a resume for a delivered token stays declared). It did
not see the resume for a token that is declared only later.

**Two proofs.** Both use the review's program `sleeper := perform sleep 1`, checked at `unit`,
and `badCode`, the code the answer `success 42` becomes.

- `verify-steppreserves.lean`, `load_and_five_inconsistent` (line 138): `typedState_load` at
  `sleeper` and the five obligations `step_evaluate`, `step_loop`, `step_resume`, `step_finish`,
  `step_drainDue` cannot all hold.
  - At load `nextToken = 0`. The queue `[evaluate root, resume root 0 badCode, drainDue]` is
    `QueueOk` in every world that types the loaded machine (`early_queueOk`, line 115).
  - The loop parks the root at token 0 in its second command, runs the queued resume, and the
    root exits with `success 42` (4 `#guard`s, lines 91-96). The run uses only those five
    commands (`early_runsOnly_five`, line 98, by `decide`).
  - No world types the end machine (`mEnd_not_typed`, line 104).
  - `load_and_steps_inconsistent` (line 172) is the same with all 18: exactly the `steps` premise
    of `m6_decision_preserves`, `m6_decisionLift`, `m6_stepFrame` and `m6_capstone_of_steps`.
- `verify-decision.lean`, `load_and_fire_inconsistent` (line 119): `typedState_load` at `sleeper`
  and the ledger's own `decision_preserves` at `fire root` cannot both hold.
  - Give the loaded root's dispatcher two tasks: `start root`, then `resume root 0 badCode`
    (`mT`, line 36). If the loaded machine is typed in a world, this machine is typed in the same
    world (`mT_typed`, line 78; the resume task is vacuous at token 0, `dT_ok`, line 62).
  - `fire root` runs the start task, which parks the root at token 0. Then it runs the resume
    task, and the root exits with 42 (2 `#guard`s, lines 43-44; `mFired_not_typed`, line 50).
  - `fire` is not an answer. So the premises of `m6_capstone` (load, and `decision_preserves` for
    every decision that is not an answer) cannot all hold at this program. The same goes for
    `m6_capstone_of_ledger` and `m6_capstone_admitted`.

The kernel checks that `LoadAt` and `FireAt` are the ledger's own statements (`example`s at
`verify-steppreserves.lean:133`, `verify-decision.lean:102` and `:113`). The per-command
hypotheses are the tree's `StepPreserves` itself.

**Bound.** Both results are conditional on `typedState_load` at `sleeper`, which is open. If it
failed, M5 would fail at a one-line program. Either way the M5 and M6 obligations as written
cannot all be discharged. I did not prove the load instance: it needs a `TypedProg` derivation
through the sleep protocol (`Typed/Residual.lean:186-222`). The same construction should work for
any program whose run parks (reading).

**The guard already has the missing bound.**
- `GuardState.keysBelow` (`Guard/Core.lean:1066`, defined at `:137-138`) asks every internal key
  to lie below `nextToken`. The keys are the timer and deferred wakes, the due list, races,
  observers and dispatcher tasks (`internalKeys`, `:124-130`).
- The queue fact has the same bound (`GuardQueue.keys`, `:1115`; `ReservedKeys.below`, `:1082`).
- So does the guard's snapshot fact that the seat copied as `guardO` (`Lift.lean:1357-1358`).
  M6's snapshot fact `m6O` (`Lift.lean:725-727`) has no bound.
- `verify-controls.lean` §3 proves the difference on the early queue. The native guard's queue
  invariant is false there (`guard_refuses_early`, line 94). M6's `QueueOk` holds
  (`m6_accepts_early`, line 101).

**What this does to the seat's result.**
- The generic lifts stand. `I` and `O` are already parameters that read the machine, so a
  repaired M6 instance plugs into the same theorems.
- The M6 instance does not "cover M6". It derives M6's statements from premises that cannot all
  hold. The reversal of the plan's §10 withdrawal is premature.
- F2's "the snapshot comes free" rests on `StepPreserves` quantifying over every pending list.
  That quantification is exactly what makes it false today. After a repair the trick should
  carry over, if the repaired obligation still quantifies over every pending list that meets the
  repaired queue fact (reading).
- "No transport lemma for `ResumeOk` is needed" is true of the lift. But it moves the transport
  into each per-command obligation, which must carry `QueueOk` of an arbitrary tail to a later
  world. That transport is false today, for a resume whose token is declared later. With the
  bound it should follow from Θ extension (`World.le`, `Typed/World.lean:131-135`) and
  `M3bWorld.typedProg_mono` (`Typed/Residual.lean:430`, declared, not proved) (reading).

## 2. Verdicts, claim by claim

The seat's own summary ("the lift family is proved and it does cover M6 ... reverses the plan's
withdrawal"): **partly**. The lift family is proved (rerun below). "Covers M6" is refuted by §1.

1. **Command-loop lift, generic; `hostOrder` an instance.** Confirmed. `driveState_lift`
   (`Lift.lean:68`), `driveState_lift_of` (`:95`) and `driveState_keeps` (`:117`) rerun at
   `[propext, Quot.sound]`. The induction follows `driveState` (`Machine/Fibers.lean:1971-1980`),
   whose stuck check matches the `m.stuck = none` premise. `hostOrder` is
   `Typed/Validity.lean:121-122`.
2. **The guard's four hand inductions are one lift at four invariants.** Confirmed. Proved
   (`driverContract_of_lift`, `Lift.lean:696`, typed exactly `DriverContract p table`). A
   dependency walk over the seat's declarations (finite check, §5) shows it reaches none of
   `driverContract`, `driveState_invariants`, `reservedKeys_driveState`,
   `requestOrInterrupted_driveState` or `interruptedAt_driveState`. The walk's positive controls
   pass.
3. **The frame law, with a halt as the one exception.** Confirmed. `driveStep_append`
   (`Lift.lean:182`) reruns at `[propext, Quot.sound]`. I upgraded the seat's native reading to a
   finite check. A host answer naming fiber 7, which does not exist, makes the native evaluator
   join an unknown fiber (`Machine/Fibers.lean:1108`). The machine halts, and a `drainDue` and a
   marker queued behind the answer are dropped (`verify-controls.lean` §1, 4 `#guard`s,
   lines 64-70). Two precisions (reading):
   - In a closed program fiber handles come only from forks, so natively this halt needs a
     host-supplied handle.
   - Not every halt drops the tail: `drainOwed`'s `postTask` on an unknown owner halts and keeps
     it (`Machine/Fibers.lean:685-692`, `:1804-1813`, `:1962-1965`). The frame law's first
     disjunct covers that case.
4. **A fire holds a snapshot outside machine and queue; for M6 it comes free; no `ResumeOk`
   transport needed.** Partly.
   - The need for `O` is right (`Machine/Fibers.lean:2009-2016`). `Guarded` and `m6_stepFrame`
     (`Lift.lean:801`) are proved.
   - "Comes free" uses the very quantification that makes `StepPreserves` false (§1).
   - The guard's `guardO` carries `ReservedKeys.below`; `m6O` dropped it.
5. **The decision lift, 13 fields, exhaustive.** Confirmed. `stepDecisionState_lift`
   (`Lift.lean:496`) reruns at `[propext, Quot.sound]`. I checked the edits against
   `stepDecisionState` (`Machine/Fibers.lean:2084-2113`), `fireState` (`:2009-2016`) and
   `advanceState` (`:2039-2053`): every write outside the loop has a field. `parkedAt_em` has no
   axioms. The 13 fields are satisfiable: the guard fills them all (`guard_decisionLift`).
6. **The answer premise must hold after the `resume`.** Confirmed. `guardQueue_refuses_live_answer`
   (`Controls.lean:35`) reruns. `GuardQueue.keys` is `Guard/Core.lean:1115` and
   `ReservedKeys.disjoint` is `:1083`. The guard runs that command by hand in
   `guardState_answerDrive` (`AnswerDecision.lean:94-112`).
7. **M6's inert answers go around the queue.** Confirmed as a reading, with the proved parts
   `inert_resume` (`Lift.lean:335`) and `answer_of_split` (`:369`). The definitions are as the seat
   says (`Typed/Assembly.lean:80-84`, `Typed/Contracts.lean:74-75`, `Typed/Validity.lean:17-18`).
   Missed: the dual case of §1.
8. **The world follows the store; `clockNone` widened.** Confirmed (reading).
   `WorldValid.state : w.state = m.state` (`Typed/Validity.lean:27`). The store order admits clock
   edits (`Stores.le`, `Laws/Machine/StoresLaws.lean:43-50`), so the widened premise is
   satisfiable in principle.
9. **`decision_preserves` follows from the 18 plus eight edits; two edits proved; statements
   kernel-checked.** Partly.
   - Confirmed: the implication `m6_decision_preserves` (`Lift.lean:950`) and the statement checks
     (the `example`s at `:782`, `:944`, `:990`). `m6_ran` and `m6_middleware` are real: the
     generated `RunMachineOk` reads only fibers, races and the store (I printed it), and
     `WorldValid` adds the token counter.
   - Refuted as a result about M6: its `steps` premise contradicts `typedState_load` at `sleeper`
     (§1). Q2's proposal to replace `decision_preserves` by the six edits moves the same defect
     into the 18.
10. **The M6 repair holds.** Partly.
    - Confirmed: `m6_capstone` (`Lift.lean:1016`), `m6_capstone_of_steps` (`:1034`),
      `m6_capstone_admitted` (`:1101`) and `noAnswer_admitted` (`:1092`) are proved implications.
      `LoadStmt root rootTy fuel fuel` is the right instance, since `replayR` loads with
      `compileFuel := fuel` (`Laws/Program/RuntimeR.lean:51-55`).
    - Refuted as "the repair holds": `load_and_fire_inconsistent` shows its two premises cannot
      both hold at `sleeper`. Restricting reachability to answer-free tapes is not enough. The
      repaired capstone statement may well be true, but this route does not reach it until the
      typed state gets the bound.
11. **Today's capstone is false; the review's counterexample reproduced.** Confirmed.
    `current_capstone_false` (`Controls.lean:111`) and `reviewTape_refused` (`Lift.lean:1117`)
    rerun. The seat's C4 statement is hand-copied. I checked with the kernel that it is the
    ledger's `typedState_reachable` at that instance (`verify-controls.lean:86`).
12. **Trace agreement with today's origin field: four edits at once, four `update` edits need
    distinct ids.** Confirmed (finite check and reading, as the seat says). `update` replaces
    every fiber with the id (`Machine/Fibers.lean:622-624`). `modify`, the drain, the interrupt
    record and `postTask` all go through it (`:634-638`, `:2016`, `:2106`, `:685-692`). Only the
    yield edit has a `#guard`; the other three are the same mechanism by reading.
13. **The trace agreement is an instance at every level.** Confirmed. `ledger_driveState`,
    `machineFact_stepDecision`, `ledger_stepDecision` and `reachable_agrees_of` rerun at
    `[propext, Quot.sound]`. The `example`s at `Lift.lean:1332` and `:1340` compile against
    `M1Trace.step_agrees` and `reachable_agrees` (`Laws/Api/TraceOrigin.lean:12-22`). The `load`
    premise matches `M1Trace.load_agrees` (`Laws/Api/Supervision.lean:1004`) by reading; no
    `example` checks that one.
14. **The guard's decision and run results are exact instances, without `driverContract`.**
    Confirmed. Proved, and the dependency walk shows that `guard_decisionLift`,
    `guardState_steppedBy_of_lift` and `guardState_reachable_of_lift` reach none of
    `driverContract`, `guardState_steppedBy`, `guardState_reachable`, `guardState_executePrefix` or
    `driveState_invariants`. `guard_decisionLift` does not even reach the `DriverContract`
    structure. The tree's own `guardState_steppedBy` does reach `driverContract`
    (`Guard/Decision.lean:11-34`), which the walk also sees.
15. **The book is not an instance.** Confirmed (reading). `StepAgrees` and `book_driveState`
    relate two named runs in lockstep (`Laws/Machine/Book.lean:694-735`). An existential later
    world loses which machine is on the right. Neither of us tried an encoding that carries the
    right-hand run in the world.

The seat's counts check out: `Lift.lean` prints 71 axiom lines (57 `[propext, Quot.sound]`, 7
`[propext]`, 7 none), with 5 statement `example`s; `Controls.lean` has 6 theorems and 10 `#guard`s.

## 3. Proposals

**R1. Give M6 the guard's bound before landing any M6 lift (amends the seat's P2).** The shapes,
not compiled:

```lean
-- the guard's key lists read no code; generalize them over κ and reuse them for RState
def InternalKeysBelowR (m : RState) : Prop := ∀ k ∈ internalKeysR m, k.2 < m.nextToken
def QueueFresh (m : RState) (cmds : List RCmd) : Prop :=
  ∀ k ∈ cmds.flatMap commandKeysR, k.2 < m.nextToken

-- TypedState gains the bound; the queue fact reads the machine, as GuardQueue does
def StepPreserves' (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, TypedState root rootTy w m → InternalKeysBelowR m →
    QueueOk root w (cmd :: rest) → QueueFresh m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 ∧ InternalKeysBelowR r.1 ∧
      QueueOk root w' r.2 ∧ QueueFresh r.1 r.2

-- the snapshot fact, as guardO has it
def m6O' (root : ProgramSource) (w : Typed.World) (m : RState) (ts : List RTask) : Prop :=
  QueueOk root w (ts.flatMap taskCmds) ∧ ∀ k ∈ ts.flatMap taskKeysR, k.2 < m.nextToken
```

The two counterexamples fail these at once: token 0 is not below `nextToken = 0`. One park
reuses an old token, `registrationDone` (`Machine/Fibers.lean:1903`). Its token is declared from
the race's creation (`RaceOk`, `Typed/Assembly.lean:57`), so the bound is enough there (reading).
The guard proves the same bound for the same `driveStep` code on the native machine, which is a
place to start.

**R2. Keep the plan's withdrawal of the M6 claim** until R1 lands. Register the two
counterexamples when the declarations change; the coordinator assigns ids.

**R3. Land the generic family (the seat's P1).** Agreed. The guard re-derivations, checked
independent of the hand inductions, show it is usable. P3 and P4 are harmless.

## 4. Open questions

- Q1 (owner): which repair closes M6? (a) The bound of R1, which mirrors the guard and keeps the
  obligations over all typed machines. (b) Obligations over reachable machines only, with
  reachability carried in the invariant, as `reachable_agrees_of` does. Recommendation: (a). The
  per-command level has no notion of reachability for machines in the middle of a decision, and
  the guard already carries (a).
- Q2: prove `typedState_load` at `sleeper`, which makes both refutations unconditional (M5 work).
- Q3: does M6 need the bound on every place that stores a token? The guard's `internalKeys` covers
  observers and races but not `f.pending`, whose M6 clause asks for a declaration for some fiber
  (`preds.PendingOk`, `Typed/Assembly.lean:53`). Reading only.
- Side note for the host-answers lane: a host answer naming a fiber that does not exist halts the
  native machine (`verify-controls.lean` §1). That is a second failure beside the host-answers
  note's wrong-type fiber handle. Path A there refuses it too (reading).

## 5. Commands and results

Every Lean run went through the lock. Paths are repository-relative;
`serial.sh` is `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh`.

| Run | Exit | Result |
| --- | --- | --- |
| `bash serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/lift/Lift.lean` | 0 | 71 axiom lines, identical to `lift.log` (`diff` empty) |
| same, `Controls.lean` | 0 | 6 axiom lines, identical to `controls.log`; 10 `#guard`s pass |
| same, `verify-steppreserves.lean` | 0 | 7 theorems, all `[propext, Quot.sound]`; 4 `#guard`s; 1 statement `example` |
| same, `verify-decision.lean` | 0 | 5 theorems, all `[propext, Quot.sound]`; 2 `#guard`s; 2 statement `example`s |
| same, `verify-controls.lean` | 0 | 2 theorems, both `[propext, Quot.sound]`; 4 `#guard`s; 1 statement `example` |
| `bash serial.sh bash -c 'cat docs/research/2026-09-30-pass/lift/Lift.lean <scratchpad>/verify-lift/depcheck.lean \| lake env lean -M6144 -DwarningAsError=true --stdin'` | 0 | 16 dependency checks as expected: 4 positive controls true, 12 negatives false |

Axiom output of my probes:

```text
Research.Pass.LiftVerify.drive_of_steps_on             [propext, Quot.sound]
Research.Pass.LiftVerify.early_runsOnly_five           [propext, Quot.sound]
Research.Pass.LiftVerify.mEnd_bad_exit                 [propext, Quot.sound]
Research.Pass.LiftVerify.mEnd_not_typed                [propext, Quot.sound]
Research.Pass.LiftVerify.early_queueOk                 [propext, Quot.sound]
Research.Pass.LiftVerify.load_and_five_inconsistent    [propext, Quot.sound]
Research.Pass.LiftVerify.load_and_steps_inconsistent   [propext, Quot.sound]
Research.Pass.LiftVerify.Decision.mFired_bad_exit      [propext, Quot.sound]
Research.Pass.LiftVerify.Decision.mFired_not_typed     [propext, Quot.sound]
Research.Pass.LiftVerify.Decision.dT_ok                [propext, Quot.sound]
Research.Pass.LiftVerify.Decision.mT_typed             [propext, Quot.sound]
Research.Pass.LiftVerify.Decision.load_and_fire_inconsistent [propext, Quot.sound]
Research.Pass.LiftVerify.Controls.guard_refuses_early  [propext, Quot.sound]
Research.Pass.LiftVerify.Controls.m6_accepts_early     [propext, Quot.sound]
```

Notes on the runs:
- The dependency walk (`depcheck.lean`, in the scratchpad, fed after the seat's file on stdin so
  the seat's file stays unchanged) first came back all false. Its positive control failed,
  because in this toolchain `ConstantInfo.value?` hides theorem bodies unless
  `allowOpaque := true`. Fixed and rerun; the table row is the fixed run.
- Scratch probes not kept (scratchpad only): the command trace of the early queue (evaluate,
  loop, resume at token 0, evaluate, loop, finish, drainDue, drainDue); the root's stack at the
  park (`asyncFinalizer`, `answer`); the printed generated predicates `RunMachineOk`,
  `RunFiberOk`, `StoresOk`, `DispatcherOk`, `BucketOk` and `TaskOk`.
- Bounds: the oleans are those built at `be15b062`. My two refutations are conditional on
  `typedState_load` at `sleeper` (§1). The dependency walk is a finite meta-level check, not a
  proof.
