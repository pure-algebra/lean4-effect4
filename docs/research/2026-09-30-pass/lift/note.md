The lift family is proved and it does cover M6: `decision_preserves` follows from the 18 per-command obligations plus six small edit facts, and the repaired capstone follows from `typedState_load` and `decision_preserves`; the same lifts re-derive the guard's `DriverContract` and `guardState_steppedBy` from lemmas the guard already has. Every theorem is at `[propext, Quot.sound]` or less.

# LIFT seat: one lift for facts every step keeps

Base `be15b062`, branch `refactor/phase1-phase3`. Seat folder `docs/research/2026-09-30-pass/lift/`.
Nothing outside this folder was edited. No build, commit or generator run.

Files:
- `Lift.lean`: the lifts and the three instances (71 theorems). One file, because probe files
  cannot import each other. Its sections follow the four tasks.
- `Controls.lean`: red controls (6 theorems, 10 `#guard`s).
- `lift.log`, `controls.log`: the fresh final runs, with axiom output and exit codes.

Evidence words: **proved** means a kernel-checked theorem in these files. **Finite check** means
a `#guard` on one concrete machine. **Reading** means I read the code and built no proof.

This reverses one withdrawal in the origin-ledger plan (§10: "the world-indexed helper shape and
every claim that the tool covers M6"). The plan review's three objections are each met by a named
premise: the queue (`I` over the pending list, and the snapshot fact `O`, F2), answer admission
(the admission `A` and the answer premise, F4), and the reference machine (the lifts are generic
in the evaluator, and M6 is instantiated at `termEvaluatorFor`, §2).

## 1. Findings

**F1. One induction, four times.** The guard proves its loop contract by four hand inductions
on fuel (`Guard/Driver.lean:18-99`). They are one lift at four invariants
(`driverContract_of_lift`). Proved.

**F2. A `fire` decision holds tasks outside the machine and the queue.** `fireState` drains the
owner's dispatcher and folds over the drained tasks (`Machine/Fibers.lean:2009-2016`). While one
task's loop runs, the rest of that snapshot is in neither the machine nor the pending list. So
the decision lift needs a snapshot fact `O`, carried through every command beside the queue
fact `I` (`Guarded J I O ts`, `Lift.lean:209`). Proved as part of `stepDecisionState_lift`.
- The guard already carries exactly this: its fold keeps the snapshot's keys reserved
  (`OuterDriver.lean:95-110`). `guardO` is that fact.
- For M6 it comes free (`m6_stepFrame`, `Lift.lean:801`). Each `StepPreserves` quantifies over
  the whole pending list, so the snapshot's commands ride as a suffix of it, and the frame law
  gives back the step on the shorter list. No world-transport lemma for `ResumeOk` is needed;
  it has none (`Typed/Contracts.lean:71-75`). Proved.

**F3. The frame law.** For every command, `driveStep` on `rest ++ s` gives the same machine as on
`rest`, and the old residue followed by `s`. The one exception is a halt: `settle`'s stuck arm
returns `[]` and drops everything (`Machine/Fibers.lean:1798-1799`). Proved generically
(`driveStep_append`). Control C2 shows the halt case happens: with an evaluator whose iteration
halts, the suffix is dropped (finite check). The native evaluator reaches the same arm through a
join on an unknown fiber (`Machine/Fibers.lean:1108`; reading).

**F4. The answer premise must hold after the answer's `resume`, not at the loop entry.**
- Guard: its queue invariant is false at `[resume id token code, drainDue]` whenever the answer
  targets a live request. A queued `resume` carries its own key (`commandKeys`,
  `Guard/Core.lean:873-876`), and reserved keys must avoid live requests
  (`ReservedKeys.disjoint`, `:1083`). Proved in `Controls.lean` as
  `guardQueue_refuses_live_answer`. The guard runs that first command by hand
  (`AnswerDecision.lean:94-112`), and `DecisionLift.answer` states exactly that shape.
- M6: `AnswerOk` asks for typing only when the fiber is parked at that token
  (`Typed/Assembly.lean:80-84`). `QueueOk` asks it of every queued `resume` whose token the
  world declares (`ResumeOk`, `Typed/Contracts.lean:74-75`), and a delivered token stays declared
  ("Historical token entries remain after delivery", `Typed/Validity.lean:17-18`). So an inert
  answer to a delivered token can put a `resume` in the queue that is not `QueueOk`. That
  `resume` is a no-op (`inert_resume`, proved; `Machine/Fibers.lean:1838-1851`), and
  `answer_of_split` routes around it, so `AnswerOk` is enough. The failing `QueueOk` itself is a
  reading: I did not build a typed world to show it.

**F5. A store edit may need a later world.** M6's world follows the store exactly
(`WorldValid.state : w.state = m.state`, `Typed/Validity.lean:27`). My first draft asked the
`clockStep` edit to keep the invariant at the same world, which M6 cannot meet. The premise now
allows a later world (`DecisionLift.clockNone`). Found while stating M6's edits; the fix is
proved through.

**F6. `decision_preserves` is the 18 command obligations plus eight edits, two of them proved.**
The edits a decision makes outside the command loop are: the dispatcher drained and disarmed
(`Machine/Fibers.lean:2015-2016`), the `ranTask` event (`:2003`), `yieldVerdict`'s modify
(`:2090-2091`), the interrupt record (`:2098-2106`), the middleware latch (`:2108`), `clockStep`
with and without a due sleep (`:2045-2048`), and answer preparation (`:2096-2097`).
`TypedState` reads only the fibers, races, store and token counter (`RunMachineOk`, generated at
`Typed/State.lean:26`; `WorldValid`, `Typed/Validity.lean:19-34`). So the trace and latch edits
are immediate (`m6_ran`, `m6_middleware`; proved). Six remain as `M6Edits`
(`Lift.lean:849-870`): drain, yield, interrupt record, `clockStep` none, `clockStep` some, and
answer preparation. The answer fact needs typing only when parked. The reference interpreter
keeps the default `prepareAnswer` (no such field in `InterpR.lean:287-384`), so that fact is a
leaf typing fact at the same world (reading).

**F7. The M6 repair.** `isAnswer`, `RReachableNoAnswer` and `m6_capstone` (`Lift.lean:960-1030`).
From `typedState_load` at `compileFuel := fuel` (what `replayR` loads with,
`Laws/Program/RuntimeR.lean:51-54`) and `decision_preserves` for decisions that are not answers,
every machine an answer-free tape reaches is typed. Proved, with every hypothesis explicit.
`m6_capstone_of_steps` takes load, the 18 and `M6Edits` instead. Control C4 reproduces the plan
review's counterexample to today's capstone (`current_capstone_false`, proved), and
`reviewTape_refused` shows its tape is outside the repaired reachability (proved by `decide`).
- The typed layer is one theorem away. With `decision_preserves` as the ledger states it,
  `m6_capstone_admitted` says every machine reached by a tape whose applied answers meet
  `AnswerOk` is typed. The no-answer repair is its special case (`noAnswer_admitted`). Proved.

**F8. The trace agreement, with today's origin field.** Of the eight edits, four keep `Agrees` at
once (`agrees_ran`, `agrees_state` for both store edits, `agrees_middleware`; proved). The other
four are exactly the edits that rewrite a fiber with `update`: drain, yield, the interrupt
record, and the owed resume a due sleep posts (`AgreesUpdates`, `Lift.lean:1290`). Control C3
shows one of them breaking the agreement on a machine whose fiber ids repeat, because `update`
replaces every fiber with that id (finite check). So with today's field these four need
distinct ids, a fact of reachable machines. With the fork ledger off the fiber, `update` cannot
reach the record. This is the ledger plan's reason, now located at four named edits.

**F9. The guard's decision level is an exact instance.** `guard_decisionLift` fills every field
of `DecisionLift` from a lemma the guard already has (`clearDispatcher_preserved`,
`taskCmds_guardQueue`, `guardState_interruptBeforeLoop`, `clockStep_preserved`,
`clockStep_owed_facts`, `guardState_driveStep_resume`, `guardQueue_resume_from_tail` and the
rest). It does not use `driverContract`. Proved.

**F10. The book is not an instance.** `StepAgrees` and `book_driveState` relate two machines run in
lockstep (`Laws/Machine/Book.lean:694-735`). An existential later world cannot say that the
right-hand machine is the other instance's `driveState`. The book stays its own relational
lift. Reading.

**F11. A classical trap.** `by_cases` on the parking condition (an existential) reached
`Classical.choice`, and `#print axioms` showed it. `parkedAt_em` decides the condition by cases
on the fiber table. Not kept as a fixture, because a theorem with that axiom breaks this pass's
rule.

## 2. What is proved

Everything in `Lift.lean` is generic in the machine's types, its `FiberCore` and
`FiberEvaluator` instances and the interpreter. The world relation is the tree's own
`WorldOrder` (`Laws/Effects/Protocol.lean:30`), which bundles reflexivity and transitivity.
M6's `World.leHost` is already an instance of it (`hostOrder`, `Typed/Validity.lean:121`).

| Task | Theorem | What it says | `Lift.lean` |
| --- | --- | --- | --- |
| 1 | `driveState_lift` | one fact per command gives the fact for `driveState` at every fuel, at a later world | 68 |
| 1 | `driveState_lift_of` | the same with the brief's exact premise (no stuck guard) | 95 |
| 1 | `driveState_keeps`, `driveState_keeps_of_keeps` | the equality (`Keeps`) form, for any projection | 117, 126 |
| 1 | `driveStep_append` | the frame law (F3) | 182 |
| 2 | `stepDecisionState_lift` | every decision keeps `J`, from the premise bundle `DecisionLift` | 496 |
| 2 | `answer_of_split` | the answer premise from a parked/not-parked split | 369 |
| 3 | `foldl_lift`, `reachable_lift` | a whole native history (`Guard.Reachable`) | 551, 1138 |
| 3 | `replayEval_lift`, `rreachable_lift` | a whole reference replay (`RReachable`) | 599, 1052 |
| 3 | `m6_capstone` | the repaired capstone, from load and `decision_preserves` | 1016 |
| 3 | `m6_capstone_admitted` | the typed-layer capstone: tapes whose answers are admitted | 1101 |
| 4 | `driverContract_of_lift` | the guard's `DriverContract`, all four fields | 696 |
| 4 | `guardState_steppedBy_of_lift`, `guardState_reachable_of_lift` | the guard's decision and run results | 1440, 1448 |
| 4 | `m6_stepKeeps`, `m6_steps_of_ledger` | M6's 18 `step_*` obligations are exactly the loop premise | 730, 740 |
| 4 | `m6_decision_preserves` | `decision_preserves` from the 18 and `M6Edits` | 950 |
| 4 | `ledger_driveState`, `ledger_stepDecision` | the trace agreement as a `Keeps`, loop and decision | 1191, 1256 |
| 4 | `reachable_agrees_of` | `M1Trace.reachable_agrees` from `load_agrees` and `step_agrees` | 1319 |

The kernel also checks that my copied statements are the ledger's own. Each `example` assigns
the tree's obligation to `ProofGraph.Obligation` of my statement: `M6Ledger.step_resume`
(`Lift.lean:782`), `M6Ledger.decision_preserves` (`:944`), `M3bAssembly.typedState_load`
(`:990`), `M1Trace.step_agrees` (`:1332`) and `M1Trace.reachable_agrees` (`:1340`).

## 3. Mismatches, exactly (task 4)

| Statement | Instance of | Mismatch |
| --- | --- | --- |
| `DriverContract` (`Guard/Contract.lean:9-29`) | `driveState_lift_unit` at four invariants | none |
| `guardState_steppedBy` (`Guard/Decision.lean:11-34`) | `stepDecisionState_lift` | none, once the answer premise is stated after the `resume` (F4) |
| `StepPreserves` (`Typed/Assembly.lean:93-97`) | `StepKeeps` at `TypedState ∧ QueueOk`, order `hostOrder` | none; it asks more than needed, since the loop never runs a command on a halted machine (`Machine/Fibers.lean:1977`) |
| `decision_preserves` (`:218-222`) | `stepDecisionState_lift` | needs six edit facts the ledger does not list (F6); inert answers go around the queue (F4); store edits move the world (F5) |
| `typedState_reachable` (`:225-227`) | `replayEval_lift` | false as stated (C4); proved for answer-free tapes (F7) |
| `M1Trace.step_agrees`, `reachable_agrees` | `foldl_lift` at `Reachable ∧ Agrees` | `step_agrees` carries a reachability premise, so the invariant carries `Reachable`; the four `update` edits need distinct ids today (F8) |
| per-command trace agreement as a `Keeps` | `driveState_keeps_of_keeps` | the lift uses one direction only; the `Keeps` also keeps disagreement |
| `book_driveState` | none | relational (F10) |

## 4. Proposals

P1. **Land the generic family** as `src/Effect4/Laws/Machine/Lift.lean` in the Laws graph. It
imports `Laws/Machine/Approximation`, `Laws/Machine/Keeps` and `Laws/Effects/Protocol`. The core
signatures, as proved:

```lean
def StepKeeps (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop) : Prop :=
  ∀ w m c rest, m.stuck = none → I w m (c :: rest) →
    ∃ w', o.le w w' ∧ I w' (driveStep interp m c rest).1 (driveStep interp m c rest).2

theorem driveState_lift (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (step : StepKeeps o interp I) :
    ∀ (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
      (cmds : List (Cmd ν σ β ε δ ι α κ)), I w m cmds →
      ∃ w', o.le w w' ∧ I w' (driveState interp fuel m cmds).1 (driveState interp fuel m cmds).2

theorem driveStep_append (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (c : Cmd ν σ β ε δ ι α κ)
    (rest s : List (Cmd ν σ β ε δ ι α κ)) :
    Framed s (driveStep interp m c rest) (driveStep interp m c (rest ++ s))

theorem stepDecisionState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (d : RunDecision ν σ β ε δ ι α)
    (hj : J w m) (ha : A w m d) :
    ∃ w', o.le w w' ∧ J w' (stepDecisionState interp fuel m d).1

theorem replayEval_lift (o : WorldOrder W) (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop)
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (pres : ∀ w m d, m.stuck = none → J w m → A w m d →
      ∃ w', o.le w w' ∧ J w' (stepDecisionState interp fuel m d).1) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      J w m → AdmittedReplay J A interp fuel m tape →
      ∃ w', o.le w w' ∧ J w' (replayEval interp fuel tape m).machine
```

`DecisionLift` (`Lift.lean:239-289`) has 13 fields: `step` (commands, with the snapshot), `nil`,
`evaluate`, `drain`, `ran`, `task`, `skip`, `yield`, `interrupt`, `middleware`, `clockNone`,
`clockSome` and `answer`. `foldl_lift` and `reachable_lift` go beside `Guard.Reachable`
(`Guard/Core.lean:31-34`). The frame law's proof uses one `first | …` over three closers; a
`src/` landing restates it arm by arm, as the tree's rule for `src/` asks.

P2. **Repair M6 by building beside.** In `Typed/Assembly.lean`, add these beside the current
definitions, move the capstone, then delete the old one:

```lean
def RunDecision.isAnswer : RunDecision ν σ β ε δ ι α → Bool
  | .answerAsync _ _ _ => true
  | _ => false

def RReachableNoAnswer (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (∀ d ∈ tape, d.isAnswer = false) ∧ m = (replayR root.program fuel tape).machine

structure M6Edits (root : ProgramSource) (rootTy : EffTy) : Prop  -- six fields, Lift.lean:849-870

theorem decision_preserves_of (steps : ∀ cmd, StepPreserves root rootTy cmd)
    (edits : M6Edits root rootTy) (fuel : Nat) (d : Api.Decision) :
    ∀ w m, TypedState root rootTy w m → AnswerOk w m d →
      ∃ w', w.leHost w' ∧ TypedState root rootTy w'
        (letI := termEvaluatorFor root.program
         stepDecisionState (interpR root.program) fuel m d).1
```

The six `M6Edits` fields become ledger obligations beside the 18. The counterexample is
registered when the declaration changes; the host-answers note proposes `E4-SCHED-CE-015`.

P3. **An optional weakening.** `StepPreserves` can take `m.stuck = none →`. The loop never runs a
command on a halted machine (`Machine/Fibers.lean:1977`), and the lift never asks for it.

P4. **The fork-ledger user.** Its decision-level list is the per-command `Keeps` plus the four
`update` edits of F8. Once the ledger lands, restate `AgreesUpdates` against it; the four should
then hold on every machine. `reachable_agrees_of` already gives `M1Trace.reachable_agrees` from
`load_agrees` and `step_agrees`.

## 5. Open questions

Q1 (owner). **Which admission does the typed guarantee state?** `AdmittedReplay` asks each
applied answer to meet `AnswerOk` in every world that types the machine it meets. That is sound
and composes (`m6_capstone_admitted`). But a host cannot compute worlds, and the link from the
runtime check (`admitAnswer`) to this is the external lane's X1/X4 work. The other option is a
run relation that carries the world explicitly. Recommendation: state M6 now over
`RReachableNoAnswer` (host-answers note, decision 1), and keep `RReachableAdmitted` as the target
the external lane proves its admission check into.

Q2 (coordinator). Keep `decision_preserves` as a ledger obligation, now derived by the lift, or
replace it by the six edits. Recommendation: replace it, and keep the derived theorem.

Q3. Where `isAnswer` lives: on `RunDecision` in `Machine/Fibers.lean`, or in the laws.

Q4. `M6Edits.drain` asks for the drained tasks' commands to be `QueueOk`. That should follow from
the generated dispatcher clause of `TypedState`, which uses the same `ResumeOk`
(`preds.ResumeOk`, `Typed/Assembly.lean:55`). Reading only.

Q5. Whether the book should get the relational form of the same family (decision and replay
lifts over a relation), to replace `book_stepDecisionState` and `book_replayEval`. Not tried.

## 6. Commands and results

Every Lean run went through the one-compiler lock. Both runs below were fresh, at the end.

```text
bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/lift/Lift.lean
  exit 0; 71 theorems: 57 at [propext, Quot.sound], 7 at [propext], 7 with no axioms;
  no sorryAx, no Classical.choice (lift.log)
bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true docs/research/2026-09-30-pass/lift/Controls.lean
  exit 0; 6 theorems, 5 at [propext, Quot.sound] and 1 with no axioms; 10 #guards pass (controls.log)
```

Only `[propext]`: `settle_append`, `reviewTape_refused`, `evaluateTape_admitted`,
`ledgerAgrees_originForks`, `agrees_ran`, `agrees_state`, `agrees_middleware`. No axioms:
`stuck_none_of_not`, `not_isSome_of_none`, `isSome_of_ne_none`, `framed_append`, `parkedAt_em`,
`foldl_lift`, `admitted_true`, and `Controls.badTape_applies_answer`. Every other theorem: `[propext, Quot.sound]`.

Along the way, not kept: an import-timing probe (2.1 s for the three law roots), a scratch of the
frame law, and a scratch showing that `TypedState` is not definitionally blind to the trace (its
generated `RunMachineOk` is a structure over the whole machine). That is why `m6_ran` rebuilds
the structures field by field.

Bounds: the probes use the oleans built at `be15b062`. The M6 obligations themselves (the 18,
the six edits, `typedState_load`) stay open; the lifts only derive from them. The fork ledger
does not exist yet, so `LedgerAgrees` is stated for any ledger projection.
