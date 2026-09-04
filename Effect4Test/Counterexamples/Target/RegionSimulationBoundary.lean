import Effect4Test.Semantics.RegionSimulationContract
import Effect4Test.Flow.RegionRunnerContract

/-!
Kernel witnesses for `E4-TARGET-CE-019` through `E4-TARGET-CE-021`.

**Spike S4 inverted the first three groups.** The compile repairs P1 (one scope
per region, every release seeing the same closing exit) and P2 (a live frontier
compiles to a live `Prim.suspend`, never to an exit) are in
`Effect4/Semantics/RegionSimulation.lean`, so every theorem that used to read
`machineAt … ≠ runnerAt …` now reads `machineAt … = runnerAt …`. The fixtures
are retained unchanged — they are the attack, and the attack is what the repair
has to survive.

What is **not** closed, and is stated here as a live divergence rather than
quietly dropped:

* the *classification* half of `E4-TARGET-CE-020`/`-021` (T8): a tape mismatch
  is a refusal on the runner side and a live suspension on the machine side, and
  the masked trace cannot tell them apart. `mismatched_decision_is_refusal` and
  `mismatched_decision_machine_is_live` pin both readings.
**Spike S4b inverted the fourth group.** S4 left one divergence, the
`leaveConfig` obligation: `tapeAfterRegion` is a region body that consumes a
decision, followed by a decision after the region, and S4's compile resumed the
region's continuation with the tape held at the *enter*, so it re-read a
consumed decision and stopped, while the runner continues with the tape it holds
at the *leave*. S4b repaired the compile — `regionInterp.contA` resumes at
`Effect4.RegionSimulation.leaveConfig` — so `tapeAfterRegion_diverges` is gone
and `tapeAfterRegion_agrees` stands in its place, and
`unrestricted_finite_agreement_false` is gone with it: no refutation of the
unrestricted **trace** equation is offered any more. `AllFiniteInputsAgree` is
retained as the `Prop` naming what T5 in general still owes, and
`unrestricted_finite_classification_false` is what survives — the *endpoint*
half, refuted by the refusal witness.

The existing fallible-release fixture remains in RegionRunnerContract.
-/

namespace Effect4Test.Counterexamples.Target.RegionSimulationBoundary

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4
open Effect4.RegionSimulation
open Effects.Trace (Val)
open Effect4Test.Semantics.RegionSimulationContract
  (alphabet service nameOf admit? answerOf rblock rregion regionFlow vars
   opAcquire opRelease regionBothSucceed)

def runnerAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option Effect4.Trace.Log :=
  (admit? raw).map fun flow => Effects.Trace.project finalizerAndOutcomeMask
    (((Flow.runRegions fuel flow service nameOf tape (.nat 5)).run []).2)

def runnerResultAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option (Flow.RunResult × Flow.Tape) :=
  (admit? raw).map fun flow =>
    (((Flow.runRegions fuel flow service nameOf tape (.nat 5)).run []).1)

def machineAt (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) :
    Option Effect4.Trace.Log :=
  (admit? raw).map fun flow => traceOfRun (FrameFiber.run
    (regionInterp alphabet flow.flow (statelessOracle alphabet flow.flow answerOf))
    (regionBound fuel) (FrameFiber.start (compileAt alphabet flow.flow
      ⟨fuel, flow.flow.entry, [.nat 5], tape⟩))).2

/-- Whether the machine is still running when its fuel is spent: `true` is a
live DB-04 frontier, `false` an exit. P2's receipts read this, because an empty
masked trace alone cannot tell "still running" from "finished silently". -/
def machineIsLive (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) : Option Bool :=
  (admit? raw).map fun flow =>
    match (FrameFiber.run
        (regionInterp alphabet flow.flow (statelessOracle alphabet flow.flow answerOf))
        (regionBound fuel) (FrameFiber.start (compileAt alphabet flow.flow
          ⟨fuel, flow.flow.entry, [.nat 5], tape⟩))).1 with
    | .running _ => true
    | .finished _ => false

-- E4-TARGET-CE-019 reuses the existing E4-FLOW-CE-019/020 witness.
abbrev failingRelease := Effect4Test.Flow.RegionRunnerContract.releaseFails

theorem failingRelease_admitted : (admit? failingRelease).isSome = true := by rfl

/-- The runner gives both releases of the one scope the same closing exit. -/
theorem same_scope_closing_exit : runnerAt failingRelease 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
      .done (.failure (.str "boom"))] := by rfl

/-- **P1, the repaired reading.** So does the compile. Before the repair the
machine wrote `finalizer 1 (failure "boom")` for the second release, because a
failing release's exit was threaded into the exit the next release observed
through `Exit.restoreAfterFinalizer`. rc.112 closes one scope with
`exitAsVoidAll` (`internal/effect.ts:3815-3827`) and never does that. -/
theorem repaired_frames_use_original_exit : machineAt failingRelease 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
      .done (.failure (.str "boom"))] := by rfl

/-- `E4-TARGET-CE-019`'s repair column, as an equation. -/
theorem failing_release_agrees :
    machineAt failingRelease 20 [] = runnerAt failingRelease 20 [] := by rfl

-- Positive control: the same two registrations, both releases succeeding.
def successfulReleases : RegionFlow String :=
  { failingRelease with blocks := failingRelease.blocks.map fun block =>
      { block with term := match block.term with
          | .acquire operation request _ target args =>
              .acquire operation request opRelease target args
          | term => term } }

theorem successfulReleases_admitted : (admit? successfulReleases).isSome = true := by rfl

theorem successful_scope_control : runnerAt successfulReleases 20 [] = some
    [.finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
      .done (.success (.nat 5))] := by rfl

theorem successful_frames_control :
    machineAt successfulReleases 20 [] = runnerAt successfulReleases 20 [] := by rfl

-- E4-TARGET-CE-020: source fuel must stop with live work, not an empty cause.
theorem source_fuel_zero_result : runnerResultAt regionBothSucceed 0 [] =
    some (.frontier (.fuel ⟨0⟩), []) := by rfl

theorem source_fuel_zero_runner : runnerAt regionBothSucceed 0 [] = some [] := by rfl

/-- **P2, the repaired reading.** The compiled machine writes nothing, because
its residual is a `Prim.suspend` fixed point. Before the repair it wrote
`done interrupted`. -/
theorem source_fuel_zero_machine : machineAt regionBothSucceed 0 [] = some [] := by rfl

/-- And the silence is a *live frontier*, not a silent completion: DB-04. -/
theorem source_fuel_zero_live : machineIsLive regionBothSucceed 0 [] = some true := by rfl

theorem source_fuel_zero_agrees :
    machineAt regionBothSucceed 0 [] = runnerAt regionBothSucceed 0 [] := by rfl

theorem source_fuel_after_acquire_result : runnerResultAt regionBothSucceed 2 [] =
    some (.frontier (.fuel ⟨2⟩), []) := by rfl

theorem source_fuel_after_acquire_runner : runnerAt regionBothSucceed 2 [] =
    some [] := by rfl

/-- **P2 with an open registration.** Before the repair the machine ran the
release's finalizer against `interrupted` and reported completion; now the
registration simply stays open on the stack. -/
theorem source_fuel_after_acquire_machine : machineAt regionBothSucceed 2 [] =
    some [] := by rfl

theorem source_fuel_after_acquire_live : machineIsLive regionBothSucceed 2 [] = some true := by rfl

theorem source_fuel_after_acquire_agrees :
    machineAt regionBothSucceed 2 [] = runnerAt regionBothSucceed 2 [] := by rfl

-- E4-TARGET-CE-021: site 7 holds the acquired resource until a false decision.
def decisionCycle : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.choose ⟨7⟩ ⟨2⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

theorem decisionCycle_admitted : (admit? decisionCycle).isSome = true := by rfl

theorem unanswered_result : runnerResultAt decisionCycle 20 [] =
    some (.frontier (.unansweredDecision ⟨7⟩), []) := by rfl

theorem unanswered_runner : runnerAt decisionCycle 20 [] = some [] := by rfl

/-- **P2 at an unanswered decision.** The acquired resource stays held. -/
theorem unanswered_machine : machineAt decisionCycle 20 [] = some [] := by rfl

theorem unanswered_live : machineIsLive decisionCycle 20 [] = some true := by rfl

theorem unanswered_decision_agrees :
    machineAt decisionCycle 20 [] = runnerAt decisionCycle 20 [] := by rfl

theorem unanswered_after_choice_result :
    runnerResultAt decisionCycle 20 [⟨⟨7⟩, true⟩] =
      some (.frontier (.unansweredDecision ⟨7⟩), []) := by rfl

theorem unanswered_after_choice_agrees :
    machineAt decisionCycle 20 [⟨⟨7⟩, true⟩] =
      runnerAt decisionCycle 20 [⟨⟨7⟩, true⟩] := by rfl

/-- The runner distinguishes a *refusal* from a frontier, keeping the unmatched
tape. -/
theorem mismatched_decision_is_refusal :
    runnerResultAt decisionCycle 20 [⟨⟨8⟩, false⟩] =
      some (.refusedSite ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, false⟩]) := by rfl

/-- **The classification half of `E4-TARGET-CE-020`/`-021` is still open.** The
machine compiles a refusal to the same live suspension it compiles a frontier
to, so the two are indistinguishable under this mask. Telling them apart is T8
(packet P5), which needs a three-way endpoint classifier rather than an equation
between exits: `Flow.RunResult.refusedSite` has no `Exit` image at all. -/
theorem mismatched_decision_machine_is_live :
    machineIsLive decisionCycle 20 [⟨⟨8⟩, false⟩] = some true := by rfl

theorem completed_decision_control :
    machineAt decisionCycle 20 [⟨⟨7⟩, false⟩] =
      runnerAt decisionCycle 20 [⟨⟨7⟩, false⟩] := by rfl

theorem completed_decision_result : runnerResultAt decisionCycle 20 [⟨⟨7⟩, false⟩] =
    some (.done (.nat 5), []) := by rfl

/-! ## The `leaveConfig` witness, inverted (spike S4b)

A region body that consumes a decision, followed by a decision after the
region. The runner leaves the region with the tape it holds at the `leave`.
Spike S4 compiled the region's continuation against the tape the `enter` was
named at, so the machine met a site mismatch and stopped; **S4b resumes at
`Effect4.RegionSimulation.leaveConfig`**, the configuration the body actually
reaches, so the two now agree. No acquire is involved, so this isolates the
`leaveConfig` repair from P1 and P2. -/

def tapeAfterRegion : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.plain (.choose ⟨7⟩ ⟨2⟩ ⟨4⟩ (vars 1)))
  , rblock 2 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 3 none ["number"] (.plain (.choose ⟨8⟩ ⟨5⟩ ⟨6⟩ (vars 1)))
  , rblock 4 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 5 none ["number"] (.plain (.ret ⟨0⟩))
  , rblock 6 none ["number"] (.plain (.ret ⟨0⟩)) ]

theorem tapeAfterRegion_admitted : (admit? tapeAfterRegion).isSome = true := by rfl

theorem tapeAfterRegion_runner_completes :
    runnerResultAt tapeAfterRegion 20 [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] =
      some (.done (.nat 5), []) := by rfl

theorem tapeAfterRegion_runner :
    runnerAt tapeAfterRegion 20 [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] =
      some [.done (.success (.nat 5))] := by rfl

/-- **S4b, the repaired reading.** The compiled machine reaches the `done` row:
its region continuation is compiled at `leaveConfig`, which carries the fuel and
tape the body held at the `leave`, so the decision after the region reads site 8
exactly as the runner does. Under S4 this was `some []`. -/
theorem tapeAfterRegion_machine :
    machineAt tapeAfterRegion 20 [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] =
      some [.done (.success (.nat 5))] := by rfl

/-- The positive theorem that replaces `tapeAfterRegion_diverges`. -/
theorem tapeAfterRegion_agrees :
    machineAt tapeAfterRegion 20 [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] =
      runnerAt tapeAfterRegion 20 [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] := by rfl

/-- The same fixture with the other branch and the other tape, so the agreement
is not an accident of one edge. -/
theorem tapeAfterRegion_agrees_other_branch :
    machineAt tapeAfterRegion 20 [⟨⟨7⟩, false⟩, ⟨⟨8⟩, true⟩] =
      runnerAt tapeAfterRegion 20 [⟨⟨7⟩, false⟩, ⟨⟨8⟩, true⟩] := by rfl

/-- The unrestricted finite-input **trace** equation. S4 refuted it, from
`tapeAfterRegion`; S4b repaired the compile and that witness is gone, so **no
refutation of this statement is offered any more**. It is not claimed true
either: proving it is exactly T5 in general
(`Effect4.RegionSimulation.RegionsSimulate`), and it is stated here as the
`Prop` that names the remaining Lean obligation. -/
def AllFiniteInputsAgree : Prop :=
  ∀ (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape),
    (admit? raw).isSome = true → machineAt raw fuel tape = runnerAt raw fuel tape

/-- The obligation is not vacuous: the equation has content at a flow whose two
sides are non-empty and whose close merges a failing release. -/
theorem finite_agreement_has_content :
    machineAt failingRelease 20 [] = runnerAt failingRelease 20 [] ∧
      runnerAt failingRelease 20 [] ≠ some [] :=
  ⟨failing_release_agrees, by decide⟩

/-- The runner's three-way endpoint, which the masked trace cannot see. -/
inductive Endpoint where
  /-- Live: a fuel frontier or an unanswered decision (`docs/DESIGN-BASIS.md` DB-04). -/
  | live
  /-- Refused: the tape is not this flow's run (`RunResult.refusedSite`/`refusedValue`). -/
  | refused
  /-- Completed: `done` or `failed`. -/
  | completed
deriving DecidableEq, Repr

def runnerEndpoint (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) : Option Endpoint :=
  (runnerResultAt raw fuel tape).map fun result =>
    match result.fst with
    | .frontier _ => .live
    | .refusedSite _ _ => .refused
    | .refusedValue _ => .refused
    | _ => .completed

/-- The machine's endpoint has only two readings: `FrameStep.running` is DB-04's
live frontier and `FrameStep.finished` is completion. There is no third. -/
def machineEndpoint (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape) : Option Endpoint :=
  (machineIsLive raw fuel tape).map fun live => if live then .live else .completed

/-- **The remaining unrestricted divergence, and the only one S4b leaves.** The
trace half is repaired; the *classification* half is not. This is the statement
`unrestricted_finite_agreement_false` used to make with the `leaveConfig`
witness and makes now with the refusal witness — T8, packet P5. -/
def AllFiniteInputsClassify : Prop :=
  ∀ (raw : RegionFlow String) (fuel : Nat) (tape : Flow.Tape),
    (admit? raw).isSome = true → machineEndpoint raw fuel tape = runnerEndpoint raw fuel tape

theorem mismatched_decision_classification_diverges :
    machineEndpoint decisionCycle 20 [⟨⟨8⟩, false⟩] ≠
      runnerEndpoint decisionCycle 20 [⟨⟨8⟩, false⟩] := by decide

theorem unrestricted_finite_classification_false : ¬ AllFiniteInputsClassify := by
  intro h
  exact mismatched_decision_classification_diverges
    (h decisionCycle 20 [⟨⟨8⟩, false⟩] decisionCycle_admitted)

#print axioms failingRelease_admitted
#print axioms same_scope_closing_exit
#print axioms repaired_frames_use_original_exit
#print axioms failing_release_agrees
#print axioms successfulReleases_admitted
#print axioms successful_scope_control
#print axioms successful_frames_control
#print axioms source_fuel_zero_result
#print axioms source_fuel_zero_runner
#print axioms source_fuel_zero_machine
#print axioms source_fuel_zero_live
#print axioms source_fuel_zero_agrees
#print axioms source_fuel_after_acquire_result
#print axioms source_fuel_after_acquire_runner
#print axioms source_fuel_after_acquire_machine
#print axioms source_fuel_after_acquire_live
#print axioms source_fuel_after_acquire_agrees
#print axioms decisionCycle_admitted
#print axioms unanswered_result
#print axioms unanswered_runner
#print axioms unanswered_machine
#print axioms unanswered_live
#print axioms unanswered_decision_agrees
#print axioms unanswered_after_choice_result
#print axioms unanswered_after_choice_agrees
#print axioms mismatched_decision_is_refusal
#print axioms mismatched_decision_machine_is_live
#print axioms completed_decision_control
#print axioms completed_decision_result
#print axioms tapeAfterRegion_admitted
#print axioms tapeAfterRegion_runner_completes
#print axioms tapeAfterRegion_runner
#print axioms tapeAfterRegion_machine
#print axioms tapeAfterRegion_agrees
#print axioms tapeAfterRegion_agrees_other_branch
#print axioms finite_agreement_has_content
#print axioms mismatched_decision_classification_diverges
#print axioms unrestricted_finite_classification_false

end Effect4Test.Counterexamples.Target.RegionSimulationBoundary
