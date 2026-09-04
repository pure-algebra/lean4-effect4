/-
Contract packet: `test/contracts/frame-simulation.contract.md` (packet D4, the
finalizer half). The region-aware compilation into the frame machine, the two
general finalizer theorems, and the instances of `regions_simulate` on the
three region programs the harness pins. Doc comments cannot precede `#guard`,
so the receipts carry line comments.
-/

import Effect4.Semantics.RegionSimulation
import Effect4.Meta.Derive

namespace Effect4Test.Semantics.RegionSimulationContract

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4
open Effect4.RegionSimulation
open Effects.Trace (Val)

#check @Effect4.RegionSimulation.compileRegion
#check @Effect4.RegionSimulation.regionInterp
#check @Effect4.RegionSimulation.statelessOracle
#check @Effect4.RegionSimulation.regionBound
#check @Effect4.RegionSimulation.unwind_failure
#check @Effect4.RegionSimulation.close_success
#check @Effect4.RegionSimulation.toOutcome_combine
#check @Effect4.RegionSimulation.failuresOfCause_causeOfFailures

-- Spike S4: the declarations the three compile repairs added.
#check @Effect4.RegionSimulation.closeWalk
#check @Effect4.RegionSimulation.regionRegistrations
#check @Effect4.RegionSimulation.closeFinish
#check @Effect4.RegionSimulation.closeExit
#check @Effect4.RegionSimulation.closeFailuresOf
#check @Effect4.RegionSimulation.regionSuspendBody
#check @Effect4.RegionSimulation.caughtNames
#check @Effect4.RegionSimulation.compileRegion_catchFree
#check @Effect4.RegionSimulation.regionInterp_finalizerExit
#check @Effect4.RegionSimulation.regionInterp_suspend_fixed
#check @Effect4.RegionSimulation.close_success_of
#check @Effect4.RegionSimulation.close_success_region
#check @Effect4.RegionSimulation.unwind_to_frame
#check @Effect4.RegionSimulation.closeFinish_eq_result?
#check @Effect4.RegionSimulation.closeExit_reasons
#check @Effect4.RegionSimulation.releaseFrames
#check @Effect4.RegionSimulation.region_close_rows
#check @Effect4.RegionSimulation.region_unwind_rows
#check @Effect4.RegionSimulation.compileRegion_never_fails
#check @Effect4.RegionSimulation.compileAt_zero_fuel_live
#check @Effect4.RegionSimulation.statelessOracle_agrees
#check @Effect4.RegionSimulation.RegionOracleAgrees
#check @Effect4.RegionSimulation.RegionsSimulate
#check @Effect4.RegionSimulation.RegionsSimulateExit

-- Spike S4b: the leave configuration, and the proof that the walk is the runner.
#check @Effect4.RegionSimulation.LeavePoint
#check @Effect4.RegionSimulation.anyReleaseFails
#check @Effect4.RegionSimulation.registeredRelease
#check @Effect4.RegionSimulation.registeredReleases
#check @Effect4.RegionSimulation.regionWalk
#check @Effect4.RegionSimulation.leaveConfig
#check @Effect4.RegionSimulation.RunPrefix
#check @Effect4.RegionSimulation.logOperation_prefix
#check @Effect4.RegionSimulation.regionLoop_jump
#check @Effect4.RegionSimulation.regionLoop_choose
#check @Effect4.RegionSimulation.regionLoop_perform
#check @Effect4.RegionSimulation.regionLoop_performCatch_ok
#check @Effect4.RegionSimulation.regionLoop_performCatch_error
#check @Effect4.RegionSimulation.regionLoop_enter
#check @Effect4.RegionSimulation.regionLoop_acquire
#check @Effect4.RegionSimulation.regionLoop_leave
#check @Effect4.RegionSimulation.closeFrame_success
#check @Effect4.RegionSimulation.leaveStep
#check @Effect4.RegionSimulation.closeWalk_agrees_regionLoop
#check @Effect4.RegionSimulation.leaveConfig_agrees_runRegions
#check @Effect4.RegionSimulation.leaveConfig_of_regionWalk
#check @Effect4.RegionSimulation.regionRegistrations_of_regionWalk
#check @Effect4.RegionSimulation.regionInterp_regionCont_resume
#check @Effect4.RegionSimulation.RegionsSimulateAll
#check @Effect4.RegionSimulation.RegionsSimulateExitAll

/-! ## Separation 4: the name alphabet is data, not a function

`DecidableEq (Prim …)` is the guard. It fails to elaborate the moment `ν` or
`σ` is instantiated at a function type, which is what `docs/FRAMES-DAG.md`
separation 4 forbids and what the obvious compilation
`ν := Σ op, (S.Answer op → Program S Val)` would do silently. -/

example : DecidableEq Effect4.RegionSimulation.Code := inferInstance

example : DecidableEq Effect4.RegionSimulation.RegionName := inferInstance

example : DecidableEq Effect4.RegionSimulation.Config := inferInstance

/-! ## The fixtures

The three region programs `harness/trace/Generate.lean` pins, re-declared here
as every other battery of this repo re-declares them: the harness is not a
library and no test imports it. -/

effect_signature RCell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫
  | acquire (n : Nat) : Nat ⟪ "acquire a resource named by a number" ⟫
  | release (n : Nat) : Unit ⟪ "release a resource" ⟫
  | boom (n : Nat) : Nat !! String ⟪ "fail with a string" ⟫
  | releaseBoom (n : Nat) : Unit !! String ⟪ "a release that fails" ⟫

def table : List OpSpec := familyTable RCell.rows

def opAcquire : OperationId := ⟨2⟩
def opRelease : OperationId := ⟨3⟩
def opBoom : OperationId := ⟨4⟩
def opReleaseBoom : OperationId := ⟨5⟩

def alphabet : FlowAlphabet String := tableAlphabet ⟨0⟩ table

/-- The stateless face of the harness family: `acquire` answers its request,
`release` answers unit, `boom` fails. `get` and `put` never appear in these
three flows, which is what makes the family stateless on them. -/
def answerOf : alphabet.Op → Val → Except Val Val := fun op request =>
  match (OpSpec.at table op).name with
  | "acquire" => .ok request
  | "release" => .ok .unit
  | "boom" => .error (.str "boom")
  | "releaseBoom" => .error (.str "boom")
  | _ => .ok .unit

def service : Flow.RegionService alphabet Id where
  handle op request := answerOf op request
  pure op :=
    match (OpSpec.at table op).kind with
    | .family => false
    | _ => true

def nameOf : alphabet.Op → String := tableNameOf ⟨0⟩ table

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def rregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩,
    resultTy := "number" }

def regionFlow (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) :
    RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

def regionNested : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

def regionTwoFail : RegionFlow String := regionFlow [rregion 1 none 5]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opRelease ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨4⟩ (vars 3)))
  , rblock 4 (some 1) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 5 none ["number"] (.plain (.ret ⟨0⟩)) ]

def regionBothSucceed : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Spike S4, P1: `E4-TARGET-CE-019`'s own fixture, promoted from the
counterexample battery to an instance of the equation. Two releases of one
scope, the second failing, on a clean leave — the case the old nested-`onExit`
compile got wrong. -/
def regionReleaseFails : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opReleaseBoom ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.leave ⟨2⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Spike S4, P3: a `performCatch` inside a region holding a resource. Its
operation fails, the failure is caught by the machine's `contE` arm — a real
`Cause` reaching a real frame, which is what `Effect.result` builds
(`internal/effect.ts:3417-3420`) — and the region still closes normally. -/
def regionCatch : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"]
      (.plain (.performCatch opBoom ⟨0⟩ ⟨2⟩ (vars 1) ⟨3⟩ (vars 1)))
  , rblock 2 (some 1) ["number", "number"] (.leave ⟨0⟩)
  , rblock 3 (some 1) ["number", "string"] (.acquire opAcquire ⟨0⟩ opRelease ⟨5⟩ (vars 1))
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩))
  , rblock 5 (some 1) ["number", "number"] (.leave ⟨0⟩) ]

def admit? (raw : RegionFlow String) : Option (CheckedRegionFlow alphabet) :=
  match admitRegions alphabet raw with
  | .ok flow => some flow
  | .error _ => none

-- All five region flows are admitted.
#guard (admit? regionNested).isSome
#guard (admit? regionTwoFail).isSome
#guard (admit? regionBothSucceed).isSome
#guard (admit? regionReleaseFails).isSome
#guard (admit? regionCatch).isSome

/-! ## The two sides of `regions_simulate` -/

/-- The runner's log, masked to `finalizer` and `done`. -/
def runnerSide (raw : RegionFlow String) : Option Effect4.Trace.Log :=
  (admit? raw).map fun flow =>
    Effects.Trace.project finalizerAndOutcomeMask
      (((Flow.runRegions (Flow.fuelFor flow.flow.erase []) flow service nameOf []
        (.nat 5)).run []).2)

/-- The frame machine's trace, projected to its service-level shadow. -/
def machineSide (raw : RegionFlow String) : Option Effect4.Trace.Log :=
  (admit? raw).map fun flow =>
    traceOfRun (Effect4.FrameFiber.run
      (regionInterp alphabet flow.flow (statelessOracle alphabet flow.flow answerOf))
      (regionBound (Flow.fuelFor flow.flow.erase []))
      (Effect4.FrameFiber.start (compileAt alphabet flow.flow
        ⟨Flow.fuelFor flow.flow.erase [], flow.flow.entry, [.nat 5], []⟩))).2

/-! ## The instances of `regions_simulate`

Three closed theorems. Each is the equation of the module header's owed
`regions_simulate`, at one region program, one stateless service, the empty
decision tape and the input `5`: the frame machine's projected trace equals the
runner's log under the mask that keeps `finalizer` and `done`.

`regionBothSucceed` is the single-region single-release case, `regionNested` is
the nested case, and `regionTwoFail` is two releases of one region closing on a
failing body. All three are decided by kernel evaluation, which is what makes
`compileRegion`'s recursion structural in the fuel rather than well-founded. -/

theorem regions_simulate_regionBothSucceed :
    machineSide regionBothSucceed = runnerSide regionBothSucceed := by rfl

theorem regions_simulate_regionNested :
    machineSide regionNested = runnerSide regionNested := by rfl

theorem regions_simulate_regionTwoFail :
    machineSide regionTwoFail = runnerSide regionTwoFail := by rfl

/-! ## What both sides are, spelled out

The equations above would be vacuous if both sides were `none`, and weak if the
mask erased everything. These pin the literal. -/

theorem runnerSide_regionBothSucceed :
    runnerSide regionBothSucceed =
      some [ .finalizer 1 (.success (.nat 5)), .done (.success (.nat 5)) ] := by rfl

theorem runnerSide_regionNested :
    runnerSide regionNested =
      some [ .finalizer 2 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom")),
        .done (.failure (.str "boom")) ] := by rfl

theorem runnerSide_regionTwoFail :
    runnerSide regionTwoFail =
      some [ .finalizer 1 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom")),
        .done (.failure (.str "boom")) ] := by rfl

-- The same three, as decision receipts: a `#guard` that a mutant to either
-- emitter would break.
#guard machineSide regionBothSucceed ==
  some [ .finalizer 1 (.success (.nat 5)), .done (.success (.nat 5)) ]
#guard machineSide regionNested ==
  some [ .finalizer 2 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom")),
    .done (.failure (.str "boom")) ]
#guard machineSide regionTwoFail ==
  some [ .finalizer 1 (.failure (.str "boom")), .finalizer 1 (.failure (.str "boom")),
    .done (.failure (.str "boom")) ]

/-! ## Spike S4: the three repairs, as receipts

P1 — one scope per region. `E4-TARGET-CE-019`'s own fixture is now an instance
of the equation: both releases of the one scope see the closing exit the runner
gives them, and the failing release surfaces once, in the run's exit. -/

theorem regions_simulate_regionReleaseFails :
    machineSide regionReleaseFails = runnerSide regionReleaseFails := by rfl

theorem runnerSide_regionReleaseFails :
    runnerSide regionReleaseFails =
      some [ .finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
        .done (.failure (.str "boom")) ] := by rfl

#guard machineSide regionReleaseFails ==
  some [ .finalizer 1 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)),
    .done (.failure (.str "boom")) ]

/-- The registrations `statelessOracle` reports for a region are the releases
the runner's `Frame` holds when it closes: `Effect4.Flow.Frame.releases`,
latest registered first. -/
def registrationsAt (raw : RegionFlow String) : Option Nat :=
  (admit? raw).map fun flow =>
    ((statelessOracle alphabet flow.flow answerOf).registrations
      ⟨Flow.fuelFor flow.flow.erase [], flow.flow.entry, [.nat 5], []⟩).length

theorem registrations_regionBothSucceed : registrationsAt regionBothSucceed = some 1 := by rfl

theorem registrations_regionTwoFail : registrationsAt regionTwoFail = some 2 := by rfl

theorem registrations_regionReleaseFails : registrationsAt regionReleaseFails = some 2 := by rfl

-- A region whose body fails still reports the registrations it made before the
-- failure, which is what the runner's `unwind` closes.
theorem registrations_regionNested : registrationsAt regionNested = some 1 := by rfl

/-- The close merge is concatenation, not union: two releases failing with the
same error report it twice. `Cause.combine` would dedup
(`Effect4.Cause.dedup_cons`); `Exit.asVoidAll` does not, and neither does
rc.112's `exitAsVoidAll` (`internal/effect.ts:2025-2038`). This is
`E4-FLOW-CE-021` at the compile's close. -/
example : closeFinish
      [ Effect4.Exit.failure (Effect4.Cause.fail (Val.str "boom"))
      , Effect4.Exit.failure (Effect4.Cause.fail (Val.str "boom")) ] =
    Effect4.Exit.failure
      ⟨[ Effect4.Reason.fail (Val.str "boom") Effect4.ReasonAnnotations.empty
       , Effect4.Reason.fail (Val.str "boom") Effect4.ReasonAnnotations.empty ]⟩ := rfl

/-! P3 — `performCatch` as `onSuccessAndFailure`. The catch flow emits exactly
one `RegionName.caught` name; every catch-free flow emits none, which is the
concrete face of `compileRegion_catchFree`. -/

def caughtOf (raw : RegionFlow String) : Option Nat :=
  (admit? raw).map fun flow =>
    (caughtNames (compileAt alphabet flow.flow
      ⟨Flow.fuelFor flow.flow.erase [], flow.flow.entry, [.nat 5], []⟩)).length

theorem regionCatch_emits_caught : caughtOf regionCatch = some 1 := by rfl

theorem regionBothSucceed_catch_free : caughtOf regionBothSucceed = some 0 := by rfl

theorem regionNested_catch_free : caughtOf regionNested = some 0 := by rfl

theorem regionTwoFail_catch_free : caughtOf regionTwoFail = some 0 := by rfl

theorem regionReleaseFails_catch_free : caughtOf regionReleaseFails = some 0 := by rfl

theorem regions_simulate_regionCatch :
    machineSide regionCatch = runnerSide regionCatch := by rfl

theorem runnerSide_regionCatch :
    runnerSide regionCatch =
      some [ .finalizer 1 (.success (.nat 5)), .done (.success (.nat 5)) ] := by rfl

#guard machineSide regionCatch ==
  some [ .finalizer 1 (.success (.nat 5)), .done (.success (.nat 5)) ]

/-! ## Spike S4b: the leave configuration, as receipts

`leaveConfig` is the configuration `Effect4.Flow.regionLoop` holds when the
region entered at the flow's entry hands its value on. These pin the literal on
both halves — the block and the fuel — so a mutant that resumed at the enter's
configuration (which is what spike S4 did) would break them. -/

def leaveConfigOf (raw : RegionFlow String) : Option (Option Config) :=
  (admit? raw).map fun flow =>
    leaveConfig alphabet flow.flow (statelessAnswer alphabet flow.flow answerOf)
      (statelessRelease alphabet flow.flow answerOf)
      ⟨Flow.fuelFor flow.flow.erase [], flow.flow.entry, [.nat 5], []⟩

/-- The entry point of a fixture: the configuration the *enter* holds. -/
def enterPointOf (raw : RegionFlow String) : Option Config :=
  (admit? raw).map fun flow =>
    ⟨Flow.fuelFor flow.flow.erase [], flow.flow.entry, [.nat 5], []⟩

/-- One region, one release, a clean leave: the runner reaches the `leave` with
two units of fuel left and no tape, and continues at block 3. -/
theorem leaveConfig_regionBothSucceed :
    leaveConfigOf regionBothSucceed = some (some ⟨2, ⟨3⟩, [.nat 5], []⟩) := by rfl

/-- **The repair has content.** The enter holds fuel 5 at block 0; the compile
used to resume at `point.fuel - 1 = 4`, and the runner resumes at 2. -/
theorem enterPoint_regionBothSucceed :
    enterPointOf regionBothSucceed = some ⟨5, ⟨0⟩, [.nat 5], []⟩ := by rfl

theorem leaveConfig_regionReleaseFails :
    leaveConfigOf regionReleaseFails = some (some ⟨2, ⟨4⟩, [.nat 5], []⟩) := by rfl

/-- P3's fixture: the caught failure runs through the error edge and the
acquire, so the leave is reached three units of fuel from the end. -/
theorem leaveConfig_regionCatch :
    leaveConfigOf regionCatch = some (some ⟨3, ⟨4⟩, [.nat 5], []⟩) := by rfl

/-- A region whose body fails reaches no `leave`, so the value arm of its scope
frame is never demanded and `leaveConfig` is honestly `none`: the cause arm
answers instead. -/
theorem leaveConfig_regionTwoFail : leaveConfigOf regionTwoFail = some none := by rfl

theorem leaveConfig_regionNested : leaveConfigOf regionNested = some none := by rfl

/-! ## P4: the instances, as instances of T5 and T6

`Effect4.RegionSimulation.RegionsSimulate` and `RegionsSimulateExit` are the two
statements of `docs/research/2026-09-03-deep-flow-to-frames.md` §2.3. The five
theorems below are instances of them, at the fuel `Flow.fuelFor` allots and the
machine bound `regionBound` gives, with `RegionOracleAgrees` discharged by
`statelessOracle_agrees` — so the equations are not merely "two expressions
evaluate the same", they are T5 and T6 at these flows.

T6 is the half that distinguishes the models: it is stated against
`runRegionsCause`, which keeps the whole merged failure list, not against
`runRegions`, which projects its head. -/

/-- The checked flow of an admitted fixture. -/
def checked (raw : RegionFlow String) (h : (admit? raw).isSome = true) :
    CheckedRegionFlow alphabet :=
  (admit? raw).get h

/-- T5 at a fixture, with the erased graph's fuel and `regionBound`'s machine
budget. -/
def SimulatesAt (raw : RegionFlow String) (h : (admit? raw).isSome = true) : Prop :=
  RegionsSimulate alphabet (checked raw h) service answerOf nameOf
    (statelessOracle alphabet (checked raw h).flow answerOf) [] (.nat 5)
    (Flow.fuelFor (checked raw h).flow.erase [])
    (regionBound (Flow.fuelFor (checked raw h).flow.erase []))

/-- T6 at a fixture. -/
def SimulatesExitAt (raw : RegionFlow String) (h : (admit? raw).isSome = true) : Prop :=
  RegionsSimulateExit alphabet (checked raw h) service answerOf nameOf
    (statelessOracle alphabet (checked raw h).flow answerOf) [] (.nat 5)
    (Flow.fuelFor (checked raw h).flow.erase [])
    (regionBound (Flow.fuelFor (checked raw h).flow.erase []))

theorem oracle_agrees (raw : RegionFlow String) (h : (admit? raw).isSome = true) :
    RegionOracleAgrees alphabet (checked raw h).flow service answerOf
      (statelessOracle alphabet (checked raw h).flow answerOf) :=
  statelessOracle_agrees alphabet (checked raw h).flow service answerOf (fun _ _ => rfl)

theorem T5_regionBothSucceed : SimulatesAt regionBothSucceed (by rfl) := fun _ _ => by rfl

theorem T5_regionNested : SimulatesAt regionNested (by rfl) := fun _ _ => by rfl

theorem T5_regionTwoFail : SimulatesAt regionTwoFail (by rfl) := fun _ _ => by rfl

theorem T5_regionReleaseFails : SimulatesAt regionReleaseFails (by rfl) := fun _ _ => by rfl

theorem T5_regionCatch : SimulatesAt regionCatch (by rfl) := fun _ _ => by rfl

theorem T6_regionBothSucceed : SimulatesExitAt regionBothSucceed (by rfl) := fun _ _ => by rfl

theorem T6_regionNested : SimulatesExitAt regionNested (by rfl) := fun _ _ => by rfl

theorem T6_regionTwoFail : SimulatesExitAt regionTwoFail (by rfl) := fun _ _ => by rfl

theorem T6_regionReleaseFails : SimulatesExitAt regionReleaseFails (by rfl) := fun _ _ => by rfl

theorem T6_regionCatch : SimulatesExitAt regionCatch (by rfl) := fun _ _ => by rfl

/-! ## The projection between the merged failure list and `Cause.combine` -/

-- The retraction, on a two-failure close: the list survives the cause.
#guard failuresOfCause (causeOfFailures [Val.str "first", Val.str "second"]) ==
  [Val.str "first", Val.str "second"]

-- `Cause.combine` prepends: the wire outcome of a merged failure is the body's.
example : outcomeOf (Effect4.Exit.failure
    (Effect4.Cause.combine (Effect4.Cause.fail (Val.str "body"))
      (Effect4.Cause.fail (Val.str "release")))) =
  Effects.Trace.Outcome.failure (Val.str "body") :=
  toOutcome_combine _ _ (Val.str "body") _ [] rfl

-- ... and it does so even when the two reasons differ only in annotations,
-- which is the shape `docs/research/2026-09-03-frame-simulation.md` section
-- 5(b) warned about: no dedup can move the head.
example (annotations : Effect4.ReasonAnnotations Unit) :
    outcomeOf (Effect4.Exit.failure
      (Effect4.Cause.combine ⟨[Effect4.Reason.fail (Val.str "body") annotations]⟩
        (Effect4.Cause.fail (Val.str "body")))) =
    Effects.Trace.Outcome.failure (Val.str "body") :=
  toOutcome_combine _ _ (Val.str "body") annotations [] rfl

end Effect4Test.Semantics.RegionSimulationContract
