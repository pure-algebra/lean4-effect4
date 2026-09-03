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

def admit? (raw : RegionFlow String) : Option (CheckedRegionFlow alphabet) :=
  match admitRegions alphabet raw with
  | .ok flow => some flow
  | .error _ => none

-- All three region flows are admitted.
#guard (admit? regionNested).isSome
#guard (admit? regionTwoFail).isSome
#guard (admit? regionBothSucceed).isSome

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
