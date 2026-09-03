/-
Independent breaker packet: test/contracts/region-total-denotation.contract.md.
The controls below run the existing fuelled meaning. The final, fully quantified
ascriptions transfer that entire Program, including every possible handler
answer, to the new fuel-free meaning. Finite controls are not the general proof.
-/

import Effect4.Semantics.RegionTotal
import Effect4Test.Semantics.RegionDenotationContract
import Effect4Test.Flow.RegionRunnerContract

namespace Effect4Test.Semantics.RegionTotalContract

open Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)
open Effect4Test.Semantics.RegionDenotationContract
  (table service nameOf admitted regionNested regionTwoFail regionBothSucceed
   regionFree rblock rregion regionFlow vars opAcquire opRelease)

/-! ## Independent concrete controls -/

-- The existing nested body failure, now with both releases failing as well.
def nestedReleaseFailures : RegionFlow String :=
  { regionNested with blocks := regionNested.blocks.map fun block =>
      { block with term := match block.term with
        | .acquire op request _ target args => .acquire op request ⟨5⟩ target args
        | term => term } }

-- A resource stays open while site 7 loops. An unanswered/mismatched tape is
-- a live frontier/refusal; only the false branch leaves and releases it.
def decisionCycle : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.choose ⟨7⟩ ⟨2⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

def observed (raw : RegionFlow String) (tape : Tape) (extra : Nat := 0) :
    Option ((((RunResult × Tape) × Failures) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    ((interpretRegions service nameOf
      (denoteRegions (fuelFor flow.flow.erase tape + extra) flow tape (.nat 5))).run
      [.decide 99 false]).run 41

def runObserved (raw : RegionFlow String) (tape : Tape) (extra : Nat := 0) :
    Option ((((RunResult × Tape) × Failures) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    ((runRegionsCause (fuelFor flow.flow.erase tape + extra) flow service nameOf
      tape (.nat 5)).run [.decide 99 false]).run 41

def resultOf (raw : RegionFlow String) (tape : Tape) (extra : Nat := 0) :=
  (observed raw tape extra).map fun result => result.1.1

#guard (admitted nestedReleaseFailures).isSome
#guard (admitted decisionCycle).isSome
#guard (admitted Effect4Test.Flow.RegionRunnerContract.releaseFails).isSome

-- Full result, unused tape, failures, pre-existing log and service state.
#guard observed regionNested [] == runObserved regionNested []
#guard observed regionTwoFail [] == runObserved regionTwoFail []
#guard observed regionBothSucceed [] == runObserved regionBothSucceed []
#guard observed regionFree [] == runObserved regionFree []
#guard observed nestedReleaseFailures [] == runObserved nestedReleaseFailures []
#guard observed Effect4Test.Flow.RegionRunnerContract.releaseFails [] ==
  runObserved Effect4Test.Flow.RegionRunnerContract.releaseFails []
#guard observed decisionCycle [⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩] ==
  runObserved decisionCycle [⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩]

-- Erasing the merged cause to only its first failure must be rejected.
#guard resultOf nestedReleaseFailures [] =
  some ((.failed (.str "boom"), []), [.str "boom", .str "boom", .str "boom"])
#guard resultOf nestedReleaseFailures [] ≠
  some ((.failed (.str "boom"), []), [.str "boom"])
#guard resultOf Effect4Test.Flow.RegionRunnerContract.releaseFails [] =
  some ((.failed (.str "boom"), []), [.str "boom"])
#guard resultOf regionBothSucceed [] = some ((.done (.nat 5), []), [])

-- Both loop visits consume exactly one compatible decision; the unused suffix
-- survives a successful leave. More than the calculated budget is also valid.
#guard resultOf decisionCycle
  [⟨⟨7⟩, true⟩, ⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩, ⟨⟨9⟩, true⟩] =
  some ((.done (.nat 5), [⟨⟨9⟩, true⟩]), [])
#guard observed decisionCycle [⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩] 37 ==
  observed decisionCycle [⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩]
#guard observed nestedReleaseFailures [] 37 == observed nestedReleaseFailures []

#guard resultOf decisionCycle [] =
  some ((.frontier (.unansweredDecision ⟨7⟩), []), [])
#guard resultOf decisionCycle [⟨⟨8⟩, true⟩] =
  some ((.refusedSite ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, true⟩]), [])
#guard resultOf decisionCycle [⟨⟨7⟩, true⟩] =
  some ((.frontier (.unansweredDecision ⟨7⟩), []), [])
#guard resultOf decisionCycle [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩] =
  some ((.refusedSite ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, false⟩]), [])

-- A suspended open scope has neither leave nor release nor done rows.
#guard (observed decisionCycle [⟨⟨7⟩, true⟩]).map (fun result => result.1.2) =
  some [.decide 99 false, .enter 1,
    .op "acquire" (.nat 5), .answer "acquire" (.nat 5), .decide 7 true, .frontier]

-- Arbitrary scope answers are part of Program equality. Even an admitted flow
-- permits a handler to answer `none`; no reachable-stack premise may hide it.
def optionRefusalHandler (refuseAcquire : Bool) :
    Handler (RegionSig (tableAlphabet ⟨0⟩ table)) Id where
  handle operation := match operation with
    | .inl ⟨.enter, _⟩ => ()
    | .inl ⟨.acquire _ _, request⟩ => if refuseAcquire then none else some (.ok request)
    | .inl ⟨.leave, _⟩ => none
    | .inl ⟨.fail, _⟩ => []
    | .inr (.inl ⟨_, request⟩) => .ok request
    | .inr (.inr _) => ()

def refusedByHandler (refuseAcquire : Bool) : Option ((RunResult × Tape) × Failures) :=
  (admitted regionBothSucceed).map fun flow =>
    interpret (M := Id) (optionRefusalHandler refuseAcquire)
      (denoteRegions (fuelFor flow.flow.erase []) flow [] (.nat 5))

#guard refusedByHandler true = some ((.frontier (.stuck ⟨1⟩), []), [])
#guard refusedByHandler false = some ((.frontier (.stuck ⟨2⟩), []), [])

/- BEGIN TOTAL-SURFACE: exact red declarations, independently checked controls above. -/

universe uTy
variable {Ty : Type uTy}

-- No fuel, checked-flow argument, stack invariant, or successful-run premise.
#check (@denoteRegionsGo :
  {Ty : Type uTy} → {alphabet : FlowAlphabet Ty} →
  (flow : RegionFlow Ty) → CyclesWF flow.erase → BlockId → Env → Tape →
  Program (RegionSig alphabet) ((RunResult × Tape) × Failures))

#check (@denoteRegionsWF :
  {Ty : Type uTy} → [DecidableEq Ty] → {alphabet : FlowAlphabet Ty} →
  CheckedRegionFlow alphabet → Tape → Val →
  Program (RegionSig alphabet) ((RunResult × Tape) × Failures))

-- Every checked region flow, input, tape and sufficient fuel; equality is of
-- the whole Program before interpreting, not only successful observed runs.
#check (@denoteRegionsFuel_eq_denoteRegionsWF :
  {Ty : Type uTy} → [DecidableEq Ty] → {alphabet : FlowAlphabet Ty} →
  (flow : CheckedRegionFlow alphabet) → (tape : Tape) → (input : Val) →
  {fuel : Nat} → fuelFor flow.flow.erase tape ≤ fuel →
  denoteRegionsFuel (alphabet := alphabet) flow.flow fuel flow.flow.entry [input] tape =
    denoteRegionsWF flow tape input)

#check (@runRegionsCause_eq_interpretWF :
  {Ty : Type uTy} → {M : Type → Type} → [Monad M] → [LawfulMonad M] →
  [DecidableEq Ty] → {alphabet : FlowAlphabet Ty} → {fuel : Nat} →
  (flow : CheckedRegionFlow alphabet) → (service : RegionService alphabet M) →
  (nameOf : alphabet.Op → String) → (tape : Tape) → (input : Val) →
  (log : Effect4.Trace.Log) → fuelFor flow.flow.erase tape ≤ fuel →
  (runRegionsCause fuel flow service nameOf tape input).run log =
    (interpretRegions service nameOf (denoteRegionsWF flow tape input)).run log)

-- Arbitrary handlers also see exactly the same denotation, including both
-- Option-refusal arms and every Except failure arm tested above.
example [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (flow : CheckedRegionFlow alphabet)
    (tape : Tape) (input : Val) {fuel : Nat} (enough : fuelFor flow.flow.erase tape ≤ fuel)
    {M : Type → Type} [Monad M] (handler : Handler (RegionSig alphabet) M) :
    interpret handler (denoteRegionsFuel flow.flow fuel flow.flow.entry [input] tape) =
      interpret handler (denoteRegionsWF flow tape input) :=
  congrArg (interpret handler) (denoteRegionsFuel_eq_denoteRegionsWF flow tape input enough)

-- A strict surplus is an instance of the same theorem, not a second meaning.
example [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (flow : CheckedRegionFlow alphabet)
    (tape : Tape) (input : Val) (extra : Nat) :
    denoteRegionsFuel flow.flow (fuelFor flow.flow.erase tape + extra)
      flow.flow.entry [input] tape = denoteRegionsWF flow tape input :=
  denoteRegionsFuel_eq_denoteRegionsWF flow tape input (Nat.le_add_right _ _)

/- END TOTAL-SURFACE -/

end Effect4Test.Semantics.RegionTotalContract
