import Effect4.Semantics.RegionSafety
import Effect4Test.Semantics.RegionTotalContract

/-!
Independent breaker packet: `test/contracts/region-safety.contract.md`.
The controls exercise existing meanings. The three public ascriptions require
every checked run, every fuel and every service outcome, including frontiers.
They do not quantify over arbitrary replacement handlers of the scope summand.
-/

namespace Effect4Test.Semantics.RegionSafetyContract

open Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)
open Effect4Test.Semantics.RegionDenotationContract
  (table service nameOf admitted regionNested regionTwoFail regionBothSucceed regionFree)
open Effect4Test.Semantics.RegionTotalContract (nestedReleaseFailures decisionCycle)

def observed (raw : RegionFlow String) (fuel : Nat) (tape : Tape)
    (input : Val := .nat 5) :
    Option ((((RunResult × Tape) × Failures) × Effect4.Trace.Log) × Nat) :=
  (admitted raw).map fun flow =>
    ((runRegionsCause fuel flow service nameOf tape input).run [.decide 99 false]).run 41

def stuckOf (raw : RegionFlow String) (fuel : Nat) (tape : Tape) : Option Bool :=
  (observed raw fuel tape).map fun result => result.1.1.1.1.stuck

def resultOf (raw : RegionFlow String) (fuel : Nat) (tape : Tape) :=
  (observed raw fuel tape).map fun result => result.1.1

-- Nonempty admitted examples: nesting, multiple releases, failed body/release,
-- region-free execution, and an arbitrary wire input all remain in scope.
#guard (admitted regionNested).isSome
#guard (admitted regionTwoFail).isSome
#guard (admitted nestedReleaseFailures).isSome
#guard (admitted decisionCycle).isSome
#guard stuckOf regionNested 20 [] = some false
#guard stuckOf regionTwoFail 20 [] = some false
#guard stuckOf nestedReleaseFailures 20 [] = some false
#guard stuckOf Effect4Test.Flow.RegionRunnerContract.releaseFails 20 [] = some false
#guard stuckOf regionFree 20 [] = some false
#guard (observed regionBothSucceed 20 [] (.str "wire input")).map
  (fun result => result.1.1.1.1.stuck) = some false
#guard resultOf nestedReleaseFailures 20 [] =
  some ((.failed (.str "boom"), []), [.str "boom", .str "boom", .str "boom"])

-- Zero/insufficient fuel, unanswered tape and refusal are not malformed state.
#guard resultOf regionBothSucceed 0 [] = some ((.frontier (.fuel ⟨0⟩), []), [])
#guard resultOf regionBothSucceed 2 [] = some ((.frontier (.fuel ⟨2⟩), []), [])
#guard stuckOf regionBothSucceed 0 [] = some false
#guard stuckOf regionBothSucceed 2 [] = some false
#guard resultOf decisionCycle 20 [] =
  some ((.frontier (.unansweredDecision ⟨7⟩), []), [])
#guard stuckOf decisionCycle 20 [] = some false
#guard stuckOf decisionCycle 20 [⟨⟨7⟩, true⟩] = some false
#guard resultOf decisionCycle 20 [⟨⟨8⟩, true⟩] =
  some ((.refusedSite ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, true⟩]), [])
#guard stuckOf decisionCycle 20 [⟨⟨8⟩, true⟩] = some false
#guard resultOf decisionCycle 37 [⟨⟨7⟩, true⟩, ⟨⟨7⟩, false⟩, ⟨⟨9⟩, true⟩] =
  some ((.done (.nat 5), [⟨⟨9⟩, true⟩]), [])

-- A service may mutate its state and then fail on acquisition.
def failingService : RegionService (tableAlphabet ⟨0⟩ table) (StateT Nat Id) where
  handle _ _ := fun state => (.error (.str "changed then failed"), state + 1)
  pure _ := false

def failedAcquisition := (admitted regionBothSucceed).map fun flow =>
  ((runRegionsCause 20 flow failingService nameOf [] (.nat 5)).run []).run 41

#guard failedAcquisition.map (fun result => result.1.1) =
  some ((.failed (.str "changed then failed"), []), [.str "changed then failed"])
#guard failedAcquisition.map (fun result => result.2) = some 42
#guard failedAcquisition.map (fun result => result.1.1.1.1.stuck) = some false

-- Raw entry into an acquire without its owning frame is genuinely stuck.
def emptyStackAtAcquire :=
  ((regionLoop (tableAlphabet ⟨0⟩ table) regionBothSucceed service nameOf 3
    ⟨1⟩ [.nat 5] [] []).run []).run 41

#guard emptyStackAtAcquire.1.1.1.1 = .frontier (.stuck ⟨1⟩)
#guard emptyStackAtAcquire.1.1.1.1.stuck = true

-- Merely being nonempty does not express ownership. The raw runner closes
-- the stack's region, even when that head disagrees with the leave's label.
def leaveWithHead (region : Nat) :=
  ((regionLoop (tableAlphabet ⟨0⟩ table) regionBothSucceed service nameOf 3
    ⟨2⟩ [.nat 5, .nat 5] [] [{ region := ⟨region⟩, releases := [] }]).run []).run 41

#guard (leaveWithHead 1).1.2 = [.leave 1 (.success (.nat 5)), .done (.success (.nat 5))]
#guard (leaveWithHead 99).1.2 = [.leave 99 (.success (.nat 5)), .done (.success (.nat 5))]
#guard (leaveWithHead 99).1.1.1.1.stuck = false
#guard (leaveWithHead 99).1.2 ≠ (leaveWithHead 1).1.2

-- The fuel-free corollary belongs to the standard handler. Arbitrary scope
-- handlers can answer none; Program equality intentionally retains that arm.
def foreignScopeHandler := (admitted regionBothSucceed).map fun flow =>
  interpret (M := Id) (Effect4Test.Semantics.RegionTotalContract.optionRefusalHandler true)
    (denoteRegionsWF flow [] (.nat 5))

#guard foreignScopeHandler.map (fun result => result.1.1.stuck) = some true

/- BEGIN SAFETY-SURFACE: the exact declarations are deliberately red before implementation. -/

universe uTy

#check (@runRegionsCause_checked_not_stuck :
  {Ty : Type uTy} → [DecidableEq Ty] → {σ : Type} → {alphabet : FlowAlphabet Ty} →
  (fuel : Nat) → (flow : CheckedRegionFlow alphabet) →
  (service : RegionService alphabet (StateT σ Id)) → (nameOf : alphabet.Op → String) →
  (tape : Tape) → (input : Val) → (log : Effect4.Trace.Log) → (state : σ) →
  (((runRegionsCause fuel flow service nameOf tape input).run log).run state).1.1.1.1.stuck = false)

#check (@runRegions_checked_not_stuck :
  {Ty : Type uTy} → [DecidableEq Ty] → {σ : Type} → {alphabet : FlowAlphabet Ty} →
  (fuel : Nat) → (flow : CheckedRegionFlow alphabet) →
  (service : RegionService alphabet (StateT σ Id)) → (nameOf : alphabet.Op → String) →
  (tape : Tape) → (input : Val) → (log : Effect4.Trace.Log) → (state : σ) →
  (((runRegions fuel flow service nameOf tape input).run log).run state).1.1.1.stuck = false)

#check (@interpretRegionsWF_checked_not_stuck :
  {Ty : Type uTy} → [DecidableEq Ty] → {σ : Type} → {alphabet : FlowAlphabet Ty} →
  (flow : CheckedRegionFlow alphabet) →
  (service : RegionService alphabet (StateT σ Id)) → (nameOf : alphabet.Op → String) →
  (tape : Tape) → (input : Val) → (log : Effect4.Trace.Log) → (state : σ) →
  (((interpretRegions service nameOf (denoteRegionsWF flow tape input)).run log).run state).1.1.1.1.stuck = false)

/- END SAFETY-SURFACE -/

end Effect4Test.Semantics.RegionSafetyContract
