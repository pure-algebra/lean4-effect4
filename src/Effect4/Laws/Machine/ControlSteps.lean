import Effect4.Laws.Machine.Lift
import Effect4.Laws.Auto.Semantics

/-!
# Arbitrary-fiber command steps

These equations serve `fiber-local-positions`, proposed in the goals packet, under
`reactive-scheduling`. The consumers are the worker stage rules and the store-site invariant.
They reach any machine and evaluator, under the stated lookup, yield and interruption premises.
They establish no stage closure, provenance, control linearity, progress or host agreement.
The command loop transcribes rc.112 `internal/effect.ts:638-655` and `:662-667`.
-/

set_option autoImplicit false

namespace Effect4.Machine.ControlSteps

open Effect4 Effect4.Machine

universe u v

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An iteration below its budget, with no pending interrupt or override, evaluates
one charged primitive. A step of `fiber-local-positions`; the native store rule consumes it. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem iteration_below_budget (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (interrupt : core.deferredInterrupt f.frame = false)
    (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    iteration interp m f yielding = evaluator.evaluate interp m (countOp f) yielding := by
  have top : runloopTop f = f := by
    simp only [runloopTop, interrupt, Bool.false_eq_true, ↓reduceIte]
  have verdict : yieldVerdict (countOp f) = false := by
    simp only [yieldVerdict, countOp, override, Option.getD_none]
    exact decide_eq_false (Nat.not_le.mpr budget)
  have injection : injectYield m (countOp f) yielding = none := by
    simp only [injectYield, verdict, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp only [iteration, top, injection]

/-- A loop command commits an arbitrary evaluator result and retains its pending commands.
A step of `fiber-local-positions`; native store and stage rules consume it. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem loop_of_iteration (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (rest : List (Cmd ν σ β ε δ ι α κ))
    (found : m.fiber? id = some f) :
    driveStep interp m (.loop id yielding) rest = settle id rest (iteration interp m f yielding) := by
  simp only [driveStep, found]

/-- One remaining command budget commits the current step before the following fuel cut.
A step of `fiber-local-positions`; the worker probe consumes it with symbolic residue. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem driveState_loop (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (yielding : Bool)
    (rest : List (Cmd ν σ β ε δ ι α κ))
    (live : m.stuck = none) (found : m.fiber? id = some f) :
    driveState interp (fuel + 1) m (.loop id yielding :: rest) =
      driveState interp fuel (settle id rest (iteration interp m f yielding)).1
        (settle id rest (iteration interp m f yielding)).2 := by
  rw [driveState_succ_cons]
  simp only [live, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    loop_of_iteration interp m id f yielding rest found]

end Effect4.Machine.ControlSteps
