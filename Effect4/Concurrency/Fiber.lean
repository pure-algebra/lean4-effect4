import Effect4.Concurrency.Interrupt

/-!
# Fiber identity and lifecycle state

Fiber state is passive first-order data. Terminal observations are supplied
by the caller, while interruption and cleanup bookkeeping remain explicit.
-/

namespace Effect4

universe u

/-- Nominal identity within one scheduler machine. -/
structure FiberId where
  value : Nat
deriving DecidableEq, Repr

/-- The representative lifecycle phases visible to the scheduler. -/
inductive FiberStatus
  | runnable
  | running
  | waiting (target : FiberId)
  | finalizing
  | done
deriving DecidableEq, Repr

namespace FiberStatus

/-- Phases in which body work may still be scheduled or interrupted. -/
def Active : FiberStatus -> Prop
  | runnable | running | waiting _ => True
  | finalizing | done => False

/-- The active phases are exactly runnable, running, and waiting. -/
theorem active_iff (status : FiberStatus) :
    Active status <->
      status = runnable \/ status = running \/
        exists target, status = waiting target := by
  cases status <;> simp [Active]

/-- Activity is decidable without inspecting a terminal observation. -/
def activeDecidable (status : FiberStatus) : Decidable (Active status) := by
  cases status with
  | runnable | running | waiting => exact isTrue trivial
  | finalizing | done => exact isFalse (fun impossible => impossible)

/-- Exhaustive local receipt for the passive lifecycle alphabet. -/
theorem cases_receipt (status : FiberStatus) :
    status = runnable \/ status = running \/
      (exists target, status = waiting target) \/
      status = finalizing \/ status = done := by
  cases status <;> simp

end FiberStatus

/-- All scheduler-visible state of one fiber. -/
structure FiberState (τ : Type u) where
  id : FiberId
  status : FiberStatus
  terminal : Option τ
  mask : InterruptMask
  interruptPending : Bool
  cleanup : CleanupState
  cleanupCount : Nat

end Effect4
