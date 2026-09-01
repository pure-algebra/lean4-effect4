import Std

/-!
# Interruption boundary data

This module owns the finite mask and cleanup alphabets and the one value a
scheduler needs in order to record interruption. The terminal observation
type itself remains external.
-/

namespace Effect4

universe u

/-- Whether delivery of an interruption is currently deferred. -/
inductive InterruptMask
  | unmasked
  | masked
deriving DecidableEq, Repr

/-- The cleanup phase retained independently of the terminal observation. -/
inductive CleanupState
  | notStarted
  | pending
  | done
deriving DecidableEq, Repr

/-- The distinguished terminal observation used when interruption is delivered. -/
structure InterruptBoundary (τ : Type u) where
  interrupted : τ

namespace InterruptMask

/-- Exhaustive local receipt for the passive mask alphabet. -/
theorem cases_receipt (mask : InterruptMask) :
    mask = unmasked \/ mask = masked := by
  cases mask <;> simp

end InterruptMask

namespace CleanupState

/-- Exhaustive local receipt for the passive cleanup alphabet. -/
theorem cases_receipt (cleanup : CleanupState) :
    cleanup = notStarted \/ cleanup = pending \/ cleanup = done := by
  cases cleanup <;> simp

end CleanupState

end Effect4
