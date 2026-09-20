/-!
The two representation-connection shapes from the observation packet §2.4, retained by
packet 2 §1. These are proof-side interfaces. Their instances and lifting proofs belong to
the corresponding representation slice; no historical store copy or decoding fallback is
part of either shape.
-/

set_option autoImplicit false

namespace Effect4.Machine.Refinement

universe u v w z

/-- A concrete step projects to one model step with the same answer, and retains the
concrete invariant needed by the next step. -/
structure Projects {C : Type u} {M : Type v} {Op : Type w} {Answer : Type z}
    (project : C → M)
    (stepC : Op → C → Option (C × Answer))
    (stepM : Op → M → Option (M × Answer))
    (WF : C → Prop) : Prop where
  step : ∀ o c, WF c →
    (stepC o c).map (fun (c', a) => (project c', a)) = stepM o (project c)
  keeps : ∀ o c c' a, WF c → stepC o c = some (c', a) → WF c'

/-- Related stores match successful steps and unanswered frontiers. Initialization and
any progress obligation for a machine lifting are supplied by that instance. -/
structure Refines {C : Type u} {M : Type v} {Op : Type w} {Answer : Type z}
    (related : C → M → Prop)
    (stepC : Op → C → Option (C × Answer))
    (stepM : Op → M → Option (M × Answer)) : Prop where
  step : ∀ o c m c' a, related c m → stepC o c = some (c', a) →
    ∃ m' a', stepM o m = some (m', a') ∧ a = a' ∧ related c' m'
  frontier : ∀ o c m, related c m → stepC o c = none → stepM o m = none

end Effect4.Machine.Refinement
