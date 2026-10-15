import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Question: administrative waiting selects an existing exit answer or the supplied park code.
Consumers: initialized crew command closure and selected-source command funding.
The producer is generic in the code predicate and establishes no wait progress.
-/
set_option autoImplicit false
namespace Effect4.Machine
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St κ φ η : Type (max u v)}

/-- Actual waiting preserves every predicate satisfied by exit answers and park code. -/
theorem awaitCode_closed (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (P : κ → Prop) (exited : ∀ exit mode, P (interp.exitValue exit mode))
    (parked : ∀ kind, P (interp.parkCode kind))
    (machine : RunMachine ν σ β ε δ ι α χ St κ φ η) (kind : ParkKind) :
    P (awaitCode interp machine kind) := by
  fun_cases awaitCode interp machine kind
  all_goals aesop (add safe apply [exited, parked])

end Effect4.Machine
