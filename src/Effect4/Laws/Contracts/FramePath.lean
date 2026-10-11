import Effect4.Laws.Auto.RuleSets

/-!
Concept: scope-lifetime-finalization R11.
Question: the saved-stack path serves typed registration and native answer transport.
Reach: arbitrary edge predicates over existing frame data, with exact endpoints.
Consumers: Typed.Contracts.FramePath and PopTrace's external-family transport.
This carrier supplies no callback or cause admissibility premise.
-/
set_option autoImplicit false
namespace Effect4.Contracts
universe u v
variable {Object : Type u} {Frame : Type v}

inductive Path (Edge : Object → Object → Frame → Prop) :
    Object → Object → List Frame → Prop
  | nil (ty : Object) : Path Edge ty ty []
  | cons {tin middle tout : Object} {frame : Frame} {rest : List Frame}
      (head : Edge tin middle frame) (tail : Path Edge middle tout rest) :
      Path Edge tin tout (frame :: rest)

namespace Path
variable {E E' : Object → Object → Frame → Prop}

/-- An edge map, endpoints and frames kept, maps paths. -/
theorem map (f : ∀ a b frame, E a b frame → E' a b frame) {a b : Object} {s : List Frame}
    (h : Path E a b s) : Path E' a b s := by
  induction h with
  | nil ty => exact .nil ty
  | cons head _ ih => exact .cons (f _ _ _ head) ih

theorem append {a b c : Object} {s₁ s₂ : List Frame} (h₁ : Path E a b s₁)
    (h₂ : Path E b c s₂) : Path E a c (s₁ ++ s₂) := by
  induction h₁ with
  | nil ty => exact h₂
  | cons head _ ih => exact .cons head (ih h₂)

theorem split : ∀ (s₁ s₂ : List Frame) {a c : Object}, Path E a c (s₁ ++ s₂) →
    ∃ b, Path E a b s₁ ∧ Path E b c s₂
  | [], _, a, _, h => ⟨a, .nil a, h⟩
  | f :: s₁, s₂, _, _, h => by
    rw [List.cons_append] at h
    cases h with
    | cons head tail =>
      obtain ⟨b, h₁, h₂⟩ := split s₁ s₂ tail
      exact ⟨b, .cons head h₁, h₂⟩

end Path

end Effect4.Contracts
