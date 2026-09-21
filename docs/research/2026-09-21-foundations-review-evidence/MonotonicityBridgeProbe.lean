import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Machine.Refinement

/-! Small reusable proof patterns. These do not instantiate an OCaml carrier or prove
machine-wide preservation; their hypotheses deliberately expose those missing bridges. -/
set_option autoImplicit false
namespace FoundationsReview.MonotonicityBridge
open Effect4.Machine Effect4.Machine.Refinement Effect4.Laws.Effects
universe u v w z

/-- Local transport only needs pre/result transport at the two selected worlds.
Global WF monotonicity is not smuggled into a typeclass or a protocol order. -/
theorem typed_transport_at {W : Type w} {S : Effects.Signature.{u, v}} {A : Type v}
    {o : WorldOrder W} {protocol : Protocol W S} {Q : W → A → Prop}
    {before after : W} {p : Effects.Program S A}
    (later : o.le before after)
    (pre : ∀ op, protocol.pre before op → protocol.pre after op)
    (result : ∀ a, Q before a → Q after a)
    (typed : Typed o protocol before Q p) : Typed o protocol after Q p := by
  cases typed with
  | pure h => exact .pure (result _ h)
  | vis hp hk =>
    exact .vis (pre _ hp) (fun future hnext ans hpost =>
      hk future (o.trans later hnext) ans hpost)

/-- A selected model invariant and answer property lift through an actual Projects
instance. Initialization, other state fields and ordered actions are separate obligations. -/
theorem projects_transfers_selected_invariant
    {C : Type u} {M : Type v} {Op : Type w} {Answer : Type z}
    {project : C → M} {stepC : Op → C → Option (C × Answer)}
    {stepM : Op → M → Option (M × Answer)} {WF : C → Prop}
    (bridge : Projects project stepC stepM WF) (P : M → Prop) (Q : Answer → Prop)
    (preserve : ∀ op m m' answer, P m → stepM op m = some (m', answer) → P m' ∧ Q answer)
    {op : Op} {c c' : C} {answer : Answer}
    (valid : WF c) (model : P (project c)) (step : stepC op c = some (c', answer)) :
    WF c' ∧ P (project c') ∧ Q answer := by
  have projected := bridge.step op c valid
  rw [step] at projected
  change some (project c', answer) = stepM op (project c) at projected
  exact ⟨bridge.keeps op c c' answer valid step,
    preserve op (project c) (project c') answer model projected.symm⟩

/-- Index-aware properties transfer through the dense arena's lookup equation, without
replacing a heterogeneous heap by one shared predicate on all values. -/
theorem arena_indexed_lookup_transfer {C A : Type} [Arena C A] [LawfulArena C A]
    (P : Nat → A → Prop) (c : C)
    (typed : ∀ i value, (Arena.toList c)[i]? = some value → P i value) :
    ∀ i value, Arena.peek c i = some value → P i value := by
  intro i value lookup
  rw [Arena.peek_toList] at lookup
  exact typed i value lookup

#print axioms typed_transport_at
#print axioms projects_transfers_selected_invariant
#print axioms arena_indexed_lookup_transfer
#print axioms Arena.list_lawful
#print axioms Arena.toList_alloc
#print axioms Arena.toList_poke
#print axioms refStep_eq_refStepOf
#print axioms refStepOf_keeps
#print axioms toList_refStepOf
#print axioms Refinement.projects_arena
#print axioms Refinement.deferredOk_iff_image
#print axioms Refinement.projects_complete
end FoundationsReview.MonotonicityBridge
