import Test.Dogfood.Scenario.Atomic.Model

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the exact downstream-exit implication in `Atomic.Store.shop_stages`.
A non-fail reason survives cause combination and excludes a failure-only result.
These cause facts assert no runtime interruption or cleanup producer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program

/-- A failure-only, nonempty cause is the only cause class whose final exit needs cleanup evidence. -/
def NeedsCleanup (cause : CauseV) : Prop :=
  (∃ reason, reason ∈ cause.reasons) ∧ ∀ reason ∈ cause.reasons, reason.tag = .fail

/-- An actual non-fail reason distinguishes an interrupted finalizer from a failure-only result. -/
def MarkedCause (cause : CauseV) : Prop := ∃ reason ∈ cause.reasons, reason.tag ≠ .fail

/-- A real non-fail reason excludes the failure-only observation premise. -/
theorem MarkedCause.not_needs {cause : CauseV} (marked : MarkedCause cause) : ¬ NeedsCleanup cause := by
  obtain ⟨reason, member, different⟩ := marked
  exact fun needed => different (needed.2 reason member)

/-- An actual interruption supplies a non-fail reason before any annotation is added. -/
theorem MarkedCause.interrupt (who : Option FiberId) : MarkedCause (Cause.interrupt who) :=
  ⟨.interrupt who .empty, List.mem_singleton_self _, by intro impossible; cases impossible⟩

/-- Actual cause annotation retains the same non-fail reason tag. -/
theorem MarkedCause.annotate (cause : CauseV) (extra : ReasonAnnotations Ann) (overwrite : Bool)
    (marked : MarkedCause cause) : MarkedCause (cause.annotate extra overwrite) := by
  obtain ⟨reason, member, different⟩ := marked
  refine ⟨reason.annotate extra overwrite, ?_, ?_⟩
  · rw [Cause.annotate_reasons]
    exact List.mem_map.mpr ⟨reason, member, rfl⟩
  · rw [Reason.annotate_tag]
    exact different

/-- The real native interrupt delta retains its reason through target and caller annotations. -/
theorem native_interrupt_marked
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) :
    MarkedCause (interruptCause interp who extra target) := by
  unfold interruptCause Supervision.interruptCause
  exact MarkedCause.annotate _ extra false
    (MarkedCause.annotate _ (interp.stackAnnotations target) false (MarkedCause.interrupt _))

/-- Removing typed failures retains the actual non-fail reason. -/
theorem MarkedCause.stripFail (cause : CauseV) (marked : MarkedCause cause) : MarkedCause cause.stripFail := by
  obtain ⟨reason, member, different⟩ := marked
  exact ⟨reason, (Cause.mem_stripFail reason cause).mpr ⟨member, different⟩, different⟩

/-- Combining retains the actual non-fail reason from the right operand. -/
theorem MarkedCause.combine_right (before after : CauseV) (marked : MarkedCause after) :
    MarkedCause (Cause.combine before after) := by
  obtain ⟨reason, member, different⟩ := marked
  exact ⟨reason, (Cause.mem_combine reason before after).mpr (.inr member), different⟩

/-- Combining retains the actual non-fail reason from the left operand. -/
theorem MarkedCause.combine_left (before after : CauseV) (marked : MarkedCause before) :
    MarkedCause (Cause.combine before after) := by
  obtain ⟨reason, member, different⟩ := marked
  exact ⟨reason, (Cause.mem_combine reason before after).mpr (.inl member), different⟩

/-- A failure-only combined cause obtains its nonempty typed evidence from the original body. -/
theorem NeedsCleanup.before_untyped (before after : CauseV)
    (untyped : ∀ reason ∈ after.reasons, reason.tag ≠ .fail)
    (needed : NeedsCleanup (Cause.combine before after)) : NeedsCleanup before := by
  obtain ⟨⟨reason, member⟩, typed⟩ := needed
  have isFail := typed reason member
  have prior : reason ∈ before.reasons := by
    rcases (Cause.mem_combine reason before after).mp member with prior | later
    · exact prior
    · exact False.elim (untyped reason later isFail)
  exact ⟨⟨reason, prior⟩, fun other present => typed other ((Cause.mem_combine other before after).mpr (.inl present))⟩

/-- The scenario's exact downstream singleton supplies the failure-only observation premise. -/
theorem downstream_needs : NeedsCleanup (Cause.fail (Err.tagged "Downstream" "unavailable")) := by
  refine ⟨⟨.fail (Err.tagged "Downstream" "unavailable") .empty, List.mem_singleton_self _⟩, ?_⟩
  intro reason member
  rw [List.mem_singleton.mp member]
  rfl
end Test.Dogfood.Scenario.Atomic.StageWorld
