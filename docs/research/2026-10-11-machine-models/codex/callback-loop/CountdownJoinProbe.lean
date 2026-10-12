import Effect4.Laws.Machine.Clauses

/-!
Concept: scope-lifetime-finalization R11.
Question: actual completed loser joins for Timeout.cleanup_keeps and retries_declared.
Consumer: the generation instance issues Cleaned only after its held attempt exits.
Missing targets remain skipped; completion alone supplies no cleanup provenance.
-/
set_option autoImplicit false
namespace Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- A completed countdown has no live target among the records it actually holds. -/
theorem countdownWalk_complete (machine : RunMachine ν σ β ε δ ι α χ St)
    (targets : List FiberId) (before after : List (Exit β ε δ ι α))
    (done : countdownWalk machine targets before = (after, none)) :
    ∀ target ∈ targets, ∀ fiber, machine.fiber? target = some fiber →
      ∃ exit, fiber.exit = some exit := by
  induction targets generalizing before after with
  | nil => intro target member; cases member
  | cons head rest ih =>
    cases found : machine.fiber? head with
    | none =>
      simp only [countdownWalk, found] at done
      intro target member fiber held
      rcases List.mem_cons.mp member with equal | later
      · subst target; rw [found] at held; cases held
      · exact ih _ _ done target later fiber held
    | some stored =>
      cases exited : stored.exit with
      | none =>
        simp only [countdownWalk, found, exited] at done
        cases done
      | some exit =>
        simp only [countdownWalk, found, exited] at done
        intro target member fiber held
        rcases List.mem_cons.mp member with equal | later
        · subst target
          have same := Option.some.inj (found.symm.trans held)
          subst fiber
          exact ⟨exit, exited⟩
        · exact ih _ _ done target later fiber held
end Effect4.Machine
