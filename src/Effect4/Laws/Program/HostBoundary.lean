import Effect4.Program.HostBoundary

/-! Proof graph for the boundary classifications and the Resource model's existing
terminal observation. No theorem in this file certifies a JavaScript binding or proves
allocation-aware machine/host refinement; that connection is S6b-2's obligation. -/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

namespace HostBoundaryResult

theorem admitted_without_attempt {HostState : Type} (current : HostState) :
    ofAttempt .admitted current none = .pending current := rfl

theorem malformed_retains_state {HostState : Type} (reason : String) (current : HostState)
    (attempt : Option (Completion Val Err Defect FiberId Ann × HostState)) :
    (ofAttempt (.malformed reason) current attempt).state = current := rfl

theorem outside_profile_retains_state {HostState : Type} (reason : String) (current : HostState)
    (attempt : Option (Completion Val Err Defect FiberId Ann × HostState)) :
    (ofAttempt (.outsideProfile reason) current attempt).state = current := rfl

theorem completed_retains_resulting_state {HostState : Type}
    (before after : HostState) (completion : Completion Val Err Defect FiberId Ann) :
    (ofAttempt .admitted before (some (completion, after))).state = after := rfl

end HostBoundaryResult

namespace Profile.Resource

/-- Index coverage plus actual completed cleanup closes every slot; cleanup of a strict
subset is insufficient. Uses the standard List membership/index and `all` equivalences. -/
theorem owned_cleanup_closes_slots (state : State) (owned : List Nat)
    (howned : OwnsAll state owned) (hclean : CleanupComplete state owned) :
    state.slots.all (fun isOpen => !isOpen) = true := by
  apply List.all_eq_true.mpr
  intro slot hslot
  obtain ⟨index, hindex, hvalue⟩ := List.getElem_of_mem hslot
  have hclosed := hclean index (howned index hindex)
  rw [List.getElem?_eq_getElem hindex] at hclosed
  have heq : slot = false := hvalue.symm.trans (Option.some.inj hclosed)
  simp [heq]

/-- This is exactly Resource.observe (matching count and all slots closed), under concrete
cleanup/ownership premises. It is neither unconditional RelatedState→observe nor a claim
that matching counts establishes handle target/session correctness. -/
theorem terminal_observe (stores : Stores) (state : State) (owned : List Nat)
    (hrelated : RelatedState stores state) (howned : OwnsAll state owned)
    (hclean : CleanupComplete state owned) : observe stores state :=
  ⟨hrelated, owned_cleanup_closes_slots state owned howned hclean⟩

/-- A useful intermediate state has an open resource and still satisfies correspondence. -/
theorem related_open_resource :
    RelatedState { Stores.empty with externals := { ExternalStore.empty with allocated := [target] } }
      ⟨[true], 0⟩ := rfl

/-- The same valid intermediate state fails the terminal cleanup observation. -/
theorem open_resource_not_terminal :
    ¬ observe { Stores.empty with externals := { ExternalStore.empty with allocated := [target] } }
      ⟨[true], 0⟩ := by decide

end Profile.Resource

namespace Profile.Choice

theorem lawful : LawfulHostSpec Scalar.profile spec where
  rep_scalar_bound := Scalar.lawful.rep_scalar_bound
  step_retains := by
    rintro row request before completion after ⟨_, _, hstep⟩
    rcases hstep with ⟨_, hafter⟩ | ⟨_, hafter⟩
    · exact Or.inl hafter
    · exact Or.inr hafter

theorem left_step (state : Nat) :
    spec.RowStep Scalar.waitRow (.nat 0) state
      (.ofExit (.success (.nat 1))) (state + 1) := ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem right_step (state : Nat) :
    spec.RowStep Scalar.waitRow (.nat 0) state
      (.ofExit (.success (.nat 2))) (state + 2) := ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- The general law is inhabited while the separately requested deterministic law fails. -/
theorem not_deterministic : ¬ DeterministicHostSpec spec := by
  intro h
  have hsame := h.step_unique Scalar.waitRow (.nat 0) 0 _ _ _ _ (left_step 0) (right_step 0)
  exact (by decide : (Completion.ofExit (.success (.nat 1)) : Completion Val Err Defect FiberId Ann) ≠
    .ofExit (.success (.nat 2))) hsame.1

end Profile.Choice

end Effect4.Program
