import Effect4.Laws.Machine.ScopeFields

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual close results retain the supplied program assertion.
Consumers: lexical source ownership and FinalizerRun.once_placed_outside_census.
The three program constructors share the existing captured finalizer invariant.
These local facts establish no execution count, history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.ScopeFields
open Effect4 Effect4.Machine

/-- A close exposes captured finalizers, a void continuation, or their stored close walk. -/
structure ClosePrograms (model : Model) (P : Program → Prop) : Prop where
  finalizer : ∀ fin exit, model.finalizer fin → P (finProgram fin exit)
  void : ∀ body, P body → P (.onSuccessConst body (.success .unit))
  walk : ∀ strategy order exit, model.strategy strategy → (∀ fin ∈ order, model.finalizer fin) →
    P (.suspend (.body (.closeWalk strategy order exit)))

/-- Unsafe close returns only programs from the captured finalizer order. -/
theorem close_unsafe_at (model : Model) (P : Program → Prop) (programs : ClosePrograms model P) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (owned : ScopesAt model state.scopes)
    (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    ScopesAt model next.scopes ∧ ∀ code ∈ program, P code := by
  unfold storesCloseScopeUnsafe at found
  cases h : scopeCloseSnapshot scope exit state with
  | none => rw [h] at found; cases found
  | some snapshot =>
    rcases snapshot with ⟨after, strategy, order⟩
    have slots := close_snapshot_at model scope exit state after strategy order owned h
    simp only [h, Option.pure_def] at found
    cases order with
    | nil =>
      cases found
      exact ⟨slots.1, by intro code member; cases member⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        exact ⟨slots.1, fun code member => by
          rw [Option.mem_def] at member
          cases member
          exact programs.finalizer fin exit (slots.2.1 fin (.head _))⟩
      | cons second tail =>
        cases found
        exact ⟨slots.1, fun code member => by
          rw [Option.mem_def] at member
          cases member
          exact programs.walk _ _ exit slots.2.2 slots.2.1⟩

/-- Public close returns the same owned finalizers and its administrative void continuation. -/
theorem close_public_at (model : Model) (P : Program → Prop) (programs : ClosePrograms model P) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (owned : ScopesAt model state.scopes)
    (found : storesCloseScope scope exit flag state = some (next, program)) :
    ScopesAt model next.scopes ∧ ∀ code, program = some code → P code := by
  unfold storesCloseScope at found
  cases h : scopeCloseSnapshot scope exit state with
  | none => rw [h] at found; cases found
  | some snapshot =>
    rcases snapshot with ⟨after, strategy, order⟩
    have slots := close_snapshot_at model scope exit state after strategy order owned h
    simp only [h, Option.pure_def] at found
    cases order with
    | nil => cases found; exact ⟨slots.1, fun _ none => by cases none⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        exact ⟨slots.1, fun _ same => by
          cases same
          exact programs.void _ (programs.finalizer fin exit (slots.2.1 fin (.head _)))⟩
      | cons second tail => cases found; exact ⟨slots.1, fun _ same => by cases same; exact programs.walk _ _ exit slots.2.2 slots.2.1⟩


end Effect4.Machine.ScopeFields
