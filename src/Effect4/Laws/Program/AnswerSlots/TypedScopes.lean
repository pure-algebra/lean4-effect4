import Effect4.Laws.Program.AnswerSlots.TypedInterp
import Effect4.Laws.Program.NativeScopeStore

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual scope closes return only certified captured crew release programs.
Reach: native state-first scope snapshots, actual close orders and acquired identity captures.
Limit: the coupled command producer supplies registration permission and the carried scope predicate.
Consumer: initialized native action closure and crew release-log history.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Scope storage retains the same acquired capture as the typed code graph. -/
def scopeModel (spec : Spec) : Effect4.Machine.ScopeFields.Model where
  finalizer := FinAt spec
  strategy := SourceScope.StrategyAt spec.root
  sequential := .inl rfl
  closeChild _ := trivial
  detach _ _ := trivial

/-- The protected capture projects to its existing source-scope certificate. -/
theorem fin_lexical (spec : Spec) (fin : FinName) (owned : FinAt spec fin) :
    SourceScope.FinAt spec.root fin := by
  cases fin
  case foreign capture => exact owned.1
  all_goals exact owned

/-- Public close preserves the capture predicate and exposes its actual typed cleanup code. -/
theorem close_public (spec : Spec) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program)
    (owned : Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) state.scopes)
    (found : storesCloseScope scope exit flag state = some (next, program)) :
    Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) next.scopes ∧
      ∀ code, program = some code → CodeAt spec .root (embed code) := by
  unfold storesCloseScope at found
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at found; cases found
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    have slots := Effect4.Machine.ScopeFields.close_snapshot_at (scopeModel spec)
      scope exit state after strategy order owned snapshot
    simp only [snapshot, Option.pure_def] at found
    cases order with
    | nil => cases found; exact ⟨slots.1, fun _ impossible => by cases impossible⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        refine ⟨slots.1, ?_⟩
        intro code same
        cases same
        exact ⟨finProgram_at spec fin exit (slots.2.1 fin (.head _)), trivial⟩
      | cons second tail =>
        cases found
        refine ⟨slots.1, ?_⟩
        intro code same
        cases same
        refine ⟨rfl, ?_, ?_, ?_⟩
        · exact ⟨(fun fin member => fin_lexical spec fin (slots.2.1 fin member)), slots.2.2⟩
        · exact fun fin member => fin_leading spec fin (slots.2.1 fin member)
        · exact slots.2.1

/-- Unsafe scoped close exposes the actual certified captured finalizers. -/
theorem close_unsafe (spec : Spec) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program)
    (owned : Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) state.scopes)
    (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) next.scopes ∧
      ∀ code, program = some code → CodeAt spec .root (embed code) := by
  unfold storesCloseScopeUnsafe at found
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at found; cases found
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    have slots := Effect4.Machine.ScopeFields.close_snapshot_at (scopeModel spec)
      scope exit state after strategy order owned snapshot
    simp only [snapshot, Option.pure_def] at found
    cases order with
    | nil => cases found; exact ⟨slots.1, fun _ impossible => by cases impossible⟩
    | cons fin rest =>
      cases rest with
      | nil =>
        cases found
        refine ⟨slots.1, ?_⟩
        intro code same
        cases same
        exact finProgram_at spec fin exit (slots.2.1 fin (.head _))
      | cons second tail =>
        cases found
        refine ⟨slots.1, ?_⟩
        intro code same
        cases same
        refine ⟨rfl, ?_, ?_, ?_⟩
        · exact ⟨(fun fin member => fin_lexical spec fin (slots.2.1 fin member)), slots.2.2⟩
        · exact fun fin member => fin_leading spec fin (slots.2.1 fin member)
        · exact slots.2.1

/-- The native close hook embeds the actual protected cleanup without assuming a returned program. -/
theorem interp_close (spec : Spec) (completed : List (FiberId × ExitV))
    (scope : Nat) (exit : ExitV) (flag : Bool) (fiber : FiberId)
    (state next : Stores) (program : Option NCode)
    (owned : Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) state.scopes)
    (found : (interpAt spec.root completed spec.table).closeScope scope exit flag fiber state = some (next, program)) :
    Effect4.Machine.ScopeFields.ScopesAt (scopeModel spec) next.scopes ∧
      ∀ code, program = some code → CodeAt spec .root code := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, program) at found
  obtain ⟨⟨after, closing⟩, operation, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  have closed := close_public spec scope exit flag state after closing owned operation
  refine ⟨closed.1, ?_⟩
  intro code same
  cases closing with
  | none => cases same
  | some body => cases same; exact closed.2 body rfl
end Effect4.Program.AnswerSlots.Typed
