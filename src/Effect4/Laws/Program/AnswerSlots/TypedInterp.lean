import Effect4.Laws.Program.AnswerSlots.TypedActions

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the actual completed-view interpreter retains protected source and acquired identities.
Reach: direct source callbacks, suspension and installed finalizer programs.
Limit: history and initialization require the joint command driver.
Consumer: the stable native head and saved family for the two crews.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Current completed exits leave source paths, leading bindings and protected identities unchanged. -/
theorem interp_contA_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (input output : Kind) (name : EffName) (value : Val)
    (owned : NameAt spec input output name) (good : ValueAt input value) :
    CodeAt spec output ((interpAt spec.root completed spec.table).contA name value) := by
  cases input with
  | root =>
    cases output with
    | root =>
      apply contA_at spec fragment
      cases name <;> exact owned
    | connection identity =>
      cases name
      case cont point => exact acquisition_return spec completed spec.table identity point value owned
      all_goals cases owned
  | connection identity =>
    cases output with
    | root =>
      cases name
      case acquired point ctx scope => exact acquired_callback spec completed spec.table identity point ctx scope value owned good
      all_goals cases owned
    | connection other => cases name <;> cases owned

/-- Current completed exits leave ordinary source cause handlers unchanged. -/
theorem interp_contE_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (input output : Kind) (name : EffName) (cause : CauseV)
    (owned : NameAt spec input output name) :
    CodeAt spec output ((interpAt spec.root completed spec.table).contE name cause) := by
  cases input with
  | root =>
    cases output with
    | root =>
      apply contE_at spec fragment
      cases name <;> exact owned
    | connection identity =>
      cases name
      case cont => trivial
      all_goals cases owned
  | connection identity =>
    cases output with
    | root =>
      cases name
      case acquired => trivial
      all_goals cases owned
    | connection other => cases name <;> cases owned

/-- Current completed exits leave stable suspended source permissions unchanged. -/
theorem interp_suspend_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (thunk : EffThunk) (owned : ThunkAt spec thunk) :
    CodeAt spec .root ((interpAt spec.root completed spec.table).suspendBody thunk) := by
  apply suspend_at spec fragment
  cases thunk <;> exact owned

/-- Stored and native cancellation introduces only existing administrative operations. -/
theorem cancel_at (spec : Spec) (name : EffName) : CodeAt spec .root (cancelProgramOf name) := by
  fun_cases cancelProgramOf name
  all_goals aesop (add norm simp [CodeAt, ValueAt, embed, cancelProgram,
    ThunkAt, OpAt, StoreThunkAt, StoreActionAt, SourceScope.ThunkAt, SourceScope.OpAt,
    SourceScope.StoreThunkAt, SourceScope.StoreActionAt, AnswerSlots.ThunkAt,
    AnswerSlots.OpAt, AnswerSlots.StoreThunkAt, AnswerSlots.StoreActionAt])

/-- The native cancellation wrapper restores failure after the existing cancellation program. -/
theorem interp_cancel_at (spec : Spec) (completed : List (FiberId × ExitV))
    (name : EffName) (cause : CauseV) :
    CodeAt spec .root ((interpAt spec.root completed spec.table).cancelThenFail name cause) :=
  ⟨.root, cancel_at spec name, trivial, trivial, trivial⟩

/-- An installed native finalizer runs its actual source or protected stored capture. -/
theorem interp_fin_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (name : EffName) (exit : ExitV) (body : NCode)
    (owned : OrdinaryName spec name)
    (found : (interpAt spec.root completed spec.table).finalizerProgram name exit = some body) :
    CodeAt spec .root body := by
  cases name
  case fin point =>
    cases found
    apply resolve_source spec fragment
    exact fin_source spec _ _ owned
  case store name =>
    cases name
    case finalizerName fin => cases found; exact finProgram_at spec fin exit owned.2.2
    all_goals cases found
  case scopeClose scope => cases found; exact ⟨rfl, trivial, trivial, trivial⟩
  case restoreCtx previous => cases found; exact ⟨rfl, trivial, trivial, trivial⟩
  all_goals cases found
end Effect4.Program.AnswerSlots.Typed
