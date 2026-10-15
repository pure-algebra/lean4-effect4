import Effect4.Laws.Program.FinalizerIterations
import Effect4.Laws.Program.CodeClosure.Family

/-!
Concept: scope-lifetime-finalization R11.
Question: actual interpreter closure for `once_placed_outside_census`.
Consumer: the common saved-family producer and full source frame debit.
The completed-exit view changes no source reservation or parameter-frame annotation.
These local interpreter facts establish no history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Actual value invocation retains the full source annotation and saved reservation. -/
theorem interp_value (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (value : Val) (placed : OncePlaced (.eff root) q = true)
    (held : NameAt q callback) :
    TemplateAt q ((interpAt root view table).contA callback value) ∧
      current root q ((interpAt root view table).contA callback value) ≤ savedSuccess q (name q) callback := by
  cases callback
  case cont point => exact value_callback root q (.cont {point with completed := view}) value placed held
  case onValue point => exact value_callback root q (.onValue {point with completed := view}) value placed held
  all_goals exact value_callback root q _ value placed held

/-- Actual cause invocation retains the full source annotation and handler reservation. -/
theorem interp_cause (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (cause : CauseV) (held : NameAt q callback) :
    TemplateAt q ((interpAt root view table).contE callback cause) ∧
      current root q ((interpAt root view table).contE callback cause) ≤ name q callback := by
  cases callback
  case caught point => exact cause_callback root q (.caught {point with completed := view}) cause held
  case onCause point => exact cause_callback root q (.onCause {point with completed := view}) cause held
  case caughtError point => exact cause_callback root q (.caughtError {point with completed := view}) cause held
  all_goals exact cause_callback root q _ cause held

/-- Actual suspension invocation retains the full source annotation and body reservation. -/
theorem interp_suspend (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (suspension : EffThunk) (placed : OncePlaced (.eff root) q = true) (held : ThunkAt q suspension) :
    TemplateAt q ((interpAt root view table).suspendBody suspension) ∧
      current root q ((interpAt root view table).suspendBody suspension) ≤ thunk root q suspension := by
  cases suspension
  case body point => exact suspended root q (.body {point with completed := view}) placed held
  all_goals exact suspended root q _ placed held

/-- Stored cancellation exposes only administrative programs. -/
theorem stored_cancel (root : NativeEff) (q : List Nat) (callback : Name) :
    TemplateAt q (embed (cancelProgram callback)) ∧ current root q (embed (cancelProgram callback)) = 0 := by
  refine ⟨embedded_code q _ (CodeClosure.Slots.store_cancel_at (PointAt q) (fun _ => True) callback), ?_⟩
  fun_cases cancelProgram callback
  all_goals rfl

/-- Native cancellation retains no selected source reservation. -/
theorem cancellation (root : NativeEff) (q : List Nat) (callback : EffName) :
    TemplateAt q (cancelProgramOf callback) ∧ current root q (cancelProgramOf callback) = 0 := by
  fun_cases cancelProgramOf callback
  case case2 base waiter token => exact stored_cancel root q (.withWaiter base waiter token)
  case case3 name => exact stored_cancel root q name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt,
    NameAt, ThunkAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt,
    CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreThunkAt,
    CodeClosure.Qualified.StoreThunkAt, CodeClosure.Qualified.StoreActionAt, CodeClosure.Qualified.OpAt,
    current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, embed])

/-- Administrative cancellation reuses the existing stored-code closure. -/
theorem interp_cancel_at (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (cause : CauseV) :
    TemplateAt q ((interpAt root view table).cancelThenFail callback cause) := by
  have closed := (cancellation root q callback).1
  change TemplateAt q (.onSuccess (cancelProgramOf callback) (.reFail cause))
  aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, NameAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt])

/-- Actual finalizer invocation retains its annotation and selected descendant reservation. -/
theorem interp_finalizer (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (exit : ExitV) (body : NCode) (held : NameAt q callback)
    (found : (interpAt root view table).finalizerProgram callback exit = some body) :
    TemplateAt q body ∧ current root q body ≤ name q callback := by
  cases callback
  case fin point =>
    cases found
    exact ⟨resolve_at root q _ held, resolve_le root q _⟩
  case store callback =>
    cases callback
    case finalizerName fin =>
      cases found
      exact ⟨finalizer_at q fin exit held, Nat.le_of_eq (fin_program_zero root q fin exit)⟩
    all_goals cases found
  case scopeClose scope => cases found; exact ⟨⟨trivial, trivial⟩, Nat.le_refl _⟩
  case restoreCtx previous => cases found; exact ⟨⟨trivial, trivial⟩, Nat.le_refl _⟩
  all_goals cases found

/-- Finalizer exit restoration adds no source reservation. -/
theorem finalizer_code (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (exit : ExitV) (body : NCode) (held : TemplateAt q body) :
    TemplateAt q (finalizerCode (interpAt root view table) exit body) ∧
      current root q (finalizerCode (interpAt root view table) exit body) = current root q body := by
  cases exit with
  | success value =>
    refine ⟨⟨⟨held.1, trivial⟩, ?_⟩, Nat.add_zero _⟩
    exact CodeClosure.registration_success body (.restore (.success value)) held.2
      (by intro acquired fin same; cases same)
  | failure cause =>
    refine ⟨⟨⟨⟨held.1, trivial⟩, trivial⟩, ?_⟩, ?_⟩
    · exact CodeClosure.registration_success (.onFailure body (.merge (.failure cause)))
        (.restore (.failure cause)) ⟨held.2, trivial⟩
        (by intro acquired fin same; cases same)
    · change current root q body + 0 + 0 = current root q body
      omega

/-- The unrestricted source instance supplies the existing callback-closure interface. -/
theorem hooks (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.Family.Hooks root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q) where
  value := fun view callback value held => (interp_value root q view table callback value placed held).1.1
  bothValue := fun view callback value held => (interp_value root q view table callback value placed (ordinary_name q callback held)).1.1
  cause := fun view callback cause held => (interp_cause root q view table callback cause (ordinary_name q callback held)).1.1
  suspend := fun view suspension held => (interp_suspend root q view table suspension placed held).1.1
  iterator := by
    intro view callback value held
    have closed := (interp_iter root q view table callback value placed (ordinary_name q callback held)).1
    cases actual : ((interpAt root view table).iterNext callback value).2
    case resume body next => rw [actual] at closed; exact ⟨closed.1.1, closed.2⟩
    all_goals trivial
  loopEnter := by
    intro view callback cursor held
    have closed := (interp_loop_enter root q view table callback cursor placed (ordinary_name q callback held)).1
    cases actual : (interpAt root view table).loopEnter callback cursor <;> rw [actual] at closed
    all_goals exact closed.1
  loopResume := by
    intro view callback cursor answer held
    have closed := (interp_loop_resume root q view table callback cursor answer placed (ordinary_name q callback held)).1
    cases actual : (interpAt root view table).loopResume callback cursor answer <;> rw [actual] at closed
    all_goals exact closed.1
  cancel := fun view callback cause => (interp_cancel_at root q view table callback cause).1
  finalizer := fun view callback exit body held found => (interp_finalizer root q view table callback exit body (ordinary_name q callback held) found).1.1
  restore := by
    intro view exit body held
    cases exit
    · exact ⟨held, trivial⟩
    · exact ⟨⟨held, trivial⟩, trivial⟩

/-- Full source annotations instantiate the common saved-frame and current-head producer. -/
def stableLaws (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    AnswerSlots.StableLaws (CodeClosure.Family.sourceSpec root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q)) :=
  CodeClosure.Family.sourceLaws root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q) (hooks root q table placed)

/-- The full annotation supplies the shared primitive-arm contract without another walk. -/
theorem templateArms (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.Arms.Rules (TemplateAt q) (interpAt root view table).toPrimInterp where
  success _ := ⟨trivial, trivial⟩
  failure _ := ⟨trivial, trivial⟩
  value body callback value held := (interp_value root q view table callback value placed held.1.2).1
  constant body next held := ⟨held.1.2, held.2.2.1⟩
  bothValue body callback other value held :=
    (interp_value root q view table callback value placed (ordinary_name q callback held.1.2.1)).1
  cause body callback cause held :=
    (interp_cause root q view table callback cause (ordinary_name q callback held.1.2)).1
  bothCause body other callback cause held :=
    (interp_cause root q view table callback cause (ordinary_name q callback held.1.2.2)).1
  cancel callback cause _ := interp_cancel_at root q view table callback cause
  iterator := by
    intro callback cursor value held
    have closed := (interp_iter root q view table callback value placed (ordinary_name q callback held.1)).1
    cases actual : ((interpAt root view table).iterNext callback value).2
    case resume body next =>
      rw [actual] at closed
      exact ⟨closed.1, fun _ => ⟨closed.2, trivial⟩⟩
    all_goals trivial
  loop := by
    intro callback cursor answer held
    have closed := (interp_loop_resume root q view table callback cursor answer placed (ordinary_name q callback held.1)).1
    cases actual : (interpAt root view table).loopResume callback cursor answer
    case «continue» next body =>
      rw [actual] at closed
      exact ⟨closed, held⟩
    case finish body => rw [actual] at closed; exact closed

/-- The exact registration relation accompanies source slots through every actual callback. -/
theorem templateRules (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.PredicateFamily.Rules root table (TemplateAt q) where
  success _ := ⟨trivial, trivial⟩
  failure _ := ⟨trivial, trivial⟩
  mask _ := ⟨trivial, trivial⟩
  children := by
    intro code held
    cases code
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.PredicateFamily.Children])
  suspend := by
    intro view thunk held
    rcases held with held | held
    all_goals exact (interp_suspend root q view table thunk placed held.1).1
  value := fun view => CodeClosure.Arms.value _ _ (templateArms root q view table placed)
  cause := fun view => CodeClosure.Arms.cause _ _ (templateArms root q view table placed)
  loopContinue := by
    intro view callback cursor next body held found
    have closed := (interp_loop_enter root q view table callback cursor placed (ordinary_name q callback held.1)).1
    rw [found] at closed
    exact ⟨closed, held⟩
  loopFinish := by
    intro view callback cursor body held found
    have closed := (interp_loop_enter root q view table callback cursor placed (ordinary_name q callback held.1)).1
    rw [found] at closed
    exact closed
  finalizer := by
    intro view frame exit next held installed
    cases frame
    case onExit body callback flag =>
      obtain ⟨program, found, equal⟩ := Option.map_eq_some_iff.mp installed
      rw [← equal]
      exact (finalizer_code root q view table exit program
        (interp_finalizer root q view table callback exit program
          (ordinary_name q callback held.1.2) found).1).1
    all_goals cases installed

/-- Full source slots and registration bodies use the common stable-family producer. -/
def templateLaws (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    AnswerSlots.StableLaws (CodeClosure.PredicateFamily.spec root table (TemplateAt q)
      (templateRules root q table placed)) :=
  CodeClosure.PredicateFamily.laws root table (TemplateAt q) (templateRules root q table placed)

end Effect4.Program.FinalizerSource
