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
    CodeAt q ((interpAt root view table).contA callback value) ∧
      current root q ((interpAt root view table).contA callback value) ≤ savedSuccess q (name q) callback := by
  cases callback
  case cont point => exact value_callback root q (.cont {point with completed := view}) value placed held
  case onValue point => exact value_callback root q (.onValue {point with completed := view}) value placed held
  all_goals exact value_callback root q _ value placed held

/-- Actual cause invocation retains the full source annotation and handler reservation. -/
theorem interp_cause (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (cause : CauseV) (held : NameAt q callback) :
    CodeAt q ((interpAt root view table).contE callback cause) ∧
      current root q ((interpAt root view table).contE callback cause) ≤ name q callback := by
  cases callback
  case caught point => exact cause_callback root q (.caught {point with completed := view}) cause held
  case onCause point => exact cause_callback root q (.onCause {point with completed := view}) cause held
  case caughtError point => exact cause_callback root q (.caughtError {point with completed := view}) cause held
  all_goals exact cause_callback root q _ cause held

/-- Actual suspension invocation retains the full source annotation and body reservation. -/
theorem interp_suspend (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (suspension : EffThunk) (placed : OncePlaced (.eff root) q = true) (held : ThunkAt q suspension) :
    CodeAt q ((interpAt root view table).suspendBody suspension) ∧
      current root q ((interpAt root view table).suspendBody suspension) ≤ thunk root q suspension := by
  cases suspension
  case body point => exact suspended root q (.body {point with completed := view}) placed held
  all_goals exact suspended root q _ placed held

/-- Stored cancellation exposes only administrative programs. -/
theorem stored_cancel (root : NativeEff) (q : List Nat) (callback : Name) :
    CodeAt q (embed (cancelProgram callback)) ∧ current root q (embed (cancelProgram callback)) = 0 := by
  refine ⟨embedded_code q _ (CodeClosure.Slots.store_cancel_at (PointAt q) (fun _ => True) callback), ?_⟩
  fun_cases cancelProgram callback
  all_goals rfl

/-- Native cancellation retains no selected source reservation. -/
theorem cancellation (root : NativeEff) (q : List Nat) (callback : EffName) :
    CodeAt q (cancelProgramOf callback) ∧ current root q (cancelProgramOf callback) = 0 := by
  fun_cases cancelProgramOf callback
  case case2 base waiter token => exact stored_cancel root q (.withWaiter base waiter token)
  case case3 name => exact stored_cancel root q name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, OrdinaryNameAt,
    NameAt, ThunkAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt,
    CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreThunkAt,
    CodeClosure.Qualified.StoreThunkAt, CodeClosure.Qualified.StoreActionAt, CodeClosure.Qualified.OpAt,
    current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, embed])

/-- Administrative cancellation reuses the existing stored-code closure. -/
theorem interp_cancel_at (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (cause : CauseV) :
    CodeAt q ((interpAt root view table).cancelThenFail callback cause) := ⟨(cancellation root q callback).1, trivial⟩

/-- Actual finalizer invocation retains its annotation and selected descendant reservation. -/
theorem interp_finalizer (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (exit : ExitV) (body : NCode) (held : NameAt q callback)
    (found : (interpAt root view table).finalizerProgram callback exit = some body) :
    CodeAt q body ∧ current root q body ≤ name q callback := by
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
  case scopeClose scope => cases found; exact ⟨trivial, Nat.le_refl _⟩
  case restoreCtx previous => cases found; exact ⟨trivial, Nat.le_refl _⟩
  all_goals cases found

/-- Finalizer exit restoration adds no source reservation. -/
theorem finalizer_code (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (exit : ExitV) (body : NCode) (held : CodeAt q body) :
    CodeAt q (finalizerCode (interpAt root view table) exit body) ∧
      current root q (finalizerCode (interpAt root view table) exit body) = current root q body := by
  cases exit with
  | success value => exact ⟨⟨held, trivial⟩, Nat.add_zero _⟩
  | failure cause =>
    refine ⟨⟨⟨held, trivial⟩, trivial⟩, ?_⟩
    change current root q body + 0 + 0 = current root q body
    omega

/-- The unrestricted source instance supplies the existing callback-closure interface. -/
theorem hooks (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.Family.Hooks root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q) where
  value := fun view callback value held => (interp_value root q view table callback value placed held).1
  bothValue := fun view callback value held => (interp_value root q view table callback value placed (ordinary_name q callback held)).1
  cause := fun view callback cause held => (interp_cause root q view table callback cause (ordinary_name q callback held)).1
  suspend := fun view suspension held => (interp_suspend root q view table suspension placed held).1
  iterator := fun view callback value held => (interp_iter root q view table callback value placed (ordinary_name q callback held)).1
  loopEnter := fun view callback cursor held => (interp_loop_enter root q view table callback cursor placed (ordinary_name q callback held)).1
  loopResume := fun view callback cursor answer held => (interp_loop_resume root q view table callback cursor answer placed (ordinary_name q callback held)).1
  cancel := fun view callback cause => interp_cancel_at root q view table callback cause
  finalizer := fun view callback exit body held found => (interp_finalizer root q view table callback exit body (ordinary_name q callback held) found).1
  restore := fun view exit body held => (finalizer_code root q view table exit body held).1

/-- Full source annotations instantiate the common saved-frame and current-head producer. -/
def stableLaws (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    AnswerSlots.StableLaws (CodeClosure.Family.sourceSpec root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q)) :=
  CodeClosure.Family.sourceLaws root table (OrdinaryNameAt q) (NameAt q) (ThunkAt q) (hooks root q table placed)

end Effect4.Program.FinalizerSource
