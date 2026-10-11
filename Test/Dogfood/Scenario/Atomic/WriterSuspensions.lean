import Test.Dogfood.Scenario.Atomic.WriterCallbacks

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: native suspended-source and repeated-body writer debit of Atomic.Cleanup.log_debits.
The laws use the existing source fragment and actual stored names.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterSuspensions
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterSource

/-- The actual shop has no captured acquisition-release constructor. -/
def noAcquisition (node : Node NativeOp) : Bool :=
  match node with
  | .eff (.acquireRelease _ _) => false
  | _ => true

theorem acquisitions_census :
    (Store.shopProgram.map fun root => (Node.addresses (.eff root)).all fun path =>
      (Node.at_ (.eff root) path).all noAcquisition) = some true := by kernel_rfl

theorem acquisition_absent (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (path : List Nat) : ¬ AcquisitionAt built.program path := by
  rintro ⟨acquire, release, found⟩
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := acquisitions_census
  rw [source] at checked
  have present := (mem_addresses_iff (.eff built.program) path).mpr (by rw [found]; rfl)
  have selected := List.all_eq_true.mp (Option.some.inj checked) path present
  rw [found] at selected
  cases selected

/-- A decided source branch cannot issue a finalizer's note allowance. -/
theorem select_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (term : Term) (decision : Decision)
    (yes no : NativeEff) (value : Val) (first : Bool) (bound : Option Val)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.select term decision yes no)))
    (scope : At built.program point) (answer : decision.decide value = some (first, bound)) :
    current id (resolve built.program (point.childBind (cond first 0 1) bound)) ≤ WriterPhase.below id point.path := by
  have actual := select_scope_at built.program point term decision yes no value first bound found scope answer
  have bounded := resolve_bound built admitted id member _ actual
  have path : (point.childBind (cond first 0 1) bound).path = point.path ++ [cond first 0 1] := by
    cases bound <;> rfl
  have ordinary := ordinary_at built admitted id member point _ found (by intro _ _ wrong; cases wrong)
  rw [path] at bounded
  exact Nat.le_trans bounded (child_le id point.path _ (Or.inl ordinary))

/-- Interpreting a stored or source suspension transfers only its active note reservation. -/
theorem suspend_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (suspended : EffThunk) (owned : ThunkAt built.program suspended) :
    current id (suspendBodyAt built.program suspended) ≤ thunk id suspended := by
  have fragment := SourceFragment.atomic_built_fragment built admitted
  revert owned
  fun_cases suspendBodyAt built.program suspended
  all_goals intro owned
  case case2 point n fuel body found =>
    have bound := resolve_bound built admitted id member (point.child 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found owned (by rfl)))
    exact Nat.le_trans bound (child_zero_le id point.path)
  case case3 point n fuel term decision yes no found first bound answer =>
    obtain ⟨value, evaluated, selected⟩ := Option.bind_eq_some_iff.mp answer
    exact select_bound built admitted id member point term decision yes no value first bound found owned selected
  case case5 point n fuel body found => have impossible := fragment.at found; cases impossible
  case case9 point n fuel key request found value path body evaluated => have impossible := fragment.at found; cases impossible
  case case11 point n fuel key request args found value path body evaluated => have impossible := fragment.at found; cases impossible
  case case13 point n fuel index request found value top rest params evaluated site selected => have impossible := fragment.at found; cases impossible
  all_goals aesop (add norm simp [current, thunk, name, program, storeName, storeAction, operation,
    program_exact, (acquisition_absent built admitted), ThunkAt, StoreThunkAt, FinAt, frontier, badShape, directHead, embed, Point.ofCapture]) (add safe apply [(compile_bound built admitted id member), child_zero_le]) (add safe forward [Fragment.at])

/-- The interpreter's completed-exit view changes no suspended note reservation. -/
theorem interp_suspend_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (suspended : EffThunk)
    (owned : ThunkAt built.program suspended) :
    current id ((interpAt built.program view built.table).suspendBody suspended) ≤ thunk id suspended := by
  cases suspended <;> dsimp only [interpAt] <;> apply suspend_bound built admitted id member <;> exact owned

end Test.Dogfood.Scenario.Atomic.WriterSuspensions
