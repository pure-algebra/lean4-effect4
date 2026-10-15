import Effect4.Laws.Program.ReleaseWriter.Callbacks

/-!
Concept: scope-lifetime-finalization R11.
Question: source suspensions retain the selected direct release reservation.
Reach: actual source-owned thunks of the direct fragment, with arbitrary row tables.
Consumers: both crews' writer frame and evaluator debit.
These bounds require no dynamic identity beyond the separate writer-store premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program

/-- A select head cannot enter the selected acquisition's release child. -/
theorem Source.select_bound {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) (term : Term) (decision : Decision) (yes no : NativeEff)
    (first : Bool) (bound : Option Val)
    (found : Node.at_ (.eff root) point.path = some (.eff (.select term decision yes no))) :
    current target (resolve root (point.childBind (cond first 0 1) bound)) ≤ leaf target point.path := by
  have bounded := source.resolve_bound (point.childBind (cond first 0 1) bound)
  have path : (point.childBind (cond first 0 1) bound).path = point.path ++ [cond first 0 1] := by
    cases bound <;> rfl
  rw [path] at bounded
  have ordinary := source.ordinary_at point _ found (by intro _ _ wrong; cases wrong)
  cases first with
  | false =>
    change _ ≤ leaf target (point.path ++ [1]) at bounded
    rw [leaf_child_one, ordinary] at bounded
    exact Nat.le_trans bounded (Nat.zero_le _)
  | true =>
    change _ ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    exact Nat.le_trans bounded (Nat.zero_le _)

/-- Source and stored suspensions transfer only their retained direct-release reservation. -/
theorem Source.suspend_bound {target : Target} {root : NativeEff} (source : Source target root)
    (suspended : EffThunk) (owned : SourceScope.ThunkAt root suspended) :
    current target (suspendBodyAt root suspended) ≤ thunk target suspended := by
  revert owned
  fun_cases suspendBodyAt root suspended
  all_goals intro owned
  case case2 point n fuel body found =>
    have bound := source.resolve_bound (point.child 0)
    change current target (resolve root (point.child 0)) ≤ leaf target (point.path ++ [0]) at bound
    rw [leaf_child_zero target _ 0 (by decide)] at bound
    exact Nat.le_trans bound (Nat.zero_le _)
  case case3 point n fuel term decision yes no found first bound answer =>
    exact source.select_bound point term decision yes no first bound found
  case case5 point n fuel body found => have impossible := source.fragment.at found; cases impossible
  case case9 point n fuel key request found value path body evaluated =>
    have impossible := source.fragment.at found; cases impossible
  case case11 point n fuel key request args found value path body evaluated =>
    have impossible := source.fragment.at found; cases impossible
  case case13 point n fuel index request found value top rest params evaluated site selected =>
    have impossible := source.fragment.at found; cases impossible
  all_goals aesop (add norm simp [current, pair, cata_prim, thunk, successName, name, program,
    storeName, storeAction, operation, Stored.program_exact, SourceScope.ThunkAt,
    SourceScope.StoreThunkAt, SourceScope.FinAt, frontier, badShape, SourceScope.directHead, embed,
    Point.ofCapture]) (add safe apply [source.compile_bound]) (add safe forward [SourceScope.Fragment.at])

/-- The completed-exit view changes no source suspension reservation. -/
theorem Source.interp_suspend_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (suspended : EffThunk)
    (owned : SourceScope.ThunkAt root suspended) :
    current target ((interpAt root view table).suspendBody suspended) ≤ thunk target suspended := by
  cases suspended <;> dsimp only [interpAt] <;> apply source.suspend_bound <;> exact owned

end Effect4.Program.ReleaseWriter
