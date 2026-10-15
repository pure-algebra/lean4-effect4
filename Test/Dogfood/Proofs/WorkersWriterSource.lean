import Test.Dogfood.Proofs.WorkersWriterWeights
import Test.Dogfood.Proofs.WorkersWriterCensus
import Test.Dogfood.Scenario.SourceFragment

/-!
Concept: scope-lifetime-finalization R11.
Question: source compilation retains the reservation used by Workers.Assertions.logs_step.
Reach: every job count, source position and compile budget of the actual workers program.
The selected release body contains one direct update; ordinary compilation keeps it dormant.
Consumer: release writer callbacks and native suspension debit.
The dynamic writer still owes the captured value and released-reference binding.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.WorkersWriterSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario WorkersWriterWeights

/-- A produced update retains its source row and captured environment. -/
theorem update_origin (row : NativeOp) (env : List Val) (value : Val)
    (key : RefKey) (term : Term) (captured : List Val)
    (produced : row.syncOpOf env value = some (.refUpdate key term captured)) :
    row = .refUpdateWith term ∧ captured = env := by
  revert produced
  fun_cases NativeOp.syncOpOf row env value
  all_goals intro produced
  all_goals cases produced
  exact ⟨rfl, rfl⟩

/-- A selected release term occurs only at its own release leaf. -/
def boundedSite (identity : Nat) (site : List Nat × NativeOp × Term × Option Nat) : Bool :=
  match site.2.1 with
  | .refUpdateWith term =>
    if (identity == 1 && term == WorkersWriters.appendOne 7 (.var 5)) ||
       (identity == 2 && term == WorkersWriters.appendOne 8 (.var 6)) then
      decide (site.1 = Programs.crewAcquire identity ++ [1])
    else true
  | _ => true

/-- The checked source census quantifies every job count and both connection identities. -/
theorem bounded_census (total : Nat) :
    [1, 2].all (fun identity => (HeapSites.performSites (Programs.workersProgram total)).all
      (boundedSite identity)) = true := by
  kernel_rfl

/-- The compiled native update retains at most the reservation at its actual source position. -/
theorem operation_bound (total identity : Nat) (member : identity ∈ [1, 2])
    (point : Point) (row : NativeOp) (request : Term) (value : Val) (op : SyncOp)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.perform row request)))
    (produced : row.syncOpOf point.env value = some op) :
    operation identity op ≤ leaf identity point.path := by
  cases op
  case refUpdate key term env =>
    obtain ⟨rowEq, envEq⟩ := update_origin row point.env value key term env produced
    subst row
    subst env
    have present := HeapSites.performSites_complete found
    have checked := List.all_eq_true.mp (List.all_eq_true.mp (bounded_census total) identity member) _ present
    by_cases selected : ((identity == 1 && term == WorkersWriters.appendOne 7 (.var 5)) ||
      (identity == 2 && term == WorkersWriters.appendOne 8 (.var 6))) = true
    · simp only [boundedSite, selected, ↓reduceIte] at checked
      have path := of_decide_eq_true checked
      simp only [operation, selected, leaf, path, ↓reduceIte, Nat.le_refl]
    · simp only [operation, selected, Bool.false_eq_true, ite_false, Nat.zero_le]
  all_goals exact Nat.zero_le _

/-- Child zero cannot be a release child, whose last edge is one. -/
theorem leaf_child_zero (identity : Nat) (path : List Nat) : leaf identity (path ++ [0]) = 0 := by
  unfold leaf
  split
  · rename_i impossible
    have last := List.append_inj_right' impossible rfl
    cases last
  · rfl

/-- The asynchronous compiler introduces no pending release write. -/
theorem async_zero (identity : Nat) (row : NativeOp) (request : Term) (point : Point) :
    current identity (asyncRoute row request point) = 0 := by
  unfold asyncRoute
  repeat' split
  all_goals rfl

/-- Compilation counts only the selected direct release leaf, including its live fuel frontier. -/
theorem compile_bound (total identity : Nat) (member : identity ∈ [1, 2])
    (body : NativeEff) (point : Point)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path = some (.eff body)) :
    current identity (compileEff body point) ≤ leaf identity point.path := by
  have fragment := SourceFragment.workers_fragment total
  revert found
  fun_induction compileEff body point
  all_goals intro found
  case case13 point n fuel row request kind value evaluated op produced notExternal notCall notParam =>
    simp only [kind, evaluated, produced, current, pair, cata_prim, thunk]
    exact operation_bound total identity member point row request value op found produced
  case case18 point n fuel first rest ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current identity (compileEff first (point.child 0)) ≤ leaf identity point.path
    change current identity (compileEff first (point.child 0)) ≤ leaf identity (point.path ++ [0]) at bounded
    rw [leaf_child_zero] at bounded
    omega
  case case20 point n fuel body handler ih | case21 point n fuel test body handler ih |
      case22 point n fuel body success failure ih | case23 point n fuel body cleanup ih |
      case25 point n fuel body noExit ih | case46 point n fuel saved body masked ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current identity (compileEff body (point.child 0)) ≤ leaf identity (point.path ++ [0]) at bounded
    rw [leaf_child_zero] at bounded
    simpa only [current, pair, cata_prim, name, Nat.add_zero] using
      (Nat.le_trans bounded (Nat.zero_le (leaf identity point.path)))
  all_goals have head := fragment.at found
  all_goals aesop (add norm simp [current, pair, cata_prim, thunk, name, frontier,
    badShape, Prim.ofExit, updateContextAt, SourceScope.directHead, async_zero])

/-- Resolution retains the same bound at every actual source point. -/
theorem resolve_bound (total identity : Nat) (member : identity ∈ [1, 2]) (point : Point) :
    current identity (resolve (Programs.workersProgram total) point) ≤ leaf identity point.path := by
  unfold resolve
  split
  · exact compile_bound total identity member _ point (by assumption)
  · exact Nat.zero_le _

end Test.Dogfood.Proofs.WorkersWriterSource
