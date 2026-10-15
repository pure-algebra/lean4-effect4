import Effect4.Laws.Program.ReleaseWriter.Weights
import Effect4.Laws.Program.CompileInduction
import Effect4.Laws.Program.NativeScope
import Effect4.Laws.Program.HeapSites

/-!
Concept: scope-lifetime-finalization R11.
Question: source compilation cannot create a pending release write before its selected leaf.
Reach: direct lexical programs with one selected acquisition and a checked native-operation bound.
Consumers: the Workers and QueueWorkers writer instances.
The source contract says nothing about captured values or the log's actual reference binding.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program

/-- The source facts needed by the shared direct-release writer. -/
structure Source (target : Target) (root : NativeEff) : Prop where
  fragment : SourceScope.Fragment root
  acquisition : SourceScope.AcquisitionAt root target.path
  release : ∃ request, Node.at_ (.eff root) (target.path ++ [1]) =
    some (.eff (.perform (.refUpdateWith target.term) request))
  operations : ∀ (point : Point) (row : NativeOp) (request : Term) (value : Val) (op : SyncOp),
    Node.at_ (.eff root) point.path = some (.eff (.perform row request)) →
    row.syncOpOf point.env value = some op → operation target op ≤ leaf target point.path

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

/-- The selected update term appears only at its direct release leaf. -/
def boundedSite (target : Target) (site : List Nat × NativeOp × Term × Option Nat) : Bool :=
  match site.2.1 with
  | .refUpdateWith term =>
    if term == target.term then decide (site.1 = target.path ++ [1]) else true
  | _ => true

/-- The complete source census supplies the operation bound once for every crew. -/
theorem Source.of_census (target : Target) (root : NativeEff)
    (fragment : SourceScope.Fragment root)
    (acquisition : SourceScope.AcquisitionAt root target.path)
    (release : ∃ request, Node.at_ (.eff root) (target.path ++ [1]) =
      some (.eff (.perform (.refUpdateWith target.term) request)))
    (census : (HeapSites.performSites root).all (boundedSite target) = true) : Source target root := by
  refine ⟨fragment, acquisition, release, ?_⟩
  intro point row request value op found produced
  cases op
  case refUpdate key term env =>
    obtain ⟨rowEq, envEq⟩ := update_origin row point.env value key term env produced
    subst row
    subst env
    have checked := List.all_eq_true.mp census _ (HeapSites.performSites_complete found)
    by_cases chosen : (term == target.term) = true
    · simp only [boundedSite, chosen, ↓reduceIte] at checked
      have path := of_decide_eq_true checked
      simp only [operation, chosen, leaf, path, ↓reduceIte, Nat.le_refl]
    · simp only [operation, chosen, Bool.false_eq_true, ite_false, Nat.zero_le]
  all_goals exact Nat.zero_le _

/-- Only child one can be the selected release leaf. -/
theorem leaf_child_zero (target : Target) (path : List Nat) (edge : Nat) (different : edge ≠ 1) :
    leaf target (path ++ [edge]) = 0 := by
  unfold leaf
  split
  · rename_i impossible
    have last := List.append_inj_right' impossible rfl
    cases last
    exact (different rfl).elim
  · rfl

/-- The release child belongs to the selected acquisition exactly. -/
theorem leaf_child_one (target : Target) (path : List Nat) :
    leaf target (path ++ [1]) = selected target path := by
  unfold leaf selected
  by_cases same : path = target.path
  · simp only [same, ↓reduceIte]
  · have different : path ++ [1] ≠ target.path ++ [1] := by
      intro equal
      exact same (List.append_singleton_inj.mp equal).1
    simp only [same, different, ite_false]

/-- A source head with another constructor cannot be the selected acquisition. -/
theorem Source.ordinary_at {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff body))
    (role : ∀ acquire release, body ≠ .acquireRelease acquire release) :
    selected target point.path = 0 := by
  unfold selected
  split
  · rename_i equal
    obtain ⟨acquire, release, actual⟩ := source.acquisition
    rw [equal, actual] at found
    exact (role acquire release (Node.eff.inj (Option.some.inj found)).symm).elim
  · rfl

/-- A different source head cannot be the selected direct release write. -/
theorem Source.leaf_zero_at {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff body))
    (role : ∀ request, body ≠ .perform (.refUpdateWith target.term) request) :
    leaf target point.path = 0 := by
  unfold leaf
  split
  · rename_i equal
    obtain ⟨request, actual⟩ := source.release
    rw [equal, actual] at found
    exact (role request (Node.eff.inj (Option.some.inj found)).symm).elim
  · rfl

/-- Asynchronous compilation introduces no pending selected reference write. -/
theorem async_zero (target : Target) (row : NativeOp) (request : Term) (point : Point) :
    current target (asyncRoute row request point) = 0 := by
  unfold asyncRoute
  repeat' split
  all_goals rfl

/-- Compiling an actual source body transfers at most its selected release leaf. -/
theorem Source.compile_bound {target : Target} {root : NativeEff} (source : Source target root)
    (body : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff body)) :
    current target (compileEff body point) ≤ leaf target point.path := by
  revert found
  fun_induction compileEff body point
  all_goals intro found
  case case13 point n fuel row request kind value evaluated op produced notExternal notCall notParam =>
    simp only [kind, evaluated, produced, current, pair, cata_prim, thunk]
    exact source.operations point row request value op found produced
  case case18 point n fuel first rest ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current target (compileEff first (point.child 0)) ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    have ordinary := source.ordinary_at point _ found (by intro _ _ wrong; cases wrong)
    simp only [current, successName, name, leaf_child_one, ordinary, Nat.add_zero]
    exact Nat.le_trans bounded (Nat.zero_le _)
  case case20 point n fuel body handler ih | case21 point n fuel test body handler ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current target (compileEff body (point.child 0)) ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    have ordinary := source.ordinary_at point _ found (by intro _ _ wrong; cases wrong)
    simpa only [current, pair, cata_prim, name, leaf_child_one, ordinary, Nat.add_zero] using
      (Nat.le_trans bounded (Nat.zero_le (leaf target point.path)))
  case case22 point n fuel body success failure ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current target (compileEff body (point.child 0)) ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    have ordinary := source.ordinary_at point _ found (by intro _ _ wrong; cases wrong)
    simpa only [current, pair, cata_prim, name, leaf_child_one, ordinary,
      leaf_child_zero target _ 2 (by decide), Nat.add_zero] using
      (Nat.le_trans bounded (Nat.zero_le (leaf target point.path)))
  case case23 point n fuel body cleanup ih | case25 point n fuel body noExit ih |
      case46 point n fuel saved body masked ih =>
    have bounded := ih (Agreement.at_child found 0)
    change current target (compileEff body (point.child 0)) ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    simpa only [current, pair, cata_prim, name, Nat.add_zero] using
      (Nat.le_trans bounded (Nat.zero_le (leaf target point.path)))
  case case34 point n fuel body options =>
    have zero := source.leaf_zero_at point _ found (by intro _ wrong; cases wrong)
    change leaf target point.path + leaf target point.path ≤ leaf target point.path
    rw [zero]
    exact Nat.le_refl 0
  all_goals have head := source.fragment.at found
  all_goals aesop (add norm simp [current, pair, cata_prim, thunk, successName, name, frontier,
    badShape, Prim.ofExit, updateContextAt, SourceScope.directHead, Point.child,
    leaf_child_zero, async_zero])

/-- Resolving any point transfers at most the reservation at its selected release leaf. -/
theorem Source.resolve_bound {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) : current target (resolve root point) ≤ leaf target point.path := by
  unfold resolve
  split
  · exact source.compile_bound _ point (by assumption)
  · exact Nat.zero_le _

end Effect4.Program.ReleaseWriter
