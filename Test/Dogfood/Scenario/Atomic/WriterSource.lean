import Test.Dogfood.Scenario.Atomic.WriterPhase
import Test.Dogfood.Scenario.Atomic.WriterOwnership

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: active note-reservation transport of Atomic.Cleanup.log_debits.
The actual source census bounds native note producers and ordinary callback entries.
No second source or execution carrier is introduced.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Program.HeapSites Effect4.Laws.Auto
open WriterPhase
local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq

/-- A native note producer lies under its selected active finalizer address. -/
def boundedSite (id : Nat) (site : List Nat × NativeOp × Term × Option Nat) : Bool :=
  match site.2.1, site.2.2.2 with
  | .refUpdateWith term, some level =>
    if term == Store.noteAt id level then WriterPhase.below id site.1 == 1 else true
  | _, _ => true

theorem bounded_census :
    (Store.shopProgram.map fun root => requests.all fun id =>
      (performSites root).all (boundedSite id)) = some true := by kernel_rfl

/-- Actual source operations retain the active note reservation of their lexical address. -/
theorem operation_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (row : NativeOp)
    (request : Term) (value : Val) (op : SyncOp)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.perform row request)))
    (scope : At built.program point) (produced : row.syncOpOf point.env value = some op) :
    operation id op ≤ WriterPhase.below id point.path := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have listed := performSites_complete found
  change HeapSites.levelAt (.eff built.program) 0 point.path = some point.env.length at scope
  rw [scope] at listed
  have checked := bounded_census
  have families := Store.shop_census
  rw [source] at checked families
  have selected := List.all_eq_true.mp (List.all_eq_true.mp (Option.some.inj checked) id member) _ listed
  have family := Store.family_of_siteOk (List.all_eq_true.mp (Option.some.inj families) _ listed)
  have update (term : Term) (key : Nat)
      (same : row = .refUpdateWith term) (native : op = .refUpdate ⟨key⟩ term point.env) :
      operation id op ≤ WriterPhase.below id point.path := by
    rw [same] at selected
    rw [native]
    unfold operation
    cases flag : term == Store.noteAt id point.env.length with
    | false => simp only [flag, Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
    | true =>
      simp only [boundedSite, flag, ↓reduceIte, beq_iff_eq] at selected
      rw [selected]
      simp only [flag, ↓reduceIte, Nat.le_refl]
  cases family with
  | make _ =>
    have native : op = .refMake value := (Option.some.inj produced).symm
    rw [native]
    exact Nat.zero_le _
  | get => obtain ⟨key, rfl⟩ := Store.get_inv produced; exact Nat.zero_le _
  | sleep => cases produced
  | decision => obtain ⟨key, rfl⟩ := Store.modify_inv produced; exact Nat.zero_le _
  | deposit requestId => obtain ⟨key, rfl⟩ := Store.modify_inv produced; exact Nat.zero_le _
  | refill => obtain ⟨key, native⟩ := Store.update_inv produced; exact update _ key rfl native
  | note requestId => obtain ⟨key, native⟩ := Store.update_inv produced; exact update _ key rfl native

/-- Every selected source parent is an actual onExit constructor. -/
def exitSite (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (SourcePaths.requestPath id) with
  | some (.eff (.onExit _ _)) => true
  | _ => false

theorem exit_census :
    (Store.shopProgram.map fun root => requests.all (exitSite root)) = some true := by kernel_rfl

theorem exit_at (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) : ExitAt built.program (SourcePaths.requestPath id) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := exit_census
  rw [source] at checked
  have selected := List.all_eq_true.mp (Option.some.inj checked) id member
  unfold exitSite at selected
  split at selected
  · next body finalizer found => exact ⟨body, finalizer, found⟩
  · cases selected

/-- A native bind callback cannot enter an actual finalizer child as an ordinary callback. -/
theorem cont_ordinary (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point)
    (owned : NameAt built.program (.cont point)) : point.path ≠ SourcePaths.requestPath id := by
  intro equal
  obtain ⟨first, rest, bound⟩ := owned.2
  obtain ⟨body, finalizer, exit⟩ := exit_at built admitted id member
  rw [equal, exit] at bound
  cases bound

/-- Distinct ordinary source children divide their parent's active reservation. -/
theorem siblings_le (id : Nat) (path : List Nat) (a b : Nat) (different : a ≠ b)
    (ordinary : path ≠ SourcePaths.requestPath id) :
    WriterPhase.below id (path ++ [a]) + WriterPhase.below id (path ++ [b]) ≤ WriterPhase.below id path := by
  have first := child_le id path a (Or.inl ordinary)
  have second := child_le id path b (Or.inl ordinary)
  have apart := Opportunities.siblings_le (Writer.notePath id) path a b different
  cases active : (SourcePaths.requestPath id ++ [1]).isPrefixOf path with
  | false =>
    have zero : WriterPhase.below id path = 0 := by simp only [WriterPhase.below, active, Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have parent : WriterPhase.below id path = Opportunities.below (Writer.notePath id) path := by
      simp only [WriterPhase.below, active, ↓reduceIte]
    have narrow (edge : Nat) : WriterPhase.below id (path ++ [edge]) ≤ Opportunities.below (Writer.notePath id) (path ++ [edge]) := by
      unfold WriterPhase.below
      split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
    have fa := narrow a
    have fb := narrow b
    omega

/-- A source constructor with a different role cannot be the selected finalizer parent. -/
theorem ordinary_at (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff built.program) point.path = some (.eff body))
    (role : ∀ first cleanup, body ≠ .onExit first cleanup) :
    point.path ≠ SourcePaths.requestPath id := by
  intro equal
  obtain ⟨first, cleanup, actual⟩ := exit_at built admitted id member
  rw [equal, actual] at found
  have same : body = .onExit first cleanup := (Node.eff.inj (Option.some.inj found)).symm
  exact role first cleanup same

/-- Child zero never activates the selected finalizer entry. -/
theorem child_zero_le (id : Nat) (path : List Nat) :
    WriterPhase.below id (path ++ [0]) ≤ WriterPhase.below id path :=
  child_le id path 0 (Or.inr (by decide))

/-- Source fiber actions lie outside the running cleanup-note fragments. -/
def inactiveAction (id : Nat) (path : List Nat) (node : Node NativeOp) : Bool :=
  match node with
  | .eff (.withFiber _) | .action _ => WriterPhase.below id path == 0
  | _ => true

theorem inactive_action_census :
    (Store.shopProgram.map fun root => requests.all fun id =>
      (Node.addresses (.eff root)).all fun path =>
        (Node.at_ (.eff root) path).all (inactiveAction id path)) = some true := by kernel_rfl

theorem action_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (action : ActionTerm NativeOp)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.withFiber action))) :
    WriterPhase.below id point.path = 0 := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := inactive_action_census
  rw [source] at checked
  have present := (mem_addresses_iff (.eff built.program) point.path).mpr (by rw [found]; rfl)
  have selected := List.all_eq_true.mp (List.all_eq_true.mp (Option.some.inj checked) id member) _ present
  rw [found] at selected
  exact beq_iff_eq.mp selected

/-- The actual asynchronous compiler producer contains no active note reservation. -/
theorem async_zero (id : Nat) (row : NativeOp) (request : Term) (point : Point) :
    current id (asyncRoute row request point) = 0 := by
  unfold asyncRoute
  repeat' split
  all_goals rfl

/-- Compiling an actual scoped source position preserves its active note reservation.
The selected onExit entry remains dormant until its native start event. -/
theorem compile_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (body : NativeEff) (point : Point)
    (found : Node.at_ (.eff built.program) point.path = some (.eff body)) (scope : At built.program point) :
    current id (compileEff body point) ≤ WriterPhase.below id point.path := by
  have fragment := SourceFragment.atomic_built_fragment built admitted
  revert found scope
  fun_induction compileEff body point
  all_goals intro found scope
  case case13 point n fuel row request kind value evaluated op produced notExternal notCall notParam =>
    simp only [kind, evaluated, produced, current, cata_prim, thunk]
    exact operation_bound built admitted id member point row request value op found scope produced
  case case18 point n fuel first rest ih =>
    change current id (compileEff first (point.child 0)) + WriterPhase.below id (point.path ++ [1]) ≤ _
    have bound := ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl)))
    have ordinary := ordinary_at built admitted id member point _ found (by intro _ _ wrong; cases wrong)
    have divided := siblings_le id point.path 0 1 (by decide) ordinary
    change current id (compileEff first (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    omega
  case case20 point n fuel body handler ih =>
    change current id (compileEff body (point.child 0)) + WriterPhase.below id (point.path ++ [1]) ≤ _
    have bound := ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl)))
    have ordinary := ordinary_at built admitted id member point _ found (by intro _ _ wrong; cases wrong)
    have divided := siblings_le id point.path 0 1 (by decide) ordinary
    change current id (compileEff body (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    omega
  case case21 point n fuel test body handler ih =>
    change current id (compileEff body (point.child 0)) + WriterPhase.below id (point.path ++ [1]) ≤ _
    have bound := ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl)))
    have ordinary := ordinary_at built admitted id member point _ found (by intro _ _ wrong; cases wrong)
    have divided := siblings_le id point.path 0 1 (by decide) ordinary
    change current id (compileEff body (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    omega
  case case22 point n fuel body success failure ih =>
    change current id (compileEff body (point.child 0)) + WriterPhase.below id (point.path ++ [1]) +
      WriterPhase.below id (point.path ++ [2]) ≤ _
    have bound := ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl)))
    change current id (compileEff body (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    have ordinary := ordinary_at built admitted id member point _ found (by intro _ _ wrong; cases wrong)
    have split01 := siblings_le id point.path 0 1 (by decide) ordinary
    have split02 := siblings_le id point.path 0 2 (by decide) ordinary
    have split12 := siblings_le id point.path 1 2 (by decide) ordinary
    have upper := below_le_one id point.path
    omega
  case case23 point n fuel body cleanup ih =>
    change current id (compileEff body (point.child 0)) + 0 ≤ _
    have bound := ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl)))
    have inherited := child_zero_le id point.path
    change current id (compileEff body (point.child 0)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    omega
  case case34 point n fuel body options =>
    change WriterPhase.below id point.path + WriterPhase.below id point.path ≤ _
    rw [action_zero built admitted id member point _ found]
    omega
  case case40 point n fuel key value body v evaluated =>
    simpa only [updateContextAt, current, cata_prim, thunk, name, operation, Point.child, Nat.zero_add, Nat.add_zero] using
      child_zero_le id point.path
  case case43 point n fuel context body ctx evaluated direct ih =>
    simpa only [updateContextAt, current, cata_prim, thunk, name, operation, Point.child, Nat.zero_add, Nat.add_zero] using
      child_zero_le id point.path
  case case25 point n fuel body noExit ih =>
    exact Nat.le_trans (ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl))))
      (child_zero_le id point.path)
  case case46 point n fuel saved body masked ih =>
    exact Nat.le_trans (ih (Agreement.at_child found 0)
      (child_at built.program point 0 (next_of_at built.program point _ 0 0 found scope (by rfl))))
      (child_zero_le id point.path)
  all_goals have head := fragment.at found
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, program, storeName, storeAction, operation,
    frontier, badShape, Prim.ofExit, updateContextAt, directHead, async_zero]) (add safe apply [child_zero_le])

/-- Resolving any existing scoped source point retains its active note reservation. -/
theorem resolve_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (scope : At built.program point) :
    current id (resolve built.program point) ≤ WriterPhase.below id point.path := by
  unfold resolve
  split
  · exact compile_bound built admitted id member _ point (by assumption) scope
  · exact Nat.zero_le _

end Test.Dogfood.Scenario.Atomic.WriterSource
