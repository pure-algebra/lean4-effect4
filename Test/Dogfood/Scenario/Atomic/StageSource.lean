import Test.Dogfood.Scenario.Atomic.StageWorld
import Test.Dogfood.Scenario.Atomic.SourcePaths
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: store-typing R4, the source and fiber-role part of `Atomic.Store.shop_stages`.
Consumer: its root fork producer assigns the six request stages to the observed fibers.
These source facts use the actual authored shop and actual spawn operation.
The root's current-prefix and next-id facts remain inputs to that producer.
No source census alone establishes their preservation through histories.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Atomic.StageSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The last request follows the root's five awaits and its sleep binder. -/
def forkBinder (slot : Nat) : Nat := if slot < 6 then 3 + slot else 15

def forkPath (slot : Nat) : List Nat := List.replicate (forkBinder slot) 1 ++ [0]
def bodyPath (slot : Nat) : List Nat := forkPath slot ++ [0, 0]

/-- The root source at each of its seven fork binders is an actual fork action. -/
def forkHead (root : NativeEff) (slot : Nat) : Bool :=
  match Node.at_ (.eff root) (forkPath slot) with
  | some (.eff (.withFiber (.fork _ _))) => true
  | _ => false

theorem fork_census :
    (Store.shopProgram.map fun root => (List.range 7).all (forkHead root)) = some true := by
  kernel_rfl

/-- The source certificate retains the actual fork program and options.
Consumer: the root's native fork action case. -/
theorem fork_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (slot : Nat) (small : slot < 7) :
    ∃ body options, Node.at_ (.eff built.program) (forkPath slot) =
      some (.eff (.withFiber (.fork body options))) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have checked := fork_census
  rw [source] at checked
  have selected := List.all_eq_true.mp (Option.some.inj checked) slot (List.mem_range.mpr small)
  unfold forkHead at selected
  split at selected
  · rename_i body options found
    exact ⟨body, options, found⟩
  · cases selected

/-- The request tags and their observed fiber roles use these exact source bodies. -/
theorem request_body_path (id : Nat) (member : id ∈ requests) :
    bodyPath id = SourcePaths.requestPath id := by
  simp only [requests, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The admission continuation tests exactly the Boolean appended by its decision. -/
def branchPath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [0, 1]

def branchHead (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (branchPath id) with
  | some (.eff (.select (.var depth) .bool _ _)) => decide (depth = forkBinder id)
  | _ => false

theorem branch_census :
    (Store.shopProgram.map fun root => requests.all (branchHead root)) = some true := by
  kernel_rfl

/-- The source branch's actual variable is the request's decision binder.
Consumer: the request continuation and branch native producers. -/
theorem branch_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ yes no, Node.at_ (.eff built.program) (branchPath id) =
      some (.eff (.select (.var (forkBinder id)) .bool yes no)) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have checked := branch_census
  rw [source] at checked
  have selected := List.all_eq_true.mp (Option.some.inj checked) id member
  unfold branchHead at selected
  split at selected
  · rename_i depth yes no found
    have same := of_decide_eq_true selected
    rw [same] at found
    exact ⟨yes, no, found⟩
  · cases selected

/-- The actual native continuation appends its decision in the source branch's tested slot. -/
theorem decision_argument (id : Nat) (point : Point) (admitted : Bool)
    (depth : point.env.length = forkBinder id) :
    (point.childWith 1 (.bool admitted)).env[forkBinder id]? = some (.bool admitted) := by
  change (point.env ++ [.bool admitted])[forkBinder id]? = _
  rw [← depth]
  exact List.getElem?_concat_length

/-- The actual branch suspension consumes the same stage-certified decision Boolean.
Consumer: the admitted deposit path and the rejected-return path. -/
theorem branch_step (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (world : StageWorld.World) (point : Point)
    (admitted : Bool) (fuel : Nat) (amount : point.fuel = fuel + 1)
    (path : point.path = branchPath id)
    (argument : point.env[forkBinder id]? = some (.bool admitted))
    (decision : StageWorld.ValueAt world (.decision id) (.bool admitted)) :
    suspendBodyAt built.program (.body point) =
      resolve built.program (point.child (cond admitted 0 1)) ∧
      world.stages id = if admitted then .admitted else .rejected := by
  obtain ⟨yes, no, found⟩ := branch_at built accepted id member
  rw [← path] at found
  refine ⟨?_, decision⟩
  exact Agreement.suspendBodyAt_select_of_decide (first := admitted) (bound := none) amount found (by
    simp only [evalTerm, argument, Option.bind_some, Decision.decide])

/-- The fork action resolves the actual child point without changing its captured environment. -/
theorem action_at (root : NativeEff) (point : Point) (body : NativeEff)
    (options : Supervision.ForkOptions)
    (found : Node.at_ (.eff root) point.path = some (.eff (.withFiber (.fork body options)))) :
    actionAt root point = some (.fork (resolve root ((point.child 0).child 0)) options (point.child 0).path) := by
  simp only [actionAt, found]

/-- The spawned program's actual point retains the authored fork body. -/
theorem body_at (root : NativeEff) (point : Point) (body : NativeEff)
    (options : Supervision.ForkOptions)
    (found : Node.at_ (.eff root) point.path = some (.eff (.withFiber (.fork body options)))) :
    Node.at_ (.eff root) ((point.child 0).child 0).path = some (.eff body) :=
  Agreement.at_child (Agreement.at_child found 0) 0

/-- The root's next-id assertion assigns its actual new fiber to the declared request role.
Consumer: the role and current-code clauses after the native fork producer. -/
theorem spawn_role (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (parent : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (slot : Nat) (point : Point) (options : Supervision.ForkOptions)
    (nextId : m.nextId = slot + 1) :
    let spawned := Machine.spawn (interpOf root table) m parent
      (resolve root ((point.child 0).child 0)) options (point.child 0).path
    spawned.2.2 = ⟨slot + 1⟩ ∧ spawned.1.nextId = slot + 2 ∧
      ∃ child ∈ spawned.1.fibers, child.id = ⟨slot + 1⟩ ∧
        child.frame.current = resolve root ((point.child 0).child 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg FiberId.mk nextId
  · change m.nextId + 1 = slot + 2
    omega
  · refine ⟨_, List.mem_append.mpr (.inr (List.mem_cons_self)), ?_, rfl⟩
    exact congrArg FiberId.mk nextId
end Test.Dogfood.Scenario.Atomic.StageSource
