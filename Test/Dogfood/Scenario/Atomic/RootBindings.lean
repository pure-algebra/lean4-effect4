import Test.Dogfood.Scenario.Atomic.StageSource

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
Question: the root's actual fork answers name the fibers used by the observation.
Reach: immutable root environment positions and actual source continuation steps.
Consumer: the coupled root fork phase and the request entry certificates.
This predicate supplies no next-id or whole-history invariant by itself.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootBindings
open Effect4 Effect4.Machine Effect4.Program

/-- Root cells precede the daemon and five requests; the last request follows the sleep. -/
abbrev expected := RootSlots.expected

/-- Every already-created handle occupies its actual source binder slot. -/
def Holds (env : List Val) : Prop :=
  ∀ slot value, expected slot = some value → slot < env.length → env[slot]? = some value

/-- The root accepts an exact handle when its next source binder declares one. -/
def Answer (env : List Val) (value : Val) : Prop :=
  ∀ required, expected env.length = some required → value = required

/-- A returned handle extends the existing root slots without replacing them. -/
theorem append (env : List Val) (value : Val) (held : Holds env) (answer : Answer env value) :
    Holds (env ++ [value]) := by
  intro slot required known small
  by_cases old : slot < env.length
  · rw [List.getElem?_append_left old]
    exact held slot required known old
  · have equal : slot = env.length := by
      simp only [List.length_append, List.length_singleton] at small
      omega
    subst slot
    rw [List.getElem?_concat_length, answer required known]

/-- The actual initializer answers create exactly the three root cell handles. -/
theorem initial : Holds [Val.cell ⟨0⟩, Val.cell ⟨1⟩, Val.cell ⟨2⟩] := by
  intro slot value known small
  have bound : slot < 3 := small
  have eq : Val.cell ⟨slot⟩ = value := Option.some.inj (by simpa only [expected, RootSlots.expected, if_pos bound] using known)
  subst value
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> rfl

/-- Root binders follow the actual right-child continuation chain. -/
def PointAt (point : Point) : Prop :=
  Holds point.env ∧ point.path = List.replicate point.env.length 1

/-- The actual answer continuation retains both its handles and its source path. -/
theorem childWith (point : Point) (value : Val) (held : PointAt point) (answer : Answer point.env value) :
    PointAt (point.childWith 1 value) := by
  refine ⟨append point.env value held.1 answer, ?_⟩
  change point.path ++ [1] = List.replicate (point.env ++ [value]).length 1
  rw [held.2, List.length_append, List.length_singleton, List.replicate_succ']

/-- A fork's returned fiber value is the exact root binder answer. -/
theorem fork_answer (env : List Val) (slot : Nat) (small : slot < 7)
    (length : env.length = StageSource.forkBinder slot) :
    Answer env (Val.fiber ⟨slot + 1⟩) := by
  intro required known
  rw [length] at known
  unfold StageSource.forkBinder at known
  by_cases first : slot < 6
  · rw [if_pos first] at known
    have low : ¬ 3 + slot < 3 := by omega
    have high : 3 + slot < 9 := by omega
    simp only [expected, RootSlots.expected, if_neg low, if_pos high] at known
    have arithmetic : 3 + slot - 2 = slot + 1 := by omega
    simpa only [arithmetic] using Option.some.inj known
  · have last : slot = 6 := by omega
    subst slot
    cases known
    rfl

/-- The actual native fork answer advances the root continuation with its declared handle. -/
theorem fork_continuation (root : NativeEff) (table : RowTable) (view)
    (point : Point) (slot : Nat) (small : slot < 7) (held : PointAt point)
    (length : point.env.length = StageSource.forkBinder slot) :
    let next := ({point with completed := view} : Point).childWith 1 (Val.fiber ⟨slot + 1⟩)
    (interpAt root view table).contA (.cont point) (Val.fiber ⟨slot + 1⟩) = resolve root next ∧
      PointAt next := by
  exact ⟨rfl, childWith {point with completed := view} _ held (fork_answer point.env slot small length)⟩

/-- One actual fork assigns its child role and extends the parent's matching source binder. -/
theorem fork_transition (root : NativeEff) (table : RowTable) (view)
    (machine : NativeMachine) (parent : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (point : Point) (slot : Nat) (options : Supervision.ForkOptions)
    (small : slot < 7) (held : PointAt point)
    (length : point.env.length = StageSource.forkBinder slot)
    (nextId : machine.nextId = slot + 1) :
    let actionPoint := point.child 0
    let spawned := Machine.spawn (interpOf root table) machine parent
      (resolve root ((actionPoint.child 0).child 0)) options (actionPoint.child 0).path
    let next := ({point with completed := view} : Point).childWith 1 (Val.fiber spawned.2.2)
    spawned.2.2 = ⟨slot + 1⟩ ∧ spawned.1.nextId = slot + 2 ∧ PointAt next ∧
      (interpAt root view table).contA (.cont point) (Val.fiber spawned.2.2) = resolve root next ∧
      ∃ child ∈ spawned.1.fibers, child.id = ⟨slot + 1⟩ ∧
        child.frame.current = resolve root ((actionPoint.child 0).child 0) := by
  obtain ⟨id, count, child⟩ := StageSource.spawn_role root table machine parent slot (point.child 0) options nextId
  obtain ⟨callback, slots⟩ := fork_continuation root table view point slot small held length
  dsimp only
  rw [id]
  exact ⟨rfl, count, slots, callback, child⟩

/-- The actual fork source binder determines both sides of the allocation counter. -/
theorem fork_rank (slot : Nat) (small : slot < 7) :
    RootSlots.rank (StageSource.forkBinder slot) = slot + 1 ∧
      RootSlots.rank (StageSource.forkBinder slot + 1) = slot + 2 := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨rfl, rfl⟩

/-- One actual fork advances the same external world used by its returned root answer. -/
theorem fork_stage_transition (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (parent : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (world : StageWorld.World) (point : Point) (slot : Nat) (options : Supervision.ForkOptions)
    (small : slot < 7) (length : point.env.length = StageSource.forkBinder slot)
    (nextId : machine.nextId = slot + 1) :
    let actionPoint := point.child 0
    let spawned := Machine.spawn (interpOf root table) machine parent
      (resolve root ((actionPoint.child 0).child 0)) options (actionPoint.child 0).path
    ∃ after : StageWorld.World, StageWorld.Future world after ∧
      spawned.1.nextId = after.nextId ∧
      StageWorld.ValueAt after (.rootAnswer point.env.length) (Val.fiber spawned.2.2) := by
  obtain ⟨id, count, child⟩ := StageSource.spawn_role root table machine parent slot (point.child 0) options nextId
  dsimp only
  refine ⟨{world with nextId := slot + 2}, ⟨fun _ => .refl _, fun _ held => held⟩, count, ?_⟩
  change slot + 2 = RootSlots.rank (point.env.length + 1) ∧ RootSlots.Answer point.env.length (Val.fiber _)
  rw [length]
  refine ⟨(fork_rank slot small).2.symm, ?_⟩
  rw [id]
  have answered := fork_answer point.env slot small length
  change RootSlots.Answer point.env.length (Val.fiber ⟨slot + 1⟩) at answered
  rw [length] at answered
  exact answered

end Test.Dogfood.Scenario.Atomic.RootBindings
