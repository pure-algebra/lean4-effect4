import Effect4.Laws.Program.AnswerSlots.Initialization
import Effect4.Laws.Machine.StoresLaws

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the actual root reference prefix has one allocation protocol independent of crew gates.
Reach: any Initialization certificate, actual returned reference keys and native store updates.
Limit: a whole-history instance still supplies root exclusivity and post-prefix source closure.
Consumer: Initialized allocation callbacks and bare Atomic and Timeout initializer adapters.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialization
open Effect4 Effect4.Machine Effect4.Program

/-- A prefix stage records only its actual source point and reference-allocation count. -/
def Stage {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (index : Nat) (point : Point) (refs : List Val) : Prop :=
  index ≤ spec.width ∧ point.path = List.replicate index 1 ∧
    point.env = spec.bindings.take index ∧ refs.length = index ∧ SourceScope.At root point

/-- The closed root begins the reference protocol before allocating any reference. -/
theorem start {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (fuel : Nat) (tape : List Bool) (refs : List Val) (empty : refs.length = 0) :
    Stage spec 0 (rootPoint fuel tape) refs := ⟨Nat.zero_le _, rfl, rfl, empty, rfl⟩

/-- One actual allocation callback advances the source prefix with its returned key. -/
theorem advance {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (index : Nat) (point : Point) (refs : List Val) (small : index < spec.width)
    (stage : Stage spec index point refs) (view : List (FiberId × ExitV)) (initial : Val) :
    Stage spec (index + 1) ({point with completed := view}.childWith 1 (.cell ⟨index⟩)) (refs ++ [initial]) := by
  obtain ⟨bound, path, env, length, source⟩ := stage
  obtain ⟨tail, found⟩ := spec.head index small
  rw [← path] at found
  have after := SourceScope.next_of_at root point _ 1 1 found source rfl
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · change point.path ++ [1] = List.replicate (index + 1) 1
    rw [path, List.replicate_succ']
  · change point.env ++ [.cell ⟨index⟩] = spec.bindings.take (index + 1)
    rw [env]
    exact spec.next index small
  · rw [List.length_append, List.length_singleton, length]
  · exact SourceScope.childWith_at root _ 1 _ after

/-- The final allocation establishes the whole declared reference-binding prefix. -/
theorem boundary {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (point : Point) (refs : List Val) (stage : Stage spec spec.width point refs) :
    Prefix (spec.bindings.take spec.width) point.env := by
  rw [stage.2.2.1]
  exact List.take_length

/-- A real reference allocation answers its current key and appends exactly the declared initial value. -/
theorem actual {root : NativeEff} (spec : AnswerSlots.Initialization root) (index : Nat)
    (state after : Stores) (value : Val)
    (ran : syncOpStep (.refMake (spec.initial index)) state = some (after, value)) :
    value = .cell ⟨state.refs.length⟩ ∧ after = {state with refs := state.refs ++ [spec.initial index]} := by
  dsimp only [syncOpStep, refStep, Option.map] at ran
  cases ran
  exact ⟨rfl, rfl⟩
end Effect4.Program.AnswerSlots.Initialization
