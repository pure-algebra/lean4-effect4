import Effect4.Laws.Program.CommandFrames

/-!
Concept: scope-lifetime-finalization, R11, the saved-mask region bracket.
Question: actual command prefixes establish the entry-stack premise of compiled_region_bracket.
Reach: a named live fiber before the fresh-id counter, with a fixed entry stack.
The detached evaluation tests the region boundary before settlement restores the entry suffix.
Limit: a continuing detached evaluation is required; no progress or permanent suffix claim follows.
Consumer: native loop and delivery transport, then the command-prefix region bracket.
-/
set_option autoImplicit false
namespace Effect4.Program.StackRegion
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

/-- The current stack consists of the region's frames followed by its fixed entry stack. -/
def Inside (below : List NCode) (fiber : NFiber) : Prop :=
  ∃ above, fiber.frame.stack = above ++ below

/-- Detach the fixed entry suffix without changing current code or execution metadata. -/
def detach (below : List NCode) (fiber : NFiber) : NFiber :=
  {fiber with frame := (fiber.frame.own
    (fiber.frame.stack.take (fiber.frame.stack.length - below.length)))}

/-- A known entry suffix reconstructs the actual fiber from its detached region. -/
theorem reattach (below : List NCode) (fiber : NFiber) (inside : Inside below fiber) :
    fiberUnder (detach below fiber) below = fiber := by
  obtain ⟨above, shape⟩ := inside
  unfold detach
  rw [shape, List.length_append, Nat.add_sub_cancel_right, List.take_left]
  unfold fiberUnder
  rw [FrameFiber.under_own fiber.frame above below shape]

/-- Adding an entry stack always exhibits that exact suffix. -/
theorem under_inside (below : List NCode) (fiber : NFiber) :
    Inside below (fiberUnder fiber below) := ⟨fiber.frame.stack, rfl⟩

/-- One actual native evaluation keeps the suffix until its detached body finishes. -/
theorem native_inside (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : NFiber) (yielding : Bool) (below : List NCode) (inside : Inside below fiber)
    (going : GoesOn (evaluateNative root machine (detach below fiber) yielding table)) :
    Inside below (evaluateNative root machine fiber yielding table).fiber := by
  have same := evaluateNative_under root table machine (detach below fiber) yielding below going
  rw [reattach below fiber inside] at same
  rw [same]
  exact under_inside below _

/-- The charged native loop uses the same boundary test, including yield injection. -/
theorem iteration_inside (root : NativeEff) (table : RowTable) (interp : NInterp)
    (machine : NativeMachine) (fiber : NFiber) (yielding : Bool) (below : List NCode)
    (inside : Inside below fiber)
    (going : GoesOn (iteration (evaluator := evaluatorFor root table)
      interp machine (detach below fiber) yielding)) :
    Inside below (iteration (evaluator := evaluatorFor root table) interp machine fiber yielding).fiber := by
  have same := iteration_under root table interp machine (detach below fiber) yielding below going
  rw [reattach below fiber inside] at same
  rw [same]
  exact under_inside below _

/-- Interference only changes metadata and current interruption answers, never the saved stack. -/
theorem other_edit_stack {first last : NFiber} (edit : OtherEdit first last) :
    last.frame.stack = first.frame.stack := by
  cases edit with
  | observe => rfl
  | filterObservers => rfl
  | interruptCause cause =>
    unfold interruptWithCause
    dsimp only
    repeat' split
    all_goals rfl

/-- A word of actual other-fiber edits retains the exact saved list. -/
theorem other_edits_stack {first last : NFiber} (edits : OtherEdits first last) :
    last.frame.stack = first.frame.stack := by
  induction edits with
  | refl => rfl
  | tail _ edit ih => exact (other_edit_stack edit).trans ih

/-- The watched existing identity retains its entry suffix while it remains live. -/
def Held (id : FiberId) (below : List NCode) (machine : NativeMachine) : Prop :=
  id.value < machine.nextId ∧
    ∀ fiber ∈ machine.fibers, fiber.id = id → fiber.exit = none → Inside below fiber

theorem Held.allocated {id : FiberId} {below : List NCode} {machine : NativeMachine}
    (held : Held id below machine) : id.value < machine.nextId := held.1

theorem Held.frames {id : FiberId} {below : List NCode} {machine : NativeMachine}
    (held : Held id below machine) :
    ∀ fiber ∈ machine.fibers, fiber.id = id → fiber.exit = none → Inside below fiber := held.2

/-- The existing interference classification excludes a fresh replacement for the watched id. -/
theorem interferes {id : FiberId} {below : List NCode} {first last : NativeMachine}
    (changed : Interferes first last) (held : Held id below first) : Held id below last := by
  refine ⟨Nat.lt_of_lt_of_le held.allocated changed.nextId, ?_⟩
  intro fiber member selected live
  rcases changed.fibers fiber member with ⟨old, present, edits⟩ | born
  · have oldSelected : old.id = id := edits.id.symm.trans selected
    have oldLive : old.exit = none := edits.exit.symm.trans live
    obtain ⟨above, shape⟩ := held.frames old present oldSelected oldLive
    exact ⟨above, (other_edits_stack edits).trans shape⟩
  · have fresh := born.1
    rw [selected] at fresh
    exact False.elim (Nat.not_le_of_lt held.allocated fresh)

/-- Installing the evaluated fiber keeps every untouched row and the same allocation bound. -/
theorem update {id : FiberId} {below : List NCode} {machine : NativeMachine}
    (fiber : NFiber) (held : Held id below machine)
    (inside : fiber.id = id → fiber.exit = none → Inside below fiber) :
    Held id below (machine.update fiber) := by
  refine ⟨held.allocated, ?_⟩
  intro other member selected live
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  split at same
  · subst other
    exact inside selected live
  · subst other
    exact held.frames old present selected live

/-- Fields outside the fiber table and allocation counter do not affect a region. -/
theorem fields {id : FiberId} {below : List NCode} {first last : NativeMachine}
    (held : Held id below first) (fibers : last.fibers = first.fibers)
    (next : first.nextId ≤ last.nextId) : Held id below last :=
  ⟨Nat.lt_of_lt_of_le held.allocated next,
    fun fiber member => held.frames fiber (fibers ▸ member)⟩

/-- Every settle outcome installs the proved suffix; exited rows remain outside the assertion. -/
theorem settleOutcome_held {id : FiberId} {below : List NCode} (owner : FiberId)
    (rest : List NCommand) (result : NIter) (held : Held id below result.machine)
    (inside : result.fiber.id = id → result.fiber.exit = none → Inside below result.fiber) :
    Held id below (settleOutcome owner rest result).1 := by
  unfold settleOutcome
  split
  · exact update _ held inside
  · exact update _ held inside
  · split
    · exact update _ held inside
    · exact update _ held inside
  · exact update _ held inside
  · exact update _ held inside
  · exact fields (update {result.fiber with running := false} held inside) rfl (Nat.le_refl _)

/-- Message settlement retains the suffix through the shared interference word and actual owner. -/
theorem settle_held {id : FiberId} {below : List NCode} (owner : FiberId)
    (rest : List NCommand) (result : NIter) (held : Held id below result.machine)
    (inside : result.fiber.id = id → result.fiber.exit = none → Inside below result.fiber) :
    Held id below (settle owner rest result).1 := by
  unfold settle
  split
  · exact settleOutcome_held owner rest result held inside
  · have changed := interferes (InterferesWithLookup.fiberEdits result.edits _).backward
      (update result.fiber held inside)
    dsimp only
    split
    · exact fields changed rfl (Nat.le_refl _)
    · rename_i selected found
      exact settleOutcome_held owner rest _ changed
        (changed.frames selected (List.mem_of_find?_eq_some found))

/-- The actual loop installation retains the region when the watched detached evaluation continues. -/
theorem loop_held (root : NativeEff) (table : RowTable) (interp : NInterp)
    (machine : NativeMachine) (fiber : NFiber) (member : fiber ∈ machine.fibers)
    (owner : FiberId) (yielding : Bool) (rest : List NCommand) (id : FiberId) (below : List NCode)
    (held : Held id below machine)
    (going : fiber.id = id → fiber.exit = none → GoesOn
      (iteration (evaluator := evaluatorFor root table) interp machine (detach below fiber) yielding)) :
    Held id below (settle owner rest
      (iteration (evaluator := evaluatorFor root table) interp machine fiber yielding)).1 := by
  apply settle_held
  · exact interferes (iteration_interferes root table interp machine fiber yielding) held
  · intro selected live
    have footprint := iteration_footprint root table interp machine fiber yielding
    rw [footprint.id] at selected
    rw [footprint.exit] at live
    exact iteration_inside root table interp machine fiber yielding below
      (held.frames fiber member selected live) (going selected live)

/-- The actual delivery installation retains the region under its uncharged detached evaluation. -/
theorem deliver_held (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (fiber : NFiber) (member : fiber ∈ machine.fibers)
    (owner : FiberId) (yielding : Bool) (rest : List NCommand) (id : FiberId) (below : List NCode)
    (held : Held id below machine)
    (going : fiber.id = id → fiber.exit = none →
      GoesOn (evaluateNative root machine (detach below fiber) yielding table)) :
    Held id below (settle owner rest (evaluateNative root machine fiber yielding table)).1 := by
  apply settle_held
  · exact interferes (evaluateNative_interferes root table machine fiber yielding) held
  · intro selected live
    have footprint := evaluateNative_footprint root table machine fiber yielding
    rw [footprint.id] at selected
    rw [footprint.exit] at live
    exact native_inside root table machine fiber yielding below
      (held.frames fiber member selected live) (going selected live)

end Effect4.Program.StackRegion
