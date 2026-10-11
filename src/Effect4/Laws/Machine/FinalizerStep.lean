import Effect4.Laws.Machine.FinalizerCredits

/-!
# Finalizer starts debit continuation frames

Concept: scope-lifetime-finalization, R11, at most one start per registration.
These helpers serve the finalizer trace bound consumed by `Atomic.cleans_once`.
A frame step accounts for every selected start and every selected pushed frame.
The bound covers arbitrary interpreters, stacks, masks, and delivered exits.
It establishes neither unique source use nor log-writer provenance or progress.
-/

set_option autoImplicit false

namespace Effect4.Machine.FinalizerCredits

universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- Select the start events for the finalizers being counted. -/
def started (choose : ν → Bool) : FrameEvent ν σ β ε δ ι α → Bool
  | .ranFinalizer name _ => choose name
  | _ => false

/-- Select the push events that create a finalizer credit. -/
def registered (choose : ν → Bool) : FrameEvent ν σ β ε δ ι α → Bool
  | .pushed frame => selected choose frame
  | _ => false

/-- Credits retained after a frame step. A finished fiber retains no stack. -/
def remaining (choose : ν → Bool) : FrameStep ν σ β ε δ ι α → Nat
  | .running fiber => stack choose fiber.stack
  | .finished _ => 0

/-- Continuation hooks record bookkeeping, without starting a finalizer. -/
theorem passEvents_no_start (choose : ν → Bool) (frame : Prim ν σ β ε δ ι α)
    (replacement : Option (Prim ν σ β ε δ ι α)) :
    (frame.passEvents replacement).countP (started choose) = 0 := by
  unfold Prim.passEvents
  split
  · split <;> rfl
  · rfl

/-- A finalizer arm records exactly its one selected start. -/
theorem finalizerEvents_count (choose : ν → Bool) (frame : Prim ν σ β ε δ ι α)
    (exit : Exit β ε δ ι α) :
    (frame.finalizerEvents exit).countP (started choose) =
      (if selected choose frame then 1 else 0) := by
  fun_cases Prim.finalizerEvents
  · exact List.countP_singleton
  all_goals rfl

/-- Push events contain no starts. -/
theorem pushed_no_start (choose : ν → Bool) (frames : List (Prim ν σ β ε δ ι α)) :
    (frames.map FrameEvent.pushed).countP (started choose) = 0 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simpa only [List.map_cons, List.countP_cons, started, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero] using ih

/-- Push events account for exactly the finalizer credits they install. -/
theorem pushed_count (choose : ν → Bool) (frames : List (Prim ν σ β ε δ ι α)) :
    (frames.map FrameEvent.pushed).countP (registered choose) = stack choose frames := by
  simp only [List.countP_map, registered, stack, Function.comp_def]

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Draining a hook's frame starts no finalizer. -/
theorem passPushed_no_start (choose : ν → Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    (FrameFiber.passPushed demand skip fiber).events.countP (started choose) = 0 := by
  unfold FrameFiber.passPushed
  split
  · rfl
  · exact passEvents_no_start choose _ _

/-- Joining continuation lookups starts no finalizer when its tail starts none. -/
theorem joinPushed_no_start (choose : ν → Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
    (tail : FramePop ν σ β ε δ ι α)
    (silent : tail.events.countP (started choose) = 0) :
    (FrameFiber.joinPushed demand skip fiber rest tail).events.countP (started choose) = 0 := by
  unfold FrameFiber.joinPushed
  split <;> simp only [List.countP_append, passPushed_no_start, silent, Nat.add_zero]

/-- The complete stack traversal records no finalizer start. -/
theorem popFrom_no_start (choose : ν → Bool) (demand : Arm) (skip : Bool) :
    ∀ (frames : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α),
      (FrameFiber.popFrom demand skip frames fiber).events.countP (started choose) = 0
  | [], _ => rfl
  | frame :: rest, fiber => by
    have tail := popFrom_no_start choose demand skip rest
      (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber
    have joined := joinPushed_no_start choose demand skip (frame.ensure fiber).1 rest _ tail
    simp only [FrameFiber.popFrom, FrameFiber.skippedCause_none,
      FrameFiber.passPushed_carriedCause_none]
    split
    · split
      · simp only [FrameFiber.passOn, List.countP_append, passEvents_no_start, joined, Nat.add_zero]
      · exact passEvents_no_start choose _ _
    · simp only [FrameFiber.passOn, List.countP_append, passEvents_no_start, joined, Nat.add_zero]

/-- A lookup selects a continuation but has not started its finalizer yet. -/
theorem getCont_no_start (choose : ν → Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α) := none) :
    (fiber.getCont demand skip cause).events.countP (started choose) = 0 := by
  rw [FrameFiber.getCont_events_cause]
  unfold FrameFiber.getCont
  split
  · rfl
  · exact popFrom_no_start choose demand skip _ _

/-- Resuming a value pays for every start from an existing continuation credit. -/
theorem resumeValue_debit (choose : ν → Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Exit β ε δ ι α)) :
    let result := fiber.resumeValue interp value provided
    result.2.countP (started choose) + remaining choose result.1 ≤
      stack choose fiber.stack + result.2.countP (registered choose) := by
  have bound := getCont_le choose fiber .contA false
  have silent := getCont_no_start choose fiber .contA false
  unfold FrameFiber.resumeValue
  split
  · simp only [remaining, List.countP_append, silent, List.countP_cons, started, List.countP_nil,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
    exact Nat.zero_le _
  · simp only [remaining, silent, Nat.zero_add]
    unfold pop at bound
    omega
  · simp only [remaining, silent, Nat.zero_add]
    unfold pop at bound
    omega
  · next frame selectedFrame =>
    rw [pop, selectedFrame] at bound
    simp only [answer] at bound
    split
    · simp only [remaining, List.countP_append, silent, finalizerEvents_count, pushed_no_start,
        pushed_count, stack, List.countP_append, Nat.zero_add, Nat.add_zero]
      simp only [stack] at bound
      omega
    · simp only [remaining, List.countP_append, silent, List.countP_cons, started, List.countP_nil,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.zero_le _

/-- Resuming a cause pays for starts after all hook and interruption handling. -/
theorem resumeCause_debit (choose : ν → Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) :
    let result := fiber.resumeCause interp cause provided
    result.2.countP (started choose) + remaining choose result.1 ≤
      stack choose fiber.stack + result.2.countP (registered choose) := by
  have bound := getCont_le choose fiber .contE true (some cause)
  have silent := getCont_no_start choose fiber .contE true (some cause)
  unfold FrameFiber.resumeCause
  dsimp only
  split
  · simp only [remaining, List.countP_append, silent, List.countP_cons, started, List.countP_nil,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
    exact Nat.zero_le _
  · simp only [remaining, silent, Nat.zero_add]
    unfold pop at bound
    omega
  · simp only [remaining, silent, Nat.zero_add]
    unfold pop at bound
    omega
  · next frame selectedFrame =>
    rw [pop, selectedFrame] at bound
    simp only [answer] at bound
    split
    · simp only [remaining, List.countP_append, silent, finalizerEvents_count, pushed_no_start,
        pushed_count, stack, List.countP_append, Nat.zero_add, Nat.add_zero]
      simp only [stack] at bound
      omega
    · simp only [remaining, List.countP_append, silent, List.countP_cons, started, List.countP_nil,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.zero_le _

/-- Each frame step debits starts and accounts for every newly pushed finalizer. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem step_debit (choose : ν → Bool) (interp : PrimInterp ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    let result := fiber.step interp
    result.2.countP (started choose) + remaining choose result.1 ≤
      stack choose fiber.stack + result.2.countP (registered choose) := by
  unfold FrameFiber.step
  split
  · exact resumeValue_debit choose interp fiber _ _
  · exact resumeCause_debit choose interp fiber _ _
  · exact resumeValue_debit choose interp fiber _ _
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · split
    · simp only [pushed_no_start, pushed_count, remaining, stack, List.countP_append, Nat.zero_add]
      omega
    · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
      selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
      selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
      selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
      selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
      selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · rename_i body name flag current
    cases chosen : choose name <;>
      simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
        selected, chosen, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  · split
    · simp only [remaining, stack, List.countP_cons, List.countP_nil, started, registered,
        selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.le_refl]
    · simp only [remaining, List.countP_nil, Nat.zero_add, Nat.add_zero, Nat.le_refl]

end Effect4.Machine.FinalizerCredits
