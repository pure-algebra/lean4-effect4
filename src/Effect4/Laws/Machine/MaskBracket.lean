import Effect4.Laws.Machine.MaskRuns

/-!
# Laws.Machine.MaskBracket — a region ends with its entry flag

`Laws/Machine/MaskRuns.lean` carries the chain `FrameFiber.MaskChain` along a run: a live fiber's
flag is a function of its stack (`MaskRuns.flag_eq`). This module states the bracket of a region
from it: **a region ends at its entry's stack and at its entry flag**, for an arbitrary body
(`saved_mask_region_bracket`). A fiber is live while its `exit` is `none`.

## The two cuts of a region

A cut is a state of one fiber: on the frame machine a `FrameFiber`, and on a run a fiber of a
reached machine. A region is no syntax of the machine. The stack alone marks it:

* **The entry** is a cut. Its stack is the entry's stack, `below`, and its flag is the entry
  flag. The body is the fiber's code there, or the action that opens a region.
* **A cut inside the region** is a later cut whose stack is `above ++ below`. The frames `above`
  are the region's own frames, and `FrameFiber.own` is the fiber with them alone.
* **The end** is inside a step, at such a cut: the pop of the own frames answers nothing, so the
  body's exit has passed each own frame. `FrameFiber.regionEnd` is the fiber that this pop
  leaves, over the entry's stack. The pop of the fiber then goes on as the pop of that fiber.

The end is no cut between two steps in general. A restoring frame and a handler of the other arm
pass inside the pop that delivers the exit, so the stack goes from `above ++ below` to a part of
`below` in one step. `Test/Machine/MaskBracket.lean` holds such a run.

## The statements

Part A is the frame machine alone.

* **The chain splits at each point of the stack** (`MaskChain.append_iff`). So a region's own
  frames hold the chain at the entry flag (`MaskChain.above`): the entry flag is to the region
  what the start flag is to the fiber.
* **The pop of two lists of frames** (`popFrom_append_answered`, `popFrom_append_unanswered`).
  Where an own frame answers, the frames under the region stay under the result's stack. Where
  no own frame answers, the pop goes on over the frames under the region, from the fiber that
  the own frames left. The law asks for no scratch premise.
* **Between the cuts** (`step_under`, `getCont_under_answered`). A step that goes on is the step
  of the own frames, and the frames under the region stay.
* **The first fact: the stack at the region's end is the entry's stack** (`regionEnd_stack`),
  by `getCont_unanswered_stack`. **The flag there is the entry flag** (`regionEnd_flag`), by
  `getCont_unanswered_flag` at the entry flag as the base. **The pop goes on from the region's
  end** (`getCont_regionEnd`).
* **The bracket at one frame machine** (`regionEnds_of_base`, `RegionEnds`).

Part B is a run of the fiber machine.

* **Inside a region the own frames hold the chain at the entry flag** (`MaskRuns.above`), at
  two cuts of one run where the fiber is live. `MaskRuns.flag_eq` is its case of no own frame.
* **The bracket of a region along a run** (`MaskRuns.bracket`).

**The second fact, that the fiber is live at both cuts, is a premise here.** No general
statement gives it: under a hand-written interpreter the command loop steps a fiber that has
exited (`Test/Machine/MaskRuns.lean`, the reached machine). At the compiled program's
interpreter the command loop steps live fibers only, and
`Program.compiled_region_bracket` (`Laws/Program/MaskBracket.lean`) takes no such premise.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. The
  proposed registry claim is `saved-mask-region-bracket`, the run-level half of
  `saved-mask-restoration`. Its pointer is `Program.compiled_region_bracket`, and
  `saved_mask_region_bracket` is its general form;
- reach: the polymorphic frame machine at every stack, demand, skip flag and carried cause, and
  two machines that hold `MaskRuns` at tables in the prefix order, at every interpreter and
  evaluator;
- the later cut's stack shape `above ++ below` is a premise, and it is the region's only mark
  on the machine. The theorem then gives the entry's stack and the entry flag at the region's
  end. It does not give that a body's run keeps that shape: `step_under` keeps it through the
  frame machine's own step, and no theorem keeps it along the fiber machine's evaluator arms
  and commands;
- it gives no cleanup, no release count, no delivery, no budget and no liveness. It states
  nothing of a region whose fiber exits inside it, and nothing of the two checkpoints of the
  mask's derived form before its body. The client premise of that form stays with the client:
  nothing is acquired or registered before the body begins (decisions rows 227 and 244 to
  246). An invariant is not progress;
- consumers: the waiting wrapper under a masked caller, then Semaphore's protected permit and
  Pool's `use`.

The design is `docs/research/2026-10-06-seat-BRACKET-design.md`.
-/

set_option autoImplicit false

universe u v

namespace Effect4.FrameFiber

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-! ## Part A: the frames

### The chain at a point of the stack -/

/-- **The chain splits at each point of the stack.** The chain over `above ++ below` is a chain
over `above` whose base is some flag `mid`, and the chain over `below` at that flag. `mid` is
the flag that the frames `below` see when every frame of `above` has passed.

A step of `saved_mask_region_bracket`, through `MaskChain.above`. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskChain.append_iff {base flag : Bool} {above below : List (Prim ν σ β ε δ ι α)} :
    MaskChain base flag (above ++ below) ↔
      ∃ mid, MaskChain mid flag above ∧ MaskChain base mid below := by
  induction above generalizing flag with
  | nil =>
    constructor
    · intro valid
      exact ⟨flag, rfl, valid⟩
    · rintro ⟨mid, same, valid⟩
      have eq : flag = mid := same
      rw [eq]
      exact valid
  | cons frame rest ih =>
    cases frame with
    | setInterruptible saved =>
      constructor
      · rintro ⟨saves, valid⟩
        obtain ⟨mid, own, under⟩ := ih.mp valid
        exact ⟨mid, ⟨saves, own⟩, under⟩
      · rintro ⟨mid, ⟨saves, own⟩, under⟩
        exact ⟨saves, ih.mpr ⟨mid, own, under⟩⟩
    | _ => exact ih

/-- **A region's own frames hold the chain at the region's entry flag.** The chain holds over
`above ++ below` at the fiber's base, and the entry flag holds the chain over `below` at that
base. Then the entry flag is the base of the own frames `above`. It is the field `chain` of
`saved_mask_region_bracket`.

The entry flag is to the region what the start flag is to the fiber. So each statement of
`Laws/Machine/MaskRuns.lean` over a base reads a region at its entry flag. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskChain.above {base entry flag : Bool} {above below : List (Prim ν σ β ε δ ι α)}
    (valid : MaskChain base flag (above ++ below)) (entered : MaskChain base entry below) :
    MaskChain entry flag above := by
  obtain ⟨mid, own, under⟩ := MaskChain.append_iff.mp valid
  rw [entered.flag_eq under]
  exact own

/-! ### A fiber over more frames -/

/-- The fiber over more frames: the frames `below` are put under its stack. -/
def under (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) :
    FrameFiber ν σ β ε δ ι α :=
  { f with stack := f.stack ++ below }

/-- A region's own fiber: the fiber with the frames `above` alone. The frames under the region
are detached. -/
def own (f : FrameFiber ν σ β ε δ ι α) (above : List (Prim ν σ β ε δ ι α)) :
    FrameFiber ν σ β ε δ ι α :=
  { f with stack := above }

/-- A fiber whose stack is `above ++ below` is its own fiber over `below`. A step of
`regionEnds_of_chain`. -/
@[semantics "scope-lifetime-finalization"]
theorem under_own (g : FrameFiber ν σ β ε δ ι α) (above below : List (Prim ν σ β ε δ ι α))
    (inside : g.stack = above ++ below) : (g.own above).under below = g := by
  cases g
  cases inside
  rfl

/-- The frames under a fiber do not change its code. A step of `step_under`. -/
@[semantics "scope-lifetime-finalization"]
theorem under_current (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) :
    (f.under below).current = f.current := rfl

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-! ### The pop of two lists of frames -/

/-- The pop of `above ++ below`, from the pop of `above` and the pop of `below` after it. Where
the first pop answers, its fiber keeps the frames `below` under its stack. Where it answers
nothing, the second pop goes on. -/
private def joinPop (head : FramePop ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α))
    (tail : FramePop ν σ β ε δ ι α) : FramePop ν σ β ε δ ι α :=
  match head.answer with
  | ContAnswer.empty =>
    FramePop.mk tail.answer (head.popped ++ tail.popped) (head.events ++ tail.events) tail.fiber
      tail.carriedCause
  | _ => { head with fiber := { head.fiber with stack := head.fiber.stack ++ below } }

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The joined pop where the first pop answers nothing. A step of `popFrom_append`. -/
@[semantics "scope-lifetime-finalization"]
private theorem joinPop_of_empty (head : FramePop ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (tail : FramePop ν σ β ε δ ι α)
    (unanswered : head.answer = ContAnswer.empty) :
    joinPop head below tail =
      FramePop.mk tail.answer (head.popped ++ tail.popped) (head.events ++ tail.events) tail.fiber
        tail.carriedCause := by
  simp only [joinPop, unanswered]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The joined pop where the first pop answers. A step of `popFrom_append`. -/
@[semantics "scope-lifetime-finalization"]
private theorem joinPop_of_answer (head : FramePop ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (tail : FramePop ν σ β ε δ ι α)
    (answered : head.answer ≠ ContAnswer.empty) :
    joinPop head below tail =
      { head with fiber := { head.fiber with stack := head.fiber.stack ++ below } } := by
  unfold joinPop
  split
  · rename_i unanswered
    exact absurd unanswered answered
  · rfl

/-- A passed frame: the rest of the pop splits at the same point. The frame that the hook pushed
is drained first, on both sides. A step of `popFrom_append`. -/
@[semantics "scope-lifetime-finalization"]
private theorem passOn_append (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (replacement : Option (Prim ν σ β ε δ ι α)) (afterHook : FrameFiber ν σ β ε δ ι α)
    (rest below : List (Prim ν σ β ε δ ι α)) (cause : Option (Cause ε δ ι α))
    (ih : ∀ (f : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)),
      popFrom demand skip (rest ++ below) f cause =
        joinPop (popFrom demand skip rest f cause) below
          (popFrom demand skip below (popFrom demand skip rest f cause).fiber
            (popFrom demand skip rest f cause).carriedCause)) :
    passOn frame replacement
        (joinPushed demand skip afterHook (rest ++ below)
          (popFrom demand skip (rest ++ below) (passPushed demand skip afterHook cause).fiber
            (passPushed demand skip afterHook cause).carriedCause) cause) =
      joinPop
        (passOn frame replacement
          (joinPushed demand skip afterHook rest
            (popFrom demand skip rest (passPushed demand skip afterHook cause).fiber
              (passPushed demand skip afterHook cause).carriedCause) cause)) below
        (popFrom demand skip below
          (passOn frame replacement
            (joinPushed demand skip afterHook rest
              (popFrom demand skip rest (passPushed demand skip afterHook cause).fiber
                (passPushed demand skip afterHook cause).carriedCause) cause)).fiber
          (passOn frame replacement
            (joinPushed demand skip afterHook rest
              (popFrom demand skip rest (passPushed demand skip afterHook cause).fiber
                (passPushed demand skip afterHook cause).carriedCause) cause)).carriedCause) := by
  cases drained : (passPushed demand skip afterHook cause).answer with
  | empty =>
    simp only [joinPushed, drained, passOn]
    rw [ih]
    cases walked : (popFrom demand skip rest (passPushed demand skip afterHook cause).fiber
        (passPushed demand skip afterHook cause).carriedCause).answer <;>
      simp only [joinPop, walked, List.append_assoc, List.cons_append]
  | deferred c => simp only [joinPushed, drained, passOn, joinPop, List.append_assoc]
  | replacement next => simp only [joinPushed, drained, passOn, joinPop, List.append_assoc]
  | frame answering => simp only [joinPushed, drained, passOn, joinPop, List.append_assoc]

/-- The pop of `above ++ below` is the pop of `above`, joined with the pop of `below` from the
fiber and the carried cause that the first pop left. The induction follows `popFrom`'s own three
cases. It asks for no scratch premise: both sides drain the same pushed frame. A step of
`popFrom_append_answered` and of `popFrom_append_unanswered`. -/
@[semantics "scope-lifetime-finalization"]
private theorem popFrom_append (demand : Arm) (skip : Bool)
    (above below : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) :
    popFrom demand skip (above ++ below) f cause =
      joinPop (popFrom demand skip above f cause) below
        (popFrom demand skip below (popFrom demand skip above f cause).fiber
          (popFrom demand skip above f cause).carriedCause) := by
  induction above generalizing f cause with
  | nil =>
    rw [List.nil_append]
    rfl
  | cons frame rest ih =>
    rw [List.cons_append]
    cases answered : Prim.answerOf frame demand (frame.ensure f).snd with
    | none =>
      simp only [popFrom, answered]
      exact passOn_append demand skip frame _ _ rest below cause ih
    | some answer =>
      cases skipped : (skip && (frame.ensure f).fst.interrupted) with
      | true =>
        simp only [popFrom, answered, skipped, if_true]
        exact passOn_append demand skip frame _ _ rest below _ ih
      | false =>
        simp only [popFrom, answered, skipped, Bool.false_eq_true, if_false]
        rw [joinPop_of_answer _ _ _ (answerOf_ne_empty frame demand _ answer answered)]
        simp only [List.append_assoc]

/-- **Where a frame of `above` answers, the frames `below` stay under the result's stack.** The
pop of `above ++ below` is the pop of `above`, and the frames `below` are not read. Every
demand, skip flag, scratch stack and carried cause is in the domain.

A step of `getCont_under_answered`. It is a general equation of the frames, with no word of the
chain. -/
@[semantics "scope-lifetime-finalization"]
theorem popFrom_append_answered (demand : Arm) (skip : Bool)
    (above below : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α))
    (answered : (popFrom demand skip above f cause).answer ≠ ContAnswer.empty) :
    popFrom demand skip (above ++ below) f cause =
      { popFrom demand skip above f cause with
        fiber := { (popFrom demand skip above f cause).fiber with
          stack := (popFrom demand skip above f cause).fiber.stack ++ below } } := by
  rw [popFrom_append, joinPop_of_answer _ _ _ answered]

/-- **Where no frame of `above` answers, the pop goes on over the frames `below`**, from the
fiber and the carried cause that the pop of `above` left. The popped frames and the events are
those of both pops, in order.

A step of `getCont_under_unanswered`. It is a general equation of the frames, with no word of
the chain. -/
@[semantics "scope-lifetime-finalization"]
theorem popFrom_append_unanswered (demand : Arm) (skip : Bool)
    (above below : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α))
    (unanswered : (popFrom demand skip above f cause).answer = ContAnswer.empty) :
    popFrom demand skip (above ++ below) f cause =
      FramePop.mk
        (popFrom demand skip below (popFrom demand skip above f cause).fiber
          (popFrom demand skip above f cause).carriedCause).answer
        ((popFrom demand skip above f cause).popped ++
          (popFrom demand skip below (popFrom demand skip above f cause).fiber
            (popFrom demand skip above f cause).carriedCause).popped)
        ((popFrom demand skip above f cause).events ++
          (popFrom demand skip below (popFrom demand skip above f cause).fiber
            (popFrom demand skip above f cause).carriedCause).events)
        (popFrom demand skip below (popFrom demand skip above f cause).fiber
          (popFrom demand skip above f cause).carriedCause).fiber
        (popFrom demand skip below (popFrom demand skip above f cause).fiber
          (popFrom demand skip above f cause).carriedCause).carriedCause := by
  rw [popFrom_append, joinPop_of_empty _ _ _ unanswered]

/-- **A `getCont` that an own frame answers keeps the frames under the region.** The pop of the
fiber over `below` is the pop of the fiber, with `below` under the result's stack. The branch of
a deferred interrupt answers too, and it keeps the whole stack. It is the field `answered` of
`saved_mask_region_bracket`.

Its consumers are `resumeValue_under` and `resumeCause_under`, and each exit that the fiber
machine delivers through `getCont` (`evaluatePrim.finalizerOr`, `Program.exitScoped`). -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_under_answered (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α))
    (answered : (f.getCont demand skip cause).answer ≠ ContAnswer.empty) :
    (f.under below).getCont demand skip cause =
      { f.getCont demand skip cause with
        fiber := (f.getCont demand skip cause).fiber.under below } := by
  unfold getCont at answered ⊢
  split at answered
  · rename_i deferred
    have same : ((f.under below).deferredInterrupt && !skip) = true := deferred
    rw [if_pos same, if_pos deferred]
    rfl
  · rename_i popping
    have same : ¬ ((f.under below).deferredInterrupt && !skip) = true := popping
    rw [if_neg same, if_neg popping]
    exact popFrom_append_answered demand skip f.stack below _ cause answered

/-- A `getCont` that no own frame answers goes on over the frames under the region, from the
fiber that the own frames left. A step of `getCont_regionEnd`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_under_unanswered (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (f.under below).getCont demand skip cause =
      FramePop.mk
        (popFrom demand skip below (f.getCont demand skip cause).fiber
          (f.getCont demand skip cause).carriedCause).answer
        ((f.getCont demand skip cause).popped ++
          (popFrom demand skip below (f.getCont demand skip cause).fiber
            (f.getCont demand skip cause).carriedCause).popped)
        ((f.getCont demand skip cause).events ++
          (popFrom demand skip below (f.getCont demand skip cause).fiber
            (f.getCont demand skip cause).carriedCause).events)
        (popFrom demand skip below (f.getCont demand skip cause).fiber
          (f.getCont demand skip cause).carriedCause).fiber
        (popFrom demand skip below (f.getCont demand skip cause).fiber
          (f.getCont demand skip cause).carriedCause).carriedCause := by
  unfold getCont at unanswered ⊢
  split at unanswered
  · cases unanswered
  · rename_i popping
    have same : ¬ ((f.under below).deferredInterrupt && !skip) = true := popping
    rw [if_neg same, if_neg popping]
    exact popFrom_append_unanswered demand skip f.stack below _ cause unanswered

/-! ### The region's end -/

/-- **The region's end.** `f` is the region's own fiber, and `below` is the entry's stack. The
pop of the own frames leaves a fiber, and the region's end is that fiber over the entry's stack.
It is a state inside a step: the pop of the fiber goes on from it (`getCont_regionEnd`). It is
read where the pop of the own frames answers nothing: the body's exit has passed each own
frame. -/
def regionEnd (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α) := none) : FrameFiber ν σ β ε δ ι α :=
  (f.getCont demand skip cause).fiber.under below

/-- **The first fact: the stack at the region's end is the entry's stack.** Where the pop of the
own frames answers nothing, it leaves no frame (`getCont_unanswered_stack`). So the frames that
are left to pop are the frames under the region, and no other. It is the field `stack` of
`RegionEnds`.

It states nothing of a pop that an own frame answers: the region has not ended there. -/
@[semantics "scope-lifetime-finalization"]
theorem regionEnd_stack (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α))
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (regionEnd f below demand skip cause).stack = below := by
  show (f.getCont demand skip cause).fiber.stack ++ below = below
  rw [getCont_unanswered_stack f demand skip cause unanswered]
  rfl

/-- **The flag at the region's end is the entry flag.** The own frames hold the chain at the
entry flag, and a pop that answers nothing ends at the base (`getCont_unanswered_flag`). It is
the field `flag` of `RegionEnds`. -/
@[semantics "scope-lifetime-finalization"]
theorem regionEnd_flag (entry : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) (own : MaskChain entry f.interruptible f.stack)
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (regionEnd f below demand skip cause).interruptible = entry :=
  getCont_unanswered_flag entry f demand skip cause own unanswered

/-- A `getCont` that answers nothing has cleared the deferred flag: its branch of a deferred
interrupt answers, and the pop keeps the flag that it found cleared. A step of
`getCont_regionEnd`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_unanswered_deferred (f : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (f.getCont demand skip cause).fiber.deferredInterrupt = false := by
  rw [getCont_answer_cause] at unanswered
  rw [getCont_fiber_cause]
  unfold getCont at unanswered ⊢
  split at unanswered
  · cases unanswered
  · rename_i popping
    rw [if_neg popping]
    exact popFrom_deferredInterrupt demand skip f.stack _

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A fiber with an empty stack and no deferred interrupt is what `getCont` detaches from it over
any frames. A step of `getCont_regionEnd`. -/
@[semantics "scope-lifetime-finalization"]
private theorem detach_under (h : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α))
    (empty : h.stack = []) (calm : h.deferredInterrupt = false) :
    ({ h.under below with stack := [], deferredInterrupt := false } :
      FrameFiber ν σ β ε δ ι α) = h := by
  cases h
  cases empty
  cases calm
  rfl

/-- **The pop goes on from the region's end.** Where the pop of the own frames answers nothing,
the pop of the fiber over `below` answers what the pop of the region's end answers, with the
carried cause that the own frames left. Its fiber and its carried cause are that pop's too, and
its popped frames and its events are those of both pops, in order.

So the frames under a region are popped from the region's end: from an empty scratch stack, at
the entry flag. It is the last three fields of `RegionEnds`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_regionEnd (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α))
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (unanswered : (f.getCont demand skip cause).answer = ContAnswer.empty) :
    (f.under below).getCont demand skip cause =
      FramePop.mk
        ((regionEnd f below demand skip cause).getCont demand skip
          (f.getCont demand skip cause).carriedCause).answer
        ((f.getCont demand skip cause).popped ++
          ((regionEnd f below demand skip cause).getCont demand skip
            (f.getCont demand skip cause).carriedCause).popped)
        ((f.getCont demand skip cause).events ++
          ((regionEnd f below demand skip cause).getCont demand skip
            (f.getCont demand skip cause).carriedCause).events)
        ((regionEnd f below demand skip cause).getCont demand skip
          (f.getCont demand skip cause).carriedCause).fiber
        ((regionEnd f below demand skip cause).getCont demand skip
          (f.getCont demand skip cause).carriedCause).carriedCause := by
  have calm := getCont_unanswered_deferred f demand skip cause unanswered
  have empty := getCont_unanswered_stack f demand skip cause unanswered
  have ended : (regionEnd f below demand skip cause).getCont demand skip
      (f.getCont demand skip cause).carriedCause =
        popFrom demand skip below (f.getCont demand skip cause).fiber
          (f.getCont demand skip cause).carriedCause := by
    have quiet : ¬ ((regionEnd f below demand skip cause).deferredInterrupt && !skip) = true := by
      show ¬ ((f.getCont demand skip cause).fiber.deferredInterrupt && !skip) = true
      rw [calm]
      exact fun h => nomatch h
    unfold getCont
    rw [if_neg quiet]
    show popFrom demand skip ((f.getCont demand skip cause).fiber.stack ++ below)
      { (f.getCont demand skip cause).fiber.under below with
        stack := [], deferredInterrupt := false } _ = _
    rw [detach_under _ below empty calm, empty]
    rfl
  rw [ended]
  exact getCont_under_unanswered f below demand skip cause unanswered

/-- **A region ends at its entry's stack and at its entry flag.** `entry` is the fiber at the
region's entry, and `g` is the fiber at a cut inside the region, with the own frames `above`.
The statement reads the pop of `g` at one demand, skip flag and carried cause. -/
structure RegionEnds (entry g : FrameFiber ν σ β ε δ ι α) (above : List (Prim ν σ β ε δ ι α))
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α)) : Prop where
  /-- **The stack at the region's end is the entry's stack.** -/
  stack : (regionEnd (g.own above) entry.stack demand skip cause).stack = entry.stack
  /-- **The flag at the region's end is the entry flag.** -/
  flag : (regionEnd (g.own above) entry.stack demand skip cause).interruptible =
    entry.interruptible
  /-- The pop of the fiber answers what the pop of the region's end answers. -/
  answer : (g.getCont demand skip cause).answer =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).answer
  /-- It leaves the fiber that the pop of the region's end leaves. -/
  fiber : (g.getCont demand skip cause).fiber =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).fiber
  /-- It carries the cause that the pop of the region's end carries. -/
  carried : (g.getCont demand skip cause).carriedCause =
    ((regionEnd (g.own above) entry.stack demand skip cause).getCont demand skip
      ((g.own above).getCont demand skip cause).carriedCause).carriedCause

/-- **The bracket of a region, from the chain of its own frames.** The fiber `g` is inside the
region of `entry`: its stack is the own frames `above` over the entry's stack. The own frames
hold the chain at the entry flag. Where their pop answers nothing, the region ends at the
entry's stack and at the entry flag, and the pop goes on from there.

A step of `regionEnds_of_base` and of `Machine.MaskRuns.bracket`. -/
@[semantics "scope-lifetime-finalization"]
theorem regionEnds_of_chain (entry g : FrameFiber ν σ β ε δ ι α)
    (above : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) (inside : g.stack = above ++ entry.stack)
    (own : MaskChain entry.interruptible g.interruptible above)
    (unanswered : ((g.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds entry g above demand skip cause := by
  have goesOn := getCont_regionEnd (g.own above) entry.stack demand skip cause unanswered
  rw [under_own g above entry.stack inside] at goesOn
  exact ⟨regionEnd_stack _ _ demand skip cause unanswered,
    regionEnd_flag entry.interruptible _ _ demand skip cause own unanswered,
    by rw [goesOn], by rw [goesOn], by rw [goesOn]⟩

/-- **The bracket of a region at one frame machine.** Two fibers hold the chain at one base. The
second is inside the region of the first: its stack is the own frames `above` over the first
one's stack. Where the pop of the own frames answers nothing, the region ends at the entry's
stack and at the entry flag. It is the field `frames` of `saved_mask_region_bracket`.

One base is needed, as for `MaskChain.flag_eq`. Along a run the base is the fiber's start flag
(`Machine.MaskRuns.bracket`). -/
@[semantics "scope-lifetime-finalization"]
theorem regionEnds_of_base (base : Bool) (entry g : FrameFiber ν σ β ε δ ι α)
    (above : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) (inside : g.stack = above ++ entry.stack)
    (entered : MaskChain base entry.interruptible entry.stack)
    (valid : MaskChain base g.interruptible g.stack)
    (unanswered : ((g.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds entry g above demand skip cause :=
  regionEnds_of_chain entry g above demand skip cause inside
    (MaskChain.above (by rw [← inside]; exact valid) entered) unanswered

/-! ### Between the cuts -/

/-- `resumeValue` that goes on is the same over more frames: its pop is answered, and the
answering frame's arm pushes over the same stack. A step of `step_under`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeValue_under (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (value : β) (provided : Option (Exit β ε δ ι α))
    (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.resumeValue interp value provided).fst = FrameStep.running next) :
    ((f.under below).resumeValue interp value provided).fst =
      FrameStep.running (next.under below) := by
  cases answered : (f.getCont Arm.contA false).answer with
  | empty =>
    rw [resumeValue_empty interp f value provided answered] at running
    cases running
  | deferred c =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeValue_deferred interp f value provided c answered] at running
    cases running
    rw [resumeValue_deferred interp (f.under below) value provided c
      (by rw [kept]; exact answered), kept]
    rfl
  | replacement code =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeValue_replacement interp f value provided code answered] at running
    cases running
    rw [resumeValue_replacement interp (f.under below) value provided code
      (by rw [kept]; exact answered), kept]
    rfl
  | frame answering =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    cases arm : answering.armA interp value provided with
    | none =>
      simp only [resumeValue, answered, arm] at running
      cases running
    | some out =>
      obtain ⟨code, pushed⟩ := out
      rw [resumeValue_frame interp f value provided answering code pushed answered arm] at running
      cases running
      rw [resumeValue_frame interp (f.under below) value provided answering code pushed
        (by rw [kept]; exact answered) arm, kept]
      simp only [under, List.append_assoc]

/-- `resumeCause` that goes on is the same over more frames. A step of `step_under`. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeCause_under (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.resumeCause interp cause provided).fst = FrameStep.running next) :
    ((f.under below).resumeCause interp cause provided).fst =
      FrameStep.running (next.under below) := by
  cases answered : (f.getCont Arm.contE true (some cause)).answer with
  | empty =>
    rw [resumeCause_empty interp f cause provided answered] at running
    cases running
  | deferred c =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeCause_deferred interp f cause c provided answered] at running
    cases running
    rw [resumeCause_deferred interp (f.under below) cause c provided
      (by rw [kept]; exact answered), kept]
    rfl
  | replacement code =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeCause_replacement interp f cause provided code answered] at running
    cases running
    rw [resumeCause_replacement interp (f.under below) cause provided code
      (by rw [kept]; exact answered), kept]
    rfl
  | frame answering =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    cases arm : answering.armE interp
        ((f.getCont Arm.contE true (some cause)).carriedCause.getD cause)
        (provided.map (f.getCont Arm.contE true (some cause)).deliveredExit) with
    | none =>
      simp only [resumeCause, answered, arm] at running
      cases running
    | some out =>
      obtain ⟨code, pushed⟩ := out
      rw [resumeCause_frame interp f cause provided answering code pushed answered arm] at running
      cases running
      rw [resumeCause_frame interp (f.under below) cause provided answering code pushed
        (by rw [kept]; exact answered) (by rw [kept]; exact arm), kept]
      simp only [under, List.append_assoc]

/-- **Between the cuts: a step that goes on keeps the frames under the region.** The step of
the fiber over `below` is the step of the fiber, with `below` under the next stack. The frames
`below` are not read and not written. It is the field `between` of
`saved_mask_region_bracket`.

It states nothing of a finished step: there the pop of the own frames answers nothing, and the
region has ended (`getCont_regionEnd`). It is the frame machine's own step. The fiber machine
writes a stack at other places too, and no theorem states this law there. -/
@[semantics "scope-lifetime-finalization"]
theorem step_under (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α)
    (running : (f.step interp).fst = FrameStep.running next) :
    ((f.under below).step interp).fst = FrameStep.running (next.under below) := by
  cases current : f.current with
  | success value =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeValue_under interp f below _ _ next running
  | failure cause =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeCause_under interp f below _ _ next running
  | sync thunk =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeValue_under interp f below _ _ next running
  | iterator generator cursor =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases arm : (Prim.iterator generator cursor : Prim ν σ β ε δ ι α).armA interp cursor none with
    | none =>
      simp only [arm] at running ⊢
      cases running
      rfl
    | some out =>
      simp only [arm] at running ⊢
      cases running
      simp only [under, List.append_assoc]
  | whileLoop loop cursor =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases entered : interp.loopEnter loop cursor with
    | «continue» cursor' body =>
      simp only [entered] at running ⊢
      cases running
      rfl
    | finish code =>
      simp only [entered] at running ⊢
      cases running
      rfl
  | _ =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases running
    rfl

end Effect4.FrameFiber

namespace Effect4.Machine

open Effect4 Effect4.FrameFiber

/-! ## Part B: a run -/

section Runs

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- The command steps the fiber: when the command loop runs it, the loop evaluates that fiber.
A cut of the command loop is a machine and its pending commands, and it reads a fiber that a
pending command steps. -/
def Steps {κ : Type (max u v)} (id : FiberId) : Cmd ν σ β ε δ ι α κ → Prop
  | Cmd.loop fiber _ => fiber = id
  | Cmd.deliver fiber _ => fiber = id
  | _ => False

/-- **Inside a region the own frames hold the chain at the entry flag.** Two machines hold the
invariant, at two tables in the prefix order. A fiber is live in both. At the second its stack
is the frames `above` over its stack at the first. Then `above` holds the chain at the flag of
the first cut. It is the field `inside` of `saved_mask_region_bracket`.

`MaskRuns.flag_eq` is its case of no own frame. The later cut's stack shape `above ++ below` is
a premise, and it is the region's only mark on the machine. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskRuns.above {bases bases' : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (kept' : MaskRuns bases' m') (grown : bases <+: bases')
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (mem' : g ∈ m'.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    {above : List (Prim ν σ β ε δ ι α)} (inside : g.frame.stack = above ++ f.frame.stack) :
    MaskChain f.frame.interruptible g.frame.interruptible above := by
  obtain ⟨base, entry, valid⟩ := kept.2 f mem
  obtain ⟨base', entry', valid'⟩ := kept'.2 g mem'
  obtain ⟨rest, rfl⟩ := grown
  rw [same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp entry).1, entry] at entry'
  cases entry'
  have chain := valid' live'
  rw [inside] at chain
  exact chain.above (valid live)

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- **The bracket of a region, along a run.** Two machines hold the invariant, at two tables in
the prefix order. A fiber is live in both. The first cut is the region's entry. At the second
the fiber is inside the region: its stack is the own frames `above` over the entry's stack.
Where the pop of the own frames answers nothing, the region ends at the entry's stack and at
the entry flag, and the pop goes on from there. It is the field `ends` of
`saved_mask_region_bracket`.

The later cut's stack shape `above ++ below` is a premise, and it is the region's only mark on
the machine. The theorem then gives the entry's stack and the entry flag at the region's end. It
does not give that a body's run keeps that shape. Both cuts need a live fiber, and
`Test/Machine/MaskBracket.lean` holds the red control. -/
@[semantics "scope-lifetime-finalization"]
theorem MaskRuns.bracket {bases bases' : List Bool} {m m' : RunMachine ν σ β ε δ ι α χ St}
    (kept : MaskRuns bases m) (kept' : MaskRuns bases' m') (grown : bases <+: bases')
    {f g : RunFiber ν σ β ε δ ι α χ} (mem : f ∈ m.fibers) (mem' : g ∈ m'.fibers)
    (same : g.id = f.id) (live : f.exit = none) (live' : g.exit = none)
    {above : List (Prim ν σ β ε δ ι α)} (inside : g.frame.stack = above ++ f.frame.stack)
    (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α))
    (unanswered : ((g.frame.own above).getCont demand skip cause).answer = ContAnswer.empty) :
    RegionEnds f.frame g.frame above demand skip cause :=
  regionEnds_of_chain f.frame g.frame above demand skip cause inside
    (kept.above kept' grown mem mem' same live live' inside) unanswered

end Runs

/-! ## The placed theorem -/

/-- The statements of the bracket of a region, in their general form: the proposed registry
claim `saved-mask-region-bracket`, over the polymorphic frame machine and over two machines that
hold the invariant `MaskRuns`. -/
structure RegionBracket (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v))
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] : Prop where
  /-- **A region's own frames hold the chain at the region's entry flag.** -/
  chain : ∀ (base entry flag : Bool) (above below : List (Prim ν σ β ε δ ι α)),
    MaskChain base flag (above ++ below) → MaskChain base entry below →
      MaskChain entry flag above
  /-- **Between the cuts: a step that goes on keeps the frames under the region.** -/
  between : ∀ (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α),
    (f.step interp).fst = FrameStep.running next →
      ((f.under below).step interp).fst = FrameStep.running (next.under below)
  /-- **A pop that an own frame answers keeps the frames under the region.** -/
  answered : ∀ (f : FrameFiber ν σ β ε δ ι α) (below : List (Prim ν σ β ε δ ι α)) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α)),
    (f.getCont demand skip cause).answer ≠ ContAnswer.empty →
      (f.under below).getCont demand skip cause =
        { f.getCont demand skip cause with
          fiber := (f.getCont demand skip cause).fiber.under below }
  /-- **The bracket at one frame machine**: two fibers at one base, the second inside the region
  of the first. -/
  frames : ∀ (base : Bool) (entry g : FrameFiber ν σ β ε δ ι α)
    (above : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)), g.stack = above ++ entry.stack →
    MaskChain base entry.interruptible entry.stack → MaskChain base g.interruptible g.stack →
      ((g.own above).getCont demand skip cause).answer = ContAnswer.empty →
        RegionEnds entry g above demand skip cause
  /-- **Inside a region the own frames hold the chain at the entry flag**, at two cuts of one
  run where the fiber is live. -/
  inside : ∀ (bases bases' : List Bool) (m m' : RunMachine ν σ β ε δ ι α χ St)
    (f g : RunFiber ν σ β ε δ ι α χ) (above : List (Prim ν σ β ε δ ι α)), MaskRuns bases m →
    MaskRuns bases' m' → bases <+: bases' → f ∈ m.fibers → g ∈ m'.fibers → g.id = f.id →
      f.exit = none → g.exit = none → g.frame.stack = above ++ f.frame.stack →
        MaskChain f.frame.interruptible g.frame.interruptible above
  /-- **The bracket of a region, along a run**: the region ends at the entry's stack and at the
  entry flag. -/
  ends : ∀ (bases bases' : List Bool) (m m' : RunMachine ν σ β ε δ ι α χ St)
    (f g : RunFiber ν σ β ε δ ι α χ) (above : List (Prim ν σ β ε δ ι α)) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α)), MaskRuns bases m → MaskRuns bases' m' →
    bases <+: bases' → f ∈ m.fibers → g ∈ m'.fibers → g.id = f.id → f.exit = none →
      g.exit = none → g.frame.stack = above ++ f.frame.stack →
        ((g.frame.own above).getCont demand skip cause).answer = ContAnswer.empty →
          RegionEnds f.frame g.frame above demand skip cause

/-- **A region ends at its entry's stack and at its entry flag**, for an arbitrary body (concept
`scope-lifetime-finalization`, requirement R11). It is the general form of the proposed registry
claim `saved-mask-region-bracket`, the run-level half of `saved-mask-restoration`. Each field
cites one theorem of this module, so its status is derived from theirs (`#plan_status`).

Reach: the polymorphic frame machine, at every stack, demand, skip flag and carried cause. Along
a run: two machines that hold `MaskRuns` at tables in the prefix order, at every interpreter and
evaluator, and a fiber that is live at both cuts.

The later cut's stack shape `above ++ below` is a premise, and it is the region's only mark on
the machine. The theorem then gives the entry's stack and the entry flag at the region's end. It
does not give that a body's run keeps that shape.

It does not establish that a fiber is live at a cut: that is a premise too, and
`Program.compiled_region_bracket` (`Laws/Program/MaskBracket.lean`) discharges it at the
compiled program's interpreter. It gives no cleanup, no release count, no delivery, no budget
and no liveness. It states nothing of a region whose fiber exits inside it. The client premise
of the mask's derived form stays with the client: nothing is acquired or registered before the
body begins (decisions rows 227 and 244 to 246).

Its consumers are `Program.compiled_region_bracket`'s: the waiting wrapper under a masked
caller, then Semaphore's protected permit and Pool's `use`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_mask_region_bracket (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u)
    (St : Type (max u v)) [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    RegionBracket ν σ β ε δ ι α χ St where
  chain := fun _ _ _ _ _ valid entered => MaskChain.above valid entered
  between := step_under
  answered := getCont_under_answered
  frames := fun base entry g above demand skip cause inside entered valid unanswered =>
    regionEnds_of_base base entry g above demand skip cause inside entered valid unanswered
  inside := fun _ _ _ _ _ _ _ kept kept' grown mem mem' same live live' inside =>
    kept.above kept' grown mem mem' same live live' inside
  ends := fun _ _ _ _ _ _ _ demand skip cause kept kept' grown mem mem' same live live' inside
      unanswered =>
    kept.bracket kept' grown mem mem' same live live' inside demand skip cause unanswered

end Effect4.Machine
