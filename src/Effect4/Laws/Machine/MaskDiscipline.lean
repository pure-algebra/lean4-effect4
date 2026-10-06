import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Machine.MaskDiscipline — the saved mask's chain is kept through a pop of the stack

A region that changes a fiber's flag pushes the frame that returns it
(`FrameFiber.uninterruptible`, `FrameFiber.interruptibleRegion`, `Machine/Frames.lean`). So on a
fiber's stack the restoring frames alternate from the negation of the flag, and the flag under
them is one fixed bit, the fiber's base. `MaskChain` states that. The flag is then a function of
the base and of the stack.

The statements are the fields of `MaskPopDiscipline`, and one placed theorem holds them
(`saved_mask_pop_discipline`). The frame machine's own pop keeps the chain at the same base:
`FrameFiber.popFrom` from an empty scratch stack, `FrameFiber.getCont`, and the finished frame's
path `Machine.frameExitState` (`Machine/Fibers.lean`). So does the entry of each region. Two
fibers with one base and one stack have one flag.

The scratch premise of the pop stays. `getCont` calls `popFrom` with an empty scratch stack.
Without the premise the statement is false, and `Test/Machine/MaskDiscipline.lean` holds the
witness.

Proof graph, each fact a step of `saved_mask_pop_discipline`:

* **A hook keeps the chain** (`ensure_maskChain`), in three cases. A restoring frame returns
  its saved flag and pushes nothing. A finalizer that masks pushes the frame that returns the
  flag. Every other hook is neutral. The popped frame sits on top of the scratch stack, so this
  step asks for no scratch premise.
* **The drain keeps the chain** (`passPushed_maskChain`): it is the hook of the scratch stack's
  top frame. **One drain empties what one hook pushed** onto an empty scratch stack
  (`passPushed_ensure_stack_nil`), so the recursive call meets the scratch premise again.
* **The pop keeps the chain** (`popFrom_maskChain`): an induction on the frames, in the form of
  `FrameFiber.popFrom_interruptedCause`. The carried cause is rewritten away first
  (`FrameFiber.popFrom_fiber_cause`), so the walk is proved once.
* **The two adapters** (`getCont_maskChain`, `frameExitState_maskChain`) split their definition
  once each. The **two entries** read the entries' own laws. The **same flag** is
  `MaskChain.flag_eq`.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. The
  proposed registry claim is `saved-mask-pop-discipline`, a step of the open run-level half of
  `saved-mask-restoration`;
- reach: the polymorphic `FrameFiber`, at every stack, demand, skip flag and carried cause, with
  one fixed base. No statement asks for a premise on a pending cause, on a deferred interrupt or
  on a frame's kind;
- it does not establish a law of a run, a completed exit, a cleanup's multiplicity, a delivery,
  a budget or liveness. It says nothing of a host or of a printed form. `Cmd.exitDone` clears a
  stack and keeps its flag, so the chain does not survive an arbitrary command;
- consumers: the later lift through `Machine.Lift` (`Laws/Machine/Lift.lean`), then the waiting
  wrapper under a masked caller and Semaphore's protected permit.

`Program.MaskInv` (`Laws/Program/Means.lean`) is a different predicate, on the reference term's
stack. Its empty stack accepts either flag, and its restoring case forgets the incoming flag.
This module imports no module of `Laws/Program`: the law is lower than the typed program.

The design is `docs/research/2026-10-06-seat-MASKPOP-design.md`.
-/

set_option autoImplicit false

universe u v

namespace Effect4.FrameFiber

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-! ## The chain -/

/-- The saved mask's chain on a stack, at one fixed base bit. `flag` is the interruptible flag
above the stack's top. A restoring frame `Prim.setInterruptible saved` saves the negation of the
flag above it, and the chain goes on under it at `saved`. Every other frame is neutral. Under the
last frame the flag is `base`.

It is proof data over the existing stack. It adds no field, no instruction and no state of the
machine. -/
def MaskChain (base : Bool) : Bool → List (Prim ν σ β ε δ ι α) → Prop
  | flag, [] => flag = base
  | flag, Prim.setInterruptible saved :: rest => flag = !saved ∧ MaskChain base saved rest
  | flag, _ :: rest => MaskChain base flag rest

/-- The chain is decidable, so a battery evaluates it on a real fiber
(`Test/Machine/MaskDiscipline.lean`). The instance decides the one definition. It is no second
definition of the chain. -/
instance MaskChain.decidable (base : Bool) :
    ∀ (flag : Bool) (stack : List (Prim ν σ β ε δ ι α)), Decidable (MaskChain base flag stack)
  | flag, [] => inferInstanceAs (Decidable (flag = base))
  | flag, frame :: rest => by
    cases frame with
    | setInterruptible saved =>
      exact @instDecidableAnd _ _ _ (MaskChain.decidable base saved rest)
    | _ => exact MaskChain.decidable base flag rest

/-- **The flag is a function of the base and of the stack**: two chains at one base over one
stack have one flag. It is the field `sameFlag` of `saved_mask_pop_discipline`. The fixed base is
needed, and so is the alternation (`Test/Machine/MaskDiscipline.lean`, two red controls). -/
@[semantics "scope-lifetime-finalization"]
theorem MaskChain.flag_eq {base flag flag' : Bool} {stack : List (Prim ν σ β ε δ ι α)}
    (h : MaskChain base flag stack) (h' : MaskChain base flag' stack) : flag = flag' := by
  induction stack generalizing flag flag' with
  | nil => exact h.trans h'.symm
  | cons frame rest ih =>
    cases frame with
    | setInterruptible saved => exact h.1.trans h'.1.symm
    | _ => exact ih h h'

/-! ## The hook and the entries -/

/-- **A hook keeps the chain.** The popped frame sits on top of the scratch stack and of the
frames that are left, `rest`. So the statement asks for no scratch premise. A restoring frame
returns its saved flag and pushes nothing. `onExit` and `asyncFinalizer` push the frame that
returns the flag exactly when they mask. Every other hook is neutral.

A step of `popFrom_maskChain`. Its consumers are the pop's answering case and
`passPushed_maskChain`. `ensure_stack_cases` gives no flag where the stack is unchanged, so each
case reads the hook's own equations. -/
@[semantics "scope-lifetime-finalization"]
theorem ensure_maskChain (base : Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
    (valid : MaskChain base fiber.interruptible (frame :: (fiber.stack ++ rest))) :
    MaskChain base (frame.ensure fiber).fst.interruptible
      ((frame.ensure fiber).fst.stack ++ rest) := by
  cases frame with
  | setInterruptible saved =>
    rw [Prim.ensure_setInterruptible_flag, Prim.ensure_setInterruptible_stack]
    exact valid.2
  | onExit body finalizer told =>
    cases masked : fiber.interruptible with
    | false =>
      rw [Prim.ensure_onExit_already_masked body finalizer told fiber masked]
      exact valid
    | true =>
      cases told with
      | true =>
        rw [Prim.ensure_onExit_told_not_to]
        exact valid
      | false =>
        rw [Prim.ensure_onExit_masks body finalizer fiber masked]
        rw [masked] at valid
        exact ⟨rfl, valid⟩
  | asyncFinalizer onInterrupt =>
    cases masked : fiber.interruptible with
    | false =>
      rw [Prim.ensure_asyncFinalizer_already_masked onInterrupt fiber masked]
      exact valid
    | true =>
      rw [Prim.ensure_asyncFinalizer_masks onInterrupt fiber masked]
      rw [masked] at valid
      exact ⟨rfl, valid⟩
  | _ => exact valid

/-- **The entry of an `uninterruptible` region keeps the chain.** On an interruptible fiber it
masks and pushes `Prim.setInterruptible true`. On a masked fiber it changes nothing. It is the
field `uninterruptible` of `saved_mask_pop_discipline`. -/
@[semantics "scope-lifetime-finalization"]
theorem uninterruptible_maskChain (base : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (valid : MaskChain base f.interruptible f.stack) :
    MaskChain base f.uninterruptible.interruptible f.uninterruptible.stack := by
  cases flag : f.interruptible <;>
    aesop (add norm simp [uninterruptible_masks, uninterruptible_already_masked, MaskChain])

/-- **The entry of an `interruptible` region keeps the chain.** On a masked fiber it sets the
flag and pushes `Prim.setInterruptible false`. On an interruptible fiber it changes nothing. It
is the field `interruptibleRegion` of `saved_mask_pop_discipline`. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptibleRegion_maskChain (base : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (valid : MaskChain base f.interruptible f.stack) :
    MaskChain base f.interruptibleRegion.fst.interruptible f.interruptibleRegion.fst.stack := by
  cases flag : f.interruptible <;>
    aesop (add norm simp [interruptibleRegion_masked, interruptibleRegion_already,
      setFiberInterruptible_flag, setFiberInterruptible_pushes, MaskChain])

/-! ## The pop -/

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- **The drain keeps the chain.** `passPushed` pops the top frame of the scratch stack and runs
its hook, so this is `ensure_maskChain` at that frame. It asks for no scratch premise. A step of
`popFrom_maskChain`: both shapes of `continueFrom_cases` read it. -/
@[semantics "scope-lifetime-finalization"]
theorem passPushed_maskChain (base : Bool) (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α))
    (rest : List (Prim ν σ β ε δ ι α))
    (valid : MaskChain base fiber.interruptible (fiber.stack ++ rest)) :
    MaskChain base (passPushed demand skip fiber cause).fiber.interruptible
      ((passPushed demand skip fiber cause).fiber.stack ++ rest) := by
  rw [passPushed_fiber_cause]
  cases scratch : fiber.stack with
  | nil =>
    rw [passPushed_nil demand skip fiber scratch]
    exact valid
  | cons pushed below =>
    rw [passPushed_fiber demand skip fiber pushed below scratch]
    rw [scratch] at valid
    exact ensure_maskChain base pushed { fiber with stack := below } rest valid

/-- **One drain empties what one hook pushed** onto an empty scratch stack. A hook pushes
nothing, or it pushes one `Prim.setInterruptible true` (`ensure_stack_cases`), and that frame's
own hook pushes nothing. A step of `popFrom_maskChain`: the recursive call meets the scratch
premise again. It is a general equation of the frames, with no word of the chain. -/
@[semantics "scope-lifetime-finalization"]
theorem passPushed_ensure_stack_nil (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α))
    (scratchEmpty : fiber.stack = []) :
    (passPushed demand skip (frame.ensure fiber).fst cause).fiber.stack = [] := by
  rw [passPushed_fiber_cause]
  rcases ensure_stack_cases frame fiber with same | ⟨pushed, -, -⟩
  · rw [passPushed_nil demand skip _ (same.trans scratchEmpty)]
    exact same.trans scratchEmpty
  · rw [passPushed_fiber demand skip _ (Prim.setInterruptible true) fiber.stack pushed,
      Prim.ensure_setInterruptible_stack]
    exact scratchEmpty

/-- **The pop keeps the chain.** From an empty scratch stack, with the chain over the fiber's
flag and the frames, the result has the chain at the same base over its flag and its stack.
Every demand, skip flag and carried cause is in the domain. It is the field `pop` of
`saved_mask_pop_discipline`.

The scratch premise is needed: `getCont` detaches the stack, so the hooks push onto an empty
scratch stack. The induction follows `popFrom_interruptedCause`. -/
@[semantics "scope-lifetime-finalization"]
theorem popFrom_maskChain (base : Bool) (demand : Arm) (skip : Bool)
    (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) (scratchEmpty : f.stack = [])
    (valid : MaskChain base f.interruptible frames) :
    MaskChain base (popFrom demand skip frames f cause).fiber.interruptible
      (popFrom demand skip frames f cause).fiber.stack := by
  rw [popFrom_fiber_cause]
  induction frames generalizing f with
  | nil =>
    rw [popFrom_nil, scratchEmpty]
    exact valid
  | cons head rest ih =>
    have hooked : MaskChain base (head.ensure f).fst.interruptible
        ((head.ensure f).fst.stack ++ rest) :=
      ensure_maskChain base head f rest (by rw [scratchEmpty]; exact valid)
    have drained := passPushed_maskChain base demand skip (head.ensure f).fst none rest hooked
    have emptied := passPushed_ensure_stack_nil demand skip head f none scratchEmpty
    have continued : MaskChain base (continueFrom demand skip head rest f).fiber.interruptible
        (continueFrom demand skip head rest f).fiber.stack := by
      rcases continueFrom_cases demand skip head rest f with shape | shape <;> rw [shape]
      · rw [emptied] at drained
        exact ih _ emptied drained
      · exact drained
    cases answered : head.answerOf demand (head.ensure f).snd with
    | none =>
      rw [popFrom_continue_fiber demand skip head rest f (Or.inl answered)]
      exact continued
    | some answer =>
      cases skipped : (skip && (head.ensure f).fst.interrupted) with
      | true =>
        rw [popFrom_continue_fiber demand skip head rest f (Or.inr skipped)]
        exact continued
      | false =>
        rw [popFrom_answer_fiber demand skip head rest f answer answered skipped]
        exact hooked

/-- **`getCont` keeps the chain.** Its branch of a deferred interrupt keeps the stack and the
flag. Its other branch is the pop from an empty scratch stack. It is the field `getCont` of
`saved_mask_pop_discipline`. -/
@[semantics "scope-lifetime-finalization"]
theorem getCont_maskChain (base : Bool) (f : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (skip : Bool) (cause : Option (Cause ε δ ι α))
    (valid : MaskChain base f.interruptible f.stack) :
    MaskChain base (f.getCont demand skip cause).fiber.interruptible
      (f.getCont demand skip cause).fiber.stack := by
  unfold getCont
  split
  · exact valid
  · exact popFrom_maskChain base demand skip f.stack _ cause rfl valid

end Effect4.FrameFiber

namespace Effect4.Machine

open Effect4 Effect4.FrameFiber

section Adapter

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- **The finished frame's path keeps the chain.** `frameExitState` is one of two calls of
`getCont`: a failure skips interrupted handlers, and every other exit demands the value arm. It
is the field `frameExit` of `saved_mask_pop_discipline`, and the seam that the later lift reads
before `Cmd.finish`. -/
@[semantics "scope-lifetime-finalization"]
theorem frameExitState_maskChain (base : Bool) (f : FrameFiber ν σ β ε δ ι α)
    (valid : MaskChain base f.interruptible f.stack) :
    MaskChain base (frameExitState f).interruptible (frameExitState f).stack := by
  unfold frameExitState
  split <;> exact getCont_maskChain base f _ _ _ valid

end Adapter

/-! ## The placed theorem -/

/-- The statements of the proposed registry claim `saved-mask-pop-discipline`. Each field keeps
the chain at one fixed base, over the polymorphic `FrameFiber`. The four instances are those of
the pop's definitions. -/
structure MaskPopDiscipline (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] : Prop where
  /-- **The pop keeps the chain.** The fiber's scratch stack is empty, and the chain holds over
  the fiber's flag and the frames. Then it holds over the result's flag and stack. Every demand,
  skip flag and carried cause is in the domain. -/
  pop : ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List (Prim ν σ β ε δ ι α))
    (f : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)), f.stack = [] →
    MaskChain base f.interruptible frames →
      MaskChain base (popFrom demand skip frames f cause).fiber.interruptible
        (popFrom demand skip frames f cause).fiber.stack
  /-- **`getCont` keeps the chain**, on its branch of a deferred interrupt and on its pop. -/
  getCont : ∀ (base : Bool) (f : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)), MaskChain base f.interruptible f.stack →
      MaskChain base (f.getCont demand skip cause).fiber.interruptible
        (f.getCont demand skip cause).fiber.stack
  /-- **The finished frame's path keeps the chain**: the state that `Machine.frameExitState`
  retains before `Cmd.finish`. -/
  frameExit : ∀ (base : Bool) (f : FrameFiber ν σ β ε δ ι α),
    MaskChain base f.interruptible f.stack →
      MaskChain base (frameExitState f).interruptible (frameExitState f).stack
  /-- **The entry of an `uninterruptible` region keeps the chain.** It pushes the frame that
  returns the flag exactly when it changes the flag. -/
  uninterruptible : ∀ (base : Bool) (f : FrameFiber ν σ β ε δ ι α),
    MaskChain base f.interruptible f.stack →
      MaskChain base f.uninterruptible.interruptible f.uninterruptible.stack
  /-- **The entry of an `interruptible` region keeps the chain**, in the same way. -/
  interruptibleRegion : ∀ (base : Bool) (f : FrameFiber ν σ β ε δ ι α),
    MaskChain base f.interruptible f.stack →
      MaskChain base f.interruptibleRegion.fst.interruptible f.interruptibleRegion.fst.stack
  /-- **Two fibers with one base and one stack have one flag.** The fixed base is needed: two
  empty stacks with opposite flags have each its own base. -/
  sameFlag : ∀ (base : Bool) (f g : FrameFiber ν σ β ε δ ι α), f.stack = g.stack →
    MaskChain base f.interruptible f.stack → MaskChain base g.interruptible g.stack →
      f.interruptible = g.interruptible

/-- **The saved mask's chain through a pop of the stack** (the proposed registry claim
`saved-mask-pop-discipline`; concept `scope-lifetime-finalization`, requirement R11). It is a
step of the open run-level half of `saved-mask-restoration`. Each field cites one theorem of
this module, so its status is derived from theirs (`#plan_status`).

Reach: the polymorphic `FrameFiber`, at every stack, demand, skip flag and carried cause, with
one fixed base. The pop asks for an empty scratch stack, as `getCont` calls it.

It does not establish a law of a run, a completed exit, a cleanup's multiplicity, a delivery, a
budget or liveness. It says nothing of a host or of a printed form. The bracket of a whole region
and each fiber's base in a run are not stated.

Its consumers are the later lift through `Machine.Lift`, then the waiting wrapper under a masked
caller and Semaphore's protected permit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_mask_pop_discipline (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    MaskPopDiscipline ν σ β ε δ ι α where
  pop := popFrom_maskChain
  getCont := getCont_maskChain
  frameExit := frameExitState_maskChain
  uninterruptible := uninterruptible_maskChain
  interruptibleRegion := interruptibleRegion_maskChain
  sameFlag := fun _ _ _ same valid valid' => valid.flag_eq (same ▸ valid')

end Effect4.Machine
