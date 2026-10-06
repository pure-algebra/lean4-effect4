import Effect4.Machine.Fibers
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

end Effect4.FrameFiber

namespace Effect4.Machine

open Effect4 Effect4.FrameFiber

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
step of the open run-level half of `saved-mask-restoration`.

Reach: the polymorphic `FrameFiber`, at every stack, demand, skip flag and carried cause, with
one fixed base. The pop asks for an empty scratch stack, as `getCont` calls it.

It does not establish a law of a run, a completed exit, a cleanup's multiplicity, a delivery, a
budget or liveness. It says nothing of a host or of a printed form. The bracket of a whole region
and each fiber's base in a run are not stated.

Its consumers are the later lift through `Machine.Lift`, then the waiting wrapper under a masked
caller and Semaphore's protected permit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal saved_mask_pop_discipline (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    MaskPopDiscipline ν σ β ε δ ι α

end Effect4.Machine
