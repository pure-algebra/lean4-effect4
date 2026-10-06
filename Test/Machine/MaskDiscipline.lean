import Effect4.Laws.Machine.MaskDiscipline
import Effect4.Laws.Machine.LiveStack
import ProofGraph.Plan

/-!
# Test.Machine.MaskDiscipline — the saved mask's chain through a pop: finite controls

`saved_mask_pop_discipline` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`) is the law: at one
fixed base bit, the frame machine's pop, `getCont`, the finished frame's path and the entry of
each region keep the chain of restoring frames (`FrameFiber.MaskChain`). This battery evaluates
the chain on real fibers, at the alphabets `Nat`.

- Five positive rows, one for each row of the table of controls in Codex's packet
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/deeper-proof-support/semantic/candidate.md`):
  both empty stacks, one restoring frame, a nested chain, a pending cause, and the two finalizers
  that mask and push.
- One sweep: every stack of at most four frames over eight frames, both flags, both bases, a
  pending cause or none, a deferred interrupt or none. Each state that holds the chain keeps it
  through every pop and every entry.
- Five red controls, each red at its own property: a pop that drops a restoring frame without
  its hook; a finalizer that masks and pushes no restoring frame; the same-flag statement
  without the fixed base; a relation that keeps the base and omits the alternation; the pop's
  statement without the scratch premise.

Placement. Each guard is a finite instance of the registry claim proposed as
`saved-mask-pop-discipline` (concept `scope-lifetime-finalization`, requirement R11). A fiber
outside the sweep is not checked here: the theorem is the general statement. The battery states
no law of a run. The region's bracket of row 1 is four instances, and no theorem states it. The
pinned statements, axioms and plan status follow the controls.
-/

set_option autoImplicit false

universe u v

namespace Test.Machine.MaskDiscipline

open Effect4 Effect4.FrameFiber Effect4.Machine

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

/-! ## The fibers -/

private def cause : C := ⟨[.interrupt (some 53) .empty]⟩

private def value : P := .onSuccess (.success 2) 3
private def handler : P := .onFailure (.success 4) 5

/-- A fiber with an empty stack. Its flag is its base. -/
private def emptyAt (flag : Bool) : F := ⟨.success 0, [], flag, none, false⟩

/-- Row 2: a masked fiber under one restoring frame, at base true. -/
private def oneFrame : F := ⟨.success 0, [.setInterruptible true], false, none, false⟩

/-- Row 3: both saved bits, with neutral frames between them, at base true. -/
private def nested : F :=
  ⟨.success 0, [.sync 1, .setInterruptible false, value, .setInterruptible true, handler], true,
    none, false⟩

/-- Row 4: a cause is pending when the restoring frame passes. -/
private def pending : F := ⟨.success 0, [.setInterruptible true, value], false, some cause, false⟩

/-- Row 5: the parking finalizer, which masks and pushes on an interruptible fiber. -/
private def parked : F := ⟨.success 0, [.asyncFinalizer 7, value], true, none, false⟩

/-- Row 5: an `onExit` whose finalizer runs masked. -/
private def guarded : F := ⟨.success 0, [.onExit (.success 1) 9 false, handler], true, none, false⟩

/-- The chain over a fiber's flag and its stack, decided by the law module's instance. -/
private def holds (base : Bool) (f : F) : Bool := decide (MaskChain base f.interruptible f.stack)

private def bools : List Bool := [true, false]

/-! ## Row 1: both empty stacks, each at its own base -/

#guard holds true (emptyAt true) && holds false (emptyAt false)

-- A pop of the empty stack leaves the bit and the empty stack, at each demand and skip flag.
#guard bools.all fun b => Arm.all.all fun d => bools.all fun s =>
  ((emptyAt b).getCont d s).fiber == emptyAt b
#guard bools.all fun b => frameExitState (emptyAt b) == emptyAt b

-- The entry that asks for the fiber's own flag leaves the fiber.
#guard (emptyAt false).uninterruptible == emptyAt false
#guard (emptyAt true).interruptibleRegion.fst == emptyAt true

-- The entry that changes the flag pushes the frame that returns it, and the base stays.
#guard (emptyAt true).uninterruptible == ⟨.success 0, [.setInterruptible true], false, none, false⟩
#guard (emptyAt false).interruptibleRegion.fst ==
  ⟨.success 0, [.setInterruptible false], true, none, false⟩
#guard holds true (emptyAt true).uninterruptible &&
  holds false (emptyAt false).interruptibleRegion.fst

-- The pop after an entry returns the entry's fiber: a region's bracket, at four instances.
#guard bools.all fun b =>
  ((emptyAt b).uninterruptible.getCont .contA false).fiber == emptyAt b &&
    ((emptyAt b).interruptibleRegion.fst.getCont .contA false).fiber == emptyAt b

/-! ## Row 2: one restoring frame, popped -/

#guard holds true oneFrame
#guard (oneFrame.getCont .contA false).popped == [.setInterruptible true]
#guard Arm.all.all fun d => bools.all fun s => (oneFrame.getCont d s).fiber == emptyAt true
#guard frameExitState oneFrame == emptyAt true
#guard frameExitState { oneFrame with current := .failure cause } ==
  { emptyAt true with current := .failure cause }

/-! ## Row 3: a nested chain with both saved bits, and neutral frames between them -/

#guard holds true nested

-- A value demand stops at `value`: the fiber is masked, under the frame that returns the base.
#guard (nested.getCont .contA false).fiber ==
  ⟨.success 0, [.setInterruptible true, handler], false, none, false⟩
-- A cause demand passes both restoring frames and stops at `handler`, at the base.
#guard (nested.getCont .contE true).fiber == emptyAt true
#guard Arm.all.all fun d => bools.all fun s => holds true (nested.getCont d s).fiber
#guard Arm.all.all fun d => bools.all fun s =>
  holds true ({ nested with interruptedCause := some cause }.getCont d s (some cause)).fiber

/-! ## Row 4: a cause that is pending when a restoring frame passes -/

#guard holds true pending

-- The bit is restored, and the replacement is failure with that cause.
#guard (pending.getCont .contA false).answer == .replacement (.failure cause)
#guard (pending.getCont .contA false).fiber == ⟨.success 0, [value], true, some cause, false⟩
#guard holds true (pending.getCont .contA false).fiber
-- With the skip on, the pop discards the replacement and walks on. The chain holds at the end.
#guard (pending.getCont .contE true (some cause)).fiber == ⟨.success 0, [], true, some cause, false⟩
#guard holds true (pending.getCont .contE true (some cause)).fiber

/-! ## Row 5: `onExit` and `asyncFinalizer`, which mask and push during the pop -/

#guard holds true parked && holds true guarded

-- The parking finalizer passes a value demand. The drain visits the frame it pushed, next.
#guard (parked.getCont .contA false).popped == [.asyncFinalizer 7, .setInterruptible true, value]
#guard (parked.getCont .contA false).fiber == emptyAt true
-- With a cause pending, the visited frame answers before `value`: failure with that cause.
#guard ({ parked with interruptedCause := some cause }.getCont .contA false).answer ==
  .replacement (.failure cause)
#guard ({ parked with interruptedCause := some cause }.getCont .contA false).popped ==
  [.asyncFinalizer 7, .setInterruptible true]
#guard ({ parked with interruptedCause := some cause }.getCont .contA false).fiber ==
  ⟨.success 0, [value], true, some cause, false⟩
-- The parking finalizer answers a cause demand, and it keeps the frame it pushed.
#guard (parked.getCont .contE true).fiber ==
  ⟨.success 0, [.setInterruptible true, value], false, none, false⟩
-- `onExit` answers, and it keeps the frame it pushed.
#guard (guarded.getCont .contA false).fiber ==
  ⟨.success 0, [.setInterruptible true, handler], false, none, false⟩
#guard [parked, guarded, { parked with interruptedCause := some cause }].all fun f =>
  Arm.all.all fun d => bools.all fun s => holds true (f.getCont d s).fiber
-- The live traversal visits the pushed frame in the same order (`popLive_eq_popFrom`).
#guard parked.getContLive .contA false == parked.getCont .contA false

/-- The proved control for the visit and for the order of the pending cause, at this instance. -/
example :
    (popFrom Arm.contA false [(.asyncFinalizer 7 : P)]
        { emptyAt true with interruptedCause := some cause }).answer =
      ContAnswer.replacement (Prim.failure cause) ∧
    (popFrom Arm.contA false [(.asyncFinalizer 7 : P)]
        { emptyAt true with interruptedCause := some cause }).popped =
      [Prim.asyncFinalizer 7, Prim.setInterruptible true] :=
  popFrom_asyncFinalizer_pops_its_push 7 cause _ rfl rfl rfl

/-! ## The sweep

Every stack of at most four frames over eight frames: both restoring frames, both `onExit`
frames, the parking finalizer, a value frame, a cause frame and a primitive that is no frame.
Each state has a flag, a base, a pending cause or none, and a deferred interrupt or none. -/

private def alphabet : List P :=
  [.setInterruptible true, .setInterruptible false, .onExit (.success 1) 9 false,
    .onExit (.success 1) 9 true, .asyncFinalizer 7, value, handler, .sync 6]

private def stacksUpTo : Nat → List (List P)
  | 0 => [[]]
  | n + 1 => [] :: (stacksUpTo n).flatMap fun stack => alphabet.map (· :: stack)

/-- The states of the sweep that hold the chain, each with its base. -/
private def states (depth : Nat) : List (Bool × F) :=
  (stacksUpTo depth).flatMap fun stack => bools.flatMap fun flag => bools.flatMap fun base =>
    [none, some cause].flatMap fun pendingCause => bools.filterMap fun deferred =>
      let f : F := ⟨.success 0, stack, flag, pendingCause, deferred⟩
      if holds base f then some (base, f) else none

#guard (stacksUpTo 4).length == 4681
#guard (states 4).length == 22408

-- Every pop keeps the chain at the same base: each demand, each skip flag, a carried cause.
#guard (states 4).all fun (base, f) => Arm.all.all fun d => bools.all fun s =>
  holds base (f.getCont d s).fiber && holds base (f.getCont d s (some cause)).fiber
-- The finished frame's path keeps it, on a success and on a failure.
#guard (states 4).all fun (base, f) =>
  holds base (frameExitState f) && holds base (frameExitState { f with current := .failure cause })
-- Each entry keeps it.
#guard (states 4).all fun (base, f) =>
  holds base f.uninterruptible && holds base f.interruptibleRegion.fst
-- One base and one stack give one flag: the other flag has no chain there.
#guard (states 4).all fun (base, f) => !holds base { f with interruptible := !f.interruptible }

/-! ## The red controls -/

/-! ### 1. A pop that drops a restoring frame without its hook -/

/-- A wrong pop of one frame: the top frame leaves the stack, and its hook does not run. -/
private def popNoHook (f : F) : F := { f with stack := f.stack.tail }

private def restoringTop (f : F) : Bool :=
  match f.stack with
  | .setInterruptible _ :: _ => true
  | _ => false

-- On row 2's fiber it ends with the real pop's stack and the wrong flag, so the chain breaks.
#guard (popNoHook oneFrame).stack == (oneFrame.getCont .contA false).fiber.stack
#guard (popNoHook oneFrame).interruptible != (oneFrame.getCont .contA false).fiber.interruptible
#guard !holds true (popNoHook oneFrame)
#guard holds true (oneFrame.getCont .contA false).fiber
-- Over the sweep it breaks the chain exactly where the dropped frame is a restoring frame.
#guard (states 4).all fun (base, f) => holds base (popNoHook f) == !restoringTop f

/-! ### 2. A finalizer that masks and pushes no restoring frame -/

/-- A wrong hook of a masking finalizer: it masks, and it pushes no restoring frame. -/
private def maskNoPush (f : F) : F := { f with interruptible := false }

-- On the empty stack at base true it ends with the real hook's flag and no frame, so the chain
-- breaks.
#guard (maskNoPush (emptyAt true)).interruptible ==
  ((Prim.asyncFinalizer 7 : P).ensure (emptyAt true)).fst.interruptible
#guard (maskNoPush (emptyAt true)).stack == []
#guard ((Prim.asyncFinalizer 7 : P).ensure (emptyAt true)).fst.stack == [.setInterruptible true]
#guard !holds true (maskNoPush (emptyAt true))
#guard holds true ((Prim.asyncFinalizer 7 : P).ensure (emptyAt true)).fst
-- Over the sweep it breaks the chain exactly where it changes the flag. The real hook keeps it.
#guard (states 4).all fun (base, f) => holds base (maskNoPush f) == !f.interruptible
#guard (states 4).all fun (base, f) => holds base ((Prim.asyncFinalizer 7 : P).ensure f).fst

/-! ### 3. The same-flag statement without the fixed base -/

/-- Two empty stacks with opposite flags, each at its own base: without one fixed base, one
stack does not give one flag. -/
theorem sameFlag_needs_base :
    ¬ ∀ (base base' flag flag' : Bool) (stack : List P),
      MaskChain base flag stack → MaskChain base' flag' stack → flag = flag' :=
  fun h => Bool.noConfusion (h true false true false [] rfl rfl)

/-! ### 4. A relation that keeps the base and omits the alternation -/

/-- The chain without its alternation: a restoring frame forgets the flag above it. The lowest
saved flag is still the base. -/
private def BaseOnly (base : Bool) : Bool → List P → Prop
  | flag, [] => flag = base
  | _, Prim.setInterruptible saved :: rest => BaseOnly base saved rest
  | flag, _ :: rest => BaseOnly base flag rest

/-- Both flags stand over one restoring frame at one base. So the weaker relation does not make
the flag a function of the base and of the stack. -/
theorem baseOnly_two_flags :
    ¬ ∀ (base flag flag' : Bool) (stack : List P),
      BaseOnly base flag stack → BaseOnly base flag' stack → flag = flag' :=
  fun h => Bool.noConfusion (h true true false [.setInterruptible true] rfl rfl)

/-- The weaker relation still keeps the base: the other base has no such stack. -/
example : ¬ BaseOnly false true [.setInterruptible true] := fun h => Bool.noConfusion h

-- The chain refuses the flag that the frame does not negate.
#guard !decide (MaskChain true true ([.setInterruptible true] : List P))
#guard decide (MaskChain true false ([.setInterruptible true] : List P))

/-! ### 5. The pop's statement without the scratch premise -/

/-- The witness of Codex's adversarial note
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/deeper-proof-support/semantic/adversarial.md`):
no frame, base false, a masked fiber, and one restoring frame on the scratch stack. The premise
on the frames holds, and the result has no chain at the base. -/
theorem pop_needs_empty_scratch :
    ¬ ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List P) (f : F) (carried : Option C),
      MaskChain base f.interruptible frames →
        MaskChain base (popFrom demand skip frames f carried).fiber.interruptible
          (popFrom demand skip frames f carried).fiber.stack := by
  intro h
  exact absurd (h false .contA false [] ⟨.success 0, [.setInterruptible true], false, none, false⟩
    none rfl) (by decide)

/-- A chain over the scratch stack followed by the frames does not replace the premise. At flag
false, scratch `[setInterruptible true]`, frames `[setInterruptible false]` and base false, the
pop ends at flag true with an empty stack. -/
theorem pop_needs_empty_scratch_joined :
    ¬ ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List P) (f : F) (carried : Option C),
      MaskChain base f.interruptible (f.stack ++ frames) →
        MaskChain base (popFrom demand skip frames f carried).fiber.interruptible
          (popFrom demand skip frames f carried).fiber.stack := by
  intro h
  exact absurd (h false .contA false [.setInterruptible false]
    ⟨.success 0, [.setInterruptible true], false, none, false⟩ none (by decide)) (by decide)

/-- Fibers with a scratch stack of at most one frame, each with at most two frames to pop and
a base that the frames hold at the fiber's flag. -/
private def loose : List (Bool × List P × F) :=
  (stacksUpTo 2).flatMap fun frames => (stacksUpTo 1).flatMap fun scratch =>
    bools.flatMap fun flag => bools.filterMap fun base =>
      let f : F := ⟨.success 0, scratch, flag, none, false⟩
      if decide (MaskChain base flag frames) then some (base, frames, f) else none

private def broken : List (Bool × List P × F) :=
  loose.filter fun (base, frames, f) => !holds base (popFrom Arm.contA false frames f).fiber

-- The statement without the premise fails, and only where the scratch stack is not empty.
#guard !broken.isEmpty
#guard broken.all fun (_, _, f) => !f.stack.isEmpty

/-! ## The statements, pinned

The placed theorem at every alphabet with the four instances, and each field as it stands, by
its type at the alphabets `Nat`. -/

example (ν σ : Type u) (β : Type v) (ε δ ι α : Type u)
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    MaskPopDiscipline ν σ β ε δ ι α :=
  saved_mask_pop_discipline ν σ β ε δ ι α

/-- The placed theorem at the alphabets `Nat`. -/
private theorem atNat : MaskPopDiscipline Nat Nat Nat Nat Nat Nat Nat :=
  saved_mask_pop_discipline Nat Nat Nat Nat Nat Nat Nat

example : ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List P) (f : F)
    (carried : Option C), f.stack = [] → MaskChain base f.interruptible frames →
      MaskChain base (popFrom demand skip frames f carried).fiber.interruptible
        (popFrom demand skip frames f carried).fiber.stack :=
  atNat.pop

example : ∀ (base : Bool) (f : F) (demand : Arm) (skip : Bool) (carried : Option C),
    MaskChain base f.interruptible f.stack →
      MaskChain base (f.getCont demand skip carried).fiber.interruptible
        (f.getCont demand skip carried).fiber.stack :=
  atNat.getCont

example : ∀ (base : Bool) (f : F), MaskChain base f.interruptible f.stack →
    MaskChain base (frameExitState f).interruptible (frameExitState f).stack :=
  atNat.frameExit

example : ∀ (base : Bool) (f : F), MaskChain base f.interruptible f.stack →
    MaskChain base f.uninterruptible.interruptible f.uninterruptible.stack :=
  atNat.uninterruptible

example : ∀ (base : Bool) (f : F), MaskChain base f.interruptible f.stack →
    MaskChain base f.interruptibleRegion.fst.interruptible f.interruptibleRegion.fst.stack :=
  atNat.interruptibleRegion

example : ∀ (base : Bool) (f g : F), f.stack = g.stack →
    MaskChain base f.interruptible f.stack → MaskChain base g.interruptible g.stack →
      f.interruptible = g.interruptible :=
  atNat.sameFlag

/-- A field in use: the pop of row 3's fiber, with a carried cause, keeps the chain. -/
example : MaskChain true (nested.getCont .contE true (some cause)).fiber.interruptible
    (nested.getCont .contE true (some cause)).fiber.stack :=
  atNat.getCont true nested .contE true (some cause) (by decide)

/-- The same-flag field in use: a fiber after an entry and its pop has the entry's stack, so it
has the entry's flag. A later lift must supply the two premises on the chain. -/
example : ((emptyAt true).uninterruptible.getCont .contA false).fiber.interruptible =
    (emptyAt true).interruptible :=
  atNat.sameFlag true _ _ (by decide) (by decide) (by decide)

/-! ## The pinned outputs

The axioms of the placed theorem and of the three statements of Codex's packet, and the placed
theorem's standing as the plan derives it from its proof. It was a planned goal, and it is
proved in place with its statement unchanged. The counts are of this battery's tree, which holds
no step of the proof: the steps are in the law graph. -/

/-- info: 'Effect4.Machine.saved_mask_pop_discipline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms saved_mask_pop_discipline

/-- info: 'Effect4.FrameFiber.popFrom_maskChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms popFrom_maskChain

/-- info: 'Effect4.FrameFiber.getCont_maskChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms getCont_maskChain

/-- info: 'Effect4.Machine.frameExitState_maskChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frameExitState_maskChain

/--
info: Effect4.Machine.saved_mask_pop_discipline: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status saved_mask_pop_discipline

end Test.Machine.MaskDiscipline
