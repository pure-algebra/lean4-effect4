import Std

/-!
# Frame-machine runtime counterexamples

This file is a self-contained breaker model of the `effect@4.0.0-rc.112`
continuation-stack machine. It deliberately does not import
`Effect4.Runtime.Runtime`: the witnesses must remain executable while the
production surface is still absent, and they must keep proving the attack after
the repaired declarations land.

Each theorem is finite and proves only the named attack. None of them is a
production law; the frozen laws live in `test/contracts/frames.contract.md`.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` sections 1-4.
-/

set_option autoImplicit false

namespace Effect4Test.Counterexamples.Runtime.Frames

/-! ## The shared miniature machine

A cause is a flat ordered list of error codes, matching the `Cause` packet's
carrier. A continuation is a nominal `Nat` name; `runA`, `runE`, `finalizerExit`
and the loop and generator interpretations are the externally supplied
functions, the shape the production model takes as a parameter.
-/

/-- A miniature flat cause. -/
abbrev MiniCause := List Nat

/-- A miniature exit. -/
inductive MiniExit
  | success (value : Nat)
  | failure (cause : MiniCause)
  deriving DecidableEq, Repr

/-- `causeCombine`: a duplicate-free union in left-then-right order. -/
def combine (left right : MiniCause) : MiniCause :=
  if left = [] then right
  else if right = [] then left
  else (left ++ right).foldl (fun acc reason =>
    if acc.contains reason then acc else acc ++ [reason]) []

/-- The three continuation slots. -/
inductive Arm
  | contA
  | contE
  | contAll
  deriving DecidableEq, Repr

/-- The primitives this packet models, one constructor per pinned op. -/
inductive Prim
  | success (value : Nat)
  | failure (cause : MiniCause)
  | onSuccess (body : Prim) (onValue : Nat)
  | onFailure (body : Prim) (onCause : Nat)
  | onSuccessAndFailure (body : Prim) (onValue : Nat) (onCause : Nat)
  | exitFrame (body : Prim)
  | onExit (body : Prim) (finalizer : Nat) (finalizerInterruptible : Bool)
  | setInterruptible (flag : Bool)
  | whileLoop (loop : Nat) (cursor : Nat)
  | iterator (generator : Nat) (cursor : Nat)
  deriving DecidableEq, Repr

/-- The frame-arm matrix of `docs/effect-rc112-fiber-runtime.html` section 3. -/
def arms : Prim -> List Arm
  | .success _ => []
  | .failure _ => []
  | .onSuccess _ _ => [.contA]
  | .onFailure _ _ => [.contE]
  | .onSuccessAndFailure _ _ _ => [.contA, .contE]
  | .exitFrame _ => [.contA, .contE]
  | .onExit _ _ _ => [.contA, .contE, .contAll]
  | .setInterruptible _ => [.contAll]
  | .whileLoop _ _ => [.contA]
  | .iterator _ _ => [.contA]

def hasArm (self : Prim) (arm : Arm) : Bool := (arms self).contains arm

/-- The five-field fiber state. -/
structure Fiber where
  current : Prim
  stack : List Prim
  interruptible : Bool
  pending : Option MiniCause
  deferred : Bool
  deriving DecidableEq, Repr

def Fiber.interrupted (self : Fiber) : Bool :=
  self.interruptible && self.pending.isSome

/-- The externally supplied continuation interpretation. -/
def runA : Nat -> Nat -> Prim
  | 0, value => .success value
  | 1, value => .success (value + 100)
  | 2, value => .success (value + 200)
  | _, value => .success value

/-- The externally supplied failure-handler interpretation: every handler
recovers with the value `99`, which is what makes a skipped handler visible. -/
def runE : Nat -> MiniCause -> Prim
  | _, _ => .success 99

/-- The externally supplied finalizer outcome. `0` succeeds (rc.112's void
finalizer), `1` fails with its own reason. -/
def finalizerExit : Nat -> MiniExit -> MiniExit
  | 0, _ => .success 0
  | 1, _ => .failure [1]
  | _, _ => .success 0

/-! ## contAll -/

/-- The pinned `[contAll]`: `OnExit` masks unless told not to, and
`SetInterruptible` restores the flag and substitutes `failCause(cause)` for both
arms when the fiber becomes interruptible with a pending cause. -/
def ensurePinned (frame : Prim) (fiber : Fiber) : Fiber × Option Prim :=
  match frame with
  | .onExit _ _ finalizerInterruptible =>
    if fiber.interruptible = true && finalizerInterruptible = false then
      ({ fiber with
          interruptible := false,
          stack := Prim.setInterruptible true :: fiber.stack }, none)
    else (fiber, none)
  | .setInterruptible flag =>
    match fiber.pending with
    | some cause =>
      if flag = true then ({ fiber with interruptible := true }, some (.failure cause))
      else ({ fiber with interruptible := flag }, none)
    | none => ({ fiber with interruptible := flag }, none)
  | _ => (fiber, none)

/-- E4-RUN-CE-013's rejected `SetInterruptible`: restore the flag and answer
nothing, so a pending cause is never turned into the continuation. -/
def ensureNoSubstitution (frame : Prim) (fiber : Fiber) : Fiber × Option Prim :=
  match frame with
  | .setInterruptible flag => ({ fiber with interruptible := flag }, none)
  | _ => ensurePinned frame fiber

/-- E4-RUN-CE-014's rejected `OnExit`: run the finalizer with the flag as it
stands, pushing no restoring frame. -/
def ensureNoMask (frame : Prim) (fiber : Fiber) : Fiber × Option Prim :=
  match frame with
  | .onExit _ _ _ => (fiber, none)
  | _ => ensurePinned frame fiber

/-! ## The pop -/

inductive Answer
  | replacement (next : Prim)
  | frame (frame : Prim)
  | empty
  deriving DecidableEq, Repr

def answerOf (frame : Prim) (demand : Arm) (replacement : Option Prim) : Option Answer :=
  match replacement with
  | some next => some (.replacement next)
  | none => if hasArm frame demand = true then some (.frame frame) else none

/-- The pinned pop: `contAll` runs on every frame passed, and the skip condition
is re-read after each `contAll`. -/
def popPinned (ensure : Prim -> Fiber -> Fiber × Option Prim) (demand : Arm)
    (skip : Bool) : List Prim -> Fiber -> Answer × List Prim × Fiber
  | [], fiber => (.empty, [], fiber)
  | frame :: rest, fiber =>
    let after := ensure frame fiber
    match answerOf frame demand after.snd with
    | some answer =>
      if skip = true && after.fst.interrupted = true then
        let tail := popPinned ensure demand skip rest after.fst
        (tail.fst, frame :: tail.snd.fst, tail.snd.snd)
      else
        (answer, [frame], { after.fst with stack := after.fst.stack ++ rest })
    | none =>
      let tail := popPinned ensure demand skip rest after.fst
      (tail.fst, frame :: tail.snd.fst, tail.snd.snd)

/-- E4-RUN-CE-010's rejected pop: run `contAll` only on the frame that answers,
because a frame that does not answer "was not used". -/
def popContAllOnAnswerOnly (demand : Arm) (skip : Bool) :
    List Prim -> Fiber -> Answer × List Prim × Fiber
  | [], fiber => (.empty, [], fiber)
  | frame :: rest, fiber =>
    if hasArm frame demand = true then
      let after := ensurePinned frame fiber
      match answerOf frame demand after.snd with
      | some answer =>
        if skip = true && after.fst.interrupted = true then
          let tail := popContAllOnAnswerOnly demand skip rest after.fst
          (tail.fst, frame :: tail.snd.fst, tail.snd.snd)
        else (answer, [frame], { after.fst with stack := after.fst.stack ++ rest })
      | none =>
        let tail := popContAllOnAnswerOnly demand skip rest after.fst
        (tail.fst, frame :: tail.snd.fst, tail.snd.snd)
    else
      let tail := popContAllOnAnswerOnly demand skip rest fiber
      (tail.fst, frame :: tail.snd.fst, tail.snd.snd)

/-- rc.112's `getCont` starts the loop with the stack detached, so whatever
`contAll` pushes lands on top of the frames that are left. -/
def getCont (ensure : Prim -> Fiber -> Fiber × Option Prim) (demand : Arm) (skip : Bool)
    (fiber : Fiber) : Answer × List Prim × Fiber :=
  popPinned ensure demand skip fiber.stack { fiber with stack := [] }

/-- E4-RUN-CE-012's rejected pop: decide the skip once, before the loop, instead
of re-reading the flag after every `contAll`. -/
def popSkipDecidedUpFront (demand : Arm) (skip : Bool) :
    List Prim -> Fiber -> Answer × List Prim × Fiber
  | [], fiber => (.empty, [], fiber)
  | frame :: rest, fiber =>
    let after := ensurePinned frame fiber
    match answerOf frame demand after.snd with
    | some answer =>
      if skip = true then
        let tail := popSkipDecidedUpFront demand skip rest after.fst
        (tail.fst, frame :: tail.snd.fst, tail.snd.snd)
      else (answer, [frame], { after.fst with stack := after.fst.stack ++ rest })
    | none =>
      let tail := popSkipDecidedUpFront demand skip rest after.fst
      (tail.fst, frame :: tail.snd.fst, tail.snd.snd)

/-! ## E4-RUN-CE-010 — contAll runs on every frame passed -/

/-- A fiber failing with `[7]`, with a mask frame below a user error handler. -/
def maskedHandlerFiber : Fiber :=
  { current := .failure [7]
    stack := [.setInterruptible false, .onFailure (.success 0) 5]
    interruptible := true
    pending := none
    deferred := false }

/-- E4-RUN-CE-010: the mask frame answers no `contE`, so a pop that runs
`contAll` only on the answering frame never clears the interruptible flag. The
pinned pop clears it on the way past. -/
theorem contAll_runs_on_skipped_frames :
    (getCont ensurePinned Arm.contE false maskedHandlerFiber).snd.snd.interruptible = false /\
      (popContAllOnAnswerOnly Arm.contE false maskedHandlerFiber.stack
        { maskedHandlerFiber with stack := [] }).snd.snd.interruptible = true := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-010: both pops walk past the same frame, so the difference is the
hook and not the traversal. -/
theorem contAll_skipped_frame_is_still_popped :
    (getCont ensurePinned Arm.contE false maskedHandlerFiber).snd.fst =
      (popContAllOnAnswerOnly Arm.contE false maskedHandlerFiber.stack
        { maskedHandlerFiber with stack := [] }).snd.fst := by
  decide

/-! ## E4-RUN-CE-011 — interruption skips user error handlers -/

/-- A fiber that has been interrupted while interruptible, with one user
`catchCause` handler on the stack. -/
def interruptedHandlerFiber : Fiber :=
  { current := .failure [7]
    stack := [.onFailure (.success 0) 5]
    interruptible := true
    pending := some [7]
    deferred := false }

/-- E4-RUN-CE-011: while the fiber is interruptible with a pending cause the
pinned pop discards the handler and empties the stack, so `catchCause` never
sees the interrupt. A pop without the skip hands the interrupt to the handler,
which recovers from it. -/
theorem interrupt_skips_user_handlers :
    (getCont ensurePinned Arm.contE true interruptedHandlerFiber).fst = Answer.empty /\
      (getCont ensurePinned Arm.contE false interruptedHandlerFiber).fst =
        Answer.frame (Prim.onFailure (Prim.success 0) 5) := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-011: the skip is conditional on the pending cause, not on the
demand. With no interruption recorded the same handler answers. -/
theorem skip_requires_a_pending_cause :
    (getCont ensurePinned Arm.contE true
        { interruptedHandlerFiber with pending := none }).fst =
      Answer.frame (Prim.onFailure (Prim.success 0) 5) := by
  decide

/-! ## E4-RUN-CE-012 — a mask frame stops the skip -/

/-- An interrupted fiber whose stack masks before its handler, exactly the shape
`uninterruptible (catchCause …)` leaves behind. -/
def interruptedMaskedFiber : Fiber :=
  { current := .failure [7]
    stack := [.setInterruptible false, .onFailure (.success 0) 5]
    interruptible := true
    pending := some [7]
    deferred := false }

/-- E4-RUN-CE-012: the skip condition is re-read after every `contAll`, so the
mask frame stops it and the handler inside the uninterruptible region does run.
A pop that decides the skip once, before the loop, empties the stack instead. -/
theorem mask_frame_stops_the_skip :
    (getCont ensurePinned Arm.contE true interruptedMaskedFiber).fst =
        Answer.frame (Prim.onFailure (Prim.success 0) 5) /\
      (popSkipDecidedUpFront Arm.contE true interruptedMaskedFiber.stack
        { interruptedMaskedFiber with stack := [] }).fst = Answer.empty := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-013 — SetInterruptible substitutes with a pending cause -/

/-- A fiber restoring interruptibility with an interrupt already recorded. -/
def restoringFiber : Fiber :=
  { current := .success 5
    stack := [.setInterruptible true, .onSuccess (.success 0) 1]
    interruptible := false
    pending := some [7]
    deferred := false }

/-- E4-RUN-CE-013: popping `SetInterruptible(true)` with a pending cause returns
`failCause(cause)` as the continuation for either arm, so the value never
reaches the `flatMap` above it. Restoring only the flag lets the success
continue and loses the interruption. -/
theorem set_interruptible_substitutes_with_a_pending_cause :
    (getCont ensurePinned Arm.contA false restoringFiber).fst =
        Answer.replacement (Prim.failure [7]) /\
      (getCont ensureNoSubstitution Arm.contA false restoringFiber).fst =
        Answer.frame (Prim.onSuccess (Prim.success 0) 1) := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-013: with no cause recorded the same frame substitutes nothing. -/
theorem set_interruptible_without_a_cause_substitutes_nothing :
    (getCont ensurePinned Arm.contA false { restoringFiber with pending := none }).fst =
      Answer.frame (Prim.onSuccess (Prim.success 0) 1) := by
  decide

/-! ## E4-RUN-CE-014 — the OnExit finalizer runs masked -/

/-- An interruptible fiber about to run an `ensuring` finalizer. -/
def finalizingFiber : Fiber :=
  { current := .success 5
    stack := [.onExit (.success 0) 0 false]
    interruptible := true
    pending := none
    deferred := false }

/-- E4-RUN-CE-014: the pinned `contAll` clears the flag and pushes the restoring
frame, so the finalizer runs uninterruptibly and interruptibility comes back
afterwards. Skipping the hook leaves the finalizer interruptible. -/
theorem on_exit_finalizer_runs_masked :
    (getCont ensurePinned Arm.contA false finalizingFiber).snd.snd.interruptible = false /\
        (getCont ensurePinned Arm.contA false finalizingFiber).snd.snd.stack =
          [Prim.setInterruptible true] /\
      ((getCont ensureNoMask Arm.contA false finalizingFiber).snd.snd.interruptible = true /\
        (getCont ensureNoMask Arm.contA false finalizingFiber).snd.snd.stack = []) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- E4-RUN-CE-014: `acquireUseRelease` asks for an interruptible release by
passing `true`, and then the hook does nothing. -/
theorem on_exit_told_not_to_mask :
    (getCont ensurePinned Arm.contA false
        { finalizingFiber with
          stack := [Prim.onExit (Prim.success 0) 0 true] }).snd.snd.interruptible = true := by
  decide

/-! ## E4-RUN-CE-015 and E4-RUN-CE-016 — restore, and merge by combine -/

/-- The pinned `OnExit` arm: run the finalizer, then restore the original exit,
merging a finalizer failure into the original cause. -/
def onExitArmPinned (finalizer : Nat) (closing : MiniExit) : MiniExit :=
  match closing, finalizerExit finalizer closing with
  | _, .success _ => closing
  | .success _, .failure finalizerCause => .failure finalizerCause
  | .failure cause, .failure finalizerCause => .failure (combine cause finalizerCause)

/-- E4-RUN-CE-015's rejected arm: the finalizer's own exit becomes the result. -/
def onExitArmFinalizerWins (finalizer : Nat) (closing : MiniExit) : MiniExit :=
  finalizerExit finalizer closing

/-- E4-RUN-CE-016's rejected arm: keep the original cause and drop the
finalizer's. -/
def onExitArmKeepsOriginal (_finalizer : Nat) (closing : MiniExit) : MiniExit :=
  closing

/-- E4-RUN-CE-016's other rejected arm: the finalizer's cause replaces the
original. -/
def onExitArmFinalizerCause (finalizer : Nat) (closing : MiniExit) : MiniExit :=
  match finalizerExit finalizer closing with
  | .success _ => closing
  | .failure finalizerCause => .failure finalizerCause

/-- E4-RUN-CE-015: a successful finalizer leaves the original exit alone. An arm
that returns the finalizer's exit loses the value the computation produced. -/
theorem on_exit_restores_the_original_exit :
    onExitArmPinned 0 (MiniExit.success 5) = MiniExit.success 5 /\
      onExitArmFinalizerWins 0 (MiniExit.success 5) = MiniExit.success 0 := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-016: a failing finalizer under a failed exit merges both causes by
`causeCombine`; neither cause may be dropped. -/
theorem finalizer_failure_merges_by_combine :
    onExitArmPinned 1 (MiniExit.failure [7]) = MiniExit.failure [7, 1] /\
      onExitArmKeepsOriginal 1 (MiniExit.failure [7]) = MiniExit.failure [7] /\
        onExitArmFinalizerCause 1 (MiniExit.failure [7]) = MiniExit.failure [1] := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-016: under a *successful* exit the finalizer's failure stands
alone, because `combineFinalizerCause` only combines on the failure arm. -/
theorem finalizer_failure_under_success_stands_alone :
    onExitArmPinned 1 (MiniExit.success 5) = MiniExit.failure [1] := by
  decide

/-! ## E4-RUN-CE-017 — the arms are assigned per instance -/

/-- The pinned `contA`: the name stored on this frame decides the continuation. -/
def armAPinned : Prim -> Nat -> Option Prim
  | .onSuccess _ onValue, value => some (runA onValue value)
  | .onSuccessAndFailure _ onValue _, value => some (runA onValue value)
  | _, _ => none

/-- E4-RUN-CE-017's rejected `contA`: the prototype fixes one continuation for
every `OnSuccess` instance, as it does for `evaluate`. -/
def armAPrototype : Prim -> Nat -> Option Prim
  | .onSuccess _ _, value => some (runA 0 value)
  | .onSuccessAndFailure _ _ _, value => some (runA 0 value)
  | _, _ => none

/-- The pinned `contE`. -/
def armEPinned : Prim -> MiniCause -> Option Prim
  | .onFailure _ onCause, cause => some (runE onCause cause)
  | .onSuccessAndFailure _ _ onCause, cause => some (runE onCause cause)
  | _, _ => none

/-- E4-RUN-CE-017: two `flatMap` frames differing only in their stored
continuation name must behave differently. A prototype-level `contA` collapses
them. -/
theorem arms_are_assigned_per_instance :
    armAPinned (Prim.onSuccess (Prim.success 0) 1) 5 ≠
        armAPinned (Prim.onSuccess (Prim.success 0) 2) 5 /\
      armAPrototype (Prim.onSuccess (Prim.success 0) 1) 5 =
        armAPrototype (Prim.onSuccess (Prim.success 0) 2) 5 := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-017: `OnSuccess` answers `contA` only, `OnFailure` answers `contE`
only, and `OnSuccessAndFailure` answers both. -/
theorem the_three_frames_answer_different_arms :
    arms (Prim.onSuccess (Prim.success 0) 1) = [Arm.contA] /\
      arms (Prim.onFailure (Prim.success 0) 1) = [Arm.contE] /\
        arms (Prim.onSuccessAndFailure (Prim.success 0) 1 2) = [Arm.contA, Arm.contE] /\
          (armAPinned (Prim.onFailure (Prim.success 0) 1) 5 = none /\
            armEPinned (Prim.onSuccess (Prim.success 0) 1) [7] = none) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## E4-RUN-CE-018 — an Exit yielded by a generator is folded inline -/

/-- What a generator step produces after its maximal run of inline `Success`
exits: the pinned model supplies the run and the outcome as first-order data. -/
inductive IterStep
  | done (value : Nat)
  | halt (cause : MiniCause)
  | resume (next : Prim) (continueAs : Nat)
  deriving DecidableEq, Repr

/-- Generator `0` yields two `Success` exits inline and then finishes. -/
def iterNext : Nat -> Nat -> List Nat × IterStep
  | 0, value => ([value + 1, value + 2], .done (value + 3))
  | _, value => ([], .done value)

/-- The pinned `Iterator` arm: the inline run never touches the stack, so the
whole fold is one machine step. -/
def iteratorArmPinned (generator cursor : Nat) : Prim × List Prim × Nat :=
  match (iterNext generator cursor).snd with
  | .done value => (.success value, [], 1)
  | .halt cause => (.failure cause, [], 1)
  | .resume next continueAs => (next, [Prim.iterator continueAs cursor], 1)

/-- E4-RUN-CE-018's rejected arm: each inline `Success` exit is pushed back
through the stack like any other effect, so the fold costs one machine step and
one `getCont` per folded value. -/
def iteratorArmThroughStack (generator cursor : Nat) : Prim × List Prim × Nat :=
  match (iterNext generator cursor).snd with
  | .done value => (.success value, [], (iterNext generator cursor).fst.length + 1)
  | .halt cause => (.failure cause, [], (iterNext generator cursor).fst.length + 1)
  | .resume next continueAs =>
    (next, [Prim.iterator continueAs cursor], (iterNext generator cursor).fst.length + 1)

/-- E4-RUN-CE-018: the generator folds two `Success` exits inline, so the pinned
arm reaches its result in a single step while a variant that routes each folded
exit through the stack takes three. The count is observable because every
`getCont` is a checkpoint at which a deferred interrupt is noticed. -/
theorem iterator_folds_exits_inline :
    (iteratorArmPinned 0 5).snd.snd = 1 /\
      (iteratorArmThroughStack 0 5).snd.snd = 3 /\
        (iteratorArmPinned 0 5).fst = (iteratorArmThroughStack 0 5).fst := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-018: the frame is pushed only for a real effect. A generator that
finishes, or that yields a `Failure` exit, leaves the stack alone. -/
theorem iterator_pushes_only_for_a_real_effect :
    (iteratorArmPinned 0 5).snd.fst = [] /\
      (iteratorArmPinned 1 5).snd.fst = [] := by
  refine ⟨by decide, by decide⟩

/-! ## E4-RUN-CE-019 — While re-tests through contA -/

/-- The loop predicate: run while the cursor is below `2`. -/
def loopTest (_loop : Nat) (cursor : Nat) : Bool := decide (cursor < 2)

/-- The cursor step reads the stored cursor and the body's answer, as rc.112's
`step(value)` reads the closure it mutates. -/
def loopStep (_loop : Nat) (cursor : Nat) (_answer : Nat) : Nat := cursor + 1

def loopBody (_loop : Nat) (cursor : Nat) : Prim := .success cursor

/-- The pinned `While` arm: step the stored cursor with the body's answer,
re-test, and only then push and run the body again. -/
def whileArmPinned (loop cursor answer : Nat) : Prim × List Prim :=
  let stepped := loopStep loop cursor answer
  if loopTest loop stepped = true then (loopBody loop stepped, [Prim.whileLoop loop stepped])
  else (.success 0, [])

/-- E4-RUN-CE-019's rejected arm: step and run the body again without re-testing,
because the predicate was already checked by `evaluate`. -/
def whileArmNoRetest (loop cursor answer : Nat) : Prim × List Prim :=
  let stepped := loopStep loop cursor answer
  (loopBody loop stepped, [Prim.whileLoop loop stepped])

/-- E4-RUN-CE-019: at the cursor where the predicate goes false the pinned arm
stops and the rejected arm pushes the frame again, so the loop never ends. -/
theorem while_retests_through_contA :
    whileArmPinned 0 1 9 = (Prim.success 0, []) /\
      whileArmNoRetest 0 1 9 = (Prim.success 2, [Prim.whileLoop 0 2]) := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-019: below the bound both agree, so the difference is the re-test
and not the step. -/
theorem while_steps_before_it_retests :
    whileArmPinned 0 0 9 = whileArmNoRetest 0 0 9 := by
  decide

/-! ## E4-RUN-CE-020 — an empty stack yields the Exit -/

/-- The pinned step of a produced value with nothing left to pop. -/
def yieldPinned (fiber : Fiber) (produced : MiniExit) : Option MiniExit :=
  match (getCont ensurePinned Arm.contA false fiber).fst with
  | .empty => some produced
  | _ => none

/-- E4-RUN-CE-020's rejected step: an empty stack is treated as a defect, or the
produced value is dropped. -/
def yieldDropped (fiber : Fiber) (_produced : MiniExit) : Option MiniExit :=
  match (getCont ensurePinned Arm.contA false fiber).fst with
  | .empty => some (MiniExit.failure [0])
  | _ => none

def emptyFiber : Fiber :=
  { current := .success 5, stack := [], interruptible := true, pending := none,
    deferred := false }

/-- E4-RUN-CE-020: with an empty stack the fiber yields the Exit it produced.
Replacing it with a defect, or with any other exit, loses the result. -/
theorem empty_stack_yields_the_exit :
    yieldPinned emptyFiber (MiniExit.success 5) = some (MiniExit.success 5) /\
      yieldDropped emptyFiber (MiniExit.success 5) = some (MiniExit.failure [0]) := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-020: a failure with nothing to catch it is yielded unchanged. -/
theorem empty_stack_yields_a_failure_unchanged :
    yieldPinned { emptyFiber with current := .failure [7] } (MiniExit.failure [7]) =
      some (MiniExit.failure [7]) := by
  decide

/-! ## E4-RUN-CE-021 — the two foreign boundaries -/

/-- The raw `FiberImpl` rc.112 hands to `withFiber`. It carries fields this
packet does not model: the observer list, the child set, and the dispatcher. -/
structure HostFiber where
  modelled : Fiber
  observers : Nat
  children : Nat
  deriving DecidableEq, Repr

/-- Everything an Effect4 interpretation of `WithFiber` may read. -/
def project (host : HostFiber) : Fiber := host.modelled

/-- Two host fibers that agree on the five modelled fields and differ in the
observer list, exactly the distinction `withFiber` exposes and this model does
not. -/
def hostLeft : HostFiber := { modelled := emptyFiber, observers := 0, children := 0 }

def hostRight : HostFiber := { modelled := emptyFiber, observers := 1, children := 2 }

/-- E4-RUN-CE-021: any Effect4 interpretation of `WithFiber` is a function of the
modelled state, so it cannot distinguish two raw `FiberImpl` objects that agree
there. The distinction is refused, not modelled. -/
theorem with_fiber_cannot_see_the_raw_fiber :
    hostLeft ≠ hostRight /\ project hostLeft = project hostRight /\
      forall (interpret : Fiber -> Prim), interpret (project hostLeft) =
        interpret (project hostRight) := by
  refine ⟨by decide, by decide, fun interpret => by rw [show project hostLeft =
    project hostRight from by decide]⟩

/-- A host `Error`: the payload Effect4 admits, plus the message and stack that
`YieldableError` inherits from `globalThis.Error`. -/
structure HostError where
  payload : Nat
  message : String
  stack : String
  deriving DecidableEq, Repr

def payloadOf (host : HostError) : Nat := host.payload

def errorLeft : HostError := { payload := 7, message := "a", stack := "x" }

def errorRight : HostError := { payload := 7, message := "b", stack := "y" }

/-- E4-RUN-CE-021: `YieldableError`'s `evaluate` is `exitFail(this)`, so the
failing value *is* the host `Error` object. Effect4 admits only the payload, so
two host errors with equal payloads and different messages and stacks are one
Effect4 cause. The host class identity is refused, not modelled. -/
theorem yieldable_error_cannot_see_the_host_class :
    errorLeft ≠ errorRight /\ payloadOf errorLeft = payloadOf errorRight /\
      forall (embed : Nat -> MiniCause), embed (payloadOf errorLeft) =
        embed (payloadOf errorRight) := by
  refine ⟨by decide, by decide, fun embed => by rw [show payloadOf errorLeft =
    payloadOf errorRight from by decide]⟩

/-- E4-RUN-CE-021: the behaviour behind both boundaries is still modelled — a
`YieldableError` evaluates to the failure carrying its payload. Only the host
object identity is refused. -/
theorem yieldable_error_evaluates_to_its_own_failure :
    (fun (payload : Nat) => Prim.failure [payload]) 7 = Prim.failure [7] := by
  decide

/-! ## E4-RUN-CE-027 — a generator's progress is not a function of its name and the last answer

Found on 2026-09-04 by writing a two-`yield*` `Effect.gen` as `Effect4/Syntax/Eff.lean` data
(`docs/research/2026-09-04-eff-compile.md` §0). rc.112's `Iterator[contA]` calls
`this[args].next(value)` on a generator *object*, which advances
(`internal/effect.ts:1362-1377`). The arm the frames pinned pushed the frame back with the
name the generator started with, so the second answer resumed the first yield: no program
with two yields was expressible, and no battery had ever run one. -/

/-- A generator with two yields: name `10` yields `1` and advances to `11`, `11` yields `2`
and advances to `12`, and `12` finishes with the answer it is given. -/
def twoYields : Nat -> Nat -> List Nat × IterStep
  | 10, _ => ([], .resume (.success 1) 11)
  | 11, _ => ([], .resume (.success 2) 12)
  | _, value => ([], .done value)

/-- The rejected arm: the frame pushed back keeps the name the generator started with. -/
def iteratorArmSameName (generator cursor : Nat) : Prim × List Prim :=
  match (twoYields generator cursor).snd with
  | .done value => (.success value, [])
  | .halt cause => (.failure cause, [])
  | .resume next _ => (next, [Prim.iterator generator cursor])

/-- The corrected arm: the frame pushed back carries the advanced generator. -/
def iteratorArmAdvancing (generator cursor : Nat) : Prim × List Prim :=
  match (twoYields generator cursor).snd with
  | .done value => (.success value, [])
  | .halt cause => (.failure cause, [])
  | .resume next continueAs => (next, [Prim.iterator continueAs cursor])

/-- The generator name of the frame an arm pushed back, if it pushed one. -/
def pushedGenerator : Prim × List Prim -> Option Nat
  | (_, [Prim.iterator generator _]) => some generator
  | _ => none

/-- E4-RUN-CE-027: the rejected arm pushes back name `10` after the first yield, so the
second answer is delivered to `10` again and yields the first effect a second time. -/
theorem same_name_reenters_the_first_yield :
    pushedGenerator (iteratorArmSameName 10 0) = some 10 /\
      (iteratorArmSameName 10 0).fst = Prim.success 1 /\
        (iteratorArmSameName 10 5).fst = Prim.success 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- E4-RUN-CE-027: the corrected arm pushes back `11`, whose answer yields the second
effect and pushes back `12`, which finishes with the answer it is given. -/
theorem advanced_name_reaches_done :
    pushedGenerator (iteratorArmAdvancing 10 0) = some 11 /\
      (iteratorArmAdvancing 11 5).fst = Prim.success 2 /\
        pushedGenerator (iteratorArmAdvancing 11 5) = some 12 /\
          iteratorArmAdvancing 12 7 = (Prim.success 7, []) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## E4-RUN-CE-028 — `While`'s step reads the closure cursor, not the answer alone

Found the same day (`docs/research/2026-09-04-eff-compile.md` §4 G3). rc.112's
`While[contA](value)` runs `step(value)` on a closure that holds the cursor
(`internal/effect.ts:4624-4645`); the arm the frames pinned stepped from the body's answer
alone and dropped the stored cursor, so a loop whose step counts (`i++`) could not be
written. -/

/-- The body of the counting loop answers a constant. -/
def constantAnswer : Nat := 0

/-- One iteration under the rejected signature, `step : answer -> cursor`: the next cursor
is a function of the answer alone, so the stored cursor is unread. -/
def iterateAnswerOnly (_cursor : Nat) : Nat := constantAnswer + 1

/-- One iteration under the corrected signature, `step : cursor -> answer -> cursor`. -/
def iterateWithCursor (cursor : Nat) : Nat := loopStep 0 cursor constantAnswer

/-- E4-RUN-CE-028: under the rejected signature the cursor after two iterations is the
cursor after one, whatever it was — the loop cannot count. -/
theorem answer_only_step_cannot_count :
    iterateAnswerOnly (iterateAnswerOnly 0) = iterateAnswerOnly 0 /\
      iterateAnswerOnly 5 = iterateAnswerOnly 0 := by
  refine ⟨by decide, by decide⟩

/-- E4-RUN-CE-028: under the corrected signature the loop counts. -/
theorem cursor_step_counts :
    iterateWithCursor 0 = 1 /\ iterateWithCursor (iterateWithCursor 0) = 2 := by
  refine ⟨by decide, by decide⟩

end Effect4Test.Counterexamples.Runtime.Frames
