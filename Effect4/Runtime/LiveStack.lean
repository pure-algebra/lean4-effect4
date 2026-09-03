import Effect4.Runtime.Runtime

/-!
# Live continuation-stack traversal

The independent packet in `test/contracts/live-stack.contract.md` owns the
additive public surface. The primitive, fiber, result and event carriers
remain owned by `Runtime.lean`. Every recursive call consumes the actual
post-hook stack; the existing detached traversal occurs only in proofs.
-/

set_option autoImplicit false

namespace Effect4.FrameFiber
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

private def prefixPop (frame : Prim ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (result : FramePop ν σ β ε δ ι α) : FramePop ν σ β ε δ ι α :=
  { result with popped := frame :: result.popped, events := events ++ result.events }

/-- Only an answering, masking OnExit can push in this profile. -/
private theorem continuing_stack (frame : Prim ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (fiber : FrameFiber ν σ β ε δ ι α)
    (continues : frame.answerOf demand (frame.ensure fiber).snd = none ∨
      (skip && (frame.ensure fiber).fst.interrupted) = true) :
    (frame.ensure fiber).fst.stack = fiber.stack := by
  cases frame <;> try rfl
  case onExit body name flag =>
    cases demand <;> cases mask : fiber.interruptible <;> cases flag <;>
      simp [Prim.ensure, Prim.answerOf, Prim.hasArm, Prim.arms,
        FrameFiber.interrupted, mask] at continues ⊢
  case setInterruptible flag =>
    cases cause : fiber.interruptedCause <;> cases flag <;>
      simp [Prim.ensure, cause]

/-- Consume the actual stack left by each hook, testing interruption after
that hook. The decreasing argument is specific to the current Prim profile.
census: rule.frames-are-primitives -/
def popLive (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool) :
    FramePop ν σ β ε δ ι α :=
  match _stackEq : self.stack with
  | [] => ⟨.empty, [], [], self⟩
  | frame :: rest =>
    let after := frame.ensure { self with stack := rest }
    match _answerEq : frame.answerOf demand after.snd with
    | none => prefixPop frame (frame.passEvents after.snd) (popLive after.fst demand skip)
    | some answer =>
      if _skipping : skip && after.fst.interrupted then
        prefixPop frame (frame.passEvents after.snd) (popLive after.fst demand skip)
      else ⟨answer, [frame], frame.passEvents after.snd, after.fst⟩
termination_by self.stack.length
decreasing_by
  · have kept := continuing_stack frame demand false { self with stack := rest } (Or.inl _answerEq)
    simp [kept, _stackEq]
  · have kept := continuing_stack frame demand skip { self with stack := rest } (Or.inr _skipping)
    simp [kept, _stackEq]

/-- Observe deferred interruption before the outer loop decides whether to
discard its answer. Even a discarded answer retains its event.
census: checkpoint.getcont-deferred -/
def getContLive (self : FrameFiber ν σ β ε δ ι α) (demand : Arm)
    (skipInterrupted : Bool) : FramePop ν σ β ε δ ι α :=
  let cleared := { self with deferredInterrupt := false }
  if self.deferredInterrupt then
    if skipInterrupted && self.interrupted then
      let next := cleared.popLive demand skipInterrupted
      { next with events := .deferred self.pendingCause :: next.events }
    else ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause], cleared⟩
  else cleared.popLive demand skipInterrupted

private def appendStack (fiber : FrameFiber ν σ β ε δ ι α)
    (suffix : List (Prim ν σ β ε δ ι α)) : FrameFiber ν σ β ε δ ι α :=
  { fiber with stack := fiber.stack ++ suffix }

private theorem interrupted_appendStack (fiber : FrameFiber ν σ β ε δ ι α)
    (suffix : List (Prim ν σ β ε δ ι α)) :
    (appendStack fiber suffix).interrupted = fiber.interrupted := rfl

private theorem ensure_appendStack (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (suffix : List (Prim ν σ β ε δ ι α)) :
    frame.ensure (appendStack fiber suffix) =
      (appendStack (frame.ensure fiber).fst suffix, (frame.ensure fiber).snd) := by
  cases frame <;> try rfl
  case onExit body name flag =>
    cases mask : fiber.interruptible <;> cases flag <;>
      simp [Prim.ensure, appendStack, mask]
  case setInterruptible flag =>
    cases cause : fiber.interruptedCause <;> cases flag <;>
      simp [Prim.ensure, appendStack, cause]

private theorem clear_empty_stack (fiber : FrameFiber ν σ β ε δ ι α)
    (empty : fiber.stack = []) : { fiber with stack := [] } = fiber := by
  cases fiber
  cases empty
  rfl

private theorem popLive_stack_eq (demand : Arm) (skip : Bool)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    popLive { fiber with stack := stack } demand skip =
      popFrom demand skip stack { fiber with stack := [] } := by
  induction stack generalizing fiber with
  | nil => rw [popLive]; rfl
  | cons frame rest ih =>
    let detached : FrameFiber ν σ β ε δ ι α := { fiber with stack := [] }
    have hook : frame.ensure { fiber with stack := rest } =
        (appendStack (frame.ensure detached).fst rest, (frame.ensure detached).snd) := by
      simpa [appendStack, detached] using ensure_appendStack frame detached rest
    rw [popLive]
    dsimp only
    rw [hook]
    cases answer : frame.answerOf demand (frame.ensure detached).snd with
    | none =>
      have empty : (frame.ensure detached).fst.stack = [] := by
        rw [continuing_stack frame demand skip detached (Or.inl answer)]
      have clean := clear_empty_stack (frame.ensure detached).fst empty
      have tail := ih (frame.ensure detached).fst
      simp only [clean] at tail
      simp only [appendStack, empty, List.nil_append]
      rw [tail]
      simp [popFrom, answer, detached, prefixPop]
    | some selected =>
      cases discard : skip && (frame.ensure detached).fst.interrupted with
      | false =>
        simp only [interrupted_appendStack, discard, Bool.false_eq_true, ↓reduceDIte]
        change _ = popFrom demand skip (frame :: rest) detached
        simp [popFrom, answer, discard, appendStack]
      | true =>
        simp only [interrupted_appendStack, discard, ↓reduceDIte]
        have empty : (frame.ensure detached).fst.stack = [] := by
          rw [continuing_stack frame demand skip detached (Or.inr discard)]
        have clean := clear_empty_stack (frame.ensure detached).fst empty
        have tail := ih (frame.ensure detached).fst
        simp only [clean] at tail
        simp only [appendStack, empty, List.nil_append]
        rw [tail]
        change _ = popFrom demand skip (frame :: rest) detached
        simp [popFrom, answer, discard, prefixPop]

/-- Whole-result equality on every existing primitive, arm and skip flag;
this does not admit AsyncFinalizer. census: rule.frames-are-primitives -/
theorem popLive_eq_popFrom (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) :
    self.popLive demand skip = popFrom demand skip self.stack { self with stack := [] } :=
  popLive_stack_eq demand skip self.stack self

/-- The legacy entry agrees when there is no deferred observation to lose.
census: checkpoint.getcont-deferred -/
theorem getContLive_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = false) :
    self.getContLive demand skip = self.getCont demand skip := by
  simp [getContLive, getCont, hdeferred, popLive_eq_popFrom]

/-- A single, non-skipping inner call agrees in every representable state.
census: checkpoint.getcont-deferred -/
theorem getContLive_false_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) : self.getContLive demand false = self.getCont demand false := by
  simp [getContLive, getCont, popLive_eq_popFrom]

/-- Keep the full deferred result whenever post-entry interruption is not
being skipped. census: checkpoint.getcont-deferred -/
theorem getContLive_deferred_kept (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = true)
    (hkeep : (skip && self.interrupted) = false) :
    self.getContLive demand skip =
      ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause],
        { self with deferredInterrupt := false }⟩ := by
  simp [getContLive, hdeferred, hkeep]

/-- Discarding the deferred answer does not discard its chronological event.
census: checkpoint.getcont-deferred -/
theorem getContLive_deferred_discarded (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (hdeferred : self.deferredInterrupt = true)
    (hinterrupted : self.interrupted = true) :
    self.getContLive demand true =
      let next := ({ self with deferredInterrupt := false }).popLive demand true
      { next with events := .deferred self.pendingCause :: next.events } := by
  simp [getContLive, hdeferred, hinterrupted]

private def skipPop (first : FramePop ν σ β ε δ ι α) (demand : Arm) :
    FramePop ν σ β ε δ ι α :=
  match first.answer with
  | .empty => first
  | _ =>
    if first.fiber.interrupted then
      let next := first.fiber.popLive demand true
      { next with popped := first.popped ++ next.popped,
                  events := first.events ++ next.events }
    else first

private theorem skipPop_prefix (frame : Prim ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (result : FramePop ν σ β ε δ ι α) (demand : Arm) :
    skipPop (prefixPop frame events result) demand =
      prefixPop frame events (skipPop result demand) := by
  cases flag : result.fiber.interrupted <;> cases answer : result.answer <;>
    simp [skipPop, prefixPop, flag, answer, List.append_assoc]

private theorem answer_nonempty (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α)) (answer : ContAnswer ν σ β ε δ ι α)
    (selected : frame.answerOf demand replacement = some answer) : answer ≠ .empty := by
  intro empty
  subst answer
  cases replacement <;> cases arm : frame.hasArm demand <;>
    simp [Prim.answerOf, arm] at selected

private theorem with_same_stack (fiber : FrameFiber ν σ β ε δ ι α)
    (stack : List (Prim ν σ β ε δ ι α)) (same : fiber.stack = stack) :
    { fiber with stack := stack } = fiber := by
  cases fiber
  cases same
  rfl

private theorem popLive_stack_while (demand : Arm)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    popLive { fiber with stack := stack } demand true =
      skipPop (popLive { fiber with stack := stack } demand false) demand := by
  induction stack generalizing fiber with
  | nil => simp [popLive, skipPop]
  | cons frame rest ih =>
    conv => lhs; rw [popLive]
    conv => rhs; arg 1; rw [popLive]
    dsimp only
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceDIte, Bool.true_and]
    let after := frame.ensure { fiber with stack := rest }
    change (match _selected : frame.answerOf demand after.snd with
      | none => prefixPop frame (frame.passEvents after.snd) (after.fst.popLive demand true)
      | some answer => if _flag : after.fst.interrupted then
          prefixPop frame (frame.passEvents after.snd) (after.fst.popLive demand true)
        else ⟨answer, [frame], frame.passEvents after.snd, after.fst⟩) =
      skipPop (match _selected : frame.answerOf demand after.snd with
        | none => prefixPop frame (frame.passEvents after.snd) (after.fst.popLive demand false)
        | some answer => ⟨answer, [frame], frame.passEvents after.snd, after.fst⟩) demand
    cases selected : frame.answerOf demand after.snd with
    | none =>
      have kept : after.fst.stack = rest :=
        continuing_stack frame demand false { fiber with stack := rest } (Or.inl selected)
      have tail := ih after.fst
      rw [with_same_stack after.fst rest kept] at tail
      simpa only [skipPop_prefix] using congrArg
        (prefixPop frame (frame.passEvents after.snd)) tail
    | some answer =>
      have nonempty := answer_nonempty frame demand after.snd answer selected
      cases flag : after.fst.interrupted <;> cases answer <;>
        simp_all [skipPop, prefixPop]

private theorem ensure_deferred (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) :
    (frame.ensure fiber).fst.deferredInterrupt = fiber.deferredInterrupt := by
  cases frame <;> try rfl
  case onExit body name flag =>
    cases mask : fiber.interruptible <;> cases flag <;> simp [Prim.ensure, mask]
  case setInterruptible flag =>
    cases cause : fiber.interruptedCause <;> cases flag <;> simp [Prim.ensure, cause]

private theorem popFrom_deferred (demand : Arm) (skip : Bool)
    (stack : List (Prim ν σ β ε δ ι α)) (fiber : FrameFiber ν σ β ε δ ι α) :
    (popFrom demand skip stack fiber).fiber.deferredInterrupt = fiber.deferredInterrupt := by
  induction stack generalizing fiber with
  | nil => rfl
  | cons frame rest ih =>
    simp only [popFrom]
    split
    · split <;> simp [ih, ensure_deferred]
    · simp [ih, ensure_deferred]

private theorem popLive_deferred (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) :
    (self.popLive demand skip).fiber.deferredInterrupt = self.deferredInterrupt := by
  rw [popLive_eq_popFrom, popFrom_deferred]

private theorem cleared_eq (self : FrameFiber ν σ β ε δ ι α)
    (hdeferred : self.deferredInterrupt = false) :
    { self with deferredInterrupt := false } = self := by
  cases self
  cases hdeferred
  rfl

private theorem getContLive_plain (self : FrameFiber ν σ β ε δ ι α)
    (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = false) :
    self.getContLive demand skip = self.popLive demand skip := by
  simp [getContLive, hdeferred, cleared_eq self hdeferred]

private theorem cleared_interrupted (self : FrameFiber ν σ β ε δ ι α) :
    ({ self with deferredInterrupt := false }).interrupted = self.interrupted := rfl

/-- One inner call followed by the source's conditional outer failure loop,
retaining all popped frames and chronological events.
census: checkpoint.exit-failcause-skip -/
theorem getContLive_while (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) :
    self.getContLive demand true =
      let first := self.getContLive demand false
      match first.answer with
      | .empty => first
      | _ =>
        if first.fiber.interrupted then
          let next := first.fiber.getContLive demand true
          { next with popped := first.popped ++ next.popped,
                      events := first.events ++ next.events }
        else first := by
  cases delayed : self.deferredInterrupt with
  | false =>
    rw [getContLive_plain self demand true delayed,
        getContLive_plain self demand false delayed]
    have next := getContLive_plain (self.popLive demand false).fiber demand true
      (by rw [popLive_deferred, delayed])
    simp only [next]
    exact popLive_stack_while demand self.stack self
  | true =>
    cases flag : self.interrupted <;>
      simp [getContLive, delayed, cleared_interrupted, flag]

end Effect4.FrameFiber
