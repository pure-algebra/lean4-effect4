import Effect4.Laws.Program.Typed.Contracts

/-!
E4-SCHED-CE-009: the divergence cannot be confined to the two stack walks.
`FrameFiber.resumeCause` retains its `cause` and `provided` arguments outside
`getCont`. Every terminal result uses that supplied exit, regardless of the
returned fiber's current code. A resumed handler also receives the original
cause. Storing the sanitized failure in `FramePop.fiber.current` therefore
does not implement the packet's rule; its consumers must change as well.

The universal terminal theorem below does not unfold the stack walk. The
remaining equations are local saved-state controls, not reachability claims.
The reachable escape is retained separately as E4-SCHED-CE-008.
-/
set_option autoImplicit false

namespace Test.Counterexamples.InterruptCarrier
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

abbrev Frame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev Interp := PrimInterp EffName EffThunk Val Err Defect FiberId Ann

def original : CauseV := Cause.fail (.tag 42)
def sanitized : CauseV := Cause.interrupt (some ⟨1⟩)

/-- The two required outcomes differ even before considering annotations. -/
theorem original_ne_sanitized : original ≠ sanitized := by
  intro h
  cases h

/-- Every terminal arm reads the arguments captured before the pop. This
proof treats `getCont` as opaque, including every field of its result. -/
theorem finished_uses_supplied_exit (interp : Interp) (frame : Frame)
    (cause : CauseV) (provided : Option ExitV) (result : ExitV)
    (h : (frame.resumeCause interp cause provided).1 = .finished result) :
    result = provided.getD (.failure cause) := by
  unfold FrameFiber.resumeCause at h
  split at h
  · cases h
    rfl
  · cases h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- Neither a changed saved fiber nor a replacement continuation can make
the unchanged consumer finish with the sanitized exit in this step. -/
theorem cannot_finish_sanitized (interp : Interp) (frame : Frame) :
    (frame.resumeCause interp original (some (.failure original))).1 ≠
      .finished (.failure sanitized) := by
  intro h
  have heq := finished_uses_supplied_exit interp frame original
    (some (.failure original)) (.failure sanitized) h
  cases heq

/-- The proposed current-code carrier already contains the desired failure. -/
def exhausted : Frame :=
  ⟨.failure sanitized, [], true, some sanitized, false⟩

/-- Updating current code alone is ineffective at the terminal consumer. -/
theorem sanitized_current_is_ignored (interp : Interp) :
    (exhausted.resumeCause interp original (some (.failure original))).1 =
      .finished (.failure original) := rfl

/-- The original masked catch state reaches the same terminal consumer. -/
def masked (handler : EffName) : Frame :=
  ⟨.failure original,
    [.setInterruptible true, .onFailure (.failure original) handler],
    false, some sanitized, false⟩

theorem masked_catch_returns_original (interp : Interp) (handler : EffName) :
    ((masked handler).step interp).1 = .finished (.failure original) := rfl

/-- After a skipped catch, a later mask may permit another handler to run.
Even if current code carried the sanitized cause, the consumer uses its old argument. -/
def remasked (handler : EffName) : Frame :=
  ⟨.failure sanitized,
    [.setInterruptible false, .onFailure (.failure original) handler],
    true, some sanitized, false⟩

theorem remasked_handler_receives_original (interp : Interp) (handler : EffName) :
    ((remasked handler).resumeCause interp original (some (.failure original))).1 =
      .running ⟨interp.contE handler original, [], false, some sanitized, false⟩ := rfl

#print axioms original_ne_sanitized
#print axioms finished_uses_supplied_exit
#print axioms cannot_finish_sanitized
#print axioms sanitized_current_is_ignored
#print axioms masked_catch_returns_original
#print axioms remasked_handler_receives_original
end Test.Counterexamples.InterruptCarrier
