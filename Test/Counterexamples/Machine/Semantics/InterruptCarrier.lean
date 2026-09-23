import Effect4.Laws.Program.Typed.Contracts

/-!
E4-SCHED-CE-009: failure delivery must carry the exit explicitly through the pop.
The original counterexample at commit 18373ad showed that changing only the saved
current code did not change the terminal or handler argument. The approved repair
adds `FramePop.carriedCause` and makes each consumer read it. The universal terminal
law below treats the walk as opaque; the local controls distinguish a preempted
catch from an empty stack and a catch entered while masked. Reachable source runs
are checked separately by E4-SCHED-CE-008.
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

/-- Every terminal arm uses the exit returned by the walk, including sanitation. -/
theorem finished_uses_carried_exit (interp : Interp) (frame : Frame)
    (cause : CauseV) (provided : Option ExitV) (result : ExitV)
    (h : (frame.resumeCause interp cause provided).1 = .finished result) :
    result = (frame.getCont .contE true (some cause)).deliveredExit
      (provided.getD (.failure cause)) := by
  unfold FrameFiber.resumeCause at h
  dsimp only at h
  split at h
  · cases h
    rfl
  · cases h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- The proposed current-code carrier already contains the desired failure. -/
def exhausted : Frame :=
  ⟨.failure sanitized, [], true, some sanitized, false⟩

/-- Updating current code alone is ineffective at the terminal consumer. -/
theorem sanitized_current_is_ignored (interp : Interp) :
    (exhausted.resumeCause interp original (some (.failure original))).1 =
      .finished (.failure original) := rfl

/-- The original masked catch state now yields the sanitized failure. -/
def masked (handler : EffName) : Frame :=
  ⟨.failure original,
    [.setInterruptible true, .onFailure (.failure original) handler],
    false, some sanitized, false⟩

theorem masked_catch_returns_sanitized (interp : Interp) (handler : EffName) :
    ((masked handler).step interp).1 = .finished (.failure sanitized) := rfl

/-- With no preempted catch, re-masking leaves the supplied failure unchanged.
The current code is deliberately different: it is not the delivery carrier. -/
def remasked (handler : EffName) : Frame :=
  ⟨.failure sanitized,
    [.setInterruptible false, .onFailure (.failure original) handler],
    true, some sanitized, false⟩

theorem remasked_handler_receives_original (interp : Interp) (handler : EffName) :
    ((remasked handler).resumeCause interp original (some (.failure original))).1 =
      .running ⟨interp.contE handler original, [], false, some sanitized, false⟩ := rfl

/-- A catch skipped before a re-mask changes the next handler's input. -/
def skippedThenRemasked (handler : EffName) : Frame :=
  { remasked handler with
    stack := .onFailure (.failure original) handler :: (remasked handler).stack }

theorem remasked_handler_receives_sanitized (interp : Interp) (handler : EffName) :
    ((skippedThenRemasked handler).resumeCause interp original (some (.failure original))).1 =
      .running ⟨interp.contE handler sanitized, [], false, some sanitized, false⟩ := rfl

#print axioms original_ne_sanitized
#print axioms finished_uses_carried_exit
#print axioms sanitized_current_is_ignored
#print axioms masked_catch_returns_sanitized
#print axioms remasked_handler_receives_original
#print axioms remasked_handler_receives_sanitized
end Test.Counterexamples.InterruptCarrier
