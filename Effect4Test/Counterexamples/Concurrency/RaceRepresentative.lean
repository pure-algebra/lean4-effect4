import Effect4.Concurrency.Scheduler

/-!
# Race representative counterexamples

These four finite witnesses constrain the binary `raceFirst` packet without
depending on its production implementation.  They reuse the existing fiber,
scheduler, interruption, cleanup, and trace carriers.
-/

namespace Effect4Test.Counterexamples.Concurrency.RaceRepresentative

open Effect4

private def coordinator : FiberId := ⟨0⟩
private def left : FiberId := ⟨1⟩
private def right : FiberId := ⟨2⟩

private def runningFiber (id : FiberId) : FiberState Nat :=
  { id := id
    status := .running
    terminal := none
    mask := .unmasked
    interruptPending := false
    cleanup := .notStarted
    cleanupCount := 0 }

private def doneFiber (id : FiberId) (result : Nat) : FiberState Nat :=
  { id := id
    status := .done
    terminal := some result
    mask := .unmasked
    interruptPending := false
    cleanup := .done
    cleanupCount := 1 }

private def finalizingFiber (id : FiberId) (result : Nat) : FiberState Nat :=
  { id := id
    status := .finalizing
    terminal := some result
    mask := .unmasked
    interruptPending := false
    cleanup := .pending
    cleanupCount := 0 }

/-!
E4-CONC-CE-008: erasing the winner choice maps distinct tie resolutions to
the same scheduler machine.
-/

private def tiedMachine : Machine Nat :=
  { fibers :=
      [runningFiber coordinator, doneFiber left 11, doneFiber right 22]
    trace := [.cleanupFinished left, .cleanupFinished right] }

private def leftTieResolution : Machine Nat × FiberId := (tiedMachine, left)
private def rightTieResolution : Machine Nat × FiberId := (tiedMachine, right)

theorem erased_winner_choice_counterexample :
    leftTieResolution.1 = rightTieResolution.1 /\
      leftTieResolution.2 ≠ rightTieResolution.2 := by
  constructor
  · rfl
  · decide

/-!
E4-CONC-CE-009: first completion and first success disagree on the smallest
two-completion tape.  `false` is the failed completion and `true` the later
successful completion; this is probe data, not a second terminal alphabet.
-/

private def firstCompletion : List Bool -> Option Bool
  | [] => none
  | completion :: _ => some completion

private def firstSuccess : List Bool -> Option Bool
  | [] => none
  | false :: rest => firstSuccess rest
  | true :: _ => some true

theorem first_completion_ne_first_success_counterexample :
    firstCompletion [false, true] = some false /\
      firstSuccess [false, true] = some true /\
      firstCompletion [false, true] ≠ firstSuccess [false, true] := by
  decide

/-!
E4-CONC-CE-010: observing the winner's terminal value does not imply that the
loser has completed cleanup.
-/

private def earlyReturnMachine : Machine Nat :=
  { fibers :=
      [runningFiber coordinator, doneFiber left 11, finalizingFiber right 22]
    trace := [.cleanupFinished left] }

theorem early_return_before_loser_cleanup_counterexample :
    earlyReturnMachine.terminal left = some 11 /\
      earlyReturnMachine.cleanupState right = some .pending /\
      earlyReturnMachine.cleanupCount right = 0 /\
      earlyReturnMachine.trace = [.cleanupFinished left] /\
      right ≠ left := by
  exact ⟨rfl, rfl, rfl, rfl, by decide⟩

/-!
E4-CONC-CE-011: a masked loser with a pending interruption is live.  It is
neither settled nor refused: an explicit unmask decision advances it to
finalization, after which cleanup still remains.
-/

private def maskedLoser : FiberState Nat :=
  { id := right
    status := .running
    terminal := none
    mask := .masked
    interruptPending := true
    cleanup := .notStarted
    cleanupCount := 0 }

private def maskedLoserMachine : Machine Nat :=
  { fibers := [runningFiber coordinator, doneFiber left 11, maskedLoser]
    trace := [.cleanupFinished left] }

private def interruptBoundary : InterruptBoundary Nat := ⟨99⟩

private def maskedExitAfter : Machine Nat :=
  Machine.transition maskedLoserMachine
    { maskedLoser with
      status := .finalizing
      terminal := some interruptBoundary.interrupted
      mask := .unmasked
      interruptPending := false
      cleanup := .pending
      cleanupCount := 0 }
    [.maskExited right, .interruptDelivered right]

theorem masked_loser_is_live_frontier_counterexample :
    maskedLoserMachine.cleanupState right = some .notStarted /\
      maskedLoserMachine.interruptPending right = some true /\
      stepEval interruptBoundary maskedLoserMachine (.exitMask right) =
        .advanced maskedExitAfter /\
      maskedExitAfter.terminal right = some interruptBoundary.interrupted /\
      maskedExitAfter.cleanupState right = some .pending := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms erased_winner_choice_counterexample
#print axioms first_completion_ne_first_success_counterexample
#print axioms early_return_before_loser_cleanup_counterexample
#print axioms masked_loser_is_live_frontier_counterexample

end Effect4Test.Counterexamples.Concurrency.RaceRepresentative
