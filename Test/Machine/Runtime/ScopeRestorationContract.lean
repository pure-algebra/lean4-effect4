import Effect4.Machine.ScopeMachine
import Effect4.Machine.Frames
import Effect4.Machine.ScopeRestoration
import Test.Counterexamples.Machine.Runtime.ScopeRestorationBoundary

set_option synthInstance.maxSize 2048

/-!
Frozen ScopeRestoration surface and finite controls.
The independently executable boundary file owns old-meaning witnesses.
No old assertion or semantic owner is changed by this packet.
-/
namespace Test.Runtime.ScopeRestorationContract
open Effect4

-- BEGIN SURFACE
section Surface
universe u v
variable {κ φ ν τ : Type u} {β : Type v} {ε δ ι α σ : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
example : PrimInterp ν τ β ε δ ι α → ScopeMachine.State κ φ β ε δ ι α →
    FrameFiber ν τ β ε δ ι α →
    Option (FrameStep ν τ β ε δ ι α × List (FrameEvent ν τ β ε δ ι α)) :=
  ScopeRestoration.resumeClosedScope

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α)
    (unfinished : machine.phase ≠ .complete) :
    ScopeRestoration.resumeClosedScope interp machine fiber = none :=
  ScopeRestoration.resumeClosedScope_unfinished interp machine fiber unfinished

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α) (world : σ) :
    (let actual := ScopeMachine.runState handler (ScopeMachine.bound scope)
       (ScopeMachine.start scope original) world
     (ScopeRestoration.resumeClosedScope interp actual.1 fiber, actual.2)) =
    (let completed := (Scope.closeExitsM handler scope original).run world
     let cleanup := match completed.1 with
       | [] => Exit.void
       | [only] => only
       | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)
     (some (FrameFiber.step interp
       { fiber with current := Prim.ofExit (Exit.restoreAfterFinalizer original cleanup) }),
      completed.2)) :=
  ScopeRestoration.resumeClosedScope_complete interp handler scope original fiber world

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (value : β) (pending : Cause ε δ ι α)
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    ScopeRestoration.resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
    some (.running ⟨.failure pending, rest, true, some pending, false⟩,
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
       .substituted pending]) :=
  ScopeRestoration.resumeClosedScope_success_pending interp machine current rest value pending completed

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (failed pending : Cause ε δ ι α)
    (completed : ScopeMachine.restore? machine = some (.failure failed)) :
    ScopeRestoration.resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
    (let continued := FrameFiber.step interp
       ⟨.failure failed, rest, true, some pending, false⟩
     some (continued.1,
       [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
        .substituted pending] ++ continued.2)) :=
  ScopeRestoration.resumeClosedScope_failure_pending interp machine current rest failed pending completed

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (value : β)
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    ScopeRestoration.resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, none, false⟩ =
    (let continued := FrameFiber.step interp ⟨.success value, rest, true, none, false⟩
     some (continued.1,
       [.popped (.setInterruptible true), .ranContAll (.setInterruptible true)]
        ++ continued.2)) :=
  ScopeRestoration.resumeClosedScope_success_no_pending interp machine current rest value completed

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α)
    (masked : fiber.interruptible = false) :
    ScopeRestoration.resumeClosedScope interp machine fiber.uninterruptible =
      ScopeRestoration.resumeClosedScope interp machine fiber :=
  ScopeRestoration.resumeClosedScope_already_masked interp machine fiber masked

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current body : Prim ν τ β ε δ ι α)
    (continuation : ν) (rest : List (Prim ν τ β ε δ ι α))
    (value : β) (pending : Option (Cause ε δ ι α))
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    ScopeRestoration.resumeClosedScope interp machine
      ⟨current, .onSuccess body continuation :: rest, false, pending, false⟩ =
    some (.running ⟨interp.contA continuation value, rest, false, pending, false⟩,
      [.popped (.onSuccess body continuation)]) :=
  ScopeRestoration.resumeClosedScope_masked_continuation interp machine current body continuation rest value pending completed

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α)
    (failed cleanup : Cause ε δ ι α)
    (original : machine.original = .failure failed)
    (completed : ScopeMachine.result? machine = some (.failure cleanup)) :
    ScopeRestoration.resumeClosedScope interp machine fiber =
    some (FrameFiber.step interp
      { fiber with current := .failure (Cause.combine failed cleanup) }) :=
  ScopeRestoration.resumeClosedScope_failure_cleanup interp machine fiber failed cleanup original completed

example
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (value : β) (cleanup pending : Cause ε δ ι α)
    (original : machine.original = .success value)
    (completed : ScopeMachine.result? machine = some (.failure cleanup)) :
    ScopeRestoration.resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
    (let continued := FrameFiber.step interp
       ⟨.failure cleanup, rest, true, some pending, false⟩
     some (continued.1,
       [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
        .substituted pending] ++ continued.2)) :=
  ScopeRestoration.resumeClosedScope_success_cleanup_failure interp machine current rest value cleanup pending original completed
end Surface
-- END SURFACE

open Test.Counterexamples.Runtime.ScopeRestorationBoundary

-- BEGIN BEHAVIOR
#guard ScopeRestoration.resumeClosedScope interp successClose.1 successFiber =
  some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)
#guard ScopeRestoration.resumeClosedScope interp successClose.1 {successFiber with interruptedCause := none} =
  some (.finished (.success 5), noMaskEvents ++ [.yielded (.success 5)])
#guard ScopeRestoration.resumeClosedScope interp (ScopeMachine.start scope (.success 5)) successFiber = none
#guard ScopeRestoration.resumeClosedScope interp (ScopeMachine.advance (ScopeMachine.start scope (.success 5))) successFiber = none
#guard ScopeRestoration.resumeClosedScope interp successClose.1
    ⟨.success 999, [.onSuccess (.success 0) 7, .setInterruptible true], false, some pending, false⟩ =
  some (.running ⟨.success 12, [.setInterruptible true], false, some pending, false⟩,
    [.popped (.onSuccess (.success 0) 7)])
#guard ScopeRestoration.resumeClosedScope interp failedClose.1 successFiber =
  some (.finished (.failure failureCause), maskEvents ++ [.yielded (.failure failureCause)])
#guard ScopeRestoration.resumeClosedScope interp failedClose.1
    { successFiber with stack := [.setInterruptible true, .onFailure (.success 0) 77] } =
  some (.finished (.failure failureCause), maskEvents ++
    [.popped (.onFailure (.success 0) 77), .yielded (.failure failureCause)])
#guard ScopeRestoration.resumeClosedScope interp failedClose.1
    { successFiber with stack := [.setInterruptible true, .onExit (.success 0) 8 false] } =
  some (.running ⟨.failure (Cause.combine failureCause (Cause.die 8)),
    [.setInterruptible true], false, some pending, false⟩,
    maskEvents ++ [.popped (.onExit (.success 0) 8 false),
      .ranContAll (.onExit (.success 0) 8 false), .ranFinalizer 8 (.failure failureCause)])
#guard ScopeRestoration.resumeClosedScope interp singleEmpty.1 successFiber =
  some (.finished (.failure ⟨[]⟩), maskEvents ++ [.yielded (.failure ⟨[]⟩)])
#guard ScopeRestoration.resumeClosedScope interp manyEmpty.1 successFiber =
  some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)

def pause (budget : Nat) := ScopeMachine.runState (handler (fun _ => Exit.void)) budget
  (ScopeMachine.start scope (.success 5)) (40,[])
#guard ScopeRestoration.resumeClosedScope interp (pause 0).1 successFiber = none
#guard ScopeRestoration.resumeClosedScope interp (pause 1).1 successFiber = none
#guard ScopeRestoration.resumeClosedScope interp (pause 2).1 successFiber = none
#guard ScopeRestoration.resumeClosedScope interp (pause 3).1 successFiber = none
#guard ScopeRestoration.resumeClosedScope interp (pause 4).1 successFiber = none
#guard (pause 2).2 = (41,[(2,.success 5)])
#guard (pause 4).2 = (42,[(2,.success 5),(1,.success 5)])
#guard (pause 4).1.phase = .ready
#guard (pause 4).1.pending = []
#guard (pause 4).1.captured.map Prod.fst = [2,1]
#guard (ScopeRestoration.resumeClosedScope interp (pause 4).1 successFiber,
    (pause 4).1, (pause 4).2) = (none, (pause 4).1, (pause 4).2)
#guard ScopeRestoration.resumeClosedScope interp (pause 5).1 successFiber =
  some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)
#guard ScopeRestoration.resumeClosedScope interp successClose.1
    {successFiber with deferredInterrupt := true} =
  some (.running ⟨.failure pending, [.setInterruptible true], false, some pending, false⟩,
    [.deferred pending])

def bodyFailureClose := runClose scope (.failure before) (fun _ => Exit.void) (40,[])
#guard ScopeRestoration.resumeClosedScope interp bodyFailureClose.1 successFiber =
  some (.finished (.failure before), maskEvents ++ [.yielded (.failure before)])
def bothFailureClose := runClose scope (.failure before)
  (fun n => .failure (Cause.die n)) (40,[])
#guard ScopeRestoration.resumeClosedScope interp bothFailureClose.1 successFiber =
  some (.finished (.failure (Cause.combine before failureCause)),
    maskEvents ++ [.yielded (.failure (Cause.combine before failureCause))])
#guard bothFailureClose.2 = (42,[(2,.failure before),(1,.failure before)])
def duplicateClose := runClose scope (.failure (Cause.die 9))
  (fun _ => .failure (Cause.die 9)) (40,[])
#guard ScopeMachine.journal duplicateClose.1 =
  [Reason.die 9 ReasonAnnotations.empty, Reason.die 9 ReasonAnnotations.empty]
#guard ScopeRestoration.resumeClosedScope interp duplicateClose.1 successFiber =
  some (.finished (.failure (Cause.die 9)), maskEvents ++ [.yielded (.failure (Cause.die 9))])
#guard ScopeRestoration.resumeClosedScope interp successClose.1
    {successFiber with interruptedCause := some (Cause.combine pending (Cause.interrupt (some 102)))} =
  some (.running ⟨.failure (Cause.combine pending (Cause.interrupt (some 102))), [], true,
    some (Cause.combine pending (Cause.interrupt (some 102))), false⟩,
    [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
      .substituted (Cause.combine pending (Cause.interrupt (some 102)))])
-- END BEHAVIOR
end Test.Runtime.ScopeRestorationContract
