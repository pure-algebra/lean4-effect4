import Effect4.Runtime.ScopeMachine
import Effect4.Runtime.Runtime

/-!
Independent finite witnesses for E4-RUN-CE-025/026.
The actual ScopeMachine and Runtime owners supply every transition. This file
imports no proposed ScopeRestoration implementation and remains executable
before that adapter exists. referenceResume is a finite witness candidate,
not a new semantic owner. The outer close uses the exit actually exposed by
the inner frame step and the service state retained by its completed close.
Pinned policy: vendor/effect-4.0.0-rc.112/src/internal/core.ts:529-548 and
vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4302-4320.
-/

namespace Effect4Test.Counterexamples.Runtime.ScopeRestorationBoundary
open Effect4
abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
abbrev M := ScopeMachine.State Nat Nat Nat Nat Nat Nat Nat
abbrev E := Exit Nat Nat Nat Nat Nat
abbrev R := Exit Unit Nat Nat Nat Nat
abbrev C := Cause Nat Nat Nat Nat
abbrev S := Scope Nat Nat Nat Nat Nat Nat Nat
abbrev W := Nat × List (Nat × E)
def pending : C := Cause.interrupt (some 101)
def before : C := Cause.fail 10
def cleanup : C := Cause.die 20
def interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat where
  contA := fun k value => .success (k + value)
  contE := fun k _ => .success k
  syncValue := id
  suspendBody := .success
  finalizerExit := fun k _ => .failure (Cause.die k)
  reifyExit := fun _ => 0
  iterNext := fun _ value => ([], .done value)
  loopTest := fun _ _ => false
  loopBody := fun _ value => .success value
  loopStep := fun _ value => value
  loopDone := fun _ => 0
  notImplemented := 999

def referenceResume (machine : M) (fiber : F) :=
  (ScopeMachine.restore? machine).map fun exit =>
    FrameFiber.step interp { fiber with current := Prim.ofExit exit }
def scope : S := ⟨.sequential, .openMap [(10,1),(20,2)]⟩
def handler (reply : Nat → R) (operation : Nat) (original : E) : StateT W Id R :=
  fun world => (reply operation, (world.1 + 1, world.2 ++ [(operation, original)]))
def runClose (scope : S) (original : E) (reply : Nat → R) (world : W) :=
  ScopeMachine.runState (handler reply) (ScopeMachine.bound scope)
    (ScopeMachine.start scope original) world
def successClose := runClose scope (.success 5) (fun _ => Exit.void) (40,[])
def failedClose := runClose scope (.success 5) (fun n => .failure (Cause.die n)) (40,[])
def successFiber : F := ⟨.success 999, [.setInterruptible true], false, some pending, false⟩
def maskEvents : List (FrameEvent Nat Nat Nat Nat Nat Nat Nat) :=
  [.popped (.setInterruptible true), .ranContAll (.setInterruptible true), .substituted pending]
def noMaskEvents : List (FrameEvent Nat Nat Nat Nat Nat Nat Nat) :=
  [.popped (.setInterruptible true), .ranContAll (.setInterruptible true)]

#guard successClose.2 = (42,[(2,.success 5),(1,.success 5)])
#guard referenceResume successClose.1 successFiber =
  some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)
#guard referenceResume successClose.1 {successFiber with interruptedCause := none} =
  some (.finished (.success 5), noMaskEvents ++ [.yielded (.success 5)])
#guard (ScopeMachine.start scope (.success 5)).scope.state = .closed (.success 5)
#guard referenceResume (ScopeMachine.start scope (.success 5)) successFiber = none
#guard referenceResume (ScopeMachine.advance (ScopeMachine.start scope (.success 5))) successFiber = none
#guard successFiber.uninterruptible = successFiber
#guard referenceResume successClose.1
    ⟨.success 999, [.onSuccess (.success 0) 7, .setInterruptible true], false, some pending, false⟩ =
  some (.running ⟨.success 12, [.setInterruptible true], false, some pending, false⟩,
    [.popped (.onSuccess (.success 0) 7)])
#guard ScopeMachine.restore? failedClose.1 = some (.failure ⟨[Reason.die 2 ReasonAnnotations.empty, Reason.die 1 ReasonAnnotations.empty]⟩)
#guard failedClose.2 = (42,[(2,.success 5),(1,.success 5)])
def failureCause : C := ⟨[Reason.die 2 ReasonAnnotations.empty, Reason.die 1 ReasonAnnotations.empty]⟩
#guard referenceResume failedClose.1 successFiber =
  some (.finished (.failure failureCause), maskEvents ++ [.yielded (.failure failureCause)])
#guard referenceResume failedClose.1
    { successFiber with stack := [.setInterruptible true, .onFailure (.success 0) 77] } =
  some (.finished (.failure failureCause), maskEvents ++
    [.popped (.onFailure (.success 0) 77), .yielded (.failure failureCause)])
#guard referenceResume failedClose.1
    { successFiber with stack := [.setInterruptible true, .onExit (.success 0) 8 false] } =
  some (.running ⟨.failure (Cause.combine failureCause (Cause.die 8)),
    [.setInterruptible true], false, some pending, false⟩,
    maskEvents ++ [.popped (.onExit (.success 0) 8 false),
      .ranContAll (.onExit (.success 0) 8 false), .ranFinalizer 8 (.failure failureCause)])
def singleton : S := ⟨.sequential, .openInline 1 1⟩
def emptyFailure : R := .failure ⟨[]⟩
def singleEmpty := runClose singleton (.success 5) (fun _ => emptyFailure) (40,[])
def manyEmpty := runClose scope (.success 5) (fun _ => emptyFailure) (40,[])
#guard referenceResume singleEmpty.1 successFiber =
  some (.finished (.failure ⟨[]⟩), maskEvents ++ [.yielded (.failure ⟨[]⟩)])
#guard referenceResume manyEmpty.1 successFiber =
  some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)
def outgoing? (inner : M × W) (fiber : F) : Option E :=
  match referenceResume inner.1 fiber with
  | some (.running next, _) => next.current.asExit?
  | some (.finished exit, _) => some exit
  | none => none
def outerAfter (inner : M × W) (fiber : F) :=
  (outgoing? inner fiber).map fun outgoing =>
    runClose scope outgoing (fun n => .failure (Cause.die n)) inner.2
def outerAfterInterrupt := outerAfter successClose successFiber
#guard outgoing? successClose successFiber = some (.failure pending)
#guard outerAfterInterrupt.map Prod.snd =
  some (44,[(2,.success 5),(1,.success 5),(2,.failure pending),(1,.failure pending)])
#guard outerAfterInterrupt.bind (fun actual => ScopeMachine.restore? actual.1) =
  some (.failure (Cause.combine pending failureCause))
#guard outerAfterInterrupt.map (fun actual => ScopeMachine.journal actual.1) = some failureCause.reasons
#guard (outerAfter failedClose successFiber).map Prod.snd =
  some (44,[(2,.success 5),(1,.success 5),(2,.failure failureCause),(1,.failure failureCause)])
#guard (outerAfter failedClose successFiber).bind (fun actual => ScopeMachine.restore? actual.1) =
  some (.failure (Cause.combine failureCause failureCause))

-- Named acceptance candidates isolate each planted false policy.
def immediateCandidate := referenceResume successClose.1 successFiber
#guard immediateCandidate = some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents)
def pausedCandidate := referenceResume (ScopeMachine.advance (ScopeMachine.start scope (.success 5))) successFiber
#guard pausedCandidate = none
def failedCandidate := referenceResume failedClose.1 successFiber
#guard failedCandidate = some (.finished (.failure failureCause), maskEvents ++ [.yielded (.failure failureCause)])
def outerCandidate := outerAfterInterrupt.bind (fun actual => ScopeMachine.restore? actual.1)
#guard outerCandidate = some (.failure (Cause.combine pending failureCause))
def nestedCandidate := referenceResume successClose.1
  ⟨.success 999, [.onSuccess (.success 0) 7, .setInterruptible true], false, some pending, false⟩
#guard nestedCandidate = some (.running ⟨.success 12, [.setInterruptible true], false, some pending, false⟩,
  [.popped (.onSuccess (.success 0) 7)])
def singletonCandidate := referenceResume singleEmpty.1 successFiber
#guard singletonCandidate = some (.finished (.failure ⟨[]⟩), maskEvents ++ [.yielded (.failure ⟨[]⟩)])

theorem pending_does_not_replace_cleanup_failure :
    referenceResume failedClose.1 successFiber =
      some (.finished (.failure failureCause), maskEvents ++ [.yielded (.failure failureCause)]) := by decide
theorem overwrite_failure_is_observably_wrong :
    referenceResume failedClose.1 successFiber ≠
      some (.running ⟨.failure pending, [], true, some pending, false⟩, maskEvents) := by decide
theorem outer_cleanup_retains_delivered_interrupt :
    outerAfterInterrupt.bind (fun actual => ScopeMachine.restore? actual.1) =
      some (.failure (Cause.combine pending failureCause)) := by decide
theorem dropping_outer_cleanup_is_observably_wrong :
    outerAfterInterrupt.bind (fun actual => ScopeMachine.restore? actual.1) ≠
      some (.failure pending) := by decide
theorem outer_cleanup_receives_actual_outgoing_exit :
    outerAfterInterrupt.map Prod.snd =
      some (44,[(2,.success 5),(1,.success 5),(2,.failure pending),(1,.failure pending)]) := by decide
end Effect4Test.Counterexamples.Runtime.ScopeRestorationBoundary
