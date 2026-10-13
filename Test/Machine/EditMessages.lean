import Effect4.Api
import Test.Counterexamples.Machine.Semantics.SelfInterrupt
/-!
Concept: reactive-scheduling, R4/R11. The R2 settlement repair serves the existing guarded run laws.
Question: retained finite controls for addressed observer and interrupt edits.
Reach: actual native producers, self-target records, and countdown callback cuts.
Limit: these reductions establish no universal simulation or progress claim.
Consumer: the R2 core migration and its shared Ledger settlement theorem.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Test.Machine.EditMessages
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
def root : NativeEff := .succeed (.lit .unit)
def interp := interpOf root []
def owner (code : NCode) : Fiber :=
  {RunFiber.make ⟨0⟩ code true (2048, false) emptyCtx with running := true}
def machine (fiber : Fiber) : NativeMachine := {Api.load root 1 with fibers := [fiber]}
def storedObservers (m : NativeMachine) : List Observer :=
  ((m.fiber? ⟨0⟩).getD (owner (.success .unit))).observers
def deferred (m : NativeMachine) : Bool :=
  ((m.fiber? ⟨0⟩).getD (owner (.success .unit))).frame.deferredInterrupt

def joinOwner := owner (interp.parkCode (.join ⟨0⟩ .awaitValue))
def joinResult := evaluatePrim interp (machine joinOwner) joinOwner false
#guard storedObservers joinResult.machine == []
#guard joinResult.edits == [.observe ⟨0⟩ (.resumeAwait ⟨0⟩ 0 .awaitValue)]
#guard storedObservers (settle ⟨0⟩ [] joinResult).1 == [.resumeAwait ⟨0⟩ 0 .awaitValue]

def countdown := countdownParkEdits interp (machine joinOwner) joinOwner [⟨0⟩] .void
def countdownResult : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  ⟨countdown.1, countdown.2.1, false, .parked, [], countdown.2.2.2⟩
#guard storedObservers (settle ⟨0⟩ [] countdownResult).1 == [.countdown ⟨0⟩ 0]

def openMachine : NativeMachine :=
  {machine joinOwner with state := {Stores.empty with scopes := Stores.empty.scopes.make 0 .sequential, nextName := 1}}
def linkResult := evaluatePrim.withFiber interp openMachine joinOwner false (.runIn ⟨0⟩ 0)
#guard storedObservers (settle ⟨0⟩ [] linkResult).1 == [.dropScopeFinalizer 0 1]
#guard (settle ⟨0⟩ [] linkResult).1.state == linkResult.machine.state

def interruptResult := evaluatePrim.interruptAs interp (machine joinOwner) joinOwner false ⟨0⟩ ⟨0⟩
#guard deferred (settle ⟨0⟩ [] interruptResult).1
theorem interrupt_commands : (settle ⟨0⟩ [] interruptResult).2 =
  [.afterInterrupt ⟨0⟩ false (.join ⟨0⟩ .awaitValue)] := rfl

def selfCause : CauseV := interruptCause interp (some ⟨0⟩) ReasonAnnotations.empty ⟨0⟩
def interruptedPark := settle ⟨0⟩ [] {countdownResult with edits := [.interrupt ⟨0⟩ selfCause]}
theorem parked_commands : interruptedPark.2 = [.loop ⟨0⟩ false] := rfl
#guard deferred interruptedPark.1
#guard ((interruptedPark.1.fiber? ⟨0⟩).getD joinOwner).parked == .notParked
-- The control records why messages precede disposition.
def tooLate := applyFiberEdit (.interrupt ⟨0⟩ selfCause)
  (settleOutcome ⟨0⟩ [] {countdownResult with edits := []}).1
theorem late_commands : tooLate.2 = [.evaluate ⟨0⟩] := rfl
#guard !(deferred tooLate.1)

def watched := {joinOwner with observers := [.countdown ⟨0⟩ 9]}
def dropped := FiberAction.dropObservers interp (machine watched) watched false 9
#guard storedObservers (settle ⟨0⟩ [] dropped).1 == []

def closedMachine : NativeMachine := {openMachine with state := {openMachine.state with
  scopes := openMachine.state.scopes.closeState 0 (.success .unit)}}
def closedResult := evaluatePrim.withFiber interp closedMachine joinOwner false (.runIn ⟨0⟩ 0)
#guard deferred (settle ⟨0⟩ [] closedResult).1
#guard (settle ⟨0⟩ [] closedResult).1.state == closedResult.machine.state

def peer : Fiber := {joinOwner with id := ⟨1⟩}
def callbackWaiter : Fiber :=
  {countdown.2.1 with
    running := false
    pending := [⟨0, some ⟨1⟩, [⟨0⟩], [], .void, false⟩]}
def callbackMachine : NativeMachine := {machine callbackWaiter with
  fibers := [callbackWaiter, {peer with exit := some (.success .unit), running := false}], nextId := 2}
def callbackResult := fireObserver interp ⟨1⟩ (.success .unit) (callbackMachine, []) (.countdown ⟨0⟩ 0)
#guard storedObservers callbackResult.1 == [.countdown ⟨0⟩ 0]
#guard (((callbackResult.1.fiber? ⟨0⟩).getD callbackWaiter).pending.map Pending.remaining) == [[]]
#guard (((callbackResult.1.fiber? ⟨0⟩).getD callbackWaiter).pending.map Pending.collected) == [[.success .unit]]
#guard (((callbackResult.1.fiber? ⟨0⟩).getD callbackWaiter).pending.map Pending.waitingOn) == [some ⟨0⟩]
-- Control (decisions row 376 (2)): the same firing while the record waits on another fiber is stale:
-- no command, nothing collected, the record and the stored observers unchanged.
def staleWaiter : Fiber := {callbackWaiter with pending := [⟨0, some ⟨0⟩, [], [], .void, false⟩]}
def staleMachine : NativeMachine := {callbackMachine with
  fibers := [staleWaiter, {peer with exit := some (.success .unit), running := false}]}
def staleResult := fireObserver interp ⟨1⟩ (.success .unit) (staleMachine, []) (.countdown ⟨0⟩ 0)
#guard staleResult.2.isEmpty
#guard ((staleResult.1.fiber? ⟨0⟩).getD callbackWaiter).pending == staleWaiter.pending
#guard storedObservers staleResult.1 == staleWaiter.observers
-- Fail-fast interrupts this idle waiter; the canceled pending guard cannot reappear.
def failFastWaiter : Fiber := {callbackWaiter with pending := [⟨0, some ⟨1⟩, [⟨0⟩], [], .void, true⟩]}
def failFastMachine : NativeMachine := {callbackMachine with fibers := [failFastWaiter, peer]}
def failFastResult := fireObserver interp ⟨1⟩ (.failure selfCause)
  (failFastMachine, []) (.countdown ⟨0⟩ 0)
#guard (((failFastResult.1.fiber? ⟨0⟩).getD failFastWaiter).pending) == []
#guard storedObservers failFastResult.1 == []

-- Raw messages explicitly refuse settlement when the local owner is absent.
def missing : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  ⟨{machine joinOwner with fibers := []}, joinOwner, false, .answered, [], [.dropToken 0]⟩
#guard (settle ⟨0⟩ [] missing).1.stuck == some (.unknownFiber ⟨0⟩)
theorem missing_commands : (settle ⟨0⟩ [] missing).2 = [] := rfl

-- Addressed edits compose cause deltas against the current target, in word order.
def priorCause : CauseV := .interrupt (some ⟨1⟩)
def alreadyInterrupted : Fiber :=
  {joinOwner with frame := {joinOwner.frame with interruptedCause := some priorCause}}
def composed := applyFiberEdit (.interrupt ⟨0⟩ selfCause) (machine alreadyInterrupted)
#guard (((composed.1.fiber? ⟨0⟩).getD joinOwner).frame.interruptedCause) ==
  some (Cause.combine priorCause selfCause)
-- Edit interpretation emits no new trace events.
theorem interrupt_trace : composed.1.trace = (machine alreadyInterrupted).trace := rfl

def observerOrderA := applyFiberEdits [.observe ⟨0⟩ (.countdown ⟨0⟩ 9), .dropToken 9]
  (machine joinOwner)
def observerOrderB := applyFiberEdits [.dropToken 9, .observe ⟨0⟩ (.countdown ⟨0⟩ 9)]
  (machine joinOwner)
#guard storedObservers observerOrderA.1 == []
#guard storedObservers observerOrderB.1 == [.countdown ⟨0⟩ 9]

-- An ordinary other-target join has the original eager helper observation.
def otherOwner := owner (interp.parkCode (.join ⟨1⟩ .awaitValue))
def otherMachine : NativeMachine := {machine otherOwner with fibers := [otherOwner, peer], nextId := 2}
def otherResult := evaluatePrim interp otherMachine otherOwner false
def eagerOther : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  {otherResult with
    machine := otherResult.machine.modify ⟨1⟩ (fun f =>
      {f with observers := f.observers ++ [.resumeAwait ⟨0⟩ 0 .awaitValue]})
    edits := []}
theorem other_join_same : settle ⟨0⟩ [] otherResult = settleOutcome ⟨0⟩ [] eagerOther := rfl
end Test.Machine.EditMessages
