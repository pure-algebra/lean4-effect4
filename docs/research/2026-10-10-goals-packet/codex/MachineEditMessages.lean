import Effect4.Laws.Program.Interference
import Effect4.Api
import ProofGraph.AxiomAudit
/-!
Concept: reactive-scheduling, R4/R11; the proposed command-moves structure.
Question: R2 retains self-target edits through the existing local-fiber write-back.
Reach: actual native join/countdown/link/interrupt producers and finite message prototypes.
Limit: no core patch, admitted-history proof, progress claim, or runtime conformance claim.
Consumer: the R2 migration plan, then the unchanged generic FiberCore evaluator seam.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.MachineEditMessages
open Effect4 Effect4.Machine Effect4.Program

/-- First-order payloads contain no interpreter or observer predicate. -/
inductive Edit (ε δ ι α : Type)
  | observe (target : FiberId) (observer : Observer)
  | dropToken (token : Nat)
  | interrupt (target : FiberId) (cause : Cause ε δ ι α)

section Generic
variable {ν σ β ε δ ι α χ St κ φ η : Type}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable [core : FiberCore ν β ε δ ι α κ φ]

/-- The already-computed cause is applied to the current target record. -/
def record (cause : Cause ε δ ι α) (f : RunFiber ν σ β ε δ ι α χ κ φ) :
    RunFiber ν σ β ε δ ι α χ κ φ × Bool :=
  if f.exit.isSome then (f, false)
  else
    let accumulated := match core.interruptedCause f.frame with
      | none => cause
      | some previous => Cause.combine previous cause
    let f := {f with frame := core.recordCause f.frame accumulated}
    if core.interruptible f.frame then
      if f.running then ({f with frame := core.setDeferred f.frame true}, false)
      else ({f with
        parked := .notParked
        pending := []
        frame := core.answerWith f.frame (core.failure accumulated)}, true)
    else (f, false)

def causeOf (interp : RunInterp ν σ β ε δ ι α χ St κ) (who : Option FiberId)
    (extra : ReasonAnnotations α) (target : FiberId) : Cause ε δ ι α :=
  Cause.annotate (Supervision.interruptCause interp.encodeFiber who (interp.stackAnnotations target)) extra false

/-- The prototype retains the exact generic interruptRecord body. -/
theorem record_source (interp : RunInterp ν σ β ε δ ι α χ St κ) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ κ φ) :
    record (causeOf interp who extra f.id) f = interruptRecord interp who extra f := rfl

def applyEdit (edit : Edit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ) :=
  match edit with
  | .observe target observer =>
    (m.modify target fun f => {f with observers := f.observers ++ [observer]}, [])
  | .dropToken token =>
    ({m with fibers := m.fibers.map fun f => {f with observers := f.observers.filter fun
      | .resumeAwait _ t _ => t ≠ token
      | .countdown _ t => t ≠ token
      | _ => true}}, [])
  | .interrupt target cause =>
    match m.fiber? target with
    | none => (m, [])
    | some f =>
      let (next, now) := record cause f
      (m.update next, if now then [.evaluate target] else [])

def applyAll (edits : List (Edit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ) :=
  edits.foldl (fun (held : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) edit =>
    let next := applyEdit edit held.1
    (next.1, held.2 ++ next.2)) (m, [])

/-- Prototype only: write back, apply messages, then choose the outcome disposition. -/
def commit (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η) (edits : List (Edit ε δ ι α)) :
    RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ) :=
  let applied := applyAll edits (it.machine.update it.fiber)
  let owner := (applied.1.fiber? it.fiber.id).getD it.fiber
  settle id rest {it with machine := applied.1, fiber := owner, nested := applied.2 ++ it.nested}
end Generic

abbrev Fiber := Moves.NFiber
abbrev Message := Edit Err Defect FiberId Ann
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann

def root : NativeEff := .succeed (.lit .unit)
def interp : Moves.NInterp := interpOf root []
def owner (code : NCode) : Fiber :=
  {RunFiber.make ⟨0⟩ code true (2048, false) emptyCtx with running := true}
def machine (fiber : Fiber) : NativeMachine := {Api.load root 1 with fibers := [fiber]}
def storedObservers (m : NativeMachine) : List Observer :=
  ((m.fiber? ⟨0⟩).getD (owner (.success .unit))).observers
def deferred (m : NativeMachine) : Bool :=
  ((m.fiber? ⟨0⟩).getD (owner (.success .unit))).frame.deferredInterrupt

-- Self-join: the actual registration is erased by today's parked write-back.
def joinOwner := owner (interp.parkCode (.join ⟨0⟩ .awaitValue))
def joinResult := evaluatePrim interp (machine joinOwner) joinOwner false
#guard storedObservers joinResult.machine == [.resumeAwait ⟨0⟩ 0 .awaitValue]
#guard storedObservers (settle ⟨0⟩ [] joinResult).1 == []
def joinMessages : NativeMachine × List NCmd :=
  commit ⟨0⟩ [] {joinResult with machine := {joinResult.machine with fibers := [joinOwner]}}
    [.observe ⟨0⟩ (.resumeAwait ⟨0⟩ 0 .awaitValue)]
#guard storedObservers joinMessages.1 == [.resumeAwait ⟨0⟩ 0 .awaitValue]

-- Self-countdown: the same loss occurs through the generic helper.
def countdown := countdownPark interp (machine joinOwner) joinOwner [⟨0⟩] .void
def countdownResult : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  ⟨countdown.1, countdown.2.1, false, .parked, []⟩
#guard storedObservers countdown.1 == [.countdown ⟨0⟩ 0]
#guard storedObservers (settle ⟨0⟩ [] countdownResult).1 == []
def countdownMessages := commit ⟨0⟩ []
  {countdownResult with machine := {countdown.1 with fibers := [joinOwner]}}
  [.observe ⟨0⟩ (.countdown ⟨0⟩ 0)]
#guard storedObservers countdownMessages.1 == [.countdown ⟨0⟩ 0]

-- Open self-link: retain the actual store registration and replace only the lost observer edit.
def openMachine : NativeMachine :=
  {machine joinOwner with state := {Stores.empty with scopes := Stores.empty.scopes.make 0 .sequential, nextName := 1}}
def linkResult := evaluatePrim.withFiber interp openMachine joinOwner false (.runIn ⟨0⟩ 0)
#guard storedObservers linkResult.machine == [.dropScopeFinalizer 0 1]
#guard storedObservers (settle ⟨0⟩ [] linkResult).1 == []
def linkMessages := commit ⟨0⟩ [] {linkResult with machine := {linkResult.machine with fibers := [joinOwner]}}
  [.observe ⟨0⟩ (.dropScopeFinalizer 0 1)]
#guard storedObservers linkMessages.1 == [.dropScopeFinalizer 0 1]
#guard linkMessages.1.state == linkResult.machine.state

-- Self-interrupt: current producer records the flag, then the local write-back erases it.
def interruptResult := evaluatePrim.interruptAs interp (machine joinOwner) joinOwner false ⟨0⟩ ⟨0⟩
def selfCause : CauseV := causeOf interp (some ⟨0⟩) (interp.stackAnnotations ⟨0⟩) ⟨0⟩
#guard deferred interruptResult.machine
#guard !(deferred (settle ⟨0⟩ [] interruptResult).1)
def interruptMessages := commit ⟨0⟩ []
  {interruptResult with machine := {interruptResult.machine with fibers := [joinOwner]}}
  [.interrupt ⟨0⟩ selfCause]
#guard deferred interruptMessages.1
theorem interrupt_commands : interruptMessages.2 = [.afterInterrupt ⟨0⟩ false (.join ⟨0⟩ .awaitValue)] := rfl

-- The parked disposition must inspect the post-message flag before marking the owner idle.
def interruptedPark := commit ⟨0⟩ []
  {countdownResult with machine := {countdown.1 with fibers := [joinOwner]}}
  [.interrupt ⟨0⟩ selfCause]
theorem parked_commands : interruptedPark.2 = [.loop ⟨0⟩ false] := rfl
#guard ((interruptedPark.1.fiber? ⟨0⟩).getD joinOwner).parked == .notParked
-- Applying the message after today's complete settlement instead sees an idle target.
def tooLate := applyEdit (.interrupt ⟨0⟩ selfCause) (settle ⟨0⟩ [] countdownResult).1
theorem late_commands : tooLate.2 = [.evaluate ⟨0⟩] := rfl
#guard !(deferred tooLate.1)

-- Token removal also needs to reach the owner's returned observer list.
def watched := {joinOwner with observers := [.countdown ⟨0⟩ 9]}
def dropped := FiberAction.dropObservers interp (machine watched) watched false 9
#guard storedObservers dropped.machine == []
#guard storedObservers (settle ⟨0⟩ [] dropped).1 == [.countdown ⟨0⟩ 9]
def droppedMessages := commit ⟨0⟩ [] {dropped with machine := machine watched} [.dropToken 9]
#guard storedObservers droppedMessages.1 == []

-- Closed self-link uses the actual native close-state hook and loses the deferred cause too.
def closedMachine : NativeMachine := {openMachine with state := {openMachine.state with
  scopes := openMachine.state.scopes.closeState 0 (.success .unit)}}
def closedResult := evaluatePrim.withFiber interp closedMachine joinOwner false (.runIn ⟨0⟩ 0)
#guard deferred closedResult.machine
#guard !(deferred (settle ⟨0⟩ [] closedResult).1)
def closedMessages := commit ⟨0⟩ []
  {closedResult with machine := {closedResult.machine with fibers := [joinOwner]}}
  [.interrupt ⟨0⟩ (causeOf interp (some ⟨0⟩) ReasonAnnotations.empty ⟨0⟩)]
#guard deferred closedMessages.1
#guard closedMessages.1.state == closedResult.machine.state

-- An ordinary other-target join retains the exact old result.
def otherOwner := owner (interp.parkCode (.join ⟨1⟩ .awaitValue))
def peer : Fiber := {joinOwner with id := ⟨1⟩}
def otherMachine : NativeMachine := {machine otherOwner with fibers := [otherOwner, peer], nextId := 2}
def otherResult := evaluatePrim interp otherMachine otherOwner false

theorem other_join_same : commit ⟨0⟩ []
    {otherResult with machine := {otherResult.machine with fibers := [otherOwner, peer]}}
    [.observe ⟨1⟩ (.resumeAwait ⟨0⟩ 0 .awaitValue)] = settle ⟨0⟩ [] otherResult := rfl

-- The countdown observer has its own stale waiter write-back outside Iter/settle.
def callbackWaiter : Fiber :=
  {countdown.2.1 with
    running := false
    pending := [⟨0, some ⟨1⟩, [⟨0⟩], [], .void, false⟩]}
def callbackMachine : NativeMachine := {machine callbackWaiter with
  fibers := [callbackWaiter, {peer with exit := some (.success .unit), running := false}]
  nextId := 2}
def callbackResult := fireObserver interp ⟨1⟩ (.success .unit) (callbackMachine, []) (.countdown ⟨0⟩ 0)
#guard storedObservers callbackResult.1 == []
#guard (((callbackResult.1.fiber? ⟨0⟩).getD callbackWaiter).pending.map Pending.waitingOn) == [some ⟨0⟩]
def callbackMessage := applyEdit (Edit.observe (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
  ⟨0⟩ (.countdown ⟨0⟩ 0)) callbackResult.1
#guard storedObservers callbackMessage.1 == [.countdown ⟨0⟩ 0]

end Test.MachineEditMessages
#axiom_audit Effect4.Laws.Program.Interference
