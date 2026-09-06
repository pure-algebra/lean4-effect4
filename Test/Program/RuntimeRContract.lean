import Effect4.Program.RuntimeR
import Test.Program.RuntimeRReference

/-!
# R3/R4 finite term/frame comparisons

Packet: `Test/contracts/program-runtime-r.contract.md`. Every comparison uses
the source, budget 120 and literal decision tape from RuntimeRReference. The
reference module separately pins expected exits, stores and waiting states.
These finite checks do not prove R5, general simulation or host correspondence.

The comparison includes all exits and complete stores (including Deferred
waiters and due resumes), replay outcome, parking, interrupt causes, deferred
flags, contexts, and allocation counters. Interruptibility is compared on live
fibers. It omits saved code, stack representation, trace, and local step counts.

`RSTEP-FB-TERMINAL-MASK`: the frame machine's `finishFrame` keeps the incoming
fiber on `FrameStep.finished` (`Machine/Fibers.lean:963-964`); the pop's restored
mask is discarded. `deliverR` keeps the returned saved state. The unused flag
can therefore differ after exit, and two literal pins below document that
difference. Every other control field is still compared on all fibers.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.RuntimeRContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Test.Program.RuntimeRReference

/-- Observable control data beyond the exit/store observation. -/
structure FiberControl where
  id : FiberId
  parked : Parked
  interruptible : Option Bool
  interruptedCause : Option CauseV
  deferredInterrupt : Bool
  context : Ctx
deriving DecidableEq

def frameControl (m : Api.Machine) : List FiberControl :=
  m.fibers.map fun f => ⟨f.id, f.parked,
    if f.exit.isSome then none else some f.frame.interruptible,
    f.frame.interruptedCause, f.frame.deferredInterrupt, f.context⟩

def termControl (m : RState) : List FiberControl :=
  m.fibers.map fun f => ⟨f.id, f.parked,
    if f.exit.isSome then none else some f.frame.interruptible,
    f.frame.interruptedCause, f.frame.deferredInterrupt, f.context⟩

def termOutcome : RReplay → Api.Outcome
  | .finished _ => .finished
  | .frontier _ => .frontier
  | .stuck why _ => .stuck why

def agrees (program : NativeEff) (tape : List Api.Decision) (choices : List Bool := []) : Bool :=
  let reference := RuntimeRReference.run program tape choices
  let term := replayR program budget tape choices
  decide (obsR term.machine = obs reference.machine ∧
    termOutcome term = reference.outcome ∧
    termControl term.machine = frameControl reference.machine ∧
    term.machine.nextId = reference.machine.nextId ∧
    term.machine.nextToken = reference.machine.nextToken ∧
    term.machine.nextRace = reference.machine.nextRace)

-- 1. Suspended continuations, both before and after their resume.
#guard agrees suspendedBind startTape
#guard agrees suspendedBind fireTape
#guard agrees deferredJoin startTape
#guard agrees deferredJoin fireTape

-- 2--5. Completion data, immediate registration and synchronous due delivery.
#guard agrees waiting startTape
#guard agrees waiting failureTape
#guard agrees waiting errorValueTape
#guard agrees waiting wrongTokenTape
#guard agrees waitingWithRef refAnswerTape
#guard agrees immediateDeferred startTape
#guard agrees dueDeferred startTape
#guard agrees dueDeferredFailure startTape

-- 6--8. Interrupted cleanup, async finalization, and nested masks.
#guard agrees ensured interruptTape
#guard agrees sequenced interruptTape
#guard agrees asyncCleanup startTape
#guard agrees asyncCleanup interruptTape
#guard agrees asyncCleanup cleanupAnswerTape
#guard agrees maskedInside interruptTape
#guard agrees maskedInside cleanupAnswerTape
#guard agrees unmaskedInside startTape
#guard agrees unmaskedInside interruptTape

-- 9--10. Context restoration and both synthesized scope-close chains.
#guard agrees scopedContext startTape
#guard agrees (closeChildren .sequential) startTape
#guard agrees (closeChildren .parallel) startTape

-- 11--13. Settled, canceled, and empty races, including the waiting prefixes.
#guard agrees raceWinner startTape
#guard agrees racePending startTape
#guard agrees racePending interruptTape
#guard agrees raceEmpty startTape
#guard agrees raceEmpty interruptTape

-- 14. Choices and compile exhaustion remain unfinished when no answer exists.
#guard agrees choice startTape
#guard agrees choice startTape [true]
#guard agrees choice startTape [false]

def termCompileZero : RReplay :=
  replayEval (interpR choice 0) budget startTape (loadR choice 0)

#guard obsR termCompileZero.machine = obs compileZero.machine
#guard termControl termCompileZero.machine = frameControl compileZero.machine
#guard termOutcome termCompileZero = .frontier

-- RSTEP-FB-TERMINAL-MASK: the frame's retained terminal flag is stale after pop.
#guard RuntimeRReference.interruptible (RuntimeRReference.run waiting failureTape) = some false
#guard ((replayR waiting budget failureTape).machine.fiber? Api.root).map
  (fun f => f.frame.interruptible) = some true
#guard RuntimeRReference.interruptible (RuntimeRReference.run scopedContext startTape) = some false
#guard ((replayR scopedContext budget startTape).machine.fiber? Api.root).map
  (fun f => f.frame.interruptible) = some true

-- The loaded state uses the existing generic observation and first-order tape.
example (program : NativeEff) (fuel : Nat) (choices : List Bool) :
    obsR (loadR program fuel choices) = ⟨[(Api.root, none)], Stores.empty⟩ :=
  obsR_load program fuel choices

example (program : NativeEff) (fuel : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    (interpR program fuel).answerCode answer = denoteCompletion answer :=
  interpR_answerCode program fuel answer

end Test.Program.RuntimeRContract
