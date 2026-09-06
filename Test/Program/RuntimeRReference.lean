import Effect4.Api
import Effect4.Machine.Approximation
import Test.Program.CompileContract

/-!
# R3/R4 reference cases

Packet: `Test/contracts/program-runtime-r.contract.md`. These are finite runs
of the existing frame machine over source programs and explicit decision tapes.
They make no claim about the term evaluator or a host runtime. Fourteen program
families retain the reference expectations checked against base c462cd1. The
source, load arguments and tapes are public for the term comparison battery.

References: CompileContract's pYieldNow, pDeferred, pMasked, pScoped and pRace;
Machine.Witnesses W2 (async finalization), W3 (race cleanup), W6b (scope closing);
Machine.Fibers evaluatePrim's async/sync/finalizer/withFiber clauses. Exact source
line citations for those existing semantics stay in their owning modules.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.RuntimeRReference

open Effect4 Effect4.Machine Effect4.Program

def budget : Nat := 120

def evaluate : Api.Decision := .evaluate Api.root
def fire : Api.Decision := .fire Api.root
def interrupt : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def reply (answer : Completion Val Err Defect FiberId Ann) (token : Nat := 0) :
    Api.Decision := .answerAsync Api.root token answer

def run (program : NativeEff) (tape : List Api.Decision) (choices : List Bool := []) :
    Api.Run := Api.replay program budget tape choices

def fiberExit (r : Api.Run) (id : Nat) : Option ExitV :=
  (r.machine.fiber? ⟨id⟩).bind RunFiber.exit

def parked (r : Api.Run) (id : Nat := 0) : Option Parked :=
  (r.machine.fiber? ⟨id⟩).map RunFiber.parked

def interruptible (r : Api.Run) (id : Nat := 0) : Option Bool :=
  (r.machine.fiber? ⟨id⟩).map fun f => f.frame.interruptible

def context (r : Api.Run) (id : Nat := 0) : Option Ctx :=
  (r.machine.fiber? ⟨id⟩).map RunFiber.context

def waiterCount (r : Api.Run) (cell : Nat := 0) : Option Nat :=
  (r.stores.deferreds.cellAt ⟨cell⟩).map fun c => c.waiters.length

def scopeClosed (r : Api.Run) (scope : Nat := 0) : Option Bool :=
  (r.stores.scopes.entryAt scope).map fun e => e.scope.isClosed

def failure : CauseV := Cause.fail (Err.tag 7)
def interrupted : ExitV := Witnesses.interruptedBy Api.root Api.root
def immediateDaemon : Supervision.ForkOptions := ⟨true, true, .inherit⟩

-- 1. A suspended success continuation resumes after yield or deferred child start.
def suspendedBind : NativeEff := Test.Syntax.CompileContract.pYieldNow
def deferredJoin : NativeEff := Test.Syntax.CompileContract.pForkJoin
def startTape : List Api.Decision := [evaluate]
def fireTape : List Api.Decision := [evaluate, fire]

#guard (run suspendedBind startTape).exit = none
#guard parked (run suspendedBind startTape) = some (.withGuard 0)
#guard (run suspendedBind fireTape).exit = some (.success (.nat 5))
#guard (run deferredJoin startTape).exit = none
#guard (run deferredJoin fireTape).exit = some (.success (.nat 42))
#guard fiberExit (run deferredJoin fireTape) 1 = some (.success (.nat 42))

-- 2. Failure exits and success carrying an error-shaped value remain distinct.
def waiting : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit)) (.callback .deferredAwait (.var 0))
def failureTape : List Api.Decision := [evaluate, reply (.ofExit (.failure failure))]
def errorValueTape : List Api.Decision :=
  [evaluate, reply (.ofExit (.success (.exitErr failure)))]
def wrongTokenTape : List Api.Decision :=
  [evaluate, reply (.ofExit (.success (.nat 9))) 1]

#guard (run waiting startTape).outcome = .frontier
#guard waiterCount (run waiting startTape) = some 1
#guard (run waiting failureTape).exit = some (.failure failure)
#guard (run waiting errorValueTape).exit = some (.success (.exitErr failure))
#guard (run waiting wrongTokenTape).exit = none
#guard parked (run waiting wrongTokenTape) = some (.withGuard 0)

-- 3. ofRefGet executes a store read as the suspended fiber resumes.
def waitingWithRef : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 8)))
    (.bind (.perform .deferredMake (.lit .unit)) (.callback .deferredAwait (.var 1)))
def refAnswerTape : List Api.Decision := [evaluate, reply (.ofRefGet ⟨0⟩)]

#guard (run waitingWithRef startTape).stores.refs = [.nat 8]
#guard (run waitingWithRef refAnswerTape).exit = some (.success (.nat 8))
#guard (run waitingWithRef refAnswerTape).stores.refs = [.nat 8]

-- 4. A completed Deferred resumes during registration, without a waiter.
def immediateDeferred : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.perform .deferredSucceed
      (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
      (.callback .deferredAwait (.var 0)))

#guard (run immediateDeferred startTape).exit = some (.success (.nat 7))
#guard waiterCount (run immediateDeferred startTape) = some 0
#guard (run immediateDeferred startTape).stores.deferreds.due = []

-- 5. Completing a pending Deferred drains its child's resume on the same tape.
def dueDeferred : NativeEff := Test.Syntax.CompileContract.pDeferred
def dueDeferredFailure : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.callback .deferredAwait (.var 0)) immediateDaemon))
      (.bind (.perform .deferredFail
        (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
        (.awaitFiber (.var 1) .joinEffect)))

#guard (run dueDeferred startTape).exit = some (.success (.nat 7))
#guard fiberExit (run dueDeferred startTape) 1 = some (.success (.nat 7))
#guard waiterCount (run dueDeferred startTape) = some 0
#guard (run dueDeferred startTape).stores.deferreds.due = []
#guard (run dueDeferredFailure startTape).exit = some (.failure failure)
#guard fiberExit (run dueDeferredFailure startTape) 1 = some (.failure failure)

-- 6. Interruption distinguishes cleanup from an ordinary success continuation.
def cleanupUnit : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 9))) (.succeed (.lit .unit))
def ensured : NativeEff := .onExit (.yieldNow 0) cleanupUnit
def sequenced : NativeEff := .bind (.yieldNow 0) cleanupUnit
def interruptTape : List Api.Decision := [evaluate, interrupt]

#guard (run ensured interruptTape).stores.refs = [.nat 9]
#guard (run sequenced interruptTape).stores.refs = []
#guard (run ensured interruptTape).exit = some interrupted
#guard (run sequenced interruptTape).exit = some interrupted

-- 7. An async cleanup is masked, and finishes its remaining store work before
-- the recorded interrupt is delivered on restoration.
def asyncCleanup : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.onExit (.succeed (.lit (.nat 7)))
      (.bind (.callback .deferredAwait (.var 0))
        (.perform .refMake (.lit (.nat 9)))))
def cleanupAnswerTape : List Api.Decision :=
  [evaluate, interrupt, reply (.ofExit (.success .unit))]

#guard (run asyncCleanup startTape).exit = none
#guard interruptible (run asyncCleanup startTape) = some false
#guard (run asyncCleanup interruptTape).exit = none
#guard (run asyncCleanup interruptTape).stores.refs = []
#guard (run asyncCleanup cleanupAnswerTape).stores.refs = [.nat 9]
#guard (run asyncCleanup cleanupAnswerTape).exit = some interrupted
#guard interruptible (run asyncCleanup cleanupAnswerTape) = some true

-- 8. The inner mask controls delivery; the outer mask is restored afterward.
def maskedInside : NativeEff := .interruptible (.uninterruptible waiting)
def unmaskedInside : NativeEff := .uninterruptible (.interruptible waiting)

#guard interruptible (run maskedInside startTape) = some false
#guard (run maskedInside interruptTape).exit = none
#guard (run maskedInside cleanupAnswerTape).exit = some interrupted
#guard interruptible (run unmaskedInside startTape) = some true
#guard (run unmaskedInside interruptTape).exit = some interrupted
#guard waiterCount (run unmaskedInside interruptTape) = some 0

-- 9. A scoped body's context is returned as a value, while the fiber's context
-- is restored and the scope closed before the root exits.
def scopedContext : NativeEff := .scoped (.withFiber .getContext)

#guard (run scopedContext startTape).exit =
  some (.success (.context { emptyCtx with ambientScope := some 0 }))
#guard context (run scopedContext startTape) = some emptyCtx
#guard scopeClosed (run scopedContext startTape) = some true

-- 10. Both close chains run actual linked-child finalizers from NativeEff.
-- The parallel strategy creates two additional immediate daemon fibers.
def closeChildren (strategy : FinalizerStrategy) : NativeEff :=
  .bind (.perform (.scopeMake strategy) (.lit .unit))
    (.bind (.withFiber (.forkIn (.yieldNow 0) immediateDaemon (.var 0)))
      (.bind (.withFiber (.forkIn (.yieldNow 0) immediateDaemon (.var 0)))
        (.bind (.exit (.succeed (.lit .unit)))
          (.withFiber (.closeScope (.var 0) (.var 3))))))

#guard (run (closeChildren .sequential) startTape).exit = some (.success .unit)
#guard scopeClosed (run (closeChildren .sequential) startTape) = some true
#guard (run (closeChildren .sequential) startTape).fiberCount = 3
#guard (fiberExit (run (closeChildren .sequential) startTape) 1).isSome
#guard (fiberExit (run (closeChildren .sequential) startTape) 2).isSome
#guard (run (closeChildren .parallel) startTape).exit = some (.success .unit)
#guard scopeClosed (run (closeChildren .parallel) startTape) = some true
#guard (run (closeChildren .parallel) startTape).fiberCount = 5
#guard (fiberExit (run (closeChildren .parallel) startTape) 1).isSome
#guard (fiberExit (run (closeChildren .parallel) startTape) 2).isSome

-- 11. A successful race settles only after interrupting its parked loser.
def raceWinner : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.withFiber (.raceAll (.cons (.callback .deferredAwait (.var 0))
      (.cons (.succeed (.lit (.nat 2))) .nil))))

#guard (run raceWinner startTape).exit = some (.success (.nat 2))
#guard (run raceWinner startTape).fiberCount = 3
#guard fiberExit (run raceWinner startTape) 1 =
  some (Test.Syntax.CompileContract.interruptedFrom Api.root ⟨1⟩)
#guard waiterCount (run raceWinner startTape) = some 0
#guard interruptible (run raceWinner startTape) = some true

-- 12. Canceling a pending race interrupts its child and removes the waiter.
def racePending : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.withFiber (.raceAll (.cons (.callback .deferredAwait (.var 0)) .nil)))

#guard (run racePending startTape).exit = none
#guard waiterCount (run racePending startTape) = some 1
#guard (run racePending interruptTape).exit = some interrupted
#guard (fiberExit (run racePending interruptTape) 1).isSome
#guard waiterCount (run racePending interruptTape) = some 0

-- 13. Empty races stay parked until interruption, without spawning an entrant.
def raceEmpty : NativeEff := .withFiber (.raceAll .nil)

#guard (run raceEmpty startTape).outcome = .frontier
#guard (run raceEmpty startTape).exit = none
#guard parked (run raceEmpty startTape) = some (.withGuard 0)
#guard (run raceEmpty startTape).fiberCount = 1
#guard (run raceEmpty interruptTape).exit = some interrupted

-- 14. Missing choices and compile exhaustion leave live frontiers. The last
-- control has compile fuel zero but a positive machine budget, so the loop
-- actually reaches the compiled suspension.
def choice : NativeEff := Test.Syntax.CompileContract.pChoose
def compileZero : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  replayEval (interpOf choice) budget startTape (Api.load choice 0)

#guard (run choice startTape).outcome = .frontier
#guard (run choice startTape).exit = none
#guard (run choice startTape [true]).exit = some (.success (.nat 1))
#guard (run choice startTape [false]).exit = some (.success (.nat 2))
#guard (compileZero.machine.fiber? Api.root).bind RunFiber.exit = none
#guard compileZero.machine.stuck = none

end Test.Program.RuntimeRReference
