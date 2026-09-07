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
  replayEval (interpR choice) budget startTape (loadR choice 0)

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

/-! ## P1b (2026-09-06): the frame machine's arms are the shared fiber actions

`Machine/Fibers.lean`'s `FiberAction` helpers are generic in the fiber core and in how an
instance installs a value answer. Under the core's own answer each is definitionally the
frame arm of `evaluatePrim` (the identities below are `rfl`), and the term evaluator's arm
is the same helper on the fiber that has saved its continuation slot. The frame arms are
not rewritten to call the helpers; nothing in `Machine/Fibers.lean`'s existing clauses
changed, and every reference expectation above is unchanged. -/

section SharedActions

variable (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
  (m : Api.Machine) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (y : Bool)

theorem frame_getId :
    evaluatePrim.withFiber interp m f y .getId = FiberAction.getId interp m f y := rfl

theorem frame_getContext :
    evaluatePrim.withFiber interp m f y .getContext = FiberAction.getContext interp m f y := rfl

theorem frame_setContext (ctx : Ctx) :
    evaluatePrim.withFiber interp m f y (.setContext ctx) = FiberAction.setContext interp m f y ctx := rfl

theorem frame_snapshotChildren :
    evaluatePrim.withFiber interp m f y .snapshotChildren =
      FiberAction.snapshotChildren interp m f y := rfl

theorem frame_dropObservers (token : Nat) :
    evaluatePrim.withFiber interp m f y (.dropObservers token) =
      FiberAction.dropObservers interp m f y token := rfl

theorem frame_runIn (target : FiberId) (scope key : Nat) :
    evaluatePrim.withFiber interp m f y (.runIn target scope key) =
      FiberAction.runIn interp m f y target scope key := rfl

theorem frame_fork (program : NCode) (options : Supervision.ForkOptions) :
    evaluatePrim.withFiber interp m f y (.fork program options) =
      FiberAction.fork interp m f y program options := rfl

theorem frame_forkIn (program : NCode) (options : Supervision.ForkOptions) (scope key : Nat) :
    evaluatePrim.withFiber interp m f y (.forkIn program options scope key) =
      FiberAction.forkIn interp m f y program options scope key := rfl

theorem frame_forkScoped (program : NCode) (options : Supervision.ForkOptions) (key : Nat) :
    evaluatePrim.withFiber interp m f y (.forkScoped program options key) =
      FiberAction.forkScoped interp m f y program options key := rfl

theorem frame_refuse (cause : CauseV) :
    evaluatePrim.withFiber interp m f y (.refuse cause) = FiberAction.refuse m f y cause := rfl

theorem frame_closeScope (scope : Nat) (exit : ExitV) :
    evaluatePrim.withFiber interp m f y (.closeScope scope exit) =
      FiberAction.closeScope interp m f y scope exit := by
  rcases hc : interp.closeScope scope exit f.frame.interruptible f.id m.state with _ | ⟨state, program⟩ <;>
    simp only [evaluatePrim.withFiber, FiberAction.closeScope, FiberCore.interruptible, frameCore, hc]

theorem frame_interruptThenJoin (target : FiberId) (interruptor : Option FiberId) :
    evaluatePrim.interruptThenJoin interp m f y target interruptor =
      FiberAction.interruptThenJoin interp m f y target interruptor := by
  rcases hm : m.fiber? target with _ | t <;>
    simp only [evaluatePrim.interruptThenJoin, FiberAction.interruptThenJoin, hm]

theorem frame_interrupt (target : FiberId) :
    evaluatePrim.withFiber interp m f y (.interrupt target) =
      FiberAction.interruptThenJoin interp m f y target (some f.id) := by
  simp only [evaluatePrim.withFiber]
  exact frame_interruptThenJoin interp m f y target (some f.id)

theorem frame_interruptScoped (target : FiberId) (h : target ≠ f.id) :
    evaluatePrim.withFiber interp m f y (.interruptScoped target) =
      FiberAction.interruptThenJoin interp m f y target (some f.id) := by
  simp only [evaluatePrim.withFiber, h, ↓reduceIte]
  exact frame_interruptThenJoin interp m f y target (some f.id)

theorem frame_interruptAll (targets : List FiberId) (who : Option FiberId) :
    evaluatePrim.withFiber interp m f y (.interruptAll targets who) =
      FiberAction.interruptAll interp m f y targets who := rfl

theorem frame_awaitAll (targets : List FiberId) :
    evaluatePrim.withFiber interp m f y (.awaitAll targets) =
      FiberAction.awaitAll interp m f y targets false := rfl

theorem frame_awaitAllFailFast (targets : List FiberId) :
    evaluatePrim.withFiber interp m f y (.awaitAllFailFast targets) =
      FiberAction.awaitAll interp m f y targets true := rfl

theorem frame_awaitNewChildren (snapshot : List FiberId) :
    evaluatePrim.withFiber interp m f y (.awaitNewChildren snapshot) =
      FiberAction.awaitNewChildren interp m f y snapshot := rfl

theorem frame_cancelRace (raceId : Nat) :
    evaluatePrim.withFiber interp m f y (.cancelRace raceId) =
      FiberAction.cancelRace interp m f y raceId := by
  rcases hr : m.race? raceId with _ | race
  · simp only [evaluatePrim.withFiber, FiberAction.cancelRace, FiberAction.coreAnswer,
      FiberCore.answerWith, FiberCore.success, frameCore, hr]
  · simp only [evaluatePrim.withFiber, FiberAction.cancelRace, FiberAction.outcomeOf, hr]

theorem frame_raceAll (entrants : List NCode) :
    evaluatePrim.withFiber interp m f y (.raceAll entrants) =
      FiberAction.raceAll interp m f y entrants := rfl

theorem frame_yieldNow (priority : Nat) :
    evaluatePrim interp m { f with frame := { f.frame with current := Prim.yieldNowWith priority } } y =
      FiberAction.yieldNow interp m
        { f with frame := { f.frame with current := Prim.yieldNowWith priority } } y priority := rfl

theorem frame_join (root : NativeEff) (target : FiberId) (mode : Supervision.ObserverMode) :
    evaluatePrim (interpOf root) m
        { f with frame := { f.frame with current := Prim.suspend (EffThunk.park (ParkKind.join target mode)) } } y =
      FiberAction.join (interpOf root) m
        { f with frame := { f.frame with current := Prim.suspend (EffThunk.park (ParkKind.join target mode)) } }
        y target mode := by
  rcases hm : m.fiber? target with _ | t
  · simp only [evaluatePrim, FiberAction.join, interpOf, hm]
  · rcases hx : t.exit with _ | exit <;>
      simp only [evaluatePrim, FiberAction.join, interpOf, hm, hx, FiberCore.answerWith,
        FiberCore.pushAsyncFinalizer, frameCore]

-- The term arms are the same helpers: a value answer installs the continuation directly
-- (P2), an answer that arrives as code goes through the saved answer slot.
theorem term_getId (i : RInterp) (m' : RState) (f' : RFiber) (next : Val → RProgram) :
    evaluateFiberR i m' f' y .getId next = FiberAction.getId i m' f' y (answerWith next) := rfl

theorem term_fork (i : RInterp) (m' : RState) (f' : RFiber) (child : Body)
    (options : Supervision.ForkOptions) (next : Val → RProgram) :
    evaluateFiberR i m' f' y (.fork child options) next =
      FiberAction.fork i m' f' y (bodyR i child) options (answerWith next) := rfl

theorem term_yieldNow (i : RInterp) (m' : RState) (f' : RFiber) (priority : Nat)
    (next : Val → RProgram) :
    evaluateFiberR i m' f' y (.yieldNow priority) next =
      FiberAction.yieldNow i m' (saveAnswerR f' (seqR next)) y priority := rfl

theorem term_join (i : RInterp) (m' : RState) (f' : RFiber) (target : FiberId)
    (next : ExitV → RProgram) :
    evaluateFiberR i m' f' y (.await target .joinEffect) next =
      FiberAction.join i m' (saveAnswerR f' next) y target .joinEffect := rfl

end SharedActions

/-! ## P2 (2026-09-06): counted operations, command budgets and scheduling witnesses

The phase model of `docs/research/2026-09-06-p0-fable-record.md` §4, landed. On every
program below the term evaluator and the corrected frame machine agree on the
observation, on the root's counted operations and on the least command budget that
settles the start; the three P1a corrections make the frame machine agree with the host
on the folded exit and the generator and loop wrappers. These are finite checks; the
local relation is inhabited by `store_step_rel` on the store step. -/

section Lockstep

def withBudget {κ φ : Type} (fs : List (RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx κ φ))
    (b : Nat) : List (RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx κ φ) :=
  fs.map fun f => { f with maxOpsBeforeYield := b, context := ⟨none, b, false⟩ }

def frameLoad (e : NativeEff) (fuel : Nat := 40) (b : Nat := 2048) : Api.Machine :=
  { Api.load e fuel with fibers := withBudget (Api.load e fuel).fibers b }

def termLoad (e : NativeEff) (fuel : Nat := 40) (b : Nat := 2048) : RState :=
  { loadR e fuel with fibers := withBudget (loadR e fuel).fibers b }

def startCmds : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode) :=
  [Cmd.evaluate Api.root, Cmd.drainDue]
def startCmdsR : List RCmd := [Cmd.evaluate Api.root, Cmd.drainDue]

def frameDrive (e : NativeEff) (cmdFuel : Nat) (b : Nat := 2048) :=
  driveState (interpOf e) cmdFuel (frameLoad e 40 b) startCmds
def termDrive (e : NativeEff) (cmdFuel : Nat) (b : Nat := 2048) :=
  driveState (interpR e) cmdFuel (termLoad e 40 b) startCmdsR

def frameCount (e : NativeEff) : List Nat := (frameDrive e 400).1.fibers.map (·.currentOpCount)
def termCount (e : NativeEff) : List Nat := (termDrive e 400).1.fibers.map (·.currentOpCount)

def cap : Nat := 400
def frameCmds (e : NativeEff) : Option Nat := go cap 0
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | k + 1, i => if settled (frameDrive e i) then some i else go k (i + 1)
def termCmds (e : NativeEff) : Option Nat := go cap 0
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | k + 1, i => if settled (termDrive e i) then some i else go k (i + 1)

def frameRun (e : NativeEff) (t : List Api.Decision) (b : Nat := 2048) :=
  replayEval (interpOf e) 400 t (frameLoad e 40 b)
def termRun (e : NativeEff) (t : List Api.Decision) (b : Nat := 2048) :=
  replayEval (interpR e) 400 t (termLoad e 40 b)

def frameObs (e : NativeEff) (t : List Api.Decision := [Api.evaluate, Api.flush]) : Obs :=
  obs (frameRun e t).machine
def termObs (e : NativeEff) (t : List Api.Decision := [Api.evaluate, Api.flush]) : Obs :=
  obs (termRun e t).machine

/-- Observation, counted operations and the least settling command budget agree. -/
def lockstep (e : NativeEff) : Bool :=
  termObs e = frameObs e && termCount e = frameCount e && termCmds e = frameCmds e

def one : Term := .lit (.nat 1)
def pureSync : NativeEff := .sync one
def store : NativeEff := .perform .refMake one
def bindStore : NativeEff := .bind store (.succeed (.var 0))
def bindTwice : NativeEff := .bind store (.bind (.perform .refGet (.var 0)) (.succeed (.var 1)))
def bindSync : NativeEff := .bind pureSync (.succeed (.app "succ" (.cons (.var 0) .nil)))
def suspended : NativeEff := .suspend (.succeed one)
def skippedHandler : NativeEff := .catchCause (.succeed one) (.succeed (.lit (.nat 2)))
def takenHandler : NativeEff := .catchCause (.fail (.lit (.nat 7))) (.succeed (.lit (.nat 9)))
def matchSuccess : NativeEff :=
  .matchCause (.succeed (.lit (.nat 4))) (.succeed (.app "succ" (.cons (.var 0) .nil))) (.succeed (.lit (.nat 2)))
def matchFailure : NativeEff :=
  .matchCause (.fail (.lit (.nat 7))) (.succeed one) (.succeed (.lit (.nat 2)))
def onExitPure : NativeEff := .onExit (.succeed one) (.succeed (.lit .unit))
def onExitRef : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.onExit (.succeed one) (.perform (.refUpdate FnName.incr) (.var 0)))
      (.perform .refGet (.var 0)))
def maskedCleanup : NativeEff :=
  .onExit (.uninterruptible (.succeed one)) (.perform .refMake (.lit (.nat 9)))
def exitSucceed : NativeEff := .exit (.succeed one)
def exitFail : NativeEff := .exit (.fail (.lit (.nat 7)))
def exitSync : NativeEff := .exit pureSync
def uninterruptibleOne : NativeEff := .uninterruptible (.succeed one)
def interruptibleOne : NativeEff := .interruptible (.succeed one)
def maskedInner : NativeEff := .uninterruptible (.interruptible (.succeed one))
def branchT : NativeEff := .branch (.lit (.bool true)) (.succeed one) (.succeed (.lit (.nat 2)))
def yieldErr : NativeEff := .yieldError (.lit (.nat 3))
def getIdP : NativeEff := .withFiber .getId
def genInline : NativeEff := .gen (.cons (.bindYield (.succeed one)) (.cons (.ret (.var 0)) .nil))
def genResumed : NativeEff :=
  .gen (.cons (.bindYield store) (.cons (.bindYield (.perform .refGet (.var 0))) (.cons (.ret (.var 1)) .nil)))
def genFail : NativeEff :=
  .gen (.cons (.bindYield (.succeed one)) (.cons (.bindYield (.fail (.lit (.nat 7)))) (.cons (.ret (.var 0)) .nil)))
def genDiscard : NativeEff :=
  .gen (.cons (.yieldDiscard store) (.cons (.bindYield (.succeed (.lit (.nat 5)))) (.cons (.ret (.var 0)) .nil)))
def whileThree : NativeEff :=
  .whileLoop (.lit (.nat 0)) (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.succeed (.lit .unit))
def whileZero : NativeEff :=
  .whileLoop (.lit (.nat 5)) (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.succeed (.lit .unit))
def whileFailing : NativeEff :=
  .whileLoop (.lit (.nat 0)) (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.fail (.lit (.nat 7)))
def yieldNowThen : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat 5)))

-- The shapes of the P0 prototype, the ten local command pairs and the corrected forms.
#guard lockstep pureSync
#guard lockstep store
#guard lockstep bindStore
#guard lockstep bindTwice
#guard lockstep bindSync
#guard lockstep suspended
#guard lockstep skippedHandler
#guard lockstep takenHandler
#guard lockstep matchSuccess
#guard lockstep matchFailure
#guard lockstep onExitPure
#guard lockstep onExitRef
#guard lockstep maskedCleanup
#guard lockstep exitSucceed
#guard lockstep exitFail
#guard lockstep exitSync
#guard lockstep uninterruptibleOne
#guard lockstep interruptibleOne
#guard lockstep maskedInner
#guard lockstep branchT
#guard lockstep yieldErr
#guard lockstep getIdP
#guard lockstep genInline
#guard lockstep genResumed
#guard lockstep genFail
#guard lockstep genDiscard
#guard lockstep whileThree
#guard lockstep whileZero
#guard lockstep whileFailing
#guard lockstep yieldNowThen
#guard lockstep scopedContext
#guard lockstep Test.Syntax.CompileContract.pGenLoop
#guard lockstep Test.Syntax.CompileContract.pWhileLoop
#guard lockstep Test.Syntax.CompileContract.pGenTwoYields
#guard lockstep Test.Syntax.CompileContract.pScoped
#guard lockstep Test.Syntax.CompileContract.pForkJoin
#guard lockstep Test.Syntax.CompileContract.pDeferred
#guard lockstep Test.Syntax.CompileContract.pRace

-- The host's counts on the corrected shapes (`host-results.json`): the folded exit is
-- one primitive, the generator and the loop carry their suspend wrapper.
#guard termCount exitSucceed = [1] ∧ termCount exitFail = [1] ∧ termCount exitSync = [3]
#guard termCount genInline = [3] ∧ termCount genResumed = [5] ∧ termCount genFail = [3]
#guard termCount whileThree = [6] ∧ termCount whileZero = [3] ∧ termCount whileFailing = [3]

-- The audit's ten local command pairs now agree; the store's answer slot is gone.
#guard (frameCmds pureSync, termCmds pureSync) = (some 6, some 6)
#guard (frameCmds store, termCmds store) = (some 7, some 7)
#guard (frameCmds bindStore, termCmds bindStore) = (some 9, some 9)
#guard (frameCmds bindTwice, termCmds bindTwice) = (some 13, some 13)
#guard (frameCmds skippedHandler, termCmds skippedHandler) = (some 6, some 6)
#guard (frameCmds onExitPure, termCmds onExitPure) = (some 9, some 9)
#guard frameCount store = [1] ∧ termCount store = [1]

/-- Handler entry is a counted step on both machines (the checkpoint audit's finding). -/
theorem entry_is_counted : frameCount skippedHandler = [2] ∧ termCount skippedHandler = [2] :=
  ⟨rfl, rfl⟩

def parkedRoot {κ φ η : Type}
    (r : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ φ η) :
    Option Parked := (r.machine.fiber? Api.root).map RunFiber.parked
def rootExit {κ φ η : Type}
    (r : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ φ η) :
    Option ExitV := (r.machine.fiber? Api.root).bind RunFiber.exit

-- Budget two: sync exits, suspend and the skipped catch park on both machines; the
-- folded exit finishes, as the host does.
#guard rootExit (termRun pureSync [Api.evaluate] 2) = some (.success (.nat 1))
#guard rootExit (termRun suspended [Api.evaluate] 2) = none
#guard parkedRoot (termRun suspended [Api.evaluate] 2) = some (.withGuard 0)
#guard rootExit (termRun suspended [Api.evaluate, Api.flush] 2) = some (.success (.nat 1))
#guard rootExit (termRun skippedHandler [Api.evaluate] 2) = none
#guard rootExit (frameRun skippedHandler [Api.evaluate] 2) = none
#guard rootExit (termRun exitSucceed [Api.evaluate] 2) = some (.success (.exitOk (.nat 1)))
#guard rootExit (frameRun exitSucceed [Api.evaluate] 2) = some (.success (.exitOk (.nat 1)))

-- The wave-2 audit's scheduling witnesses: a context budget of six supplied through
-- Completion, then a sync; both machines now finish.
def withBudgetProgram : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.callback .deferredAwait (.var 0))
      (.bind (.withFiber (.setContext (.var 1))) (.sync (.lit (.nat 5)))))
def budgetTape (n : Nat) : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.context ⟨none, n, false⟩)))]
#guard rootExit (frameRun withBudgetProgram (budgetTape 6)) = some (.success (.nat 5))
#guard rootExit (termRun withBudgetProgram (budgetTape 6)) = some (.success (.nat 5))
#guard termObs withBudgetProgram (budgetTape 6) = frameObs withBudgetProgram (budgetTape 6)

-- A chain of allocations long enough to cross the default budget (two counted steps per
-- allocation, 1100 of them) yields at the same point on both machines, with the same
-- heap so far, and finishes after the flush with the whole heap.
def chain : Nat → NativeEff
  | 0 => .succeed (.lit .unit)
  | n + 1 => .bind (.perform .refMake (.lit (.nat n))) (chain n)
def chainRun (n fuel cmdFuel : Nat) (t : List Api.Decision) :=
  (obs (replayEval (interpOf (chain n)) cmdFuel t (Api.load (chain n) fuel)).machine,
   obs (replayEval (interpR (chain n)) cmdFuel t (loadR (chain n) fuel)).machine)
#guard (chainRun 1100 1200 8000 [Api.evaluate]).1 = (chainRun 1100 1200 8000 [Api.evaluate]).2
#guard (chainRun 1100 1200 8000 [Api.evaluate]).2.exits = [(Api.root, none)]
-- Counts one to 2047 run before the injected yield; the allocations sit at the even counts.
#guard (chainRun 1100 1200 8000 [Api.evaluate]).2.stores.refs.length = 1023
#guard (chainRun 1100 1200 8000 [Api.evaluate, Api.flush]).1 =
  (chainRun 1100 1200 8000 [Api.evaluate, Api.flush]).2
#guard (chainRun 1100 1200 8000 [Api.evaluate, Api.flush]).2.stores.refs.length = 1100

-- Scanner exhaustion and the compile frontier stay unanswered on the term.
#guard rootExit (replayEval (interpR genInline) 400 [Api.evaluate] (termLoad genInline 1)) = none
#guard (replayEval (interpR genInline) 400 [Api.evaluate] (termLoad genInline 1)).machine.stuck = none
#guard rootExit (replayEval (interpR pureSync) 400 [Api.evaluate] (termLoad pureSync 0)) = none

end Lockstep

/-! ## The local relation, inhabited on the store step

The commands of one iteration with their code erased: the residual work both sides leave
for the shared loop, compared shape by shape. `store_step_rel` says that on a store
`sync` the frame machine's counted step and the term's agree on the outcome, the residual
commands and the store, for every machine, fiber and continuation with equal stores. -/

inductive CmdShape
  | evaluate (fiber : FiberId)
  | loop (fiber : FiberId) (yielding : Bool)
  | deliver (fiber : FiberId) (yielding : Bool)
  | finish (fiber : FiberId) (exit : ExitV)
  | resume (fiber : FiberId) (token : Nat)
  | launch (race : Nat)
  | link (scope : Nat) (key : Nat) (target : FiberId)
  | drainDue
deriving DecidableEq

def cmdShape {κ : Type} : Cmd EffName EffThunk Val Err Defect FiberId Ann κ → CmdShape
  | .evaluate id => .evaluate id
  | .loop id y => .loop id y
  | .deliver id y => .deliver id y
  | .finish id ex => .finish id ex
  | .resume id token _ => .resume id token
  | .launch race => .launch race
  | .link _ scope key target _ _ => .link scope key target
  | .drainDue => .drainDue

def frameStoreStep (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (op : SyncOp) (y : Bool) :
    Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores :=
  evaluatePrim (interpOf root) m { f with frame := { f.frame with current := Prim.sync (EffThunk.op op) } } y

def termStoreStep (root : NativeEff) (m' : RState) (f' : RFiber) (op : SyncOp)
    (k : Val → RProgram) (y : Bool) : RIter :=
  evaluateR (interpR root) m' { f' with frame := { f'.frame with current := .vis (.inl op) k } } y

theorem store_step_rel (root : NativeEff) (m : Api.Machine) (m' : RState)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (f' : RFiber)
    (op : SyncOp) (k : Val → RProgram) (y : Bool) (hs : m.state = m'.state) :
    (frameStoreStep root m f op y).outcome = (termStoreStep root m' f' op k y).outcome ∧
    (frameStoreStep root m f op y).nested.map cmdShape =
      (termStoreStep root m' f' op k y).nested.map cmdShape ∧
    (frameStoreStep root m f op y).machine.state = (termStoreStep root m' f' op k y).machine.state := by
  unfold frameStoreStep termStoreStep
  simp only [evaluatePrim, evaluateR, interpOf]
  rw [hs]
  rcases syncOpStep op m'.state with _ | ⟨state, value⟩ <;> simp [cmdShape, hs]

-- The loaded state uses the existing generic observation and first-order tape.
example (program : NativeEff) (fuel : Nat) (choices : List Bool) :
    obsR (loadR program fuel choices) = ⟨[(Api.root, none)], Stores.empty⟩ :=
  obsR_load program fuel choices

example (program : NativeEff) (answer : Completion Val Err Defect FiberId Ann) :
    (interpR program).answerCode answer = denoteCompletion answer :=
  interpR_answerCode program answer

end Test.Program.RuntimeRContract
