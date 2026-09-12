import Effect4.Laws.Program.RuntimeR
import Test.Program.RuntimeRReference

/-!
# R3/R4 finite term/frame comparisons

Packet: `Test/contracts/program-runtime-r.contract.md`. Every comparison uses
the source, budget 120 and literal decision tape from RuntimeRReference. The
reference module separately pins expected exits, stores and waiting states.
These finite checks do not prove R5, general simulation or host correspondence.

The comparison includes all exits and complete stores (including Deferred
waiters and due resumes), replay outcome, parking, interrupt causes, deferred
flags, contexts, and allocation counters. Interruptibility is compared on every
fiber. It omits saved code, stack representation, trace, and local step counts.

The repaired `finishFrame` retains the final pop's saved state, including the
mask while `Cmd.finish` is still pending. Control comparison includes masks
on both live and exited fibers; it still omits the representation of code and
stacks, which the P3 relation must supply.
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
  interruptible : Bool
  interruptedCause : Option CauseV
  deferredInterrupt : Bool
  context : Ctx
deriving DecidableEq

def frameControl (m : Api.Machine) : List FiberControl :=
  m.fibers.map fun f => ⟨f.id, f.parked,
    f.frame.interruptible,
    f.frame.interruptedCause, f.frame.deferredInterrupt, f.context⟩

def termControl (m : RState) : List FiberControl :=
  m.fibers.map fun f => ⟨f.id, f.parked,
    f.frame.interruptible,
    f.frame.interruptedCause, f.frame.deferredInterrupt, f.context⟩

def termOutcome : RReplay → Api.Outcome
  | .finished _ => .finished
  | .frontier _ _ => .frontier
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

-- 14. Compile exhaustion leaves a live frontier.
def termCompileZero : RReplay :=
  replayEval (interpR compileZeroProg) budget startTape (loadR compileZeroProg 0)

#guard obsR termCompileZero.machine = obs compileZero.machine
#guard termControl termCompileZero.machine = frameControl compileZero.machine
#guard termOutcome termCompileZero = .frontier

-- The final pop retains the restored mask, including after fiber exit.
#guard RuntimeRReference.interruptible (RuntimeRReference.run waiting failureTape) = some true
#guard ((replayR waiting budget failureTape).machine.fiber? Api.root).map
  (fun f => f.frame.interruptible) = some true
#guard RuntimeRReference.interruptible (RuntimeRReference.run scopedContext startTape) = some true
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

theorem frame_runIn (target : FiberId) (scope : Nat) :
    evaluatePrim.withFiber interp m f y (.runIn target scope) =
      FiberAction.runIn interp m f y target scope := rfl

theorem frame_fork (program : NCode) (options : Supervision.ForkOptions) :
    evaluatePrim.withFiber interp m f y (.fork program options) =
      FiberAction.fork interp m f y program options := rfl

theorem frame_forkIn (program : NCode) (options : Supervision.ForkOptions) (scope : Nat) :
    evaluatePrim.withFiber interp m f y (.forkIn program options scope) =
      FiberAction.forkIn interp m f y program options scope := rfl

theorem frame_forkScoped (program : NCode) (options : Supervision.ForkOptions) :
    evaluatePrim.withFiber interp m f y (.forkScoped program options) =
      FiberAction.forkScoped interp m f y program options := rfl

theorem frame_refuse (cause : CauseV) :
    evaluatePrim.withFiber interp m f y (.refuse cause) = FiberAction.refuse m f y cause := rfl

theorem frame_closeScope (scope : Nat) (exit : ExitV) :
    evaluatePrim.withFiber interp m f y (.closeScope scope exit) =
      FiberAction.closeScope interp m f y scope exit := by
  rcases hc : interp.closeScope scope exit f.frame.interruptible f.id m.state with _ | ⟨state, program⟩ <;>
    simp only [evaluatePrim.withFiber, FiberAction.closeScope, FiberCore.interruptible, frameCore, hc]

-- D6b: the public interrupt answers the `fiberInterruptAs` program; that program's arm records
-- and delegates; the scoped finalizer answers void on itself, else the public program.
theorem frame_interrupt (target : FiberId) :
    evaluatePrim.withFiber interp m f y (.interrupt target) =
      FiberAction.interrupt interp m f y target := rfl

theorem frame_interruptAs (target who : FiberId) :
    evaluatePrim.withFiber interp m f y (.interruptAs target who) =
      FiberAction.interruptAs interp m f y target who := by
  rcases hm : m.fiber? target with _ | t <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, FiberAction.interruptAs, hm]

theorem frame_interruptScoped (target : FiberId) :
    evaluatePrim.withFiber interp m f y (.interruptScoped target) =
      FiberAction.interruptScoped interp m f y target := by
  by_cases h : target = f.id
  · simp only [evaluatePrim.withFiber, FiberAction.interruptScoped, FiberAction.coreAnswer,
      FiberCore.answerWith, FiberCore.success, frameCore, h, ↓reduceIte]
  · simp only [evaluatePrim.withFiber, FiberAction.interruptScoped, FiberCore.answerWith, frameCore, h,
      ↓reduceIte]

-- §20: the `Scope` service read answers the handle or dies; the parallel close's step
-- delegates to the shared forks and the await command
theorem frame_ambientScope :
    evaluatePrim.withFiber interp m f y .ambientScope = FiberAction.ambientScope interp m f y := by
  rcases h : interp.ambientScope f.context with _ | scope <;>
    simp only [evaluatePrim.withFiber, FiberAction.ambientScope, FiberAction.coreAnswer,
      FiberCore.answerWith, FiberCore.success, FiberCore.failure, frameCore, h]

theorem frame_closePar (finalizers : List NCode) :
    evaluatePrim.withFiber interp m f y (.closePar finalizers) =
      FiberAction.closePar interp m f y finalizers := rfl

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
  · simp only [evaluatePrim.withFiber, FiberAction.cancelRace, hr]

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
  fs.map fun f => { f with maxOpsBeforeYield := b, context := emptyCtx.provide Env.maxOpsKey (.nat b) }

def frameLoad (e : NativeEff) (fuel : Nat := 40) (b : Nat := 2048) : Api.Machine :=
  { Api.load e fuel with fibers := withBudget (Api.load e fuel).fibers b }

def termLoad (e : NativeEff) (fuel : Nat := 40) (b : Nat := 2048) : RState :=
  { loadR e fuel with fibers := withBudget (loadR e fuel).fibers b }

def startCmds : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode) :=
  [Cmd.evaluate Api.root, Cmd.drainDue]
def startCmdsR : List RCmd := [Cmd.evaluate Api.root, Cmd.drainDue]

def frameDrive (e : NativeEff) (cmdFuel : Nat) (b : Nat := 2048) :=
  letI := evaluatorFor e
  driveState (interpOf e) cmdFuel (frameLoad e 40 b) startCmds
def termDrive (e : NativeEff) (cmdFuel : Nat) (b : Nat := 2048) :=
  letI := termEvaluatorFor e
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
  letI := evaluatorFor e
  replayEval (interpOf e) 400 t (frameLoad e 40 b)
def termRun (e : NativeEff) (t : List Api.Decision) (b : Nat := 2048) :=
  letI := termEvaluatorFor e
  replayEval (interpR e) 400 t (termLoad e 40 b)

def frameObs (e : NativeEff) (t : List Api.Decision := [Api.evaluate, Api.flush]) : Obs :=
  obs (frameRun e t).machine
def termObs (e : NativeEff) (t : List Api.Decision := [Api.evaluate, Api.flush]) : Obs :=
  obs (termRun e t).machine

/-- Observation, counted operations and the least settling command budget agree. -/
def lockstep (e : NativeEff) : Bool :=
  termObs e = frameObs e && termCount e = frameCount e && termCmds e = frameCmds e

-- E4-CHECK-CE-005: source construction can fold a completed join. A join
-- constructed while live keeps its Async form through a later mask/fork entry.
def constructionChild : NativeEff := .succeed (.lit (.nat 42))
def constructionFork (immediate : Bool) : NativeEff :=
  .withFiber (.fork constructionChild { immediateDaemon with startImmediately := immediate })
def constructionJoin : NativeEff := .awaitFiber (.var 0) .joinEffect
def constructionDirect : NativeEff := .bind (constructionFork true) constructionJoin
def constructionGen : NativeEff := .bind (constructionFork true)
  (.gen (.cons (.bindYield constructionJoin) (.cons (.ret (.var 1)) .nil)))
def constructionExit : NativeEff := .bind (constructionFork true) (.exit constructionJoin)
def constructionLive : NativeEff := .bind (constructionFork false) constructionJoin
def constructionMask : NativeEff := .bind (constructionFork false) (.uninterruptible constructionJoin)
def constructionForkBody : NativeEff := .bind (constructionFork false)
  (.withFiber (.fork constructionJoin immediateDaemon))

def constructionRows : List NativeEff :=
  [constructionDirect, constructionGen, constructionExit,
   constructionLive, constructionMask, constructionForkBody]

#guard constructionRows.all (fun e => Api.wellTyped e && Api.readable e)
#guard constructionRows.all lockstep
#guard [constructionDirect, constructionGen, constructionExit].map frameCount = [[4, 1], [6, 1], [4, 1]]

def constructionViewsAgree : Bool := constructionRows.all fun e =>
  [2048, 4, 6].all fun b => [[Api.evaluate], [Api.evaluate, Api.flush]].all fun tape =>
    let frame := (frameRun e tape b).machine
    let term := (termRun e tape b).machine
    obs frame = obs term && frameControl frame = termControl term &&
      frame.fibers.map (·.currentOpCount) = term.fibers.map (·.currentOpCount)

#guard constructionViewsAgree

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

-- E4-CHECK-CE-009: source OnExit pays an ordinary success frame, and only
-- a failed body adds the failure frame that combines a failing cleanup.
def finalizerTimingRows : List NativeEff :=
  [.onExit (.succeed one) (.succeed (.lit .unit)),
   .onExit (.fail one) (.succeed (.lit .unit)),
   .onExit (.succeed one) (.fail (.lit (.nat 2))),
   .onExit (.fail one) (.fail (.lit (.nat 2)))]

theorem finalizer_success_code (root : NativeEff) (value : Val) (code : NCode) :
    finalizerCode (interpOf root) (.success value) code =
      Prim.onSuccess code (.restore (.success value)) := rfl

theorem finalizer_failure_code (root : NativeEff) (cause : CauseV) (code : NCode) :
    finalizerCode (interpOf root) (.failure cause) code =
      Prim.onSuccess (Prim.onFailure code (.merge (.failure cause)))
        (.restore (.failure cause)) := rfl

#guard finalizerTimingRows.all (fun e => Api.wellTyped e && Api.readable e)
#guard finalizerTimingRows.all lockstep
#guard finalizerTimingRows.map frameCount = [[5], [6], [4], [6]]
#guard finalizerTimingRows.map termCount = [[5], [6], [4], [6]]

def finalizerTimingViews : Bool := finalizerTimingRows.all fun e =>
  [2048, 4, 6].all fun b => [[Api.evaluate], [Api.evaluate, Api.flush]].all fun tape =>
    let frame := (frameRun e tape b).machine
    let term := (termRun e tape b).machine
    obs frame = obs term && frameControl frame = termControl term &&
      frame.fibers.map (·.currentOpCount) = term.fibers.map (·.currentOpCount) &&
      (letI := evaluatorFor e
       Suffices (interpOf e) 400 tape (frameLoad e 40 b)) &&
      (letI := termEvaluatorFor e
       Suffices (interpR e) 400 tape (termLoad e 40 b))

#guard finalizerTimingViews
#guard ((frameRun (.onExit (.fail one) (.succeed (.lit .unit))) [Api.evaluate] 6).machine.fiber?
  Api.root).map (·.exit) = some none
#guard ((termRun (.onExit (.fail one) (.succeed (.lit .unit))) [Api.evaluate] 6).machine.fiber?
  Api.root).map (·.exit) = some none

-- E4-CHECK-CE-004: entry allocates and installs context in one WithFiber;
-- empty close restores it during the body's delivery and returns no effect.
def scopedTimingRows : List NativeEff :=
  [.scoped (.succeed one), .scoped (.fail one),
   .scoped (.scoped (.succeed one)),
   .bind (constructionFork false) (.scoped constructionJoin),
   .bind (constructionFork true) (.scoped constructionJoin)]

#guard scopedTimingRows.all (fun e => Api.wellTyped e && Api.readable e)
#guard scopedTimingRows.all lockstep
#guard (scopedTimingRows.take 3).map frameCount = [[4], [4], [7]]
#guard (scopedTimingRows.take 3).map termCount = [[4], [4], [7]]

def scopedTimingViews : Bool := scopedTimingRows.all fun e =>
  [2048, 4, 6].all fun b => [[Api.evaluate], [Api.evaluate, Api.flush]].all fun tape =>
    let frame := (frameRun e tape b).machine
    let term := (termRun e tape b).machine
    obs frame = obs term && frameControl frame = termControl term &&
      frame.fibers.map (·.context) = term.fibers.map (·.context) &&
      frame.fibers.map (·.currentOpCount) = term.fibers.map (·.currentOpCount) &&
      (letI := evaluatorFor e
       Suffices (interpOf e) 400 tape (frameLoad e 40 b)) &&
      (letI := termEvaluatorFor e
       Suffices (interpR e) 400 tape (termLoad e 40 b))

#guard scopedTimingViews

/-- Finite command-prefix checks also compare the state before settlement,
including allocation and context restoration in their source-defined step. -/
def scopedPrefixViews : Bool := scopedTimingRows.all fun e =>
  (List.range 80).all fun fuel =>
    let frame := (frameDrive e fuel).1
    let term := (termDrive e fuel).1
    obs frame = obs term && frameControl frame = termControl term &&
      frame.fibers.map (·.context) = term.fibers.map (·.context) &&
      frame.fibers.map (·.currentOpCount) = term.fibers.map (·.currentOpCount)

#guard scopedPrefixViews
#guard ((frameRun (.scoped (.succeed one)) [Api.evaluate] 4).machine.fiber? Api.root).map (·.exit) =
  some none
#guard ((termRun (.scoped (.succeed one)) [Api.evaluate] 4).machine.fiber? Api.root).map (·.exit) =
  some none
#guard ((frameRun (.scoped (.scoped (.succeed one))) [Api.evaluate]).machine.fiber?
  Api.root).map (·.context) = some emptyCtx
#guard (frameRun (.scoped (.scoped (.succeed one))) [Api.evaluate]).machine.state.scopes.entries.all
  (fun entry => entry.scope.isClosed)

/-- A completing store thunk must run its waiter before the scoped callback:
the waiter interrupts this still-running owner, so the scope closes with that
interruption rather than the thunk's success. -/
def scopedCompletionInterrupt : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork
      (.scoped (.perform .deferredSucceed (.app "pair" (.cons (.var 0) (.cons one .nil)))))
      { immediateDaemon with startImmediately := false }))
      (.bind (.withFiber (.fork
        (.bind (.callback .deferredAwait (.var 0)) (.withFiber (.interrupt (.var 1))))
        immediateDaemon))
        (.awaitFiber (.var 1) .joinEffect)))

#guard Api.wellTyped scopedCompletionInterrupt && Api.readable scopedCompletionInterrupt
#guard lockstep scopedCompletionInterrupt
#guard (frameRun scopedCompletionInterrupt [Api.evaluate, Api.flush]).machine.state.scopes.status 0 =
  some (some (Witnesses.interruptedWith ⟨2⟩ ⟨1⟩ (stores.stackAnnotations ⟨2⟩)))
#guard (termRun scopedCompletionInterrupt [Api.evaluate, Api.flush]).machine.state.scopes.status 0 =
  some (some (Witnesses.interruptedWith ⟨2⟩ ⟨1⟩ (stores.stackAnnotations ⟨2⟩)))

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
/-- E4-CHECK-CE-010: Effect.fiberId is a number, so admitted arithmetic can use it.
Pinned `internal/effect.ts:1092–1100`. Logical root ID is Api.root = 0. -/
def getIdSucc : NativeEff := .bind getIdP
  (.succeed (.app "succ" (.cons (.var 0) .nil)))
#guard Api.wellTyped getIdSucc && Api.readable getIdSucc
#guard (Api.replay getIdSucc 100 [Api.evaluate]).exit = some (.success (.nat 1))
#guard (obsR (replayR getIdSucc 100 [Api.evaluate]).machine).exits =
  [(Api.root, some (.success (.nat 1)))]
#guard lockstep getIdSucc

/-- The optional interruptor is numeric provenance, including unallocated IDs.
The snapshot operation is admitted but lies outside the printer profile. -/
def numericInterruptor : NativeEff := .bind (.withFiber .snapshotChildren)
  (.withFiber (.interruptAll (.var 0) (some (.lit (.nat 99)))))
#guard Api.wellTyped numericInterruptor
#guard (Api.replay numericInterruptor 100 [Api.evaluate]).exit = some (.success .unit)
#guard (obsR (replayR numericInterruptor 100 [Api.evaluate]).machine).exits =
  [(Api.root, some (.success .unit))]

theorem native_id_value (root : NativeEff) (fiber : FiberId) :
    (interpOf root).fiberIdValue fiber = Val.nat fiber.value ∧
    (interpR root).fiberIdValue fiber = Val.nat fiber.value ∧
    (interpOf root).fiberValue fiber = Val.fiber fiber ∧
    (interpR root).fiberValue fiber = Val.fiber fiber := ⟨rfl, rfl, rfl, rfl⟩
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

-- E4-CHECK-CE-008: an outer source suspension returns the child's full code.
-- Actual Api.print output on rc.112 counts both suspensions; source evidence is
-- docs/research/probes/p012-review/emitted-host-results.json at acfc2fc.
#guard Api.wellTyped (.suspend genInline)
#guard Api.wellTyped (.suspend whileThree)
#guard Api.wellTyped (.suspend branchT)
#guard lockstep (.suspend genInline)
#guard lockstep (.suspend whileThree)
#guard lockstep (.suspend branchT)
#guard frameCount (.suspend genInline) = [4]
#guard frameCount (.suspend whileThree) = [7]
#guard frameCount (.suspend branchT) = [3]

-- D6a/D6b (source-repairs §§16, 19): the pinned host counts of `probes/p3-d6/host-d6b.json`
-- on the race and interrupt rows, agreed by both models — the winner-time cleanup
-- (`raceWinner`, `capturedLiveRace`), the public interrupt's `fiberInterruptAs` return
-- (`interruptDone`, `interruptLive`), ordered interrupt-all with its `asVoid(fiberAwaitAll)`
-- return (`interruptAllDone`, `orderedInterrupt`) and the counted child-exit middleware
-- entry (`middlewareChild`).
#guard lockstep Test.Program.RuntimeRReference.raceWinner
#guard lockstep Test.Program.RuntimeRReference.interruptDone
#guard lockstep Test.Program.RuntimeRReference.interruptLive
#guard lockstep Test.Program.RuntimeRReference.interruptAllDone
#guard lockstep Test.Program.RuntimeRReference.orderedInterrupt
#guard lockstep Test.Program.RuntimeRReference.middlewareChild
#guard frameCount Test.Program.RuntimeRReference.raceWinner = [12, 4, 1]
#guard frameCount Test.Program.RuntimeRReference.interruptDone = [8, 1]
#guard frameCount Test.Program.RuntimeRReference.interruptLive = [8, 1]
#guard frameCount Test.Program.RuntimeRReference.interruptAllDone = [11, 1, 1]
#guard frameCount Test.Program.RuntimeRReference.orderedInterrupt = [15, 8, 1]
#guard frameCount Test.Program.RuntimeRReference.middlewareChild = [7, 4]

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

/-- The saved final-pop state is retained before the exit command commits it. -/
theorem finished_pop_state (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (y : Bool)
    (ex : ExitV) (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (nested : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) :
    evaluatePrim.finishFrame m f y (.finished ex) events nested =
      ⟨m.emit (events.map (RunEvent.frame f.id)),
        { f with frame := frameExitState f.frame }, y, .finished ex, nested⟩ := rfl

/-- The old terminal-only mask exception missed this live, unfinished command
boundary (`E4-RTERM-CE-005`). Both machines now retain the completed pop. -/
theorem pending_finish_controls :
    (frameDrive uninterruptibleOne 3).1.fibers.map (·.frame.interruptible) = [true] ∧
    (termDrive uninterruptibleOne 3).1.fibers.map (·.frame.interruptible) = [true] ∧
    (frameDrive uninterruptibleOne 3).1.fibers.map (·.frame.stack.isEmpty) = [true] ∧
    (termDrive uninterruptibleOne 3).1.fibers.map (·.frame.stack.isEmpty) = [true] ∧
    (frameDrive uninterruptibleOne 3).1.fibers.map (·.frame.deferredInterrupt) = [false] ∧
    (termDrive uninterruptibleOne 3).1.fibers.map (·.frame.deferredInterrupt) = [false] ∧
    (frameDrive uninterruptibleOne 3).1.fibers.map (·.exit) = [none] ∧
    (termDrive uninterruptibleOne 3).1.fibers.map (·.exit) = [none] ∧
    (frameDrive uninterruptibleOne 3).2 = [.finish Api.root (.success (.nat 1)), .drainDue] ∧
    (termDrive uninterruptibleOne 3).2 = [.finish Api.root (.success (.nat 1)), .drainDue] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms finished_pop_state
#print axioms pending_finish_controls

-- The old frame compiler finished this source at budget 7 while the term and host
-- parked. Equal sufficient command budgets now retain the same live observation.
#guard rootExit (frameRun (.suspend whileThree) [Api.evaluate] 7) = none
#guard rootExit (termRun (.suspend whileThree) [Api.evaluate] 7) = none
#guard obs (frameRun (.suspend whileThree) [Api.evaluate] 7).machine =
  obsR (termRun (.suspend whileThree) [Api.evaluate] 7).machine

-- Budget two: sync exits, suspend and the skipped catch park on both machines; the
-- folded exit finishes, as the host does.
#guard rootExit (termRun pureSync [Api.evaluate] 2) = some (.success (.nat 1))
#guard rootExit (termRun suspended [Api.evaluate] 2) = none
#guard parkedRoot (termRun suspended [Api.evaluate] 2) = some (.withGuard 0)
-- At this small budget the resume answer spends count one; count two injects
-- again before the saved Success. The finite flush reaches its live frontier.
#guard rootExit (termRun suspended [Api.evaluate, Api.flush] 2) = none
#guard rootExit (frameRun suspended [Api.evaluate, Api.flush] 2) = none
#guard (frameDrive suspended 400 2).1.fibers.map (·.currentOpCount) = [3]
#guard (termDrive suspended 400 2).1.fibers.map (·.currentOpCount) = [3]
#guard (frameDrive suspended 400 1).1.fibers.map (·.currentOpCount) = [2]
#guard (termDrive suspended 400 1).1.fibers.map (·.currentOpCount) = [2]
#guard obs (frameRun suspended [Api.evaluate, Api.flush] 2).machine =
  obsR (termRun suspended [Api.evaluate, Api.flush] 2).machine
#guard rootExit (termRun skippedHandler [Api.evaluate] 2) = none
#guard rootExit (frameRun skippedHandler [Api.evaluate] 2) = none
#guard rootExit (termRun exitSucceed [Api.evaluate] 2) = some (.success (.exitOk (.nat 1)))
#guard rootExit (frameRun exitSucceed [Api.evaluate] 2) = some (.success (.exitOk (.nat 1)))

-- An interrupt above an injected yield still runs cleanup and skips the outer
-- cause handler while interruption remains pending (internal/core.ts:539-545).
def injectedCleanup : NativeEff :=
  .onExit (.suspend (.succeed (.lit (.nat 1)))) (.perform .refMake (.lit (.nat 9)))
def injectedCaught : NativeEff := .catchCause injectedCleanup (.succeed (.lit (.nat 99)))
def injectedInterruptTape : List Api.Decision :=
  [Api.evaluate, .interruptFrom (some ⟨1⟩) ReasonAnnotations.empty Api.root, Api.flush]
#guard Api.wellTyped injectedCleanup && Api.wellTyped injectedCaught
#guard rootExit (frameRun injectedCleanup injectedInterruptTape 3) =
  some (Witnesses.interruptedBy ⟨1⟩ Api.root)
#guard rootExit (termRun injectedCleanup injectedInterruptTape 3) =
  some (Witnesses.interruptedBy ⟨1⟩ Api.root)
#guard (frameRun injectedCleanup injectedInterruptTape 3).machine.state.refs = [.nat 9]
#guard obs (frameRun injectedCleanup injectedInterruptTape 3).machine =
  obsR (termRun injectedCleanup injectedInterruptTape 3).machine
#guard rootExit (frameRun injectedCaught injectedInterruptTape 4) =
  some (Witnesses.interruptedBy ⟨1⟩ Api.root)
#guard rootExit (termRun injectedCaught injectedInterruptTape 4) =
  some (Witnesses.interruptedBy ⟨1⟩ Api.root)
#guard (frameRun injectedCaught injectedInterruptTape 4).machine.state.refs = [.nat 9]
#guard obs (frameRun injectedCaught injectedInterruptTape 4).machine =
  obsR (termRun injectedCaught injectedInterruptTape 4).machine

-- The wave-2 audit's scheduling witnesses: a context budget of six supplied through
-- Completion, then a sync; both machines now finish.
def withBudgetProgram : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.callback .deferredAwait (.var 0))
      (.bind (.withFiber (.setContext (.var 1))) (.sync (.lit (.nat 5)))))
def budgetTape (n : Nat) : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0
    (.ofExit (.success (.context (emptyCtx.provide Env.maxOpsKey (.nat n)))))]
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
  | enrollRace (race : Nat) (child : FiberId)
  | registrationDone (race : Nat) (yielding : Bool)
  | interruptTarget (target : FiberId) (who : Option FiberId)
  | afterInterrupt (host : FiberId) (yielding : Bool) (kind : ParkKind)
  | raceCancel (race : Nat) (host : FiberId) (yielding : Bool) (remaining visited : List FiberId)
  | trackChild (parent child : FiberId)
  | observe (fiber : FiberId) (exit : ExitV) (observer : Observer)
  | exitDone (fiber : FiberId)
  | closeParAwait (host : FiberId) (yielding : Bool) (fibers : List FiberId)
  | link (scope : Nat) (target : FiberId)
  | drainDue
  | wake (list : WakeKey) (phase : WakePhase)
deriving DecidableEq

def cmdShape {κ : Type} : Cmd EffName EffThunk Val Err Defect FiberId Ann κ → CmdShape
  | .evaluate id => .evaluate id
  | .loop id y => .loop id y
  | .deliver id y => .deliver id y
  | .finish id ex => .finish id ex
  | .resume id token _ => .resume id token
  | .launch race => .launch race
  | .enrollRace race child => .enrollRace race child
  | .registrationDone race y => .registrationDone race y
  | .interruptTarget target who _ => .interruptTarget target who
  | .afterInterrupt host y kind => .afterInterrupt host y kind
  | .raceCancel race host y remaining visited => .raceCancel race host y remaining visited
  | .trackChild parent child => .trackChild parent child
  | .observe fiber ex observer => .observe fiber ex observer
  | .exitDone fiber => .exitDone fiber
  | .closeParAwait host y fibers => .closeParAwait host y fibers
  | .link _ scope target _ _ => .link scope target
  | .drainDue => .drainDue
  | .wake list phase => .wake list phase

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
  simp only [evaluatePrim, evaluateR, evaluateRawR, prepareR, answerR, interpOf]
  rw [hs]
  rcases syncOpStep op m'.state with _ | ⟨state, value⟩ <;> simp [prepareIterR, cmdShape, hs]

-- The loaded state uses the existing generic observation and first-order tape.
example (program : NativeEff) (fuel : Nat) (choices : List Bool) :
    obsR (loadR program fuel choices) = ⟨[(Api.root, none)], Stores.empty⟩ :=
  obsR_load program fuel choices

example (program : NativeEff) (answer : Completion Val Err Defect FiberId Ann) :
    (interpR program).answerCode answer = denoteCompletion answer :=
  interpR_answerCode program answer

/-! ## D6a/D6b: a deferred interrupt recorded during a race's registration

`internal/effect.ts:662-667`: when the registration returns `Yield` but a nested run
recorded a deferred interrupt, the host clears its yield guard and continues the same entry
through the next loop top, which fails it with the recorded cause; the cancel frame the
registration pushed is still on the stack and runs. No emitted program can interrupt its
own host from inside the registration, so this row is assembled by hand: the empty race is
driven until its registration is about to return (the queue head is `registrationDone`),
the interrupt is recorded on the running host, and the drive continues. -/

section DeferredRegistration

def raceEmptyRegistering :=
  letI := evaluatorFor Test.Program.RuntimeRReference.raceEmpty
  driveState (interpOf Test.Program.RuntimeRReference.raceEmpty) 4
    (frameLoad Test.Program.RuntimeRReference.raceEmpty 40 2048) startCmds

-- the host is running its entry, unparked, two counted ops in (`WithFiber`, `Async`), and the
-- registration's return is the next command
#guard raceEmptyRegistering.2.map cmdShape = [.registrationDone 0 false, .drainDue]
#guard (raceEmptyRegistering.1.fiber? Api.root).map
  (fun f => (f.running, f.frame.deferredInterrupt, f.parked, f.currentOpCount)) =
    some (true, false, .notParked, 2)

def raceEmptyDeferred :=
  letI := evaluatorFor Test.Program.RuntimeRReference.raceEmpty
  match raceEmptyRegistering.1.fiber? Api.root with
  | none => raceEmptyRegistering
  | some host =>
    let recorded := interruptRecord (interpOf Test.Program.RuntimeRReference.raceEmpty) (some ⟨9⟩)
      ReasonAnnotations.empty host
    driveState (interpOf Test.Program.RuntimeRReference.raceEmpty) 400
      (raceEmptyRegistering.1.update recorded.1) raceEmptyRegistering.2

-- the record defers (the host is running), the return clears the guard instead of parking,
-- the next loop top fails the host with the recorded cause, the cancel frame runs, and the
-- host exits interrupted in the same entry with every command consumed
#guard (raceEmptyRegistering.1.fiber? Api.root).map (fun host =>
  (interruptRecord (interpOf Test.Program.RuntimeRReference.raceEmpty) (some ⟨9⟩)
    ReasonAnnotations.empty host).2) = some false
#guard raceEmptyDeferred.2 = []
#guard raceEmptyDeferred.1.stuck = none
#guard (raceEmptyDeferred.1.fiber? Api.root).bind RunFiber.exit =
  some (Witnesses.interruptedBy ⟨9⟩ Api.root)
#guard (raceEmptyDeferred.1.fiber? Api.root).map
  (fun f => (f.parked, f.frame.deferredInterrupt, f.frame.stack.length, f.currentOpCount)) =
    some (.notParked, false, 0, 10)

end DeferredRegistration

section SourceRepairs20

-- source-repairs §20 (2026-09-07): `forkScoped`'s `flatMap(scope, forkIn)` wrapper and the
-- multiple-finalizer close through `scopeCloseFinalizers`' generator, sequential and
-- parallel. The four rows are the discovery rows of `probes/p3-d4/p10_manifest.lean`; the
-- pinned host run is `probes/p3-d4/host-d4c.json`. Variables are numbered by binding depth
-- from the root. The rows are well typed and printed; none reads back (a reader gap).
def scopedDaemon : Supervision.ForkOptions := ⟨true, true, .inherit⟩
/-- The scoped entry, the wrapper's `OnSuccess`/`Service`/`Success`, `forkIn`, the child's own
count, and the close of a scope whose one finalizer the finished child already removed. -/
def forkScopedDone : NativeEff := .scoped (.withFiber (.forkScoped (.succeed one) scopedDaemon))
/-- One live scoped child: the close runs its one finalizer directly. -/
def seqOne : NativeEff := .scoped (.bind (.perform .deferredMake (.lit .unit))
  (.bind (.withFiber (.forkScoped (.callback .deferredAwait (.var 0)) scopedDaemon))
    (.succeed (.lit .unit))))
/-- Two live scoped children: the close walks two finalizers through the sequential
generator, each under the `Exit` primitive. -/
def seqTwo : NativeEff := .scoped (.bind (.perform .deferredMake (.lit .unit))
  (.bind (.withFiber (.forkScoped (.callback .deferredAwait (.var 0)) scopedDaemon))
    (.bind (.withFiber (.forkScoped (.callback .deferredAwait (.var 0)) scopedDaemon))
      (.succeed (.lit .unit)))))
/-- A parallel scope with two live `forkIn` children closed with an exit value: one generator
step forks both finalizers as immediate daemons and awaits them. -/
def parTwo : NativeEff :=
  .bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.bind (.perform .deferredMake (.lit .unit))
      (.bind (.withFiber (.forkIn (.callback .deferredAwait (.var 1)) scopedDaemon (.var 0)))
        (.bind (.withFiber (.forkIn (.callback .deferredAwait (.var 1)) scopedDaemon (.var 0)))
          (.bind (.exit (.succeed (.lit .unit))) (.withFiber (.closeScope (.var 0) (.var 4)))))))

def sourceRepairs20Rows : List NativeEff := [forkScopedDone, seqOne, seqTwo, parTwo]
#guard sourceRepairs20Rows.all Api.wellTyped
#guard sourceRepairs20Rows.all lockstep
-- the host's counts (`host-d4c.json`, budget 2048): the eight of the wrapper's row, the
-- nineteen with one direct finalizer, the thirty-eight through the sequential generator, and
-- the eighteen of the parallel step with its two six-op daemons
#guard sourceRepairs20Rows.map frameCount = [[8, 1], [19, 4], [38, 4, 4], [18, 4, 4, 6, 6]]
#guard sourceRepairs20Rows.map termCount = [[8, 1], [19, 4], [38, 4, 4], [18, 4, 4, 6, 6]]
#guard sourceRepairs20Rows.map frameCmds = [some 17, some 40, some 74, some 75]
#guard sourceRepairs20Rows.map termCmds = [some 17, some 40, some 74, some 75]

end SourceRepairs20

end Test.Program.RuntimeRContract
