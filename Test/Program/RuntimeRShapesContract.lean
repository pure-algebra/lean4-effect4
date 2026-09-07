import Effect4.Program.RuntimeR
import Test.Program.CompileContract
import Test.Program.DenoteRContract

/-!
R3 direct synthesized shapes and R4 source/control boundaries. Comparisons
observe every exit and the whole store, on the displayed finite tapes.
Packet: `Test/contracts/program-runtime-r.contract.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.RuntimeRShapesContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Test.Syntax.CompileContract

def rootEff : NativeEff := .succeed (.lit .unit)
def seedTerm (code : RProgram) (state : Stores := Stores.empty) : RState :=
  { (RunMachine.empty state : RState) with
    fibers := [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }
def seedFrame (code : NCode) (state : Stores := Stores.empty) : Api.Machine :=
  { (RunMachine.empty state : Api.Machine) with
    fibers := [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }
def tape : List Api.Decision := [.evaluate Api.root]
def runShape (code : RProgram) (state : Stores := Stores.empty)
    (decisions : List Api.Decision := tape) : RReplay :=
  replayEval (interpR rootEff) 300 decisions (seedTerm code state)
def shapeAgrees (code : Effect4.Machine.Program) (term : RProgram)
    (state : Stores := Stores.empty) (decisions : List Api.Decision := tape) : Bool :=
  decide (obsR (runShape term state decisions).machine =
    obs (replayEval (interpOf rootEff) 300 decisions (seedFrame (embed code) state)).machine)
def rootExit (r : RReplay) : Option ExitV := (r.machine.fiber? Api.root).bind RunFiber.exit

-- All finalizer branches, including the self guard and external park shape.
#guard shapeAgrees (finProgram (.release 7 false) (.success .unit))
  (denoteFin (.release 7 false) (.success .unit))
#guard shapeAgrees (finProgram (.release 7 true) (.success .unit))
  (denoteFin (.release 7 true) (.success .unit))
#guard shapeAgrees (finProgram (.interruptFiber Api.root true) (.success .unit))
  (denoteFin (.interruptFiber Api.root true) (.success .unit))
#guard shapeAgrees (finProgram (.interruptFiber Api.root false) (.success .unit))
  (denoteFin (.interruptFiber Api.root false) (.success .unit))
#guard shapeAgrees (finProgram (.awaitNewChildren []) (.success .unit))
  (denoteFin (.awaitNewChildren []) (.success .unit))
#guard shapeAgrees (finProgram (.detachFromParent 0 1) (.success .unit))
  (denoteFin (.detachFromParent 0 1) (.success .unit))
#guard shapeAgrees (finProgram (.parkThen 9) (.success .unit))
  (denoteFin (.parkThen 9) (.success .unit))
  Stores.empty [ .evaluate Api.root, .answerAsync Api.root 0 (.ofExit (.success .unit)) ]

def scopeState : Stores := { Stores.empty with
  scopes := ((Stores.empty.scopes.make 0 .sequential).addFinalizer 0 1 (.release 7 false)).1
  nextName := 2 }
#guard shapeAgrees (finProgram (.closeChildScope 0) (.success .unit))
  (denoteFin (.closeChildScope 0) (.success .unit)) scopeState
#guard ((runShape (denoteFin (.closeChildScope 0) (.success .unit)) scopeState).machine.state.scopes.status 0) =
  some (some (.success .unit))
#guard shapeAgrees (finProgram (.detachFromParent 0 1) (.success .unit))
  (denoteFin (.detachFromParent 0 1) (.success .unit)) scopeState

-- Failure accounting is ordered in both close walks (source-repairs §20: the generator of
-- `scopeCloseFinalizers`, sequential through the `Exit` primitive, parallel as immediate
-- daemons awaited together) and preserves all releases.
def releases : List FinName := [.release 7 true, .release 8 false, .release 9 true]
def failed : ExitV := .failure (Cause.fail (.tag 3))
#guard shapeAgrees (Prim.suspend (Thunk.body (.closeWalk .sequential releases failed)))
  (closeWalkR .sequential releases failed)
#guard shapeAgrees (Prim.suspend (Thunk.body (.closeWalk .parallel releases failed)))
  (closeWalkR .parallel releases failed)
#guard rootExit (runShape (closeWalkR .sequential releases failed)) =
  some (.failure ⟨(Cause.fail (Err.tag 7)).reasons ++ (Cause.fail (Err.tag 9)).reasons⟩)
#guard rootExit (runShape (closeWalkR .parallel releases failed)) =
  some (.failure ⟨(Cause.fail (Err.tag 7)).reasons ++ (Cause.fail (Err.tag 9)).reasons⟩)

-- Both Completion shapes and the exact stored-code decoder, including a live refusal.
#guard shapeAgrees (completionPrim (.ofExit failed)) (denoteCompletion (.ofExit failed))
#guard shapeAgrees (completionPrim (.ofRefGet ⟨0⟩)) (denoteCompletion (.ofRefGet ⟨0⟩))
  { Stores.empty with refs := [.nat 12] }
#guard rootExit (runShape (denoteStored (.yieldNowWith 0))) = none
#guard (runShape (denoteStored (.yieldNowWith 0))).machine.stuck = none
#guard (runShape (.vis (.inr (.closeScope 0 (.success .unit))) Effects.Program.pure)).machine.stuck =
  some (.unknownScope 0)

-- All cancel cases, the loop's restore hook, and the malformed-marker boundary.
#guard shapeAgrees (cancelProgram (.withWaiter (.cancelAwait ⟨0⟩) Api.root 2))
  (denoteStoreCancel (.withWaiter (.cancelAwait ⟨0⟩) Api.root 2))
#guard shapeAgrees (cancelProgram (.withWaiter .cancelPark Api.root 2))
  (denoteStoreCancel (.withWaiter .cancelPark Api.root 2))
#guard shapeAgrees (cancelProgram (.withWaiter (.cancelRace 0) Api.root 2))
  (denoteStoreCancel (.withWaiter (.cancelRace 0) Api.root 2))
#guard shapeAgrees (cancelProgram (.constant .unit)) (denoteStoreCancel (.constant .unit))
#guard rootExit (runShape (restoreR (.pure (.success .unit)) (.restore failed))) = some failed
#guard rootExit (runShape (restoreR (.pure (.success .unit)) (.constant .unit))) =
  some Effect4.Program.Denote.outsideExit
-- the cleanup-end marker delivers its exit through the saved slots, as the frame's
-- `Prim.ofExit` does (P3 walk agreement); with no slot it is the fiber's exit
#guard rootExit (runShape (.vis (.inr (.finishFinalizer (.success .unit))) Effects.Program.pure)) =
  some (.success .unit)

-- Existing source fixtures exercise every straight handler, generator control,
-- loop cursor, stateful failure and malformed fallback on a fixed tape.
def sources : List NativeEff := [pSucceed, pBindSync, pFail, pCatch, pMatchValue,
  pMatchCause, pMatchCauseReified, pExit, pOnExit, pDie, pRefSet, pRefUpdate,
  pRefModify, pGenTwoYields, pGenIfThen, pGenIfElse, pGenFail, pGenElseEnds,
  pGenThenEnds, pGenLoop, pGenLoopBreakInElse, pWhileLoop, pBranchTrue,
  pBranchFalse, Test.Program.DenoteRContract.writeThenFail,
  .succeed (.var 0), .sync (.var 0), .callback .refGet (.lit .unit)]
def sourceAgrees (source : NativeEff) : Bool :=
  decide (obsR (replayR source 400 tape).machine = obs (Api.replay source 400 tape).machine)
#guard sources.all sourceAgrees

-- Pending interruption skips an ordinary catch; restoring the inner mask lets
-- the catch inside an uninterruptible region handle the same recorded cause.
def caughtYield : NativeEff := .catchCause (.yieldNow 0) (.perform .refMake (.lit (.nat 6)))
def interruptTape : List Api.Decision :=
  [.evaluate Api.root, .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root]
def interruptedAgrees (source : NativeEff) : Bool :=
  decide (obsR (replayR source 120 interruptTape).machine =
    obs (Api.replay source 120 interruptTape).machine)
#guard interruptedAgrees caughtYield
#guard interruptedAgrees (.uninterruptible (.catchCause (.interruptible (.yieldNow 0))
  (.perform .refMake (.lit (.nat 6)))))

-- A completing sync owes a child resume before delivering its own answer. The
-- child interrupts the completing parent, so its later write must not run and
-- its finalizer must run. This exercises the `answered`/`deliver` split itself.
def dueInterrupt : NativeEff :=
  let child : NativeEff := .bind (.callback .deferredAwait (.var 0))
    (.withFiber (.interrupt (.var 1)))
  let done : NativeEff := .perform .deferredSucceed
    (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil)))
  let parent : NativeEff := .onExit (.bind done (.perform .refMake (.lit (.nat 99))))
    (.perform .refMake (.lit (.nat 9)))
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork parent ⟨false, true, .inherit⟩))
      (.bind (.withFiber (.fork child ⟨true, true, .inherit⟩))
        (.awaitFiber (.var 1) .joinEffect)))
#guard Api.wellTyped dueInterrupt && Api.readable dueInterrupt
#guard obs (Api.replay dueInterrupt 400 [Api.evaluate, Api.flush]).machine =
  obsR (replayR dueInterrupt 400 [Api.evaluate, Api.flush]).machine
#guard (Api.replay dueInterrupt 400 [Api.evaluate, Api.flush]).stores.refs = [.nat 9]
#guard (replayR dueInterrupt 400 [Api.evaluate, Api.flush]).machine.state.refs = [.nat 9]

end Test.Program.RuntimeRShapesContract
