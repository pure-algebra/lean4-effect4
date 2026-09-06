import Effect4.Program.DenoteR
import Test.Program.CompileContract

/-! R2 finite probes and universal statement pins. The observer runs store nodes only;
it stops at every fiber node, including frontiers. It never uses `fiberRefusal`.
Packet: `Test/contracts/program-denote-r.contract.md`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.DenoteRContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched
open Test.Syntax.CompileContract

inductive Observation
  | done (exit : ExitV) (stores : Stores)
  | waiting (operation : FiberOp) (stores : Stores)
  | exhausted
deriving DecidableEq

/-- A finite store-only observer; reaching a fiber operation leaves it unanswered. -/
def observe : Nat → RProgram → Stores → Observation
  | 0, _, _ => .exhausted
  | n + 1, program, stores =>
    match program with
    | .pure ex => .done ex stores
    | .vis (.inl op) k =>
      let (value, stores') := (storeHandler.handle op).run stores
      observe n (k value) stores'
    | .vis (.inr op) _ => .waiting op stores

def rootPoint (fuel : Nat := 80) (env : List Val := []) (choices : List Bool := []) : Point :=
  ⟨[], env, fuel, choices⟩

def unfolded (e : NativeEff) (n : Nat := 160) (fuel : Nat := 80)
    (env : List Val := []) (choices : List Bool := []) : RProgram :=
  denoteR e n e (rootPoint fuel env choices)

def result (e : NativeEff) : Observation := observe 200 (unfolded e) Stores.empty

def answer? : Observation → Option ExitV
  | .done ex _ => some ex
  | _ => none

def operation? : Observation → Option FiberOp
  | .waiting op _ => some op
  | _ => none

def stores? : Observation → Option Stores
  | .done _ s | .waiting _ s => some s
  | _ => none

-- Store effects before failure survive into the finalizer and the final observation.
#guard result pSucceed = .done (.success (.nat 42)) Stores.empty
#guard answer? (result pOnExit) = some (meaning pOnExit [] Stores.empty).1
#guard answer? (result pRefSet) = some (meaning pRefSet [] Stores.empty).1
#guard stores? (result pRefSet) = some (meaning pRefSet [] Stores.empty).2
#guard answer? (result pMatchCauseReified) = some (meaning pMatchCauseReified [] Stores.empty).1

def writeThenFail : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 1)))
    (.onExit (.fail (.lit (.nat 7)))
      (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 9)) .nil)))))

#guard answer? (result writeThenFail) = some (.failure (Cause.fail (Err.tag 7)))
#guard ((stores? (result writeThenFail)).map Stores.refs) = some [.nat 9]
#guard result (.succeed (.var 0)) = .done badShapeExit Stores.empty
#guard result (.sync (.var 0)) = .done (.success .unit) Stores.empty

-- Fuel and unanswered choices are visible operations, never terminal failures.
#guard observe 5 (unfolded pSucceed 0 1) Stores.empty =
  .waiting (.frontier .unfoldingFuel (.effect (rootPoint 1))) Stores.empty
#guard observe 5 (unfolded pSucceed 5 0) Stores.empty =
  .waiting (.frontier .compileFuel (.effect (rootPoint 0))) Stores.empty
#guard observe 5 (unfolded pChoose 2 1 [] []) Stores.empty =
  .waiting (.frontier .unansweredChoice (.effect (rootPoint 1))) Stores.empty
#guard observe 5 (unfolded pChoose 2 1 [] [true]) Stores.empty =
  .done (.success (.nat 1)) Stores.empty
#guard observe 5 (unfolded pChoose 2 1 [] [false]) Stores.empty =
  .done (.success (.nat 2)) Stores.empty
#guard operation? (result (.acquireRelease pSucceed pSucceed)) =
  some (.frontier .unsupported (.effect (rootPoint)))

-- The false branch is child 1; the action and child are two further address components.
def branchFork : NativeEff :=
  .branch (.lit (.bool false)) pFail (.withFiber (.fork pSucceed deferredChild))
#guard operation? (result branchFork) =
  some (.fork ⟨[1, 0, 0], [], 77, []⟩ deferredChild)

def scopedFork : NativeEff := .withFiber (.forkScoped pSucceed scopedChild)
#guard operation? (result scopedFork) = some (.forkScoped ⟨[0, 0], [], 78, []⟩ scopedChild 80)

def forkInTerm : NativeEff := .withFiber (.forkIn pSucceed deferredChild (.var 0))
#guard operation? (observe 5 (unfolded forkInTerm 10 8 [.scopeHandle 3]) Stores.empty) =
  some (.forkIn ⟨[0, 0], [.scopeHandle 3], 6, []⟩ deferredChild 3 8)

#guard operation? (result (.uninterruptible pFail)) = some (.mask false ⟨[0], [], 79, []⟩)
#guard operation? (result (.interruptible pFail)) = some (.mask true ⟨[0], [], 79, []⟩)
#guard operation? (result (.scoped pSucceed)) = some (.scoped ⟨[0], [], 79, []⟩ 0)
#guard ((stores? (result (.scoped pSucceed))).map fun s => s.scopes.entries.length) = some 1

def closeTerm : NativeEff := .withFiber (.closeScope (.var 0) (.var 1))
#guard operation? (observe 5 (unfolded closeTerm 10 8
  [.scopeHandle 3, .exitErr (Cause.fail Err.boom)]) Stores.empty) =
  some (.closeScope 3 (.failure (Cause.fail Err.boom)))

def awaitTerm (mode : Supervision.ObserverMode) : NativeEff := .awaitFiber (.var 0) mode
def asyncTerm : NativeEff := .callback .deferredAwait (.var 0)

#guard operation? (observe 5 (unfolded (awaitTerm .joinEffect) 10 8 [.fiber ⟨2⟩]) Stores.empty) =
  some (.await ⟨2⟩ .joinEffect)
#guard operation? (observe 5 (unfolded asyncTerm 10 8 [.promise ⟨0⟩]) Stores.empty) =
  some (.async (.registerAwait ⟨0⟩) (.promise ⟨0⟩))
#guard result (.callback .deferredAwait (.lit (.nat 0))) = .done badShapeExit Stores.empty
#guard result (.callback .refGet (.lit .unit)) = .done badShapeExit Stores.empty

/-- Feed an explicit exit only to operations whose contract answers with an exit. -/
def replyExit (program : RProgram) (ex : ExitV) : Observation :=
  match program with
  | .vis (.inr (.async _ _)) k => observe 20 (k ex) Stores.empty
  | .vis (.inr (.await _ .joinEffect)) k => observe 20 (k ex) Stores.empty
  | .vis (.inr (.forkScoped _ _ _)) k => observe 20 (k ex) Stores.empty
  | _ => .exhausted

#guard replyExit (unfolded asyncTerm 10 8 [.promise ⟨0⟩]) (.failure (Cause.fail Err.boom)) =
  .done (.failure (Cause.fail Err.boom)) Stores.empty
#guard replyExit (unfolded asyncTerm 10 8 [.promise ⟨0⟩])
  (.success (.exitErr (Cause.fail Err.boom))) =
  .done (.success (.exitErr (Cause.fail Err.boom))) Stores.empty
#guard replyExit (unfolded (awaitTerm .joinEffect) 10 8 [.fiber ⟨2⟩])
  (.failure (Cause.fail Err.boom)) = .done (.failure (Cause.fail Err.boom)) Stores.empty
#guard replyExit (unfolded scopedFork) (.failure (Cause.die Defect.missingService)) =
  .done (.failure (Cause.die Defect.missingService)) Stores.empty

-- Existing generator witnesses exercise both block exits, local bindings and both break paths.
#guard answer? (result pGenTwoYields) = exitOf (replayEff pGenTwoYields [evaluateRoot]) 0
#guard answer? (result pGenIfThen) = exitOf (replayEff pGenIfThen [evaluateRoot]) 0
#guard answer? (result pGenIfElse) = exitOf (replayEff pGenIfElse [evaluateRoot]) 0
#guard answer? (result pGenElseEnds) = some (.success (.nat 2))
#guard answer? (result pGenThenEnds) = some (.success (.nat 2))
#guard answer? (result pGenFail) = some (.failure (Cause.fail (Err.tag 7)))
#guard answer? (result pGenLoop) = some (.success (.nat 3))
#guard answer? (result pGenLoopBreakInElse) = some (.success (.nat 3))
#guard ((stores? (result pGenLoop)).map Stores.refs) = some [.nat 3]
#guard answer? (result pWhileLoop) = some (.success (.nat 3))
#guard ((stores? (result pWhileLoop)).map Stores.refs) = some [.nat 3]

def inlineGen : NativeEff := .gen (.cons (.bindYield pSucceed) (.cons (.ret (.var 0)) .nil))
def resumedGen : NativeEff :=
  .gen (.cons (.bindYield (.sync (.lit (.nat 42)))) (.cons (.ret (.var 0)) .nil))

-- At scan fuel 1 an inline yield exhausts; a sync resumes and receives a fresh scan budget.
#guard operation? (observe 20 (unfolded inlineGen 30 1) Stores.empty) =
  some (.frontier .compileFuel (.generator (rootPoint 1) [1] [.nat 42] 0))
#guard observe 20 (unfolded resumedGen 30 1) Stores.empty = .done (.success (.nat 42)) Stores.empty
#guard inlineYield pSucceed (rootPoint) = some (.success (.nat 42))
#guard inlineYield (.sync (.lit (.nat 42))) (rootPoint) = none

def endlessLoop : NativeEff := .whileLoop (.lit (.nat 0)) (.lit (.bool true)) (.var 0) pSucceed
#guard operation? (observe 30 (unfolded endlessLoop 1 80) Stores.empty) =
  some (.frontier .unfoldingFuel (.loop (rootPoint) (.nat 0)))

#check (@denoteR_straight : ∀ (root : NativeEff) (n : Nat) (e : NativeEff) (p : Point),
  Straight e = true → Agreement.depth e ≤ n → Agreement.depth e ≤ p.fuel →
  denoteR root n e p = Effects.Program.inl (denote e p.env))
#check (@inlineYield_eq_headExit : ∀ (e : NativeEff) (p : Point),
  inlineYield e p = headExit (compileEff e p))

end Test.Program.DenoteRContract
