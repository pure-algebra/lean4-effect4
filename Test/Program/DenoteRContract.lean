import Effect4.Program.DenoteR
import Test.Program.CompileContract

/-! R2 finite probes and universal statement pins. The store observer first erases
control markers, then stops at every remaining fiber node, including frontiers.
Raw probes retain the handler and cleanup markers. Neither uses `fiberRefusal`.
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
def observeRaw : Nat → RProgram → Stores → Observation
  | 0, _, _ => .exhausted
  | n + 1, program, stores =>
    match program with
    | .pure ex => .done ex stores
    | .vis (.inl op) k =>
      let (value, stores') := (storeHandler.handle op).run stores
      observeRaw n (k value) stores'
    | .vis (.inr op) _ => .waiting op stores

/-- The former store-only meaning after removing explicit control boundaries. -/
def observe (fuel : Nat) (program : RProgram) (stores : Stores) : Observation :=
  observeRaw fuel (eraseControl program) stores

def rootPoint (fuel : Nat := 80) (env : List Val := []) (choices : List Bool := []) : Point :=
  ⟨[], env, fuel, choices⟩

def unfolded (e : NativeEff) (fuel : Nat := 80)
    (env : List Val := []) (choices : List Bool := []) : RProgram :=
  denoteR e e (rootPoint fuel env choices)

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

-- Compile fuel and unanswered choices are visible operations, never terminal failures.
-- P2 removed the unfolding budget: loops and generators are runtime operations, so the
-- compile budget at the point is the only frontier of this kind.
#guard observe 5 (unfolded pSucceed 0) Stores.empty =
  .waiting (.frontier .compileFuel (rootPoint 0)) Stores.empty
#guard observe 5 (unfolded pChoose 1 [] []) Stores.empty =
  .waiting (.frontier .unansweredChoice (rootPoint 1)) Stores.empty
#guard observe 5 (unfolded pChoose 1 [] [true]) Stores.empty =
  .done (.success (.nat 1)) Stores.empty
#guard observe 5 (unfolded pChoose 1 [] [false]) Stores.empty =
  .done (.success (.nat 2)) Stores.empty
#guard operation? (result (.acquireRelease pSucceed pSucceed)) =
  some (.frontier .unsupported (rootPoint))

-- The false branch is child 1; the action and child are two further address components.
def branchFork : NativeEff :=
  .branch (.lit (.bool false)) pFail (.withFiber (.fork pSucceed deferredChild))
#guard operation? (result branchFork) =
  some (.fork (.at_ ⟨[1, 0, 0], [], 77, []⟩) deferredChild)

def scopedFork : NativeEff := .withFiber (.forkScoped pSucceed scopedChild)
#guard operation? (result scopedFork) = some (.forkScoped ⟨[0, 0], [], 78, []⟩ scopedChild 80)

def forkInTerm : NativeEff := .withFiber (.forkIn pSucceed deferredChild (.var 0))
#guard operation? (observe 5 (unfolded forkInTerm 8 [.scopeHandle 3]) Stores.empty) =
  some (.forkIn ⟨[0, 0], [.scopeHandle 3], 6, []⟩ deferredChild 3 8)

#guard operation? (result (.uninterruptible pFail)) = some (.mask false (.at_ ⟨[0], [], 79, []⟩))
#guard operation? (result (.interruptible pFail)) = some (.mask true (.at_ ⟨[0], [], 79, []⟩))
-- P2: `scoped` denotes structurally as the compile spells it (the scope store's `scopeMake`
-- under a success boundary, then the context frames); the observer runs the store
-- operation and stops at the first fiber operation, the context read.
#guard operation? (result (.scoped pSucceed)) = some .getContext
#guard ((stores? (result (.scoped pSucceed))).map fun s => s.scopes.entries.length) = some 1

def closeTerm : NativeEff := .withFiber (.closeScope (.var 0) (.var 1))
#guard operation? (observe 5 (unfolded closeTerm 8
  [.scopeHandle 3, .exitErr (Cause.fail Err.boom)]) Stores.empty) =
  some (.closeScope 3 (.failure (Cause.fail Err.boom)))

def awaitTerm (mode : Supervision.ObserverMode) : NativeEff := .awaitFiber (.var 0) mode
def asyncTerm : NativeEff := .callback .deferredAwait (.var 0)

#guard operation? (observe 5 (unfolded (awaitTerm .joinEffect) 8 [.fiber ⟨2⟩]) Stores.empty) =
  some (.await ⟨2⟩ .joinEffect)
#guard operation? (observe 5 (unfolded asyncTerm 8 [.promise ⟨0⟩]) Stores.empty) =
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

#guard replyExit (unfolded asyncTerm 8 [.promise ⟨0⟩]) (.failure (Cause.fail Err.boom)) =
  .done (.failure (Cause.fail Err.boom)) Stores.empty
#guard replyExit (unfolded asyncTerm 8 [.promise ⟨0⟩])
  (.success (.exitErr (Cause.fail Err.boom))) =
  .done (.success (.exitErr (Cause.fail Err.boom))) Stores.empty
#guard replyExit (unfolded (awaitTerm .joinEffect) 8 [.fiber ⟨2⟩])
  (.failure (Cause.fail Err.boom)) = .done (.failure (Cause.fail Err.boom)) Stores.empty
#guard replyExit (unfolded scopedFork) (.failure (Cause.die Defect.missingService)) =
  .done (.failure (Cause.die Defect.missingService)) Stores.empty

-- P2: generators and loops are runtime operations behind the host's suspend checkpoint;
-- the static observer stops at their entry, and their execution is compared with the
-- frame machine on every generator and loop fixture in `RuntimeRShapesContract` and
-- counted in `RuntimeRContract`. The entry carries the generator's or the loop's point.
#guard operation? (result pGenTwoYields) = some (.gen (rootPoint))
#guard operation? (result pGenLoop) = some (.gen (rootPoint))
#guard operation? (result pWhileLoop) = some (.loop ⟨[1, 0], [.cell ⟨0⟩], 78, []⟩ (.nat 0))

def inlineGen : NativeEff := .gen (.cons (.bindYield pSucceed) (.cons (.ret (.var 0)) .nil))
def resumedGen : NativeEff :=
  .gen (.cons (.bindYield (.sync (.lit (.nat 42)))) (.cons (.ret (.var 0)) .nil))

-- The entry is reached at any positive compile fuel; scan exhaustion is a runtime
-- frontier of the walk, pinned in `RuntimeRContract`.
#guard operation? (observe 20 (unfolded inlineGen 1) Stores.empty) = some (.gen (rootPoint 1))
#guard operation? (observe 20 (unfolded resumedGen 1) Stores.empty) = some (.gen (rootPoint 1))
#guard inlineYield pSucceed (rootPoint) = some (.success (.nat 42))
#guard inlineYield (.sync (.lit (.nat 42))) (rootPoint) = none
-- P1a (row D1 of the P0 record): `exit` of an immediate exit is that exit's success;
-- `exit` of a `sync` is not, and a loop is never an immediate exit (rows D1, D3).
#guard inlineYield (.exit pSucceed) (rootPoint) = some (.success (.exitOk (.nat 42)))
#guard inlineYield pExit (rootPoint) = some (.success (.exitErr (Cause.fail (Err.tag 7))))
#guard inlineYield (.exit (.sync (.lit (.nat 42)))) (rootPoint) = none
#guard inlineYield (.whileLoop (.lit (.nat 0)) (.lit (.bool true)) (.var 0) pSucceed) (rootPoint) = none
#guard result (.exit pSucceed) = .done (.success (.exitOk (.nat 42))) Stores.empty
#guard operation? (observeRaw 1 (unfolded (.exit pSucceed)) Stores.empty) = none

def endlessLoop : NativeEff := .whileLoop (.lit (.nat 0)) (.lit (.bool true)) (.var 0) pSucceed
#guard operation? (observe 30 (unfolded endlessLoop) Stores.empty) =
  some (.loop (rootPoint) (.nat 0))

-- Cleanup and an ordinary success continuation retain different boundary data.
-- Their old, erased terms coincide, so the distinction must remain in denoteR.
def cleanupUnit : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 9))) (.succeed (.lit .unit))
def ensured : NativeEff := .onExit (.yieldNow 0) cleanupUnit
def sequenced : NativeEff := .bind (.yieldNow 0) cleanupUnit

#guard operation? (observeRaw 1 (unfolded ensured) Stores.empty) =
  some (.guard_ (.onExit false))
#guard operation? (observeRaw 1 (unfolded sequenced) Stores.empty) =
  some (.guard_ .onSuccess)
#guard operation? (observeRaw 1 (unfolded (.catchCause pFail pSucceed)) Stores.empty) =
  some (.guard_ .onFailure)
-- P1a: `exit pFail` folds to its exit (row D1) and retains no boundary; the both-arm
-- boundary is retained exactly when the body is not an immediate exit.
#guard operation? (observeRaw 1 (unfolded (.exit pFail)) Stores.empty) = none
#guard operation? (observeRaw 1 (unfolded (.exit pBindSync)) Stores.empty) =
  some (.guard_ .all)

theorem cleanup_boundary_distinct : unfolded ensured ≠ unfolded sequenced := by
  intro h
  have heads := congrArg (fun p => operation? (observeRaw 1 p Stores.empty)) h
  change some (FiberOp.guard_ (.onExit false)) = some (.guard_ .onSuccess) at heads
  cases heads

example : eraseControl (unfolded ensured) = eraseControl (unfolded sequenced) := rfl

-- Erasure only removes boundary bookkeeping. Fiber work and live frontiers stay visible.
#guard operation? (observeRaw 1 (eraseControl (unfolded ensured)) Stores.empty) =
  some (.yieldNow 0)
#guard operation? (observeRaw 1 (eraseControl (guardR .all
  (.vis (.inr .getId) (fun v => .pure (.success v))))) Stores.empty) = some .getId
#guard operation? (observeRaw 1 (eraseControl (guardR .onSuccess
  (pending .compileFuel (rootPoint 0)))) Stores.empty) =
  some (.frontier .compileFuel (rootPoint 0))
#guard observeRaw 1 (eraseControl (.vis (.inr (.unguard (.failure (Cause.fail Err.boom))))
  Effects.Program.pure)) Stores.empty = .done (.failure (Cause.fail Err.boom)) Stores.empty
#guard observeRaw 1 (eraseControl (.vis (.inr (.finishFinalizer (.success (.nat 7))))
  Effects.Program.pure)) Stores.empty = .done (.success (.nat 7)) Stores.empty

#check (@denoteR_straight : ∀ (root : NativeEff) (e : NativeEff) (p : Point),
  Straight e = true → Agreement.depth e ≤ p.fuel →
  eraseControl (denoteR root e p) = Effects.Program.inl (denote e p.env))
#check (@meaning_denoteR_straight : ∀ (root : NativeEff) (e : NativeEff) (p : Point),
  Straight e = true → Agreement.depth e ≤ p.fuel → ∀ stores : Stores,
  (Effects.interpret rHandler (eraseControl (denoteR root e p))).run stores =
    meaning e p.env stores)
-- P2: the checkpoints erase with the boundary markers.
#guard observeRaw 1 (eraseControl (suspendR (rootPoint) (.pure (.success (.nat 1))))) Stores.empty =
  .done (.success (.nat 1)) Stores.empty
#guard operation? (observeRaw 1 (unfolded (.suspend pSucceed)) Stores.empty) = some (.suspend (rootPoint))
#guard operation? (observeRaw 1 (unfolded (.sync (.lit (.nat 42)))) Stores.empty) = some (.sync (.nat 42))
#guard result (.suspend pSucceed) = .done (.success (.nat 42)) Stores.empty
#check (@inlineYield_eq_headExit : ∀ (e : NativeEff) (p : Point),
  inlineYield e p = headExit (compileEff e p))

end Test.Program.DenoteRContract
