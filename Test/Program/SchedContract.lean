import Effect4.Laws.Program.Sched
import Test.Program.CompileContract

/-!
# Sched contract — the term scheduler's signature, pinned

Packet: `Test/contracts/program-sched.contract.md`; module `src/Effect4/Laws/Program/Sched.lean`
(slice two, R1 of `docs/research/2026-09-05-slices-2-3-worksheets.md`). These guards pin
the shape of `RSig` (the store signature on the left, the fiber signature on the right, one
value, exit or boundary-entry answer), the placeholder nature of the right half, and
`meaning_via_rsig` on the contract programs: the straight-line denotation injected on
the left means, under the summed handler, what `meaning` says. Every pin is a `#guard`
over first-order values.
-/

set_option autoImplicit false

namespace Test.Program.SchedContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched
open Test.Syntax.CompileContract (pSucceed pBindSync pFail pCatch pOnExit pRefSet pBranchTrue
  scopedChild exitOf replayEff evaluateRoot)

/-! ## The signature's shape -/

example : RSig.Op = (SyncOp ⊕ FiberOp) := rfl
example (o : SyncOp) : RSig.Answer (Sum.inl o) = Val := rfl
example (o : FiberOp) : RSig.Answer (Sum.inr o) = o.answer := rfl
example (body : Body) : RSig.Answer (.inr (.mask false body)) = ExitV := rfl
example (p : Point) : RSig.Answer (.inr (.fork (.at_ p) scopedChild)) = Val := rfl
example (id : FiberId) : RSig.Answer (.inr (.await id .joinEffect)) = ExitV := rfl
example (id : FiberId) : RSig.Answer (.inr (.await id .awaitValue)) = Val := rfl
example (kind : GuardKind) : RSig.Answer (.inr (.guard_ kind)) = Option ExitV := rfl
example (ex : ExitV) : RSig.Answer (.inr (.unguard ex)) = ExitV := rfl
example (ex : ExitV) : RSig.Answer (.inr (.finishFinalizer ex)) = ExitV := rfl
example (body : Point) : RSig.Answer (.inr (.scoped body)) = ExitV := rfl
example (previous : Ctx) (scope : Nat) (ex : ExitV) :
    RSig.Answer (.inr (.scopeExit previous scope ex)) = ExitV := rfl
-- P2: the checkpoints answer a value; the loop and generator entries answer their exit.
example (p : Point) : RSig.Answer (.inr (.suspend p)) = Val := rfl
example (v : Val) : RSig.Answer (.inr (.sync v)) = Val := rfl
example (p : Point) : RSig.Answer (.inr (.gen p)) = ExitV := rfl
example (p : Point) (cursor : Val) : RSig.Answer (.inr (.loop p cursor)) = ExitV := rfl
example (reason : PendingReason) (p : Point) : RSig.Answer (.inr (.frontier reason p)) = ExitV := rfl

-- E4-SCHED-CE-002: the scout's proposed collision is false; success adds `exitOk`.
theorem exit_encoding_distinguishes (c : CauseV) :
    reifyExitVal (Exit.success (Val.exitErr c)) ≠ reifyExitVal (Exit.failure c) := by
  simp [reifyExitVal]

theorem exit_encoding_roundtrip (ex : ExitV) : exitOfVal (reifyExitVal ex) = some ex := by
  show exitImage.ofVal (reifyExitVal ex) = some ex
  rw [reifyExitVal_eq_exitImage]
  exact exitImage.ofVal_toVal ex

/-! ## R2 scout corrections, checked before changing the contract -/

-- E4-SCHED-CE-003: the draft's zero arm cannot satisfy its unconditional restriction law.
theorem draft_zero_not_straight : (Effects.Program.pure outsideExit : RProgram) ≠
    Effects.Program.inl (denote pSucceed []) := by
  intro h
  cases h

#guard compile pSucceed 0 [] = frontier ⟨[], [], 0, [], [], 0⟩

-- Async completion and a scoped fork can deliver failures through the caller's handlers.
example : completionPrim (.ofExit (.failure (Cause.fail Err.boom))) =
    Prim.failure (Cause.fail Err.boom) := rfl

def forkWithoutScope : NativeEff := .withFiber (.forkScoped pSucceed scopedChild)
#guard exitOf (replayEff forkWithoutScope [evaluateRoot]) 0 =
  some (Exit.failure (Cause.die Defect.missingService))

-- the fiber operations are first-order and decidable: two distinct leaves, two equal ones
#guard decide (FiberOp.getId = FiberOp.getContext) = false
#guard decide (FiberOp.yieldNow 0 = FiberOp.yieldNow 0) = true
#guard decide (FiberOp.await ⟨1⟩ Supervision.ObserverMode.awaitValue =
  FiberOp.await ⟨1⟩ Supervision.ObserverMode.joinEffect) = false
#guard decide (Body.at_ ⟨[], [], 0, [], [], 0⟩ = Body.raceCleanup 0) = false
#guard decide (Body.fin (.release 1 false) (.success .unit) =
  Body.fin (.release 1 false) (.success .unit)) = true
#guard decide (FiberOp.guard_ (.onExit false) = FiberOp.guard_ .onSuccess) = false
#guard decide (FiberOp.unguard (.success .unit) = FiberOp.finishFinalizer (.success .unit)) = false
#guard (FiberOp.guard_ .all).defaultAnswer = none
#guard (FiberOp.unguard (.failure (Cause.fail Err.boom))).defaultAnswer =
  .failure (Cause.fail Err.boom)
#guard (FiberOp.finishFinalizer (.success (.nat 7))).defaultAnswer = .success (.nat 7)
#guard (FiberOp.gen ⟨[], [], 0, [], [], 0⟩).defaultAnswer = .success .unit
#guard (FiberOp.loop ⟨[], [], 0, [], [], 0⟩ (.nat 0)).defaultAnswer = .success .unit
#guard decide (FiberOp.suspend ⟨[], [], 0, [], [], 0⟩ = FiberOp.sync .unit) = false
#guard FiberOp.construction.defaultAnswer = []
#guard (FiberOp.scoped ⟨[], [], 0, [], [], 0⟩).defaultAnswer = .success .unit
#guard (FiberOp.scopeExit emptyCtx 0 (.failure (Cause.fail Err.boom))).defaultAnswer = .success .unit
example : FiberOp.construction.answer = List (FiberId × ExitV) := rfl

/-! ## The store half under the summed handler -/

/-- One store operation handled on the empty store, as a first-order pair (the answer type
reduces to `Val` only once the side of the sum is known). -/
def handledL (o : SyncOp) : Val × Stores := (rHandler.handle (Sum.inl o)).run Stores.empty

/-- One fiber operation handled on the empty store. -/
def handledR (o : FiberOp) : o.answer × Stores := (rHandler.handle (Sum.inr o)).run Stores.empty

-- `rHandler` on the left is the store handler: a `refMake` on the empty store mints cell 0
#guard handledL (SyncOp.refMake (Val.nat 7))
  == ((storeHandler.handle (SyncOp.refMake (Val.nat 7))).run Stores.empty : Val × Stores)
#guard (handledL (SyncOp.refMake (Val.nat 7))).1 == Val.cell ⟨0⟩
-- and on the right it is the placeholder: `unit`, the store untouched (E4-SCHED-CE-001)
#guard (handledR FiberOp.getId : Val × Stores) == (Val.unit, Stores.empty)

/-! ## `meaning_via_rsig`, one program at a time -/

def viaRSig (e : NativeEff) : ExitV × Stores :=
  (Effects.interpret rHandler (Effects.Program.inl (denote e []))).run Stores.empty

#guard (viaRSig pSucceed).1 == (meaning pSucceed [] Stores.empty).1
#guard (viaRSig pBindSync).1 == (meaning pBindSync [] Stores.empty).1
#guard (viaRSig pFail).1 == (meaning pFail [] Stores.empty).1
#guard (viaRSig pCatch).1 == (meaning pCatch [] Stores.empty).1
#guard (viaRSig pOnExit).1 == (meaning pOnExit [] Stores.empty).1
#guard (viaRSig pBranchTrue).1 == (meaning pBranchTrue [] Stores.empty).1
#guard (viaRSig pRefSet).1 == (meaning pRefSet [] Stores.empty).1
#guard (viaRSig pRefSet).2 == (meaning pRefSet [] Stores.empty).2

/-! ## The statements, frozen -/

#check (@Effect4.Program.Sched.interpret_inl_store :
  ∀ {A : Type} (program : Effects.Program StoreSig A),
    Effects.interpret rHandler (Effects.Program.inl program) =
      Effects.interpret storeHandler program)

#check (@Effect4.Program.Sched.meaning_via_rsig :
  ∀ (e : NativeEff) (env : List Val) (s : Stores),
    (Effects.interpret rHandler (Effects.Program.inl (denote e env))).run s = meaning e env s)

end Test.Program.SchedContract
