import Effect4.Program.Sched
import Test.Program.CompileContract

/-!
# Sched contract — the term scheduler's signature, pinned

Packet: `Test/contracts/program-sched.contract.md`; module `src/Effect4/Program/Sched.lean`
(slice two, R1 of `docs/research/2026-09-05-slices-2-3-worksheets.md`). These guards pin
the shape of `RSig` (the store signature on the left, the fiber signature on the right, one
value or exit per answer), the placeholder nature of the right half, and `meaning_via_rsig` on the
contract programs: the straight-line denotation injected on the left means, under the
summed handler, what `meaning` says. Every pin is a `#guard` over first-order values.
-/

set_option autoImplicit false

namespace Test.Program.SchedContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched
open Test.Syntax.CompileContract (pSucceed pBindSync pFail pCatch pOnExit pRefSet pBranchTrue
  pChoose scopedChild exitOf replayEff evaluateRoot)

/-! ## The signature's shape -/

example : RSig.Op = (SyncOp ⊕ FiberOp) := rfl
example (o : SyncOp) : RSig.Answer (Sum.inl o) = Val := rfl
example (o : FiberOp) : RSig.Answer (Sum.inr o) = o.answer := rfl
example (p : Point) : RSig.Answer (.inr (.mask false p)) = ExitV := rfl
example (id : FiberId) : RSig.Answer (.inr (.await id .joinEffect)) = ExitV := rfl
example (id : FiberId) : RSig.Answer (.inr (.await id .awaitValue)) = Val := rfl

-- E4-SCHED-CE-002: the scout's proposed collision is false; success adds `exitOk`.
theorem exit_encoding_distinguishes (c : CauseV) :
    reifyExitVal (Exit.success (Val.exitErr c)) ≠ reifyExitVal (Exit.failure c) := by
  simp [reifyExitVal]

theorem exit_encoding_roundtrip (ex : ExitV) : exitOfVal (reifyExitVal ex) = some ex := by
  cases ex <;> rfl

/-! ## R2 scout corrections, checked before changing the contract -/

-- E4-SCHED-CE-003: the draft's zero arm cannot satisfy its unconditional restriction law.
theorem draft_zero_not_straight : (Effects.Program.pure outsideExit : RProgram) ≠
    Effects.Program.inl (denote pSucceed []) := by
  intro h
  cases h

#guard compile pSucceed 0 [] = frontier ⟨[], [], 0, []⟩
#guard compile pChoose 1 [true] = Prim.success (Val.nat 1)
#guard compile pChoose 1 [] = frontier ⟨[], [], 1, []⟩

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
