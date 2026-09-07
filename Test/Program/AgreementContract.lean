import Effect4.Program.Agreement.Machine
import Test.Program.CompileContract

/-!
# Agreement contract — the theorem's hypotheses and its local run, pinned

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §9. `run_eq_meaning`
(`src/Effect4/Program/Agreement/Machine.lean`) says: a straight-line program, with fuel for
its depth and its commands, runs to its meaning's exit and stores, under the op budget or
past it. These guards pin, one program at a time, what the theorem consumes — `Plain`,
`depth`, `steps`, the local run of `Agreement.lean` — and the two roads of the run: the
exit within one loop entry, and the yield at the budget, the park, and the rounds of `flush`
(`pLong`, two yields deep). The oracle over `Api.run` itself is
`Test/Program/DenoteContract.lean`; the theorem is what makes those guards a corollary.

Every pin is a `#guard` over first-order values; no helper touches a `String`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.AgreementContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Test.Syntax.CompileContract (fuel pSucceed pBindSync pFail pCatch pMatchValue pMatchCause
  pMatchCauseReified pExit pOnExit pDie pRefSet pRefUpdate pRefModify pBranchTrue pBranchFalse
  pDeferred pForkJoin pYieldNow pMasked)

/-! ## The fragment: plain is straight minus `onExit` -/

#guard Plain pSucceed = true
#guard Plain pBindSync = true
#guard Plain pFail = true
#guard Plain pCatch = true
#guard Plain pMatchValue = true
#guard Plain pMatchCause = true
#guard Plain pMatchCauseReified = true
#guard Plain pExit = true
#guard Plain pDie = true
#guard Plain pRefSet = true
#guard Plain pRefUpdate = true
#guard Plain pRefModify = true
#guard Plain pBranchTrue = true
#guard Plain pBranchFalse = true

-- E4-DEN-CE-004, repaired the same day: `onExit` was straight (its meaning stated) but not
-- plain (its run not proved), because the `OnExit` frame's finalizer runs under a mask whose
-- restoring frame the pop leaves on the stack (`Frames.lean`, `ensure`). The local run now
-- models the mask (`maskStack`, the fiber's interruptible flag) and `Plain` is `Straight`.
#guard Straight pOnExit = true
#guard Plain pOnExit = true

/-- `Effect.onExit` inside a finalizer: the inner frame is met while the fiber is already
masked, so no second restoring frame is pushed (`maskStack false`). -/
def pNestedFinalizer : NativeEff :=
  .onExit (.succeed (.lit (.nat 1)))
    (.onExit (.succeed (.lit (.nat 2))) (.succeed (.lit (.nat 3))))

/-- `Effect.onExit` whose finalizer fails: the body's success is replaced by the finalizer's
failure, on both sides (`restoreAfterFinalizer`). -/
def pOnExitFails : NativeEff := .onExit (.succeed (.lit (.nat 1))) (.fail (.lit (.nat 8)))

#guard Plain pNestedFinalizer = true
#guard Plain pOnExitFails = true
#guard maskStack true [] = [Prim.setInterruptible true]
#guard maskStack false [] = []

#guard Plain pDeferred = false
#guard Plain pForkJoin = false
#guard Plain pYieldNow = false
#guard Plain pMasked = false

/-! ## The two measures the theorem's fuel and budget hypotheses read -/

#guard depth pSucceed = 1
#guard depth pBindSync = 2
#guard depth pRefSet = 3
#guard depth pMatchValue = 2
#guard steps pSucceed = 0
#guard steps pBindSync = 3
#guard steps pFail = 0
#guard steps pCatch = 2
#guard steps pRefSet = 7
#guard steps pBranchTrue = 1
#guard steps pOnExit = 12
#guard steps pNestedFinalizer = 10
#guard depth pNestedFinalizer = 3

-- The contract's fuel covers every plain program's depth and commands, and the budget its
-- steps.
#guard depth pRefSet ≤ fuel
#guard 2 * steps pRefSet + 6 ≤ fuel

/-! ## The local run: the frame machine over the stores, from the root -/

/-- The corollary `localRun_root` instantiated: `steps p + 1` local steps from the compiled
root over the empty stores finish with the meaning. -/
def localAgrees (p : NativeEff) : Bool :=
  localRun p (steps p + 1) (fiberOf (compile p fuel) []) Stores.empty ==
    some (meaning p [] Stores.empty)

#guard localAgrees pSucceed
#guard localAgrees pBindSync
#guard localAgrees pFail
#guard localAgrees pCatch
#guard localAgrees pMatchValue
#guard localAgrees pMatchCause
#guard localAgrees pMatchCauseReified
#guard localAgrees pExit
#guard localAgrees pDie
#guard localAgrees pRefSet
#guard localAgrees pRefUpdate
#guard localAgrees pRefModify
#guard localAgrees pBranchTrue
#guard localAgrees pBranchFalse
#guard localAgrees pOnExit
#guard localAgrees pOnExitFails
#guard localAgrees pNestedFinalizer

-- The finalizer runs masked and the mask lifts: the local run of `pOnExitFails` ends on an
-- interruptible fiber with the merged failure.
#guard (meaning pOnExitFails [] Stores.empty).1 = Exit.failure (Cause.fail (Err.tag 8))
#guard (meaning pNestedFinalizer [] Stores.empty).1 = Exit.success (Val.nat 1)
#guard (Api.run pNestedFinalizer fuel).exit = some (Exit.success (Val.nat 1))
#guard (Api.run pNestedFinalizer fuel).trace.any fun
  | RunEvent.finalizerProgram _ _ _ => true
  | _ => false

-- One step fewer is not enough for a program that takes every step: the bound is tight for
-- `pBindSync` (a push, a `sync`, its delivery, then the exit leaving the empty stack).
#guard localRun pBindSync (steps pBindSync) (fiberOf (compile pBindSync fuel) []) Stores.empty
  = none

/-! ## The invariants the simulation carries -/

#guard PlainCode (compile pRefSet fuel) = true
#guard PlainCode (compile pMatchCause fuel) = true
-- The `onExit` frame is plain code now, with its finalizer name; the frame a mask leaves is
-- a plain frame; an `onExit` under any other name or with the finalizer interruptible is not.
#guard PlainCode (compile pOnExit fuel) = true
#guard PlainCode (compile (.onExit (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))) fuel)
  = true
#guard PlainFrame (Prim.setInterruptible true) = true
#guard PlainFrame (Prim.setInterruptible false) = false
#guard PlainCode (Prim.onExit (Prim.success Val.unit) (EffName.fin (rootPoint fuel)) true) = false
#guard PlainCode (Prim.onExit (Prim.success Val.unit) (EffName.scopeClose 0) false) = false
#guard isSync (compile pBindSync fuel) = false
#guard isSync (Prim.sync (EffThunk.pure (rootPoint fuel))) = true

/-! ## The register rows -/

-- E4-DEN-CE-005 (repaired): the run past the op budget. The row's first witness is the
-- tape form: under the tape's `yieldVerdict` override the first iteration injects a yield
-- (the fiber parks on its own dispatcher and `flush` resumes it), and the run still finishes
-- with the meaning. The theorem used to carry `steps e + 2 ≤ defaultBudget` to keep that
-- path out of the proof; it no longer does.
def yielded : Api.Run :=
  Api.replay pBindSync fuel
    [RunDecision.yieldVerdict Api.root true, Api.evaluate, Api.flush]

#guard yielded.outcome == Api.Outcome.finished
#guard yielded.exit == some (meaning pBindSync [] Stores.empty).1
#guard yielded.stores == (meaning pBindSync [] Stores.empty).2
#guard yielded.trace.any fun
  | RunEvent.yieldInjected _ _ => true
  | _ => false
#guard (Api.run pBindSync fuel).trace.all fun
  | RunEvent.yieldInjected _ _ => false
  | _ => true

-- The second witness is the ordinary run of a program whose steps exceed the budget:
-- `chain n` is `n` binds of a `succeed`, `2n` local steps, all at the loop, so `pLong`
-- (`4200` steps, `4201` with the exit) spans three loop entries — the count reaches
-- `defaultBudget` twice, the root parks twice (`yieldInjected`, `parkedOn`), `flush` fires
-- it twice (`ranTask`, `resumedWith`, `started`), and the run still finishes with the
-- meaning. `pLong_agrees` below is the theorem's instance on it.
def chain : Nat → NativeEff
  | 0 => .succeed (.lit (.nat 0))
  | n + 1 => .bind (.succeed (.lit (.nat n))) (chain n)

theorem chain_straight : ∀ n, Straight (chain n) = true
  | 0 => rfl
  | n + 1 => by simp [chain, Straight, chain_straight n]

theorem chain_steps : ∀ n, steps (chain n) = 2 * n
  | 0 => rfl
  | n + 1 => by simp only [chain, steps, chain_steps n]; omega

theorem chain_depth : ∀ n, depth (chain n) = n + 1
  | 0 => rfl
  | n + 1 => by simp only [chain, depth, chain_depth n]; omega

def pLong : NativeEff := chain 2100
def fuelLong : Nat := 16384

#guard steps pLong = 4200
#guard depth pLong = 2101
#guard Straight pLong = true
#guard 2 * defaultBudget < steps pLong

def long : Api.Run := Api.run pLong fuelLong

#guard long.outcome == Api.Outcome.finished
#guard long.exit == some (meaning pLong [] Stores.empty).1
#guard long.stores == (meaning pLong [] Stores.empty).2
#guard (long.trace.filter fun
  | RunEvent.yieldInjected _ _ => true
  | _ => false).length == 2
#guard (long.trace.filter fun
  | RunEvent.resumedWith _ _ _ => true
  | _ => false).length == 2
#guard (long.trace.filter fun
  | RunEvent.started _ => true
  | _ => false).length == 3
-- the yield is injected at the budget, and the count restarts on every resume
#guard long.trace.all fun
  | RunEvent.yieldInjected _ atOp => atOp == defaultBudget
  | _ => true

/-! ## The statement, frozen -/

/-- The packet's theorem, as landed: the hypotheses are `Straight`, the depth under the
fuel, and the commands under the fuel — no op budget. -/
theorem run_eq_meaning_frozen (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      (Api.run e fuel).exit = some (meaning e [] Stores.empty).1 ∧
      (Api.run e fuel).stores = (meaning e [] Stores.empty).2 :=
  run_eq_meaning e fuel hs hd hfuel

/-- The theorem on the `onExit` program of the compile contract, its side conditions
discharged by `decide`. -/
theorem pOnExit_agrees :
    (Api.run pOnExit fuel).outcome = Api.Outcome.finished ∧
      (Api.run pOnExit fuel).exit = some (meaning pOnExit [] Stores.empty).1 ∧
      (Api.run pOnExit fuel).stores = (meaning pOnExit [] Stores.empty).2 :=
  run_eq_meaning pOnExit fuel (by decide) (by decide) (by decide)

/-- The theorem on one contract program, its side conditions discharged by `decide`: what the
`agrees` guard of `Test/Program/DenoteContract.lean` checked, now a consequence. -/
theorem pRefSet_agrees :
    (Api.run pRefSet fuel).outcome = Api.Outcome.finished ∧
      (Api.run pRefSet fuel).exit = some (meaning pRefSet [] Stores.empty).1 ∧
      (Api.run pRefSet fuel).stores = (meaning pRefSet [] Stores.empty).2 :=
  run_eq_meaning pRefSet fuel (by decide) (by decide) (by decide)

/-- The theorem past the budget: `pLong` yields twice under the ordinary run, and its side
conditions are the chain's measures. -/
theorem pLong_agrees :
    (Api.run pLong fuelLong).outcome = Api.Outcome.finished ∧
      (Api.run pLong fuelLong).exit = some (meaning pLong [] Stores.empty).1 ∧
      (Api.run pLong fuelLong).stores = (meaning pLong [] Stores.empty).2 :=
  run_eq_meaning pLong fuelLong (by unfold pLong; exact chain_straight 2100)
    (by unfold pLong fuelLong; rw [chain_depth]; omega)
    (by unfold pLong fuelLong; rw [chain_steps]; omega)

end Test.Program.AgreementContract
