import Effect4.Laws.Program.Denote
import Effect4.Api
import Test.Program.CompileContract

/-!
# Denote contract — the straight-line meaning against the machine, pinned

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §4.3. For every program of
`Test/Program/CompileContract.lean` in the fragment (`Straight p = true`), `meaning p []
Stores.empty` is what `Api.run p fuel` answers: the same exit, the same stores, a finished
run. These guards are the executable oracle of the packet's stated theorem `run_eq_meaning`,
one program at a time; the theorem replaces them and keeps them as its anti-vacuity kit.

Every pin is a `#guard` over first-order values; no helper touches a `String`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.DenoteContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Test.Syntax.CompileContract (fuel pSucceed pBindSync pFail pCatch pMatchValue pMatchCause
  pMatchCauseReified pExit pOnExit pDie pRefSet pRefUpdate pRefModify pBranchTrue pBranchFalse
  pDeferred pForkJoin pRace pScoped pGenTwoYields pWhileLoop pYieldNow pMasked)

/-- The oracle: on the ordinary run (`evaluate` then `flush`) the machine finishes with the
meaning's exit and the meaning's stores. -/
def agrees (p : NativeEff) : Bool :=
  let r := Api.run p fuel
  let m := meaning p [] Stores.empty
  r.outcome == Api.Outcome.finished && r.exit == some m.1 && r.stores == m.2

/-! ## The fragment, by program -/

#guard Straight pSucceed = true
#guard Straight pBindSync = true
#guard Straight pFail = true
#guard Straight pCatch = true
#guard Straight pMatchValue = true
#guard Straight pMatchCause = true
#guard Straight pMatchCauseReified = true
#guard Straight pExit = true
#guard Straight pOnExit = true
#guard Straight pDie = true
#guard Straight pRefSet = true
#guard Straight pRefUpdate = true
#guard Straight pRefModify = true
#guard Straight pBranchTrue = true
#guard Straight pBranchFalse = true

-- Outside the fragment: a park, a fork, a race, a scope, a generator, a loop, a
-- yield, a mask.
#guard Straight pDeferred = false
#guard Straight pForkJoin = false
#guard Straight pRace = false
#guard Straight pScoped = false
#guard Straight pGenTwoYields = false
#guard Straight pWhileLoop = false
#guard Straight pYieldNow = false
#guard Straight pMasked = false

/-! ## The oracle, one program at a time -/

#guard agrees pSucceed
#guard agrees pBindSync
#guard agrees pFail
#guard agrees pCatch
#guard agrees pMatchValue
#guard agrees pMatchCause
#guard agrees pMatchCauseReified
#guard agrees pExit
#guard agrees pOnExit
#guard agrees pDie
#guard agrees pRefSet
#guard agrees pRefUpdate
#guard agrees pRefModify
#guard agrees pBranchTrue
#guard agrees pBranchFalse

-- The meanings themselves, so a change to the machine and a change to the denotation that
-- agree with each other still have to agree with these.
#guard (meaning pBindSync [] Stores.empty).1 = Exit.success (Val.nat 2)
#guard (meaning pRefSet [] Stores.empty).1 = Exit.success (Val.nat 7)
#guard (meaning pRefSet [] Stores.empty).2.refs = [Val.nat 7]
#guard (meaning pRefModify [] Stores.empty).1 = Exit.success (Val.nat 5)
#guard (meaning pRefModify [] Stores.empty).2.refs = [Val.nat 6]
#guard (meaning pOnExit [] Stores.empty).1 = Exit.success (Val.nat 1)
#guard (meaning pOnExit [] Stores.empty).2.refs = [Val.nat 1]
#guard (meaning pExit [] Stores.empty).1 = Exit.success (Val.exitErr (Cause.fail (Err.tag 7)))
#guard (meaning pDie [] Stores.empty).1 = Exit.failure (Cause.die (Defect.user 3))

/-! ## A failing finalizer under `onExit`: the merged cause

`Effect.onExit` whose finalizer fails: the body's success is replaced by the finalizer's
failure (`restoreAfterFinalizer`), on both sides. -/

def pOnExitFails : NativeEff := .onExit (.succeed (.lit (.nat 1))) (.fail (.lit (.nat 8)))

#guard Straight pOnExitFails = true
#guard agrees pOnExitFails
#guard (meaning pOnExitFails [] Stores.empty).1 = Exit.failure (Cause.fail (Err.tag 8))

/-! ## The register rows -/

-- E4-DEN-CE-001: an ill-formed `sync` term answers `unit` on both sides (the compile's
-- `syncValueAt` is `getD Val.unit`); an ill-formed `succeed` is the `badName` defect on both.
#guard (meaning (.sync (.var 3)) [] Stores.empty).1 = Exit.success Val.unit
#guard (Api.run (.sync (.var 3)) fuel).exit = some (Exit.success Val.unit)
#guard (meaning (.succeed (.var 3)) [] Stores.empty).1 = badShapeExit
#guard (Api.run (.succeed (.var 3)) fuel).exit = some badShapeExit

-- E4-DEN-CE-002: the handler's `none` arm is the machine's fallback. A program cannot spell
-- a handle (`Lit` has none), so the row is stated at the handler and the interp.
/-- The handler's answer, typed as the pair it is. -/
def handled (o : SyncOp) (s : Stores) : Val × Stores := (storeHandler.handle o).run s

#guard handled (SyncOp.refGet ⟨5⟩) Stores.empty = (Val.unit, Stores.empty)
#guard (interpOf pSucceed).syncState (EffThunk.op (SyncOp.refGet ⟨5⟩)) Stores.empty = none
#guard (interpOf pSucceed).syncValue (EffThunk.op (SyncOp.refGet ⟨5⟩)) = Val.unit

-- E4-DEN-CE-003: the machine's trace carries frame events the algebra has no producer for;
-- the agreement is on the exit and the stores.
#guard (Api.run pBindSync fuel).trace.any fun
  | RunEvent.frame _ _ => true
  | _ => false

end Test.Program.DenoteContract
