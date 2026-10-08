import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.TypedRun
import Test.Program.LoopSoundContract

/-!
# Loop agreement contract

The local machine run on the loop programs: it finishes with the budgeted meaning's exit and
stores, which is what `localRun_rootB` proves for every program of `Looped`: a loop alone,
nested, under a decision, a handler, a finalizer and a reified exit.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.LoopAgreementContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Test.Syntax.CompileContract (pIterateCount pIterateAnswer pIterateRef pIterateWide)
open Test.Program.DenoteBContract (pLoopUnderSelect pLoopCaught pLoopExit pLoopNested)
open Test.Program.LoopSoundContract (pLoopFinalizer)

/-- The local run at a generous step count agrees with the budgeted meaning at budget 9. -/
def localAgrees (e : NativeEff) : Bool :=
  match localRun e 400 (fiberOf (compile e 40) []) Stores.empty, meaningB 9 e [] Stores.empty with
  | some (ex, s), (some ex', s') => ex == ex' && s == s'
  | _, _ => false

def covered : List NativeEff :=
  [pIterateCount, pIterateAnswer, pIterateRef, pIterateWide, pLoopNested, pLoopUnderSelect,
   pLoopCaught, pLoopExit, pLoopFinalizer]

#guard covered.all fun e => Looped e && depthB e ≤ 40 && localAgrees e

/-! ## The machine itself, on every loop program of the battery

`loopAgreement` says the machine finishes with the budgeted meaning's answer past a bound. The
guard reads it at one fuel: the ordinary run of each program agrees with the meaning at
budget 9, exit and stores. -/

def machineAgrees (e : NativeEff) : Bool :=
  let r := Api.run e 400
  match meaningB 9 e [] Stores.empty with
  | (some ex, s) => r.outcome == Api.Outcome.finished && r.exit == some ex && r.stores == s
  | _ => false

#guard covered.all machineAgrees
-- The fuel bound the theorem names is a number one can compute.
#guard covered.all fun e => max (depthB e) (2 * (boundB 9 e + 1) + 4) ≤ 400

end Test.Program.LoopAgreementContract
