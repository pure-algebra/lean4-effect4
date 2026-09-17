import Effect4.Laws.Program.Agreement.Loop
import Test.Program.LoopSoundContract

/-!
# Loop agreement contract (layer A)

The local machine run on the loop programs: it finishes with the budgeted meaning's exit and
stores, which is what `localRun_rootB` proves for `LoopedSeq`. The guards also run the forms
the theorem does not cover yet (a loop under a decision, a handler, a finalizer, a reified
exit): the agreement holds of them too, and the proof is owed.
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

def covered : List NativeEff := [pIterateCount, pIterateAnswer, pIterateRef, pIterateWide, pLoopNested]
def owed : List NativeEff := [pLoopUnderSelect, pLoopCaught, pLoopExit, pLoopFinalizer]

#guard covered.all fun e => LoopedSeq e && depthB e ≤ 40 && localAgrees e
#guard owed.all fun e => Looped e && !LoopedSeq e && localAgrees e

/-- info: 'Effect4.Program.Agreement.loop_reaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms loop_reaches
/-- info: 'Effect4.Program.Agreement.localRun_compileB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms localRun_compileB
/-- info: 'Effect4.Program.Agreement.localRun_rootB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms localRun_rootB

end Test.Program.LoopAgreementContract
