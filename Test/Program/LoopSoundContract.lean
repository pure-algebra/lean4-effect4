import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.TypedRun
import Test.Program.DenoteBContract

/-!
# Loop soundness contract

`Laws/Program/LoopSound.lean` read on the loop programs of the other contracts: at every
budget a typed loop-bearing program's run does not depend on the wrong-shape exit, finished or
not. The negative pins are loops that are in the fragment and ill-typed, and they do depend on
it: a step outside the cursor type, and a result that does not evaluate.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Program.LoopSoundContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Test.Syntax.CompileContract (pIterateCount pIterateAnswer pIterateRef pIterateWide
  pIterateBadResult)
open Test.Program.DenoteBContract (pLoopUnderSelect pLoopCaught pLoopOnExit pLoopExit
  pLoopNested)

def marker : ExitV := Exit.failure (Cause.die (Defect.user 424242))

def neverWrongAt (k : Nat) (e : NativeEff) : Bool :=
  (runP (denoteBWith marker k e []) Stores.empty).1 == (meaningB k e [] Stores.empty).1

/-- A loop in a finalizer, typed: under `onExit` the finalizer's binder 0 is the reified exit,
so the loop's cursor is `var 1` and its body's answer `var 2`. -/
def pLoopFinalizer : NativeEff :=
  .onExit pIterateCount
    (.iterate .nat (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil)) (.var 2) (.var 1)
      (.succeed (.lit (.nat 7))))

def typedLoops : List NativeEff :=
  [pIterateCount, pIterateAnswer, pIterateRef, pIterateWide, pLoopUnderSelect, pLoopCaught,
   pLoopFinalizer, pLoopExit, pLoopNested]

#guard typedLoops.all fun e => Looped e && (Api.typeOf e).isSome
#guard typedLoops.all fun e => [0, 1, 3, 4, 9].all fun k => neverWrongAt k e

-- Found by the theorem, 2026-09-17: `pLoopOnExit` puts a closed loop under `onExit`, where
-- its `var 0` is the reified exit and not the cursor. It is ill-typed, and from the budget at
-- which the body finishes it goes wrong. The machine goes wrong the same way, which is why
-- `DenoteBContract`'s agreement guard holds of it.
#guard Looped pLoopOnExit && (Api.typeOf pLoopOnExit).isNone
#guard neverWrongAt 3 pLoopOnExit && !neverWrongAt 4 pLoopOnExit

-- In the fragment, ill-typed, and wrong: the result term has no binder to read.
#guard Looped pIterateBadResult && (Api.typeOf pIterateBadResult).isNone
#guard !neverWrongAt 4 pIterateBadResult
#guard (runP (denoteBWith marker 4 pIterateBadResult []) Stores.empty).1 == some marker

/-- info: 'Effect4.Program.Denote.soundB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms soundB
/-- info: 'Effect4.Program.Denote.iter_soundB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms iter_soundB
/-- info: 'Effect4.Program.Denote.meaningB_never_wrong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaningB_never_wrong
/-- info: 'Effect4.Program.Denote.meaningB_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaningB_typed
/-- info: 'Effect4.Program.Denote.meaningB_stores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaningB_stores

/-! ## On the certificate a caller holds -/

-- The whole-program checker and `effTy` agree on every fragment program of this battery.
#guard (typedLoops ++ [pLoopOnExit, pIterateBadResult]).all fun e =>
  Api.typeOf e == effTy nativeSignature [] e

/-- info: 'Effect4.Program.Denote.typeOfProgram_looped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms typeOfProgram_looped
/-- info: 'Effect4.Program.Denote.TypedProgram.run_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TypedProgram.run_sound
/-- info: 'Effect4.Program.Denote.TypedProgram.run_sound_of_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TypedProgram.run_sound_of_agreement

end Test.Program.LoopSoundContract
