import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.TypedRun
import Test.Program.DenoteBContract

/-!
# Loop soundness contract

`Laws/Program/LoopSound.lean` read on the loop programs of the other contracts: at every
budget a typed loop-bearing program's run does not depend on the wrong-shape exit, finished or
not. The negative pins are loops that are in the fragment and ill-typed, and they do depend on
it: a step outside the cursor type, and a result that does not evaluate. The restated
invariant (decisions row 209: the environment fits at a world, and the store fits) is ascribed at
its exact proposition.
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
    (.iterate none (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil)) (.var 2) (.var 1)
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

/-! ## The restated statements, ascribed (decisions row 209) -/

/-- One budgeted run of a pair of programs: they run alike, and the run reaches a later world
over the stores it leaves, whose store fits, at which a finished exit satisfies `Typed.ExitOk`. -/
example (pw pd : Effects.Program StoreSig (Option ExitV)) (w : Typed.World) (a e : Ty) :
    SoundB pw pd w a e ↔ runP pw w.state = runP pd w.state ∧
      ∃ w', w'.state = (runP pd w.state).2 ∧ StoreOk w w' ∧
        ∀ ex, (runP pd w.state).1 = some ex → Typed.ExitOk w' ⟨a, e, Env.Requirement.empty⟩ ex :=
  ⟨fun h => ⟨h.independent, h.reaches⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `soundB`: at every budget, from every world whose store fits, in every environment typed
there. -/
example : ∀ (bad : ExitV) (k : Nat) (e : NativeEff) (tys : TyEnv) (env : List Val)
    (w : Typed.World) (t : EffTy), Looped e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env w →
    SoundB (denoteBWith bad k e env) (denoteB k e env) w t.answer t.error :=
  @soundB

/-- `meaningB_stores`: finished or not, the stores are the state of a world whose store fits. -/
example : ∀ (k : Nat) (e : NativeEff) (t : EffTy), Looped e = true →
    effTy nativeSignature [] e = some t →
    ∃ w : Typed.World, w.state = (meaningB k e [] Stores.empty).2 ∧ StoreFits w :=
  @meaningB_stores

/-! ## On the certificate a caller holds -/

-- The whole-program checker and `effTy` agree on every fragment program of this battery.
#guard (typedLoops ++ [pLoopOnExit, pIterateBadResult]).all fun e =>
  Api.typeOf e == effTy nativeSignature [] e

end Test.Program.LoopSoundContract
