import Effect4.Laws.Program.MeaningSound
import Test.Program.CompileContract

/-!
# Meaning soundness contract

The theorems of `Laws/Program/MeaningSound.lean` read on programs: a typed straight program's
exit has its type, and its run does not depend on the wrong-shape exit. The negative pins show
the premise is needed: an ill-typed program does depend on it. The restated invariant (decisions
row 209: the environment fits at a world, and the store fits) is ascribed at its exact
proposition, so a declaration that keeps a frozen name but weakens the statement fails here.
-/

set_option autoImplicit false

namespace Test.Program.MeaningSoundContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Test.Syntax.CompileContract (pSucceed pBindSync)

/-- A marker no program produces, standing in for the wrong-shape exit. -/
def marker : ExitV := Exit.failure (Cause.die (Defect.user 424242))

def neverWrong (e : NativeEff) : Bool :=
  (runP (denoteWith marker e []) Stores.empty).1 == (meaning e [] Stores.empty).1

/-- Ill-typed: a variable with no binder. It is straight, and it goes wrong. -/
def pUnbound : NativeEff := .succeed (.var 0)

/-- Ill-typed: a decision over a number. -/
def pBadSelect : NativeEff :=
  .select (.lit (.nat 1)) .bool (.succeed (.lit .unit)) (.succeed (.lit .unit))

#guard [pSucceed, pBindSync].all fun e => Straight e && (Api.typeOf e).isSome && neverWrong e
#guard Straight pUnbound && (Api.typeOf pUnbound).isNone && !neverWrong pUnbound
#guard Straight pBadSelect && (Api.typeOf pBadSelect).isNone && !neverWrong pBadSelect
#guard (runP (denoteWith marker pUnbound []) Stores.empty).1 == marker

/-! ## The restated statements, ascribed (decisions row 209) -/

/-- What a run keeps: the environment fits at the world, and the store fits. -/
example (tys : TyEnv) (env : List Val) (w : Typed.World) :
    TypedAt tys env w ↔ Typed.EnvTyped w tys env ∧ StoreFits w :=
  ⟨fun h => ⟨h.fits, h.store⟩, fun h => ⟨h.1, h.2⟩⟩

/-- One run of a pair of programs: they run alike, and the run reaches a later world over the
stores it leaves, whose store fits, at which the exit satisfies `Typed.ExitOk`. -/
example (pw pd : Effects.Program StoreSig ExitV) (w : Typed.World) (a e : Ty) :
    SoundP pw pd w a e ↔ runP pw w.state = runP pd w.state ∧
      ∃ w', w'.state = (runP pd w.state).2 ∧ StoreOk w w' ∧
        Typed.ExitOk w' ⟨a, e, Env.Requirement.empty⟩ (runP pd w.state).1 :=
  ⟨fun h => ⟨h.independent, h.reaches⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `sound`: from every world whose store fits, in every environment typed there. -/
example : ∀ (bad : ExitV) (e : NativeEff) (tys : TyEnv) (env : List Val) (w : Typed.World)
    (t : EffTy), Straight e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env w → Sound bad e env w t :=
  @sound

/-- `meaning_stores`: the stores a typed straight program leaves are the state of a world whose
store fits. -/
example : ∀ (e : NativeEff) (t : EffTy), Straight e = true →
    effTy nativeSignature [] e = some t →
    ∃ w : Typed.World, w.state = (meaning e [] Stores.empty).2 ∧ StoreFits w :=
  @meaning_stores

end Test.Program.MeaningSoundContract
