import Effect4.Laws.Program.MeaningSound
import Test.Program.CompileContract

/-!
# Meaning soundness contract

The theorems of `Laws/Program/MeaningSound.lean` read on programs: a typed straight program's
exit has its type, and its run does not depend on the wrong-shape exit. The negative pins show
the premise is needed: an ill-typed program does depend on it.
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

/-- info: 'Effect4.Program.Denote.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sound
/-- info: 'Effect4.Program.Denote.meaning_never_wrong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaning_never_wrong
/-- info: 'Effect4.Program.Denote.meaning_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meaning_typed
/-- info: 'Effect4.Program.Denote.run_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_typed

end Test.Program.MeaningSoundContract
