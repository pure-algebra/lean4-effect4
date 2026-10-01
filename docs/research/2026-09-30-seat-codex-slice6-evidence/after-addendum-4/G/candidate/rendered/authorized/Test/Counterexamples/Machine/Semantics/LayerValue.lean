import Effect4.Api
import Effect4.Laws.Program.Typing.Sound

/-!
E4-PROV-CE-006: a layer leaf must supply a value below its key's declared service type.
The two former leaf rules are retained locally as `Reviewed.LayerHasTy`. Their carrier
claim is refuted by the same Boolean-at-nat and string-at-nat leaves. The current checker
refuses the original gap programs at their layer paths and keeps matching values.
These are finite admission controls, not runtime or whole-machine preservation theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Counterexamples.LayerValue
open Effect4 Effect4.Machine Effect4.Program
open Conform.Effect4.Typing (HasTy)

abbrev E := NativeEff

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def unknownKey : ServiceKey := ⟨⟨40⟩, ⟨40⟩⟩
def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def succOf (t : Term) : Term := .app "succ" (.cons t .nil)

def valueLeak : E :=
  .scoped (.provideLayer (.effect key (.succeed (s "x"))) false (.service key))
def succeedLeak : E := .provideLayer (.succeed key (.bool true)) false (.service key)
def crash2 : E :=
  .bind (.provideLayer (.succeed key (.bool true)) false (.service key))
    (.succeed (succOf (.var 0)))
def valueControl : E :=
  .scoped (.provideLayer (.effect key (.succeed (n 5))) false (.service key))
def untypedSucceed : E :=
  .provideLayer (.succeed unknownKey (.nat 5)) false (.succeed (.lit .unit))
def untypedEffect : E :=
  .provideLayer (.effect unknownKey (.succeed (n 5))) false (.succeed (.lit .unit))

namespace Reviewed
/-- Exactly the two pre-G leaf constructors; other layer constructors are not needed for
this counterexample. Body typing uses the unchanged succeed rule at the empty environment. -/
inductive LayerHasTy (sig : Signature NativeOp) : LayerTerm NativeOp → LayerTy → Prop
  | succeed {key : ServiceKey} {value : Lit} {v : Env.Val} :
      litVal value = some v →
      LayerHasTy sig (.succeed key value)
        ⟨Env.Requirement.single key, .never, Env.Requirement.empty⟩
  | effect {key : ServiceKey} {body : NativeEff} {t : EffTy} :
      HasTy sig [] body t →
      LayerHasTy sig (.effect key body)
        ⟨Env.Requirement.single key, t.error, bodyRequires sig t⟩
end Reviewed

def leafTy : LayerTy := ⟨Env.Requirement.single key, .never, Env.Requirement.empty⟩

theorem key_service_nat : (nativeSignature []).serviceTy key = some .nat := by
  decide +kernel

theorem old_succeed_admitted :
    Reviewed.LayerHasTy (nativeSignature []) (.succeed key (.bool true)) leafTy :=
  .succeed rfl

theorem old_effect_admitted :
    Reviewed.LayerHasTy (nativeSignature []) (.effect key (.succeed (s "x"))) leafTy :=
  .effect (.succeed rfl)

/-- The old succeed rule cannot justify the declared nat carrier. -/
theorem old_succeed_carrier_claim_false : ¬ (
    Reviewed.LayerHasTy (nativeSignature []) (.succeed key (.bool true)) leafTy →
    Ty.sub (Lit.ty (.bool true)).normalize Ty.nat.normalize = true) := by
  intro h
  exact Bool.noConfusion (h old_succeed_admitted)

/-- The old effect rule has the same gap for its successful answer. -/
theorem old_effect_carrier_claim_false : ¬ (
    Reviewed.LayerHasTy (nativeSignature []) (.effect key (.succeed (s "x"))) leafTy →
    Ty.sub Ty.string.normalize Ty.nat.normalize = true) := by
  intro h
  exact Bool.noConfusion (h old_effect_admitted)

theorem valueLeak_refused : Api.typeOf valueLeak [] = none := by decide +kernel
theorem valueLeak_location : Api.explain valueLeak [] =
    some ⟨[0, 0], .valueNotSubtype key .string .nat⟩ := by decide +kernel

theorem succeedLeak_refused : Api.typeOf succeedLeak [] = none := by decide +kernel
theorem succeedLeak_location : Api.explain succeedLeak [] =
    some ⟨[0], .valueNotSubtype key .bool .nat⟩ := by decide +kernel

theorem crash2_refused : Api.typeOf crash2 [] = none := by decide +kernel
theorem crash2_location : Api.explain crash2 [] =
    some ⟨[0, 0], .valueNotSubtype key .bool .nat⟩ := by decide +kernel

theorem untypedSucceed_refused : Api.typeOf untypedSucceed [] = none := by decide +kernel
theorem untypedSucceed_location : Api.explain untypedSucceed [] =
    some ⟨[0], .serviceUnknown unknownKey⟩ := by decide +kernel

theorem untypedEffect_refused : Api.typeOf untypedEffect [] = none := by decide +kernel
theorem untypedEffect_location : Api.explain untypedEffect [] =
    some ⟨[0], .serviceUnknown unknownKey⟩ := by decide +kernel

theorem valueControl_checked : Api.typeOf valueControl [] = some (EffTy.pure .nat) := by
  decide +kernel

/-- Literal-alphabet refusal remains first, including at an unknown key. -/
theorem literal_refusal_first :
    Checker.checkLayer (nativeSignature []) [] (.succeed unknownKey (.str "x")) =
      .error ⟨[], .literalOutsideAlphabet (.str "x")⟩ := by decide +kernel

/-- Existing effect-body refusal remains before the key lookup. -/
theorem effect_body_refusal_first :
    Checker.checkLayer (nativeSignature []) [] (.effect unknownKey (.succeed (.var 0))) =
      .error ⟨[0], .term (.var 0)⟩ := by
  decide +kernel

#print axioms key_service_nat
#print axioms old_succeed_admitted
#print axioms old_effect_admitted
#print axioms old_succeed_carrier_claim_false
#print axioms old_effect_carrier_claim_false
#print axioms valueLeak_refused
#print axioms valueLeak_location
#print axioms succeedLeak_refused
#print axioms succeedLeak_location
#print axioms crash2_refused
#print axioms crash2_location
#print axioms untypedSucceed_refused
#print axioms untypedSucceed_location
#print axioms untypedEffect_refused
#print axioms untypedEffect_location
#print axioms valueControl_checked
#print axioms literal_refusal_first
#print axioms effect_body_refusal_first

end Test.Counterexamples.LayerValue
