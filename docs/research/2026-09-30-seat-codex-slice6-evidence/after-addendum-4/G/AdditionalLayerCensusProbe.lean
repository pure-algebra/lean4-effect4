import Test.Program.Gen

/-! UNCOMPILED, source-tied corpus diagnostic probe. No production change.
The retained corpus index already refuses g141; this is not a fifth newly refused program.
Its earlier layer leaf should become the first refusal under G, at [0,0].
The source equality below must check before relying on the retained JSON observation. -/
set_option autoImplicit false
namespace Research.Slice6.G.AdditionalLayerCensus
open Effect4 Effect4.Program

def key : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩
def body : Eff NativeOp := .yieldNow 0
def program : Eff NativeOp :=
  .provideLayer (.orDie (.effect key body)) false
    (.bind (.awaitFiber (.app "snd" (.cons (.lit (.nat 1)) .nil)) .joinEffect)
      (.service ⟨⟨8⟩, ⟨4⟩⟩))

theorem exact_source_program : Test.Program.Gen.program 141 4 = program := by
  decide +kernel

theorem already_refused : Api.wellTyped (Test.Program.Gen.program 141 4) = false := by
  decide +kernel

theorem old_layer_accepted :
    (Checker.checkLayer (nativeSignature []) [0, 0] (.effect key body)).toOption.isSome = true := by
  decide +kernel

theorem body_answer_is_unit :
    (Checker.check (nativeSignature []) [] [0, 0, 0] body).toOption.map EffTy.answer = some .unit := by
  decide +kernel

def revisedEffectLeaf (sig : Signature NativeOp) (p : List Nat)
    (service : ServiceKey) (program : Eff NativeOp) : Except TypeRefusal LayerTy := do
  let t ← Checker.check sig [] (p ++ [0]) program
  let ty ← Checker.expect ⟨p, .serviceUnknown service⟩ (sig.serviceTy service)
  if Ty.sub t.answer.normalize ty.normalize then
    pure ⟨Effect4.Machine.Env.Requirement.single service, t.error, bodyRequires sig t⟩
  else throw ⟨p, .valueNotSubtype service t.answer ty⟩

theorem new_leaf_refused : revisedEffectLeaf (nativeSignature []) [0, 0] key body =
    .error ⟨[0, 0], .valueNotSubtype key .unit .nat⟩ := by
  decide +kernel

#print axioms exact_source_program
#print axioms already_refused
#print axioms old_layer_accepted
#print axioms body_answer_is_unit
#print axioms new_leaf_refused
end Research.Slice6.G.AdditionalLayerCensus
