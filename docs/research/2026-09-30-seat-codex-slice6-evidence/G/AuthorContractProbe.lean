import Test.Program.AuthorContract

/-!
G stop probe for the existing guard at Test/Program/AuthorContract.lean:267-268.
The expression is copied verbatim and uses that module's actual Counter declaration.
Its elaboration is an effect leaf with a string-returning body, not a succeed leaf.

The proposed check below copies only G's revised effect-leaf equation. It retains
Checker.check at the original empty environment and body path before comparing
the inferred answer with the signature's service carrier. This fixture's body has
no layer, so its body check is unchanged by G. No source checker is modified.
-/

set_option autoImplicit false
namespace Research.Slice6.G.AuthorContractProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.AuthorContract (Counter)

/-- The exact authored expression whose existing guard expects acceptance. -/
def authorFixture : LayerSrc NativeOp := Layer.value Counter.key (str "x")

def body : NativeEff := .succeed (.lit (.str "x"))
def layer : LayerTerm NativeOp := .effect Counter.key body

/-- The authoring helper uses the effect constructor; substituting a succeed leaf
would instead exercise the older literal-alphabet refusal. -/
theorem exact_elaboration : elaborateLayer authorFixture = .ok layer := rfl

theorem actual_counter_key : Counter.key = ⟨⟨4⟩, ⟨4⟩⟩ := rfl

theorem actual_counter_carrier : Counter.carrier = .nat := rfl

theorem signature_carrier : (nativeSignature []).serviceTy Counter.key = some .nat := by
  decide +kernel

theorem literal_type : Lit.ty (.str "x") = .string := rfl

theorem body_check : Checker.check (nativeSignature []) [] [0] body =
    .ok (EffTy.pure .string) := by
  decide +kernel

theorem existing_guard_accepts :
    (Effect4.Api.checkLayer authorFixture).toOption.map (fun l => l.provides) =
      some [Counter.key] := by
  decide +kernel

theorem existing_checker_accepts : Checker.checkLayer (nativeSignature []) [] layer =
    .ok ⟨Effect4.Machine.Env.Requirement.single Counter.key, .never, Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

/-- G's revised effect-leaf equation, with the original body check intact. -/
def revisedEffectLeaf (sig : Signature NativeOp) (p : List Nat)
    (key : ServiceKey) (program : NativeEff) : Except TypeRefusal LayerTy := do
  let t ← Checker.check sig [] (p ++ [0]) program
  let ty ← Checker.expect ⟨p, .serviceUnknown key⟩ (sig.serviceTy key)
  if Ty.sub t.answer.normalize ty.normalize then
    pure ⟨Effect4.Machine.Env.Requirement.single key, t.error, bodyRequires sig t⟩
  else throw ⟨p, .valueNotSubtype key t.answer ty⟩

theorem revised_leaf_refuses : revisedEffectLeaf (nativeSignature []) [] Counter.key body =
    .error ⟨[], .valueNotSubtype Counter.key .string .nat⟩ := by
  decide +kernel

/-- Pin the refusal to the authored expression's exact elaborated constructor and body. -/
theorem same_authored_layer_changes :
    elaborateLayer authorFixture = .ok (.effect Counter.key body) ∧
    (Checker.checkLayer (nativeSignature []) [] (.effect Counter.key body)).toOption.isSome = true ∧
    revisedEffectLeaf (nativeSignature []) [] Counter.key body =
      .error ⟨[], .valueNotSubtype Counter.key .string .nat⟩ :=
  ⟨exact_elaboration, by decide +kernel, revised_leaf_refuses⟩

/-- The synthetic succeed spelling would be a different test with a different refusal. -/
theorem succeed_is_not_this_fixture :
    Checker.checkLayer (nativeSignature []) [] (.succeed Counter.key (.str "x")) =
      .error ⟨[], .literalOutsideAlphabet (.str "x")⟩ := by
  decide +kernel

#print axioms exact_elaboration
#print axioms actual_counter_key
#print axioms actual_counter_carrier
#print axioms signature_carrier
#print axioms literal_type
#print axioms body_check
#print axioms existing_guard_accepts
#print axioms existing_checker_accepts
#print axioms revised_leaf_refuses
#print axioms same_authored_layer_changes
#print axioms succeed_is_not_this_fixture

end Research.Slice6.G.AuthorContractProbe
