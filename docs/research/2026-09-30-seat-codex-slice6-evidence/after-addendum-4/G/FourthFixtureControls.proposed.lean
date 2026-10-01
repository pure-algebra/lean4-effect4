import Test.Codegen.TemplatesContract

/-! Proposed post-G controls for the exact fourth fixture. These fail on the current pre-G
checker by design. No repository file has been changed and no Lean command has run here. -/
set_option autoImplicit false
namespace Test.Counterexamples.LayerValue.TemplateFixture
open Effect4 Effect4.Machine Effect4.Program

def key : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩
def body : NativeEff := .bind (.succeed (.lit .unit)) (.succeed (.var 0))

theorem exact_source_effect :
    Test.Codegen.TemplatesContract.layerSamples[1]? = some (.effect key body) := rfl

theorem template_effect_leaf_refused :
    (Test.Codegen.TemplatesContract.layerSamples[1]?).map
      (Checker.checkLayer Test.Codegen.TemplatesContract.sig []) =
        some (.error ⟨[], .valueNotSubtype key .unit .nat⟩) := by
  decide +kernel

/-- The same real key with its neighboring nat-valued leaf remains accepted. -/
theorem exact_source_succeed :
    Test.Codegen.TemplatesContract.layerSamples[0]? = some (.succeed key (.nat 1)) := rfl

theorem template_succeed_leaf_accepted :
    (Test.Codegen.TemplatesContract.layerSamples[0]?).map
      (Checker.checkLayer Test.Codegen.TemplatesContract.sig []) =
        some (.ok ⟨Env.Requirement.single key, .never, Env.Requirement.empty⟩) := by
  decide +kernel

#print axioms exact_source_effect
#print axioms template_effect_leaf_refused
#print axioms exact_source_succeed
#print axioms template_succeed_leaf_accepted
end Test.Counterexamples.LayerValue.TemplateFixture
