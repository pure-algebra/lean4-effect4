import Test.Codegen.TemplatesContract

/-!
UNCOMPILED G scope-stop probe, prepared 2026-09-30.

The public layerSamples[1]? at Test/Codegen/TemplatesContract.lean:58 contains
the private key and body declared at :25-28. This probe proves a definitional
equality to that actual list entry before making any typing claim about it.

The candidate below copies only G's amended effect-leaf equation, following
G/AuthorContractProbe.lean. It leaves the existing body checker unchanged;
this particular body contains no layer, so G does not change its body check.
No production source, test, register or generated file is modified.

Addendum 4 authorizes only leftWins, rightWins and the AuthorContract Counter
fixture as expected newly refused in-tree fixtures. This distinct sample is
therefore a fourth-fixture stop if the following theorems check. Its existing
test is about printing, so the test need not fail when layer typing changes.
-/

set_option autoImplicit false

namespace Research.Slice6.G.FourthFixtureProbe

open Effect4 Effect4.Machine Effect4.Program

def key : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩
def body : NativeEff := .bind (.succeed (.lit .unit)) (.succeed (.var 0))
def layer : LayerTerm NativeOp := .effect key body

/-- Select the actual public source entry; do not substitute a newly invented test. -/
def actualSample : Option (LayerTerm NativeOp) :=
  Test.Codegen.TemplatesContract.layerSamples[1]?

theorem exact_source_sample : actualSample = some layer := rfl

theorem exact_source_signature : Test.Codegen.TemplatesContract.sig = nativeSignature [] := rfl

theorem signature_carrier : Test.Codegen.TemplatesContract.sig.serviceTy key = some .nat := by
  decide +kernel

theorem body_check : Checker.check Test.Codegen.TemplatesContract.sig [] [0] body =
    .ok (EffTy.pure .unit) := by
  decide +kernel

theorem unit_does_not_fit_nat : Ty.sub Ty.unit.normalize Ty.nat.normalize = false := by
  decide +kernel

theorem existing_checker_accepts : Checker.checkLayer Test.Codegen.TemplatesContract.sig [] layer =
    .ok ⟨Effect4.Machine.Env.Requirement.single key, .never,
      Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

/-- The acceptance is explicitly pinned to the actual public sample, including its index. -/
theorem existing_source_sample_accepts :
    actualSample.map (Checker.checkLayer Test.Codegen.TemplatesContract.sig []) =
      some (.ok ⟨Effect4.Machine.Env.Requirement.single key, .never,
        Effect4.Machine.Env.Requirement.empty⟩) := by
  decide +kernel

/-- G's revised effect-leaf equation: closed body first, then key and subtype checks. -/
def revisedEffectLeaf (sig : Signature NativeOp) (p : List Nat)
    (service : ServiceKey) (program : NativeEff) : Except TypeRefusal LayerTy := do
  let t ← Checker.check sig [] (p ++ [0]) program
  let ty ← Checker.expect ⟨p, .serviceUnknown service⟩ (sig.serviceTy service)
  if Ty.sub t.answer.normalize ty.normalize then
    pure ⟨Effect4.Machine.Env.Requirement.single service, t.error, bodyRequires sig t⟩
  else throw ⟨p, .valueNotSubtype service t.answer ty⟩

theorem revised_leaf_refuses : revisedEffectLeaf Test.Codegen.TemplatesContract.sig [] key body =
    .error ⟨[], .valueNotSubtype key .unit .nat⟩ := by
  decide +kernel

/-- Apply the candidate only when the source-selected entry is an effect leaf.
Returning none for another constructor makes a changed source fixture visible. -/
def revisedSourceSample : Option (Except TypeRefusal LayerTy) :=
  actualSample.bind fun sample =>
    match sample with
    | .effect service program =>
      some (revisedEffectLeaf Test.Codegen.TemplatesContract.sig [] service program)
    | _ => none

theorem revised_source_sample_refuses : revisedSourceSample =
    some (.error ⟨[], .valueNotSubtype key .unit .nat⟩) := by
  decide +kernel

theorem same_source_sample_changes :
    Test.Codegen.TemplatesContract.layerSamples[1]? = some (.effect key body) ∧
    (Checker.checkLayer Test.Codegen.TemplatesContract.sig [] layer).toOption.isSome = true ∧
    revisedSourceSample = some (.error ⟨[], .valueNotSubtype key .unit .nat⟩) :=
  ⟨exact_source_sample, by decide +kernel, revised_source_sample_refuses⟩

#print axioms exact_source_sample
#print axioms exact_source_signature
#print axioms signature_carrier
#print axioms body_check
#print axioms unit_does_not_fit_nat
#print axioms existing_checker_accepts
#print axioms existing_source_sample_accepts
#print axioms revised_leaf_refuses
#print axioms revised_source_sample_refuses
#print axioms same_source_sample_changes

end Research.Slice6.G.FourthFixtureProbe
