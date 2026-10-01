import Effect4.Api
import Effect4.Program.Provision

/-! UNCOMPILED. Distinguish the standalone native projection of an existing docs
layer from the complete raw-runtime program that uses it. The complete program
was already refused, because dbKey has no native service declaration. The layer
alone was formerly accepted because checkLayer did not consult that declaration.
Exact source occurrence: Provision.lean:636, and its orDie twin at :638. -/
set_option autoImplicit false
namespace Research.Slice6.G.ProjectedLayerBoundary
open Effect4 Effect4.Program Effect4.Program.Provision

def projected : LayerTerm NativeOp := .effect dbKey (.fail (.lit (.nat 7)))
def actualProjection : Option (LayerTerm NativeOp) :=
  docsLayer (.effect dbKey (.fail (.lit (.nat 7))))

theorem exact_source_projection : actualProjection = some projected := rfl

theorem docs_layer_accepted :
    Checker.checkLayer docsSig [] (.effect dbKey (.fail (.lit (.nat 7)))) =
      .ok ⟨Effect4.Machine.Env.Requirement.single dbKey, .nat,
        Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

theorem old_native_layer_accepted :
    Checker.checkLayer (nativeSignature []) [] projected =
      .ok ⟨Effect4.Machine.Env.Requirement.single dbKey, .nat,
        Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

theorem native_key_unknown : (nativeSignature []).serviceTy dbKey = none := by
  decide +kernel

/-- This is the exact program run by provideThenService projected dbKey.
The source use supplies no typing signature: runNative compiles/runs it directly. -/
def completeProgram : Eff NativeOp := .provideLayer projected true (.service dbKey)

theorem exact_runtime_use : provideThenService projected dbKey = runNative completeProgram := rfl

theorem exact_source_runtime_use :
    (docsLayer (.effect dbKey (.fail (.lit (.nat 7))))).map (provideThenService · dbKey) =
      some (runNative completeProgram) := rfl

theorem complete_program_already_refused : Api.wellTyped completeProgram = false := by
  decide +kernel

def revisedEffectLeaf {Op : Type} (sig : Signature Op) (p : List Nat)
    (service : ServiceKey) (program : Eff Op) : Except TypeRefusal LayerTy := do
  let t ← Checker.check sig [] (p ++ [0]) program
  let ty ← Checker.expect ⟨p, .serviceUnknown service⟩ (sig.serviceTy service)
  if Ty.sub t.answer.normalize ty.normalize then
    pure ⟨Effect4.Machine.Env.Requirement.single service, t.error, bodyRequires sig t⟩
  else throw ⟨p, .valueNotSubtype service t.answer ty⟩

theorem new_native_leaf_refused :
    revisedEffectLeaf (nativeSignature []) [] dbKey (.fail (.lit (.nat 7))) =
      .error ⟨[], .serviceUnknown dbKey⟩ := by
  decide +kernel

/-- Under the docs signature, the original layer has a declared Db service and its
never answer is a subtype. This comparison does not assert that the runtime use
above invokes a checker; it does not. -/
theorem revised_docs_leaf_still_accepted :
    revisedEffectLeaf docsSig [] dbKey (.fail (.lit (.nat 7))) =
      .ok ⟨Effect4.Machine.Env.Requirement.single dbKey, .nat,
        Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

/-- The second source occurrence is the orDie wrapper of the same projected leaf. -/
theorem exact_orDie_source_projection :
    docsLayer (.orDie (.effect dbKey (.fail (.lit (.nat 7))))) = some (.orDie projected) := rfl

theorem old_native_orDie_layer_accepted :
    Checker.checkLayer (nativeSignature []) [] (.orDie projected) =
      .ok ⟨Effect4.Machine.Env.Requirement.single dbKey, .never,
        Effect4.Machine.Env.Requirement.empty⟩ := by
  decide +kernel

theorem complete_orDie_program_already_refused :
    Api.wellTyped (.provideLayer (.orDie projected) true (.service dbKey)) = false := by
  decide +kernel

/-- If checked as a native orDie layer, G descends to this leaf at [0]; its
service lookup fails there before orDie can change the successful signature. -/
theorem new_native_orDie_inner_leaf_refused :
    revisedEffectLeaf (nativeSignature []) [0] dbKey (.fail (.lit (.nat 7))) =
      .error ⟨[0], .serviceUnknown dbKey⟩ := by
  decide +kernel

#print axioms exact_source_projection
#print axioms docs_layer_accepted
#print axioms old_native_layer_accepted
#print axioms native_key_unknown
#print axioms complete_program_already_refused
#print axioms new_native_leaf_refused
#print axioms exact_runtime_use
#print axioms exact_source_runtime_use
#print axioms revised_docs_leaf_still_accepted
#print axioms exact_orDie_source_projection
#print axioms old_native_orDie_layer_accepted
#print axioms complete_orDie_program_already_refused
#print axioms new_native_orDie_inner_leaf_refused
end Research.Slice6.G.ProjectedLayerBoundary
