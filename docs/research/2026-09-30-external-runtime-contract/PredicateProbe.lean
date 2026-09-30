import Effect4.Laws.Program.Typed.Admission

set_option autoImplicit false

namespace Test.ExternalRuntimePredicate
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

-- These are precise facts about the present predicate, not reachable-state claims.
-- No declaration of the named fiber is required for any of these HandlesFit proofs.
theorem product_skips_payload (w : Typed.World) :
    HandlesFit w (.list [Value.fiber 1, .unit])
      (.prod (.fiberOf .nat .never) .unit) := by
  exact True.intro

theorem result_skips_payload (w : Typed.World) :
    HandlesFit w (.ctor 1 [Value.fiber 1])
      (.except .never (.fiberOf .nat .never)) := by
  exact True.intro

theorem exit_skips_payload (w : Typed.World) :
    HandlesFit w (Value.exitOk (Value.fiber 1))
      (.exitOf (.fiberOf .nat .never) .never) := by
  exact True.intro

theorem union_uses_unrelated_arm (w : Typed.World) :
    HandlesFit w (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) := by
  exact Or.inr True.intro

theorem product_has_shape :
    Val.hasTy (.list [Value.fiber 1, .unit])
      (.prod (.fiberOf .nat .never) .unit) = true := by
  rfl

#print axioms product_skips_payload
#print axioms result_skips_payload
#print axioms exit_skips_payload
#print axioms union_uses_unrelated_arm
#print axioms product_has_shape

end Test.ExternalRuntimePredicate
