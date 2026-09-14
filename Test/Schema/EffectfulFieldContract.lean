/-
Contract packet: `Test/contracts/schema-effectful-field.contract.md`.

Breaker-owned red battery for `SCHEMA-PG-EFFECTFUL-FIELD`. The builder makes
this file green without editing it.
-/

import Effect4.Schema.EffectfulField

namespace Test.Schema.EffectfulFieldContract

open Effect4 Effects

universe uOp uAns v

variable {signature : Signature.{uOp, uAns}}
variable {S A : Type uAns}

/-! ## F0 — portable data reuses existing identities and annotation carrier -/

#synth DecidableEq EffectfulFieldSpec
#synth Repr EffectfulFieldSpec

example : EffectfulFieldSpec.annotationKey.name = "effect4/effectful-field" := by
  rfl

/-! ## F1 — admission sees exact raw same-name occurrences -/

example (annotations : Annotations) :
    EffectfulFieldSpec.rawOccurrences annotations =
      (Annotations.payloadsAt EffectfulFieldSpec.annotationKey.name).collect annotations := by
  rfl

/-! ## F2 — resolved bridge reuses Signature and Program -/

/-! ## F3 — generated programs have exact ordered equations -/

/-! ## F4 — interpretation preserves the generated order -/

end Test.Schema.EffectfulFieldContract
