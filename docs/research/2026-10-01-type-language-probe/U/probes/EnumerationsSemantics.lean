import ProbeU.Enum
import Conform.Effect4.LcnfSemantics

/-! Probe U, question 1: the constructors the rung-2 vectors reach (tested), against the
generic unfold. -/

open ProbeU

#guard missing Conform.Effect4.LcnfSemantics.vectors ==
  [.lit, .refOf, .deferredOf, .var, .unknown]
#guard Conform.Effect4.LcnfSemantics.vectors.length == 1330
#guard (coverage Conform.Effect4.LcnfSemantics.vectors).length == 15
#guard missing (enumTy 3 1) == []

open Effect4.Program in
#guard Conform.Effect4.LcnfSemantics.leaves ==
  [.never, .unit, .nat, .int, .string, .bool, .handle "Ref.Ref<number>", .handle Ty.scopeTarget]
