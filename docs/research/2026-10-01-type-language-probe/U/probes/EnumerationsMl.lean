import ProbeU.Enum
import Conform.Effect4.LcnfMl

/-! Probe U, question 1: the constructors the rung-3 vectors reach (tested); the rung-2 copy of
the same enumeration is `EnumerationsSemantics.lean`. -/

open ProbeU

#guard missing Conform.Effect4.LcnfMl.vectors == [.lit, .refOf, .deferredOf, .var, .unknown]
open Effect4.Program in
#guard Conform.Effect4.LcnfMl.leaves ==
  [.never, .unit, .nat, .int, .string, .bool, .handle "Ref.Ref<number>", .handle Ty.scopeTarget]
