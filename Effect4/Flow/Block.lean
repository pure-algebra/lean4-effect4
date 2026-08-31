import Std

/-!
# First-order flow blocks

This module owns the nominal identities, closed operation alphabet, and raw
block terms used by flow admission. Raw terms contain only stable identities;
they deliberately contain no Lean continuation or semantic `Program`.
-/

namespace Effect4

/-- Stable identity of a declared flow block. -/
structure BlockId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of an operation in a closed flow alphabet. -/
structure OperationId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of the closed alphabet expected by a raw flow. -/
structure AlphabetId where
  value : Nat
deriving DecidableEq, Repr

/-- Stable identity of an explicit nondeterministic decision site. -/
structure DecisionId where
  value : Nat
deriving DecidableEq, Repr

/--
A closed operation alphabet supplied at the admission boundary.

Raw flows retain only `id`. Executable lookup and its two inverse laws remain
in this trusted semantic environment, so no host function enters canonical
flow content.
-/
structure FlowAlphabet.{uTy, uOp} (Ty : Type uTy) where
  id : AlphabetId
  Op : Type uOp
  operationId : Op → OperationId
  lookup : OperationId → Option Op
  requestTy : Op → Ty
  answerTy : Op → Ty
  lookup_operationId : ∀ operation,
    lookup (operationId operation) = some operation
  operationId_of_lookup : ∀ {id operation},
    lookup id = some operation → operationId operation = id

/-- A first-order block terminator. Every continuation is a nominal block ID. -/
inductive RawTerm where
  | ret
  | jump (target : BlockId)
  | perform (operation : OperationId) (target : BlockId)
  | choose (decision : DecisionId) (left right : BlockId)
deriving DecidableEq, Repr

namespace RawTerm

/-- Direct graph successors named by a raw terminator, in source order. -/
def successors : RawTerm → List BlockId
  | .ret => []
  | .jump target => [target]
  | .perform _ target => [target]
  | .choose _ left right => [left, right]

end RawTerm

/-- A first-order ANF block with one typed input payload. -/
structure RawBlock (Ty : Type uTy) where
  id : BlockId
  inputTy : Ty
  term : RawTerm
deriving DecidableEq, Repr

end Effect4
