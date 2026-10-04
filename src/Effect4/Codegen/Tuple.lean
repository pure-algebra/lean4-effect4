import Effect4.Data.NatDecimal
import TypeScript.Syntax

/-! Exact structural tuple projection syntax.
Literal string markers retain every stored natural index, including indices above the target
number profile. Source reification into JavaScript numbers checks its narrower profile separately.
The reader's size fact serves `readTerm`; the remaining laws live in `Laws/Codegen/Tuple.lean`. -/

namespace Effect4.Codegen.Tuple
open TypeScript

/-- Tuple helper bindings remain separate from program heads and ordinary atom applications. -/
def helperNames : List String := ["tupleAt"]

/-- Retain a static index twice so the canonical helper call carries its literal target type. -/
def writeAt (index : Nat) (target : Expr) : Expr :=
  .call (.call (.generic (.ident "tupleAt") [.literal (Nat.repr index)]) [.str (Nat.repr index)]) [target]

/-- Both markers agree and spell a natural canonically; the child expression stays unchanged. -/
def readAt : Expr → Option (Nat × Expr)
  | .call (.call (.generic (.ident "tupleAt") [.literal marker]) [.str key]) [target] => do
    if key = marker then
      let index ← Data.NatDecimal.read key
      some (index, target)
    else none
  | _ => none

/-- Exact-codecs termination helper for `readTerm`, serving `collection-term-print-read`.
Successful structural reading alone makes the child smaller; this states no execution claim. -/
theorem readAt_size (e : Expr) (index : Nat) (target : Expr)
    (h : readAt e = some (index, target)) : sizeOf target < sizeOf e := by
  unfold readAt at h
  split at h
  · split at h
    · obtain ⟨index', hindex, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.Tuple
