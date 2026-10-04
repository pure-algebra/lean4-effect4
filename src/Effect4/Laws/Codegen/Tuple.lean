import Effect4.Codegen.Tuple
import Effect4.Codegen.Record
import Effect4.Laws.Data.NatDecimal

/-! Exact tuple projection wrappers, serving `collection-term-print-read` and `printed-modules`.
Retraction covers all indices and child expressions. Exactness assumes successful reading.
Consumers: the tuple cases of `readTerm_printTerm` and `readTerm_exact`, requirements R2/R3.
These structural laws establish no target typing, source reification or execution theorem. -/

namespace Effect4.Codegen.Tuple
open TypeScript

theorem readAt_writeAt (index : Nat) (target : Expr) :
    readAt (writeAt index target) = some (index, target) := by
  simp only [writeAt, readAt, ↓reduceIte, Data.NatDecimal.read_repr,
    Option.bind_eq_bind, Option.bind_some]

theorem readAt_exact (e : Expr) (index : Nat) (target : Expr)
    (h : readAt e = some (index, target)) : writeAt index target = e := by
  unfold readAt at h
  split at h
  · next marker key target' =>
    split at h
    · next heq =>
      obtain ⟨index', hindex, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hs := Data.NatDecimal.read_exact hindex
      simp only [writeAt, hs, heq]
    · exact nomatch h
  · exact nomatch h

/-- Tuple projection is disjoint from each earlier record wrapper reader. -/
theorem readRecord_writeAt (index : Nat) (target : Expr) :
    Record.readRecord (writeAt index target) = none := rfl

theorem readField_writeAt (index : Nat) (target : Expr) :
    Record.readField (writeAt index target) = none := rfl

theorem readSet_writeAt (index : Nat) (target : Expr) :
    Record.readSet (writeAt index target) = none := rfl

end Effect4.Codegen.Tuple
