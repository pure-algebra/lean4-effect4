import Effect4.Laws.Program.TypeAlgebra
import Effect4.Program.Compile

/-! The signature and external protocol share one normalized view of a raw table row.
These theorems concern Lean row lookup and value membership, not a host execution claim. -/
namespace Effect4.Program

theorem normalizeTypes_request (row : Row) (v : Store.Val) (allocated : List String) :
    Val.hasTy v row.normalizeTypes.request allocated = Val.hasTy v row.request allocated :=
  hasTy_normalize row.request v allocated

theorem normalizeTypes_answer (row : Row) (v : Store.Val) (allocated : List String) :
    Val.hasTy v row.normalizeTypes.answer allocated = Val.hasTy v row.answer allocated :=
  hasTy_normalize row.answer v allocated

theorem normalizeTypes_error (row : Row) (v : Store.Val) (allocated : List String) :
    Val.hasTy v row.normalizeTypes.error allocated = Val.hasTy v row.error allocated :=
  hasTy_normalize row.error v allocated

theorem externalRow_raw {table : RowTable} {i : Nat} {linked : Row}
    (h : externalRow table i = some linked) :
    ∃ raw, table[i]? = some raw ∧ raw.registration = .external ∧ raw.kind = .async ∧
      linked = raw.normalizeTypes := by
  obtain ⟨raw, hraw, hrest⟩ := Option.bind_eq_some_iff.mp h
  by_cases hs : raw.registration = .external ∧ raw.kind = .async
  · have heq : raw.normalizeTypes = linked := by simpa [guard, hs] using hrest
    exact ⟨raw, hraw, hs.1, hs.2, heq.symm⟩
  · simp [guard, hs] at hrest
    exact nomatch hrest

theorem externalRow_signature {table : RowTable} {i : Nat} {linked : Row}
    (h : externalRow table i = some linked) :
    (nativeSignature table).rowOf (.external i) = linked := by
  obtain ⟨raw, hraw, _, _, rfl⟩ := externalRow_raw h
  simp [nativeSignature, nativeRowOf, hraw]

theorem externalRow_normalized {table : RowTable} {i : Nat} {linked : Row}
    (h : externalRow table i = some linked) : linked.normalizeTypes = linked := by
  obtain ⟨raw, _, _, _, rfl⟩ := externalRow_raw h
  exact Row.normalizeTypes_idem raw

end Effect4.Program
