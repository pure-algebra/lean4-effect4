import Effect4.Program.Compile

/-!
# Invocation — the two syntactic forms of one asynchronous call (DI-61)

`compile_perform_eq_callback` proves the production compiler emits identical code for
`perform` and `callback` on every external index or asynchronous built-in, at every point
and fuel. `compile_zero_fuel` retains the live-frontier boundary. The older await-only
statements remain available as corollaries.

`checkTable_none_externalRow` connects the table check to the registration lookup. Neither
code equality nor table registration alone establishes host conformance, completion, or
resource liveness. The independent 55 × 2 matrix and timed/external executions live in
`Test/Program/InvocationContract.lean`; the external replay equality there is a bounded
fixture, not the table-aware reference theorem reserved by DI-57.

The sync `perform` route remains distinct: `callback` on a sync row is still `badShape`.
The compiler's reference denotation and its head/key proofs change with this routing;
`run_eq_ref` retains its empty-table, no-oracle statement.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The shared dispatcher -/

/-- Fuel zero is the live frontier in both forms, before any operation is looked at
(`Compile.lean`, `compileEff`'s first match). -/
theorem compile_zero_fuel (e : NativeEff) (p : Point) (h : p.fuel = 0) :
    compileEff e p = frontier p := by
  unfold compileEff
  rw [h]

/-- The extraction is exact: at positive fuel `callback` compiles to the shared dispatcher,
for every operation and every request term. -/
theorem compileEff_callback_eq_asyncRoute (op : NativeOp) (r : Term) (p : Point) {k : Nat}
    (hf : p.fuel = k + 1) : compileEff (.callback op r) p = asyncRoute op r p := by
  unfold compileEff
  rw [hf]

/-- DI-61. External calls and asynchronous built-ins compile identically under the two
invocation spellings, for every point and fuel. The external case is independent of any
supplied table: registration reads that table when the code executes. -/
theorem compile_perform_eq_callback (op : NativeOp) (r : Term) (p : Point)
    (h : (∃ i, op = .external i) ∨ op.row.kind = .async) :
    compileEff (.perform op r) p = compileEff (.callback op r) p := by
  cases op with
  | scopeMake strategy => cases strategy <;> simp [NativeOp.row] at h
  | _ => first
    | (unfold compileEff; cases p.fuel <;> rfl)
    | (simp [NativeOp.row] at h)

/-- `Deferred.await` retains the historical wire spelling as a compatible invocation. -/
theorem compile_perform_eq_callback_await (r : Term) (p : Point) :
    compileEff (.perform .deferredAwait r) p = compileEff (.callback .deferredAwait r) p :=
  compile_perform_eq_callback .deferredAwait r p (.inr rfl)

/-- The original restricted statement, retained for callers; DI-61 removes its exclusions
in `compile_perform_eq_callback`. -/
theorem compile_perform_eq_callback_of_await (op : NativeOp) (r : Term) (p : Point)
    (hkind : (NativeOp.row op).kind = .async) (hne : ∀ i, op ≠ .external i) (hns : op ≠ .sleep) :
    compileEff (.perform op r) p = compileEff (.callback op r) p := by
  clear hne hns
  exact compile_perform_eq_callback op r p (.inr hkind)

/-! ## The table check and the registration lookup -/

/-- An accepted table registers every row it holds: what `checkTable` decides is exactly what
the registration hook consults through `externalRow`. The converse direction (a rejected table
has a position `externalRow` refuses) is `checkTable`'s own `index`. -/
theorem checkTable_none_externalRow {table : RowTable} (h : checkTable table = none)
    (i : Nat) (row : Row) (hi : table[i]? = some row) : externalRow table i = some row := by
  have hlt : i < table.length := by
    rcases Nat.lt_or_ge i table.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hi
      simp at hi
  have hnone :
      (match table[i]? with
        | some row =>
          if row.registration ≠ .external then some (TableRefusal.notExternal i)
          else if row.kind ≠ .async then some (TableRefusal.notAsync i)
          else none
        | none => none) = none := by
    have := List.findSome?_eq_none_iff.mp h i (List.mem_range.mpr hlt)
    exact this
  rw [hi] at hnone
  by_cases hreg : row.registration = .external
  · by_cases hkind : row.kind = .async
    · simp [externalRow, hi, hreg, hkind, guard]
    · simp [hreg, hkind] at hnone
  · simp [hreg] at hnone

end Effect4.Program
