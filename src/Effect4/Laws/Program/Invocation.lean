import Effect4.Program.Compile

/-!
# Invocation — one invocation form, routed by the row's kind (DI-61)

`perform` is the one invocation form. An external index or an asynchronous built-in compiles
to the shared dispatcher `asyncRoute`, at every point and positive fuel
(`compileEff_perform_eq_asyncRoute`); a synchronous row takes the synchronous route.
`compile_zero_fuel` retains the live-frontier boundary.

Until the `Eff` series retired it, a second spelling `callback` compiled to the same dispatcher,
and DI-61's theorem `compile_perform_eq_callback` was the equality of the two on exactly this
domain. It justified the retirement (checked at `478ed4b7`) and left with the constructor;
what remains is the statement of the route itself.

`checkTable_none_externalRow` connects the table check to the registration lookup. Neither
code equality nor table registration alone establishes host conformance, completion, or
resource liveness. The independent matrix and the timed and external executions live in
`Test/Program/InvocationContract.lean`; the external replay equality there is a bounded
fixture, not the table-aware reference theorem reserved by DI-57.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The shared dispatcher -/

/-- Fuel zero is the live frontier, before any operation is looked at (`Compile.lean`,
`compileEff`'s first match). -/
theorem compile_zero_fuel (e : NativeEff) (p : Point) (h : p.fuel = 0) :
    compileEff e p = frontier p := by
  unfold compileEff
  rw [h]

/-- DI-61. An external call or an asynchronous built-in compiles to the shared dispatcher, at
every point and positive fuel. The external case is independent of any supplied table:
registration reads that table when the code executes. -/
theorem compileEff_perform_eq_asyncRoute (op : NativeOp) (r : Term) (p : Point) {k : Nat}
    (hf : p.fuel = k + 1) (h : (∃ i, op = .external i) ∨ op.row.kind = .async) :
    compileEff (.perform op r) p = asyncRoute op r p := by
  unfold compileEff
  rw [hf]
  cases op with
  | external i => rfl
  | sleep => rfl
  | deferredAwait => rfl
  | scopeMake strategy => cases strategy <;> simp [NativeOp.row] at h
  | _ => simp [NativeOp.row] at h

/-! ## The table check and the registration lookup -/

/-- An accepted table registers the normalized linked view of every row it holds. The raw
metadata remains unchanged in the table (DI-53). The converse direction (a rejected table
has a position `externalRow` refuses) is `checkTable`'s own `index`. -/
theorem checkTable_none_externalRow {table : RowTable} (h : checkTable table = none)
    (i : Nat) (row : Row) (hi : table[i]? = some row) :
    externalRow table i = some row.normalizeTypes := by
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
