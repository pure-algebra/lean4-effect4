module

public import Effect4.Program.Native

/-!
# Program.Table — the row table invariants and keys

`Table.lawful` is the three program-plane requirements on a supplied `RowTable`:
1. Unique keys (`(table.map rowKey).Nodup`).
2. No collision with a built-in spelling key (`builtinKeys`): checked by key, since no list holds
   every built-in operation (`Deferred.make` carries its type arguments).
3. Value rows (`shape = .value`) have no trailing names (`row.trailing = []`).

Name safety (avoiding binder collision with `a0`, `a1`, ... and reserved expression heads)
is a printer and reader concern (`Codegen/Print.lean`, `Codegen/Read.lean`), kept strictly
out of the program plane so that admission never imports codegen.
-/

@[expose] public section

namespace Effect4.Program

/-- The key identifying an operation in a table: its spelling and its trailing argument names. -/
def rowKey (row : Row) : String × List String := (row.spelling, row.trailing)

def Row.key (row : Row) : String × List String := rowKey row

/-- Uniqueness makes the first matching row exactly the supplied position. -/
theorem rowIndex_roundTrip (table : List Row) (hn : (table.map rowKey).Nodup)
    (i : Nat) (hi : i < table.length) :
    table.findIdx? (fun row => decide (rowKey row = rowKey table[i])) = some i := by
  induction table generalizing i with
  | nil => cases hi
  | cons row rest ih =>
    have hnodup := List.nodup_cons.mp hn
    cases i with
    | zero => simp [List.findIdx?_cons]
    | succ i =>
      have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
      have hne : rowKey row ≠ rowKey rest[i] := by
        intro he
        exact hnodup.1 (List.mem_map.mpr ⟨rest[i], List.getElem_mem hi', he.symm⟩)
      simp [List.findIdx?_cons, hne, ih hnodup.2 i hi']

/-- A successful lookup names an existing row with exactly the supplied key. -/
theorem rowIndex_exact (table : List Row) (key : String × List String) (i : Nat)
    (h : table.findIdx? (fun row => decide (rowKey row = key)) = some i) :
    ∃ hi : i < table.length, rowKey table[i] = key := by
  induction table generalizing i with
  | nil => simp at h
  | cons row rest ih =>
    rw [List.findIdx?_cons] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨Nat.zero_lt_succ _, of_decide_eq_true hk⟩
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hlt, hk⟩ := ih j hj
      exact ⟨Nat.succ_lt_succ hlt, hk⟩

/-- The built-in spelling keys: one per representative of `NativeOp.spelled`. -/
def builtinKeys : List (String × List String) := NativeOp.spelled.map (rowKey ∘ NativeOp.row)

/-- **Every built-in operation has a built-in key**: a row's spelling and trailing names depend
neither on the type arguments its operation carries nor on its binder term, which the faces print
as a function after the request. So `NativeOp.spelled`'s keys cover every operation but an
external one. -/
theorem NativeOp.rowKey_mem (op : NativeOp) (h : ∀ i, op ≠ .external i) :
    rowKey op.row ∈ builtinKeys := by
  cases op with
  | external i => exact absurd rfl (h i)
  | deferredMakeOf _ _ => exact (by decide : ("Deferred.make", ([] : List String)) ∈ builtinKeys)
  | scopeMake s => cases s <;> decide
  | refUpdateWith _ => exact (by decide : ("Ref.update", ([] : List String)) ∈ builtinKeys)
  | refGetAndUpdateWith _ =>
    exact (by decide : ("Ref.getAndUpdate", ([] : List String)) ∈ builtinKeys)
  | refUpdateAndGetWith _ =>
    exact (by decide : ("Ref.updateAndGet", ([] : List String)) ∈ builtinKeys)
  | refUpdateSomeWith _ => exact (by decide : ("Ref.updateSome", ([] : List String)) ∈ builtinKeys)
  | refGetAndUpdateSomeWith _ =>
    exact (by decide : ("Ref.getAndUpdateSome", ([] : List String)) ∈ builtinKeys)
  | refUpdateSomeAndGetWith _ =>
    exact (by decide : ("Ref.updateSomeAndGet", ([] : List String)) ∈ builtinKeys)
  | refModifyWith _ => exact (by decide : ("Ref.modify", ([] : List String)) ∈ builtinKeys)
  | refModifySomeWith _ =>
    exact (by decide : ("Ref.modifySome", ([] : List String)) ∈ builtinKeys)
  | _ => decide

theorem builtinLookup_none (key : String × List String) (h : key ∉ builtinKeys) :
    NativeOp.spelled.find? (fun op => decide (rowKey op.row = key)) = none := by
  apply List.find?_eq_none.mpr
  intro op hop heq
  apply h
  exact List.mem_map.mpr ⟨op, hop, of_decide_eq_true heq⟩

namespace Table

/-- The three program-plane table requirements:
1. Unique keys (`table.map rowKey`).
2. No collision with a built-in spelling key (`builtinKeys`).
3. Value rows (`shape = .value`) have empty trailing names (`row.trailing.isEmpty`). -/
def lawful (table : RowTable) : Bool :=
  decide (table.map rowKey).Nodup &&
    table.all (fun row => !builtinKeys.contains (rowKey row)) &&
    table.all (fun row => !decide (row.shape = .value) || row.trailing.isEmpty)

end Table

end Effect4.Program
