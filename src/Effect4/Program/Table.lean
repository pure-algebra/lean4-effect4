import Effect4.Program.Native

/-!
# Program.Table — the row table invariants and keys

`Table.lawful` is the three program-plane requirements on a supplied `RowTable`:
1. Unique keys (`(table.map rowKey).Nodup`).
2. No collision with built-in native operations (`NativeOp.all`).
3. Value rows (`shape = .value`) have no trailing names (`row.trailing = []`).

Name safety (avoiding binder collision with `a0`, `a1`, ... and reserved expression heads)
is a printer and reader concern (`Codegen/Print.lean`, `Codegen/Read.lean`), kept strictly
out of the program plane so that admission never imports codegen.
-/

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

theorem builtinLookup_none (key : String × List String)
    (h : key ∉ NativeOp.all.map (rowKey ∘ NativeOp.row)) :
    NativeOp.all.find? (fun op => decide (rowKey op.row = key)) = none := by
  apply List.find?_eq_none.mpr
  intro op hop heq
  apply h
  exact List.mem_map.mpr ⟨op, hop, of_decide_eq_true heq⟩

namespace Table

/-- The three program-plane table requirements:
1. Unique keys (`table.map rowKey`).
2. No collision with `NativeOp.all` (`(nativeRowOf [] op).key`).
3. Value rows (`shape = .value`) have empty trailing names (`row.trailing.isEmpty`). -/
def lawful (table : RowTable) : Bool :=
  decide (table.map rowKey).Nodup &&
    table.all (fun row => !(NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey row)) &&
    table.all (fun row => !decide (row.shape = .value) || row.trailing.isEmpty)

/-- Why a table is not lawful on the program plane. -/
inductive LawfulRefusal
  | duplicateKey (key : String × List String)
  | builtinCollision (key : String × List String)
  | valueRowTrailing (key : String × List String)
deriving DecidableEq, Repr

/-- Decide why a table is unlawful, or `none` if lawful. -/
def checkLawful (table : RowTable) : Option LawfulRefusal :=
  let keys := table.map rowKey
  if let some dupKey := findDup keys then
    some (.duplicateKey dupKey)
  else if let some row := table.find? (fun r => (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey r)) then
    some (.builtinCollision (rowKey row))
  else if let some row := table.find? (fun r => r.shape = .value && !r.trailing.isEmpty) then
    some (.valueRowTrailing (rowKey row))
  else
    none
where
  findDup : List (String × List String) → Option (String × List String)
    | [] => none
    | k :: rest => if rest.contains k then some k else findDup rest

end Table

end Effect4.Program
