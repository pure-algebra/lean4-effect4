import Effect4.Program.Admission
import Aesop

/-!
# Laws.Program.Typed.AdmissionRows — the API's table checks, read row by row

`lawfulSig_of_admitted` (`Laws/Program/Typed/AdmittedSource.lean`) reads `rowChecks`
(`Laws/Program/Signature.lean`) off a table the API admits. Admission
(`src/Effect4/Program/Admission.lean`) runs three table checks that had no reading by row:

* `checkTable_eq_none_iff`: the runner registers a table exactly when every row is external and
  asynchronous.
* `findIntInTable_eq_none_iff`: no request, answer or error column mentions `int`.
* `findInternalHandleInTable_eq_none_iff`: no answer or error column names an internal handle.

Admission scans a column at its table position (`["table", i, "request"]`); `rowChecks` scans it at
the root `[]`. A scan's root only prefixes the path it reports, so its `none` does not depend on
the root (`findInt_eq_none_iff_root`, `findInternalHandle_eq_none_iff_root`). Both are proved once
over `Ty` with the generated eliminator `Ty.ind`. The arms list only the constructors whose
children sit in a list; one search closes every other constructor. The fold route
(`hom_eq_cata_ty`) would need a second algebra, the scan at the root, which repeats the scan.

Placement (`AGENTS.md`). Concept: `residual-program-typing`. Every theorem here is a step of the
claim `admitted-source-lawful`, and its consumer is `lawfulSig_of_admitted`. Reach: the raw
columns of any supplied row table. They do not establish the three conditions of `AdmissionGap`,
which admission does not check (`E4-TYPED-CE-041`).
-/

set_option autoImplicit false

namespace Effect4.Program

/-! ## A scan's `none` does not depend on its root -/

/-- A right fold of first answers answers `none` exactly when every element does. A step of
`admitted-source-lawful`; consumer: `findInternalHandle_eq_none_iff_root`, whose record and tuple
scans are such folds. -/
theorem foldr_orElse_eq_none_iff {α β : Type} (f : α → Option β) :
    ∀ l : List α, l.foldr (fun x acc => f x <|> acc) none = none ↔ ∀ x ∈ l, f x = none
  | [] => by aesop
  | x :: l => by
    have ih := foldr_orElse_eq_none_iff f l
    aesop (add norm simp [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_none_iff])

/-- **The internal-handle scan's `none` does not depend on its root** (proved). A step of
`admitted-source-lawful`: admission scans an answer or error column at its table position,
`rowChecks` at `[]`. Consumer: `findInternalHandleInTable_go_eq_none_iff`. -/
theorem findInternalHandle_eq_none_iff_root (pos : Path) (t : Ty) :
    findInternalHandle pos t = none ↔ findInternalHandle [] t = none := by
  induction t generalizing pos with
  | record fs ih =>
    simp only [findInternalHandle, cata_ty_record, internalHandleScan, foldr_orElse_eq_none_iff,
      List.forall_mem_map]
    exact forall₂_congr fun x hx => (ih x hx _).trans (ih x hx _).symm
  | tuple ts ih =>
    simp only [findInternalHandle, cata_ty_tuple, internalHandleScan, foldr_orElse_eq_none_iff]
    refine forall₂_congr fun x hx => ?_
    obtain ⟨t, ht, hx1⟩ := List.mem_map.mp (List.fst_mem_of_mem_zipIdx hx)
    rw [← hx1]
    exact (ih t ht _).trans (ih t ht _).symm
  | _ => aesop (add norm simp [findInternalHandle, internalHandleScan, Option.orElse_eq_orElse,
      Option.orElse_eq_or, Option.or_eq_none_iff])

/-- The integer scan of a record's fields answers `none` exactly when every field's scan does, at
the field's name. A step of `admitted-source-lawful`; consumer: `findInt_eq_none_iff_root`. -/
theorem findIntFields_eq_none_iff (pos : Path) : ∀ fs : List (String × Bool × Ty),
    findIntFields pos fs = none ↔ ∀ f ∈ fs, findInt (pos ++ [f.1]) f.2.2 = none
  | [] => by aesop (add norm simp [findIntFields])
  | f :: rest => by
    have ih := findIntFields_eq_none_iff pos rest
    aesop (add norm simp [findIntFields, Option.orElse_eq_orElse, Option.orElse_eq_or,
      Option.or_eq_none_iff])

/-- The integer scan of a tuple's or an application's items answers `none` exactly when every
item's scan does, at its decimal position. A step of `admitted-source-lawful`; consumer:
`findInt_eq_none_iff_root`. -/
theorem findIntItems_eq_none_iff (pos : Path) : ∀ (i : Nat) (ts : List Ty),
    findIntItems pos i ts = none ↔ ∀ x ∈ ts.zipIdx i, findInt (pos ++ [toString x.2]) x.1 = none
  | _, [] => by aesop (add norm simp [findIntItems])
  | i, t :: rest => by
    have ih := findIntItems_eq_none_iff pos (i + 1) rest
    aesop (add norm simp [findIntItems, Option.orElse_eq_orElse, Option.orElse_eq_or,
      Option.or_eq_none_iff])

/-- **The integer scan's `none` does not depend on its root** (proved). A step of
`admitted-source-lawful`: admission scans a column at its table position, `rowChecks` at `[]`.
Consumer: `findIntInTable_go_eq_none_iff`. -/
theorem findInt_eq_none_iff_root (pos : Path) (t : Ty) :
    findInt pos t = none ↔ findInt [] t = none := by
  induction t generalizing pos with
  | record fs ih =>
    simp only [findInt, findIntFields_eq_none_iff]
    exact forall₂_congr fun x hx => (ih x hx _).trans (ih x hx _).symm
  | tuple ts ih | app _ ts ih =>
    simp only [findInt, findIntItems_eq_none_iff]
    exact forall₂_congr fun x hx =>
      (ih x.1 (List.fst_mem_of_mem_zipIdx hx) _).trans
        (ih x.1 (List.fst_mem_of_mem_zipIdx hx) _).symm
  | _ => aesop (add norm simp [findInt, Option.orElse_eq_orElse, Option.orElse_eq_or,
      Option.or_eq_none_iff])

/-! ## The table checks, row by row -/

/-- The integer scan from a position finds nothing exactly when no row's column does, each read at
the root. A step of `admitted-source-lawful`; consumer: `findIntInTable_eq_none_iff`. -/
theorem findIntInTable_go_eq_none_iff :
    ∀ (rows : RowTable) (index : Nat), findIntInTable.go index rows = none ↔
      ∀ row ∈ rows, findInt [] row.request = none ∧ findInt [] row.answer = none ∧
        findInt [] row.error = none
  | [], _ => ⟨fun _ _ hr => (nomatch hr), fun _ => rfl⟩
  | row :: rest, index => by
    have ih := findIntInTable_go_eq_none_iff rest (index + 1)
    aesop (add norm simp [findIntInTable.go, Option.orElse_eq_orElse, Option.orElse_eq_or,
      Option.or_eq_none_iff, findInt_eq_none_iff_root])

/-- **The table's integer scan finds nothing exactly when no column mentions `int`** (proved), each
column read at the root as `rowChecks` reads it. A step of `admitted-source-lawful`; consumer:
`lawfulSig_of_admitted` (`AdmittedProgram.intFreeTable`). -/
theorem findIntInTable_eq_none_iff (table : RowTable) :
    findIntInTable table = none ↔
      ∀ row ∈ table, findInt [] row.request = none ∧ findInt [] row.answer = none ∧
        findInt [] row.error = none :=
  findIntInTable_go_eq_none_iff table 0

/-- The internal-handle scan from a position finds nothing exactly when no row's answer or error
does, each read at the root. A step of `admitted-source-lawful`; consumer:
`findInternalHandleInTable_eq_none_iff`. -/
theorem findInternalHandleInTable_go_eq_none_iff :
    ∀ (rows : RowTable) (index : Nat), findInternalHandleInTable.go index rows = none ↔
      ∀ row ∈ rows, findInternalHandle [] row.answer = none ∧
        findInternalHandle [] row.error = none
  | [], _ => ⟨fun _ _ hr => (nomatch hr), fun _ => rfl⟩
  | row :: rest, index => by
    have ih := findInternalHandleInTable_go_eq_none_iff rest (index + 1)
    aesop (add norm simp [findInternalHandleInTable.go, Option.orElse_eq_orElse,
      Option.orElse_eq_or, Option.or_eq_none_iff, findInternalHandle_eq_none_iff_root])

/-- **The table's internal-handle scan finds nothing exactly when no answer or error column names
an internal handle** (proved), each read at the root as `rowChecks` reads it. A step of
`admitted-source-lawful`; consumer: `lawfulSig_of_admitted` (`AdmittedProgram.internalFreeTable`). -/
theorem findInternalHandleInTable_eq_none_iff (table : RowTable) :
    findInternalHandleInTable table = none ↔
      ∀ row ∈ table, findInternalHandle [] row.answer = none ∧
        findInternalHandle [] row.error = none :=
  findInternalHandleInTable_go_eq_none_iff table 0

/-- **The runner registers a table exactly when every row is external and asynchronous**
(proved): `checkTable`'s two refusals, read by row. `checkTable_none_externalRow`
(`Laws/Program/Invocation.lean`) reads the same check at the registration lookup. A step of
`admitted-source-lawful`; consumer: `lawfulSig_of_admitted` (`AdmittedProgram.runnable`). -/
theorem checkTable_eq_none_iff (table : RowTable) :
    checkTable table = none ↔ ∀ row ∈ table, row.registration = .external ∧ row.kind = .async := by
  unfold checkTable
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro h row hrow
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrow
    have hcheck := h i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
    rw [hi] at hcheck
    aesop
  · intro h i _
    aesop (add norm simp [List.getElem?_eq_some_iff])

end Effect4.Program
