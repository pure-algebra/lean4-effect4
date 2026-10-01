import Effect4.Program.Table
import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Program.Typed
import Effect4.Program.Fragment
import Effect4.Program.Fold

/-!
# Program.Admission — static verification and admission certificates

A program is admitted to run when:
1. It contains no occurrences of the reserved integer type (`.int`).
2. It is well-typed against the supplied row table (`Program.typeOf program table = some ty`).
3. The table meets the three program-plane lawfulness conditions (`Table.lawful table = true`).
4. Every row can be registered by the runner (`checkTable table = none`).
5. Host answer and error types contain no internal handle kind (row 97 interim).

All five requirements are verified by `admitProgram`, producing a certified `AdmittedProgram`
whose fields witness each check. If admission fails, an exact `AdmitRefusal` reports the failure.
Admission depends strictly on the program plane and never imports codegen.

`admitStraightProgram` adds membership in the existing straight fragment to that
same admission result. It does not re-run a second typing judgment or claim an
application behavior; execution and safety results remain in the Laws graph.
-/

namespace Effect4.Program

/-- A boundary field path, with decimal positions for table rows. -/
abbrev Path := List String

/-- First occurrence of the reserved integer constructor in a raw type. -/
def findInt (pos : Path) : Ty → Option Path
  | .int => some pos
  | .option t | .list t => findInt (pos ++ ["inner"]) t
  | .causeOf e => findInt (pos ++ ["error"]) e
  | .prod a b | .union a b =>
      findInt (pos ++ ["left"]) a <|> findInt (pos ++ ["right"]) b
  | .except e a => findInt (pos ++ ["error"]) e <|> findInt (pos ++ ["value"]) a
  | .exitOf a e | .fiberOf a e | .deferredOf a e =>
      findInt (pos ++ ["value"]) a <|> findInt (pos ++ ["error"]) e
  | .refOf a => findInt (pos ++ ["value"]) a
  | .never | .unknown | .unit | .nat | .string | .bool | .handle _ | .lit _ | .var _ => none

/-- Inhabitance as a fold (decisions row 127; DI-67): `never`, `int` and a template parameter
have no member; a product needs both columns, a result or a union either; every other former
has a member at every argument in some world (`none`, `[]`, a failure with no typed reason, the
empty cause, a declared handle). The laws are `Laws/Program/Typed/Membership.lean`'s
`inhabited_of_fits` (sound), `fits_of_inhabited_handleFree` (complete on the data fragment) and
the handle witnesses. -/
def inhabitedAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := false
  ty_string := true
  ty_bool := true
  ty_handle _ := true
  ty_option _ := true
  ty_list _ := true
  ty_prod a b := a && b
  ty_except e a := e || a
  ty_exitOf _ _ := true
  ty_causeOf _ := true
  ty_fiberOf _ _ := true
  ty_union l r := l || r
  ty_lit _ := true
  ty_refOf _ := true
  ty_deferredOf _ _ := true
  ty_var _ := false
  ty_unknown := true

/-- Whether a type has a member (`inhabitedAlg`). -/
def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t

/-- A column admission accepts (row 127): the designed bottom, canonical `never`, or a type with
a member. `prod never nat` and `except never never` are canonical, not `never`, and empty, so
they are refused; `list int` has a member and is the `int` scan's to refuse (DB-15), not this
check's. -/
def admitColumn (t : Ty) : Bool := t.normalize == .never || inhabited t

/-- Scan every supplied row before normalization can discard any syntax. -/
def findIntInTable (table : RowTable) : Option Path := go 0 table
where
  go (index : Nat) : RowTable → Option Path
    | [] => none
    | row :: rest =>
        let pos := ["table", toString index]
        findInt (pos ++ ["request"]) row.request <|>
          findInt (pos ++ ["answer"]) row.answer <|>
          findInt (pos ++ ["error"]) row.error <|> go (index + 1) rest

/-- Locate internal handle types with the generated type fold. Raw syntax is inspected
before normalization, including every nested answer and error column. -/
def internalHandleScan : TyAlgebra (fun _ => Path → Option Path) where
  ty_never := fun _ => none
  ty_unit := fun _ => none
  ty_nat := fun _ => none
  ty_int := fun _ => none
  ty_string := fun _ => none
  ty_bool := fun _ => none
  ty_handle target := fun pos => if internalHandleTargets.contains target then some pos else none
  ty_option inner := fun pos => inner (pos ++ ["inner"])
  ty_list inner := fun pos => inner (pos ++ ["inner"])
  ty_prod left right := fun pos => left (pos ++ ["left"]) <|> right (pos ++ ["right"])
  ty_except error value := fun pos => error (pos ++ ["error"]) <|> value (pos ++ ["value"])
  ty_exitOf value error := fun pos => value (pos ++ ["value"]) <|> error (pos ++ ["error"])
  ty_causeOf error := fun pos => error (pos ++ ["error"])
  ty_fiberOf _ _ := some
  ty_union left right := fun pos => left (pos ++ ["left"]) <|> right (pos ++ ["right"])
  ty_lit _ := fun _ => none
  ty_refOf _ := some
  ty_deferredOf _ _ := some
  ty_var _ := fun _ => none
  ty_unknown := fun _ => none

def findInternalHandle (pos : Path) (ty : Ty) : Option Path :=
  cata_ty internalHandleScan ty pos

/-- Requests may pass internal handles outward. Host answer and error columns cannot
introduce them until their declaration registry is available (row 97 interim). -/
def findInternalHandleInTable (table : RowTable) : Option Path := go 0 table
where
  go (index : Nat) : RowTable → Option Path
    | [] => none
    | row :: rest =>
        let pos := ["table", toString index]
        findInternalHandle (pos ++ ["answer"]) row.answer <|>
          findInternalHandle (pos ++ ["error"]) row.error <|> go (index + 1) rest

/-- The inferred answer and error are the program's explicit type columns. -/
def findIntInEffTy (ty : EffTy) : Option Path :=
  findInt ["program", "answer"] ty.answer <|> findInt ["program", "error"] ty.error

/-- A type stated inside the program tree is the third place the reserved constructor can
hide (DI-92): an `iterate`'s cursor annotation. The columns of the certificate do not see it,
since a cursor's type need not reach the answer or the error. The path is the node's, then
`cursorTy`. -/
def findIntInProgram (program : NativeEff) : Option Path :=
  foldMapAt_eff (M := Option Path) none (· <|> ·) [] program
    (f_eff := fun e p => match e with
      | .iterate (some t) _ _ _ _ _ =>
        findInt ("program" :: p.map toString ++ ["cursorTy"]) t
      | _ => none)

/-! ## The table's lawful check and its located refusal agree (TY-05)

`Table.lawful` (a Boolean) and `Table.checkLawful` (the located refusal) are two definitions of
one condition (`Program/Table.lean`). `Table.checkLawful_eq_none_iff` ties them, so admission takes
its refusal from `checkLawful` alone and the certificate's `lawful` field from the theorem: no key
is invented for a failure the located check does not explain (the former fallback,
`duplicateKey ("", [])`, was unreachable, and is gone). -/

/-- `findDup` finds a repeated key exactly when the keys repeat. -/
theorem Table.findDup_eq_none_iff :
    ∀ keys : List (String × List String), Table.checkLawful.findDup keys = none ↔ keys.Nodup
  | [] => ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | k :: rest => by
    unfold Table.checkLawful.findDup
    rw [List.nodup_cons]
    by_cases hk : rest.contains k = true
    · rw [if_pos hk]
      exact ⟨fun h => (nomatch h), fun h => absurd (List.contains_iff_mem.mp hk) h.1⟩
    · rw [if_neg hk, Table.findDup_eq_none_iff rest]
      exact ⟨fun h => ⟨fun hm => hk (List.contains_iff_mem.mpr hm), h⟩, fun h => h.2⟩

/-- The three conditions `Table.lawful` decides, as a proposition. -/
theorem Table.lawful_eq_true_iff (table : RowTable) :
    Table.lawful table = true ↔
      (table.map rowKey).Nodup ∧
      (∀ row ∈ table,
        (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey row) = false) ∧
      (∀ row ∈ table, (!decide (row.shape = .value) || row.trailing.isEmpty) = true) := by
  unfold Table.lawful
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨hnd, hcol⟩, htr⟩
    refine ⟨hnd, fun row hr => ?_, htr⟩
    have h := hcol row hr
    cases hc : (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey row)
    · rfl
    · simp only [hc, Bool.not_true, Bool.false_eq_true] at h
  · rintro ⟨hnd, hcol, htr⟩
    refine ⟨⟨hnd, fun row hr => ?_⟩, htr⟩
    simp only [hcol row hr, Bool.not_false]

/-- **The located refusal is complete** (TY-05, proved): `checkLawful` refuses exactly the tables
`lawful` refuses. -/
theorem Table.checkLawful_eq_none_iff (table : RowTable) :
    Table.checkLawful table = none ↔ Table.lawful table = true := by
  rw [Table.lawful_eq_true_iff, ← Table.findDup_eq_none_iff]
  simp only [Table.checkLawful]
  cases h1 : Table.checkLawful.findDup (table.map rowKey) with
  | some k => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | none =>
    cases h2 : table.find? (fun r =>
        (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey r)) with
    | some row =>
      refine ⟨fun h => (nomatch h), fun h => ?_⟩
      have hmem := List.mem_of_find?_eq_some h2
      have hp := List.find?_some h2
      rw [h.2.1 row hmem] at hp
      cases hp
    | none =>
      cases h3 : table.find? (fun r => decide (r.shape = .value) && !r.trailing.isEmpty) with
      | some row =>
        refine ⟨fun h => (nomatch h), fun h => ?_⟩
        have hmem := List.mem_of_find?_eq_some h3
        have hp := List.find?_some h3
        have ht := h.2.2 row hmem
        cases hs : decide (row.shape = .value) <;> cases he : row.trailing.isEmpty <;>
          simp only [hs, he, Bool.not_false, Bool.not_true, Bool.or_false,
            Bool.and_false, Bool.and_true, Bool.false_eq_true] at hp ht
      | none =>
        refine ⟨fun _ => ⟨rfl, fun row hr => ?_, fun row hr => ?_⟩, fun _ => rfl⟩
        · have := List.find?_eq_none.mp h2 row hr
          cases hc : (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey row)
          · rfl
          · exact absurd hc this
        · have := List.find?_eq_none.mp h3 row hr
          cases hs : decide (row.shape = .value) <;> cases he : row.trailing.isEmpty <;>
            simp only [hs, he, Bool.not_false, Bool.not_true, Bool.or_false, Bool.or_true,
              Bool.and_false, Bool.and_true, not_true_eq_false] at this ⊢

/-- TY-05's statement: a table `lawful` refuses, `checkLawful` locates. -/
theorem Table.checkLawful_of_not_lawful (table : RowTable) (h : Table.lawful table = false) :
    Table.checkLawful table ≠ none := by
  intro hnone
  rw [(Table.checkLawful_eq_none_iff table).mp hnone] at h
  cases h

/-- Admission refusals, reporting the exact failure reason. -/
inductive AdmitRefusal
  /-- `Program.typeOf` answered `none` against this table. -/
  | illTyped
  /-- Duplicate row keys in the supplied table. -/
  | duplicateKey (key : String × List String)
  /-- The supplied row collides with a built-in native operation. -/
  | builtinCollision (key : String × List String)
  /-- A value row has trailing names. -/
  | valueRowTrailing (key : String × List String)
  /-- This runner cannot register a supplied row, with its position. -/
  | table (why : TableRefusal)
  /-- A raw table, the program tree or the inferred program type mentions the reserved
  integer constructor. -/
  | uninhabited («at» : Path)
  /-- A host answer or error type mentions a reserved internal handle kind. -/
  | internalHandle («at» : Path)
deriving DecidableEq, Repr

/-- A program admitted to run against a table: its type, the execution checks, and
the successful integer and internal-handle scans. The fields are proofs, so an `AdmittedProgram` cannot be forged by
building the structure with the wrong table — the table and the program are its indices. -/
structure AdmittedProgram (program : NativeEff) (table : RowTable)
    extends TypedProgram (nativeSignature table) program where
  lawful : Table.lawful table = true
  runnable : checkTable table = none
  intFreeTable : findIntInTable table = none
  internalFreeTable : findInternalHandleInTable table = none
  intFreeProgram : findIntInProgram program = none
  intFreeType : findIntInEffTy ty = none

/-- Decide admission by scanning raw table types, taking the one typing certificate
(`checkTypedProgram`, shared with code generation), scanning its columns, then checking
names and registrations. Each certificate field records the exact check that admitted it. -/
def admitProgram (program : NativeEff) (table : RowTable := []) :
    Except AdmitRefusal (AdmittedProgram program table) :=
  match htable : findIntInTable table with
  | some pos => .error (.uninhabited pos)
  | none =>
    match hinternal : findInternalHandleInTable table with
    | some pos => .error (.internalHandle pos)
    | none =>
    match hprogram : findIntInProgram program with
    | some pos => .error (.uninhabited pos)
    | none =>
    match checkTypedProgram (nativeSignature table) program with
    | none => .error .illTyped
    | some typing =>
      match htype : findIntInEffTy typing.ty with
      | some pos => .error (.uninhabited pos)
      | none =>
        match hlawful : Table.checkLawful table with
        | some (.duplicateKey k) => .error (.duplicateKey k)
        | some (.builtinCollision k) => .error (.builtinCollision k)
        | some (.valueRowTrailing k) => .error (.valueRowTrailing k)
        | none =>
          match hrunnable : checkTable table with
          | some why => .error (.table why)
          | none => .ok ⟨typing, (Table.checkLawful_eq_none_iff table).mp hlawful, hrunnable, htable,
              hinternal, hprogram, htype⟩

/-- Failure of ordinary admission, or a program outside the proved straight fragment.
Outside-fragment refusal does not mean that the program is ill-typed. -/
inductive StraightAdmitRefusal
  | admission (why : AdmitRefusal)
  | outsideFragment
deriving DecidableEq, Repr

/-- Ordinary admission plus executable membership in the straight fragment. The
existing runtime certificate remains available to the admitted run entry points.
No denotation, safety theorem or user specification is stored in this package. -/
structure AdmittedStraightProgram (program : NativeEff) (table : RowTable) where
  admitted : AdmittedProgram program table
  straight : Denote.Straight program = true

/-- Compute ordinary admission first, preserving its refusal, then check membership
in the existing straight fragment. The successful package records those two checks. -/
def admitStraightProgram (program : NativeEff) (table : RowTable := []) :
    Except StraightAdmitRefusal (AdmittedStraightProgram program table) :=
  match admitProgram program table with
  | .error why => .error (.admission why)
  | .ok admitted =>
    if h : Denote.Straight program = true then .ok ⟨admitted, h⟩
    else .error .outsideFragment

/-- Fragment admission retains every ordinary admission refusal. -/
theorem admitStraightProgram_admission_error (program : NativeEff) (table : RowTable)
    (why : AdmitRefusal) (h : admitProgram program table = .error why) :
    admitStraightProgram program table = .error (.admission why) := by
  simp [admitStraightProgram, h]

/-- An admitted member carries the same admission certificate and its membership proof. -/
theorem admitStraightProgram_ok (program : NativeEff) (table : RowTable)
    (admitted : AdmittedProgram program table)
    (hAdmit : admitProgram program table = .ok admitted)
    (hStraight : Denote.Straight program = true) :
    admitStraightProgram program table = .ok ⟨admitted, hStraight⟩ := by
  simp [admitStraightProgram, hAdmit, hStraight]

/-- A well-admitted program outside the fragment receives the distinct domain refusal. -/
theorem admitStraightProgram_outside (program : NativeEff) (table : RowTable)
    (admitted : AdmittedProgram program table)
    (hAdmit : admitProgram program table = .ok admitted)
    (hStraight : Denote.Straight program = false) :
    admitStraightProgram program table = .error .outsideFragment := by
  simp [admitStraightProgram, hAdmit, hStraight]

/-- Integer syntax in any supplied table row is refused with its exact path. -/
theorem admitProgram_table_int (program : NativeEff) (table : RowTable) (pos : Path)
    (h : findIntInTable table = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    have same : found = pos := Option.some.inj (hfound.symm.trans h)
    cases same
    rfl
  · rename_i hnone
    rw [h] at hnone
    contradiction

/-- A reserved host handle type is refused immediately after the integer table scan. -/
theorem admitProgram_table_internal (program : NativeEff) (table : RowTable) (pos : Path)
    (hTable : findIntInTable table = none) (h : findInternalHandleInTable table = some pos) :
    admitProgram program table = .error (.internalHandle pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i found hfound
      have same : found = pos := Option.some.inj (hfound.symm.trans h)
      cases same
      rfl
    · rename_i hnone
      rw [h] at hnone
      contradiction

/-- Integer syntax stated inside the program tree is refused after both table scans. -/
theorem admitProgram_program_int (program : NativeEff) (table : RowTable) (pos : Path)
    (hTable : findIntInTable table = none) (hInternal : findInternalHandleInTable table = none)
    (h : findIntInProgram program = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i found hfound
      rw [hInternal] at hfound
      contradiction
    · split
      · rename_i found hfound
        have same : found = pos := Option.some.inj (hfound.symm.trans h)
        cases same
        rfl
      · rename_i hnone
        rw [h] at hnone
        contradiction

/-- An inferred integer occurrence is refused after the table and tree scans succeed. -/
theorem admitProgram_type_int (program : NativeEff) (table : RowTable) (ty : EffTy) (pos : Path)
    (hTable : findIntInTable table = none) (hInternal : findInternalHandleInTable table = none)
    (hProgram : findIntInProgram program = none)
    (hTy : typeOfProgram (nativeSignature table) program = some ty)
    (hInt : findIntInEffTy ty = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i found hfound
      rw [hInternal] at hfound
      contradiction
    · split
      · rename_i found hfound
        rw [hProgram] at hfound
        contradiction
      · have hChecked : checkTypedProgram (nativeSignature table) program = some ⟨ty, hTy⟩ := by
          unfold checkTypedProgram
          split
          · rename_i hnone
            rw [hTy] at hnone
            contradiction
          · rename_i inferred hinferred
            have same : inferred = ty := Option.some.inj (hinferred.symm.trans hTy)
            cases same
            rfl
        rw [hChecked]
        dsimp only
        split
        · rename_i found hfound
          have same : found = pos := Option.some.inj (hfound.symm.trans hInt)
          cases same
          rfl
        · rename_i hnone
          rw [hInt] at hnone
          contradiction

end Effect4.Program
