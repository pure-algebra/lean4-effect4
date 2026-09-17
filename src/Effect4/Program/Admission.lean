import Effect4.Program.Table
import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Program.Fragment
import Effect4.Program.Fold

/-!
# Program.Admission — static verification and admission certificates

A program is admitted to run when:
1. It contains no occurrences of the reserved integer type (`.int`).
2. It is well-typed against the supplied row table (`Program.typeOf program table = some ty`).
3. The table meets the three program-plane lawfulness conditions (`Table.lawful table = true`).
4. Every row can be registered by the runner (`checkTable table = none`).

All four requirements are verified by `admitProgram`, producing a certified `AdmittedProgram`
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
  | .exitOf a e | .fiberOf a e =>
      findInt (pos ++ ["value"]) a <|> findInt (pos ++ ["error"]) e
  | .never | .unit | .nat | .string | .bool | .handle _ | .lit _ => none

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
deriving DecidableEq, Repr

/-- A program admitted to run against a table: its type, the execution checks, and
the successful integer scans. The fields are proofs, so an `AdmittedProgram` cannot be forged by
building the structure with the wrong table — the table and the program are its indices. -/
structure AdmittedProgram (program : NativeEff) (table : RowTable)
    extends TypedProgram (nativeSignature table) program where
  lawful : Table.lawful table = true
  runnable : checkTable table = none
  intFreeTable : findIntInTable table = none
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
    match hprogram : findIntInProgram program with
    | some pos => .error (.uninhabited pos)
    | none =>
    match checkTypedProgram (nativeSignature table) program with
    | none => .error .illTyped
    | some typing =>
      match htype : findIntInEffTy typing.ty with
      | some pos => .error (.uninhabited pos)
      | none =>
        if hlawful : Table.lawful table = true then
          match hrunnable : checkTable table with
          | some why => .error (.table why)
          | none => .ok ⟨typing, hlawful, hrunnable, htable, hprogram, htype⟩
        else
          match Table.checkLawful table with
          | some (.duplicateKey k) => .error (.duplicateKey k)
          | some (.builtinCollision k) => .error (.builtinCollision k)
          | some (.valueRowTrailing k) => .error (.valueRowTrailing k)
          | none => .error (.duplicateKey ("", []))

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
  split <;> simp_all

/-- Integer syntax stated inside the program tree is refused with its exact path, after the
table scan succeeds (DI-92). -/
theorem admitProgram_program_int (program : NativeEff) (table : RowTable) (pos : Path)
    (hTable : findIntInTable table = none) (h : findIntInProgram program = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · simp_all
  · split <;> simp_all

/-- An inferred integer occurrence is refused after the table and the tree scans succeed. -/
theorem admitProgram_type_int (program : NativeEff) (table : RowTable) (ty : EffTy) (pos : Path)
    (hTable : findIntInTable table = none) (hProgram : findIntInProgram program = none)
    (hTy : typeOfProgram (nativeSignature table) program = some ty)
    (hInt : findIntInEffTy ty = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · simp_all
  · split
    · simp_all
    · split
      · rename_i hnone
        unfold checkTypedProgram at hnone
        split at hnone <;> simp_all
      · rename_i typing _
        have heq : typing.ty = ty := Option.some.inj (typing.typed.symm.trans hTy)
        split
        · rename_i pos' hpos'
          rw [heq] at hpos'
          have hpos : pos' = pos := by injection (hpos'.symm.trans hInt)
          rw [hpos]
        · rename_i hnone
          rw [heq, hInt] at hnone
          contradiction

end Effect4.Program
