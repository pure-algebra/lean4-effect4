import Effect4.Program.Table
import Effect4.Program.Typing
import Effect4.Program.Native

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
  /-- A raw table or inferred program type mentions the reserved integer constructor. -/
  | uninhabited («at» : Path)
deriving DecidableEq, Repr

/-- A program admitted to run against a table: its type, the execution checks, and
the successful integer scans. The fields are proofs, so an `AdmittedProgram` cannot be forged by
building the structure with the wrong table — the table and the program are its indices. -/
structure AdmittedProgram (program : NativeEff) (table : RowTable) where
  ty : EffTy
  typed : typeOfProgram (nativeSignature table) program = some ty
  lawful : Table.lawful table = true
  runnable : checkTable table = none
  intFreeTable : findIntInTable table = none
  intFreeType : findIntInEffTy ty = none

/-- Decide admission by scanning raw table types, inferring the program type, scanning
its columns, then checking names and registrations. Each certificate field records
the exact check that admitted it. -/
def admitProgram (program : NativeEff) (table : RowTable := []) :
    Except AdmitRefusal (AdmittedProgram program table) :=
  match htable : findIntInTable table with
  | some pos => .error (.uninhabited pos)
  | none =>
    match htyped : typeOfProgram (nativeSignature table) program with
    | none => .error .illTyped
    | some ty =>
      match htype : findIntInEffTy ty with
      | some pos => .error (.uninhabited pos)
      | none =>
        if hlawful : Table.lawful table = true then
          match hrunnable : checkTable table with
          | some why => .error (.table why)
          | none => .ok ⟨ty, htyped, hlawful, hrunnable, htable, htype⟩
        else
          match Table.checkLawful table with
          | some (.duplicateKey k) => .error (.duplicateKey k)
          | some (.builtinCollision k) => .error (.builtinCollision k)
          | some (.valueRowTrailing k) => .error (.valueRowTrailing k)
          | none => .error (.duplicateKey ("", []))

/-- Integer syntax in any supplied table row is refused with its exact path. -/
theorem admitProgram_table_int (program : NativeEff) (table : RowTable) (pos : Path)
    (h : findIntInTable table = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split <;> simp_all

/-- An inferred integer occurrence is refused after the table scan succeeds. -/
theorem admitProgram_type_int (program : NativeEff) (table : RowTable) (ty : EffTy) (pos : Path)
    (hTable : findIntInTable table = none) (hTy : typeOfProgram (nativeSignature table) program = some ty)
    (hInt : findIntInEffTy ty = some pos) :
    admitProgram program table = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · simp_all
  · split
    · simp_all
    · rename_i ty' hty'
      have heq : ty' = ty := by injection (hty'.symm.trans hTy)
      subst heq
      split
      · rename_i pos' hpos'
        have hpos : pos' = pos := by injection (hpos'.symm.trans hInt)
        rw [hpos]
      · rename_i hnone
        rw [hInt] at hnone
        contradiction

end Effect4.Program
