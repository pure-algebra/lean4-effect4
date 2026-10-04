import Effect4.Program.SigApp
import Effect4.Program.CheckedTyping
import Effect4.Program.Fragment
import Effect4.Program.Formation

/-!
# Program.Admission — static verification and admission certificates

A program is admitted to run against an application's signature (`SigApp`, decisions row 21:
the signature's admission is part of program admission) when:

1. No raw table column mentions the reserved integer type (`findIntInTable`). DI-67 rules the
   refusal: `uninhabited at`, with the integer's path.
2. The signature is lawful (`admitSig app = .ok ()`, `Program/SigApp.lean`). Every row is one this
   runner registers, collides with no built-in key, names no trailing argument as a value row,
   introduces no internal handle kind in its answer or error (row 97 interim), has no empty column
   (rows 127 and 149), has an admissible template and is well scoped (row 42). The row keys are
   distinct, every service declaration is lawful at a distinct code (rows 113 and 114), and every
   key a row requires has a carrier. Refused as `signature why`, with the signature's own located
   refusal.
3. The program tree mentions no reserved integer type (`findIntInProgram`, DI-92).
4. Every raw type of the program and the table is formed: distinct record names, valid map keys
   (rows 192 and 193).
5. The program is well-typed at the signature (`typeOfProgram app.signature program = some ty`).
6. The inferred answer and error mention no reserved integer type, and each is inhabited or
   `never` (`admitColumn`, rows 127 and 149; refused as `uninhabited at` and `emptyColumn at`).

`admitProgram` verifies all six, in this order, producing a certified `AdmittedProgram` whose
fields witness each check. If admission fails, an exact `AdmitRefusal` reports the failure.
Admission depends strictly on the program plane and never imports codegen.

A caller at a row table alone admits at `⟨table, []⟩`, whose signature is `nativeSignature table`
by definition (`SigApp.signature_nil`).

`admitStraightProgram` adds membership in the existing straight fragment to that
same admission result. It does not re-run a second typing judgment or claim an
application behavior; execution and safety results remain in the Laws graph.
-/

namespace Effect4.Program

/-- Scan every supplied row before normalization can discard any syntax: the table's integer
refusal is DI-67's `uninhabited at`, at the integer's path. The signature's admission reads the
same scan at each column's root (`rowChecks`). -/
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

/-- DI-92's raw integer profile reaches every program annotation, including a
record whose value is later discarded. The shared collector retains cursor paths. -/
def findIntInProgram (program : NativeEff) : Option Path :=
  (Formation.programAnnotations program).findSome? fun (path, ty) => findInt path ty

/-! ## The column check, located (rows 127 and 149)

`admitColumn` at every column admission reads, each refusal at its position. A supplied row's
request, answer and error column is the signature's (`RowReason.emptyColumn`, `rowChecks`); the
program's inferred answer and error are this module's (`findEmptyColumnInEffTy`). Its refusal is
`emptyColumn at` (row 149); the frozen `AdmitRefusal.uninhabited at` stays the `int` scan's.
`admitProgram` runs it last, so every earlier refusal keeps its statement. -/

/-- The column check at a position: the position when the column is refused (rows 127, 149). -/
def emptyColumnAt (pos : Path) (t : Ty) : Option Path :=
  if admitColumn t then none else some pos

/-- The program's own columns: the inferred answer and error. -/
def findEmptyColumnInEffTy (ty : EffTy) : Option Path :=
  emptyColumnAt ["program", "answer"] ty.answer <|> emptyColumnAt ["program", "error"] ty.error

theorem emptyColumnAt_eq_none_iff (pos : Path) (t : Ty) :
    emptyColumnAt pos t = none ↔ admitColumn t = true := by
  unfold emptyColumnAt
  cases admitColumn t with
  | true => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- **The program scan finds nothing exactly when both columns are admitted (proved).** -/
theorem findEmptyColumnInEffTy_eq_none_iff (ty : EffTy) :
    findEmptyColumnInEffTy ty = none ↔ admitColumn ty.answer = true ∧ admitColumn ty.error = true := by
  unfold findEmptyColumnInEffTy
  simp only [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_none_iff,
    emptyColumnAt_eq_none_iff]

/-- Admission refusals, reporting the exact failure reason. -/
inductive AdmitRefusal
  /-- `Program.typeOf` answered `none` at the application's signature. -/
  | illTyped
  /-- The application's signature is not lawful, with its located refusal (`admitSig`,
  decisions row 21): a row, a row key, a service declaration, a service code or a required key
  with no carrier. -/
  | signature (why : SigRefusal)
  /-- A raw table, the program tree or the inferred program type mentions the reserved
  integer constructor. -/
  | uninhabited («at» : Path)
  /-- The program's answer or error column is empty and is not `never` (rows 127, 149). -/
  | emptyColumn («at» : Path)
  /-- A raw type fails the shared formation judgment (rows 192 and 193). -/
  | formation (why : Formation.Refusal)
deriving DecidableEq, Repr

/-- A program admitted to run against an application's signature: its type at
`app.signature`, the table's integer scan, the signature's admission, raw formation and the
program's integer and column scans. Its proof fields refer to the exact program and signature
that index the certificate. -/
structure AdmittedProgram (program : NativeEff) (app : SigApp)
    extends TypedProgram app.signature program where
  intFreeTable : findIntInTable app.rows = none
  signature : admitSig app = .ok ()
  formed : Formation.InputFormed program app.rows
  intFreeProgram : findIntInProgram program = none
  intFreeType : findIntInEffTy ty = none
  columnsType : findEmptyColumnInEffTy ty = none

/-- Decide admission: the raw table's integer scan (DI-67), the signature's admission
(`admitSig`), the program tree's integer scan, raw formation, the one typing certificate
(`checkTypedProgram`, shared with code generation) at the signature, and last the inferred
columns' integer and column scans (rows 127, 149). Each certificate field records the exact check
that admitted it. -/
def admitProgram (program : NativeEff) (app : SigApp := {}) :
    Except AdmitRefusal (AdmittedProgram program app) :=
  match htable : findIntInTable app.rows with
  | some pos => .error (.uninhabited pos)
  | none =>
    match hsig : admitSig app with
    | .error why => .error (.signature why)
    | .ok () =>
    match hprogram : findIntInProgram program with
    | some pos => .error (.uninhabited pos)
    | none =>
    match hformed : Formation.checkInput program app.rows with
    | some why => .error (.formation why)
    | none =>
    match checkTypedProgram app.signature program with
    | none => .error .illTyped
    | some typing =>
      match htype : findIntInEffTy typing.ty with
      | some pos => .error (.uninhabited pos)
      | none =>
        match hcolType : findEmptyColumnInEffTy typing.ty with
        | some pos => .error (.emptyColumn pos)
        | none => .ok ⟨typing, htable, hsig,
            (Formation.checkInput_eq_none_iff program app.rows).mp hformed, hprogram, htype,
            hcolType⟩

/-- Failure of ordinary admission, or a program outside the proved straight fragment.
Outside-fragment refusal does not mean that the program is ill-typed. -/
inductive StraightAdmitRefusal
  | admission (why : AdmitRefusal)
  | outsideFragment
deriving DecidableEq, Repr

/-- Ordinary admission plus executable membership in the straight fragment. The
existing runtime certificate remains available to the admitted run entry points.
No denotation, safety theorem or user specification is stored in this package. -/
structure AdmittedStraightProgram (program : NativeEff) (app : SigApp) where
  admitted : AdmittedProgram program app
  straight : Denote.Straight program = true

/-- Compute ordinary admission first, preserving its refusal, then check membership
in the existing straight fragment. The successful package records those two checks. -/
def admitStraightProgram (program : NativeEff) (app : SigApp := {}) :
    Except StraightAdmitRefusal (AdmittedStraightProgram program app) :=
  match admitProgram program app with
  | .error why => .error (.admission why)
  | .ok admitted =>
    if h : Denote.Straight program = true then .ok ⟨admitted, h⟩
    else .error .outsideFragment

/-- Fragment admission retains every ordinary admission refusal. -/
theorem admitStraightProgram_admission_error (program : NativeEff) (app : SigApp)
    (why : AdmitRefusal) (h : admitProgram program app = .error why) :
    admitStraightProgram program app = .error (.admission why) := by
  simp only [admitStraightProgram, h]

/-- An admitted member carries the same admission certificate and its membership proof. -/
theorem admitStraightProgram_ok (program : NativeEff) (app : SigApp)
    (admitted : AdmittedProgram program app)
    (hAdmit : admitProgram program app = .ok admitted)
    (hStraight : Denote.Straight program = true) :
    admitStraightProgram program app = .ok ⟨admitted, hStraight⟩ := by
  simp only [admitStraightProgram, hAdmit, hStraight, ↓reduceDIte]

/-- A well-admitted program outside the fragment receives the distinct domain refusal. -/
theorem admitStraightProgram_outside (program : NativeEff) (app : SigApp)
    (admitted : AdmittedProgram program app)
    (hAdmit : admitProgram program app = .ok admitted)
    (hStraight : Denote.Straight program = false) :
    admitStraightProgram program app = .error .outsideFragment := by
  simp only [admitStraightProgram, hAdmit, hStraight, Bool.false_eq_true, ↓reduceDIte]

/-- Integer syntax in any supplied table row is refused with its exact path (DI-67), before the
signature's admission. -/
theorem admitProgram_table_int (program : NativeEff) (app : SigApp) (pos : Path)
    (h : findIntInTable app.rows = some pos) :
    admitProgram program app = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    have same : found = pos := Option.some.inj (hfound.symm.trans h)
    cases same
    rfl
  · rename_i hnone
    rw [h] at hnone
    contradiction

/-- An unlawful signature is refused with its own located refusal, right after the table's
integer scan (decisions row 21). -/
theorem admitProgram_signature (program : NativeEff) (app : SigApp) (why : SigRefusal)
    (hTable : findIntInTable app.rows = none) (h : admitSig app = .error why) :
    admitProgram program app = .error (.signature why) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i refused hrefused
      have same : refused = why := Except.error.inj (hrefused.symm.trans h)
      cases same
      rfl
    · rename_i hok
      rw [h] at hok
      contradiction

/-- Integer syntax stated inside the program tree is refused after the table's integer scan and
the signature's admission. -/
theorem admitProgram_program_int (program : NativeEff) (app : SigApp) (pos : Path)
    (hTable : findIntInTable app.rows = none) (hSig : admitSig app = .ok ())
    (h : findIntInProgram program = some pos) :
    admitProgram program app = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i refused hrefused
      rw [hSig] at hrefused
      contradiction
    · split
      · rename_i found hfound
        have same : found = pos := Option.some.inj (hfound.symm.trans h)
        cases same
        rfl
      · rename_i hnone
        rw [h] at hnone
        contradiction

/-- An inferred integer occurrence is refused after the raw scans, the signature's admission
and formation succeed. -/
theorem admitProgram_type_int (program : NativeEff) (app : SigApp) (ty : EffTy) (pos : Path)
    (hTable : findIntInTable app.rows = none) (hSig : admitSig app = .ok ())
    (hProgram : findIntInProgram program = none)
    (hFormed : Formation.checkInput program app.rows = none)
    (hTy : typeOfProgram app.signature program = some ty)
    (hInt : findIntInEffTy ty = some pos) :
    admitProgram program app = .error (.uninhabited pos) := by
  unfold admitProgram
  split
  · rename_i found hfound
    rw [hTable] at hfound
    contradiction
  · split
    · rename_i refused hrefused
      rw [hSig] at hrefused
      contradiction
    · split
      · rename_i found hfound
        rw [hProgram] at hfound
        contradiction
      · split
        · rename_i why refused
          rw [hFormed] at refused
          contradiction
        · have hChecked : checkTypedProgram app.signature program = some ⟨ty, hTy⟩ := by
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
