import Effect4.Program.SigApp
import Effect4.Program.CheckedTyping
import Effect4.Program.Fragment
import Effect4.Program.Formation

/-!
# Program.Admission — static verification and admission certificates

A program is admitted to run against an application's signature (`SigApp`, decisions row 21:
the signature's admission is part of program admission) when:

1. The signature is lawful (`admitSig app = .ok ()`, `Program/SigApp.lean`). Every row is one this
   runner registers, collides with no built-in key, names no trailing argument as a value row,
   introduces no internal handle kind in its answer or error (row 97 interim), has no empty column
   (rows 127 and 149), has an admissible template and is well scoped (row 42). The row keys are
   distinct, every service declaration is lawful at a distinct code (rows 113 and 114), and every
   key a row requires has a carrier. Refused as `signature why`, with the signature's own located
   refusal.
2. Every raw type of the program, the table and the declared service carriers is formed:
   distinct record names, valid map keys (rows 192 and 193), and no type variable outside a
   row's template (row 288, point 6 a).
3. The program is well-typed at the signature (`typeOfProgram app.signature program = some ty`).
4. The inferred answer and error are each inhabited or `never` (`admitColumn`, rows 127 and
   149; refused as `emptyColumn at`).

An integer column is admitted: the integer scan went with the integers packet's slice 1
(decisions rows 121, 309 and 317). `admitProgram` verifies all four, in this order, producing a certified `AdmittedProgram` whose
fields witness each check. If admission fails, an exact `AdmitRefusal` reports the failure.
Admission depends strictly on the program plane and never imports codegen.

A caller at a row table alone admits at `⟨table, []⟩`, whose signature is `nativeSignature table`
by definition (`SigApp.signature_nil`).

`admitStraightProgram` adds membership in the existing straight fragment to that
same admission result. It does not re-run a second typing judgment or claim an
application behavior; execution and safety results remain in the Laws graph.
-/

namespace Effect4.Program

/-! ## The column check, located (rows 127 and 149)

`admitColumn` at every column admission reads, each refusal at its position. A supplied row's
request, answer and error column is the signature's (`RowReason.emptyColumn`, `rowChecks`); the
program's inferred answer and error are this module's (`findEmptyColumnInEffTy`). Its refusal is
`emptyColumn at` (row 149). `admitProgram` runs it last, so every earlier refusal keeps its statement. -/

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
  /-- The program's answer or error column is empty and is not `never` (rows 127, 149). -/
  | emptyColumn («at» : Path)
  /-- A raw type fails the shared formation judgment (rows 192 and 193). -/
  | formation (why : Formation.Refusal)
deriving DecidableEq, Repr

/-- A program admitted to run against an application's signature: its type at
`app.signature`, the signature's admission, raw formation and the program's column scan. Its
proof fields refer to the exact program and signature that index the certificate. -/
structure AdmittedProgram (program : NativeEff) (app : SigApp)
    extends TypedProgram app.signature program where
  signature : admitSig app = .ok ()
  formed : Formation.InputFormed program app.rows app.services
  columnsType : findEmptyColumnInEffTy ty = none

/-- Decide admission: the signature's admission (`admitSig`), raw formation, the one typing
certificate (`checkTypedProgram`, shared with code generation) at the signature, and last the
inferred columns' column scan (rows 127, 149). Each certificate field records the exact check
that admitted it. -/
def admitProgram (program : NativeEff) (app : SigApp := {}) :
    Except AdmitRefusal (AdmittedProgram program app) :=
  match hsig : admitSig app with
  | .error why => .error (.signature why)
  | .ok () =>
    match hformed : Formation.checkInput program app.rows app.services with
    | some why => .error (.formation why)
    | none =>
      match checkTypedProgram app.signature program with
      | none => .error .illTyped
      | some typing =>
        match hcolType : findEmptyColumnInEffTy typing.ty with
        | some pos => .error (.emptyColumn pos)
        | none => .ok ⟨typing, hsig,
            (Formation.checkInput_eq_none_iff program app.rows app.services).mp hformed, hcolType⟩

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

/-- An unlawful signature is refused with its own located refusal, first (decisions row 21). -/
theorem admitProgram_signature (program : NativeEff) (app : SigApp) (why : SigRefusal)
    (h : admitSig app = .error why) :
    admitProgram program app = .error (.signature why) := by
  unfold admitProgram
  split
  · rename_i refused hrefused
    have same : refused = why := Except.error.inj (hrefused.symm.trans h)
    cases same
    rfl
  · rename_i hok
    rw [h] at hok
    contradiction

end Effect4.Program
