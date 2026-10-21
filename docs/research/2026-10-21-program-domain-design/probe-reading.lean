import Effect4.Laws.Program.Folds.Checker
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.ProfileSupport
import Effect4.Laws.Program.CheckedTyping

/-!
# Probe: the algebraic reading, stated against the tree

Each `example` below restates, with its full statement, one fact the reading of the note rests
on, and closes it with the tree's own theorem or by `rfl`. Nothing here is new; the probe checks
that the citations of the note say what the note says they say.
-/

set_option autoImplicit false

namespace Probe.Reading

open Effect4 Effect4.Program

/-! ## 1. The free object and its fold -/

-- reader: `Eff NativeOp` is initial: every homomorphism out of it is the fold of its algebra
example {R : EffFam → Type} (alg : EffAlgebra NativeOp R) (hom : EffHom alg)
    (e : Eff NativeOp) : hom.f_eff e = cata_eff alg e :=
  hom_eq_cata_eff hom e

/-! ## 2. The signature is data, and a program reads it by position -/

-- reader: Σ_app is interpreted as a typing signature over the native alphabet
example : SigApp → Signature NativeOp := SigApp.signature

-- reader: a host call is a position, in the domain exactly when the table has a row there
example (app : SigApp) (i : Nat) :
    app.signature.dom (.external i) = decide (i < app.rows.length) := rfl

-- reader: an invocation and a parameter's run are outside the application's domain; only a
-- block's signature (`Signature.withDefs`) and a body's (`Signature.withParams`) admit them
example (app : SigApp) (k : Nat) : app.signature.dom (.call k) = false := rfl
example (app : SigApp) (k : Nat) : app.signature.dom (.param k) = false := rfl

/-! ## 3. Typing is a paramorphism of the checker's algebra -/

-- reader: the checker is the fold of its algebra (`fold_of`, accumulator shape): the carrier
-- pairs each subtree with a function of the environment and the path
example (sig : Signature NativeOp) (env : TyEnv) (p : List Nat) (e : Eff NativeOp) :
    Checker.check sig env p e = (cata_eff (Checker.check.alg sig) e).snd env p :=
  Checker.check.eq_cata sig env p e

-- reader: the whole-program typing reads the references' formation, then the module check of
-- the expansion
example (sig : Signature NativeOp) (program : Eff NativeOp) :
    typeOfProgram sig program =
      if program.layerRefsWF then (Checker.checkModule sig program.expandRefs).toOption
      else none := rfl

/-! ## 4. Admission: four judgments, each with its located refusal and its completeness law -/

-- reader: signature admission is complete against `LawfulSig`
example (app : SigApp) : admitSig app = .ok () ↔ LawfulSig app := admitSig_ok_iff app

-- reader: raw formation is complete against `InputFormed`
example (program : Eff NativeOp) (app : SigApp) :
    Formation.checkInput program app.rows app.services = none ↔
      Formation.InputFormed program app.rows app.services :=
  Formation.checkInput_eq_none_iff program app.rows app.services

-- reader: the typing refusal is absent exactly when the program types
example (app : SigApp) (program : Eff NativeOp) :
    programRefusal app.signature program = none ↔
      (typeOfProgram app.signature program).isSome = true :=
  programRefusal_none_iff app.signature program

-- reader: the column scan finds nothing exactly when both columns are admitted
example (decls : TyDecls) (ty : EffTy) :
    findEmptyColumnInEffTy decls ty = none ↔
      admitColumnIn decls ty.answer = true ∧ admitColumnIn decls ty.error = true :=
  findEmptyColumnInEffTy_eq_none_iff decls ty

-- reader: the decision procedure answers every certificate it is given
example (program : Eff NativeOp) (app : SigApp) (a : AdmittedProgram program app) :
    admitProgram program app = .ok a :=
  admitProgram_eq_ok a

/-! ## 5. Profile support is asked by a target, outside admission -/

-- reader: profile support of a program is complete against its literal fold
example (profile : ProfileData) (program : NativeEff) :
    profile.literalRefusal program = none ↔ (natLiterals program).all profile.admitsNat = true :=
  ProfileData.literalRefusal_eq_none_iff profile program

end Probe.Reading
