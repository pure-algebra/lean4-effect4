import Effect4.Laws.Program.Typing.Inversion

/-!
# The select rule keeps both requirement rows

Concept: residual-program-typing. Role: finite controls of the checker's select rule.
The inversion reader refuses a rule that discards the second arm's requirements.
The checker probe requires two distinct service keys, even with a literal scrutinee.
These controls add no theorem and establish no progress or host agreement.
-/

namespace Test.Program.SelectRulesRed

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

variable {Op : Type}

/-- An intentionally wrong rule: only the first arm's requirements remain. -/
inductive WrongSelect (sig : Signature Op) : TyEnv → Eff Op → EffTy → Prop
  | select {env : TyEnv} {s : Term} {d : Decision} {a0 a1 : Eff Op} {t : Ty}
      {e0 e1 : List Ty} {t0 t1 : EffTy} {answer : Ty} :
      termTy sig env s = some t →
      d.arms t = some (e0, e1) →
      effTy sig (env ++ e0) a0 = some t0 →
      effTy sig (env ++ e1) a1 = some t1 →
      EffTy.joinAnswer t0.answer t1.answer = some answer →
      WrongSelect sig env (.select s d a0 a1)
        ⟨answer, t0.error.join t1.error, t0.requires⟩

/--
error: Type mismatch
  WrongSelect.select hs harms h0 h1 hj
has type
  WrongSelect sig env (Eff.select s d a0 a1)
    { answer := answer, error := t0.error.join t1.error, requires := t0.requires }
but is expected to have type
  WrongSelect sig env (Eff.select s d a0 a1)
    { answer := answer, error := t0.error.join t1.error, requires := t0.requires.union t1.requires }
-/
#guard_msgs (error) in
example (sig : Signature Op) (env : TyEnv) (s : Term) (d : Decision)
    (a0 a1 : Eff Op) (t : EffTy)
    (h : effTy sig env (.select s d a0 a1) = some t) :
    WrongSelect sig env (.select s d a0 a1) t := by
  obtain ⟨ty, e0, e1, t0, t1, answer, hs, harms, h0, h1, hj, rfl⟩ := inv_select sig env s d a0 a1 t h
  exact .select hs harms h0 h1 hj


def leftKey : ServiceKey := ⟨⟨1⟩, ⟨0⟩⟩
def rightKey : ServiceKey := ⟨⟨2⟩, ⟨0⟩⟩
def signature : Signature Empty :=
  { rowOf := Empty.elim, atomOf := fun _ _ => none,
    scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => some .nat }

#guard (effTy signature []
  (.select (.lit (.bool true)) .bool (.service leftKey) (.service rightKey))).map
    EffTy.requires = some (Requirement.ofList [leftKey, rightKey])
#guard Requirement.ofList [leftKey] != Requirement.ofList [leftKey, rightKey]

end Test.Program.SelectRulesRed
