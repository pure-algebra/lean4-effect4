import Effect4.Laws.Program.Typing.Sound

/-! Input-indexed checking for tools and proofs. A successful value carries its declarative
judgment. Assessment gaps describe the separate connections that this checker does not prove;
removing a gap from a report cannot construct a judgment or a host theorem. -/
namespace Effect4.Program
open Conform.Effect4.Typing
open Std.Do

inductive TypingGap where
  | checkerRefusal
  | valueModel
  | targetRepresentation
  | executionRelation
  | hostBehavior
  deriving DecidableEq, Repr

structure TypingRefusal where
  path : List Nat := []
  reason : TypingGap := .checkerRefusal
  deriving DecidableEq, Repr

/-- The checker is the only source of the returned type, and the proof refers to this input. -/
def checkTyping (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
    Except TypingRefusal { t : EffTy // HasTy sig env program t } :=
  match h : effTy sig env program with
  | none => .error {}
  | some t => .ok ⟨t, effTy_sound sig program env t h⟩

/-- A refusal states exactly that the executable checker did not return a type. It does not
claim that no broader language could assign one. -/
theorem checkTyping_refuses_iff (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
    checkTyping sig env program = .error {} ↔ effTy sig env program = none := by
  unfold checkTyping
  split <;> simp_all

/-- Independent obligations remain visible even after a typing result is proved. -/
structure TypingAssessment (sig : Signature Op) (env : TyEnv) (program : Eff Op) where
  typing : Except TypingRefusal { t : EffTy // HasTy sig env program t }
  remaining : List TypingGap

def assessTyping (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
    TypingAssessment sig env program :=
  ⟨checkTyping sig env program,
    [.valueModel, .targetRepresentation, .executionRelation, .hostBehavior]⟩

/-- An Except specification keeps the refusal observation as well as success. Standard
`Std.Do` bind/throw/pure specifications can compose this with downstream checking. -/
@[spec] theorem checkTyping_spec (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
    ⦃⌜True⌝⦄ checkTyping sig env program
      ⦃(fun t => ⌜HasTy sig env program t.val⌝,
        fun _ => ⌜effTy sig env program = none⌝, ())⦄ := by
  unfold checkTyping
  split <;> simp_all [Triple.iff, wp, Except.instWP._aux_1, Id.run, ExceptT.run]
  apply effTy_sound sig program env
  assumption

end Effect4.Program
