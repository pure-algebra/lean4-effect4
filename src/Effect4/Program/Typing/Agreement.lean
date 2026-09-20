import Effect4.Program.Typing

/-!
# Program.Typing.Agreement — the projection law, the list sort, and the folds

What the core root proves about the checker's projections (`Program/Typing.lean`) without the
proof graph: the law of the projection (DI-86, `explain_none_iff`: a check is `ok` or it is
`error`, so `explain` is `none` exactly when `effTy` answers — `Api.check` is total by it), the
mode flag and the list sort's shape, the projections as the fold of `check.alg` at the root
(`effTy.eq_cata`, what the census reads). The term typer needs no agreement: `argTy` is the
fold (`Typing/Rules.lean`, `Folds/Term.lean`) and `termTy` its projection at `false`. Soundness
and completeness against `HasTy`, and every
consequence that needs them, are the proof graph's (`Laws/Program/Typing/CheckSound.lean`).
-/

namespace Effect4.Program

namespace Checker

variable {Op : Type}

open Effect4.Machine.Env (Requirement)

/-! ## The mode flag and the list sort -/

/-- After a `return` the tail must be empty. -/
theorem checkStmts_afterRet (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (ret p : List Nat) :
    (rest : Stmts Op) → checkStmts sig env inLoop (some ret) p rest =
      (match rest with
        | .nil => pure ⟨none, .never, Requirement.empty⟩
        | .cons _ _ => throw ⟨ret, .returnNotLast⟩)
  | .nil => rfl
  | .cons _ _ => rfl

/-- The signatures of a `cons` are a `cons`: never `ok []`. -/
theorem checkLayers_cons_ne_nil (sig : Signature Op) (p : List Nat) (next : LayerTerm Op)
    (tail : LayerTerms Op) : checkLayers sig p (.cons next tail) ≠ .ok [] := by
  rw [checkLayers.eq_2]
  cases checkLayer sig (p ++ [0]) next with
  | error r => exact nofun
  | ok h =>
    cases checkLayers sig (p ++ [1]) tail with
    | error r => exact nofun
    | ok t => exact nofun

/-- The nonempty merge is some. -/
theorem mergeNonempty_cons (l : LayerTy) :
    (ls : List LayerTy) → ∃ m, LayerTy.mergeNonempty (l :: ls) = some m
  | [] => ⟨l, rfl⟩
  | m :: rest =>
    let ⟨x, hx⟩ := mergeNonempty_cons m rest
    ⟨l.merge x, by simp only [LayerTy.mergeNonempty, hx, Option.map_some]⟩

/-! ## The whole program, and the projection law -/

/-- `typeOf` is the success of the check at the root, by definition. -/
theorem typeOf_eq (sig : Signature Op) (program : Eff Op) :
    (check sig [] [] program).toOption = typeOf sig program := rfl

/-- `explain` is the refusal of the check at the root, by definition. -/
theorem explain_eq (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    refusal (check sig env [] e) = explain sig env e := rfl

/-- A check is `ok` or it is `error`: its refusal is `none` exactly when its success is
`some`. Every `*_none_iff` below is this, through the agreement. -/
theorem refusal_none_iff {α : Type} (x : Except TypeRefusal α) :
    refusal x = none ↔ x.toOption.isSome := by
  cases x <;> simp only [refusal, Except.toOption, Option.isSome, reduceCtorEq,
    Bool.false_eq_true, iff_self]

end Checker

/-! ## The law of the projection (DI-86)

`explain` answers `none` exactly when `effTy` answers: the located refusal is the check's, by
definition, and a check is `ok` or it is `error`. Once a mutual induction following every arm
of two hand blocks (`Blame.lean`, before 2026-09-18). `Api.check` is total by it. -/

open Checker

/-- The law of the projection: `explain` refuses exactly when the checker does. -/
theorem explain_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    explain sig env e = none ↔ (effTy sig env e).isSome :=
  refusal_none_iff (check sig env [] e)

/-- A refusal is where a program fails to type, and a typed program has no refusal. -/
theorem blame_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    blame sig env e = none ↔ (effTy sig env e).isSome := by
  simp [blame, ← explain_none_iff]

end Effect4.Program
