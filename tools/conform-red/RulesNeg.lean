import Effect4.Laws.Program.Typing.Inversion

/-!
# conform-red/RulesNeg — the red control for the declarative type system

**This file must fail to compile.** It is outside the `Conform` glob (`lakefile.toml`:
`srcDir = "tools"`, `globs = ["Conform.+"]`), so `lake build Conform` never sees it; it is run
on its own and its failure is the evidence that the rules of
`Conform.Effect4.Typing.HasTy` and the two directions of `Conform.Effect4.Typing.Sound` are not
vacuous — that a *wrong* rule really does break, at the exact place the discipline says it
should.

Run it, and expect exit 1 with the two errors named below:

```
cd /Users/pooks/Dev/lean4-effect4
LEAN_NUM_THREADS=3 lake env lean -M6144 tools/conform-red/RulesNeg.lean   # exit 1
```

**The wrong rule.** `WrongBranch` is `HasTy.branch` with one column changed: the requirement
row of a conditional is the `then` arm's alone, `a.requires`, instead of the union
`a.requires.union b.requires`. This is not an invented mistake — it is what rc.112 infers for
the printed head `Effect.suspend(() => t ? a : b)` (types seat §3.4), and it is exactly the
error `tools/conform-red/Probe2Neg.lean` plants one level down, at the triple. Planting it in
the *rule* shows the failure reaches the two theorems the seat is measured by:

1. **The soundness case fails.** `wrongBranch_sound` is the `branch` arm of `effTy_sound`
   verbatim — the generated `inv_branch`, then the rule — and it is refused with an
   application type mismatch: the inversion hands over the union, the rule wants the `then`
   arm's row alone. *The generated inversion is what refuses it*, which is the point: the
   machine-written premises and the human-written conclusion are checked against each other.
2. **The completeness case fails too, and differently.** `wrongBranch_complete` reduces
   through the checker's `branch` equation and leaves the residual pure goal
   `a.requires = a.requires.union b.requires` open — a proposition that is false as soon as
   the `else` arm requires a key the `then` arm does not. So the wrong rule is not merely
   unprovable in one direction; it does not describe `effTy` in either.

Both errors are *unsolved goals* or *type mismatch* at the marked lines. If this file ever
compiles, something in `HasTy`, `Inversion` or `Sound` has stopped saying what it claims.
-/

namespace Conform.Effect4.Typing.RulesNeg

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

variable {Op : Type}

/-- The wrong rule: the conditional's requirement row is the `then` arm's alone. Everything
else is `HasTy.branch` unchanged. -/
inductive WrongBranch (sig : Signature Op) : TyEnv → Eff Op → EffTy → Prop
  | branch {env : TyEnv} {test : Term} {thenB elseB : Eff Op} {a b : EffTy} {answer : Ty} :
      termTy sig env test = some .bool →
      effTy sig env thenB = some a →
      effTy sig env elseB = some b →
      EffTy.joinAnswer a.answer b.answer = some answer →
      WrongBranch sig env (.branch test thenB elseB)
        ⟨answer, a.error.join b.error, a.requires⟩

/-- ERROR 1 — the soundness case. The `branch` arm of `effTy_sound`, verbatim, against the
wrong rule. The generated inversion delivers `a.requires.union b.requires`; the rule concludes
`a.requires`; the application is refused. -/
theorem wrongBranch_sound (sig : Signature Op) (env : TyEnv) (test : Term)
    (thenB elseB : Eff Op) (t : EffTy)
    (h : effTy sig env (.branch test thenB elseB) = some t) :
    WrongBranch sig env (.branch test thenB elseB) t := by
  obtain ⟨htest, a, b, answer, ha, hb, hj, rfl⟩ := inv_branch sig env test thenB elseB t h
  exact .branch htest ha hb hj

/-- ERROR 2 — the completeness case. The checker's `branch` equation reduces the goal to
`a.requires = a.requires.union b.requires`, which `simp` cannot close and which is false
whenever the `else` arm requires a key the `then` arm does not. -/
theorem wrongBranch_complete (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy)
    (hd : WrongBranch sig env e t) : effTy sig env e = some t := by
  cases hd
  rename_i htest ha hb hj
  simp [effTy, htest, ha, hb, hj]

end Conform.Effect4.Typing.RulesNeg
