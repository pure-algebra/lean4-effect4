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

**The wrong rule.** `WrongSelect` is `HasTy.select` with one column changed: the requirement
row of a value-decided fork is child 0's alone, `t0.requires`, instead of the union
`t0.requires.union t1.requires`. (Until `branch` retired into `select … .bool` this control
was stated on `HasTy.branch`; the planted error is the same.) This is not an invented mistake — it is what rc.112 infers for
the printed head `Effect.suspend(() => t ? a : b)` (types seat §3.4), and it is exactly the
error `tools/conform-red/Probe2Neg.lean` plants one level down, at the triple. Planting it in
the *rule* shows the failure reaches the two theorems the seat is measured by:

1. **The soundness case fails.** `wrongSelect_sound` is the `select` arm of `effTy_sound`
   verbatim — the inversion `inv_select`, then the rule — and it is refused with an
   application type mismatch: the inversion hands over the union, the rule wants child 0's
   row alone. *The generated inversion is what refuses it*, which is the point: the
   machine-written premises and the human-written conclusion are checked against each other.
2. **The completeness case fails too, and differently.** `wrongSelect_complete` reduces
   through the checker's `select` equation and leaves the residual pure goal
   `t0.requires = t0.requires.union t1.requires` open — a proposition that is false as soon as
   child 1 requires a key child 0 does not. So the wrong rule is not merely
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

/-- The wrong rule: the fork's requirement row is child 0's alone. Everything else is
`HasTy.select` unchanged. -/
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

/-- ERROR 1 — the soundness case. The `select` arm of `effTy_sound`, verbatim, against the
wrong rule. The inversion delivers `t0.requires.union t1.requires`; the rule concludes
`t0.requires`; the application is refused. -/
theorem wrongSelect_sound (sig : Signature Op) (env : TyEnv) (s : Term) (d : Decision)
    (a0 a1 : Eff Op) (t : EffTy)
    (h : effTy sig env (.select s d a0 a1) = some t) :
    WrongSelect sig env (.select s d a0 a1) t := by
  obtain ⟨ty, e0, e1, t0, t1, answer, hs, harms, h0, h1, hj, rfl⟩ := inv_select sig env s d a0 a1 t h
  exact .select hs harms h0 h1 hj

/-- ERROR 2 — the completeness case. The checker's `select` equation reduces the goal to
`t0.requires = t0.requires.union t1.requires`, which `simp` cannot close and which is false
whenever child 1 requires a key child 0 does not. -/
theorem wrongSelect_complete (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy)
    (hd : WrongSelect sig env e t) : effTy sig env e = some t := by
  cases hd
  rename_i hs harms h0 h1 hj
  simp [effTy, hs, harms, h0, h1, hj]

end Conform.Effect4.Typing.RulesNeg
