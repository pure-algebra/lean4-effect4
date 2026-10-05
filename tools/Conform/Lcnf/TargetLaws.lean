import Conform.Lcnf.SemanticsTarget

/-!
# Conform.Lcnf.TargetLaws — laws of the target evaluator

**What it is.** Theorems about `Target.evalT` that a rule of the LCNF route rests on. The first
is the law of `let x = e in x`: the route writes `v` where the LCNF has `let x := v; return x`.

**Depends on.** `Conform.Lcnf.SemanticsTarget`. Nothing from this repository's core.

**Why the law is here and not in a battery.** Every statement about `Target.evalT` reaches
`Classical.choice`, proved or planned, because the evaluator's own definition does. Two rules
of `Target.applyPrim` traverse a `String`: the rule `lcnf_utf8_length` calls `String.length`,
and `cmp?` orders two strings with `<`. The axiom gate (`Test/Audit/AxiomGate.lean`) holds
every declaration of a `Test.*` module to `[propext, Quot.sound]`, so such a statement cannot
be a declaration there. This module is tooling, outside the gate's audit. The battery
`Test/Audit/LetReturn.lean` pins the law's statement and its axiom list, and holds the finite
control on the route.

**Properties.**
* The law's proof adds no axiom to those of `Target.evalT`: both lists are
  `[propext, Classical.choice, Quot.sound]` — *checked* (`#guard_msgs` in the battery).
* The proof leaves the inner evaluation opaque. It unfolds one `let` and one variable, and it
  unfolds no `partial` helper.
-/

namespace Conform.Lcnf.Target

/-- The head binding answers its own name. `decide_eq_true` is the lawful equality of `String`
by name: a `simp` at `(x == x) = true` reaches `Classical.choice`. A step of
`let_return_outcome`. -/
theorem TEnv.find?_head (env : TEnv) (x : String) (v : TValue) :
    TEnv.find? ((x, v) :: env) x = some v := by
  unfold TEnv.find?
  rw [List.find?_cons]
  have h : ((x, v).1 == x) = true := decide_eq_true rfl
  rw [h]
  rfl

/-- One step of the evaluator at a `let`. A step of `let_return_outcome`. -/
theorem evalT_letIn (prog : Program) (fuel : Nat) (env : TEnv) (x : String) (v body : Expr) :
    evalT prog (fuel + 1) env (.letIn x v body) =
      match evalT prog fuel env v with
      | .value vv => evalT prog fuel ((x, vv) :: env) body
      | o => o := rfl

/-- A name that the environment binds evaluates to its value. A step of
`let_return_outcome`. -/
theorem evalT_var_bound (prog : Program) (fuel : Nat) (env : TEnv) (x : String) (v : TValue)
    (h : env.find? x = some v) : evalT prog (fuel + 1) env (.var x) = .value v := by
  rw [evalT]
  simp only [h]

/-- **The law of `let x = e in x`.** The target evaluator gives `let x = e in x` at fuel `n + 2`
the outcome that it gives `e` at fuel `n + 1`: a value, a refusal, the target's own exception
or the fuel frontier.

- Concept: `translation-simulation`; property: an equal-observation law of one local rewrite
  of the LCNF route.
- Question: the proposed registry claim `ocaml-let-return-outcome` (role simulation); consumer:
  the identity-continuation case of `OCaml5.Lcnf.code` (`src/OCaml5/Lcnf/Translate.lean`).
- Reach: every outcome of `Target.evalT`, under the two related fuels, for every program,
  environment, name and expression. `x` may be bound in the environment or not. Decisions
  row 28 (open) bounds what a verified lowering is.
- Does not establish: the emitted bytes, the cost, any other rule of the translation, or the
  agreement of this evaluator with compiled OCaml. The same-fuel statement is false
  (`let_return_same_fuel_refuted`). The axiom list holds `Classical.choice`, from the
  evaluator's definition, so the law is outside the trust ceiling of the proof graph.
- Unlocks: R8, its open part on typed lowering: the first checked local rewrite of the route. -/
theorem let_return_outcome (prog : Program) (n : Nat) (env : TEnv) (x : String) (e : Expr) :
    evalT prog (n + 2) env (.letIn x e (.var x)) = evalT prog (n + 1) env e := by
  rw [evalT_letIn]
  cases h : evalT prog (n + 1) env e with
  | value vv => exact evalT_var_bound prog n _ x vv (TEnv.find?_head env x vv)
  | stuck r => rfl
  | outOfFuel => rfl
  | exn m => rfl

/-- The red control of `let_return_outcome`: with one fuel for both sides the statement is
false. At fuel one the `let` has no fuel left for its right side, and the literal answers. -/
theorem let_return_same_fuel_refuted :
    ¬ ∀ (prog : Program) (n : Nat) (env : TEnv) (x : String) (e : Expr),
        evalT prog (n + 1) env (.letIn x e (.var x)) = evalT prog (n + 1) env e := by
  intro h
  have frontier : evalT default 1 [] (.letIn "x" (.int 7) (.var "x")) = .outOfFuel := rfl
  have answer :
      evalT default 1 [] (.int 7) = .value (.int ((default : Program).pe.word.wrap 7)) := rfl
  exact TOutcome.noConfusion (frontier.symm.trans ((h default 0 [] "x" (.int 7)).trans answer))

end Conform.Lcnf.Target
