import Conform.Lcnf.TargetLaws
import Conform.Effect4.LcnfMl
import Conform.Effect4.LoweringNames
import OCaml5.Lcnf.Translate

/-! The law of `let x = e in x` on the target evaluator, pinned, with its finite control on the
LCNF route. The route writes `v` where the LCNF has `let x := v; return x`
(`OCaml5.Lcnf.code`, `src/OCaml5/Lcnf/Translate.lean`).

The law is `Conform.Lcnf.Target.let_return_outcome` (`tools/Conform/Lcnf/TargetLaws.lean`), with
its placement in its docstring. It is not a declaration of this file. `Target.evalT` reaches
`Classical.choice` through its own definition, so a statement about it cannot be a declaration
of a `Test.*` module under the axiom gate. This file declares nothing. It holds three checks:
the statement, the axiom lists, and one translated declaration evaluated in both forms. -/
open Lean Elab Command Compiler LCNF
open Conform.Lcnf

/-! ## The statement

Each `example` stops elaborating when the law's statement changes. -/

example (prog : Target.Program) (n : Nat) (env : Target.TEnv) (x : String) (e : Target.Expr) :
    Target.evalT prog (n + 2) env (.letIn x e (.var x)) = Target.evalT prog (n + 1) env e :=
  Target.let_return_outcome prog n env x e

-- The red control: with one fuel for both sides the statement is false.
example :
    ¬ ∀ (prog : Target.Program) (n : Nat) (env : Target.TEnv) (x : String) (e : Target.Expr),
        Target.evalT prog (n + 1) env (.letIn x e (.var x)) = Target.evalT prog (n + 1) env e :=
  Target.let_return_same_fuel_refuted

/-! ## The axiom lists

The law's list is the evaluator's own: the proof adds no axiom. `Classical.choice` is in both,
so the law is outside the ceiling `[propext, Quot.sound]`. The lookup lemma is under it. -/

/-- info: 'Conform.Lcnf.Target.evalT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Target.evalT

/--
info: 'Conform.Lcnf.Target.let_return_outcome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Target.let_return_outcome

/--
info: 'Conform.Lcnf.Target.let_return_same_fuel_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Target.let_return_same_fuel_refuted

/-- info: 'Conform.Lcnf.Target.TEnv.find?_head' does not depend on any axioms -/
#guard_msgs in
#print axioms Target.TEnv.find?_head

/-! ## The finite control on the route

`Conform.Effect4.LoweringNames.mulCap` is `x * _mula`. Its persisted mono body is
`let x := v; return x`, and the route writes `v`. The control builds the form with the `let`
again, under three names for the binder, and compares the two forms at related fuels: every
outcome, the frontier included. With one fuel for both it finds a difference. -/

run_cmd liftTermElabM do
  let root := ``Conform.Effect4.LoweringNames.mulCap
  -- The persisted mono body names its result and returns it.
  let some decl ← OCaml5.Lcnf.monoDecl? root
    | throwError "let-return control: {root} has no mono declaration"
  let binder ← match decl.value with
    | .code (.let d (.return y)) =>
      if d.fvarId == y then pure d.binderName
      else throwError "let-return control: {root} does not return its own binding"
    | _ => throwError "let-return control: {root} is not `let x := v; return x`"
  -- The route's form: the right side alone.
  let translated ← OCaml5.Lcnf.translateClosure #[root]
  unless translated.todos.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
    throwError "let-return control: {root} refused: {translated.todos}"
  let short ← match Conform.Effect4.LcnfMl.assemble translated.decls with
    | .ok program => pure program
    | .error why => throwError "let-return control: {why}"
  let name := OCaml5.Lcnf.globalName root
  let some (params, body) := short.binds[name]?
    | throwError "let-return control: {name} is not bound"
  if body matches .letIn .. then
    throwError "let-return control: the route kept the `let` of {root}"
  let same (a b : Target.TOutcome) : Bool :=
    match a, b with
    | .value v, .value w => v.beq w
    | .stuck r, .stuck s => r == s
    | .outOfFuel, .outOfFuel => true
    | .exn m, .exn n => m == n
    | _, _ => false
  let args := #[Target.TValue.int 3, Target.TValue.int 5]
  -- The binder under three names: the LCNF's own, the first parameter's (it hides the
  -- parameter) and one that nothing binds.
  for x in [OCaml5.Lcnf.localName binder, params.headD "x", "nothing_binds_this"] do
    let long : Target.Program :=
      { short with binds := short.binds.insert name (params, .letIn x body (.var x)) }
    -- one more unit of fuel for the form with the `let`, at every fuel
    for k in [0:16] do
      let before := Target.runT long (k + 1) name args
      let after := Target.runT short k name args
      unless same before after do
        throwError "let-return control: `{x}`, fuel {k}: {before.render} with the let, {after.render} without"
    -- both forms answer Lean's `3 * 5`, and the frontier is below the answer
    unless same (Target.runT long 16 name args) (.value (.int 15)) &&
        same (Target.runT short 15 name args) (.value (.int 15)) &&
        same (Target.runT short 0 name args) .outOfFuel do
      throwError "let-return control: `{x}`: the two forms do not answer 15"
    -- the red control: with one fuel for both forms some fuel tells them apart
    unless (List.range 16).any fun k =>
        !same (Target.runT long k name args) (Target.runT short k name args) do
      throwError "let-return control: `{x}`: the same-fuel comparison found no difference"
