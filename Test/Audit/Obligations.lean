import Effect4.Laws.Auto.Obligations

/-! Controls of the law graph's entry point for planned goals (`Effect4.Laws.Auto.Obligations`,
decisions row 203): a goal declared through the law import, with a docstring, binders and a
universe; a theorem that rests on it; and the standing each one reads back. -/
namespace Test.Obligations
open Lean Elab Command ProofGraph

/-- A planned goal with binders. -/
proof_goal pending (n : Nat) : n + 0 = n

/-- A universe-polymorphic planned goal. -/
proof_goal polymorphic.{u} (α : Sort u) (x : α) : x = x

/-- A theorem whose proof uses the goal: proved modulo `pending`, never proved. -/
theorem resting : 3 + 0 = 3 := pending 3

run_cmd liftTermElabM do
  let env ← getEnv
  for (name, expected) in [(``pending, Standing.goal), (``polymorphic, .goal),
      (``resting, .modulo #[``pending])] do
    let (reached, _) := (standing env name).run {}
    let some (s, axioms) := reached | throwError "{name}: no standing"
    unless s == expected do throwError "{name}: standing {s.word}"
    unless axioms.isEmpty do throwError "{name}: real axioms {axioms}"
  let some (.thmInfo info) := env.find? ``polymorphic | throwError "polymorphic is not a theorem"
  unless info.levelParams == [`u] do throwError "polymorphic lost its universe"
  unless (← findDocString? env ``pending) == some "A planned goal with binders. " do
    throwError "pending lost its docstring"

end Test.Obligations
