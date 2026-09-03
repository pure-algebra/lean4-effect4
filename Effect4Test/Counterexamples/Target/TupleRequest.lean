/-
Counterexample `E4-TARGET-CE-026` (`test/counterexamples/REGISTER.md`), the
residue of `E4-TARGET-CE-022` the multi-argument repair left behind and the
survey found (finding H15).

`E4-TARGET-CE-022` was repaired by destructuring the request slot at the call:
`Lowering.callOf` selects `Lowering.tupleArgs` by `OpSpec.arity`, so
`jobs.ack(b10p3[0], b10p3[1])` calls a two-parameter row with two arguments.
But `tupleArgs` took a `TypeScript.Expr` and projected only the `.ident` case:

    def tupleArgs (request : Expr) (arity : Nat) : List Expr :=
      match request with
      | .ident name => tupleProjections name arity
      | _ => [request]

so any other request expression lowered an operation of *any* arity to a
one-argument call, with no refusal -- `E4-TARGET-CE-022`'s defect exactly,
behind a fallthrough. It was unreachable only because every caller happened to
pass `Slot.expr`, which was `.ident` for every slot; and `Slot.catchValue`
already spelled `a4.success`, one AST repair away from not being an `.ident`
at all.

The repair is not a refusal but an unrepresentable case: `tupleArgs` takes the
request slot's *spelling*, and `callOf` takes a `Slot`, so every request has a
path to project and there is no fallthrough to be wrong in. A projection is a
string operation -- `x[0]` is not a node of the pinned target fragment -- so a
signature that admits arbitrary expressions was claiming a totality it never
had.

No definition here traverses a rendered module.
-/

import Effect4.Target.TypeScript.Skeleton

namespace Effect4Test.Counterexamples.Target.TupleRequest

open Effect4.Target.EffectV4
open _root_.TypeScript (Expr)

/-! ## The attack, replayed

The retired clause, copied verbatim as data so the defect stays testable after
the repair. `witness` is a request expression that is not an identifier; the
retired reading answers one argument for it at every arity. -/

/-- The retired `tupleArgs`, kept only so the attack can still be run. -/
def retired (request : Expr) (arity : Nat) : List Expr :=
  match request with
  | .ident name => Lowering.tupleArgs name arity
  | _ => [request]

/-- A request expression that is not a bare identifier. Nothing on the path to
`callOf` built one, which is why the defect never fired. -/
def witness : Expr := .call (.ident "ticket") []

-- One argument for a three-parameter operation, silently.
#guard (retired witness 3).length = 1
#guard (retired witness 2).length = 1
-- And it is a fallthrough, not a refusal: the same arity over an identifier is
-- projected correctly, so nothing in the answer says the other case was wrong.
#guard (retired (.ident "b4p0") 3).length = 3

/-! ## The repair

`Lowering.tupleArgs` takes the slot's spelling, so the argument count is the
arity for every path and every arity above zero, and there is no other case.
-/

#guard (Lowering.tupleArgs "a4.success" 2) ==
  [Expr.ident "a4.success[0]", Expr.ident "a4.success[1]"]
#guard (Lowering.tupleArgs "a4.success" 3) ==
  [Expr.ident "a4.success[0]", Expr.ident "a4.success[1][0]",
   Expr.ident "a4.success[1][1]"]

/-- One argument per parameter, at every arity above zero and every spelling.
This is the statement the retired clause made false. -/
theorem tupleArgs_length (path : String) :
    ∀ arity, 0 < arity → (Lowering.tupleArgs path arity).length = arity := by
  intro arity
  induction arity generalizing path with
  | zero => intro h; exact absurd h (by decide)
  | succ n ih =>
      intro _
      match n with
      | 0 => rfl
      | m + 1 =>
          have : (Lowering.tupleArgs (path ++ "[1]") (m + 1)).length = m + 1 :=
            ih (path ++ "[1]") (by omega)
          simp [Lowering.tupleArgs, this]

/-! ## The bad case is unrepresentable

`Lowering.callOf` takes a `Slot`. A `TypeScript.Expr` request is not a term of
its domain any more, so the attacked call cannot be written at all -- the
receipt below names the exact rejected term. -/

-- The two signatures are the repair: a spelling in, and a slot in.
#check (@Lowering.tupleArgs : String → Nat → List Expr)
#check (@Lowering.callOf : ServiceRow → OpSpec → Slot → Expr)

/--
error: Application type mismatch
-/
#guard_msgs(drop info, error, substring := true) in
#check Lowering.callOf { name := "Jobs", ops := [] }
  (OpSpec.infallible "run" "readonly [JobQueue, number]" "number"
    [("conn", "JobQueue"), ("job", "number")])
  (Expr.call (Expr.ident "ticket") [])

-- The same call on the slot itself is what the lowering writes, and it carries
-- both arguments.
#guard Lowering.callOf { name := "Jobs", ops := [] }
    (OpSpec.infallible "run" "readonly [JobQueue, number]" "number"
      [("conn", "JobQueue"), ("job", "number")])
    (Slot.catchValue ⟨4⟩) ==
  Expr.call (.ident "jobs.run") [.ident "a4.success[0]", .ident "a4.success[1]"]

-- And a one-parameter row is still called on the slot, undestructured.
#guard Lowering.callOf { name := "Jobs", ops := [] }
    (OpSpec.unary "ack" .family "number" "void") (Slot.param ⟨10⟩ 3) ==
  Expr.call (.ident "jobs.ack") [.ident "b10p3"]

-- The one theorem here stays inside the ceiling.
#print axioms tupleArgs_length

end Effect4Test.Counterexamples.Target.TupleRequest
