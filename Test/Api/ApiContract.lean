import Effect4.Api
import TypeScript.Render

/-!
# Api contract — the application face, crossed the way a caller crosses it

`Effect4/Api.lean` is the one module an application imports. This battery uses nothing but
its interface: a program is typed, printed, compiled and run through `Effect4.Api`, and the
Schema syntax is rendered through the pinned package. Rendered bytes appear only inside
`#guard`s (a battery definition over a rendered `String` reaches `Classical.choice`).
-/

namespace Test.Api.ApiContract

open Effect4 Effect4.Api
open Effect4.Machine (Val)
open TypeScript (house0)
open TypeScript.Render (expr)

/-- `Effect.succeed(42)`. -/
def p42 : Program := .succeed (.lit (.nat 42))

/-- `Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(succ(a0)))`. -/
def pBind : Program :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))

/-- A program the printer refuses: an internal action of the machine. -/
def pInternal : Program := .withFiber (.setContext (.lit .unit))

/-! ## Typing and printing -/

#guard wellTyped p42
#guard wellTyped pBind
#guard (print p42).map (expr house0 0) = .ok "Effect.succeed(42)"
#guard (print pBind).map (expr house0 0)
  = .ok "Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(succ(a0)))"
#guard (printDecl "main" p42).isSome
#guard (printDecl "main" pInternal).isNone
#guard (print pInternal).isOk = false

/-! ## Running -/

#guard (run p42 100).outcome = Outcome.finished
#guard (run p42 100).exit = some (Exit.success (Val.nat 42))
#guard (run pBind 100).exit = some (Exit.success (Val.nat 2))
#guard (run p42 100).fiberCount = 1
#guard (runSync p42 100).2 = Exit.success (Val.nat 42)
-- No fuel: the run is a frontier, not a failure.
#guard (run p42 0).outcome = Outcome.frontier
-- An empty tape leaves the root unevaluated: a frontier with no exit.
#guard (replay p42 100 []).exit = none

/-! ## Schema, as syntax -/

#guard expr house0 0 (jsonExpr (.arr [])) = "[]"

/-! ## Axiom receipts -/

#print axioms Effect4.Api.typeOf
#print axioms Effect4.Api.print
#print axioms Effect4.Api.printDecl
#print axioms Effect4.Api.compile
#print axioms Effect4.Api.replay
#print axioms Effect4.Api.run
#print axioms Effect4.Api.runSync
#print axioms Effect4.Api.schemaDocument
#print axioms Effect4.Api.jsonExpr

end Test.Api.ApiContract
