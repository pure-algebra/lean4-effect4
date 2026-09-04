import Effect4.Codegen.Print
import TypeScript.Render

/-!
# Print contract — the §5.1 spelling table, pinned byte for byte

Plan: `docs/research/2026-09-04-ast-relation-plan.md` §5.1. One `#guard` per constructor of
`Effect4.Program.Eff` (the 24 rows of `arms`), per statement form of a generator body, per
`awaitFiber` mode, per fork shape (both `daemon` values against all three `MaskMode`s), per
refusal, and two for `printDecl`. Every pin is the rendered bytes of
`TypeScript.Render.expr TypeScript.house0 0`, so the battery fails on a spelling change and
on a layout change alike.

Everything is inlined inside the `#guard`s on purpose: a battery definition that folds over
a rendered `String` reaches `Classical.choice` through Lean's UTF-8 decoding proof and would
put this module outside the tree's axiom ceiling. The three definitions below are the
alphabet only — rows, atoms and a scope key — and hold string *literals* without traversing
one. `#guard` itself leaves no declaration for the gate to audit.

The alphabet is `Fin 3`: a call row on a handle request (`Ref.get`), a nullary value row
(`cell.count`, the service route's shape), and an async row (`Deferred.await`), which is
exactly the three ways `printRow` can answer.
-/

namespace Test.Syntax.PrintContract

open Effect4.Program
open Effect4.Machine.Env (Requirement)
open TypeScript (house0)
open TypeScript.Render (expr constDecl)

/-- The three rows of the battery's perform alphabet: a call row whose request is a handle,
a value row whose request is `unit`, and an async row. -/
def rowOf : Fin 3 → Row
  | 0 => ⟨"get", "Ref.get", .call, [], .sync, .handle "Ref.Ref<number>", .nat, .never, [],
           "Ref.ts:200"⟩
  | 1 => ⟨"count", "cell.count", .value, [], .sync, .unit, .nat, .never, [], "Ref.ts:210"⟩
  | 2 => ⟨"await", "Deferred.await", .call, [], .async,
           .handle "Deferred.Deferred<number, never>", .nat, .never, [], "Deferred.ts:120"⟩

/-- A read-modify-write row: its pure function prints after the request. -/
def updateRow : Row :=
  ⟨"update", "Ref.update", .call, ["incr"], .sync, .handle "Ref.Ref<number>", .unit, .never, [],
    "Ref.ts:1273-1276"⟩

#guard expr house0 0 (printRow updateRow (.var 0)) = "Ref.update(a0, incr)"

/-- The battery's signature. `atomOf` declares one pure atom, `succ : number -> number`;
the printer never consults it (an atom prints as its own name) but `Signature` carries it
for `typeOf`. -/
def sig : Signature (Fin 3) :=
  { rowOf := rowOf
  , atomOf := fun atom args => if atom = "succ" ∧ args = [Ty.nat] then some Ty.nat else none
  , scopeKey := ⟨⟨0⟩, ⟨0⟩⟩ }

/-! ## Exits, thunks and rows -/

#guard (print sig 0 (.succeed (.lit (.nat 1)))).map (expr house0 0)
  = .ok "Effect.succeed(1)"

#guard (print sig 0 (.fail (.lit (.str "boom")))).map (expr house0 0)
  = .ok "Effect.fail(\"boom\")"

#guard (print sig 0 (.failCause (.fail (.lit (.str "boom"))))).map (expr house0 0)
  = .ok "Effect.failCause(Cause.fail(\"boom\"))"

#guard (print sig 0 (.failCause (.die (.lit (.str "bug"))))).map (expr house0 0)
  = .ok "Effect.failCause(Cause.die(\"bug\"))"

#guard (print sig 0 (.failCause (.interrupt none))).map (expr house0 0)
  = .ok "Effect.failCause(Cause.interrupt())"

#guard (print sig 0 (.failCause (.interrupt (some (.lit (.nat 7)))))).map (expr house0 0)
  = .ok "Effect.failCause(Cause.interrupt(7))"

#guard (print sig 0 (.failCause (.both (.fail (.lit (.str "l"))) (.interrupt none)))).map
    (expr house0 0)
  = .ok "Effect.failCause(Cause.combine(Cause.fail(\"l\"), Cause.interrupt()))"

#guard (print sig 1 (.yieldError (.var 0))).map (expr house0 0) = .ok "a0"

#guard (print sig 1 (.sync (.app "succ" (.cons (.var 0) .nil)))).map (expr house0 0)
  = .ok "Effect.sync(() => succ(a0))"

#guard (print sig 0 (.suspend (.succeed (.lit .unit)))).map (expr house0 0)
  = .ok "Effect.suspend(() => Effect.succeed(undefined))"

#guard (print sig 1 (.perform 0 (.var 0))).map (expr house0 0) = .ok "Ref.get(a0)"

#guard (print sig 0 (.perform 1 (.lit .unit))).map (expr house0 0) = .ok "cell.count"

#guard (print sig 1 (.callback 2 (.var 0))).map (expr house0 0) = .ok "Deferred.await(a0)"

/-! ## Sequencing: the two frame shapes of §2.1 -/

#guard (print sig 0 (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0)))).map (expr house0 0)
  = .ok "Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(a0))"

#guard (print sig 0 (.gen (.cons (.bindYield (.perform 0 (.var 0)))
      (.cons (.ret (.var 0)) .nil)))).map (expr house0 0)
  = .ok "Effect.gen(function* () {\n  const a0 = yield* Ref.get(a0)\n  return a0\n})"

#guard (print sig 0 (.gen (.cons (.yieldDiscard (.succeed (.lit (.nat 1))))
      (.cons (.ret (.lit .unit)) .nil)))).map (expr house0 0)
  = .ok "Effect.gen(function* () {\n  yield* Effect.succeed(1)\n  return undefined\n})"

#guard (print sig 0 (.gen (.cons (.ifElse (.lit (.bool true))
      (.cons (.bindYield (.succeed (.lit (.nat 1)))) .nil)
      (.cons (.yieldDiscard (.succeed (.lit .unit))) .nil))
      (.cons (.ret (.lit (.nat 0))) .nil)))).map (expr house0 0)
  = .ok ("Effect.gen(function* () {\n  if (true) {\n    const a0 = yield* Effect.succeed(1)\n"
      ++ "  } else {\n    yield* Effect.succeed(undefined)\n  }\n  return 0\n})")

#guard (print sig 0 (.gen (.cons (.whileTrue
      (.cons (.yieldDiscard (.succeed (.lit (.nat 1)))) (.cons .breakLoop .nil)))
      (.cons (.ret (.lit .unit)) .nil)))).map (expr house0 0)
  = .ok ("Effect.gen(function* () {\n  while (true) {\n    yield* Effect.succeed(1)\n"
      ++ "    break\n  }\n  return undefined\n})")

#guard (print sig 0 (.gen (.cons .breakLoop .nil))).map (expr house0 0)
  = .ok "Effect.gen(function* () {\n  break\n})"

#guard (print sig 0 (.gen .nil)).map (expr house0 0)
  = .ok "Effect.gen(function* () {\n})"

/-! ## Failure, exit and the masks -/

#guard (print sig 0 (.catchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0)))).map
    (expr house0 0)
  = .ok "Effect.catchCause(Effect.succeed(1), (a0) => Effect.succeed(a0))"

#guard (print sig 0 (.matchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0))
      (.failCause (.fail (.var 0))))).map (expr house0 0)
  = .ok ("Effect.matchCauseEffect(Effect.succeed(1), { onFailure: (a0) => "
      ++ "Effect.failCause(Cause.fail(a0)), onSuccess: (a0) => Effect.succeed(a0) })")

#guard (print sig 0 (.onExit (.succeed (.lit (.nat 1))) (.succeed (.var 0)))).map
    (expr house0 0)
  = .ok "Effect.onExit(Effect.succeed(1), (a0) => Effect.succeed(a0))"

#guard (print sig 0 (.exit (.succeed (.lit (.nat 1))))).map (expr house0 0)
  = .ok "Effect.exit(Effect.succeed(1))"

#guard (print sig 0 (.uninterruptible (.succeed (.lit (.nat 1))))).map (expr house0 0)
  = .ok "Effect.uninterruptible(Effect.succeed(1))"

#guard (print sig 0 (.interruptible (.succeed (.lit (.nat 1))))).map (expr house0 0)
  = .ok "Effect.interruptible(Effect.succeed(1))"

/-! ## Control by value, scheduling and parking -/

#guard (print sig 0 (.branch (.lit (.bool true)) (.succeed (.lit (.nat 1)))
      (.succeed (.lit .unit)))).map (expr house0 0)
  = .ok "Effect.suspend(() => true ? Effect.succeed(1) : Effect.succeed(undefined))"

#guard (print sig 0 (.whileLoop (.lit (.nat 0)) (.var 0) (.app "succ" (.cons (.var 1) .nil))
      (.succeed (.var 0)))).map (expr house0 0)
  = .ok ("Effect.suspend(() => {\n  let a0 = 0\n  return Effect.whileLoop({\n"
      ++ "    while: () => a0,\n    body: () => Effect.succeed(a0),\n"
      ++ "    step: (a1) => {\n      a0 = succ(a1)\n    },\n  })\n})")

#guard (print sig 0 (.yieldNow 2)).map (expr house0 0) = .ok "Effect.yieldNowWith(2)"

#guard (print sig 1 (.awaitFiber (.var 0) .joinEffect)).map (expr house0 0)
  = .ok "Fiber.join(a0)"

#guard (print sig 1 (.awaitFiber (.var 0) .awaitValue)).map (expr house0 0)
  = .ok "Fiber.await(a0)"

/-! ## Scopes -/

#guard (print sig 0 (.scoped (.succeed (.lit (.nat 1))))).map (expr house0 0)
  = .ok "Effect.scoped(Effect.succeed(1))"

#guard (print sig 0 (.acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.var 1)))).map
    (expr house0 0)
  = .ok "Effect.acquireRelease(Effect.succeed(1), (a0, a1) => Effect.succeed(a1))"

#guard (print sig 2 (.withFiber (.closeScope (.var 0) (.var 1)))).map (expr house0 0)
  = .ok "Scope.close(a0, a1)"

/-! ## `withFiber`: the fork family across both `daemon` values and all three `MaskMode`s -/

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨true, false, .interruptible⟩))).map (expr house0 0)
  = .ok ("Effect.forkChild(Effect.succeed(1), { startImmediately: true, "
      ++ "uninterruptible: false })")

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨true, false, .uninterruptible⟩))).map (expr house0 0)
  = .ok ("Effect.forkChild(Effect.succeed(1), { startImmediately: true, "
      ++ "uninterruptible: true })")

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨false, false, .inherit⟩))).map (expr house0 0)
  = .ok ("Effect.forkChild(Effect.succeed(1), { startImmediately: false, "
      ++ "uninterruptible: \"inherit\" })")

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨true, true, .interruptible⟩))).map (expr house0 0)
  = .ok ("Effect.forkDetach(Effect.succeed(1), { startImmediately: true, "
      ++ "uninterruptible: false })")

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨false, true, .uninterruptible⟩))).map (expr house0 0)
  = .ok ("Effect.forkDetach(Effect.succeed(1), { startImmediately: false, "
      ++ "uninterruptible: true })")

#guard (print sig 0 (.withFiber (.fork (.succeed (.lit (.nat 1)))
      ⟨true, true, .inherit⟩))).map (expr house0 0)
  = .ok ("Effect.forkDetach(Effect.succeed(1), { startImmediately: true, "
      ++ "uninterruptible: \"inherit\" })")

#guard (print sig 1 (.withFiber (.forkIn (.succeed (.lit (.nat 1)))
      ⟨true, false, .inherit⟩ (.var 0)))).map (expr house0 0)
  = .ok ("Effect.forkIn(Effect.succeed(1), a0, { startImmediately: true, "
      ++ "uninterruptible: \"inherit\" })")

#guard (print sig 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1)))
      ⟨true, false, .interruptible⟩))).map (expr house0 0)
  = .ok ("Effect.forkScoped(Effect.succeed(1), { startImmediately: true, "
      ++ "uninterruptible: false })")

/-! ## `withFiber`: the handle actions -/

#guard (print sig 2 (.withFiber (.runIn (.var 0) (.var 1)))).map (expr house0 0)
  = .ok "Fiber.runIn(a0, a1)"

#guard (print sig 1 (.withFiber (.interrupt (.var 0)))).map (expr house0 0)
  = .ok "Fiber.interrupt(a0)"

#guard (print sig 1 (.withFiber (.interruptAll (.var 0) none))).map (expr house0 0)
  = .ok "Fiber.interruptAll(a0)"

#guard (print sig 2 (.withFiber (.interruptAll (.var 0) (some (.var 1))))).map (expr house0 0)
  = .ok "Fiber.interruptAllAs(a0, a1)"

#guard (print sig 1 (.withFiber (.awaitAll (.var 0)))).map (expr house0 0)
  = .ok "Fiber.awaitAll(a0)"

#guard (print sig 0 (.withFiber (.raceAll (.cons (.succeed (.lit (.nat 1)))
      (.cons (.succeed (.lit .unit)) .nil))))).map (expr house0 0)
  = .ok "Effect.raceAll([Effect.succeed(1), Effect.succeed(undefined)])"

#guard (print sig 0 (.withFiber .getContext)).map (expr house0 0) = .ok "Effect.context()"

#guard (print sig 0 (.withFiber .getId)).map (expr house0 0) = .ok "Effect.fiberId"

/-! ## The refused row of §5.1

`choose` is flows-only (D2); the five internal actions have no public rc.112 export with the
same frame shape. Each refusal names itself, so a refusal is data rather than a gap. -/

#guard (print sig 0 (.choose 0 (.succeed (.lit (.nat 1))) (.succeed (.lit .unit)))).map
    (expr house0 0)
  = .error (.choose 0)

#guard (print sig 1 (.withFiber (.interruptScoped (.var 0)))).map (expr house0 0)
  = .error (.internalAction "interruptScoped")

#guard (print sig 1 (.withFiber (.awaitAllFailFast (.var 0)))).map (expr house0 0)
  = .error (.internalAction "awaitAllFailFast")

#guard (print sig 0 (.withFiber .snapshotChildren)).map (expr house0 0)
  = .error (.internalAction "snapshotChildren")

#guard (print sig 1 (.withFiber (.awaitNewChildren (.var 0)))).map (expr house0 0)
  = .error (.internalAction "awaitNewChildren")

#guard (print sig 1 (.withFiber (.setContext (.var 0)))).map (expr house0 0)
  = .error (.internalAction "setContext")

/-! ## `printDecl`: the two-parameter type exactly when the requirement is empty -/

#guard constDecl house0
    (printDecl "program" ⟨.nat, .never, Requirement.empty⟩
      (.call (.ident "Effect.succeed") [.int 1]))
  = "export const program: Effect.Effect<number, never> = Effect.succeed(1)\n"

#guard constDecl house0
    (printDecl "program" ⟨.nat, .never, Requirement.single ⟨⟨1⟩, ⟨2⟩⟩⟩
      (.call (.ident "Effect.succeed") [.int 1]))
  = "export const program = Effect.succeed(1)\n"

end Test.Syntax.PrintContract
