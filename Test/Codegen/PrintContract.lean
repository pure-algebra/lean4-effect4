import Effect4.Codegen.Print
import Effect4.Program.Native
import TypeScript.Render

/-!
# Print contract — the §5.1 spelling table, pinned byte for byte

Plan: `docs/research/2026-09-04-ast-relation-plan.md` §5.1. One `#guard` per constructor of
`Effect4.Program.Eff` (the 28 rows of `arms`), per statement form of a generator body, per
`awaitFiber` mode, per fork shape (both `daemon` values against all three `MaskMode`s), per
refusal, and two for `printDecl`. Every pin is the rendered bytes of
`TypeScript.Render.expr TypeScript.house0 0`, so the battery fails on a spelling change and
on a layout change alike.

Everything is inlined inside the `#guard`s on purpose: a battery definition that folds over
a rendered `String` reaches `Classical.choice` through Lean's UTF-8 decoding proof and would
put this module outside the tree's axiom ceiling. The definitions below are the
alphabet only — rows, atoms and a scope key — and hold string *literals* without traversing
one. `#guard` itself leaves no declaration for the gate to audit.

The alphabet is `Fin 3`: a call row on a handle request (`Ref.get`), a nullary value row
(`cell.count`, the service route's shape), and an async row (`Deferred.await`), which is
the original row sample. The tuple-call tests below cover its separate argument-list
convention, both native rows and a fixture with trailing names.
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
           "Ref.ts:200", [], .deferred⟩
  | 1 => ⟨"count", "cell.count", .value, [], .sync, .unit, .nat, .never, [], "Ref.ts:210", [], .deferred⟩
  | 2 => ⟨"await", "Deferred.await", .call, [], .async,
           .handle "Deferred.Deferred<number, never>", .nat, .never, [], "Deferred.ts:120", [], .deferred⟩

/-- A read-modify-write row: its pure function prints after the request. -/
def updateRow : Row :=
  ⟨"update", "Ref.update", .call, ["incr"], .sync, .handle "Ref.Ref<number>", .unit, .never, [],
    "Ref.ts:1273-1276", [], .deferred⟩

#guard (printRow updateRow (.var 0)).map (expr house0 0) = .ok "Ref.update(a0, incr)"

/-- A tuple-call fixture with two ordered trailing names. Native tuple calls currently
have no trailing names; this fixture checks the generic row convention. -/
def tupleRow : Row :=
  ⟨"tuple", "Fixture.tuple", .tupleCall, ["first", "second"], .sync,
    .prod .nat .nat, .nat, .never, [], "§14 tuple-call fixture", [], .deferred⟩

/-- A row that declares explicit type arguments: the export's own parameters have defaults,
so the call must carry them or the host types the answer at those defaults
(`E4-CHECK-CE-013`). -/
def genericRow : Row :=
  ⟨"make", "Deferred.make", .call, [], .sync, .unit,
    .handle "Deferred.Deferred<number, number>", .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:171",
    ["number", "number"], .deferred⟩

#guard (printRow genericRow (.lit .unit)).map (expr house0 0) = .ok "Deferred.make<number, number>()"

#guard match printRow genericRow (.lit .unit) with
  | .ok expression => expression ==
      .call (.generic (.ident "Deferred.make") [.name ["number"] [], .name ["number"] []]) []
  | .error _ => false

#guard match printRow { genericRow with typeArgs := ["number); injected("] } (.lit .unit) with
  | .error (.typeSpelling spelling) => spelling == genericRow.spelling
  | _ => false

-- A saved tuple is read once per component; a `pair` prints its components
-- (source-repairs §18).
#guard (printRow tupleRow (.var 0)).map (expr house0 0) =
  .ok "Fixture.tuple(fst(a0), snd(a0), first, second)"

#guard (printRow tupleRow
    (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil)))).map (expr house0 0) =
  .ok "Fixture.tuple(2, 7, first, second)"

-- A request that is neither a pair nor a variable is outside the readable image and
-- still prints, once per component.
#guard (printRow tupleRow (.app "requestOnce" .nil)).map (expr house0 0) =
  .ok "Fixture.tuple(fst(requestOnce()), snd(requestOnce()), first, second)"

-- A product request does not change the calling convention of an ordinary call row.
#guard (printRow { tupleRow with shape := .call }
    (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil)))).map (expr house0 0) =
  .ok "Fixture.tuple(pair(2, 7), first, second)"

-- All five corrected native exports receive the pair's components as their two
-- arguments, the pinned two-argument signatures the host infers its types from.
#guard ([NativeOp.refSet, .refGetAndSet, .refSetAndGet, .deferredSucceed, .deferredFail].map
    fun op => (printRow op.row
      (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))).map (expr house0 0)) =
  [ .ok "Ref.set(a0, 7)"
  , .ok "Ref.getAndSet(a0, 7)"
  , .ok "Ref.setAndGet(a0, 7)"
  , .ok "Deferred.succeed(a0, 7)"
  , .ok "Deferred.fail(a0, 7)" ]

-- The tuple may be saved in a variable; its components are read from the binder.
#guard (print nativeSignature 0
    (.bind (.perform .deferredMake (.lit .unit))
      (.bind (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
        (.perform .deferredSucceed (.var 1))))).map (expr house0 0) =
  .ok ("Effect.flatMap(Deferred.make<number, number>(), (a0) => " ++
    "Effect.flatMap(Effect.succeed(pair(a0, 7)), (a1) => Deferred.succeed(fst(a1), snd(a1))))")

/-- The battery's signature. `atomOf` declares one pure atom, `succ : number -> number`;
the printer never consults it (an atom prints as its own name) but `Signature` carries it
for `typeOf`. -/
def sig : Signature (Fin 3) :=
  { rowOf := rowOf
  , atomOf := fun atom args => if atom = "succ" ∧ args = [Ty.nat] then some Ty.nat else none
  , scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => none }

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

-- a failure prints as `Effect.fail`, never as a bare value (DI-72; `yieldError` printed the
-- same image until it retired into `fail`)
#guard (print sig 1 (.fail (.var 0))).map (expr house0 0) = .ok "Effect.fail(a0)"
#guard (print sig 0 (.fail (.lit (.nat 19)))).map (expr house0 0) = .ok "Effect.fail(19)"

#guard (print sig 1 (.sync (.app "succ" (.cons (.var 0) .nil)))).map (expr house0 0)
  = .ok "Effect.sync(() => succ(a0))"

#guard (print sig 0 (.suspend (.succeed (.lit .unit)))).map (expr house0 0)
  = .ok "Effect.suspend(() => Effect.succeed(undefined))"

#guard (print sig 1 (.perform 0 (.var 0))).map (expr house0 0) = .ok "Ref.get(a0)"

#guard (print sig 0 (.perform 1 (.lit .unit))).map (expr house0 0) = .ok "cell.count"

#guard (print sig 1 (.perform 2 (.var 0))).map (expr house0 0) = .ok "Deferred.await(a0)"

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

#guard (print sig 0 (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1)))
      (.succeed (.lit .unit)))).map (expr house0 0)
  = .ok "Effect.suspend(() => true ? Effect.succeed(1) : Effect.succeed(undefined))"

#guard (print sig 0 (.iterate .nat (.lit (.nat 0)) (.var 0) (.app "succ" (.cons (.var 1) .nil))
      (.var 0) (.succeed (.var 0)))).map (expr house0 0)
  = .ok ("Effect.suspend(() => {\n  let a0: number = 0\n  return Effect.map(Effect.whileLoop({\n"
      ++ "    while: () => a0,\n    body: () => Effect.succeed(a0),\n"
      ++ "    step: (a1) => {\n      a0 = succ(a1)\n    },\n  }), () => a0)\n})")

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
  = .ok "Effect.withFiber(() => {\n  Fiber.runIn(a0, a1)\n  return Effect.void\n})"

-- Both source terms occur once, inside the callback that performs the scope link.
#guard (print sig 0 (.withFiber (.runIn (.app "targetOnce" .nil)
    (.app "scopeOnce" .nil)))).map (expr house0 0) =
  .ok "Effect.withFiber(() => {\n  Fiber.runIn(targetOnce(), scopeOnce())\n  return Effect.void\n})"

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

The five internal actions have no public rc.112 export with the
same frame shape. Each refusal names itself, so a refusal is data rather than a gap. -/

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

#guard (printDecl "program" ⟨.nat, .never, Requirement.empty⟩
      (.call (.ident "Effect.succeed") [.int 1])).map (constDecl house0)
  = .ok "export const program: Effect.Effect<number, never> = Effect.succeed(1)\n"

#guard (printDecl "program" ⟨.nat, .never, Requirement.single ⟨⟨1⟩, ⟨2⟩⟩⟩
      (.call (.ident "Effect.succeed") [.int 1])).map (constDecl house0)
  = .ok "export const program = Effect.succeed(1)\n"

-- The raw declaration printer now exposes its type domain. A closed body
-- alone cannot make an arbitrary legacy handle spelling representable.
#guard match printDecl "program"
    ⟨.handle "not a type !", .never, Requirement.empty⟩
    (.call (.ident "Effect.succeed") [.int 1]) with
  | .error (.typeSpelling spelling) => spelling == "not a type !"
  | _ => false
#guard declarationTypeRepresentable
    ⟨.handle "not a type !", .never, Requirement.empty⟩ = false

/-! ## `printEntry`: an export name the reader can tell from everything it decodes

`E4-TARGET-NAME-CE-001`. The declaration printer used to accept any export name, so a block
could export `a0` (a printed binder the reader recovers by comparison), `Effect.succeed` (a
reserved head) or `L_0` (a layer reference name), and be misread. The entry printer now
refuses all three by name, before it looks at the row table. -/

#guard match printEntry [] nativeSignature "a0" ⟨.nat, .never, Requirement.empty⟩
    (.succeed (.lit (.nat 1))) with
  | .error (.unsafeName spelling) => spelling == "a0"
  | _ => false

#guard match printEntry [] nativeSignature "Effect.succeed" ⟨.nat, .never, Requirement.empty⟩
    (.succeed (.lit (.nat 1))) with
  | .error (.unsafeName spelling) => spelling == "Effect.succeed"
  | _ => false

#guard match printEntry [] nativeSignature "L_0" ⟨.nat, .never, Requirement.empty⟩
    (.succeed (.lit (.nat 1))) with
  | .error (.unsafeName spelling) => spelling == "L_0"
  | _ => false

#guard exportNameSafe "main" = true
#guard exportNameSafe "a0" = false
#guard exportNameSafe "Effect.succeed" = false
#guard exportNameSafe "L_0" = false
#guard exportNameSafe "export" = false
#guard (printEntry [] nativeSignature "main" ⟨.nat, .never, Requirement.empty⟩
    (.succeed (.lit (.nat 1)))).isOk

#print axioms Effect4.Program.exportNameSafe
#print axioms Effect4.Program.declarationType
#print axioms Effect4.Program.printDecl_fields
#print axioms Effect4.Program.printEntry_ok

end Test.Syntax.PrintContract
