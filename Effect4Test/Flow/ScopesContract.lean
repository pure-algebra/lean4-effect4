/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), the `Scopes` family.
Lowering lane L3.

Frozen: the sixteen operation rows of rc.112's `Scope` surface, the scope-store
projection the Lean face runs under, and the traced log of every program the
corpus carries — including the four `generated/traces/scope/*.tsv` was
generated from, whose rows are **unchanged**.

**The family is imported, not re-declared.** Before lane L3 the four-row
`Scopes` was declared inside `harness/trace/Generate.lean`, which is a script
and not a library, so nothing under `Effect4/` could state a theorem about it.
It is `Effect4/Runtime/ScopeFamily.lean` now — beside the frozen
`Effect4/Runtime/Scope.lean` state machine, which it uses unchanged and adds no
scope semantics to — and the script imports it.

The battery lives under `Effect4Test/Flow/` with the other traced families
(`Refs`, `Deferreds`, `Layers`, `Fibers`), which is where a *family* battery
goes; `Effect4Test/Runtime/Scope{,Machine,Restoration}Contract.lean` remain the
batteries of the `Scope` carrier itself.

Nothing here is a statement about the host: the same rows are compared with
rc.112 by `scripts/check-trace-host.sh`'s `scope` section through
`harness/trace/scope-tail.ts`, and that comparison is evidence, never a
theorem. Doc comments cannot precede `#guard`, so the receipts carry line
comments.
-/

import Effect4.Runtime.ScopeFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.ScopesContract

open Effect4.ScopeFamily

#check @Effect4.ScopeFamily.Scopes
#check (@Effect4.ScopeFamily.Scopes.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.ScopeFamily.scopesLive
#check @Effect4.ScopeFamily.scopeGoldenLog

/-! ## The rows

The first four keep their spelling, their order and their answers exactly, so
the four committed goldens are untouched; twelve follow. `make` stays nullary
and takes rc.112's own `"sequential"` default (`internal/effect.ts:3915`), and
`makeWith` is the same entry point with the optional argument supplied — one
rc.112 call, two rows, which is what keeps the goldens byte-identical. -/

#guard Scopes.rows.name = "Scopes"

#guard Scopes.rows.ops.map (·.name) =
  [ "make", "addFinalizer", "remove", "close", "makeWith", "fork", "addFinalizerExit"
  , "closeExit", "isClosed", "closedWith", "provide", "use", "forkIn", "runIn", "linked"
  , "exitFiber" ]

#guard (Scopes.rows.ops.take 4).map (·.name) = ["make", "addFinalizer", "remove", "close"]

#guard Scopes.rows.ops.map (·.params.length) =
  [0, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2]

#guard Scopes.rows.ops.map (fun row => (row.name, row.tsAnswer)) =
  [ ("make", "Scope.Closeable"), ("addFinalizer", "boolean"), ("remove", "void")
  , ("close", "ReadonlyArray<number>"), ("makeWith", "Scope.Closeable")
  , ("fork", "Scope.Closeable"), ("addFinalizerExit", "boolean")
  , ("closeExit", "ReadonlyArray<number>"), ("isClosed", "boolean")
  , ("closedWith", "Option.Option<boolean>"), ("provide", "boolean")
  , ("use", "ReadonlyArray<number>"), ("forkIn", "boolean"), ("runIn", "boolean")
  , ("linked", "ReadonlyArray<number>"), ("exitFiber", "void") ]

#guard Scopes.rows.ops.map (fun row => (row.name, row.tsParams.map Prod.snd)) =
  [ ("make", []), ("addFinalizer", ["Scope.Closeable", "number"])
  , ("remove", ["Scope.Closeable", "number"]), ("close", ["Scope.Closeable"])
  , ("makeWith", ["number"]), ("fork", ["Scope.Closeable", "number"])
  , ("addFinalizerExit", ["Scope.Closeable", "number"])
  , ("closeExit", ["Scope.Closeable", "Result.Result<number, number>"])
  , ("isClosed", ["Scope.Closeable"]), ("closedWith", ["Scope.Closeable"])
  , ("provide", ["Scope.Closeable", "number"]), ("use", ["Scope.Closeable", "number"])
  , ("forkIn", ["Scope.Closeable", "number"]), ("runIn", ["Scope.Closeable", "number"])
  , ("linked", ["Scope.Closeable"]), ("exitFiber", ["Scope.Closeable", "number"]) ]

-- No operation declares an error channel: a close that runs nothing answers the
-- empty order and a refused registration answers `false`, and neither is a
-- typed failure.
#guard Scopes.rows.ops.all (fun row => row.error.isNone)

-- `closeExit` is the one row that carries a `Result` on the wire, which is why
-- the emitted module imports it.
#guard Scopes.rows.usesResult

/-! ## The handler is a projection of the scope store

The clauses of `Effect4/Runtime/ScopeFamily.lean`, cited here as the shapes the
rows below rest on; their axiom receipts are in
`Effect4Test/Flow/ScopesAxiomReport.lean`. -/

#check @Effect4.ScopeFamily.fork_registers_the_linkage_names
#check @Effect4.ScopeFamily.close_cascades_to_the_child
#check @Effect4.ScopeFamily.close_writes_the_parent_state_first
#check @Effect4.ScopeFamily.closeOrder_is_the_keys
#check @Effect4.ScopeFamily.linkFiber_closed_scope
#check @Effect4.ScopeFamily.linkFiber_names

-- `SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`), closed: a fork
-- registers exactly two names under one shared key, minted from the linkage
-- counter that starts above the corpus's own keys.
#guard decide (
  ((forkedPair.scopeAt ⟨0⟩).map (fun scope => scope.closeOrder.map FinName.key))
    = Option.some [100])
#guard decide (
  ((forkedPair.scopeAt ⟨1⟩).map (fun scope => scope.closeOrder.map FinName.key))
    = Option.some [100])
#guard forkedPair.nextKey == 101

-- The parent's finalizer names the child scope and the child's names the
-- parent, which is what makes the cascade a consequence of the registration
-- and not of the close.
#guard decide (
  ((forkedPair.scopeAt ⟨0⟩).map Effect4.Scope.closeOrder)
    = Option.some [FinName.closeChildScope 100 1])
#guard decide (
  ((forkedPair.scopeAt ⟨1⟩).map Effect4.Scope.closeOrder)
    = Option.some [FinName.detachFromParent 100 0])

-- Closing the parent closes the child, and the second close of either runs
-- nothing.
#guard decide ((forkedPair.close ⟨0⟩ Effect4.Exit.void).scopes.map Effect4.Scope.isClosed
  = [true, true])
#guard decide ((forkedPair.close ⟨0⟩ Effect4.Exit.void).closeOrderOf ⟨0⟩ = [])

-- A linked fiber's key is minted from the same counter, and its observer
-- removes exactly that key when the fiber exits.
#guard decide (
  ((({} : ScopeStore).make Effect4.FinalizerStrategy.sequential).2.linkFiber ⟨0⟩ 7 true).1.linkedTo
      ⟨0⟩ = [7])
#guard decide (
  (((({} : ScopeStore).make Effect4.FinalizerStrategy.sequential).2.linkFiber ⟨0⟩ 7 true).1.dropLink
      ⟨0⟩ 7).closeOrderOf ⟨0⟩ = [])

/-! ## The corpus, and the rows each program renders

The wire rows are written inline in each receipt: a `def` rendering rows would
reach `Classical.choice` through the renderer and the axiom gate scans test
declarations too, while a `#guard` is a command, not a declaration. An unknown
name answers a row that no golden can match. -/

#guard scopePrograms.length == 8

#guard scopePrograms.map (·.name) ==
  [ "lifo", "addAfterClosed", "remove", "closeTwice", "forkLinkage", "provideThenUse"
  , "forkInClosed", "closeWithExit" ]

-- The four committed goldens come first, and their rows are byte-identical to
-- `generated/traces/scope/*.tsv`.
#guard (scopePrograms.take 4).map (·.name) == ["lifo", "addAfterClosed", "remove", "closeTwice"]

-- `scope/lifo.tsv`: three finalizers, closed once, keys back last registered
-- first (`internal/effect.ts:3815`).
#guard ((scopePrograms.find? (·.name == "lifo")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\taddFinalizer\t[0, 1]"
  , "answer\taddFinalizer\ttrue"
  , "op\taddFinalizer\t[0, 2]"
  , "answer\taddFinalizer\ttrue"
  , "op\taddFinalizer\t[0, 3]"
  , "answer\taddFinalizer\ttrue"
  , "op\tclose\t0"
  , "answer\tclose\t[3, [2, [1, []]]]"
  , "done\t{\"success\":[3, [2, [1, []]]]}" ]

-- `scope/addAfterClosed.tsv`: registering on a closed scope runs the finalizer
-- now and answers `false` (`internal/effect.ts:3846-3858`).
#guard ((scopePrograms.find? (·.name == "addAfterClosed")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\taddFinalizer\t[0, 1]"
  , "answer\taddFinalizer\ttrue"
  , "op\tclose\t0"
  , "answer\tclose\t[1, []]"
  , "op\taddFinalizer\t[0, 2]"
  , "answer\taddFinalizer\tfalse"
  , "done\t{\"success\":false}" ]

-- `scope/remove.tsv`: a removed key does not run. `remove` has no rc.112 entry
-- point — the package's exports map sends `./internal/*` to `null` — so the
-- golden pins the public mutable `Scope.state` shape and the model, not a call.
#guard ((scopePrograms.find? (·.name == "remove")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\taddFinalizer\t[0, 1]"
  , "answer\taddFinalizer\ttrue"
  , "op\taddFinalizer\t[0, 2]"
  , "answer\taddFinalizer\ttrue"
  , "op\tremove\t[0, 1]"
  , "answer\tremove\t[]"
  , "op\tclose\t0"
  , "answer\tclose\t[2, []]"
  , "done\t{\"success\":[2, []]}" ]

-- `scope/closeTwice.tsv`: the second close runs nothing and answers the empty
-- order.
#guard ((scopePrograms.find? (·.name == "closeTwice")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\taddFinalizer\t[0, 1]"
  , "answer\taddFinalizer\ttrue"
  , "op\taddFinalizer\t[0, 2]"
  , "answer\taddFinalizer\ttrue"
  , "op\tclose\t0"
  , "answer\tclose\t[2, [1, []]]"
  , "op\tclose\t0"
  , "answer\tclose\t[]"
  , "done\t{\"success\":[]}" ]

-- forkLinkage: the parent's close answers *its own* key — the linkage key 100,
-- above the corpus's own — and the cascade is visible through `isClosed` of the
-- child rather than through a longer answer.
#guard ((scopePrograms.find? (·.name == "forkLinkage")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\tfork\t[0, 0]"
  , "answer\tfork\t1"
  , "op\taddFinalizer\t[1, 1]"
  , "answer\taddFinalizer\ttrue"
  , "op\tclose\t0"
  , "answer\tclose\t[100, []]"
  , "op\tisClosed\t1"
  , "answer\tisClosed\ttrue"
  , "done\t{\"success\":true}" ]

-- provideThenUse: `Scope.provide` (`Scope.ts:310`) leaves the scope open and
-- `Scope.use` (`:616`) closes it on exit. Same registration, two lifetimes;
-- rc.112 v4 has **no `Scope.extend`**, so the row is named after the v4
-- spelling.
#guard ((scopePrograms.find? (·.name == "provideThenUse")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\tprovide\t[0, 1]"
  , "answer\tprovide\ttrue"
  , "op\tuse\t[0, 2]"
  , "answer\tuse\t[2, [1, []]]"
  , "done\t{\"success\":[2, [1, []]]}" ]

-- forkInClosed: `forkIn` and `Fiber.runIn` register the same name at different
-- guards (`internal/effect.ts:5368-5372` against `:5455`), and the exited
-- fiber's observer removes its own key, so only the second link is left.
#guard ((scopePrograms.find? (·.name == "forkInClosed")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\tforkIn\t[0, 1]"
  , "answer\tforkIn\ttrue"
  , "op\trunIn\t[0, 2]"
  , "answer\trunIn\ttrue"
  , "op\texitFiber\t[0, 1]"
  , "answer\texitFiber\t[]"
  , "op\tlinked\t0"
  , "answer\tlinked\t[2, []]"
  , "done\t{\"success\":[2, []]}" ]

-- closeWithExit: a close with a typed-failure exit runs the same order, and
-- `closedWith` reports that the closing exit failed.
#guard ((scopePrograms.find? (·.name == "closeWithExit")).map (fun entry => entry.log.map Effect4.Target.TypeScript.Trace.row)).getD ["unknown scope program"] ==
  [ "op\tmake\t[]"
  , "answer\tmake\t0"
  , "op\taddFinalizerExit\t[0, 1]"
  , "answer\taddFinalizerExit\ttrue"
  , "op\tcloseExit\t[0, [false, 4]]"
  , "answer\tcloseExit\t[1, []]"
  , "op\tclosedWith\t0"
  , "answer\tclosedWith\t{\"some\":false}"
  , "done\t{\"success\":{\"some\":false}}" ]

/-! ## What the family fixes about a handle, and what it refuses -/

-- A scope crosses the wire as a bare index and as nothing else.
#guard Scopes.encodeAnswer .make ⟨2⟩ = Effects.Trace.Val.nat 2
#guard Scopes.encodeParam .fork (⟨0⟩, 1) = Effects.Trace.Val.pair (.nat 0) (.nat 1)

-- The parallel strategy is recorded and not run: `makeWith 1` stores it, and
-- the close still answers the sequential order, because the parallel close
-- forks one daemon fiber per finalizer (`internal/effect.ts:3819-3826`) and
-- this lane has no fiber machine. census: scope.close-parallel
#guard decide ((({} : ScopeStore).make Effect4.FinalizerStrategy.parallel).2.scopes.map
  Effect4.Scope.strategy = [Effect4.FinalizerStrategy.parallel])

-- `addFinalizer` and `addFinalizerExit` are the same store operation here:
-- `scopeRun` is the void exit for every name, so what a finalizer *does* is
-- DB-02's supplied `run` argument and not canonical content. The two rows
-- differ on the host and not in this model.
#guard decide (
  (scopesLive Scopes.Name.addFinalizer (⟨0⟩, 1)
      (({} : ScopeStore).make Effect4.FinalizerStrategy.sequential).2).2.closeOrderOf ⟨0⟩
    = (scopesLive Scopes.Name.addFinalizerExit (⟨0⟩, 1)
      (({} : ScopeStore).make Effect4.FinalizerStrategy.sequential).2).2.closeOrderOf ⟨0⟩)

-- Every program of the corpus ends in a success: no operation of this family
-- has an error channel and no program of it is a frontier.
#guard scopePrograms.all (fun entry => entry.log.all (fun event =>
  match event with
  | .done (.success _) => true
  | .done _ => false
  | _ => true))

-- Every log agrees with itself under every registered mask; agreement is a
-- projection equality and never more.
#guard scopePrograms.all (fun entry =>
  Effect4.Trace.maskTable.all (fun mask => Effect4.Trace.agree mask.2 entry.log entry.log))

end Effect4Test.Flow.ScopesContract
