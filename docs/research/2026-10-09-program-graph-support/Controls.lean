import Tools.View.Run

/-! Finite controls for the D1-D3 graph reading, refreshed at 78f7bcbe.
No new theorem or production representation. The existing authoring admission and
Run.runPure are the observations, with fixed budgets and no host rows.
-/

open Effect4 Effect4.Program Effect4.Machine

namespace ProgramGraphSupport

structure Case where
  name : String
  program : NativeEff
  refs : List Nat
  exit : ExitV
  forks : Nat := 0

def value (n : Nat) : NativeEff := .succeed (.lit (.nat n))
def failure (n : Nat) : NativeEff := .fail (.lit (.nat n))
def mark (n : Nat) (next : NativeEff) : NativeEff :=
  .bind (.perform .refMake (.lit (.nat n))) next

def opts (immediate : Bool) : Supervision.ForkOptions :=
  { startImmediately := immediate, daemon := false, maskMode := .inherit }

def forkOrder (immediate : Bool) : NativeEff :=
  .bind (.withFiber (.fork (mark 9 (value 42)) (opts immediate)))
    (.bind (.perform .refMake (.lit (.nat 1))) (.awaitFiber (.var 0) .joinEffect))

def repeatedFork : NativeEff :=
  .iterate none (.lit (.nat 0))
    (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 2)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.var 0)
    (.withFiber (.fork (.succeed (.lit .unit)) (opts true)))

def scopedRelease : NativeEff :=
  .scoped (.bind (.acquireRelease (mark 10 (value 1)) (mark 30 (value 3)))
    (mark 20 (value 2)))

def detachedWait : NativeEff :=
  .bind (.perform (.deferredMakeOf .nat .nat) (.lit .unit))
    (.bind (.withFiber (.fork (.perform .deferredAwait (.var 0))
      { startImmediately := true, daemon := true, maskMode := .inherit }))
      (mark 20 (value 2)))

def cases : List Case :=
  [⟨"release-runs-at-scope-close", scopedRelease, [10, 20, 30], .success (.nat 2), 0⟩,
   ⟨"fork-has-no-implicit-join", detachedWait, [20], .success (.nat 2), 1⟩,
   ⟨"catch-success-bypasses-handler", .catchCause (mark 10 (value 1)) (mark 20 (value 2)),
      [10], .success (.nat 1), 0⟩,
   ⟨"catch-failure-runs-body-then-handler", .catchCause (mark 10 (failure 7)) (mark 20 (value 2)),
      [10, 20], .success (.nat 2), 0⟩,
   ⟨"catch-handler-failure-escapes", .catchCause (mark 10 (failure 7)) (mark 20 (failure 9)),
      [10, 20], .failure (.fail (.tag 9)), 0⟩,
   ⟨"match-success-runs-body-then-value-arm",
      .matchCause (mark 10 (value 1)) (mark 20 (value 2)) (mark 30 (value 3)),
      [10, 20], .success (.nat 2), 0⟩,
   ⟨"match-failure-runs-body-then-cause-arm",
      .matchCause (mark 10 (failure 7)) (mark 20 (value 2)) (mark 30 (value 3)),
      [10, 30], .success (.nat 3), 0⟩,
   ⟨"match-value-arm-failure-does-not-run-cause-arm",
      .matchCause (mark 10 (value 1)) (mark 20 (failure 9)) (mark 30 (value 3)),
      [10, 20], .failure (.fail (.tag 9)), 0⟩,
   ⟨"select-true-runs-one-arm",
      .select (.lit (.bool true)) .bool (mark 20 (value 2)) (mark 30 (value 3)),
      [20], .success (.nat 2), 0⟩,
   ⟨"select-false-runs-other-arm",
      .select (.lit (.bool false)) .bool (mark 20 (value 2)) (mark 30 (value 3)),
      [30], .success (.nat 3), 0⟩,
   ⟨"on-exit-runs-body-then-finalizer", .onExit (mark 10 (value 1)) (mark 40 (value 4)),
      [10, 40], .success (.nat 1), 0⟩,
   ⟨"fork-immediate-order", forkOrder true, [9, 1], .success (.nat 42), 1⟩,
   ⟨"fork-deferred-order", forkOrder false, [1, 9], .success (.nat 42), 1⟩,
   ⟨"race-success-does-not-launch-later-entrant",
      .withFiber (.raceAll (.cons (mark 10 (value 1)) (.cons (mark 20 (value 2)) .nil))),
      [10], .success (.nat 1), 1⟩,
   ⟨"race-failure-allows-next-entrant",
      .withFiber (.raceAll (.cons (mark 10 (failure 7)) (.cons (mark 20 (value 2)) .nil))),
      [10, 20], .success (.nat 2), 2⟩,
   ⟨"one-fork-site-two-runtime-fibers", repeatedFork, [], .success (.nat 2), 2⟩]

def exitLabel : Option ExitV → String
  | some (.success (.nat n)) => s!"success {n}"
  | some (.failure (.fail (.tag n))) => s!"failure {n}"
  | some _ => "other exit"
  | none => "live"

def check (c : Case) : IO Lean.Json := do
  let built ← match Api.Author.Internal.finishBuild c.program [] [] with
    | .ok b => pure b
    | .error _ => throw (IO.userError s!"{c.name}: admission refused")
  let run := Run.runPure built "graph-support" { compileFuel := 400, fuel := 400 }
  if run.machine.state.refs != c.refs.map Val.nat then
    throw (IO.userError s!"{c.name}: allocation order {reprStr run.machine.state.refs}")
  if run.exit != some c.exit then
    throw (IO.userError s!"{c.name}: exit {exitLabel run.exit}")
  if run.machine.forks.length != c.forks then
    throw (IO.userError s!"{c.name}: forks {run.machine.forks.length}")
  let sites := run.machine.forks.map (·.site)
  let children := run.machine.forks.map (·.child.value)
  let graph := Tools.View.Run.fiberGraph run.machine []
  if (graph.nodes.toList.map (·.key)).eraseDups.length != graph.nodes.size then
    throw (IO.userError s!"{c.name}: fiber view merged identities")
  if c.name == "fork-has-no-implicit-join" then
    let fork ← match run.machine.forks.head? with
      | some f => pure f
      | none => throw (IO.userError "Detached fork record is missing")
    let child ← match run.machine.fiber? fork.child with
      | some f => pure f
      | none => throw (IO.userError "Detached child is missing")
    if child.exit.isSome then
      throw (IO.userError "Detached child must remain live after parent exits")
  if c.name == "one-fork-site-two-runtime-fibers" then
    if sites.eraseDups.length != 1 || children.eraseDups.length != 2 || graph.nodes.size != 3 then
      throw (IO.userError "Repeated-site control does not distinguish source and runtime identity")
  pure (Lean.Json.mkObj [
    ("name", Lean.toJson c.name), ("admitted", .bool true),
    ("refs", Lean.toJson c.refs), ("exit", Lean.toJson (exitLabel run.exit)),
    ("forkSites", Lean.toJson sites), ("childIds", Lean.toJson children),
    ("fiberGraphKeys", Lean.toJson (graph.nodes.toList.map (·.key))),
    ("journalRows", Lean.toJson run.journal.length)])

def checkEmptyRace : IO Lean.Json := do
  let p : NativeEff := .withFiber (.raceAll .nil)
  let built ← match Api.Author.Internal.finishBuild p [] [] with
    | .ok b => pure b
    | .error _ => throw (IO.userError "empty race: admission refused")
  let run := Run.runPure built "graph-support" { compileFuel := 400, fuel := 400 }
  if run.exit.isSome || !run.machine.forks.isEmpty then
    throw (IO.userError "Empty race must remain live without launched children")
  pure (Lean.Json.mkObj [
    ("name", Lean.toJson "empty-race-is-live"), ("admitted", .bool true),
    ("exit", Lean.toJson (exitLabel run.exit)), ("forkCount", Lean.toJson run.machine.forks.length)])

end ProgramGraphSupport

def main : IO Unit := do
  let rows ← ProgramGraphSupport.cases.mapM ProgramGraphSupport.check
  let empty ← ProgramGraphSupport.checkEmptyRace
  let rows := rows ++ [empty]
  IO.println (Lean.Json.mkObj [
    ("base", Lean.toJson "78f7bcbe"),
    ("budget", Lean.toJson (400 : Nat)),
    ("caseCount", Lean.toJson rows.length),
    ("cases", Lean.toJson rows)]).compress
