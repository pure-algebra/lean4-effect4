import Test.Dogfood.Scenario.QueueWorkers.CleanupSource
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.StoreExecution

/-!
Concept: scope-lifetime-finalization R11.
Question: the release writer equations serve `Assertions.logs_history`.
Reach: every job total and each of the three actual acquisition paths.
The environment premises name the root bindings and the acquired identity.
Limit: these equations do not establish those premises along a history.
Consumer: the queue crew's answer-flow and writer-ledger instance.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.QueueWorkers.ReleaseWrites
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The release note appends its captured acquired value. -/
def releaseTerm (identity : Nat) : Term :=
  .app "append" (.cons (.var (identity + 7)) (.cons
    (.app "cons" (.cons (.var (identity + 5)) (.cons (.app "nil" .nil) .nil))) .nil))

/-- Each source release writes the third reference binding. -/
theorem source (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    Node.at_ (.eff (Programs.queueProgram total)) (Programs.queueAcquire identity ++ [1]) =
      some (.eff (.perform (.refUpdateWith (releaseTerm identity)) (.var 2))) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  kernel_rfl

/-- The six root bindings precede the fork bindings and the acquired identity. -/
def environment (identity : Nat) (q opened assigned count gate first second exit : Val)
    (released : RefKey) : List Val :=
  [q, opened, .cell released, assigned, count, gate] ++
    (if identity = 1 then [] else if identity = 2 then [first] else [first, second]) ++
    [.nat identity, exit]

/-- The compiled release note selects the captured log cell, with any exit and decision tape. -/
theorem code (total identity : Nat) (member : identity ∈ [1, 2, 3])
    (q opened assigned count gate first second exit : Val) (released : RefKey)
    (fuel : Nat) (tape : List Bool) :
    resolve (Programs.queueProgram total)
      { path := Programs.queueAcquire identity ++ [1],
        env := environment identity q opened assigned count gate first second exit released,
        fuel := fuel + 1, tape } =
      .sync (.op (.refUpdate released (releaseTerm identity)
        (environment identity q opened assigned count gate first second exit released))) := by
  rw [Agreement.resolve_of_at (source total identity member)]
  rcases List.mem_cons.mp member with rfl | tail
  · cases released; kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · cases released; kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  cases released
  kernel_rfl

/-- The release term appends its own acquired identity once. -/
theorem value (identity : Nat) (member : identity ∈ [1, 2, 3])
    (q opened assigned count gate first second exit : Val) (released : RefKey) (old : List Val) :
    evalTerm ((environment identity q opened assigned count gate first second exit released) ++ [.list old])
      (releaseTerm identity) = some (.list (old ++ [.nat identity])) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  kernel_rfl

/-- One actual release-store operation appends its captured identity and answers unit. -/
theorem operation (identity : Nat) (member : identity ∈ [1, 2, 3])
    (state : Stores) (q opened assigned count gate first second exit : Val)
    (released : RefKey) (old : List Val)
    (read : refPeek state.refs released = some (.list old)) :
    syncOpStep (.refUpdate released (releaseTerm identity)
      (environment identity q opened assigned count gate first second exit released)) state =
      some ({ state with refs := refPoke state.refs released (.list (old ++ [.nat identity])) }, .unit) := by
  change (refStep (.refUpdate released (releaseTerm identity)
    (environment identity q opened assigned count gate first second exit released)) state.refs).map _ = _
  rw [refStep_update state.refs released _ _ _ _ read
    (value identity member q opened assigned count gate first second exit released old)]
  rfl
end Test.Dogfood.Scenario.QueueWorkers.ReleaseWrites
