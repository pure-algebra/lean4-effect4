import Test.Program.PoolPublicData
import Test.Program.PoolScenarios
import Effect4.Library.Pool.Ops

/-!
# Pool's public operations on the machine: the cases (rows 267 to 269, 276 and 279)

The operations are the library's (`src/Effect4/Library/Pool/Ops.lean`): `Pool.make` and
`Pool.use`, with the close that `make` registers. This battery runs the card's cases over them
on the Lean machine (`docs/research/2026-10-05-claude-lead/module-cards/pool.md`, section 9),
and it compares each answer with the profile's. The first check of the cases ran over test
fixtures (`Test/Program/PoolScenarios.lean`), before the operations existed.

| Case | The schedule | The profile's answer |
| --- | --- | --- |
| PP1 | Size 1. A borrows and returns, then B. The pool's scope closes | B gets the same resource. The finalizer runs once, at the close |
| PP2 | Size 2. A and B hold 1 and 2. A returns, then B. C borrows, then D | C gets the resource 2, then D gets the resource 1 (row 269) |
| PP3 | Size 1. H holds. A waits, then B. H returns. Then A returns | A gets the item, and B still waits. After A's return B gets it |
| PP4 | PP3, and A is interrupted after H's return and before the posted helper runs | The helper serves B |
| PP5, the public form | Size 1. H holds, A enrols, H returns | The helper selects A at the count 1, and A's own step takes the item |
| PP6 | The acquisition registers a cleanup and fails | `make` fails with the acquisition's failure. The cleanup runs at the scope's close, and no borrower runs |
| PP7 | Size 1. H holds, and W waits. The pool's scope closes | W is interrupted. The close ends after H's return, and the finalizer runs after that return (row 268) |
| PP8 | Size 1. H holds. A waits and is interrupted. H returns, and B borrows | No waiter is left after the interruption. B gets the item |
| the closed pool | The pool's scope has closed. L borrows | L's exit is the interruption of its own fiber, and its body does not run (row 279) |
| the closing pool | H holds, and the close waits. L borrows | The same exit, before H's return. The close then ends |

**PP7 and the closing pool are the profile's own.** Both Effect builds end the close at once
(decisions row 268 signs the difference).

**The pool is made inside a scope.** `withPool` opens the scope, makes the pool and runs the
case there. So each case ends with the close: every borrower's gate is open before the scope's
end, or the close waits for it. The log is read after the close.

**What a case observes.** A snapshot of the cell is `[the idle stamps, the borrowed items'
stamps, their leases' stamps, the number of waiters, closing, next]`. The log holds rows of
numbers. A borrower's mark is a number: H is 9, A is 1, B is 2, C is 3, D is 4 and L is 5.

| Row | Who writes it | What it says |
| --- | --- | --- |
| `[1, mark, resource]` | the borrower's body, at its entry | the borrower holds the resource |
| `[2, mark, resource]` | the borrower's body, at its end | the return follows |
| `[8]` | a fiber that opens a gate | the gate opens after this row |
| `[9, resource]` | the resource's finalizer | it ran |

**A changed policy is a variant of Pool's part** (`Policy`): another return, another wake or
another close. The policy with no change is the library's operation, tree for tree. Each red
control changes one piece, and each changed program builds: the checker types it.

**The settings of every run.** The tape is `[evaluate root, flush]`. The fuel is 20000, and the
compile fuel is 20000. The budget of operations before a yield is the default, 2048 for each
fiber, and no run holds an injected yield. A child is forked with the default options: it
starts at once. A helper is posted: a detached fork with a deferred start, uninterruptible.

Placement. Each case is a finite control of the proposed claim `pool-expansion-agrees` (concept
`translation-simulation`, requirement R10), on the side of the operations' use in a program.
PP7 and the two cases of a closed pool are finite controls of the proposed claim
`pool-close-waits` (concept `scope-lifetime-finalization`, requirement R11). Every guard is one
run on one schedule. None proves delivery, a cancellation law, a law of the wake across
helpers, a close that ends or liveness, and none is a host run: the host runs are the truth
lane's (`harness/truth/Truth.lean`). The last section names the runs of the generated engine's
fixture: the ten cases cross to the engine after the two earlier runs.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolPublic

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Pool (initial returnStep selectStep closeStep heldBy freed)
open Test.Program.PoolScenarios (mk verdict budget runOn plain exitOn exitOf exitsOf yieldsOf
  noRows say heldOf leasesOf settle snap rows returnBackStep oneBorrower fuel buildOf showExit
  fixtureOf)

-- The policy with no change is the library's operation, tree for tree, at a caller's scope
-- and at three sizes.
#guard [1, 2, 3].all fun size =>
  (treeAt ["a"] ((opsOf {}).make .nat size (succeed (var "a")))).isSome &&
    treeAt ["a"] ((opsOf {}).make .nat size (succeed (var "a"))) ==
      treeAt ["a"] (library.make .nat size (succeed (var "a")))
#guard (treeAt ["p"] ((opsOf {}).use .nat (var "p") fun r => succeed r)).isSome &&
  treeAt ["p"] ((opsOf {}).use .nat (var "p") fun r => succeed r) ==
    treeAt ["p"] (Pool.use .nat (var "p") fun r => succeed r)
-- The pieces: the return and the close over the library's parts are the library's.
#guard treeAt ["p", "i"] (giveBackOver returnStep (fun pool => post (Pool.wake pool (nat 1)))
    (var "p") (var "i")) == treeAt ["p", "i"] (Pool.giveBack (var "p") (var "i"))
#guard treeAt ["p"] (closeOver (fun pool => waitRetry .unit Pool.endedClose (Pool.closer pool))
    (var "p")) == treeAt ["p"] (Pool.close (var "p"))
-- Red control of the comparison: a changed policy is another tree.
#guard treeAt ["p"] ((opsOf { drain := fun _ => succeed unit }).make .nat 1 (succeed (nat 1))) !=
  treeAt ["p"] (library.make .nat 1 (succeed (nat 1)))
-- A size of zero has no pool.
#guard treeAt [] (makeAt .nat 0 (succeed (nat 1))) ==
  treeAt [] (failCause (Authoring.Cause.die (str "pool: a size of zero")))

-- Each case builds over the library's operations: the checker types every step inside its
-- `Ref.modify`, and the mask's saved state at each restore site.
#guard cases.map verdict = List.replicate 10 "built"
-- Each case requires nothing: the pool is made inside a scope.
#guard cases.map closedOf = List.replicate 10 (some true)
-- A pool that is made outside a scope builds, and the built program requires the scope.
#guard verdict (library.make .nat 1 (succeed (nat 1))) = "built" &&
  closedOf (library.make .nat 1 (succeed (nat 1))) = some false
-- Its type says so, as `make_types` states it: the pool's handle, no failure, and exactly the
-- scope's key as its requirement.
#guard ((Effect4.Api.Author.build (mk (library.make .nat 1 (succeed (nat 1))))).toOption.map
    fun b => decide (b.ty.answer = .refOf (Pool.cellTy .nat)) && decide (b.ty.error = .never) &&
      decide (b.ty.requires = Env.Requirement.single (nativeSignature b.table).scopeKey)) =
  some true
-- Its run has no scope that takes the close: the root dies with the missing service.
#guard exitOf (library.make .nat 1 (succeed (nat 1))) =
  some (.failure (Cause.die Defect.missingService))
-- The closed pool's types: L's exit has no failure type, because an interruption is outside
-- the failure column. The case itself has no failure.
#guard typesOf closed = some (.tuple [.exitOf .unit .never,
  .tuple [.list .nat, .list .nat, .list .nat, .nat, .bool, .nat], .list (.list .nat)], .never)
#guard exitOf pp1 = some (.success (.list [snap [0] [] [] 0 false 2, rows pp1Rows]))
#guard exitOf pp2 = some (.success (.list
  [.list [snap [1, 0] [] [] 0 false 2, snap [] [0, 1] [3, 2] 0 false 4], rows pp2Rows]))
#guard exitOf pp3 = some (.success (.list
  [.list [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2,
    snap [] [0] [2] 0 false 3], rows pp3Rows]))
#guard exitOf pp4 = some (.success (.list
  [.list [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1,
    snap [] [0] [1] 0 false 2], rows pp4Rows]))
#guard exitOf pp5 = some (.success (.list
  [.list [snap [] [0] [0] 1 false 1, snap [0] [] [] 1 false 1, snap [] [0] [1] 0 false 2],
    rows pp5Rows]))

-- PP6. `make` fails with the acquisition's failure, 77. The acquisition wrote its row, and its
-- cleanup ran at the scope's close. No row follows `make` in the scope: no borrower ran.
#guard exitOf pp6 = some (.success (.list
  [.bool true, .some (.nat 77), rows [[5], [9, 1]]]))
#guard exitOf pp7 = some (.success (.list
  [snap [] [0] [0] 1 false 1, .bool true, .bool false, snap [0] [] [] 0 true 1, rows pp7Rows]))
#guard exitOf pp8 = some (.success (.list
  [.list [snap [] [0] [0] 1 false 1, snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1,
    snap [] [0] [1] 0 false 2], rows pp8Rows]))

-- The closed pool. L is fiber 1. Its exit is a failure whose cause is the interruption of
-- fiber 1: its own. Its body did not run: no row of L. The finalizer ran at the close, before
-- L asked. The cell stays as the close left it.
#guard exitOf closed = some (.success (.list
  [Val.exitErr (Cause.interrupt (some ⟨1⟩)), snap [0] [] [] 0 true 0, rows [[9, 1]]]))

-- The closing pool. L is fiber 3. Its exit is the interruption of fiber 3, before H's return:
-- the gate opens after it. While H holds, the cell reads H's lease as it was, no idle stamp,
-- and one waiter, which is the closer: L's request left no entry. The close then ends after
-- H's return, and the finalizer runs after it.
#guard exitOf closing = some (.success (.list
  [snap [] [0] [0] 1 false 1, Val.exitErr (Cause.interrupt (some ⟨3⟩)),
    snap [] [0] [0] 1 true 1, .bool false, snap [0] [] [] 0 true 1, rows pp7Rows]))
#guard [pp1Rows, pp3Rows, pp4Rows, pp5Rows, pp7Rows, pp8Rows].all fun log =>
  oneBorrower 1 (withStamp log)
#guard oneBorrower 1 (withStamp pp2Rows) && oneBorrower 2 (withStamp pp2Rows)

/-! ### The reading of the machine, on the trace

A borrower that a helper resumes runs inside the helper's task. So does the closer. -/

-- PP3. H is fiber 1, A fiber 2, B fiber 3, and the helpers are fibers 4 and 5. A holds, so
-- the first helper exits before A does.
#guard exitsOf pp3 = some [1, 4, 2, 5, 3, 0]
-- PP4. The interrupted A (fiber 2) exits before the helper (fiber 4) runs.
#guard exitsOf pp4 = some [1, 2, 4, 3, 0]
-- PP7. W is fiber 2 and the gate's opener fiber 3. The close's helper is fiber 4: W exits
-- inside its task, and so do the opener and H, fiber 1. H's return posts the helper of fiber
-- 5, which wakes the closer: the root runs to its exit inside that task.
#guard exitsOf pp7 = some [2, 1, 3, 4, 0, 5]
-- The closing pool. L is fiber 3: it exits after W and before H.
#guard exitsOf closing = some [2, 3, 1, 4, 5, 0, 6]
-- The closed pool: the close posts no helper, because nobody waits.
#guard exitsOf closed = some [1, 0]

/-! ### The settings -/

-- No run holds an injected yield: the budget of 2048 operations is not reached.
#guard cases.map yieldsOf = List.replicate 10 (some [])
-- Each run finishes, and each of the tape's two decisions is played: none is refused.
#guard (cases.map fun src =>
    (runOn plain src).map fun r => (decide (r.inspect.outcome = .finished), r.phases)) =
  List.replicate 10 (some (true, [.progressed, .progressed]))
-- One flush is every flush: two more change nothing.
#guard exitOn [Api.evaluate, Api.flush, Api.flush, Api.flush] pp7 = exitOf pp7
-- The ordinary run gives each answer too, at the truth lane's fuel: the root evaluated, then
-- one flush.
#guard cases.all fun src => (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src
-- Red control of the fuel: at a fuel of 5 no case has an exit.
#guard cases.all fun src => (exitAt 5 src).isNone

/-! ### The red controls: each changed policy fails its own case

Each changed policy builds, so typing does not catch it. -/

#guard [pp2With backOrder, pp4With early, pp1With finalizing, pp7With noWait].map verdict =
  List.replicate 4 "built"

-- A return that puts the item at the end fails PP2: the idle items are `[0, 1]`, and C gets
-- the resource 1.
#guard exitOf (pp2With backOrder) = some (.success (.list
  [.list [snap [0, 1] [] [] 0 false 2, snap [] [0, 1] [2, 3] 0 false 4],
    rows [[1, 1, 1], [1, 2, 2], [2, 1, 1], [2, 2, 2], [1, 3, 1], [1, 4, 2], [2, 3, 1], [2, 4, 2],
      [9, 2], [9, 1]]]))
#guard exitOf (pp2With backOrder) != exitOf pp2
-- At the size 1 the two orders are one: PP2 is the case that tells them apart.
#guard exitOf (pp3With backOrder) = exitOf pp3

-- A selection made when the wake is posted fails PP4. H's return selects A at once. A then
-- leaves, and the helper resolves the hint of a waiter that left. B is never served: the item
-- stays idle while B waits, and B's body never runs. The close then refuses B.
#guard exitOf (pp4With early) = some (.success (.list
  [.list [snap [] [0] [0] 2 false 1, snap [0] [] [] 1 false 1, snap [0] [] [] 1 false 1,
    snap [0] [] [] 1 false 1], rows [[1, 9, 1], [2, 9, 1], [9, 1]]]))
#guard exitOf (pp4With early) != exitOf pp4

-- A return that runs the item's finalizer fails PP1: the finalizer's row stands between A's
-- return and B's entry, so B gets a finalized resource.
#guard exitOf (pp1With finalizing) = some (.success (.list
  [snap [0] [] [] 0 false 2,
    rows [[1, 1, 1], [2, 1, 1], [9, 1], [1, 2, 1], [2, 2, 1], [9, 1], [9, 1]]]))
#guard exitOf (pp1With finalizing) != exitOf pp1

-- **A close that does not wait fails PP7**: the finalizer's row stands before the gate opens
-- and before H's body ends. The close finalized an item that H still holds. Every other part
-- of the answer is the library's: the exits and the two cells.
#guard exitOf (pp7With noWait) = some (.success (.list
  [snap [] [0] [0] 1 false 1, .bool true, .bool false, snap [0] [] [] 0 true 1,
    rows [[1, 9, 1], [9, 1], [8], [2, 9, 1]]]))
#guard exitOf (pp7With noWait) != exitOf pp7
-- Under the close that does not wait the root exits before H's return posts its helper: the
-- helper, fiber 4, finds nobody.
#guard exitsOf (pp7With noWait) = some [2, 1, 3, 0, 4]
-- With no holder at the close the two closes give one answer: PP1 is no control of the wait.
#guard exitOf (pp1With fun _ => noWait) = exitOf pp1

-- Each case has a name, and no name is written twice.
#guard publicRuns.length = cases.length && (engineRuns.map (·.1)).eraseDups.length = 12
-- Every run has a text. The raw run that the fixture records gives the checked session's exit.
#guard fixtureText.isSome
#guard publicRuns.all fun (_, src) =>
  (buildOf src).map (fun p => (Api.run p fuel).exit) == some (exitOf src)
-- No public run finishes at the engine test's small fuel.
#guard publicRuns.all fun (_, src) =>
  (buildOf src).any fun p => (Api.run p 3).outcome != .finished && (Api.run p 3).exit.isNone
-- The three answers that hold more than numbers, Booleans and lists, in the engine's spelling.
#guard (exitOf pp6).bind showExit = some "success list[true,some 77,list[list[5],list[9,1]]]"
#guard (exitOf closed).bind showExit = some
  ("success list[ctor 1 [ctor 0 [list[ctor 2 [some ctor 0 [1], ctor 0 [list[]]]]]]," ++
    "list[list[0],list[],list[],0,true,0],list[list[9,1]]]")
#guard (exitOf closing).bind showExit = some
  ("success list[list[list[],list[0],list[0],1,false,1]," ++
    "ctor 1 [ctor 0 [list[ctor 2 [some ctor 0 [3], ctor 0 [list[]]]]]]," ++
    "list[list[],list[0],list[0],1,true,1],false,list[list[0],list[],list[],0,true,1]," ++
    "list[list[1,9,1],list[8],list[2,9,1],list[9,1]]]")

end Test.Program.PoolPublic
