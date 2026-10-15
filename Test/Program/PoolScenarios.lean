import Test.Program.PoolScenariosData
import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Mask
import Effect4.Library.Waiting
import Effect4.Library.Pool.Steps
import Effect4.Store.Carrier.Fold
import Effect4.Store.Domain.ProgramWire

/-!
# Pool on the machine: the first check of the cases (decisions rows 267 to 269)

The card's answers are the two builds' answers and readings of the machine's rules
(`docs/research/2026-10-05-claude-lead/module-cards/pool.md`, section 9). This battery runs Pool
programs on the Lean machine and compares each answer with the profile's, case by case. The
pin's answers are the probe's
(`docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-lifecycle.v401.out`).

| Case | The schedule | The profile's answer |
| --- | --- | --- |
| PP1 | Size 1. A borrows and returns, then B. The pool's scope closes | B gets the same resource, and no finalizer runs between |
| PP2 | Size 2. A and B hold 1 and 2. A returns, then B. C borrows, then D | C gets resource 2, then D gets resource 1: a returned item joins the front (row 269) |
| PP3 | Size 1. H holds. A waits, then B. H returns. Then A returns | A gets the item, and B still waits. After A's return B gets it |
| PP4 | PP3, and A is interrupted after H's return and before the posted helper runs | The helper serves B: the selection is made when the helper runs |
| PP8 | Size 1. H holds. A waits and is interrupted. H returns, and B borrows | No waiter is left after the interruption. B gets the item, and nobody is notified |
| PP5, the public retry case | Size 1. H holds, A enrols, H returns | The helper selects A at the count 1. After the selection the item is idle, no waiter is enrolled and A holds nothing. A's own step then takes the item |
| PP5, the low-level control | A stated state: the pool is open, the item is idle, and A and then B wait. One helper at the count 2 | One selection removes A and B. A takes the item and returns it, and B then takes it |

**PP5 is no public schedule of the profile.** Its borrowers ask while the acquisition waits,
and row 267's `make` acquires every item before it answers. So it runs in two forms, each
labelled below.

- **The low-level control** builds its state by hand: a raw lease of the root, the enrolments
  of A and of B, and a raw return that posts nothing. PP3 reaches the same state, after H's
  return and before its helper. The state and the count 2 are premises of the control. No
  public operation posts that count at an open pool: a return posts 1, and the close posts
  every waiter only after it refuses new leases.
- **The public retry case** is a schedule of the profile.

**The operations here are test fixtures.** `use` is one mask around the lease and the body's
hook: the lease loop with a wait and a withdrawal, then the body under `onExit` at the mask's
restore site. A return posts one helper with the count 1 where a wake is owed (decisions row
238). The helper runs one selection step, and it then resolves each selected hint in order.
The fixtures use `posted`, `onInterrupt` and `waitAt` of `src/Effect4/Library/Waiting.lean`,
and the mask's builder. They do not use `waitRetry`: its own mask ends before the body's hook
is installed. Two red controls of that mask stand before the engine's fixture: a lease in its
own mask loses the lease, or it cannot be interrupted while it waits. The public `make` and
`use` are the library's since (`src/Effect4/Library/Pool/Ops.lean`), and
`Test/Program/PoolPublic.lean` runs the cases over them. This battery stays as the first check
of the cases: its fixtures write their rows inside the lease's loop and inside the helper.

**The steps are the library's** (`src/Effect4/Library/Pool/Steps.lean`): the lease step, the
return step, the selection, the withdrawal and the close's first step. The cell is the
library's too (`src/Effect4/Library/Pool/Cell.lean`), at a resource type of numbers. Each red
control changes one step or one fixture.

**The settings of every run.**

- The tape is `[evaluate root, flush]`: two decisions.
- The fuel is 20000, and the compile fuel is 20000.
- The budget of operations before a yield is the default, 2048 for each fiber. No run holds
  an injected yield.
- A child is forked with the default options: it starts at once. A helper is posted: a
  detached fork with a deferred start, uninterruptible.
- The root yields four times where a case lets the posted helpers run.

**What a scenario observes.** A snapshot of the cell is `[the idle stamps, the borrowed items'
stamps, their leases' stamps, the number of waiters, closing, next]`. The log holds rows of
numbers. A borrower's mark is a number: H is 9, A is 1, B is 2, C is 3 and D is 4.

| Row | Who writes it | What it says |
| --- | --- | --- |
| `[1, mark, resource, lease]` | the borrower, after its own lease step | the lease commits |
| `[2, mark, resource, lease]` | the borrower's hook, after its return step | the lease returned |
| `[3, mark, …]` | a probed helper, after its selection step | the selected identities, in order |
| `[4, mark]` | the borrower, when its wait ends | it was notified |
| `[5, idle, borrowed, waiters]` | a probed helper, after its selection step | the cell before any notification |
| `[6, mark]` | the borrower | its lease was refused |
| `[9, resource]` | the resource's finalizer | it ran |

Placement. Each scenario is a finite control of the proposed claim `pool-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the steps' use in a
program. The cases PP3, PP4 and the two forms of PP5 are the finite controls of the card's
reading of the machine's wake (concept `reactive-scheduling`, requirement R12): a resumed
borrower runs inside the helper's task. Every guard is one run on one schedule. None proves
delivery, a cancellation law, a law of the wake across helpers or liveness, and none is a host
run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Pool

-- Each scenario builds: the checker types every step inside its `Ref.modify`.
#guard [pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, pp5control probed holding, c1 library, stale].map verdict =
  List.replicate 10 "built"
#guard exitOf (pp1 plainly) = some (.success (.list [snap [0] [] [] 0 false 2, rows pp1Rows]))
#guard exitOf (pp2 library) = some (.success (.list
  [snap [1, 0] [] [] 0 false 2, snap [] [0, 1] [3, 2] 0 false 4, rows pp2Rows]))
#guard exitOf (pp3 library) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2,
    snap [] [0] [2] 0 false 3, rows pp3Rows]))
#guard exitOf (pp4 library) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1,
    snap [] [0] [1] 0 false 2, rows pp4Rows]))
#guard exitOf (pp8 library) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1,
    snap [] [0] [1] 0 false 2, rows pp8Rows]))
#guard exitOf (pp5public probed) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2, rows pp5publicRows]))
#guard exitOf (pp5control probed atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3, rows pp5controlRows]))
#guard exitOf (pp5control probed holding) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2, rows pp5holdingRows]))

-- The probe changes no answer: the helper with no probe gives the same cells and the same
-- order of leases, on both forms.
#guard exitOf (pp5public library) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2,
    rows [[1, 9, 1, 0], [2, 9, 1, 0], [4, 1], [1, 1, 1, 1]]]))
#guard exitOf (pp5control library atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3,
    rows [[4, 1], [1, 1, 1, 1], [2, 1, 1, 1], [4, 2], [1, 2, 1, 2]]]))

-- C1. The first step begins the close and counts one waiter. W is notified and refused. A new
-- borrower is refused at once. A second close begins nothing. H's lease is still held while
-- the pool is closing, and H's return makes the item idle.
#guard exitOf (c1 library) = some (.success (.list
  [.list [.bool true, .nat 1], snap [] [0] [0] 1 true 1, snap [] [0] [0] 0 true 1,
    .list [.bool false, .nat 0], snap [0] [] [] 0 true 1,
    rows [[1, 9, 1, 0], [4, 1], [6, 1], [6, 2], [2, 9, 1, 0]]]))

-- S1. The lease 0 returns. The second return of the lease 0 is refused, and nothing changes:
-- the lease 1 still holds the item. The lease 1 then returns.
#guard exitOf stale = some (.success (.list
  [.list [.bool true, .bool false], snap [] [0] [1] 0 false 2, .list [.bool false, .bool false],
    snap [] [0] [1] 0 false 2, .list [.bool true, .bool false], snap [0] [] [] 0 false 2]))

-- One borrower for an item, on each log of the profile's policy.
#guard [pp1Rows, pp3Rows, pp4Rows, pp8Rows, pp5publicRows, pp5controlRows, pp5holdingRows].all
  (oneBorrower 1)
#guard oneBorrower 1 pp2Rows && oneBorrower 2 pp2Rows

/-! ### The reading of the machine, on the trace

A borrower that a helper resumes runs inside the helper's task. -/

-- PP5, the control. A is fiber 1, B fiber 2 and the helper fiber 3. A exits before the helper
-- does: A's lease, its body and its return ran inside the helper's task.
#guard exitsOf (pp5control probed atOnce) = some [1, 3, 2, 0]
-- C1. W is fiber 2 and the helper fiber 3. The refused W exits inside the helper's task.
#guard exitsOf (c1 library) = some [2, 3, 4, 1, 0]
-- PP3. H is fiber 1, A fiber 2, B fiber 3, and the helpers are fibers 4 and 5. A holds, so
-- the first helper exits before A does.
#guard exitsOf (pp3 library) = some [1, 4, 2, 5, 3, 0]
-- PP4. The interrupted A (fiber 2) exits before the helper (fiber 4) runs.
#guard exitsOf (pp4 library) = some [1, 2, 4, 3, 0]

/-! ### The settings -/

-- No run holds an injected yield: the budget of 2048 operations is not reached.
#guard [pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, c1 library, stale].map yieldsOf = List.replicate 9 (some [])
-- Each fiber's budget of operations before a yield, at the end of PP3.
#guard ((runOn plain (pp3 library)).map fun r => r.machine.fibers.map (·.maxOpsBeforeYield)) =
  some (List.replicate 6 2048)
-- Each run finishes, and each of the tape's two decisions is played: none is refused.
#guard ([pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, c1 library, stale].map fun src =>
      (runOn plain src).map fun r => (decide (r.inspect.outcome = .finished), r.phases)) =
  List.replicate 9 (some (true, [.progressed, .progressed]))
-- One flush is every flush: two more change nothing.
#guard exitOn [Api.evaluate, Api.flush, Api.flush, Api.flush] (pp3 library) =
  exitOf (pp3 library)

#guard [pp2 backOrder, pp4 early, pp5public handing, pp5control handing atOnce,
    pp1 finalizingAt].map verdict = List.replicate 5 "built"

-- A return that puts the item at the end fails PP2: the idle items are `[0, 1]`, and C gets
-- the resource 1.
#guard exitOf (pp2 backOrder) = some (.success (.list
  [snap [0, 1] [] [] 0 false 2, snap [] [0, 1] [2, 3] 0 false 4,
    rows [[1, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0], [2, 2, 2, 1], [1, 3, 1, 2], [1, 4, 2, 3]]]))
#guard exitOf (pp2 backOrder) != exitOf (pp2 library)
-- At the size 1 the two orders are one: PP2 is the case that tells them apart.
#guard exitOf (pp3 backOrder) = exitOf (pp3 library)

-- A selection made when the wake is posted fails PP4. H's return selects A at once. A then
-- leaves, and the helper resolves the hint of a waiter that left. B is never served: the
-- item stays idle while B waits.
#guard exitOf (pp4 early) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 1 false 1, snap [0] [] [] 1 false 1,
    snap [0] [] [] 1 false 1, rows [[1, 9, 1, 0], [2, 9, 1, 0]]]))
#guard exitOf (pp4 early) != exitOf (pp4 library)
#guard exitOf (pp5public handing) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2, rows pp5publicHandedRows]))
#guard exitOf (pp5public handing) != exitOf (pp5public probed)
#guard exitOf (pp5control handing atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [0] [] [] 0 false 3, rows pp5controlHandedRows]))
#guard !oneBorrower 1 pp5controlHandedRows
#guard oneBorrower 1 pp5controlRows

-- A return that runs the item's finalizer fails PP1: the finalizer's row stands between A's
-- return and B's commit, so B gets a finalized resource.
#guard exitOf (pp1 finalizingAt) = some (.success (.list
  [snap [0] [] [] 0 false 2,
    rows [[1, 1, 1, 0], [2, 1, 1, 0], [9, 1], [1, 2, 1, 1], [2, 2, 1, 1], [9, 1], [9, 1]]]))
#guard exitOf (pp1 finalizingAt) != exitOf (pp1 plainly)

#guard [interruptedHolder useOneRegion, interruptedHolder useTwoRegions,
    interruptedWaiter library.use, interruptedWaiter useNestedMask].map verdict =
  List.replicate 4 "built"

-- G1, one region. The interruption waits for the mask's end. The hook is installed by then,
-- so the lease returns: the item is idle again.
#guard exitOf (interruptedHolder useOneRegion) = some (.success (.list
  [snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1, rows [[1, 1, 1, 0], [2, 1, 1, 0]]]))
-- G1, two regions. The interruption lands at the first mask's end, before the hook is
-- installed. No return runs: the item stays borrowed by a fiber that has exited.
#guard exitOf (interruptedHolder useTwoRegions) = some (.success (.list
  [snap [] [0] [0] 0 false 1, snap [] [0] [0] 0 false 1, rows [[1, 1, 1, 0]]]))
#guard exitOf (interruptedHolder useTwoRegions) != exitOf (interruptedHolder useOneRegion)

-- G2, the profile's `use`. The interrupted waiter's entry leaves, and A never leases.
#guard exitOf (interruptedWaiter library.use) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1,
    rows [[1, 9, 1, 0], [2, 9, 1, 0]]]))
-- G2, the nested mask. The wait cannot be interrupted: A's entry stays, and no withdrawal
-- runs. After H's return A is notified, and A commits a lease after its own interruption.
#guard exitOf (interruptedWaiter useNestedMask) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 1 false 1, snap [0] [] [] 0 false 2,
    rows [[1, 9, 1, 0], [2, 9, 1, 0], [4, 1], [1, 1, 1, 1], [2, 1, 1, 1]]]))
#guard exitOf (interruptedWaiter useNestedMask) != exitOf (interruptedWaiter library.use)

-- Every run has a text. The raw run that the fixture records gives the checked session's exit.
#guard (fixtureOf engineRuns).isSome
#guard engineRuns.all fun (_, src) =>
  (buildOf src).map (fun p => (Api.run p fuel).exit) == some (exitOf src)
-- No run finishes at the engine test's small fuel.
#guard engineRuns.all fun (_, src) =>
  (buildOf src).any fun p => (Api.run p 3).outcome != .finished && (Api.run p 3).exit.isNone

end Test.Program.PoolScenarios
