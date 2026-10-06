import Test.Program.PoolScenarios
import Effect4.Modules.Pool.Ops

/-!
# Pool's public operations on the machine: the cases (rows 267 to 269, 276 and 279)

The operations are the library's (`src/Effect4/Modules/Pool/Ops.lean`): `Pool.make` and
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

/-! ## The operations of a case -/

/-- The operations that a case runs. The library's are `library`. A changed policy is another
value. -/
structure Ops where
  make : Ty → Nat → Src NativeOp → Src NativeOp
  use : Ty → TermSrc → (TermSrc → Src NativeOp) → Src NativeOp

/-- The library's `make` at a size that a case states. A size of zero has no pool: the
library's `make` takes a proof that the size is positive. -/
def makeAt (A : Ty) (size : Nat) (acquire : Src NativeOp) : Src NativeOp :=
  if positive : 0 < size then Pool.make A size acquire positive
  else failCause (Authoring.Cause.die (str "pool: a size of zero"))

/-- The library's operations. -/
def library : Ops := { make := makeAt, use := Pool.use }

/-! ## A policy: Pool's part, with its knobs -/

/-- Post one helper (decisions row 238). -/
def post (helper : Src NativeOp) : Src NativeOp :=
  andThen (withFiber (Action.fork helper posted)) (succeed unit)

/-- The return over a return step, and over what it does where a wake is owed. The library's
return is the return over `returnStep` and one posted `Pool.wake` at the count 1. -/
def giveBackOver (step : TermSrc → TermSrc → TermSrc → TermSrc) (owed : TermSrc → Src NativeOp)
    (pool item : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool (step (field item "stamp") (field item "lease"))) fun reply =>
    ifElse (tupleAt reply 1) (owed pool) (succeed unit)

/-- The close over the closer's wait. The library's close is the close over the wrapper's loop
at `Pool.closer`. -/
def closeOver (drain : TermSrc → Src NativeOp) (pool : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool closeStep) fun first =>
    andThen
      (ifElse (andT (tupleAt first 0) (notT (app "isZero" [tupleAt first 1])))
        (post (Pool.wake pool (tupleAt first 1)))
        (succeed unit))
      (drain pool)

/-- A policy: the return, the closer's wait, and the lease at a restore site. Each default is
the library's. -/
structure Policy where
  giveBack : TermSrc → TermSrc → Src NativeOp :=
    giveBackOver returnStep fun pool => post (Pool.wake pool (nat 1))
  drain : TermSrc → Src NativeOp := fun pool => waitRetry .unit Pool.endedClose (Pool.closer pool)
  leaseAt : Ty → TermSrc → (Src NativeOp → Src NativeOp) → Src NativeOp := Pool.lease

/-- The operations of a policy: `make` over the policy's close, and `use` over its lease and
its return. -/
def opsOf (p : Policy) : Ops :=
  { make := fun A size acquire =>
      Pool.acquireAll acquire size fun resources =>
        bindWith (Ref.make (initial A resources)) fun pool =>
          andThen (Pool.atClose (closeOver p.drain pool)) (succeed pool)
    use := fun A pool body =>
      protectedBy (p.leaseAt A pool) (fun item => p.giveBack pool item)
        (fun item => body (field item "resource")) }

/-- The tree of a source at a caller's scope of names. -/
def treeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

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

/-! ### The changed policies of the red controls -/

/-- A return that puts its item at the end of the idle items: rc.112's order. -/
def backOrder : Ops :=
  opsOf { giveBack := giveBackOver returnBackStep fun pool => post (Pool.wake pool (nat 1)) }

/-- A selection made when the wake is posted: the returning fiber selects, and the posted
helper resolves the hints that it was given. -/
def early : Ops :=
  opsOf { giveBack := giveBackOver returnStep fun pool =>
    bindWith (Ref.modifyWith pool (selectStep (nat 1))) fun selected =>
      post (Pool.resolveAll selected) }

/-- A return that runs the item's finalizer: the finalizer's row follows each return. -/
def finalizing (log : TermSrc) : Ops :=
  opsOf { giveBack := fun pool item =>
    andThen (Pool.giveBack pool item) (say log [nat 9, field item "resource"]) }

/-- A close that does not wait: the first step and the wake, and no closer's wait. -/
def noWait : Ops := opsOf { drain := fun _ => succeed unit }

/-! ## What a case observes -/

/-- A snapshot of the cell. -/
def snapshot (pool : TermSrc) : Src NativeOp :=
  bindWith (Ref.get pool) fun s =>
    succeed (tuple [field s "available", heldOf s, leasesOf s, len (field s "waiters"),
      field s "closing", field s "next"])

/-- The acquisition of the cases: the `n`-th acquisition answers the resource `n`, and its
finalizer writes the row `[9, n]`. -/
def acquire (counter log : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith counter fun n => app "pair" [app "succ" [n], app "succ" [n]]) fun n =>
    acquireRelease "res" "x" (succeed n) (say log [nat 9, var "res"])

/-- A borrower's body: it writes that it holds the resource, it runs `work`, and it writes that
it ends. The return follows the last row. -/
def holding (log : TermSrc) (mark : Nat) (work : Src NativeOp) : TermSrc → Src NativeOp :=
  fun resource =>
    andThen (say log [nat 1, nat mark, resource])
      (andThen work (say log [nat 2, nat mark, resource]))

/-- A case: a log, a counter of the acquisitions, and a pool of a size in its own scope. `k`
runs inside the pool's scope, with the pool's handle and the log. The answer is `k`'s answer,
and the log as it stands after the scope's close. -/
def withPool (ops : Ops) (size : Nat) (k : TermSrc → TermSrc → Src NativeOp) : Src NativeOp :=
  eff do
    let log ← Ref.make noRows
    let counter ← Ref.make (nat 0)
    let inside ← scope (eff do
      let pool ← ops.make .nat size (acquire counter log)
      k pool log)
    let l ← Ref.get log
    return tuple [inside, l]

/-- The answer and failure types of a built source. -/
def typesOf (src : Src NativeOp) : Option (Ty × Ty) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => (b.ty.answer, b.ty.error)

/-- Whether a built source requires nothing from its surroundings. -/
def closedOf (src : Src NativeOp) : Option Bool :=
  (Effect4.Api.Author.build (mk src)).toOption.map (·.closed)

/-- The root's exit of the ordinary run at a fuel: the root evaluated, then one flush. The truth
lane runs each program so, at the fuel 1000. -/
def exitAt (fuel : Nat) (src : Src NativeOp) : Option ExitV :=
  (Effect4.Api.Author.build (mk src)).toOption.bind fun b => (Api.run b.program fuel).exit

/-! ## The cases -/

/-- PP1. Size 1. A borrows and returns, then B. The pool's scope closes. `opsAt` takes the log,
for the one red control whose return runs the finalizer. -/
def pp1With (opsAt : TermSrc → Ops) : Src NativeOp :=
  withPool (opsAt (var "log")) 1 fun pool log => eff do
    let _ ← fork ((opsAt log).use .nat pool (holding log 1 (succeed unit)))
    let _ ← fork ((opsAt log).use .nat pool (holding log 2 (succeed unit)))
    snapshot pool

/-- PP2. Size 2. A and B hold the resources 1 and 2. A returns, then B. C borrows, then D. The
gates of C and D open at the end. -/
def pp2With (ops : Ops) : Src NativeOp :=
  withPool ops 2 fun pool log => eff do
    let gA ← Deferred.make .unit .never
    let gB ← Deferred.make .unit .never
    let gC ← Deferred.make .unit .never
    let gD ← Deferred.make .unit .never
    let _ ← fork (ops.use .nat pool (holding log 1 (Deferred.await gA)))
    let _ ← fork (ops.use .nat pool (holding log 2 (Deferred.await gB)))
    let _ ← Deferred.succeed gA unit
    let _ ← Deferred.succeed gB unit
    let between ← snapshot pool
    let _ ← fork (ops.use .nat pool (holding log 3 (Deferred.await gC)))
    let _ ← fork (ops.use .nat pool (holding log 4 (Deferred.await gD)))
    let after ← snapshot pool
    let _ ← Deferred.succeed gC unit
    let _ ← Deferred.succeed gD unit
    return tuple [between, after]

/-- PP3. Size 1. H holds. A waits, then B. H returns. Then A returns. B's gate opens at the
end. -/
def pp3With (ops : Ops) : Src NativeOp :=
  withPool ops 1 fun pool log => eff do
    let gH ← Deferred.make .unit .never
    let gA ← Deferred.make .unit .never
    let gB ← Deferred.make .unit .never
    let _ ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let _ ← fork (ops.use .nat pool (holding log 1 (Deferred.await gA)))
    let _ ← fork (ops.use .nat pool (holding log 2 (Deferred.await gB)))
    let before ← snapshot pool
    let _ ← Deferred.succeed gH unit
    let posted ← snapshot pool
    let _ ← settle
    let afterOne ← snapshot pool
    let _ ← Deferred.succeed gA unit
    let _ ← settle
    let afterTwo ← snapshot pool
    let _ ← Deferred.succeed gB unit
    return tuple [before, posted, afterOne, afterTwo]

/-- PP4. PP3, and A is interrupted after H's return and before the posted helper runs. The
root does not yield between H's return and A's interruption. -/
def pp4With (ops : Ops) : Src NativeOp :=
  withPool ops 1 fun pool log => eff do
    let gH ← Deferred.make .unit .never
    let gB ← Deferred.make .unit .never
    let _ ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let a ← fork (ops.use .nat pool (holding log 1 (succeed unit)))
    let _ ← fork (ops.use .nat pool (holding log 2 (Deferred.await gB)))
    let before ← snapshot pool
    let _ ← Deferred.succeed gH unit
    let posted ← snapshot pool
    let _ ← withFiber (Action.interrupt a)
    let left ← snapshot pool
    let _ ← settle
    let after ← snapshot pool
    let _ ← Deferred.succeed gB unit
    return tuple [before, posted, left, after]

/-- PP8. Size 1. H holds. A waits and is interrupted. H returns, and B borrows. -/
def pp8With (ops : Ops) : Src NativeOp :=
  withPool ops 1 fun pool log => eff do
    let gH ← Deferred.make .unit .never
    let gB ← Deferred.make .unit .never
    let _ ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let a ← fork (ops.use .nat pool (holding log 1 (succeed unit)))
    let waiting ← snapshot pool
    let _ ← withFiber (Action.interrupt a)
    let left ← snapshot pool
    let _ ← Deferred.succeed gH unit
    let _ ← settle
    let returned ← snapshot pool
    let _ ← fork (ops.use .nat pool (holding log 2 (Deferred.await gB)))
    let after ← snapshot pool
    let _ ← Deferred.succeed gB unit
    return tuple [waiting, left, returned, after]

/-- **PP5, the public form.** H leases, A enrols, H returns, the helper selects A at the count
1, and A's own step takes the item. -/
def pp5With (ops : Ops) : Src NativeOp :=
  withPool ops 1 fun pool log => eff do
    let gH ← Deferred.make .unit .never
    let gA ← Deferred.make .unit .never
    let _ ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let _ ← fork (ops.use .nat pool (holding log 1 (Deferred.await gA)))
    let before ← snapshot pool
    let _ ← Deferred.succeed gH unit
    let posted ← snapshot pool
    let _ ← settle
    let after ← snapshot pool
    let _ ← Deferred.succeed gA unit
    return tuple [before, posted, after]

/-- **PP6.** The acquisition registers a cleanup, writes the row `[5]` and fails with 77. A
borrower follows in the program, with the row `[6]` before it. The answer: whether the scope's
exit is a failure, its failure, and the log. -/
def pp6With (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let e ← Authoring.exit (scope (eff do
    let pool ← ops.make .nat 1
      (andThen (acquireRelease "res" "x" (succeed (nat 1)) (say log [nat 9, var "res"]))
        (andThen (say log [nat 5]) (fail (nat 77))))
    let _ ← say log [nat 6]
    ops.use .nat pool (holding log 1 (succeed unit))))
  let l ← Ref.get log
  return tuple [app "causeIsFail" [e], app "causeError" [e], l]

/-- **PP7.** Size 1. H holds, and W waits. A third fiber awaits W's exit, writes the row `[8]`
and opens H's gate. The pool's scope closes: the close wakes W, and it waits for H. The answer:
the cell before the close; whether W's exit and H's exit are interruptions; the cell after the
close; and the log. -/
def pp7With (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let counter ← Ref.make (nat 0)
  let gH ← Deferred.make .unit .never
  let inside ← scope (eff do
    let pool ← ops.make .nat 1 (acquire counter log)
    let h ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let w ← fork (ops.use .nat pool (holding log 1 (succeed unit)))
    let _ ← fork (eff do
      let _ ← await w
      let _ ← say log [nat 8]
      Deferred.succeed gH unit)
    let before ← snapshot pool
    return tuple [before, h, w, pool])
  let ew ← await (tupleAt inside 2)
  let eh ← await (tupleAt inside 1)
  let after ← snapshot (tupleAt inside 3)
  let l ← Ref.get log
  return tuple [tupleAt inside 0, app "causeIsInterrupt" [ew], app "causeIsInterrupt" [eh],
    after, l]

/-- **The closed pool.** The pool's scope closes with no borrower. Then L borrows. The answer:
L's exit, the cell after it, and the log. -/
def closedWith (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let counter ← Ref.make (nat 0)
  let pool ← scope (ops.make .nat 1 (acquire counter log))
  let late ← fork (ops.use .nat pool (holding log 5 (succeed unit)))
  let e ← await late
  let after ← snapshot pool
  let l ← Ref.get log
  return tuple [e, after, l]

/-- **The closing pool.** H holds, and W waits. L awaits W's exit, and then it borrows: the
close has begun by then, and H still holds. A fourth fiber awaits L's exit, reads the cell,
writes the row `[8]` and opens H's gate. The answer: the cell before the close; L's exit; the
cell after L's exit, while H holds; whether H's exit is an interruption; the cell after the
close; and the log. -/
def closingWith (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let counter ← Ref.make (nat 0)
  let gH ← Deferred.make .unit .never
  let seen ← Ref.make (tuple [app "take" [single (nat 0), nat 0],
    app "take" [single (nat 0), nat 0], app "take" [single (nat 0), nat 0], nat 0, bool false,
    nat 0])
  let inside ← scope (eff do
    let pool ← ops.make .nat 1 (acquire counter log)
    let h ← fork (ops.use .nat pool (holding log 9 (Deferred.await gH)))
    let w ← fork (ops.use .nat pool (holding log 1 (succeed unit)))
    let late ← fork (eff do
      let _ ← await w
      ops.use .nat pool (holding log 5 (succeed unit)))
    let _ ← fork (eff do
      let _ ← await late
      let s ← snapshot pool
      let _ ← Ref.set seen s
      let _ ← say log [nat 8]
      Deferred.succeed gH unit)
    let before ← snapshot pool
    return tuple [before, h, late, pool])
  let el ← await (tupleAt inside 2)
  let eh ← await (tupleAt inside 1)
  let whileHeld ← Ref.get seen
  let after ← snapshot (tupleAt inside 3)
  let l ← Ref.get log
  return tuple [tupleAt inside 0, el, whileHeld, app "causeIsInterrupt" [eh], after, l]

/-- The profile's policy as PP1 takes it: it does not read the log. -/
def plainly : TermSrc → Ops := fun _ => library

def pp1 : Src NativeOp := pp1With plainly
def pp2 : Src NativeOp := pp2With library
def pp3 : Src NativeOp := pp3With library
def pp4 : Src NativeOp := pp4With library
def pp5 : Src NativeOp := pp5With library
def pp6 : Src NativeOp := pp6With library
def pp7 : Src NativeOp := pp7With library
def pp8 : Src NativeOp := pp8With library
def closed : Src NativeOp := closedWith library
def closing : Src NativeOp := closingWith library

/-- The ten cases over the library's operations, in order. -/
def cases : List (Src NativeOp) := [pp1, pp2, pp3, pp4, pp5, pp6, pp7, pp8, closed, closing]

-- Each case builds over the library's operations: the checker types every step inside its
-- `Ref.modify`, and the mask's saved state at each restore site.
#guard cases.map verdict = List.replicate 10 "built"
-- Each case requires nothing: the pool is made inside a scope.
#guard cases.map closedOf = List.replicate 10 (some true)
-- A pool that is made outside a scope builds, and the built program requires the scope.
#guard verdict (library.make .nat 1 (succeed (nat 1))) = "built" &&
  closedOf (library.make .nat 1 (succeed (nat 1))) = some false
-- The closed pool's types: L's exit has no failure type, because an interruption is outside
-- the failure column. The case itself has no failure.
#guard typesOf closed = some (.tuple [.exitOf .unit .never,
  .tuple [.list .nat, .list .nat, .list .nat, .nat, .bool, .nat], .list (.list .nat)], .never)

/-! ### The profile's answers, on the machine -/

-- PP1. B gets the same resource: both bodies hold the resource 1. No finalizer runs between:
-- the finalizer's one row is the last, at the scope's close.
def pp1Rows : List (List Nat) := [[1, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [9, 1]]
#guard exitOf pp1 = some (.success (.list [snap [0] [] [] 0 false 2, rows pp1Rows]))

-- PP2. After the two returns the idle items are `[1, 0]`: B's item, which came back last, is
-- at the front. C gets the resource 2, then D gets the resource 1 (row 269). The close
-- finalizes the items in the reverse order of their acquisition.
def pp2Rows : List (List Nat) :=
  [[1, 1, 1], [1, 2, 2], [2, 1, 1], [2, 2, 2], [1, 3, 2], [1, 4, 1], [2, 3, 2], [2, 4, 1],
    [9, 2], [9, 1]]
#guard exitOf pp2 = some (.success (.list
  [.list [snap [1, 0] [] [] 0 false 2, snap [] [0, 1] [3, 2] 0 false 4], rows pp2Rows]))

-- PP3. After H's return and before the helper, the item is idle beside two waiters: a state
-- of the profile. The helper then notifies A alone, and A's own step takes the item: B still
-- waits. After A's return the next helper notifies B.
def pp3Rows : List (List Nat) :=
  [[1, 9, 1], [2, 9, 1], [1, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [9, 1]]
#guard exitOf pp3 = some (.success (.list
  [.list [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2,
    snap [] [0] [2] 0 false 3], rows pp3Rows]))

-- PP4. After H's return two requests wait. A's interruption leaves one. The helper then
-- selects the first waiter of the state that it finds, which is B: it serves no waiter that
-- left. A's body never runs.
def pp4Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 2, 1], [2, 2, 1], [9, 1]]
#guard exitOf pp4 = some (.success (.list
  [.list [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1,
    snap [] [0] [1] 0 false 2], rows pp4Rows]))

-- PP5, the public form. After H's return the item is idle beside A's entry. The helper
-- selects A, and A's own step takes the item at the lease's stamp 1.
def pp5Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 1, 1], [2, 1, 1], [9, 1]]
#guard exitOf pp5 = some (.success (.list
  [.list [snap [] [0] [0] 1 false 1, snap [0] [] [] 1 false 1, snap [] [0] [1] 0 false 2],
    rows pp5Rows]))

-- PP6. `make` fails with the acquisition's failure, 77. The acquisition wrote its row, and its
-- cleanup ran at the scope's close. No row follows `make` in the scope: no borrower ran.
#guard exitOf pp6 = some (.success (.list
  [.bool true, .some (.nat 77), rows [[5], [9, 1]]]))

-- PP7. W is interrupted, and H is not. The gate opens after W's exit. H's body ends, and the
-- finalizer's row follows H's return: the close waited for H (row 268). After the close the
-- item is idle in a closing pool, and nobody waits.
def pp7Rows : List (List Nat) := [[1, 9, 1], [8], [2, 9, 1], [9, 1]]
#guard exitOf pp7 = some (.success (.list
  [snap [] [0] [0] 1 false 1, .bool true, .bool false, snap [0] [] [] 0 true 1, rows pp7Rows]))

-- PP8. The interrupted waiter's entry leaves. H's return then owes no wake, and B leases at
-- once.
def pp8Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 2, 1], [2, 2, 1], [9, 1]]
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

-- One borrower for an item, on each log: each entry of a body is followed by that body's end
-- before the next entry of the resource. A row of the log holds no lease's stamp here, so the
-- check reads the rows at a stamp of zero.
def withStamp (log : List (List Nat)) : List (List Nat) :=
  log.map fun row => if row.length = 3 then row ++ [0] else row
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

/-! ## The engine's fixture: the public cases

The fixture of the generated engine's lane (`ocaml/engine/test/pool/pool.txt`) holds the two
runs of `Test/Program/PoolScenarios.lean`, and then the ten cases of this battery, in order.
Each program crosses as its canonical bytes. The engine's test runs each on both carriers, and
it compares the root's exit with the exit of Lean's machine. The writer beside the engine's
test writes `fixtureText`, and `Test/Program/PoolEngine.lean` binds the committed file to it.

Three answers hold a value that is no number, Boolean or list. PP6 answers a present option,
the failure 77. The two cases of a closed pool answer L's reified exit, a constructor's value
whose cause names L's own fiber. The fixture spells each as the engine's `show_val` does
(`Test.Program.PoolScenarios.showAlgebra`). -/

/-- The names of the public runs in the fixture, in the order of `cases`. -/
def publicNames : List String :=
  ["public-pp1", "public-pp2", "public-pp3", "public-pp4", "public-pp5", "public-pp6",
    "public-pp7", "public-pp8", "public-closed", "public-closing"]

/-- The public runs of the engine's fixture: each case of `cases` under its name. -/
def publicRuns : List (String × Src NativeOp) := publicNames.zip cases

/-- Every run of the engine's fixture: the two earlier runs, and then the public cases. -/
def engineRuns : List (String × Src NativeOp) :=
  Test.Program.PoolScenarios.engineRuns ++ publicRuns

/-- The fixture's whole text. `none` when a run does not build, does not finish, or answers a
value with no spelling. -/
def fixtureText : Option String := fixtureOf engineRuns

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
