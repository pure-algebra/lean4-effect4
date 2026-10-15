import Test.Program.PoolScenariosData
import Effect4.Library.Pool.Ops

/-! Shared fixture data. The battery imports these declarations without restating them. -/

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

/-! ### The profile's answers, on the machine -/

-- PP1. B gets the same resource: both bodies hold the resource 1. No finalizer runs between:
-- the finalizer's one row is the last, at the scope's close.
def pp1Rows : List (List Nat) := [[1, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [9, 1]]

-- PP2. After the two returns the idle items are `[1, 0]`: B's item, which came back last, is
-- at the front. C gets the resource 2, then D gets the resource 1 (row 269). The close
-- finalizes the items in the reverse order of their acquisition.
def pp2Rows : List (List Nat) :=
  [[1, 1, 1], [1, 2, 2], [2, 1, 1], [2, 2, 2], [1, 3, 2], [1, 4, 1], [2, 3, 2], [2, 4, 1],
    [9, 2], [9, 1]]

-- PP3. After H's return and before the helper, the item is idle beside two waiters: a state
-- of the profile. The helper then notifies A alone, and A's own step takes the item: B still
-- waits. After A's return the next helper notifies B.
def pp3Rows : List (List Nat) :=
  [[1, 9, 1], [2, 9, 1], [1, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [9, 1]]

-- PP4. After H's return two requests wait. A's interruption leaves one. The helper then
-- selects the first waiter of the state that it finds, which is B: it serves no waiter that
-- left. A's body never runs.
def pp4Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 2, 1], [2, 2, 1], [9, 1]]

-- PP5, the public form. After H's return the item is idle beside A's entry. The helper
-- selects A, and A's own step takes the item at the lease's stamp 1.
def pp5Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 1, 1], [2, 1, 1], [9, 1]]

-- PP7. W is interrupted, and H is not. The gate opens after W's exit. H's body ends, and the
-- finalizer's row follows H's return: the close waited for H (row 268). After the close the
-- item is idle in a closing pool, and nobody waits.
def pp7Rows : List (List Nat) := [[1, 9, 1], [8], [2, 9, 1], [9, 1]]

-- PP8. The interrupted waiter's entry leaves. H's return then owes no wake, and B leases at
-- once.
def pp8Rows : List (List Nat) := [[1, 9, 1], [2, 9, 1], [1, 2, 1], [2, 2, 1], [9, 1]]

-- One borrower for an item, on each log: each entry of a body is followed by that body's end
-- before the next entry of the resource. A row of the log holds no lease's stamp here, so the
-- check reads the rows at a stamp of zero.
def withStamp (log : List (List Nat)) : List (List Nat) :=
  log.map fun row => if row.length = 3 then row ++ [0] else row

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

end Test.Program.PoolPublic
