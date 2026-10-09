import Test.Program.PoolPublic
import Test.Program.SemaphoreFaces

/-!
# The faces of Pool's operations and steps: what prints and reads back (rows 255, 267 and 276)

An operation's binder term prints as a function of the cell's current value,
`Ref.modify(cell, (s) => …)`, and reads back. `Deferred.make`'s type arguments print from the
operation and read back. A loop's stated cursor type reads back through the checked type
reader, on the readable types (`Classes.ReadableTy`, DI-91). So:

- **Each case prints as a module and reads back.** The ten cases of
  `Test/Program/PoolPublic.lean` run the library's operations
  (`src/Effect4/Library/Pool/Ops.lean`). The module reader gives the built program back.
- **One use of each operation prints and reads back**, alone at a caller's scope and in a
  program that makes its pool. The text of each is pinned. A step's row is long, and its text is
  pinned in full further down, so the operation's pin writes a mark in its place.
- **Each of the six step terms prints and reads back alone**: one `Ref.modify` over the step,
  on a cell and handles that the node receives as bound values. The text of each is pinned in
  full.

**What the texts show.** `use` prints as its expansion: one mask, the lease's loop of attempts
at a stated cursor type, the wait as `pipe(…, saved)` at the mask's restore site, the refusal of
a closed pool, and `Effect.onExit` of the body at the restore site. Its hook is the return step
and one `Effect.forkDetach`, whose body is the selection step and a loop over the selected
hints. The close prints its first step, the same posted helper at the count that the step
answers, and the closer's loop under a mask of its own. `make` prints its acquisitions in
order, one `Ref.make` of the initial cell, and one `Effect.acquireRelease` whose release is the
close. The pin's own `Pool` is not printed: a module's clients are programs over its expansion
(decisions rows 230 and 235).

**The answer at a closed pool is one text.** `Pool.refused` prints as
`Effect.flatMap(Effect.fiberId, (who) => Effect.failCause(Cause.interrupt(who)))`. The text of
`use` holds it once, and no other operation holds an interruption.

Each step row of this battery fixes the name `s` for the cell's current value. Every other term
under that binder is this battery's own variable. An operation mints the name of each of its
binders, and a caller's name is not captured (`Test/Program/PoolOps.lean`).

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on Pool's
operations and step terms. Every guard is one program. None states target typing or a host
run. Each printed module of the truth lane is type-checked under tsgo 7 and run on rc.112 there
(`harness/truth/Truth.lean`). The rendered bytes stay inside each guard. The helpers are those
of `Test/Program/SemaphoreFaces.lean`, by import: the printer's and the reader's verdicts, a
node at bound names, and a step's row.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolFaces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open TypeScript (house0)
open TypeScript.Render (expr)
open Test.Program.SemaphoreFaces (printVerdict nodeAt printedAt rowAt roundTrips readVerdict
  readsAs)
open Test.Program.PoolScenarios (exitOf snap)
open Test.Program.PoolPublic (cases pp1 pp2 pp3 pp5 pp7 pp2With pp7With backOrder noWait
  snapshot)
open Effect4.Pool (leaseStep returnStep selectStep withdrawStep closeStep drainStep)

/-! ## The cases' modules: printed, and read back -/

/-- One construction in its scope. The answer is the cell after the scope's close. -/
def makeOnly : Src NativeOp := eff do
  let pool ← scope (Pool.make .nat 2 (succeed (nat 7)))
  snapshot pool

/-- One protected use, on a pool that the program makes. -/
def useOnly : Src NativeOp := scope (eff do
  let pool ← Pool.make .nat 1 (succeed (nat 7))
  Pool.use .nat pool fun resource => succeed resource)

/-- One use of each public operation, each in a program that makes its pool. The close is the
release that `make` registers, so both programs run it. -/
def uses : List (Src NativeOp) := [makeOnly, useOnly]

-- Each case's module prints, and it reads back as the built program: the lease's loop and the
-- closer's loop state their cursors' types, and the checked type reader reads them (DI-91).
#guard cases.map printVerdict = List.replicate 10 "printed"
#guard cases.map readVerdict = List.replicate 10 "reads back"
-- One use of each operation, in a program that makes its pool: the module prints, and it reads
-- back as the built program.
#guard uses.map printVerdict = List.replicate 2 "printed"
#guard uses.map readVerdict = List.replicate 2 "reads back"
-- What the two programs answer on the machine. After the close of a pool of two the cell is
-- closing, with both items idle. The body's answer is the resource.
#guard exitOf makeOnly = some (.success (snap [0, 1] [] [] 0 true 0))
#guard exitOf useOnly = some (.success (.nat 7))
-- Red control: a use of one operation reads as that program, and not as a use of another.
#guard readsAs useOnly useOnly && readsAs makeOnly makeOnly && !readsAs makeOnly useOnly
-- Red control of the comparison: a case's module reads as that case's program, and as no other
-- case's.
#guard readsAs pp1 pp1 && readsAs pp7 pp7 && !readsAs pp1 pp3 && !readsAs pp3 pp5
-- Red control of the policies: the module of a case over the library's operations does not
-- read as the same case over a changed policy. The printed module tells the close that waits
-- from the close that does not, and the release's order of reuse from rc.112's.
#guard !readsAs pp7 (pp7With noWait) && !readsAs pp2 (pp2With backOrder)

/-! ## One use of each operation, alone at a caller's scope

The caller's name for the handle is `q`. Each operation is one node at the level of the
caller's names. It prints, and its text reads back as itself. The last five nodes are parts
that the operations are written over: the refusal, the lease at a restore that is the
identity, the return, the wake and the walk over the selected hints. -/

/-- `make` at the size 2, on an acquisition that answers 7. It reads no name of a caller. -/
def made : Src NativeOp := Pool.make .nat 2 (succeed (nat 7))

/-- `use` of the caller's pool `q`, with a body that answers its resource. -/
def used : Src NativeOp := Pool.use .nat (var "q") fun resource => succeed resource

/-- The close of the caller's pool `q`. -/
def closed : Src NativeOp := Pool.close (var "q")

/-- One use of each operation and of each part, each as one node at the level of the caller's
names. -/
def operationNodes : List (Nat × Option (Eff NativeOp)) :=
  [ (0, nodeAt [] made)
  , (1, nodeAt ["q"] used)
  , (1, nodeAt ["q"] closed)
  , (0, nodeAt [] Pool.refused)
  , (1, nodeAt ["q"] (Pool.lease .nat (var "q") fun wait => wait))
  , (2, nodeAt ["q", "i"] (Pool.giveBack (var "q") (var "i")))
  , (1, nodeAt ["q"] (Pool.wake (var "q") (nat 1)))
  , (1, nodeAt ["l"] (Pool.resolveAll (var "l"))) ]

#guard operationNodes.all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: an operation that reads the handle does not print at a level with no handle.
#guard !roundTrips 0 (nodeAt ["q"] used)

/-! The printed text of each. A step's row is replaced by a mark: the row is the step's text of
the section "Each step alone", at the level of the operation's own binders. The guard computes
the row and replaces it, so a mark in a pin says that the row is that step's row. The caller's
handle is `a0`.

The binders of `use` are the mask's restore `a1`, the request's identity `a2`, the loop's
cursor `a3`, the round's hint `a4`, the lease step's reply `a5` and the wait's exit `a6`. After
the loop `a2` is what the lease answers, an optional item, and then the item. The hook binds the
body's exit `a3` and the return step's reply `a4`. Its helper binds the selected waiters `a5`,
the walk's index `a6` and the waiter `a7`.

The close binds its first step's reply `a1`, and its helper the selected waiters `a2`. The
closer's loop binds its mask's restore `a3`, the closer's identity `a4`, the cursor `a5`, the
round's hint `a6`, the closer's step's reply `a7` and the wait's exit `a8`. -/

-- The refusal in full: the borrower's own identity, and a failure whose cause is its
-- interruption. It is the one definition of the answer at a closed pool.
#guard (printedAt [] Pool.refused).map (expr house0 0) = some
  "Effect.flatMap(Effect.fiberId, (a0) => Effect.failCause(Cause.interrupt(a0)))"
-- `use`: one mask. The acquisition is the lease's loop at a stated cursor type, an option of an
-- optional item. A round makes its hint and runs the lease step. Where the pool is closing or
-- the step leased, the round answers what the step answered. Otherwise it waits at the restore
-- site, and an interrupted wait withdraws. A loop that ends without a lease is a defect. An
-- empty answer is the refusal. Then `Effect.onExit` of the body at the restore site,
-- `pipe(body, a1)`, on the item's resource. The hook is the return step, and one posted helper
-- where its reply says that a waiter is enrolled: the selection step at the count 1, and then
-- each selected hint in order.
#guard ((printedAt ["q"] used).bind fun operation =>
    (rowAt ["q", "saved", "id", "cursor", "hint"]
      (leaseStep (var "id") (var "hint"))).bind fun step =>
    (rowAt ["q", "saved", "id", "cursor", "hint", "r", "e"]
      (withdrawStep (var "id"))).bind fun withdrawal =>
    (rowAt ["q", "saved", "got", "e"]
      (returnStep (field (var "got") "stamp") (field (var "got") "lease"))).bind fun returned =>
    (rowAt ["q", "saved", "got", "e", "r"] (selectStep (nat 1))).map fun selected =>
      ((((expr house0 0 operation).replace (expr house0 0 step) "<the lease step>").replace
        (expr house0 0 withdrawal) "<the withdrawal>").replace
        (expr house0 0 returned) "<the return step>").replace
        (expr house0 0 selected) "<the selection step>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a1) => Effect.succeed(a1)), (a1) => Effect.uninterruptible(Effect.flatMap(Effect.flatMap(Effect.flatMap(Deferred.make<void, never>(), (a2) => Effect.flatMap(Effect.suspend(() => {\n  let a3: Option.Option<Option.Option<{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }>> = none()\n  return Effect.map(Effect.whileLoop({\n    while: () => not(isSome(a3)),\n    body: () => Effect.flatMap(Deferred.make<void, never>(), (a4) => Effect.flatMap(<the lease step>, (a5) => ifCase(() => or(tupleAt<\"0\">(\"0\")(a5), isSome(tupleAt<\"1\">(\"1\")(a5))), () => Effect.succeed(some(tupleAt<\"1\">(\"1\")(a5))), () => Effect.flatMap(Effect.onExit(pipe(Deferred.await(a4), a1), (a6) => ifCase(() => causeIsInterrupt(a6), () => <the withdrawal>, () => Effect.succeed(undefined))), (a6) => Effect.succeed(none()))))),\n    step: (a4) => {\n      a3 = a4\n    },\n  }), () => a3)\n}), (a3) => optionCase(a3, () => Effect.failCause(Cause.die(\"pool: the loop ended without a lease\")), (a4) => Effect.succeed(a4)))), (a2) => optionCase(a2, () => Effect.flatMap(Effect.fiberId, (a3) => Effect.failCause(Cause.interrupt(a3))), (a3) => Effect.succeed(a3))), (a2) => Effect.onExit(pipe(Effect.succeed(recordRequired<\"resource\">(\"resource\")(a2)), a1), (a3) => Effect.flatMap(<the return step>, (a4) => ifCase(() => tupleAt<\"1\">(\"1\")(a4), () => Effect.flatMap(Effect.forkDetach(Effect.flatMap(<the selection step>, (a5) => Effect.suspend(() => {\n  let a6 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a6, length(a5)),\n    body: () => optionCase(get(a5, a6), () => Effect.succeed(undefined), (a7) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a7), undefined), (a8) => Effect.succeed(undefined))),\n    step: (a7) => {\n      a6 = succ(a6)\n    },\n  }), () => undefined)\n})), { startImmediately: false, uninterruptible: true }), (a5) => Effect.succeed(undefined)), () => Effect.succeed(undefined)))))))"
-- The close: the first step. Where it began the close and a waiter is enrolled, one posted
-- helper, whose selection step takes as many waiters as the first step counted. Then the
-- closer's loop under a mask of its own, at the cursor type of an optional unit: a round makes
-- its hint and runs the closer's step. Where no lease is outstanding, the round ends the loop.
-- Otherwise the closer waits at the restore site, and an interrupted wait withdraws.
#guard ((printedAt ["q"] closed).bind fun operation =>
    (rowAt ["q"] closeStep).bind fun step =>
    (rowAt ["q", "first"] (selectStep (tupleAt (var "first") 1))).bind fun selected =>
    (rowAt ["q", "first", "d", "saved", "id", "cursor", "hint"]
      (drainStep (var "id") (var "hint"))).bind fun drained =>
    (rowAt ["q", "first", "d", "saved", "id", "cursor", "hint", "r", "e"]
      (withdrawStep (var "id"))).map fun withdrawal =>
      ((((expr house0 0 operation).replace (expr house0 0 step) "<the close's first step>").replace
        (expr house0 0 selected) "<the selection step>").replace
        (expr house0 0 drained) "<the closer's step>").replace
        (expr house0 0 withdrawal) "<the withdrawal>") = some
  "Effect.flatMap(<the close's first step>, (a1) => Effect.flatMap(ifCase(() => and(tupleAt<\"0\">(\"0\")(a1), not(isZero(tupleAt<\"1\">(\"1\")(a1)))), () => Effect.flatMap(Effect.forkDetach(Effect.flatMap(<the selection step>, (a2) => Effect.suspend(() => {\n  let a3 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a3, length(a2)),\n    body: () => optionCase(get(a2, a3), () => Effect.succeed(undefined), (a4) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a4), undefined), (a5) => Effect.succeed(undefined))),\n    step: (a4) => {\n      a3 = succ(a3)\n    },\n  }), () => undefined)\n})), { startImmediately: false, uninterruptible: true }), (a2) => Effect.succeed(undefined)), () => Effect.succeed(undefined)), (a2) => Effect.flatMap(Effect.uninterruptibleMask((a3) => Effect.succeed(a3)), (a3) => Effect.uninterruptible(Effect.flatMap(Deferred.make<void, never>(), (a4) => Effect.flatMap(Effect.suspend(() => {\n  let a5: Option.Option<void> = none()\n  return Effect.map(Effect.whileLoop({\n    while: () => not(isSome(a5)),\n    body: () => Effect.flatMap(Deferred.make<void, never>(), (a6) => Effect.flatMap(<the closer's step>, (a7) => ifCase(() => a7, () => Effect.succeed(some(undefined)), () => Effect.flatMap(Effect.onExit(pipe(Deferred.await(a6), a3), (a8) => ifCase(() => causeIsInterrupt(a8), () => <the withdrawal>, () => Effect.succeed(undefined))), (a8) => Effect.succeed(none()))))),\n    step: (a6) => {\n      a5 = a6\n    },\n  }), () => a5)\n}), (a5) => optionCase(a5, () => Effect.failCause(Cause.die(\"pool: the loop ended before the pool was drained\")), (a6) => Effect.succeed(a6))))))))"
-- `make` at the size 2: the two acquisitions in order, `a0` and `a1`. One `Ref.make` of the
-- initial cell, a record at the cell's declared type: the items at the stamps 0 and 1, both
-- idle. Then one `Effect.acquireRelease` in the surrounding scope, whose release is the close
-- of the pool `a2`. The answer is the pool. The close's text is replaced by a mark: it is the
-- close's text of the guard above, at the level of this node's binders.
#guard ((printedAt [] made).bind fun operation =>
    (printedAt ["a", "b", "q", "c", "d"] (Pool.close (var "q"))).map fun closing =>
      (expr house0 0 operation).replace (expr house0 0 closing) "<the close>") = some
  "Effect.flatMap(Effect.succeed(7), (a0) => Effect.flatMap(Effect.succeed(7), (a1) => Effect.flatMap(Ref.make(recordValue<{ readonly available: ReadonlyArray<number>; readonly closing: boolean; readonly items: ReadonlyArray<{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }>; readonly next: number; readonly waiters: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }> }>([10, [20], [[4, [[5, [3, \"items\"], [5, [1, false], [10, [8], [[10, [20], [[4, [[5, [3, \"borrowed\"], [5, [1, false], [10, [5], []]]], [5, [3, \"lease\"], [5, [1, false], [10, [2], []]]], [5, [3, \"resource\"], [5, [1, false], [10, [2], []]]], [5, [3, \"stamp\"], [5, [1, false], [10, [2], []]]]]]]]]]]], [5, [3, \"available\"], [5, [1, false], [10, [8], [[10, [2], []]]]]], [5, [3, \"waiters\"], [5, [1, false], [10, [8], [[10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]]]]]], [5, [3, \"closing\"], [5, [1, false], [10, [5], []]]], [5, [3, \"next\"], [5, [1, false], [10, [2], []]]]]]]], { items: append(cons(recordValue<{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }>([10, [20], [[4, [[5, [3, \"stamp\"], [5, [1, false], [10, [2], []]]], [5, [3, \"resource\"], [5, [1, false], [10, [2], []]]], [5, [3, \"borrowed\"], [5, [1, false], [10, [5], []]]], [5, [3, \"lease\"], [5, [1, false], [10, [2], []]]]]]]], { stamp: 0, resource: a0, borrowed: false, lease: 0 }), nil()), cons(recordValue<{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }>([10, [20], [[4, [[5, [3, \"stamp\"], [5, [1, false], [10, [2], []]]], [5, [3, \"resource\"], [5, [1, false], [10, [2], []]]], [5, [3, \"borrowed\"], [5, [1, false], [10, [5], []]]], [5, [3, \"lease\"], [5, [1, false], [10, [2], []]]]]]]], { stamp: 1, resource: a1, borrowed: false, lease: 0 }), nil())), available: append(cons(0, nil()), cons(1, nil())), waiters: nil(), closing: false, next: 0 })), (a2) => Effect.flatMap(Effect.acquireRelease(Effect.succeed(undefined), (a3, a4) => <the close>), (a3) => Effect.succeed(a2)))))"
-- The wake alone: the selection step, and the walk over what it selected.
#guard ((printedAt ["q"] (Pool.wake (var "q") (nat 1))).bind fun operation =>
    (rowAt ["q"] (selectStep (nat 1))).map fun selected =>
      (expr house0 0 operation).replace (expr house0 0 selected) "<the selection step>") = some
  "Effect.flatMap(<the selection step>, (a1) => Effect.suspend(() => {\n  let a2 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a2, length(a1)),\n    body: () => optionCase(get(a1, a2), () => Effect.succeed(undefined), (a3) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a3), undefined), (a4) => Effect.succeed(undefined))),\n    step: (a3) => {\n      a2 = succ(a2)\n    },\n  }), () => undefined)\n}))"
-- Red control of the marks: without the replacement each text holds its step rows. The counts
-- are of `Ref.modify(`, of `Effect.forkDetach(`, of `Deferred.make<` and of `fold(`.
#guard ([(["q"], used), (["q"], closed), ([], made),
    (["q"], Pool.wake (var "q") (nat 1))].map fun entry =>
    (printedAt entry.1 entry.2).map fun printed =>
      let text := expr house0 0 printed
      ((text.splitOn "Ref.modify(").length - 1, (text.splitOn "Effect.forkDetach(").length - 1,
        (text.splitOn "Deferred.make<").length - 1, (text.splitOn "fold(").length - 1)) =
  [some (4, 1, 2, 8), some (4, 1, 2, 4), some (4, 1, 2, 4), some (1, 0, 0, 0)]
-- **The answer at a closed pool is one text.** The counts are of `Cause.interrupt(`, of
-- `Effect.fiberId`, of `Effect.onExit(`, of `Effect.uninterruptibleMask(`, of
-- `Effect.acquireRelease(` and of `Ref.make(`. `use` holds one interruption, and the close and
-- `make` hold none. `use` holds two hooks, the wait's and the body's, under one mask. The close
-- holds the wait's hook under the closer's mask. `make` holds the close, and one registration.
#guard ([(["q"], used), (["q"], closed), ([], made)].map fun entry =>
    (printedAt entry.1 entry.2).map fun printed =>
      ["Cause.interrupt(", "Effect.fiberId", "Effect.onExit(", "Effect.uninterruptibleMask(",
        "Effect.acquireRelease(", "Ref.make("].map fun mark =>
        ((expr house0 0 printed).splitOn mark).length - 1) =
  [some [1, 1, 2, 1, 0, 0], some [0, 0, 1, 1, 0, 0], some [0, 0, 1, 1, 1, 1]]
-- The interruption that `use` holds is the refusal's own text, at the level of its place.
#guard ((printedAt ["q"] used).bind fun operation =>
    (printedAt ["q", "saved", "got"] Pool.refused).map fun refusal =>
      ((expr house0 0 operation).splitOn (expr house0 0 refusal)).length - 1) = some 1

/-! ## Each step alone prints and reads back -/

/-- The six steps, each as one node at the level of its bound values. -/
def stepNodes : List (Nat × Option (Eff NativeOp)) :=
  [ (3, nodeAt ["q", "id", "hint"]
      (Ref.modify "s" (leaseStep (var "id") (var "hint") (var "s")) (var "q")))
  , (3, nodeAt ["q", "i", "l"] (Ref.modify "s" (returnStep (var "i") (var "l") (var "s")) (var "q")))
  , (2, nodeAt ["q", "n"] (Ref.modify "s" (selectStep (var "n") (var "s")) (var "q")))
  , (2, nodeAt ["q", "id"] (Ref.modify "s" (withdrawStep (var "id") (var "s")) (var "q")))
  , (1, nodeAt ["q"] (Ref.modify "s" (closeStep (var "s")) (var "q")))
  , (3, nodeAt ["q", "id", "hint"]
      (Ref.modify "s" (drainStep (var "id") (var "hint") (var "s")) (var "q"))) ]

-- Each of the six nodes elaborates, prints, and reads back as itself.
#guard stepNodes.all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: a node read at another level is another program's text, and it does not read
-- back as itself there.
#guard !roundTrips 2 (nodeAt ["q", "id", "hint"]
  (Ref.modify "s" (leaseStep (var "id") (var "hint") (var "s")) (var "q")))

/-! A node's printed text is rendered inside each guard: a battery definition over rendered text
reaches `Classical.choice` (AGENTS.md, Trust). In each text the cell is `a0`, and the cell's
current value is the binder after the step's own values. -/

-- The lease step in full: three arms. At a closing pool the reply says so, with no item. With
-- no idle item the request enrols. Otherwise the first idle stamp's item is leased at the
-- cell's `next`. The request's own entry leaves by a fold in each arm.
#guard (rowAt ["q", "id", "hint"] (leaseStep (var "id") (var "hint"))).map (expr house0 0) = some
  "Ref.modify(a0, (a3) => ite(recordRequired<\"closing\">(\"closing\")(a3), pair(tuple(true, get(take(recordRequired<\"items\">(\"items\")(a3), 0), 0)), recordSet<\"waiters\">(\"waiters\")(a3)(fold(recordRequired<\"waiters\">(\"waiters\")(a3), take(recordRequired<\"waiters\">(\"waiters\")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), append(a4, cons(a5, nil())), a4)))), ite(isZero(length(recordRequired<\"available\">(\"available\")(a3))), pair(tuple(false, get(take(recordRequired<\"items\">(\"items\")(a3), 0), 0)), recordSet<\"waiters\">(\"waiters\")(a3)(append(fold(recordRequired<\"waiters\">(\"waiters\")(a3), take(recordRequired<\"waiters\">(\"waiters\")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), append(a4, cons(a5, nil())), a4)), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { hint: a2, id: a1 }), nil())))), pair(tuple(false, get(fold(recordRequired<\"items\">(\"items\")(a3), take(recordRequired<\"items\">(\"items\")(a3), 0), (a4, a5) => ite(eq(recordRequired<\"stamp\">(\"stamp\")(a5), getOrElse(get(recordRequired<\"available\">(\"available\")(a3), 0), 0)), append(a4, cons(recordSet<\"lease\">(\"lease\")(recordSet<\"borrowed\">(\"borrowed\")(a5)(true))(recordRequired<\"next\">(\"next\")(a3)), nil())), a4)), 0)), recordSet<\"next\">(\"next\")(recordSet<\"available\">(\"available\")(recordSet<\"items\">(\"items\")(recordSet<\"waiters\">(\"waiters\")(a3)(fold(recordRequired<\"waiters\">(\"waiters\")(a3), take(recordRequired<\"waiters\">(\"waiters\")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), append(a4, cons(a5, nil())), a4))))(fold(recordRequired<\"items\">(\"items\")(a3), take(recordRequired<\"items\">(\"items\")(a3), 0), (a4, a5) => append(a4, cons(ite(eq(recordRequired<\"stamp\">(\"stamp\")(a5), getOrElse(get(recordRequired<\"available\">(\"available\")(a3), 0), 0)), recordSet<\"lease\">(\"lease\")(recordSet<\"borrowed\">(\"borrowed\")(a5)(true))(recordRequired<\"next\">(\"next\")(a3)), a5), nil())))))(drop(recordRequired<\"available\">(\"available\")(a3), 1)))(add(recordRequired<\"next\">(\"next\")(a3), 1))))))"
-- The return step in full: the fold that looks for the borrowed item at the stamp `a1` and at
-- the lease `a2`. Where it is found, the item is idle again at the front of the idle stamps,
-- and the reply's second part says whether a waiter is enrolled. Otherwise the cell stays.
#guard (rowAt ["q", "i", "l"] (returnStep (var "i") (var "l"))).map (expr house0 0) = some
  "Ref.modify(a0, (a3) => ite(fold(recordRequired<\"items\">(\"items\")(a3), false, (a4, a5) => or(a4, and(eq(recordRequired<\"stamp\">(\"stamp\")(a5), a1), and(recordRequired<\"borrowed\">(\"borrowed\")(a5), eq(recordRequired<\"lease\">(\"lease\")(a5), a2))))), pair(tuple(true, not(isZero(length(recordRequired<\"waiters\">(\"waiters\")(a3))))), recordSet<\"available\">(\"available\")(recordSet<\"items\">(\"items\")(a3)(fold(recordRequired<\"items\">(\"items\")(a3), take(recordRequired<\"items\">(\"items\")(a3), 0), (a4, a5) => append(a4, cons(ite(and(eq(recordRequired<\"stamp\">(\"stamp\")(a5), a1), and(recordRequired<\"borrowed\">(\"borrowed\")(a5), eq(recordRequired<\"lease\">(\"lease\")(a5), a2))), recordSet<\"borrowed\">(\"borrowed\")(a5)(false), a5), nil())))))(cons(a1, recordRequired<\"available\">(\"available\")(a3)))), pair(tuple(false, false), a3)))"
-- The selection step in full: the first `a1` waiters leave, and they are the reply.
#guard (rowAt ["q", "n"] (selectStep (var "n"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => pair(take(recordRequired<\"waiters\">(\"waiters\")(a2), a1), recordSet<\"waiters\">(\"waiters\")(a2)(drop(recordRequired<\"waiters\">(\"waiters\")(a2), a1))))"
-- The withdrawal in full.
#guard (rowAt ["q", "id"] (withdrawStep (var "id"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => pair(undefined, recordSet<\"waiters\">(\"waiters\")(a2)(fold(recordRequired<\"waiters\">(\"waiters\")(a2), take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1)), append(a3, cons(a4, nil())), a3)))))"
-- The close's first step in full: the reply says whether this step began the close, and how
-- many waiters are enrolled.
#guard (rowAt ["q"] closeStep).map (expr house0 0) = some
  "Ref.modify(a0, (a1) => pair(tuple(not(recordRequired<\"closing\">(\"closing\")(a1)), length(recordRequired<\"waiters\">(\"waiters\")(a1))), recordSet<\"closing\">(\"closing\")(a1)(true)))"
-- The closer's step in full: the fold that looks for a borrowed item. Where one is found, the
-- closer enrols at the end. Otherwise its entry leaves, and the reply says that the pool is
-- drained.
#guard (rowAt ["q", "id", "hint"] (drainStep (var "id") (var "hint"))).map (expr house0 0) = some
  "Ref.modify(a0, (a3) => ite(fold(recordRequired<\"items\">(\"items\")(a3), false, (a4, a5) => or(a4, recordRequired<\"borrowed\">(\"borrowed\")(a5))), pair(false, recordSet<\"waiters\">(\"waiters\")(a3)(append(fold(recordRequired<\"waiters\">(\"waiters\")(a3), take(recordRequired<\"waiters\">(\"waiters\")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), append(a4, cons(a5, nil())), a4)), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { hint: a2, id: a1 }), nil())))), pair(true, recordSet<\"waiters\">(\"waiters\")(a3)(fold(recordRequired<\"waiters\">(\"waiters\")(a3), take(recordRequired<\"waiters\">(\"waiters\")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), append(a4, cons(a5, nil())), a4))))))"
-- The printed types of the cell, of an item and of a waiter, at resources that are numbers.
#guard (Effect4.Codegen.Types.ofTy (Pool.cellTy .nat)).map (TypeScript.Render.type house0) = some
  "{ readonly available: ReadonlyArray<number>; readonly closing: boolean; readonly items: ReadonlyArray<{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }>; readonly next: number; readonly waiters: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }> }"
#guard (Effect4.Codegen.Types.ofTy (Pool.itemTy .nat)).map (TypeScript.Render.type house0) = some
  "{ readonly borrowed: boolean; readonly lease: number; readonly resource: number; readonly stamp: number }"
#guard (Effect4.Codegen.Types.ofTy Pool.waiterTy).map (TypeScript.Render.type house0) = some
  "{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }"

end Test.Program.PoolFaces
