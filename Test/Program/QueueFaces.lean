import Test.Program.QueueScenarios
import Effect4.Codegen.ListFold
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.PrintReadable
import TypeScript.Render

/-!
# The faces of the Queue's operations and steps: what prints and reads back (decisions row 255)

Seat T5's part A and the first two steps of its part B are in the tree. An operation's binder
term prints as a function of the cell's current value, `Ref.modify(cell, (s) => …)`, and reads
back. `Deferred.make`'s type arguments print from the operation and read back. A loop's stated
cursor type reads back through the checked type reader, on the readable types
(`Classes.ReadableTy`, DI-91). So:

- **Each scenario prints as a module and reads back.** Each of the eight scenarios of
  `Test/Program/QueueScenarios.lean` takes, and the take's loop states its cursor's type. The
  module reader gives the built program back. Both answers are pinned.
- **One use of each operation prints and reads back.** The operations are the library's
  (`src/Effect4/Modules/Queue/Ops.lean`): the construction, `size`, `poll`, `offer` and `take`.
  Each is printed alone at a caller's scope, and in a program that makes its queue. The text
  of each is pinned. A step's row is long, and its text is pinned in full further down, so the
  operation's pin writes a mark in its place. An offer makes two `Deferred` handles and states
  no cursor type. A take states the type of its loop's cursor.
- **Each of the six step terms prints and reads back alone**: one `Ref.modify` over the step,
  on a cell and handles that the node receives as bound values. The size step is a term over
  the value of a `Ref.get`.
- **A step that needs no handle prints as a whole module** and reads back: the poll step and
  the size step, on a cell that the program makes with `Ref.make`.

Each step row of this battery fixes the name `s` for the cell's current value. Every other term
under that binder is this battery's own variable (addendum 2 of the seat's brief). An operation
mints the name of each of its binders, and a caller's name is not captured
(`Test/Program/QueueOps.lean`).

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on the
Queue's operations and step terms. Every guard is one program. None states target typing or a host run. **Each
printed step is type-checked under tsgo 7 by the truth lane, not here**: the compiler control
`harness/truth/queue-steps.typecheck.ts` copies the six texts that the section "The texts that
the compiler control copies" pins, each at the cell's printed type. The compiler accepts each of
the six, and it accepted each before the literal rule of decisions row 256 too: that rule's
difference was in the readiness probe's take step and in the rate limiter's request, not in
this module's steps (seat T5's measure). Five whole modules over the operations are
type-checked under tsgo 7 and run on rc.112 by the truth lane: `pQueueWake`, `pQueueFull`,
`pQueueInterrupted`, `pQueueMasked` and `pQueueOrder` (`harness/truth/Truth.lean`). The
rendered bytes stay inside each guard.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueFaces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open TypeScript (house0)
open TypeScript.Render (expr)
open Test.Program.QueueScenarios (mk r1 r2 r3 r4 r5 r6 r7 r8)

/-- The module printer's answer on a source, by name. -/
def printVerdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => "not built"
  | .ok b =>
    match Effect4.Api.emitModule "main" b.program b.table with
    | .ok _ => "printed"
    | .error (.print (.binderTerm spelling)) => "refused: binderTerm " ++ spelling
    | .error (.print (.typeSpelling name)) => "refused: typeSpelling " ++ name
    | .error (.print (.internalAction name)) => "refused: internalAction " ++ name
    | .error _ => "refused"

/-- Whether the printed module of a source reads back to the built program. -/
def readsBack (src : Src NativeOp) : Bool :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => false
  | .ok b =>
    match Effect4.Api.printModule "main" b.program b.table with
    | some m => decide (Effect4.Api.readModule m b.table = .ok b.program)
    | none => false

/-- A node elaborated under bound names, at the level they give. -/
def nodeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-- A node elaborated under bound names and printed at their level: the expression, not yet
rendered. -/
def printedAt (names : List String) (src : Src NativeOp) :=
  (nodeAt names src).bind fun p => (print nativeSignature names.length p).toOption

/-- A node prints, and reads back as itself, at a level. -/
def roundTrips (level : Nat) (node : Option (Eff NativeOp)) : Bool :=
  match node with
  | some p => readable nativeSignature nativeSpell level p &&
      decide (roundTrip nativeSignature nativeSpell level p = .ok p)
  | none => false

/-- The module reader's answer on a source's printed module, by name. -/
def readVerdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => "not built"
  | .ok b =>
    match Effect4.Api.printModule "main" b.program b.table with
    | none => "not printed"
    | some m =>
      match Effect4.Api.readModule m b.table with
      | .ok p => if p = b.program then "reads back" else "reads another program"
      | .error (.annotation what) => "refused: annotation " ++ what
      | .error _ => "refused"

/-- Whether the printed module of one source reads back as the built program of another. -/
def readsAs (printed other : Src NativeOp) : Bool :=
  match Effect4.Api.Author.build (mk printed), Effect4.Api.Author.build (mk other) with
  | .ok a, .ok b =>
    match Effect4.Api.printModule "main" a.program a.table with
    | some m => decide (Effect4.Api.readModule m a.table = .ok b.program)
    | none => false
  | _, _ => false

/-! ## The scenarios' modules: printed, and read back -/

/-- One offer into room, on a queue that the program makes. -/
def offerOnly : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let a ← Queue.offer .nat q (nat 1)
  return a

/-- One take, on a queue that the program makes. -/
def takeOnly : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let a ← Queue.take .nat q
  return a

/-- One construction: the queue's cell. -/
def boundedOnly : Src NativeOp := Queue.bounded .nat 2

/-- One read of the size, on a queue that the program makes. -/
def sizeOnly : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let n ← Queue.size .nat q
  return n

/-- One poll, on a queue that the program makes. -/
def pollOnly : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let a ← Queue.poll .nat q
  return a

-- Each scenario's module prints: `Deferred.make`'s type arguments print from the operation.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map printVerdict = List.replicate 8 "printed"
-- Each reads back as the built program: the take's loop states its cursor's type, and the
-- checked type reader reads it (DI-91; the state plan's T5, part B). Before that step the
-- module reader refused each by name, `annotation "local const"`.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map readVerdict = List.replicate 8 "reads back"
-- One use of each operation, in a program that makes its queue: the module prints, and it
-- reads back as the built program.
#guard [boundedOnly, sizeOnly, pollOnly, offerOnly, takeOnly].map printVerdict =
  List.replicate 5 "printed"
#guard [boundedOnly, sizeOnly, pollOnly, offerOnly, takeOnly].map readVerdict =
  List.replicate 5 "reads back"
-- Red control: a use of one operation reads as that program, and not as a use of another.
#guard readsAs takeOnly takeOnly && !readsAs takeOnly offerOnly && !readsAs pollOnly sizeOnly
-- Red control of the comparison: a scenario's module reads as that scenario's program, and as
-- no other scenario's.
#guard readsAs r1 r1 && readsAs r4 r4 && !readsAs r1 r4 && !readsAs r4 r1
-- The smallest program that makes a request's identity prints and reads back.
#guard printVerdict (bindName "id" (Deferred.make .unit .never) fun _ => succeed (nat 1)) =
  "printed"
#guard readVerdict (bindName "id" (Deferred.make .unit .never) fun _ => succeed (nat 1)) =
  "reads back"

/-! ## One use of each operation, alone at a caller's scope

The caller's names are `q` for the handle and `m` for the message. Each operation is one node at
the level of those names. It prints, and its text reads back as itself, at number messages and
at string messages. -/

/-- One use of each operation, each as one node at the level of the caller's names. -/
def operationNodes (A : Ty) : List (Nat × Option (Eff NativeOp)) :=
  [ (0, nodeAt [] (Queue.bounded A 2))
  , (1, nodeAt ["q"] (Queue.size A (var "q")))
  , (1, nodeAt ["q"] (Queue.poll A (var "q")))
  , (2, nodeAt ["q", "m"] (Queue.offer A (var "q") (var "m")))
  , (1, nodeAt ["q"] (Queue.take A (var "q"))) ]

#guard (operationNodes .nat).all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
#guard (operationNodes .string).all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: an operation that reads the handle does not print at a level with no handle.
#guard !roundTrips 0 (nodeAt ["q"] (Queue.take .nat (var "q")))

/-! The printed text of each. A step's row is replaced by a mark: the row is the step's text
of the section "The texts that the compiler control copies", at the level of the operation's own
binders. The guard computes the row and replaces it, so a mark in a pin says that the row is
that step's row. The binders of a take are the mask's restore `a1`, the request's identity
`a2`, the loop's cursor `a3`, the round's hint `a4` and the step's reply `a5`. An offer has no
cursor: its binders are the restore `a2`, the identity `a3`, the hint `a4` and the reply
`a5`, after the handle `a0` and the message `a1`. -/

-- The construction: one `Ref.make` of the empty cell, a record at the cell's declared type.
#guard (printedAt [] (Queue.bounded .nat 2)).map (expr house0 0) = some
  "Ref.make(recordValue<{ readonly cap: number; readonly msgs: ReadonlyArray<number>; readonly offers: ReadonlyArray<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>; readonly takers: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }> }>([10, [20], [[4, [[5, [3, \"msgs\"], [5, [1, false], [10, [8], [[10, [2], []]]]]], [5, [3, \"cap\"], [5, [1, false], [10, [2], []]]], [5, [3, \"takers\"], [5, [1, false], [10, [8], [[10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]]]]]], [5, [3, \"offers\"], [5, [1, false], [10, [8], [[10, [20], [[4, [[5, [3, \"batch\"], [5, [1, false], [10, [5], []]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [5], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"rest\"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]]]]]]]]]], { msgs: nil(), cap: 2, takers: nil(), offers: nil() }))"
-- The size: one read of the cell, then the term over its value.
#guard (printedAt ["q"] (Queue.size .nat (var "q"))).map (expr house0 0) = some
  "Effect.flatMap(Ref.get(a0), (a1) => Effect.succeed(length(recordRequired<\"msgs\">(\"msgs\")(a1))))"
-- The poll: the step under `Effect.uninterruptible`, then one posted helper for each offerer
-- that the step accepted, each with the answer `true`, then the step's first answer.
#guard ((printedAt ["q"] (Queue.poll .nat (var "q"))).bind fun operation =>
    (printedAt ["q"] (Ref.modify "s" (Queue.pollStep .nat (var "s")) (var "q"))).map fun step =>
      (expr house0 0 operation).replace (expr house0 0 step) "<the poll step>") = some
  "Effect.uninterruptible(Effect.flatMap(<the poll step>, (a1) => Effect.flatMap(Effect.suspend(() => {\n  let a2 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a2, length(tupleAt<\"1\">(\"1\")(a1))),\n    body: () => optionCase(get(tupleAt<\"1\">(\"1\")(a1), a2), () => Effect.succeed(undefined), (a3) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a3), true), { startImmediately: false, uninterruptible: true }), (a4) => Effect.succeed(undefined))),\n    step: (a3) => {\n      a2 = succ(a2)\n    },\n  }), () => a2)\n}), (a2) => Effect.succeed(tupleAt<\"0\">(\"0\")(a1)))))"
-- The offer: the mask's getter, the request's two cells, the step, one posted wake for each
-- taker that the step names, and then the answer or the wait at the mask's restore site. An
-- interrupted wait withdraws the request and posts what the withdrawal names.
#guard ((printedAt ["q", "m"] (Queue.offer .nat (var "q") (var "m"))).bind fun operation =>
    (printedAt ["q", "m", "saved", "id", "hint"] (Ref.modify "s"
      (Queue.offerStep .nat (var "id") (var "hint") (var "m") (var "s")) (var "q"))).bind fun step =>
    (printedAt ["q", "m", "saved", "id", "hint", "r", "x", "e"] (Ref.modify "s"
      (Queue.withdrawOffer .nat (var "id") (var "s")) (var "q"))).map fun withdrawal =>
      ((expr house0 0 operation).replace (expr house0 0 step) "<the offer step>").replace
        (expr house0 0 withdrawal) "<the offer's withdrawal>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a2) => Effect.succeed(a2)), (a2) => Effect.uninterruptible(Effect.flatMap(Deferred.make<void, never>(), (a3) => Effect.flatMap(Deferred.make<boolean, never>(), (a4) => Effect.flatMap(<the offer step>, (a5) => Effect.flatMap(Effect.suspend(() => {\n  let a6 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a6, length(tupleAt<\"1\">(\"1\")(a5))),\n    body: () => optionCase(get(tupleAt<\"1\">(\"1\")(a5), a6), () => Effect.succeed(undefined), (a7) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a7), undefined), { startImmediately: false, uninterruptible: true }), (a8) => Effect.succeed(undefined))),\n    step: (a7) => {\n      a6 = succ(a6)\n    },\n  }), () => a6)\n}), (a6) => optionCase(tupleAt<\"0\">(\"0\")(a5), () => Effect.onExit(pipe(Deferred.await(a4), a2), (a7) => Effect.suspend(() => causeIsInterrupt(a7) ? Effect.flatMap(<the offer's withdrawal>, (a8) => Effect.suspend(() => {\n  let a9 = 0\n  return Effect.map(Effect.whileLoop({\n    while: () => lt(a9, length(a8)),\n    body: () => optionCase(get(a8, a9), () => Effect.succeed(undefined), (a10) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a10), undefined), { startImmediately: false, uninterruptible: true }), (a11) => Effect.succeed(undefined))),\n    step: (a10) => {\n      a9 = succ(a9)\n    },\n  }), () => a9)\n})) : Effect.succeed(undefined))), (a7) => Effect.succeed(a7))))))))"
-- The take: the mask's getter, the request's identity, and the loop of attempts at a stated
-- cursor type. A round makes its hint, runs the step, posts the offerers' answers and the
-- takers' wakes, and then answers or waits at the restore site. An interrupted wait withdraws.
-- A loop that ends without a message is a defect.
#guard ((printedAt ["q"] (Queue.take .nat (var "q"))).bind fun operation =>
    (printedAt ["q", "saved", "id", "cursor", "hint"] (Ref.modify "s"
      (Queue.takeStep .nat (var "id") (var "hint") (var "s")) (var "q"))).bind fun step =>
    (printedAt ["q", "saved", "id", "cursor", "hint", "r", "x", "y", "e"] (Ref.modify "s"
      (Queue.withdrawTake .nat (var "id") (var "s")) (var "q"))).map fun withdrawal =>
      ((expr house0 0 operation).replace (expr house0 0 step) "<the take step>").replace
        (expr house0 0 withdrawal) "<the take's withdrawal>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a1) => Effect.succeed(a1)), (a1) => Effect.uninterruptible(Effect.flatMap(Deferred.make<void, never>(), (a2) => Effect.flatMap(Effect.suspend(() => {\n  let a3: Option.Option<number> = none()\n  return Effect.map(Effect.whileLoop({\n    while: () => not(isSome(a3)),\n    body: () => Effect.flatMap(Deferred.make<void, never>(), (a4) => Effect.flatMap(<the take step>, (a5) => Effect.flatMap(Effect.suspend(() => {\n      let a6 = 0\n      return Effect.map(Effect.whileLoop({\n        while: () => lt(a6, length(tupleAt<\"1\">(\"1\")(a5))),\n        body: () => optionCase(get(tupleAt<\"1\">(\"1\")(a5), a6), () => Effect.succeed(undefined), (a7) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a7), true), { startImmediately: false, uninterruptible: true }), (a8) => Effect.succeed(undefined))),\n        step: (a7) => {\n          a6 = succ(a6)\n        },\n      }), () => a6)\n    }), (a6) => Effect.flatMap(Effect.suspend(() => {\n      let a7 = 0\n      return Effect.map(Effect.whileLoop({\n        while: () => lt(a7, length(tupleAt<\"2\">(\"2\")(a5))),\n        body: () => optionCase(get(tupleAt<\"2\">(\"2\")(a5), a7), () => Effect.succeed(undefined), (a8) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a8), undefined), { startImmediately: false, uninterruptible: true }), (a9) => Effect.succeed(undefined))),\n        step: (a8) => {\n          a7 = succ(a7)\n        },\n      }), () => a7)\n    }), (a7) => optionCase(tupleAt<\"0\">(\"0\")(a5), () => Effect.flatMap(Effect.onExit(pipe(Deferred.await(a4), a1), (a8) => Effect.suspend(() => causeIsInterrupt(a8) ? Effect.flatMap(<the take's withdrawal>, (a9) => Effect.suspend(() => {\n      let a10 = 0\n      return Effect.map(Effect.whileLoop({\n        while: () => lt(a10, length(a9)),\n        body: () => optionCase(get(a9, a10), () => Effect.succeed(undefined), (a11) => Effect.flatMap(Effect.forkDetach(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a11), undefined), { startImmediately: false, uninterruptible: true }), (a12) => Effect.succeed(undefined))),\n        step: (a11) => {\n          a10 = succ(a10)\n        },\n      }), () => a10)\n    })) : Effect.succeed(undefined))), (a8) => Effect.succeed(none())), (a8) => Effect.succeed(some(a8))))))),\n    step: (a4) => {\n      a3 = a4\n    },\n  }), () => a3)\n}), (a3) => optionCase(a3, () => Effect.failCause(Cause.die(\"queue: the loop ended without a message\")), (a4) => Effect.succeed(a4))))))"
-- Red control of the marks: without the replacement the take's text holds its two step rows,
-- its three posts and its two `Deferred.make` calls, and it is longer than its pin.
#guard ((printedAt ["q"] (Queue.take .nat (var "q"))).map fun operation =>
    let text := expr house0 0 operation
    ((text.splitOn "Ref.modify(").length - 1, (text.splitOn "Effect.forkDetach(").length - 1,
      (text.splitOn "Deferred.make<").length - 1, (text.splitOn "<the take step>").length - 1)) =
  some (2, 3, 2, 0)
#guard ((printedAt ["q", "m"] (Queue.offer .nat (var "q") (var "m"))).map fun operation =>
    let text := expr house0 0 operation
    ((text.splitOn "Ref.modify(").length - 1, (text.splitOn "Effect.forkDetach(").length - 1,
      (text.splitOn "Deferred.make<").length - 1, (text.splitOn "<the offer step>").length - 1)) =
  some (2, 2, 2, 0)

/-! ## Each step alone prints and reads back -/

/-- The six steps, each as one node at the level of its bound values. -/
def stepNodes (A : Ty) : List (Nat × Option (Eff NativeOp)) :=
  [ (3, nodeAt ["q", "id", "hint"]
      (Ref.modify "s" (Queue.takeStep A (var "id") (var "hint") (var "s")) (var "q")))
  , (4, nodeAt ["q", "a", "id", "hint"]
      (Ref.modify "s" (Queue.offerStep A (var "id") (var "hint") (var "a") (var "s")) (var "q")))
  , (1, nodeAt ["q"] (Ref.modify "s" (Queue.pollStep A (var "s")) (var "q")))
  , (1, nodeAt ["q"]
      (bindName "s" (Ref.get (var "q")) fun s => succeed (Queue.sizeStep A s)))
  , (2, nodeAt ["q", "id"]
      (Ref.modify "s" (Queue.withdrawTake A (var "id") (var "s")) (var "q")))
  , (2, nodeAt ["q", "id"]
      (Ref.modify "s" (Queue.withdrawOffer A (var "id") (var "s")) (var "q"))) ]

-- Each of the six nodes elaborates, prints, and reads back as itself: at number messages, and
-- at string messages, where the offer's record declaration names another type.
#guard (stepNodes .nat).all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
#guard (stepNodes .string).all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: a node read at another level is another program's text, and it does not read
-- back as itself there.
#guard !roundTrips 2 (nodeAt ["q", "id", "hint"]
  (Ref.modify "s" (Queue.takeStep .nat (var "id") (var "hint") (var "s")) (var "q")))

/-! A node's printed text is rendered inside each guard: a battery definition over rendered text
reaches `Classical.choice` (AGENTS.md, Trust). -/

-- The size step in full: a read of the cell, then the term over its value.
#guard ((nodeAt ["q"]
    (bindName "s" (Ref.get (var "q")) fun s => succeed (Queue.sizeStep .nat s))).bind fun p =>
      (print nativeSignature 1 p).toOption.map (expr house0 0)) = some
  "Effect.flatMap(Ref.get(a0), (a1) => Effect.succeed(length(recordRequired<\"msgs\">(\"msgs\")(a1))))"
-- Each step of a `Ref.modify` prints the row with its term as a function of the cell's value,
-- and as many folds as the term holds: nine for the take, none for the offer, one for the poll,
-- three and one for the two withdrawals.
#guard ((stepNodes .nat).map fun entry =>
    (entry.2.bind fun p => (print nativeSignature entry.1 p).toOption.map (expr house0 0)).map
      fun text =>
        ((text.splitOn "Ref.modify(a0, (a").length - 1, (text.splitOn "fold(").length - 1)) =
  [some (1, 9), some (1, 0), some (1, 1), some (0, 0), some (1, 3), some (1, 1)]
-- A fold inside a step's term binds the two levels above the cell's value: the withdrawal's
-- removal reads the cell as `a2` and folds with `a3` and `a4`.
#guard ((nodeAt ["q", "id"]
    (Ref.modify "s" (Queue.withdrawOffer .nat (var "id") (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 2 p).toOption.map (expr house0 0)).any fun text =>
  (text.splitOn "(a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))").length == 2

/-! ## The texts that the compiler control copies

`harness/truth/queue-steps.typecheck.ts` type-checks the six printed steps under tsgo 7, each at
the cell's printed type. It copies the texts below and the size step's text above, so each is
pinned here in full: a change of the printer or of a step moves this file and that one together.
The three printed types are the control's `Cell`, `Taker` and `Offer`. -/

-- The take step in full.
#guard ((nodeAt ["q", "id", "hint"]
    (Ref.modify "s" (Queue.takeStep .nat (var "id") (var "hint") (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 3 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a3) => ite(and(not(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a3)))), or(fold(take(recordRequired<\"takers\">(\"takers\")(a3), 1), false, (a4, a5) => sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)), and(not(fold(recordRequired<\"takers\">(\"takers\")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<\"id\">(\"id\")(a5), a1)))), isZero(length(recordRequired<\"takers\">(\"takers\")(a3)))))), pair(tuple(get(recordRequired<\"msgs\">(\"msgs\")(a3), 0), take(recordRequired<\"offers\">(\"offers\")(a3), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3))), sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3)))), ite(isZero(length(fold(take(recordRequired<\"offers\">(\"offers\")(a3), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3))), sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3)))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), (a4, a5) => append(a4, recordRequired<\"rest\">(\"rest\")(a5))))), take(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil())))), 0), take(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil())))), 1))), recordSet<\"offers\">(\"offers\")(recordSet<\"takers\">(\"takers\")(recordSet<\"msgs\">(\"msgs\")(a3)(fold(take(recordRequired<\"offers\">(\"offers\")(a3), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3))), sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3)))), drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1), (a4, a5) => append(a4, recordRequired<\"rest\">(\"rest\")(a5)))))(fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), a4, append(a4, cons(a5, nil()))))))(drop(recordRequired<\"offers\">(\"offers\")(a3), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3))), sub(recordRequired<\"cap\">(\"cap\")(a3), length(drop(recordRequired<\"msgs\">(\"msgs\")(a3), 1))), length(recordRequired<\"offers\">(\"offers\")(a3)))))), pair(tuple(none(), take(recordRequired<\"offers\">(\"offers\")(a3), 0), take(recordRequired<\"takers\">(\"takers\")(a3), 0)), recordSet<\"takers\">(\"takers\")(a3)(ite(fold(recordRequired<\"takers\">(\"takers\")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<\"id\">(\"id\")(a5), a1))), fold(recordRequired<\"takers\">(\"takers\")(a3), take(recordRequired<\"takers\">(\"takers\")(a3), 0), (a4, a5) => append(a4, cons(ite(sameHandle(recordRequired<\"id\">(\"id\")(a5), a1), recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { id: a1, hint: a2 }), a5), nil()))), append(recordRequired<\"takers\">(\"takers\")(a3), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { id: a1, hint: a2 }), nil())))))))"
-- The offer step in full.
#guard ((nodeAt ["q", "a", "id", "hint"]
    (Ref.modify "s" (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 4 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a4) => ite(not(isZero(length(recordRequired<\"offers\">(\"offers\")(a4)))), pair(tuple(none(), take(recordRequired<\"takers\">(\"takers\")(a4), 0)), recordSet<\"offers\">(\"offers\")(a4)(append(recordRequired<\"offers\">(\"offers\")(a4), cons(recordValue<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [5], []], [10, [], []]]]]], [5, [3, \"batch\"], [5, [1, false], [10, [5], []]]], [5, [3, \"rest\"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { id: a2, hint: a3, batch: false, rest: cons(a1, nil()) }), nil())))), ite(lt(length(recordRequired<\"msgs\">(\"msgs\")(a4)), recordRequired<\"cap\">(\"cap\")(a4)), pair(tuple(some(true), ite(isZero(length(append(recordRequired<\"msgs\">(\"msgs\")(a4), cons(a1, nil())))), take(recordRequired<\"takers\">(\"takers\")(a4), 0), take(recordRequired<\"takers\">(\"takers\")(a4), 1))), recordSet<\"msgs\">(\"msgs\")(a4)(append(recordRequired<\"msgs\">(\"msgs\")(a4), cons(a1, nil())))), pair(tuple(none(), ite(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a4))), take(recordRequired<\"takers\">(\"takers\")(a4), 0), take(recordRequired<\"takers\">(\"takers\")(a4), 1))), recordSet<\"offers\">(\"offers\")(a4)(append(recordRequired<\"offers\">(\"offers\")(a4), cons(recordValue<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [5], []], [10, [], []]]]]], [5, [3, \"batch\"], [5, [1, false], [10, [5], []]]], [5, [3, \"rest\"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { id: a2, hint: a3, batch: false, rest: cons(a1, nil()) }), nil())))))))"
-- The poll step in full.
#guard ((nodeAt ["q"] (Ref.modify "s" (Queue.pollStep .nat (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 1 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a1) => ite(and(not(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a1)))), isZero(length(recordRequired<\"takers\">(\"takers\")(a1)))), pair(tuple(get(recordRequired<\"msgs\">(\"msgs\")(a1), 0), take(recordRequired<\"offers\">(\"offers\")(a1), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1))), sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1))))), recordSet<\"offers\">(\"offers\")(recordSet<\"msgs\">(\"msgs\")(a1)(fold(take(recordRequired<\"offers\">(\"offers\")(a1), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1))), sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1)))), drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1), (a2, a3) => append(a2, recordRequired<\"rest\">(\"rest\")(a3)))))(drop(recordRequired<\"offers\">(\"offers\")(a1), ite(lt(sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1))), sub(recordRequired<\"cap\">(\"cap\")(a1), length(drop(recordRequired<\"msgs\">(\"msgs\")(a1), 1))), length(recordRequired<\"offers\">(\"offers\")(a1)))))), pair(tuple(none(), take(recordRequired<\"offers\">(\"offers\")(a1), 0)), a1)))"
-- The taker's withdrawal in full.
#guard ((nodeAt ["q", "id"]
    (Ref.modify "s" (Queue.withdrawTake .nat (var "id") (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 2 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a2))), take(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))), 0), take(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))), 1)), recordSet<\"takers\">(\"takers\")(a2)(fold(recordRequired<\"takers\">(\"takers\")(a2), take(recordRequired<\"takers\">(\"takers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))))))"
-- The offer's withdrawal in full.
#guard ((nodeAt ["q", "id"]
    (Ref.modify "s" (Queue.withdrawOffer .nat (var "id") (var "s")) (var "q"))).bind fun p =>
      (print nativeSignature 2 p).toOption.map (expr house0 0)) = some
  "Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<\"msgs\">(\"msgs\")(a2))), take(recordRequired<\"takers\">(\"takers\")(a2), 0), take(recordRequired<\"takers\">(\"takers\")(a2), 1)), recordSet<\"offers\">(\"offers\")(a2)(fold(recordRequired<\"offers\">(\"offers\")(a2), take(recordRequired<\"offers\">(\"offers\")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1), a3, append(a3, cons(a4, nil())))))))"
-- The printed types of the cell, of a waiting taker and of a pending offer, at number messages.
#guard (Effect4.Codegen.Types.ofTy (Queue.cellTy .nat)).map (TypeScript.Render.type house0) = some
  "{ readonly cap: number; readonly msgs: ReadonlyArray<number>; readonly offers: ReadonlyArray<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>; readonly takers: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }> }"
#guard (Effect4.Codegen.Types.ofTy Queue.takerTy).map (TypeScript.Render.type house0) = some
  "{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }"
#guard (Effect4.Codegen.Types.ofTy (Queue.offerTy .nat)).map (TypeScript.Render.type house0) = some
  "{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }"

/-! ## A step that needs no handle, as a whole module -/

/-- The poll step on a cell that the program makes. -/
def pollModule : Src NativeOp :=
  bindName "q" (Ref.make (Queue.empty .nat 1)) fun q =>
    Ref.modify "s" (Queue.pollStep .nat (var "s")) q

/-- The size step on a cell that the program makes. -/
def sizeModule : Src NativeOp :=
  bindName "q" (Ref.make (Queue.empty .nat 1)) fun q =>
    bindName "s" (Ref.get q) fun s => succeed (Queue.sizeStep .nat s)

-- The cell's type names `Deferred<void, never>`, and the program makes no `Deferred`: the
-- module prints, and its text reads back to the built program.
#guard printVerdict pollModule = "printed" && readsBack pollModule
#guard printVerdict sizeModule = "printed" && readsBack sizeModule
-- The expression round trip, which reads under the program's classes, gives each program back.
#guard [pollModule, sizeModule].all fun src =>
  ((Effect4.Api.Author.build (mk src)).toOption.map fun b =>
    decide (Effect4.Api.roundTrip b.program = .ok b.program)) = some true

end Test.Program.QueueFaces
