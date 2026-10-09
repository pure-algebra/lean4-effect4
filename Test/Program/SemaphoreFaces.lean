import Test.Program.SemaphoreScenarios
import Effect4.Codegen.ListFold
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.PrintReadable
import TypeScript.Render

/-!
# The faces of Semaphore's operations and steps: what prints and reads back (rows 255 and 276)

An operation's binder term prints as a function of the cell's current value,
`Ref.modify(cell, (s) => …)`, and reads back. `Deferred.make`'s type arguments print from the
operation and read back. A loop's stated cursor type reads back through the checked type
reader, on the readable types (`Classes.ReadableTy`, DI-91). So:

- **Each scenario prints as a module and reads back.** The eleven scenarios of
  `Test/Program/SemaphoreScenarios.lean` run the library's six operations
  (`src/Effect4/Library/Semaphore/Ops.lean`). The module reader gives the built program back.
- **One use of each operation prints and reads back**, alone at a caller's scope and in a
  program that makes its semaphore. The text of each is pinned. A step's row is long, and its
  text is pinned in full further down, so the operation's pin writes a mark in its place.
- **Each of the five step terms prints and reads back alone**: one `Ref.modify` over the step,
  on a cell and handles that the node receives as bound values. The text of each is pinned in
  full.

**What the texts show.** `take` prints as its expansion: the mask's getter, the request's
identity, the loop of attempts at a stated cursor type, and the wait as `pipe(…, saved)`, the
mask's restore site. `release` prints under `Effect.uninterruptible`, with one
`Effect.forkDetach` whose body is the walk. A protected form prints one mask over the
acquisition, `Effect.onExit` and the body at the restore site. The pin's own `Semaphore` is not
printed: a module's clients are programs over its expansion (decisions rows 230 and 235).

Each step row of this battery fixes the name `s` for the cell's current value. Every other term
under that binder is this battery's own variable. An operation mints the name of each of its
binders, and a caller's name is not captured (`Test/Program/SemaphoreOps.lean`).

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on
Semaphore's operations and step terms. Every guard is one program. None states target typing
or a host run. Each printed module of the truth lane is type-checked under tsgo 7 and run on
rc.112 there (`harness/truth/Truth.lean`). The rendered bytes stay inside each guard.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreFaces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open TypeScript (house0)
open TypeScript.Render (expr)
open Test.Program.SemaphoreScenarios (mk p1 p2 p3 p4 p7 t1 ifAvailable handoff maskedCaller
  p1Joined p4Joined)
open Effect4.Semaphore (takeStep takeIfAvailableStep releaseStep visitStep withdrawStep)

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

/-- A node elaborated under bound names, at the level they give. -/
def nodeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-- A node elaborated under bound names and printed at their level: the expression, not yet
rendered. -/
def printedAt (names : List String) (src : Src NativeOp) :=
  (nodeAt names src).bind fun p => (print nativeSignature names.length p).toOption

/-- The printed row of a step at bound names: one `Ref.modify` of the cell `q`, with the step's
term under the written name `s`. -/
def rowAt (names : List String) (step : TermSrc → TermSrc) :=
  printedAt names (Ref.modify "s" (step (var "s")) (var "q"))

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

/-- One construction: the semaphore's cell. -/
def makeOnly : Src NativeOp := Semaphore.make 2

/-- One take, on a semaphore that the program makes. -/
def takeOnly : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.take q (nat 1)
  return a

/-- One release. -/
def releaseOnly : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.release q (nat 1)
  return a

/-- One take that never waits. -/
def takeIfAvailableOnly : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.takeIfAvailable q (nat 1)
  return a

/-- One protected body. -/
def withPermitsOnly : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.withPermits q (nat 1) (succeed (nat 7))
  return a

/-- One protected body that never waits. -/
def withPermitsIfAvailableOnly : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.withPermitsIfAvailable q (nat 1) (succeed (nat 7))
  return a

/-- One use of each operation, each in a program that makes its semaphore. -/
def uses : List (Src NativeOp) :=
  [makeOnly, takeOnly, releaseOnly, takeIfAvailableOnly, withPermitsOnly,
    withPermitsIfAvailableOnly]

-- Each scenario's module prints, and it reads back as the built program: the take's loop
-- states its cursor's type, and the checked type reader reads it (DI-91).
#guard [p1, p2, p3, p4, p7, t1, ifAvailable, handoff, maskedCaller, p1Joined, p4Joined].map
    printVerdict = List.replicate 11 "printed"
#guard [p1, p2, p3, p4, p7, t1, ifAvailable, handoff, maskedCaller, p1Joined, p4Joined].map
    readVerdict = List.replicate 11 "reads back"
-- One use of each operation, in a program that makes its semaphore: the module prints, and it
-- reads back as the built program.
#guard uses.map printVerdict = List.replicate 6 "printed"
#guard uses.map readVerdict = List.replicate 6 "reads back"
-- Red control: a use of one operation reads as that program, and not as a use of another.
#guard readsAs takeOnly takeOnly && !readsAs takeOnly releaseOnly &&
  !readsAs withPermitsOnly withPermitsIfAvailableOnly
-- Red control of the comparison: a scenario's module reads as that scenario's program, and as
-- no other scenario's.
#guard readsAs p1 p1 && readsAs p4 p4 && !readsAs p1 p4 && !readsAs p4 p1
-- A joined form's module is another module than its case's.
#guard readsAs p1Joined p1Joined && !readsAs p1Joined p1 && !readsAs p4Joined p4

/-! ## One use of each operation, alone at a caller's scope

The caller's names are `q` for the handle and `n` for the count. Each operation is one node at
the level of those names. It prints, and its text reads back as itself. -/

/-- One use of each operation, each as one node at the level of the caller's names. -/
def operationNodes : List (Nat × Option (Eff NativeOp)) :=
  [ (0, nodeAt [] (Semaphore.make 2))
  , (2, nodeAt ["q", "n"] (Semaphore.take (var "q") (var "n")))
  , (2, nodeAt ["q", "n"] (Semaphore.release (var "q") (var "n")))
  , (2, nodeAt ["q", "n"] (Semaphore.takeIfAvailable (var "q") (var "n")))
  , (2, nodeAt ["q", "n"] (Semaphore.withPermits (var "q") (var "n") (succeed (nat 7))))
  , (2, nodeAt ["q", "n"]
      (Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed (nat 7)))) ]

#guard operationNodes.all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: an operation that reads the handle does not print at a level with no handle.
#guard !roundTrips 0 (nodeAt ["q", "n"] (Semaphore.take (var "q") (var "n")))

/-! The printed text of each. A step's row is replaced by a mark: the row is the step's text of
the section "Each step alone", at the level of the operation's own binders. The guard computes
the row and replaces it, so a mark in a pin says that the row is that step's row. The caller's
handle is `a0` and its count `a1`. The binders of a take are the mask's restore `a2`, the
request's identity `a3`, the loop's cursor `a4`, the round's hint `a5` and the step's reply
`a6`. A release binds its step's reply `a2`, and its helper's walk binds the cursor `a3`, a
visit's reply `a4` and the selected waiter `a5`. A protected form binds the restore `a2` and the
acquired value `a3`, and its hook binds the body's exit `a4`. -/

-- The construction: one `Ref.make` of the initial cell, a record at the cell's declared type.
#guard (printedAt [] (Semaphore.make 2)).map (expr house0 0) = some
  "Ref.make(recordValue<{ readonly next: number; readonly permits: number; readonly taken: number; readonly waiters: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never>; readonly need: number; readonly stamp: number }> }>([10, [20], [[4, [[5, [3, \"permits\"], [5, [1, false], [10, [2], []]]], [5, [3, \"taken\"], [5, [1, false], [10, [2], []]]], [5, [3, \"waiters\"], [5, [1, false], [10, [8], [[10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"need\"], [5, [1, false], [10, [2], []]]], [5, [3, \"stamp\"], [5, [1, false], [10, [2], []]]]]]]]]]]], [5, [3, \"next\"], [5, [1, false], [10, [2], []]]]]]]], { permits: 2, taken: 0, waiters: nil(), next: 0 }))"
-- The take that never waits: the step's row, and nothing else.
#guard ((printedAt ["q", "n"] (Semaphore.takeIfAvailable (var "q") (var "n"))).bind
    fun operation => (rowAt ["q", "n"] (takeIfAvailableStep (var "n"))).map fun step =>
      (expr house0 0 operation).replace (expr house0 0 step) "<the take-if-available step>") =
  some "<the take-if-available step>"
-- The release: the step under `Effect.uninterruptible`; where its reply says that a waiter is
-- enrolled, one posted helper, whose body is the walk; then the free count. The walk is a loop
-- at a cursor that starts at `some(0)`: each round is one visit, and a visit that selects a
-- waiter resolves its hint and answers the next cursor.
#guard ((printedAt ["q", "n"] (Semaphore.release (var "q") (var "n"))).bind fun operation =>
    (rowAt ["q", "n"] (releaseStep (var "n"))).bind fun step =>
    (rowAt ["q", "n", "r", "c"] (visitStep (app "getOrElse" [var "c", nat 0]))).map fun visit =>
      ((expr house0 0 operation).replace (expr house0 0 step) "<the release step>").replace
        (expr house0 0 visit) "<the visit step>") = some
  "Effect.uninterruptible(Effect.flatMap(<the release step>, (a2) => Effect.flatMap(Effect.suspend(() => tupleAt<\"1\">(\"1\")(a2) ? Effect.flatMap(Effect.forkDetach(Effect.suspend(() => {\n  let a3 = some(0)\n  return Effect.map(Effect.whileLoop({\n    while: () => isSome(a3),\n    body: () => Effect.flatMap(<the visit step>, (a4) => optionCase(a4, () => Effect.succeed(none()), (a5) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a5), undefined), (a6) => Effect.succeed(some(add(recordRequired<\"stamp\">(\"stamp\")(a5), 1)))))),\n    step: (a4) => {\n      a3 = a4\n    },\n  }), () => undefined)\n}), { startImmediately: false, uninterruptible: true }), (a3) => Effect.succeed(undefined)) : Effect.succeed(undefined)), (a3) => Effect.succeed(tupleAt<\"0\">(\"0\")(a2)))))"
-- The take: the mask's getter, the request's identity, and the loop of attempts at a stated
-- cursor type. A round makes its hint and runs the step. Where the step took, the round
-- answers the count. Otherwise it waits at the restore site, and an interrupted wait
-- withdraws. A loop that ends without a take is a defect.
#guard ((printedAt ["q", "n"] (Semaphore.take (var "q") (var "n"))).bind fun operation =>
    (rowAt ["q", "n", "saved", "id", "cursor", "hint"]
      (takeStep (var "n") (var "id") (var "hint"))).bind fun step =>
    (rowAt ["q", "n", "saved", "id", "cursor", "hint", "r", "e"]
      (withdrawStep (var "id"))).map fun withdrawal =>
      ((expr house0 0 operation).replace (expr house0 0 step) "<the take step>").replace
        (expr house0 0 withdrawal) "<the withdrawal>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a2) => Effect.succeed(a2)), (a2) => Effect.uninterruptible(Effect.flatMap(Deferred.make<void, never>(), (a3) => Effect.flatMap(Effect.suspend(() => {\n  let a4: Option.Option<number> = none()\n  return Effect.map(Effect.whileLoop({\n    while: () => not(isSome(a4)),\n    body: () => Effect.flatMap(Deferred.make<void, never>(), (a5) => Effect.flatMap(<the take step>, (a6) => Effect.suspend(() => a6 ? Effect.succeed(some(a1)) : Effect.flatMap(Effect.onExit(pipe(Deferred.await(a5), a2), (a7) => Effect.suspend(() => causeIsInterrupt(a7) ? <the withdrawal> : Effect.succeed(undefined))), (a7) => Effect.succeed(none()))))),\n    step: (a5) => {\n      a4 = a5\n    },\n  }), () => a4)\n}), (a4) => optionCase(a4, () => Effect.failCause(Cause.die(\"semaphore: the loop ended without a take\")), (a5) => Effect.succeed(a5))))))"
-- The protected permit: one mask. The acquisition is the take's loop, bound as `a3`. Then
-- `Effect.onExit` of the body at the restore site, `pipe(body, a2)`, with the release as its
-- hook.
#guard ((printedAt ["q", "n"]
      (Semaphore.withPermits (var "q") (var "n") (succeed (nat 7)))).bind fun operation =>
    (rowAt ["q", "n", "saved", "id", "cursor", "hint"]
      (takeStep (var "n") (var "id") (var "hint"))).bind fun step =>
    (rowAt ["q", "n", "saved", "id", "cursor", "hint", "r", "e"]
      (withdrawStep (var "id"))).bind fun withdrawal =>
    (rowAt ["q", "n", "saved", "got", "e"] (releaseStep (var "n"))).bind fun released =>
    (rowAt ["q", "n", "saved", "got", "e", "r", "c"]
      (visitStep (app "getOrElse" [var "c", nat 0]))).map fun visit =>
      ((((expr house0 0 operation).replace (expr house0 0 step) "<the take step>").replace
        (expr house0 0 withdrawal) "<the withdrawal>").replace
        (expr house0 0 released) "<the release step>").replace
        (expr house0 0 visit) "<the visit step>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a2) => Effect.succeed(a2)), (a2) => Effect.uninterruptible(Effect.flatMap(Effect.flatMap(Deferred.make<void, never>(), (a3) => Effect.flatMap(Effect.suspend(() => {\n  let a4: Option.Option<number> = none()\n  return Effect.map(Effect.whileLoop({\n    while: () => not(isSome(a4)),\n    body: () => Effect.flatMap(Deferred.make<void, never>(), (a5) => Effect.flatMap(<the take step>, (a6) => Effect.suspend(() => a6 ? Effect.succeed(some(a1)) : Effect.flatMap(Effect.onExit(pipe(Deferred.await(a5), a2), (a7) => Effect.suspend(() => causeIsInterrupt(a7) ? <the withdrawal> : Effect.succeed(undefined))), (a7) => Effect.succeed(none()))))),\n    step: (a5) => {\n      a4 = a5\n    },\n  }), () => a4)\n}), (a4) => optionCase(a4, () => Effect.failCause(Cause.die(\"semaphore: the loop ended without a take\")), (a5) => Effect.succeed(a5)))), (a3) => Effect.onExit(pipe(Effect.succeed(7), a2), (a4) => Effect.uninterruptible(Effect.flatMap(<the release step>, (a5) => Effect.flatMap(Effect.suspend(() => tupleAt<\"1\">(\"1\")(a5) ? Effect.flatMap(Effect.forkDetach(Effect.suspend(() => {\n  let a6 = some(0)\n  return Effect.map(Effect.whileLoop({\n    while: () => isSome(a6),\n    body: () => Effect.flatMap(<the visit step>, (a7) => optionCase(a7, () => Effect.succeed(none()), (a8) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a8), undefined), (a9) => Effect.succeed(some(add(recordRequired<\"stamp\">(\"stamp\")(a8), 1)))))),\n    step: (a7) => {\n      a6 = a7\n    },\n  }), () => undefined)\n}), { startImmediately: false, uninterruptible: true }), (a6) => Effect.succeed(undefined)) : Effect.succeed(undefined)), (a6) => Effect.succeed(tupleAt<\"0\">(\"0\")(a5)))))))))"
-- The protected form that never waits: the same mask over the step that never waits. The body
-- and the hook each select on what that step answered, `a3`.
#guard ((printedAt ["q", "n"]
      (Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed (nat 7)))).bind
    fun operation =>
    (rowAt ["q", "n", "saved"] (takeIfAvailableStep (var "n"))).bind fun step =>
    (rowAt ["q", "n", "saved", "took", "e"] (releaseStep (var "n"))).bind fun released =>
    (rowAt ["q", "n", "saved", "took", "e", "r", "c"]
      (visitStep (app "getOrElse" [var "c", nat 0]))).map fun visit =>
      (((expr house0 0 operation).replace (expr house0 0 step)
        "<the take-if-available step>").replace
        (expr house0 0 released) "<the release step>").replace
        (expr house0 0 visit) "<the visit step>") = some
  "Effect.flatMap(Effect.uninterruptibleMask((a2) => Effect.succeed(a2)), (a2) => Effect.uninterruptible(Effect.flatMap(<the take-if-available step>, (a3) => Effect.onExit(pipe(Effect.suspend(() => a3 ? Effect.flatMap(Effect.succeed(7), (a4) => Effect.succeed(some(a4))) : Effect.succeed(none())), a2), (a4) => Effect.suspend(() => a3 ? Effect.flatMap(Effect.uninterruptible(Effect.flatMap(<the release step>, (a5) => Effect.flatMap(Effect.suspend(() => tupleAt<\"1\">(\"1\")(a5) ? Effect.flatMap(Effect.forkDetach(Effect.suspend(() => {\n  let a6 = some(0)\n  return Effect.map(Effect.whileLoop({\n    while: () => isSome(a6),\n    body: () => Effect.flatMap(<the visit step>, (a7) => optionCase(a7, () => Effect.succeed(none()), (a8) => Effect.flatMap(Deferred.succeed(recordRequired<\"hint\">(\"hint\")(a8), undefined), (a9) => Effect.succeed(some(add(recordRequired<\"stamp\">(\"stamp\")(a8), 1)))))),\n    step: (a7) => {\n      a6 = a7\n    },\n  }), () => undefined)\n}), { startImmediately: false, uninterruptible: true }), (a6) => Effect.succeed(undefined)) : Effect.succeed(undefined)), (a6) => Effect.succeed(tupleAt<\"0\">(\"0\")(a5))))), (a5) => Effect.succeed(undefined)) : Effect.succeed(undefined))))))"
-- Red control of the marks: without the replacement each text holds its step rows. The counts
-- are of `Ref.modify(`, of `Effect.forkDetach(`, of `Deferred.make<` and of `fold(`.
#guard ([Semaphore.take (var "q") (var "n"), Semaphore.release (var "q") (var "n"),
    Semaphore.withPermits (var "q") (var "n") (succeed (nat 7)),
    Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed (nat 7)),
    Semaphore.takeIfAvailable (var "q") (var "n")].map fun operation =>
    (printedAt ["q", "n"] operation).map fun printed =>
      let text := expr house0 0 printed
      ((text.splitOn "Ref.modify(").length - 1, (text.splitOn "Effect.forkDetach(").length - 1,
        (text.splitOn "Deferred.make<").length - 1, (text.splitOn "fold(").length - 1)) =
  [some (2, 0, 2, 3), some (2, 1, 0, 3), some (4, 1, 2, 6), some (3, 1, 0, 3),
    some (1, 0, 0, 0)]

/-! ## Each step alone prints and reads back -/

/-- The five steps, each as one node at the level of its bound values. -/
def stepNodes : List (Nat × Option (Eff NativeOp)) :=
  [ (4, nodeAt ["q", "n", "id", "hint"]
      (Ref.modify "s" (takeStep (var "n") (var "id") (var "hint") (var "s")) (var "q")))
  , (2, nodeAt ["q", "n"] (Ref.modify "s" (takeIfAvailableStep (var "n") (var "s")) (var "q")))
  , (2, nodeAt ["q", "n"] (Ref.modify "s" (releaseStep (var "n") (var "s")) (var "q")))
  , (2, nodeAt ["q", "c"] (Ref.modify "s" (visitStep (var "c") (var "s")) (var "q")))
  , (2, nodeAt ["q", "id"] (Ref.modify "s" (withdrawStep (var "id") (var "s")) (var "q"))) ]

-- Each of the five nodes elaborates, prints, and reads back as itself.
#guard stepNodes.all fun entry => entry.2.isSome && roundTrips entry.1 entry.2
-- Red control: a node read at another level is another program's text, and it does not read
-- back as itself there.
#guard !roundTrips 2 (nodeAt ["q", "n", "id", "hint"]
  (Ref.modify "s" (takeStep (var "n") (var "id") (var "hint") (var "s")) (var "q")))

/-! A node's printed text is rendered inside each guard: a battery definition over rendered text
reaches `Classical.choice` (AGENTS.md, Trust). -/

-- The take step in full: the request's own entry leaves by a fold in each arm.
#guard (rowAt ["q", "n", "id", "hint"] (takeStep (var "n") (var "id") (var "hint"))).map
    (expr house0 0) = some
  "Ref.modify(a0, (a4) => ite(not(lt(sub(recordRequired<\"permits\">(\"permits\")(a4), recordRequired<\"taken\">(\"taken\")(a4)), a1)), pair(true, recordSet<\"waiters\">(\"waiters\")(recordSet<\"taken\">(\"taken\")(a4)(add(recordRequired<\"taken\">(\"taken\")(a4), a1)))(fold(recordRequired<\"waiters\">(\"waiters\")(a4), take(recordRequired<\"waiters\">(\"waiters\")(a4), 0), (a5, a6) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a6), a2)), append(a5, cons(a6, nil())), a5)))), pair(false, recordSet<\"next\">(\"next\")(recordSet<\"waiters\">(\"waiters\")(a4)(append(fold(recordRequired<\"waiters\">(\"waiters\")(a4), take(recordRequired<\"waiters\">(\"waiters\")(a4), 0), (a5, a6) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a6), a2)), append(a5, cons(a6, nil())), a5)), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never>; readonly need: number; readonly stamp: number }>([10, [20], [[4, [[5, [3, \"hint\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"id\"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, \"need\"], [5, [1, false], [10, [2], []]]], [5, [3, \"stamp\"], [5, [1, false], [10, [2], []]]]]]]], { hint: a3, id: a2, need: a1, stamp: recordRequired<\"next\">(\"next\")(a4) }), nil()))))(add(recordRequired<\"next\">(\"next\")(a4), 1)))))"
-- The take-if-available step in full.
#guard (rowAt ["q", "n"] (takeIfAvailableStep (var "n"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => ite(not(lt(sub(recordRequired<\"permits\">(\"permits\")(a2), recordRequired<\"taken\">(\"taken\")(a2)), a1)), pair(true, recordSet<\"taken\">(\"taken\")(a2)(add(recordRequired<\"taken\">(\"taken\")(a2), a1))), pair(false, a2)))"
-- The release step in full: the truncated subtraction, and the reply's two parts.
#guard (rowAt ["q", "n"] (releaseStep (var "n"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => pair(tuple(sub(recordRequired<\"permits\">(\"permits\")(a2), sub(recordRequired<\"taken\">(\"taken\")(a2), a1)), not(isZero(length(recordRequired<\"waiters\">(\"waiters\")(a2))))), recordSet<\"taken\">(\"taken\")(a2)(sub(recordRequired<\"taken\">(\"taken\")(a2), a1))))"
-- The visit step in full: the fold of the waiters from the first fitting one stands three
-- times, and the cursor `a1` and the cell `a2` stand in its body.
#guard (rowAt ["q", "c"] (visitStep (var "c"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => ite(isZero(sub(recordRequired<\"permits\">(\"permits\")(a2), recordRequired<\"taken\">(\"taken\")(a2))), pair(get(take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), 0), a2), pair(get(fold(recordRequired<\"waiters\">(\"waiters\")(a2), take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), (a3, a4) => ite(or(not(isZero(length(a3))), and(not(lt(recordRequired<\"stamp\">(\"stamp\")(a4), a1)), not(lt(sub(recordRequired<\"permits\">(\"permits\")(a2), recordRequired<\"taken\">(\"taken\")(a2)), recordRequired<\"need\">(\"need\")(a4))))), append(a3, cons(a4, nil())), a3)), 0), recordSet<\"waiters\">(\"waiters\")(a2)(append(take(recordRequired<\"waiters\">(\"waiters\")(a2), sub(length(recordRequired<\"waiters\">(\"waiters\")(a2)), length(fold(recordRequired<\"waiters\">(\"waiters\")(a2), take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), (a3, a4) => ite(or(not(isZero(length(a3))), and(not(lt(recordRequired<\"stamp\">(\"stamp\")(a4), a1)), not(lt(sub(recordRequired<\"permits\">(\"permits\")(a2), recordRequired<\"taken\">(\"taken\")(a2)), recordRequired<\"need\">(\"need\")(a4))))), append(a3, cons(a4, nil())), a3))))), drop(fold(recordRequired<\"waiters\">(\"waiters\")(a2), take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), (a3, a4) => ite(or(not(isZero(length(a3))), and(not(lt(recordRequired<\"stamp\">(\"stamp\")(a4), a1)), not(lt(sub(recordRequired<\"permits\">(\"permits\")(a2), recordRequired<\"taken\">(\"taken\")(a2)), recordRequired<\"need\">(\"need\")(a4))))), append(a3, cons(a4, nil())), a3)), 1))))))"
-- The withdrawal in full.
#guard (rowAt ["q", "id"] (withdrawStep (var "id"))).map (expr house0 0) = some
  "Ref.modify(a0, (a2) => pair(undefined, recordSet<\"waiters\">(\"waiters\")(a2)(fold(recordRequired<\"waiters\">(\"waiters\")(a2), take(recordRequired<\"waiters\">(\"waiters\")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<\"id\">(\"id\")(a4), a1)), append(a3, cons(a4, nil())), a3)))))"
-- The printed types of the cell and of a waiter.
#guard (Effect4.Codegen.Types.ofTy Semaphore.cellTy).map (TypeScript.Render.type house0) = some
  "{ readonly next: number; readonly permits: number; readonly taken: number; readonly waiters: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never>; readonly need: number; readonly stamp: number }> }"
#guard (Effect4.Codegen.Types.ofTy Semaphore.waiterTy).map (TypeScript.Render.type house0) = some
  "{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never>; readonly need: number; readonly stamp: number }"

end Test.Program.SemaphoreFaces
