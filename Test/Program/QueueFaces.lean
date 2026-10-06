import Test.Program.QueueScenarios
import Effect4.Codegen.ListFold
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.PrintReadable
import TypeScript.Render

/-!
# The faces of the Queue's steps: what prints and reads back today (decisions row 255)

Seat T5's part A and the first two steps of its part B are in the tree. An operation's binder
term prints as a function of the cell's current value, `Ref.modify(cell, (s) => …)`, and reads
back. `Deferred.make`'s type arguments print from the operation and read back. A loop's stated
cursor type reads back through the checked type reader, on the readable types
(`Classes.ReadableTy`, DI-91). So:

- **Each scenario prints as a module and reads back.** Each of the eight scenarios of
  `Test/Program/QueueScenarios.lean` takes, and the take's loop states its cursor's type. The
  module reader gives the built program back. Both answers are pinned.
- **A program that only takes prints and reads back, and so does a program that only offers.**
  The second makes two `Deferred` handles and states no cursor type.
- **Each of the six step terms prints and reads back alone**: one `Ref.modify` over the step,
  on a cell and handles that the node receives as bound values. The size step is a term over
  the value of a `Ref.get`.
- **A step that needs no handle prints as a whole module** and reads back: the poll step and
  the size step, on a cell that the program makes with `Ref.make`.

Each row here fixes the name `s` for the cell's current value. Every other term under that
binder is this battery's own variable (addendum 2 of the seat's brief).

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on the
Queue's step terms. Every guard is one program. None states target typing or a host run. **Each
printed step is type-checked under tsgo 7 by the truth lane, not here**: the compiler control
`harness/truth/queue-steps.typecheck.ts` copies the six texts that the section "The texts that
the compiler control copies" pins, each at the cell's printed type. The compiler accepts each of
the six, and it accepted each before the literal rule of decisions row 256 too: that rule's
difference was in the readiness probe's take step and in the rate limiter's request, not in
this module's steps (seat T5's measure). A scenario's whole module is type-checked by no lane
yet. The rendered bytes stay inside each guard.
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

-- Each scenario's module prints: `Deferred.make`'s type arguments print from the operation.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map printVerdict = List.replicate 8 "printed"
-- Each reads back as the built program: the take's loop states its cursor's type, and the
-- checked type reader reads it (DI-91; the state plan's T5, part B). Before that step the
-- module reader refused each by name, `annotation "local const"`.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map readVerdict = List.replicate 8 "reads back"
-- A program that only takes reads back, and so does a program that only offers.
#guard printVerdict takeOnly = "printed" && readVerdict takeOnly = "reads back"
#guard printVerdict offerOnly = "printed" && readVerdict offerOnly = "reads back"
-- Red control of the comparison: a scenario's module reads as that scenario's program, and as
-- no other scenario's.
#guard readsAs r1 r1 && readsAs r4 r4 && !readsAs r1 r4 && !readsAs r4 r1
-- The smallest program that makes a request's identity prints and reads back.
#guard printVerdict (bindName "id" (Deferred.make .unit .never) fun _ => succeed (nat 1)) =
  "printed"
#guard readVerdict (bindName "id" (Deferred.make .unit .never) fun _ => succeed (nat 1)) =
  "reads back"

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
