import Test.Program.QueueScenarios
import Effect4.Codegen.ListFold
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.PrintReadable
import TypeScript.Render

/-!
# The faces of the Queue's steps: what prints and reads back today (decisions row 255)

Seat T5's part A and the first step of its part B are in the tree. An operation's binder term
prints as a function of the cell's current value, `Ref.modify(cell, (s) => …)`, and reads back.
`Deferred.make`'s type arguments print from the operation and read back. A loop that states its
cursor's type prints, and the module reader refuses it (DI-91): seat T5's next step. So:

- **Each scenario prints as a module, and the reader refuses it by name.** Each of the eight
  scenarios of `Test/Program/QueueScenarios.lean` takes, and the take's loop states its
  cursor's type. The reader's refusal is `annotation "local const"`. Both answers are pinned.
- **A program that only offers prints and reads back**: it makes two `Deferred` handles and
  states no cursor type.
- **Each of the six step terms prints and reads back alone**: one `Ref.modify` over the step,
  on a cell and handles that the node receives as bound values. The size step is a term over
  the value of a `Ref.get`.
- **A step that needs no handle prints as a whole module** and reads back: the poll step and
  the size step, on a cell that the program makes with `Ref.make`.

Each row here fixes the name `s` for the cell's current value. Every other term under that
binder is this battery's own variable (addendum 2 of the seat's brief).

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on the
Queue's step terms. Every guard is one program. None states target typing or a host run. **A
printed step is not type-checked under tsgo here**: on the target, `pair` and `tuple` keep a
literal's type, and the take step's two arms then differ. The owner has not ruled on that
finding, so the check waits. The rendered bytes stay inside each guard.
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

/-! ## The scenarios' modules: printed, and refused by the reader by name -/

open Test.Program.QueueScenarios (offer take) in
/-- One offer into room, on a cell that the program makes. -/
def offerOnly : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let a ← offer .nat q (nat 1)
  return a

open Test.Program.QueueScenarios (offer take) in
/-- One take, on a cell that the program makes. -/
def takeOnly : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let a ← take .nat q
  return a

-- Each scenario's module prints: `Deferred.make`'s type arguments print from the operation.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map printVerdict = List.replicate 8 "printed"
-- The module reader refuses each, by name: the take's loop states its cursor's type, which
-- prints as an annotated local constant (DI-91).
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map readVerdict =
  List.replicate 8 "refused: annotation local const"
-- The refusal is the take's: a program that only takes has it, and a program that only offers
-- prints and reads back.
#guard printVerdict takeOnly = "printed" && readVerdict takeOnly = "refused: annotation local const"
#guard printVerdict offerOnly = "printed" && readVerdict offerOnly = "reads back"
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
