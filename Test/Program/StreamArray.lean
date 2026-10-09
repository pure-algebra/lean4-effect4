import Effect4.Author
import Effect4.Run
import Effect4.Library.Stream.ArrayDefs
import Effect4.Laws.Library.Stream.Array

/-! Readers and finite controls for streams constructed from stored arrays.
The public authoring interface checks and runs inline and definition-backed sources.
The observations retain emitted batches, clean ends and the next pending array.
These controls establish no whole-run, schedule or outside-runtime theorem. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.StreamArray
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Schema Effect4.Schema.Model

/-- Observe a finite checked module through the public running interface. -/
def runModule (m : Module NativeOp) : Option ExitV :=
  (Api.Author.build m).toOption.bind fun built => (Api.run built.program 2000).exit

/-- The numeric instance tests the shared module construction command. -/
def numbers : Stream.ArrayDefinitions := Stream.ArrayDefinitions.make "arrays" .nat

/-- A concrete definition-backed source states its element type once. -/
def numericSource (items : TermSrc) : Stream.Source :=
  { elem := .nat, done := .unit
    opened := numbers.openArray items, pull := numbers.pull, close := numbers.close }

/-- This tests the existing Source metadata boundary without a new public helper. -/
def mismatchedSource (items : TermSrc) : Stream.Source :=
  { numericSource items with elem := .bool }

def input : TermSrc := listOf [nat 1, nat 2, nat 3]
def expected : Val := .list [.nat 1, .nat 2, .nat 3]

#guard runModule { main := Stream.runCollect (Stream.fromArray .nat input) } =
  some (.success expected)
#guard runModule { main := Stream.runCollect (Stream.fromArray .nat nilT) } =
  some (.success (.list []))
#guard runModule (numbers.module (Stream.runCollect (numericSource input))) =
  some (.success expected)
#guard runModule (numbers.module (Stream.runCollect (numericSource nilT))) =
  some (.success (.list []))

/-- Repeated pulls retain the clean ends and the cleared pending state. -/
def repeated : Src NativeOp :=
  bindWith (numbers.openArray input) fun receiver =>
    bindWith (numbers.pull receiver) fun first =>
      bindWith (numbers.pull receiver) fun second =>
        bindWith (numbers.pull receiver) fun third =>
          bindWith (Ref.get receiver) fun pending =>
            succeed (tuple [first, second, third, pending])

#guard runModule (numbers.module repeated) = some (.success (Val.tuple
  [Program.Stream.chunkVal [.nat 1, .nat 2, .nat 3],
   Program.Stream.endVal .unit, Program.Stream.endVal .unit, .list []]))

/-- The empty source never emits an empty Chunk. -/
def emptyPull : Src NativeOp :=
  bindWith (numbers.openArray nilT) fun receiver => numbers.pull receiver
#guard runModule (numbers.module emptyPull) =
  some (.success (Program.Stream.endVal .unit))
#guard Program.Stream.endVal .unit != Program.Stream.chunkVal []

/-- Two openings own separate pending cells. -/
def independent : Src NativeOp :=
  bindWith (numbers.openArray input) fun first =>
    bindWith (numbers.openArray input) fun second =>
      bindWith (numbers.pull first) fun a =>
        bindWith (numbers.pull second) fun b => succeed (tuple [a, b])
#guard runModule (numbers.module independent) = some (.success (Val.tuple
  [Program.Stream.chunkVal [.nat 1, .nat 2, .nat 3],
   Program.Stream.chunkVal [.nat 1, .nat 2, .nat 3]]))

/-- A caller's input retains its reading beneath the array source's internal binders. -/
def caller (name : String) : Src NativeOp :=
  bindName name (succeed input) fun items =>
    bindWith (Stream.runCollect (Stream.fromArray .nat items)) fun values =>
      succeed (tuple [values, items])
#guard ["current", "receiver", "batch", "items", "answer"].all fun name =>
  runModule { main := caller name } == some (.success (Val.tuple [expected, expected]))

-- Missing definitions are refused through public module admission.
#guard (Api.Author.build { main := numbers.pull (nat 0) }).toOption.isNone
-- A source declared numeric refuses string elements.
#guard (Api.Author.build (numbers.module (numbers.openArray (listOf [str "wrong"])))).toOption.isNone
-- A handle's payload type must match the declared instance.
#guard (Api.Author.build (numbers.module
  (bindWith (Ref.make (ascribe (.list .bool) (listOf [bool true]))) fun receiver =>
    numbers.pull receiver))).toOption.isNone
-- A conflicting source element annotation is refused when collection uses it.
#guard (Api.Author.build (numbers.module (Stream.runCollect
  (mismatchedSource input)))).toOption.isNone
-- Inline sources enforce the element declaration too.
#guard (Api.Author.build { main := (Stream.runCollect
  (Stream.fromArray .nat (listOf [str "wrong"]))) }).toOption.isNone

/-- The shared declaration checker refuses an incorrect answer column. -/
eff_module WrongArray where
  pull (receiver : Stream.arrayHandleTy .nat) : .nat := Stream.arrayPull .nat receiver
#guard (Api.Author.build ((WrongArray.make "wrong").module
  (succeed unit))).toOption.isNone

/-- Source metadata is authoring data; this consumer does not validate its element field. -/
def metadataMismatch : Src NativeOp := Stream.runForEach
  (mismatchedSource input) (fun item => succeed (app "succ" [item]))
#guard runModule (numbers.module metadataMismatch) = some (.success .unit)

-- The independent model retains the batch and the next pending state.
#guard Stream.ArrayModel.pull ([1, 2, 3] : List Nat) = ([1, 2, 3], [])
#guard Stream.ArrayModel.pull ([] : List Nat) = ([], [])
#guard Stream.ArrayModel.pull ([1, 2, 3] : List Nat) != ([1, 2, 3], [1, 2, 3])

/-- A real carrier reads the registered one-cell simulation statement. -/
example {env : Env} {path : List Nat} {vals : List Val} {receiver : TermSrc}
    {q : RefKey} {stores : Stores}
    (depth : vals.length = env.names.length)
    (reference : Reads receiver env path vals (Val.cell q))
    (held : refPeek stores.refs q = some (.list [.nat 1, .nat 2, .nat 3])) :=
  Stream.arrayStep_agrees .nat Leaves.deferredKeys ([1, 2, 3] : List Nat) depth reference held

/-- The numeric reader uses the shared typed callback connector. -/
example {table : RowTable} {receiver : TermSrc} {s : TypedScope}
    (reference : Typed (nativeSignature table) receiver s (.refOf (.list .nat))) :
    Answers (nativeSignature table) (Stream.arrayBatch .nat receiver) s (.list .nat) :=
  Stream.arrayBatch_answers .nat rfl (nodesFormed_of_check rfl) reference

end Test.Program.StreamArray
