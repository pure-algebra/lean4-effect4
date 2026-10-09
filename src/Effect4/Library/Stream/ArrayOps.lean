module

public import Effect4.Library.Stream.ArraySteps
public import Effect4.Library.Stream.Ops
public import Effect4.Program.Authoring.Ascribe

/-!
# A stream source from stored array data

Latest `vendor/effect-4.0.1/src/Stream.ts:1052-1053`, `fromArray`, emits its entire nonempty array once.
Latest `vendor/effect-4.0.1/src/Channel.ts:899` and `1139-1152`, `succeed` and `fromEffect`, supply the one-shot pull.
A Ref stores the pending list here, under decisions rows 331 and 335.
The atomic extraction uses the shared typed callback connector.
Clean completion remains the existing `End` value with `unit` leftover.
The source owns no foreign iterator, closure or second program representation.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Stream
open Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The implemented source uses Effect orchestration and Ref state (decisions row 335). -/
def arrayBuildingBlocks : List String := ["Effect", "Ref"]

/-- Allocate the pending array at its declared element type. -/
def arrayOpen (A : Ty) (items : TermSrc) : Src NativeOp :=
  Ref.make (ascribe (.list A) items)

/-- Atomically extract the pending batch and clear it. -/
def arrayBatch (A : Ty) (receiver : TermSrc) : Src NativeOp :=
  Step.callback (arrayStep A) arrayCaptures (Ref.modifyWith receiver)

/-- Emit a nonempty batch, or end immediately when no batch remains. -/
def arrayPull (A : Ty) (receiver : TermSrc) : Src NativeOp :=
  bindWith (arrayBatch A receiver) fun batch =>
    ifElse (isEmpty batch)
      (succeed (app "pair" [str "End", unit]))
      (succeed (app "pair" [str "Chunk", batch]))

/-- Close an array source; its Ref needs no external release. -/
def arrayClose (_receiver : TermSrc) : Src NativeOp := succeed unit

/-- A source that emits its stored array once, then ends with `unit`.
An empty array ends on its first pull. Each open allocates its own pending state. -/
def fromArray (A : Ty) (items : TermSrc) : Source :=
  { elem := A, done := .unit
    opened := arrayOpen A items
    pull := arrayPull A
    close := arrayClose }

end Effect4.Stream
