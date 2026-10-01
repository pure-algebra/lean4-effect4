import Effect4.Codegen.Types

/-! RED CONTROL for `HandleSpellings.lean`: asserts that the legacy grammar reads an object type
inside a generic handle. It must fail at that `#guard` and nowhere else. -/

open Effect4.Codegen.Types

#guard (parseLegacy "Chunk.Chunk<number>").isSome
#guard (parseLegacy "Queue.Dequeue<{ readonly id: number }>").isSome
