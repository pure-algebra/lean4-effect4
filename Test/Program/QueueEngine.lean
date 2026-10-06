import Test.Program.QueueMask
import Effect4.Store.Domain.ProgramWire

/-!
# Five of the Queue's programs on the generated engine: the fixture's binding (row 255)

The engine's test `ocaml/engine/test/queue/test_queue.ml` runs five programs over the library's
operations on the generated engine, on both carriers: the scenarios R1, R4, R2 and R5 of
`Test/Program/QueueScenarios.lean`, and the masked caller of `Test/Program/QueueMask.lean`. In
R2 a taker waits and an offer wakes it. In R5 a waiting taker is interrupted. Each program
crosses as its canonical bytes. The fixture `ocaml/engine/test/queue/queue.txt` holds them, with
the fuel and the root's exit of Lean's machine. The writer is `write.lean`, in that folder.

This battery binds the committed fixture to the programs: its bytes are the bytes of the
programs that `Api.Author.build` admits, and its exits are the exits of Lean's machine at the
fixture's fuel, in the engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. The generated group `fixtures` closes that gap (`docs/GENERATED.md`): its marker
depends on the fixture itself, `make gen-fixtures` writes a changed fixture again from Lean,
and `make check-gen` refuses a committed fixture that Lean does not write.

Placement. A finite control of the proposed claim `queue-expansion-agrees` (concept
`translation-simulation`, requirement R10) on the lowered code: five runs, one schedule each,
the engine's own drive loop. It states no agreement of the engine with the machine beyond the
root's exit and the two carriers' reports on these five programs, and no host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.QueueScenarios (r1 r2 r4 r5 mk)
open Test.Program.QueueMask (maskedCaller)

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/queue/queue.txt"

/-- The fixture's fuel. -/
def fuel : Nat := 20000

def build (src : Authoring.Src NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build (mk src)).toOption.map (·.program)

/-- The fixture's runs, in its order: each name with its source. -/
def runs : List (String × Authoring.Src NativeOp) :=
  [("r1", r1), ("r4", r4), ("r2", r2), ("r5", r5), ("masked", maskedCaller)]

-- The fixture's shape: five runs, each with its fuel, one program and one exit.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "run ") =
  runs.map fun run => "run " ++ run.1
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "fuel ") =
  List.replicate 5 s!"fuel {fuel}"
-- Each program line is the canonical bytes of the program that the build admits.
#guard (runs.mapM fun run => (build run.2).map fun p => "program " ++ Wire.hexOf p) =
  some ((committed.splitOn "\n").filter fun line => line.startsWith "program ")
-- Each exit line is the engine's spelling of the root's exit of Lean's machine.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "exit ") =
  ["exit success list[true,true,1,2]", "exit success list[true,1,true,2]", "exit success 7",
   "exit success list[5,0]", "exit success list[1,9,true,0,0]"]
#guard (runs.map fun run => (build run.2).map fun p => (Api.run p fuel).exit) =
  [ some (some (.success (.list [.bool true, .bool true, .nat 1, .nat 2])))
  , some (some (.success (.list [.bool true, .nat 1, .bool true, .nat 2])))
  , some (some (.success (.nat 7)))
  , some (some (.success (.list [.nat 5, .nat 0])))
  , some (some (.success (.list [.nat 1, .nat 9, .bool true, .nat 0, .nat 0]))) ]
-- The bytes read back as the program: the wire's round trip on these five programs.
#guard runs.all fun run => (build run.2).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding: the five programs are five byte strings, and the fixture holds
-- no sixth program.
#guard ((runs.mapM fun run => (build run.2).map Wire.hexOf).map fun bytes =>
  bytes.eraseDups.length) = some 5
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 5

end Test.Program.QueueEngine
