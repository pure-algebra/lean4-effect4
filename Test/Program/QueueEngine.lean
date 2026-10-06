import Test.Program.QueueScenarios
import Effect4.Store.Domain.ProgramWire

/-!
# Two of the Queue's scenarios on the generated engine: the fixture's binding (row 255)

The engine's test `ocaml/engine/test/queue/test_queue.ml` runs the scenarios R1 and R4 of
`Test/Program/QueueScenarios.lean` on the generated engine, on both carriers. Each program
crosses as its canonical bytes. The fixture `ocaml/engine/test/queue/queue.txt` holds them, with
the fuel and the root's exit of Lean's machine. The writer is `write.lean`, in that folder.

This battery binds the committed fixture to the programs: its bytes are the bytes of the
programs that `Api.Author.build` admits, and its exits are the exits of Lean's machine at the
fixture's fuel, in the engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. `lake env lean Test/Program/QueueEngine.lean` elaborates it afresh.

Placement. A finite control of the proposed claim `queue-expansion-agrees` (concept
`translation-simulation`, requirement R10) on the lowered code: two runs, one schedule each,
the engine's own drive loop. It states no agreement of the engine with the machine beyond the
root's exit and the two carriers' reports on these two programs, and no host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.QueueScenarios (r1 r4 mk)

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/queue/queue.txt"

/-- The fixture's fuel. -/
def fuel : Nat := 20000

def build (src : Authoring.Src NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build (mk src)).toOption.map (·.program)

-- The fixture's shape: two runs, each with its fuel, one program and one exit.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "run ") = ["run r1", "run r4"]
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "fuel ") =
  [s!"fuel {fuel}", s!"fuel {fuel}"]
-- Each program line is the canonical bytes of the program that the build admits.
#guard ((build r1).bind fun a => (build r4).map fun b =>
    (committed.splitOn "\n").filter (fun line => line.startsWith "program ") ==
      ["program " ++ Wire.hexOf a, "program " ++ Wire.hexOf b]) = some true
-- Each exit line is the engine's spelling of the root's exit of Lean's machine.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "exit ") =
  ["exit success list[true,true,1,2]", "exit success list[true,1,true,2]"]
#guard ((build r1).map fun p => (Api.run p fuel).exit) =
  some (some (.success (.list [.bool true, .bool true, .nat 1, .nat 2])))
#guard ((build r4).map fun p => (Api.run p fuel).exit) =
  some (some (.success (.list [.bool true, .nat 1, .bool true, .nat 2])))
-- The bytes read back as the program: the wire's round trip on these two programs.
#guard [r1, r4].all fun src => (build src).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding: the two programs are two byte strings, and the fixture holds
-- no third program.
#guard ((build r1).bind fun a => (build r4).map fun b => Wire.hexOf a != Wire.hexOf b) = some true
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 2

end Test.Program.QueueEngine
