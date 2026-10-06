import Test.Program.SemaphoreScenarios

/-!
# Three of Semaphore's cases on the generated engine: the fixture's binding (row 265)

The engine's test `ocaml/engine/test/semaphore/test_semaphore.ml` runs the cases P1, P3 and P9
of `Test/Program/SemaphoreScenarios.lean` on the generated engine, on both carriers. The
programs are over the library's operations (`src/Effect4/Modules/Semaphore/Ops.lean`). Each
program crosses as its canonical bytes. The fixture `ocaml/engine/test/semaphore/semaphore.txt`
holds them, with the fuel and the root's exit of Lean's machine. The writer is `write.lean`, in
that folder.

**P9 crosses with its tape as data.** P9 is P1's program under another tape: the root evaluated,
then the verdict that fiber 2 yields at its next check, then the flush. The fixture holds that
tape as one line of decisions, and the engine's test replays it. A run with no tape is the
engine's own drive loop.

This battery binds the committed fixture to the programs. Its whole text is the text that
`Test.Program.SemaphoreScenarios.fixtureText` computes: the bytes of the programs that
`Api.Author.build` admits, each tape's words, and the exits of Lean's machine at the fixture's
fuel, in the engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. The generated group `fixtures` closes that gap (`docs/GENERATED.md`): its marker
depends on the fixture itself, `make gen-fixtures` writes a changed fixture again from Lean,
and `make check-gen` refuses a committed fixture that Lean does not write.

Placement. A finite control of the proposed claim `semaphore-expansion-agrees` (concept
`translation-simulation`, requirement R10) on the lowered code: three runs, one schedule each.
The three are the finite controls of row 259's reading on the engine (concept
`reactive-scheduling`, requirement R12). It states no agreement of the engine with the machine
beyond the root's exit and the two carriers' reports on these runs. P9's tape is three
decisions: it is no law of the engine's replay. No run is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.SemaphoreScenarios

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/semaphore/semaphore.txt"

-- The committed file is the text Lean writes: every run's name, fuel, bytes and exit.
#guard fixtureText = some committed

-- The fixture's shape: three runs, in the order of `engineRuns`, each at the one fuel.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "run ") =
  ["run p1", "run p3", "run p9"]
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "fuel ").all
  (· == s!"fuel {fuel}")
-- One run holds a tape, the last: P9's three decisions, as words.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "tape ") =
  ["tape evaluate:0 yieldVerdict:2:true flush"]
#guard (engineRuns.map fun r => (r.name, r.tape.length)) = [("p1", 0), ("p3", 0), ("p9", 3)]

-- Each exit line is the engine's spelling of the root's exit of Lean's machine: the counts
-- before the release, the counts after the walk, and the marks.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "exit ") =
  ["exit success list[list[2,2,list[2,1],list[0,1]],list[2,1,list[1],list[1]],list[22]]",
   "exit success list[list[2,2,list[1,1],list[0,1]],list[2,1,list[1],list[1]],list[21,22]]",
   "exit success list[list[2,2,list[2,1],list[0,1]],list[1,1,list[2],list[2]],list[31]]"]
-- They are the pin's answers of the scenarios battery, in that spelling.
#guard showExit (.success (.list [count 2 [2, 1] [0, 1], count 2 [1] [1], marks [22]])) =
  some "success list[list[2,2,list[2,1],list[0,1]],list[2,1,list[1],list[1]],list[22]]"
#guard (exitOf p1).bind showExit =
  some "success list[list[2,2,list[2,1],list[0,1]],list[2,1,list[1],list[1]],list[22]]"
#guard (exitOf p3).bind showExit =
  some "success list[list[2,2,list[1,1],list[0,1]],list[2,1,list[1],list[1]],list[21,22]]"
-- P9: B yielded at its resume, C took 1, and B waits again with a new entry, the stamp 2.
#guard (exitOn yieldAtResume p1).bind showExit =
  some "success list[list[2,2,list[2,1],list[0,1]],list[1,1,list[2],list[2]],list[31]]"

-- The bytes read back as the program: the wire's round trip on the programs.
#guard engineRuns.all fun r => (buildOf r.src).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding. The three runs hold two programs: P9's bytes are P1's, and the
-- tape alone tells the two runs apart. The three runs answer three exits, so a swapped run
-- fails the first guard.
#guard ((engineRuns.filterMap fun r => (buildOf r.src).map Wire.hexOf).eraseDups).length = 2
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 3
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").eraseDups.length = 2
#guard ((engineRuns.map fun r => r.exitAt fuel).eraseDups).length = 3 &&
  (engineRuns.map fun r => r.exitAt fuel).all Option.isSome
-- A value with no spelling here is refused, never spelled loosely: a handle, and a list that
-- holds one.
#guard showVal (Val.promise ⟨1⟩) = none && showVal (.list [.nat 1, Val.promise ⟨1⟩]) = none

end Test.Program.SemaphoreEngine
