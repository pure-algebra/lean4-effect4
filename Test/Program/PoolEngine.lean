import Test.Program.PoolScenarios

/-!
# Two of Pool's cases on the generated engine: the fixture's binding (rows 267 to 269)

The engine's test `ocaml/engine/test/pool/test_pool.ml` runs two cases of
`Test/Program/PoolScenarios.lean` on the generated engine, on both carriers: PP4, and the
low-level control of PP5. Each program crosses as its canonical bytes. The fixture
`ocaml/engine/test/pool/pool.txt` holds them, with the fuel and the root's exit of Lean's
machine. The writer is `write.lean`, in that folder.

This battery binds the committed fixture to the programs. Its whole text is the text that
`Test.Program.PoolScenarios.fixtureText` computes: the bytes of the programs that
`Api.Author.build` admits, and the exits of Lean's machine at the fixture's fuel, in the
engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. The generated group `fixtures` closes that gap (`docs/GENERATED.md`): its marker
depends on the fixture itself, `make gen-fixtures` writes a changed fixture again from Lean,
and `make check-gen` refuses a committed fixture that Lean does not write.

Placement. A finite control of the proposed claim `pool-expansion-agrees` (concept
`translation-simulation`, requirement R10) on the lowered code: two runs, one schedule each,
the engine's own drive loop. It states no agreement of the engine with the machine beyond the
root's exit and the two carriers' reports on these two programs. The control of PP5 is no
public schedule: its helper's count 2 is a premise. No run is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.PoolScenarios

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/pool/pool.txt"

-- The committed file is the text Lean writes: every run's name, fuel, bytes and exit.
#guard fixtureText = some committed

-- The fixture's shape: two runs, in the order of `engineRuns`, each at the one fuel.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "run ") =
  ["run pp4", "run pp5control"]
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "fuel ").all
  (· == s!"fuel {fuel}")

-- Each exit line is the engine's spelling of the root's exit of Lean's machine: the snapshots
-- of the cell, and the log's rows.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "exit ") =
  ["exit success list[list[list[],list[0],list[0],2,false,1]," ++
      "list[list[0],list[],list[],2,false,1],list[list[0],list[],list[],1,false,1]," ++
      "list[list[],list[0],list[1],0,false,2]," ++
      "list[list[1,9,1,0],list[2,9,1,0],list[4,2],list[1,2,1,1]]]",
   "exit success list[false,list[list[0],list[],list[],2,false,1]," ++
      "list[list[],list[0],list[2],0,false,3]," ++
      "list[list[3,1,2],list[5,1,0,0],list[4,1],list[1,1,1,1],list[2,1,1,1],list[4,2]," ++
      "list[1,2,1,2]]]"]
-- They are the profile's answers of the scenarios battery, in that spelling.
#guard showExit (.success (.list
    [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1,
      snap [] [0] [1] 0 false 2, rows pp4Rows])) = (exitOf (pp4 library)).bind showExit
#guard showExit (.success (.list
    [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3, rows pp5controlRows])) =
  (exitOf (pp5control probed atOnce)).bind showExit
#guard ((exitOf (pp4 library)).bind showExit).isSome &&
  ((exitOf (pp5control probed atOnce)).bind showExit).isSome

-- The bytes read back as the program: the wire's round trip on the two programs.
#guard engineRuns.all fun (_, src) => (buildOf src).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding. The two programs are two byte strings, and the fixture holds
-- no third program. The two runs answer two exits, so a swapped run fails the first guard.
#guard ((engineRuns.filterMap fun (_, src) => (buildOf src).map Wire.hexOf).eraseDups).length = 2
#guard exitOf (pp4 library) != exitOf (pp5control probed atOnce)
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 2
-- A value with no spelling here is refused, never spelled loosely: a handle, and a list that
-- holds one.
#guard showVal (Val.promise ⟨1⟩) = none && showVal (.list [.nat 1, Val.promise ⟨1⟩]) = none

end Test.Program.PoolEngine
