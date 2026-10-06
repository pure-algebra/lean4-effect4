import Test.Program.PoolPublic

/-!
# Twelve of Pool's runs on the generated engine: the fixture's binding (rows 267 to 269, 276 and 279)

The engine's test `ocaml/engine/test/pool/test_pool.ml` runs twelve programs on the generated
engine, on both carriers. Two are cases of `Test/Program/PoolScenarios.lean`, over that
battery's own test forms: PP4, and the low-level control of PP5. Ten are the public cases of
`Test/Program/PoolPublic.lean`, over the library's `make` and `use`. Each program crosses as its
canonical bytes. The fixture `ocaml/engine/test/pool/pool.txt` holds them, with the fuel and the
root's exit of Lean's machine. The writer is `write.lean`, in that folder.

This battery binds the committed fixture to the programs. Its whole text is the text that
`Test.Program.PoolPublic.fixtureText` computes: the bytes of the programs that
`Api.Author.build` admits, and the exits of Lean's machine at the fixture's fuel, in the
engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. The generated group `fixtures` closes that gap (`docs/GENERATED.md`): its marker
depends on the fixture itself, `make gen-fixtures` writes a changed fixture again from Lean,
and `make check-gen` refuses a committed fixture that Lean does not write.

Placement. A finite control of the proposed claim `pool-expansion-agrees` (concept
`translation-simulation`, requirement R10) on the lowered code: twelve runs, one schedule each,
the engine's own drive loop. The runs of PP7 and of the two closed pools are finite controls of
the proposed claim `pool-close-waits` (concept `scope-lifetime-finalization`, requirement R11)
on the lowered code. The battery states no agreement of the engine with the machine beyond the
root's exit and the two carriers' reports on these twelve programs. The control of PP5 is no
public schedule: its helper's count 2 is a premise. No run is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.PoolScenarios (fuel buildOf showVal showExit exitOf snap rows pp4Rows
  pp5controlRows probed atOnce pp5control)
open Test.Program.PoolPublic (engineRuns publicRuns publicNames fixtureText)

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/pool/pool.txt"

/-! Each guard below reads the committed text's lines itself: a battery definition over text
reaches `Classical.choice` (AGENTS.md, Trust). -/

-- The committed file is the text Lean writes: every run's name, fuel, bytes and exit.
#guard fixtureText = some committed

-- The fixture's shape: twelve runs, in the order of `engineRuns`, each at the one fuel. The
-- first two are the earlier runs, and the ten public cases follow under their names.
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "run ") =
  ["run pp4", "run pp5control"] ++ publicNames.map ("run " ++ ·)
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "run ") =
  engineRuns.map fun run => "run " ++ run.1
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "fuel ") =
  List.replicate 12 s!"fuel {fuel}"

-- Each exit line is the engine's spelling of the root's exit of Lean's machine. The first two
-- hold the snapshots of the cell and the log's rows of the first battery's forms.
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "exit ").take 2 =
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
      snap [] [0] [1] 0 false 2, rows pp4Rows])) =
  (exitOf (Test.Program.PoolScenarios.pp4 Test.Program.PoolScenarios.library)).bind showExit
#guard showExit (.success (.list
    [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3, rows pp5controlRows])) =
  (exitOf (pp5control probed atOnce)).bind showExit
-- The ten public exit lines are the answers that `Test/Program/PoolPublic.lean` pins, each in
-- the engine's spelling: the exit of the checked session on the case.
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "exit ").drop 2 =
  publicRuns.filterMap fun run => ((exitOf run.2).bind showExit).map ("exit " ++ ·)
#guard publicRuns.all fun run => ((exitOf run.2).bind showExit).isSome
-- Three of them in full. PP6: the failure is a present option. PP7: the finalizer's row
-- follows H's return, so the close waited. The closed pool: L's exit is a constructor's value,
-- and its cause names the fiber 1, which is L's own.
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "exit ")[7]? =
  some "exit success list[true,some 77,list[list[5],list[9,1]]]"
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "exit ")[8]? = some
  ("exit success list[list[list[],list[0],list[0],1,false,1],true,false," ++
    "list[list[0],list[],list[],0,true,1],list[list[1,9,1],list[8],list[2,9,1],list[9,1]]]")
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "exit ")[10]? = some
  ("exit success list[ctor 1 [ctor 0 [list[ctor 2 [some ctor 0 [1], ctor 0 [list[]]]]]]," ++
    "list[list[0],list[],list[],0,true,0],list[list[9,1]]]")

-- The bytes read back as the program: the wire's round trip on the twelve programs.
#guard engineRuns.all fun run => (buildOf run.2).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding. The twelve programs are twelve byte strings, and the fixture
-- holds no thirteenth program. The twelve runs answer twelve exits, so a swapped run fails the
-- first guard.
#guard ((engineRuns.filterMap fun run => (buildOf run.2).map Wire.hexOf).eraseDups).length = 12
#guard (((committed.splitOn "\n").filter fun line => line.startsWith "exit ").eraseDups).length =
  12
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 12
-- A value with no spelling here is refused, never spelled loosely: a handle, a list that holds
-- one, the unit and an empty option. No run of the fixture holds one of them, so the engine's
-- test would check no spelling of it.
#guard showVal (Val.promise ⟨1⟩) = none && showVal (.list [.nat 1, Val.promise ⟨1⟩]) = none &&
  showVal .unit = none && showVal .none = none
-- A present option and a constructor's value have the spellings that the three runs hold.
#guard showVal (.some (.nat 77)) = some "some 77" &&
  showVal (.ctor 0 [.nat 1, .bool true]) = some "ctor 0 [1, true]"

end Test.Program.PoolEngine
