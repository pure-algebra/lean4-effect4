import Test.Program.MaskContract

/-!
# The mask on the generated engine: the fixture's binding (decisions rows 244 to 246)

The engine's test `ocaml/engine/test/mask/test_mask.ml` runs ten programs of
`Test/Program/MaskContract.lean` on the generated engine, on both carriers. Each program
crosses as its canonical bytes. The fixture `ocaml/engine/test/mask/mask.txt` holds them, with
the fuel and the root's exit of Lean's machine. The writer is `write.lean`, in that folder.

This battery binds the committed fixture to the programs. Its whole text is the text that
`Test.Program.MaskContract.fixtureText` computes: the bytes of the programs that
`Api.Author.build` admits, and the exits of Lean's machine at the fixture's fuel, in the
engine's spelling.

The binding holds where this battery is elaborated. Lake does not see the fixture as an input:
it reads `include_str` as part of this file. So a fixture that changes alone does not rebuild
the battery. The generated group `fixtures` closes that gap (`docs/GENERATED.md`): its marker
depends on the fixture itself, `make gen-fixtures` writes a changed fixture again from Lean,
and `make check-gen` refuses a committed fixture that Lean does not write.

Placement. A finite control of the claims `saved-mask-restoration` (concept
`scope-lifetime-finalization`, requirement R11) and `mask-printed-form-profile` (concept
`translation-simulation`, requirements R10 and R11) on the lowered code: ten runs, one
schedule each, the engine's own drive loop. It states no agreement of the engine with the
machine beyond the root's exit and the two carriers' reports on these ten programs, and no
host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.MaskEngine

open Effect4 Effect4.Machine Effect4.Program
open Test.Program.MaskContract

/-- The committed fixture, read where this battery is elaborated. -/
def committed : String := include_str "../../ocaml/engine/test/mask/mask.txt"

-- The committed file is the text Lean writes: every run's name, fuel, bytes and exit.
#guard fixtureText = some committed

-- The fixture's shape: ten runs, in the order of `engineRuns`, each at the one fuel.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "run ") =
  ["run s1", "run s2", "run s3", "run s4", "run s5inner", "run s5outer", "run s6", "run s7",
   "run s9", "run s10"]
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "fuel ").all
  (· == s!"fuel {fuel}")

-- Each exit line is the engine's spelling of the root's exit of Lean's machine. The saved
-- image crosses as its own frame, `ctor 7`, and never as a Boolean.
#guard (committed.splitOn "\n").filter (fun line => line.startsWith "exit ") =
  ["exit success list[ctor 7 [true],ctor 7 [false]]",
   "exit success list[true,1]",
   "exit success list[1,true,18]",
   "exit success list[true,111]",
   "exit success list[1,true,18]",
   "exit success list[1,true,1]",
   "exit success list[true,1]",
   "exit success list[ctor 7 [true],ctor 7 [true],ctor 7 [true],ctor 7 [false],ctor 7 [false]]",
   "exit success list[ctor 7 [false],ctor 7 [true],ctor 7 [true],ctor 7 [false],ctor 7 [false]]",
   "exit success list[ctor 7 [true],ctor 7 [false],ctor 7 [true]]"]

-- The bytes read back as the program: the wire's round trip on the ten programs, with the two
-- appended constructors in them.
#guard engineRuns.all fun (_, src) => (buildOf (mk src)).any fun p =>
  Wire.decodeProgram (Wire.encodeProgram p) = some p

-- Red controls of the binding. The ten programs are ten byte strings. The interrupted wait
-- and the masked caller's wait answer two exits, so a swapped run fails the first guard.
#guard ((engineRuns.filterMap fun (_, src) => (buildOf (mk src)).map Wire.hexOf).eraseDups).length = 10
#guard exitOf s2 != exitOf s3
#guard ((committed.splitOn "\n").filter fun line => line.startsWith "program ").length = 10

end Test.Program.MaskEngine
