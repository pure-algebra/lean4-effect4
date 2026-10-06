import Test.Program.MaskContract

/-!
The writer of the mask's engine fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Program.MaskContract`:

    lake env lean --run ocaml/engine/test/mask/write.lean

It writes `mask.txt` beside this file, or into the folder that its one argument names. The
text is `Test.Program.MaskContract.fixtureText`: for each run of `engineRuns` there, the fuel,
the program's canonical bytes (`Effect4.Program.Wire.hexOf`) and the root's exit of Lean's
machine, in the spelling of the engine's `show_exit` (`ocaml/engine/e4_engine.ml`). The battery
`Test/Program/MaskEngine.lean` binds the committed file to that text, and `test_mask.ml`,
beside this file, reads it.
-/

open Test.Program.MaskContract

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/mask"
  match fixtureText with
  | some text =>
    IO.FS.writeFile s!"{folder}/mask.txt" text
    IO.println s!"wrote {folder}/mask.txt"
    return 0
  | none =>
    IO.eprintln "write.lean: a run does not build, does not finish, or answers a value with no spelling"
    return 1
