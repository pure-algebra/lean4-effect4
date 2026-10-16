import Test.Codegen.ModeledLane

/-!
The writer of the Modeled lane's fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Codegen.ModeledLane`:

    lake env lean --run ocaml/engine/test/modeled/write.lean

It writes `modeled.txt` beside this file, or into the folder that its one argument names. The
text is `Test.Codegen.ModeledLane.fixtureText`; `test_modeled.ml`, beside this file, reads it.
-/

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/modeled"
  IO.FS.writeFile s!"{folder}/modeled.txt" Test.Codegen.ModeledLane.fixtureText
  IO.println s!"wrote {folder}/modeled.txt"
  return 0
