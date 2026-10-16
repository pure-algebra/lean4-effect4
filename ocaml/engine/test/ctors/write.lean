import Test.Codegen.ConstructorLane

/-!
The writer of the constructor lane's fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Codegen.ConstructorLane`:

    lake env lean --run ocaml/engine/test/ctors/write.lean

It writes `ctors.txt` beside this file, or into the folder that its one argument names. The text
is `Test.Codegen.ConstructorLane.fixtureText`; `test_ctors.ml`, beside this file, reads it.
-/

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/ctors"
  IO.FS.writeFile s!"{folder}/ctors.txt" Test.Codegen.ConstructorLane.fixtureText
  IO.println s!"wrote {folder}/ctors.txt"
  return 0
