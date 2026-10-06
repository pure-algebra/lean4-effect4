import Test.Program.PoolPublic

/-!
The writer of Pool's engine fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Program.PoolPublic`:

    lake env lean --run ocaml/engine/test/pool/write.lean

It writes `pool.txt` beside this file, or into the folder that its one argument names. The
text is `Test.Program.PoolPublic.fixtureText`: for each run of `engineRuns` there, the fuel,
the program's canonical bytes (`Effect4.Program.Wire.hexOf`) and the root's exit of Lean's
machine, in the spelling of the engine's `show_exit` (`ocaml/engine/e4_engine.ml`). The runs
are the two of `Test/Program/PoolScenarios.lean`, and then the ten public cases. The battery
`Test/Program/PoolEngine.lean` binds the committed file to that text, and `test_pool.ml`,
beside this file, reads it.
-/

open Test.Program.PoolPublic (fixtureText)

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/pool"
  match fixtureText with
  | some text =>
    IO.FS.writeFile s!"{folder}/pool.txt" text
    IO.println s!"wrote {folder}/pool.txt"
    return 0
  | none =>
    IO.eprintln "write.lean: a run does not build, does not finish, or answers a value with no spelling"
    return 1
