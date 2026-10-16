import Test.Dogfood.Scenario.Todo.HostLane

/-!
The writer of the to-do host lane's fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Dogfood.Scenario.Todo.HostLane`:

    lake env lean --run ocaml/engine/test/todo/write.lean

It writes `todo-host.txt` beside this file, or into the folder that its one argument names. The
text is `Test.Dogfood.Scenario.Todo.HostLane.fixtureText`; `test_todo.ml`, beside this file, reads
it. It writes nothing when a request of the script does not build.
-/

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/todo"
  match Test.Dogfood.Scenario.Todo.HostLane.fixtureText with
  | none =>
    IO.eprintln "write.lean: a request of the script does not build"
    return 1
  | some text =>
    IO.FS.writeFile s!"{folder}/todo-host.txt" text
    IO.println s!"wrote {folder}/todo-host.txt"
    return 0
