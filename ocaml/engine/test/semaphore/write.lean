import Test.Program.SemaphoreScenarios

/-!
The writer of Semaphore's engine fixture. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Program.SemaphoreScenarios`:

    lake env lean --run ocaml/engine/test/semaphore/write.lean

It writes `semaphore.txt` beside this file, or into the folder that its one argument names. The
text is `Test.Program.SemaphoreScenarios.fixtureText`: for each run of `engineRuns` there, the
fuel, the run's tape when it has one, the program's canonical bytes
(`Effect4.Program.Wire.hexOf`) and the root's exit of Lean's machine, in the spelling of the
engine's `show_exit` (`ocaml/engine/e4_engine.ml`). A tape is one line of decisions, each a
word (`decisionWord`, in that battery). The battery `Test/Program/SemaphoreEngine.lean` binds
the committed file to that text, and `test_semaphore.ml`, beside this file, reads it.
-/

open Test.Program.SemaphoreScenarios

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/semaphore"
  match fixtureText with
  | some text =>
    IO.FS.writeFile s!"{folder}/semaphore.txt" text
    IO.println s!"wrote {folder}/semaphore.txt"
    return 0
  | none =>
    IO.eprintln "write.lean: a run does not build, does not finish, answers a value with no spelling, or holds a decision with no word"
    return 1
