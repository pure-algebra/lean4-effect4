import Test.Dogfood.Scenario.Tape

/-!
The writer of the scenario fixtures. `make gen-fixtures` runs it, with every other lane's
writer (`scripts/generate.py --only fixtures`, the group `fixtures` of `docs/GENERATED.md`).
Alone, run it from the repository's root, after a build of `Test.Dogfood.Scenario.Tape`:

    lake env lean --run ocaml/engine/test/scenarios/write.lean

It writes each fixture of `Test.Dogfood.Scenario.Lowered.fixtures` beside this file, or into
the folder that its one argument names. The battery `Test/Dogfood/Scenario/Lowered.lean` binds
each committed file to the text written here, and `test_scenarios.ml`, beside this file, reads
the files.

The writer refuses, and writes nothing, when the lane's names are not in order
(`Test.Dogfood.Scenario.Lowered.findings`): a name that the lane takes and its record does not
list, or an own run of the lane that carries the name of a record's run. So one name has one
script on every lane.
-/

def main (args : List String) : IO UInt32 := do
  let folder := args.head?.getD "ocaml/engine/test/scenarios"
  let findings := Test.Dogfood.Scenario.Lowered.findings
  unless findings.isEmpty do
    for finding in findings do
      IO.eprintln s!"write.lean: {finding}"
    return 1
  match Test.Dogfood.Scenario.Lowered.fixtureTexts with
  | none =>
    IO.eprintln "write.lean: a tape holds a decision the fixture format does not carry"
    return 1
  | some all =>
    for (file, text) in all do
      IO.FS.writeFile s!"{folder}/{file}" text
      IO.println s!"wrote {folder}/{file}"
    return 0
