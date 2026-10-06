import Test.Dogfood.Scenario.Lowered

/-!
The writer of the scenario fixtures. Run it from the repository's root:

    lake env lean --run ocaml/engine/test/scenarios/write.lean

It writes each fixture of `Test.Dogfood.Scenario.Lowered.fixtures` beside this file. The battery
`Test/Dogfood/Scenario/Lowered.lean` binds each committed file to the text written here, and
`ocaml/engine/test/test_scenarios.ml` reads the files.
-/

def main : IO UInt32 := do
  match Test.Dogfood.Scenario.Lowered.fixtureTexts with
  | none =>
    IO.eprintln "write.lean: a program does not build, or a tape holds a decision the fixture format does not carry"
    return 1
  | some all =>
    for (file, text) in all do
      IO.FS.writeFile s!"ocaml/engine/test/scenarios/{file}" text
      IO.println s!"wrote ocaml/engine/test/scenarios/{file}"
    return 0
