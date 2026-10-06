import Test.Dogfood.Scenario.Tape

/-!
# The lowered runs: the machine's part of each scenario, bound to the engine's fixtures

`Test/Dogfood/Scenario/Tape.lean` holds what Lean writes for the machine clause of each scenario:
the lowered runs, their machine tapes and the fixture text. This battery binds that text to the
files that the engine's test reads, and holds the machine clause's controls and its record.

* **The binding.** The text of each fixture must be the committed file under
  `ocaml/engine/test/scenarios/`. `test_scenarios.ml`, in that folder, reads that file, decodes
  the table with `Eff_wire.decode_row_exact`, replays each prefix of the tape through the
  generated `api_replay` on both instances, and compares each view.
* **The Lean half of the machine clause.** At every position of every fixture the raw frame
  replay of the tape's prefix (`Api.replay`) shows the session machine's view: the finite
  controls of the theorem `tape_replays`.

A fixture that is not the text Lean writes fails this battery, and `Tape.lean` still builds. So
the writer runs first, and this battery binds its files afterwards (`Test/Dogfood/README.md`).

The binding holds where this battery is elaborated. Lake does not see a fixture as an input: it
reads `include_str` as part of this file. So a fixture that changes alone does not rebuild the
battery, and `lake build` then binds nothing. The generated group `fixtures` closes that gap
(`docs/GENERATED.md`): its marker depends on the fixtures themselves, `make gen-fixtures` writes
a changed fixture again from Lean, and `make check-gen` refuses a committed fixture that Lean
does not write.

The host run of each scenario is not here: it waits on the keyed lane.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Lowered

open Effect4 Effect4.Machine Effect4.Program

/-! ## 1. The controls -/

/-- The committed fixtures, read where this battery is elaborated. -/
def committed : List (String × String) :=
  [ ("workers.txt", include_str "../../../ocaml/engine/test/scenarios/workers.txt")
  , ("routing.txt", include_str "../../../ocaml/engine/test/scenarios/routing.txt")
  , ("atomic.txt", include_str "../../../ocaml/engine/test/scenarios/atomic.txt")
  , ("timeout.txt", include_str "../../../ocaml/engine/test/scenarios/timeout.txt") ]

/-- The controls of the machine clause. -/
def controls : List Control :=
  match shownFixtures, (Effect4.Api.Author.build (Workers.crew 2)).toOption with
  | some all, some crew =>
    let runs := all.flatMap (·.2)
    let starved : Shown := Lowered.shown
      ⟨"workers/starved", Run.open crew "workers" { fuel := 7, compileFuel := 2000 }, Workers.lowest⟩
    [ green "machine"
        "every tape reads every row, and its raw replay shows the session machine at every position"
        (runs.all fun run => run.2.agrees)
    , green "machine" "each committed fixture is the text Lean writes for the admitted programs"
        (all.all fun entry =>
          (committed.find? (·.1 == entry.1)).map (·.2) == fixture entry.2)
    , red "machine" "a tape without its last decision ends at another machine view"
        (runs.all fun run => run.2.lastCounts)
    , red "machine" "at a small budget the tape stops at the frontier and leaves the rows unread"
        (starved.left != 0 && !starved.agrees && starved.raw.map (·.2) == starved.views) ]
  | _, _ => [green "machine" "the scenarios' programs build" false]

/-- The lowered runs as a scenario: its claim is the machine clause. -/
def scenario : Scenario :=
  { name := "lowered"
    program := ``fixtures
    observation := ``machineView
    claim := ``tape_replays
    clauses := [⟨"machine", ``tape_replays⟩]
    controls := controls }

#scenario_gate scenario

end Test.Dogfood.Scenario.Lowered
