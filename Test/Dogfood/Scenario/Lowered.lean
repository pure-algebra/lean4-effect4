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
* **One name, one script.** A lowered run with the name of a record's run is that named run
  (`taken`, `Tape.lean`). Two controls hold the lane's names: the lane has its runs, and an own
  run that carries the name of a record's run is refused.

A fixture that is not the text Lean writes fails this battery, and `Tape.lean` still builds. So
the writer runs first, and this battery binds its files afterwards (`Test/Dogfood/README.md`).

The binding holds where this battery is elaborated. Lake does not see a fixture as an input: it
reads `include_str` as part of this file. So a fixture that changes alone does not rebuild the
battery, and `lake build` then binds nothing. The generated group `fixtures` closes that gap
(`docs/GENERATED.md`): its marker depends on the fixtures themselves, `make gen-fixtures` writes
a changed fixture again from Lean, and `make check-gen` refuses a committed fixture that Lean
does not write.

The host run of each scenario is not here: the keyed lane performs it
(`harness/truth/session/Keyed.lean`).
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
  , ("queue-workers.txt",
      include_str "../../../ocaml/engine/test/scenarios/queue-workers.txt")
  , ("routing.txt", include_str "../../../ocaml/engine/test/scenarios/routing.txt")
  , ("atomic.txt", include_str "../../../ocaml/engine/test/scenarios/atomic.txt")
  , ("timeout.txt", include_str "../../../ocaml/engine/test/scenarios/timeout.txt") ]

/-- The controls of the lane's names: one name has one script. The lane takes each run that a
record lists from the record, and it refuses an own run that carries the name of a record's run.
They stand outside the fixtures' match. So a lane that a name keeps from its fixtures fails
twice: at the control that the lane has its fixtures, and here, where the name is at fault. -/
def nameControls : List Control :=
  [ green "machine"
      "the lane's names are in order: each taken name is a record's run, and no own run carries one"
      [] fun _ => findings == []
  , red "machine" "an own run with the name of a record's run is refused, by that name"
      [] fun _ =>
        (Workers.scenario.run? "lowest").any fun run =>
          let clashing : Option (List (String × Lowered)) :=
            some [("workers.txt", ⟨"workers/lowest", run.opened, []⟩)]
          (fixturesOf clashing).isNone &&
            findingsOf clashing ==
              ["the name workers/lowest carries two scripts: an own run of the lane and a run of a record"] ]

/-- The controls of the machine clause. The four of the tapes read no named run of a record: the
lowered runs are the tape module's own table, `fixtures`, and `shownFixtures` plays each one. The
run at a small budget takes its program and its script from the workers record's run `lowest`. -/
def controls : List Control :=
  match shownFixtures, Workers.scenario.run? "lowest" with
  | some all, some lowest =>
    let runs := all.flatMap (·.2)
    let starved : Shown := Lowered.shown
      ⟨"workers/starved", Run.open lowest.opened.built "workers" { fuel := 7, compileFuel := 2000 },
        lowest.moves⟩
    [ green "machine"
        "every tape reads every row, and its raw replay shows the session machine at every position"
        [] fun _ => runs.all fun run => run.2.agrees
    , green "machine" "each committed fixture is the text Lean writes for the admitted programs"
        [] fun _ =>
          all.all fun entry => (committed.find? (·.1 == entry.1)).map (·.2) == fixture entry.2
    , red "machine"
        "a tape cut before its last decision that moves the view ends at another machine view"
        [] fun _ => runs.all fun run => run.2.lastCounts
    , red "machine" "a tape in which no decision moves the view does not pass: it is not skipped"
        [] fun _ =>
          let still := machineView lowest.opened
          let unmoved : Shown :=
            { positions := [], left := 0, views := [still, still, still]
              raw := [(.frontier, still), (.frontier, still), (.frontier, still)]
              observedTableDifference := false }
          unmoved.agrees && !unmoved.lastCounts
    , red "machine" "at a small budget the tape stops at the frontier and leaves the rows unread"
        [] fun _ => starved.left != 0 && !starved.agrees && starved.raw.map (·.2) == starved.views ]
      ++ nameControls
  | _, _ => green "machine" "the lane has its fixtures" [] (fun _ => false) :: nameControls

/-- The lowered runs as a scenario: its claim is the machine clause. Its record lists no named
run: the lane's runs are the tape module's table. -/
def scenario : Scenario :=
  { name := "lowered"
    program := ``fixtures
    observation := ``machineView
    claim := ``tape_replays
    clauses := [⟨"machine", ``tape_replays⟩]
    controls := controls }

#scenario_gate scenario

end Test.Dogfood.Scenario.Lowered
