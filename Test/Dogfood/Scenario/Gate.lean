import Test.Dogfood.Scenario
import Effect4.Author
import Test.Audit.ScenarioGate

/-!
# Test.Dogfood.Scenario.Gate — controls of the scenario gate

`#scenario_gate` (`Test/Dogfood/Scenario.lean`) refuses a record that says more than its
declarations give. This battery runs the gate once over fourteen fixture records: three that it
accepts, and eleven that it refuses by name.

The fixtures name the driver's declarations and the law graph's. Twelve of the fourteen stand on
a claim that is a planned goal: its node costs no walk of the proof graph. That goal is this
battery's own, `Fixture.pending`. A scenario's goal cannot serve: it stops being a goal when it
is proved, as the driver's `tape_replays` did. This module is no root of the semantics report
(`tools/ProofGraph/Registry.lean`), so the plan does not show the fixture goal.

Five fixtures hold named runs. They play two scripts on the battery's own program, `tiny`, so
that the gate's part of a run is controlled here: it plays each named run, and it hands a
comparison the runs that the control names.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4

namespace Fixture

/-- The gate's own planned goal. It states nothing of a program and nothing uses it: the
fixtures below need a claim that rests on a goal. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal pending : True


/-- A green control and a red control of an entry, both constant: each reads no run. -/
def both (entry : String) : List Control :=
  [green entry "a run the entry allows" [] fun _ => true, red entry "a fault" [] fun _ => true]

/-- Green control. The claim is a placed theorem of this battery. Its proof uses the clause, a
law that the registry lists as a requirement's top node. Two laws stand beside it with controls
only: a placed theorem of this battery, and a theorem of a default module of the registry. -/
def sound : Scenario :=
  { name := "sound", program := ``play, observation := ``receipts, claim := ``replays
    clauses := [⟨"replay", ``Effect4.Run.journal_replays⟩]
    laws := [⟨"inert", ``receipt_inert⟩, ⟨"receipt", ``Effect4.Api.HostSession.submit_machine⟩]
    controls := both "replay" ++ both "inert" ++ both "receipt" }

/-- Red control: a claim whose proof does not use the record's clause. -/
def wrongTop : Scenario := { sound with name := "wrongTop", claim := ``receipt_inert }

/-- Green control. The claim is a planned goal, and the record names it as its one clause. -/
def planned : Scenario :=
  { name := "planned", program := ``play, observation := ``receipts, claim := ``pending
    clauses := [⟨"machine", ``pending⟩], controls := both "machine" }

/-- Red control: a program that names no declaration. -/
def unresolved : Scenario := { planned with name := "unresolved", program := `Nowhere.program }

/-- Red control: a claim that is a definition. -/
def noTheorem : Scenario := { planned with name := "noTheorem", claim := ``play }

/-- Red control: a law that is a battery's theorem with no placement. `play_opened` is a helper
of `replays` (`Test/Dogfood/Scenario.lean`), and it carries no `@[semantics …]`. -/
def unplaced : Scenario :=
  { planned with name := "unplaced", laws := [⟨"inert", ``play_opened⟩]
                 controls := both "machine" ++ both "inert" }

/-- Red control: a law of the law graph with no placement. `Effect4.Run.step_id` carries no
`@[semantics …]`, and no row of the registry names it or its module. -/
def unplacedLaw : Scenario :=
  { planned with name := "unplacedLaw", laws := [⟨"inert", ``Effect4.Run.step_id⟩]
                 controls := both "machine" ++ both "inert" }

/-- Red control: a claim that rests on a planned goal which no clause names. -/
def unlisted : Scenario :=
  { planned with name := "unlisted", clauses := [], laws := [⟨"inert", ``receipt_inert⟩]
                 controls := both "inert" }

/-- Red control: a clause with no red control, a law with no green control, a control of no
entry, and a control that fails. -/
def loose : Scenario :=
  { planned with
    name := "loose"
    laws := [⟨"inert", ``receipt_inert⟩]
    controls :=
      [ green "machine" "a run the clause allows" [] fun _ => true
      , red "inert" "a fault" [] fun _ => true
      , red "other" "a stray run" [] fun _ => true
      , green "machine" "a false run" [] fun _ => false ] }

/-! ### The named runs -/

/-- The gate's own program: its root answers 7 when the host starts it. -/
def tiny : Option Api.Built :=
  (Effect4.Api.Author.program (Program.Authoring.succeed (Program.Authoring.nat 7))).toOption

/-- Two named runs on `tiny`: the program opened and not started, and the program started. A
program that does not build leaves no run, and every fixture that reads one then fails. -/
def tinyRuns : List NamedRun :=
  match tiny with
  | some built => [⟨"opened", Run.open built "gate", []⟩, ⟨"started", Run.open built "gate", [.start]⟩]
  | none => []

/-- Whether a comparison got one run, and that run's root answered 7. -/
def answered : List Run → Bool
  | [run] => run.exit == some (.success (.nat 7))
  | _ => false

/-- Whether a comparison got one run, and that run's root has no exit. -/
def waiting : List Run → Bool
  | [run] => run.exit == none
  | _ => false

/-- Green control: each control reads a played run. The same comparison passes on the run that
the script started, and the other comparison passes on the run that no script moved. -/
def played : Scenario :=
  { planned with
    name := "played"
    runs := tinyRuns
    controls :=
      [ green "machine" "the started run answers" ["started"] answered
      , red "machine" "the opened run has no exit" ["opened"] waiting ] }

/-- Red control: the comparison of `played`'s green control, on the other run. The gate hands a
comparison the run that its control names, and no other. -/
def misread : Scenario :=
  { played with
    name := "misread"
    controls :=
      [ green "machine" "the opened run answers" ["opened"] answered
      , red "machine" "the started run has no exit" ["started"] waiting ] }

/-- Red control: a control that reads a run which the record does not list. The gate names the
run, and it does not judge the comparison. -/
def missingRun : Scenario :=
  { played with
    name := "missingRun"
    controls :=
      [ green "machine" "the finished run answers" ["started", "finished"] answered
      , red "machine" "the opened run has no exit" ["opened"] waiting ] }

/-- Red control: a record that lists one run's name twice. -/
def twiceListed : Scenario :=
  { played with name := "twiceListed", runs := tinyRuns ++ tinyRuns.take 1 }

/-- Red control: a named run that no control reads. A lane would perform it, and no control
would compare it. -/
def unread : Scenario :=
  { played with
    name := "unread"
    controls :=
      [ green "machine" "the started run answers" ["started"] answered
      , red "machine" "a fault" [] fun _ => true ] }

end Fixture

-- One run of the gate over the fourteen fixtures, on one plan. The green control is that no
-- finding names `sound`, `planned` or `played`. Each red control is one finding or more, by its
-- fixture's name.
/--
error: wrongTop: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "replay" (Effect4.Run.journal_replays)
unresolved: Nowhere.program does not resolve to a declaration
noTheorem: the claim Test.Dogfood.Scenario.play is no theorem and no planned goal
unplaced: the claim Test.Dogfood.Scenario.play_opened has no placement at a requirement
unplacedLaw: the claim Effect4.Run.step_id has no placement: no semantics attribute and no row of the semantics registry
unlisted: the claim Test.Dogfood.Scenario.Fixture.pending rests on the planned goal Test.Dogfood.Scenario.Fixture.pending, which no clause names
loose: the clause "machine" has no red control
loose: the law "inert" has no green control
loose: the control "a stray run" names no clause and no law
loose: the control "a false run" fails
misread: the control "the opened run answers" fails
misread: the control "the started run has no exit" fails
missingRun: the control "the finished run answers" reads the run "finished", which the record does not list
twiceListed: the record lists the run "opened" twice
unread: no control reads the run "opened"
-/
#guard_msgs (error) in
#scenario_gate Fixture.sound Fixture.wrongTop Fixture.planned Fixture.unresolved Fixture.noTheorem
  Fixture.unplaced Fixture.unplacedLaw Fixture.unlisted Fixture.loose Fixture.played
  Fixture.misread Fixture.missingRun Fixture.twiceListed Fixture.unread

#guard Fixture.sound.problems = [] && Fixture.planned.problems = [] && Fixture.played.problems = []

-- The lists that two findings are made from: a name listed twice, and a run that no control
-- reads. The record with the unread run has that one finding, and no other.
#guard Fixture.twiceListed.repeated = ["opened"] && Fixture.played.repeated = []
#guard Fixture.unread.unread = ["opened"] && Fixture.played.unread = []
#guard Fixture.unread.problems = ["unread: no control reads the run \"opened\""]

end Test.Dogfood.Scenario
