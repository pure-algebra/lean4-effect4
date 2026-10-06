import Test.Dogfood.Scenario

/-!
# Test.Dogfood.Scenario.Gate — controls of the scenario gate

`#scenario_gate` (`Test/Dogfood/Scenario.lean`) refuses a record that says more than its
declarations give. This battery runs the gate once over nine fixture records: two that it
accepts, and seven that it refuses by name.

The fixtures name the driver's declarations and the law graph's. Seven of the nine stand on a
claim that is a planned goal: its node costs no walk of the proof graph. That goal is this
battery's own, `Fixture.pending`. A scenario's goal cannot serve: it stops being a goal when it
is proved, as the driver's `tape_replays` did. This module is no root of the semantics report
(`tools/Tools/SemanticsRegistry.lean`), so the plan does not show the fixture goal.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4

namespace Fixture

/-- The gate's own planned goal. It states nothing of a program and nothing uses it: the
fixtures below need a claim that rests on a goal. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal pending : True


/-- A green control and a red control of an entry, both constant. -/
def both (entry : String) : List Control :=
  [green entry "a run the entry allows" true, red entry "a fault" true]

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

/-- Red control: a law that is a battery's theorem with no placement. -/
def unplaced : Scenario :=
  { planned with name := "unplaced", laws := [⟨"inert", ``play_id⟩]
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
    controls := [green "machine" "a run the clause allows" true, red "inert" "a fault" true,
      red "other" "a stray run" true, green "machine" "a false run" false] }

end Fixture

-- One run of the gate over the nine fixtures, on one plan. The green control is that no finding
-- names `sound` or `planned`; each red control is one finding or more, by its fixture's name.
/--
error: wrongTop: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "replay" (Effect4.Run.journal_replays)
unresolved: Nowhere.program does not resolve to a declaration
noTheorem: the claim Test.Dogfood.Scenario.play is no theorem and no planned goal
unplaced: the claim Test.Dogfood.Scenario.play_id has no placement at a requirement
unplacedLaw: the claim Effect4.Run.step_id has no placement: no semantics attribute and no row of the semantics registry
unlisted: the claim Test.Dogfood.Scenario.Fixture.pending rests on the planned goal Test.Dogfood.Scenario.Fixture.pending, which no clause names
loose: the clause "machine" has no red control
loose: the law "inert" has no green control
loose: the control "a stray run" names no clause and no law
loose: the control "a false run" fails
-/
#guard_msgs (error) in
#scenario_gate Fixture.sound Fixture.wrongTop Fixture.planned Fixture.unresolved Fixture.noTheorem
  Fixture.unplaced Fixture.unplacedLaw Fixture.unlisted Fixture.loose

#guard Fixture.sound.problems = [] && Fixture.planned.problems = []

end Test.Dogfood.Scenario
