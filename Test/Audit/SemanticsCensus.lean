import Effect4.Laws.Auto.Semantics
import ProofGraph.Goal
import ProofGraph.Sketch

namespace Test.Audit.SemanticsCensus

@[semantics "fixture-one"] theorem firstWitness : True := True.intro
@[semantics "fixture-two"] theorem secondWitness : 1 = 1 := rfl
theorem untaggedWitness : True := True.intro
-- An authored name that begins with `eq_` is counted: the population is decided by Lean's own
-- auxiliary predicates (`ProofGraph.isAuxiliary`), not by spelling.
theorem eq_cata : True := True.intro

-- The attribute keyword stays available as an ordinary identifier.
def semantics : Nat := 1
#guard semantics == 1

/-- error: semantics: expected a nonempty kebab-case concept id -/
#guard_msgs (error) in
attribute [semantics "Not a concept"] untaggedWitness

/-- error: semantics: Test.Audit.SemanticsCensus.firstWitness already has a concept -/
#guard_msgs (error) in
attribute [semantics "other-concept"] firstWitness

/-- error: Cannot add attribute `[semantics]` to declaration `Nat.add_comm` because it is in an imported module -/
#guard_msgs (error) in
attribute [semantics "fixture-one"] Nat.add_comm

/-- error: semantics census: module Missing.Semantic.Module is not loaded -/
#guard_msgs (error) in
#semantics_census Missing.Semantic.Module

/--
info: semantics census
fixture-one	Test.Audit.SemanticsCensus.firstWitness	theorem	#[]
fixture-two	Test.Audit.SemanticsCensus.secondWitness	theorem	#[]
untagged: 2 theorems in 1 modules (universe: Test.Audit.SemanticsCensus)
Test.Audit.SemanticsCensus	Test.Audit.SemanticsCensus.eq_cata
Test.Audit.SemanticsCensus	Test.Audit.SemanticsCensus.untaggedWitness
-/
#guard_msgs in
#semantics_census Test.Audit.SemanticsCensus

-- Planned-goal fixtures (decisions row 203), loaded by the separate report driver
-- (`tools/Drivers/SemanticsControls.lean`); they follow the census snapshot.
/-- an open planned goal -/
proof_goal wantedGoal : True
/-- a theorem that rests on the goal: proved modulo `wantedGoal` -/
theorem restingWitness : True ∧ True := ⟨wantedGoal, True.intro⟩
-- a sketch: proved modulo its two parts, which no requirement of the controls reaches
/--
info: Test.Audit.SemanticsCensus.sketchedGoal: proved modulo 2 part(s)
proof_goal sketchedGoal.part1 : True
proof_goal sketchedGoal.part2 : True
-/
#guard_msgs in
proof_sketch sketchedGoal : True ∧ True := by
  refine ⟨?_, ?_⟩

end Test.Audit.SemanticsCensus
