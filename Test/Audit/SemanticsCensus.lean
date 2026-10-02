import Effect4.Laws.Auto.Semantics
import ProofGraph.Ledger

namespace Test.Audit.SemanticsCensus

@[semantics "fixture-one"] theorem firstWitness : True := True.intro
@[semantics "fixture-two"] theorem secondWitness : 1 = 1 := rfl
theorem untaggedWitness : True := True.intro

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
untagged: 1 theorems in 1 modules (universe: Test.Audit.SemanticsCensus)
Test.Audit.SemanticsCensus	Test.Audit.SemanticsCensus.untaggedWitness
-/
#guard_msgs in
#semantics_census Test.Audit.SemanticsCensus

-- Ledger fixtures loaded by the separate report driver; they follow the census snapshot.
theorem checkedGoal : ProofGraph.Obligation True := ⟨⟩
theorem checkedGoal.checked : True := True.intro
theorem wantedGoal : ProofGraph.Obligation True := ⟨⟩
def wantedGoal.wanted : ProofWanted True := ⟨⟩
theorem missingGoal : ProofGraph.Obligation True := ⟨⟩
theorem bothGoal : ProofGraph.Obligation True := ⟨⟩
theorem bothGoal.checked : True := True.intro
def bothGoal.wanted : ProofWanted True := ⟨⟩
theorem wrongCheckedGoal : ProofGraph.Obligation False := ⟨⟩
theorem wrongCheckedGoal.checked : True := True.intro
theorem wrongWantedGoal : ProofGraph.Obligation True := ⟨⟩
def wrongWantedGoal.wanted : ProofWanted False := ⟨⟩

end Test.Audit.SemanticsCensus
