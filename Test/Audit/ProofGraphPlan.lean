import ProofGraph.Plan
import ProofGraph.Sketch
import Effect4.Laws.Program.Typed.Commands.Clauses.All

/-!
Controls of the planning graph with planned goals (`tools/ProofGraph/Plan.lean`, decisions row
203). A synthetic plan shows a theorem proved modulo two goals, then the same decomposition
proved, and the red controls pin each refusal:

1. a theorem that uses a goal is proved modulo it, never proved. The real case is `m7_of_ledger`
   with `LoadsTyped` proved by `loadsTyped` and `DecisionKeeps` a goal; with `decision_preserves`
   in its place, the same statement rests on one goal, `invoke_arm`: the typed run of an
   invocation with programs, which slice CX2 proves in place (decisions row 340);
2. a node whose axioms leave the semantic ceiling is refused;
3. a hand-written `sorry` is not a goal: the plan refuses it as an axiom outside the ceiling, and
   `tagGoal` refuses to tag a theorem whose body is not `sorry`, or a definition;
4. a sketch whose script reports an error, or closes its statement, is refused;
5. the dependency walk gives no answer from an unfinished stack: at a budget that cannot empty
   it, the walk says so, and `buildPlan` refuses such a walk.
-/
namespace Test.ProofGraphPlan
open Lean Meta Elab Command ProofGraph

def A (n : Nat) : Prop := n = n
def B (n : Nat) : Prop := n + 0 = n
def C (n : Nat) : Prop := A n ∧ B n

proof_goal leafA : ∀ n, A n
proof_goal leafB : ∀ n, B n
/-- The decomposition of `top`: an ordinary theorem whose proof uses the two goals. -/
theorem top (n : Nat) : C n := ⟨leafA n, leafB n⟩

/--
info: Test.ProofGraphPlan.top: modulo [Test.ProofGraphPlan.leafA, Test.ProofGraphPlan.leafB]; nearest [Test.ProofGraphPlan.leafB, Test.ProofGraphPlan.leafA]; 0 lemmas, 2 definitions
next goals: 2
  goal Test.ProofGraphPlan.leafA : ∀ (n : Nat), A n
  goal Test.ProofGraphPlan.leafB : ∀ (n : Nat), B n
-/
#guard_msgs in
#plan_status top

-- 5. The walk from `top` at one pop leaves its stack unfinished and gives no answer. At the
-- plan's own budget it answers the two goals, as the status above prints them.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let isNode (c : Name) : Bool := c == ``leafA || c == ``leafB || c == ``top
  let short ← walkWithin 1 [`Test] isNode ``top
  let whole ← walkWithin walkBudget [`Test] isNode ``top
  return short.isNone &&
    (whole.map fun w => w.1.size == 2 && w.1.contains ``leafA && w.1.contains ``leafB) == some true

-- The same decomposition over proved leaves is proved.
theorem provedA : ∀ n, A n := fun _ => rfl
theorem provedB : ∀ n, B n := fun _ => rfl
theorem provedTop (n : Nat) : C n := ⟨provedA n, provedB n⟩

/--
info: Test.ProofGraphPlan.provedTop: proved; nearest []; 2 lemmas, 2 definitions
next goals: 0
-/
#guard_msgs in
#plan_status provedTop

-- 1. The M7 route with `DecisionKeeps` as a goal: proved modulo that goal only.
open Effect4.Program.Typed in
proof_goal keeps (root : ProgramSource) (rootTy : Effect4.Program.EffTy) (fuel : Nat)
    (d : Effect4.Api.Decision) : DecisionKeeps root rootTy fuel d

open Effect4.Program.Typed in
theorem m7Modulo (root : ProgramSource) (rootTy : Effect4.Program.EffTy) (fuel : Nat)
    (tape : List Effect4.Api.Decision) :
    M7Exits root rootTy fuel tape ∧ M7Stores root rootTy fuel tape ∧
      M7NoHalt root rootTy fuel tape :=
  m7_of_ledger root rootTy fuel tape (loadsTyped root rootTy fuel fuel) (keeps root rootTy fuel)

run_cmd liftTermElabM do
  let plan ← buildPlan [`Test] #[``m7Modulo, ``Effect4.Program.Typed.m7_proved] (← IO.mkRef {})
  let said : Standing → String
    | .modulo goals => s!"modulo {goals}"
    | standing => standing.word
  let some node := plan.find? ``m7Modulo | throwError "m7Modulo is not a node"
  unless node.standing == .modulo #[``Effect4.Program.Typed.invoke_arm, ``keeps] do
    throwError "m7Modulo is {said node.standing}, not modulo [invoke_arm, keeps]"
  let some proved := plan.find? ``Effect4.Program.Typed.m7_proved | throwError "m7_proved is not a node"
  unless proved.standing == .modulo #[``Effect4.Program.Typed.invoke_arm] do
    throwError "m7_proved is {said proved.standing}, not modulo [invoke_arm]"
  unless plan.next #[``m7Modulo, ``Effect4.Program.Typed.m7_proved] ==
      #[``Effect4.Program.Typed.invoke_arm, ``keeps] do
    throwError "the next goals are not keeps and invoke_arm"

-- 2. A node outside the semantic ceiling is refused.
/-- error: plan: Classical.em: disallowed axioms [Classical.choice] -/
#guard_msgs (error) in
#plan_status Classical.em

-- 3. A hand-written `sorry` reaches `sorryAx` itself, which no ceiling admits; the declaration
-- is added inside a rolled-back state, so it never reaches the axiom gate.
/-- error: plan: Test.ProofGraphPlan.hand: disallowed axioms [sorryAx] -/
#guard_msgs (error) in
run_cmd liftTermElabM do
  withoutModifyingState do
    let p := mkConst ``True
    let value ← mkSorry p false
    withOptions (warn.sorry.set · false) do
      addDecl <| .thmDecl { name := `Test.ProofGraphPlan.hand, levelParams := [], type := p, value }
    discard <| buildPlan [`Test] #[`Test.ProofGraphPlan.hand] (← IO.mkRef {})

/-- error: goal: the body of Test.ProofGraphPlan.provedTop is not `sorry` -/
#guard_msgs (error) in
run_cmd liftTermElabM <| withoutModifyingState <| tagGoal ``provedTop

/-- error: goal: Test.ProofGraphPlan.A is not a theorem -/
#guard_msgs (error) in
run_cmd liftTermElabM <| withoutModifyingState <| tagGoal ``A

-- 4. Sketches: the holes become goals, and the theorem rests on them.
/--
info: Test.ProofGraphPlan.sketched: proved modulo 2 part(s)
proof_goal sketched.part1 : ∀ (n : Nat), A n
proof_goal sketched.part2 : ∀ (n : Nat), B n
-/
#guard_msgs in
proof_sketch sketched (n : Nat) : C n := by
  refine ⟨?_, ?_⟩

run_cmd liftTermElabM do
  let plan ← buildPlan [`Test] #[``sketched] (← IO.mkRef {})
  let some node := plan.find? ``sketched | throwError "sketched is not a node"
  unless node.standing == .modulo #[``sketched.part1, ``sketched.part2] do
    throwError "sketched is {node.standing.word}"

/--
error: sketch: the script reported an error: don't know how to synthesize placeholder for argument `right`
context:
n : Nat
⊢ B n
-/
#guard_msgs (error) in
proof_sketch broken (n : Nat) : C n := by
  exact ⟨?_, ?_⟩

/-- error: sketch: the script closes Test.ProofGraphPlan.direct; write it as a theorem -/
#guard_msgs (error) in
proof_sketch direct (n : Nat) : A n := by
  rfl

end Test.ProofGraphPlan
