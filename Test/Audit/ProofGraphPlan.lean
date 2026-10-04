import ProofGraph.Plan
import ProofGraph.Extract
import Effect4.Laws.Program.Typed.Commands.Clauses.All

/-!
Controls of the planning graph (`tools/ProofGraph/Plan.lean`). A synthetic plan walks one goal
from declared through reduced and ready to proved, and the red controls pin each refusal:

1. a reduction whose conclusion does not unify with its target;
2. a cycle among matched edges;
3. an edge that reaches an axiom outside the semantic ceiling, which the kernel alone accepts;
4. a loose premise, which is reported, keeps its target from being ready, and offers no closing
   command. The real case is `m7_of_ledger` with `LoadsTyped` matched by `loadsTyped` and
   `DecisionKeeps` left loose; with `decision_preserves` as a node too, the goal is ready, and
   the closing command applies the checked implication in full and publishes a kernel-checked
   proof.
-/
namespace Test.ProofGraphPlan
open Lean Meta Elab Command ProofGraph

def A (n : Nat) : Prop := n = n
def B (n : Nat) : Prop := n + 0 = n
def C (n : Nat) : Prop := A n ∧ B n

theorem leafA : Obligation (∀ n, A n) := ⟨⟩
theorem leafB : Obligation (∀ n, B n) := ⟨⟩
theorem top : Obligation (∀ n, C n) := ⟨⟩

/-- The reduction of `top` to its two leaves. -/
theorem top_of (a : ∀ n, A n) (b : ∀ n, B n) (n : Nat) : C n := ⟨a n, b n⟩

/--
info: Test.ProofGraphPlan.top: reduced
  via Test.ProofGraphPlan.top_of (checked)
    Test.ProofGraphPlan.leafA ⊢ ∀ (n : Nat), A n
    Test.ProofGraphPlan.leafB ⊢ ∀ (n : Nat), B n
Test.ProofGraphPlan.leafA: declared
Test.ProofGraphPlan.leafB: declared
next goals: [Test.ProofGraphPlan.leafA, Test.ProofGraphPlan.leafB]
-/
#guard_msgs in
#plan_status top via top_of for top

/-- error: plan: Test.ProofGraphPlan.top is reduced, not ready -/
#guard_msgs in
#obligation_close top via top_of for top

theorem leafA.checked : ∀ n, A n := fun _ => rfl
theorem leafB.checked : ∀ n, B n := fun _ => rfl

-- The printed closing command is the one run below: applied in full and kernel-checked.
/--
info: Test.ProofGraphPlan.top: ready
  via Test.ProofGraphPlan.top_of (checked)
    Test.ProofGraphPlan.leafA ⊢ ∀ (n : Nat), A n
    Test.ProofGraphPlan.leafB ⊢ ∀ (n : Nat), B n
Test.ProofGraphPlan.leafA: proved
Test.ProofGraphPlan.leafB: proved
next goals: [Test.ProofGraphPlan.top]
close Test.ProofGraphPlan.top with: #obligation_close Test.ProofGraphPlan.top via Test.ProofGraphPlan.top_of for Test.ProofGraphPlan.top
-/
#guard_msgs in
#plan_status top via top_of for top

#obligation_close top via top_of for top

/--
info: Test.ProofGraphPlan.top: proved
  via Test.ProofGraphPlan.top_of (checked)
    Test.ProofGraphPlan.leafA ⊢ ∀ (n : Nat), A n
    Test.ProofGraphPlan.leafB ⊢ ∀ (n : Nat), B n
Test.ProofGraphPlan.leafA: proved
Test.ProofGraphPlan.leafB: proved
next goals: []
-/
#guard_msgs in
#plan_status top via top_of for top

-- 1. A conclusion that does not unify with the target is refused.
theorem wrong_of (a : ∀ n, A n) (n : Nat) : A n := a n

/-- error: plan: the conclusion of Test.ProofGraphPlan.wrong_of does not unify with Test.ProofGraphPlan.top -/
#guard_msgs in
#plan_status top via wrong_of for top

-- 2. A cycle among matched edges is refused.
def P (n : Nat) : Prop := n = n
def Q (n : Nat) : Prop := n = n
theorem goalP : Obligation (∀ n, P n) := ⟨⟩
theorem goalQ : Obligation (∀ n, Q n) := ⟨⟩
theorem p_of (q : ∀ n, Q n) (n : Nat) : P n := q n
theorem q_of (p : ∀ n, P n) (n : Nat) : Q n := p n

/-- error: plan: cycle through [Test.ProofGraphPlan.goalP, Test.ProofGraphPlan.goalQ] -/
#guard_msgs in
#plan_status goalP via p_of for goalP, q_of for goalQ

-- 3. The kernel accepts this edge; the semantic ceiling refuses it. The premise is discharged by
-- the target's own hypothesis, and `Classical.byContradiction` reaches `Classical.choice`.
theorem classicalGoal : Obligation (∀ p : Prop, (¬p → False) → p) := ⟨⟩

/-- error: plan: the edge Classical.byContradiction → Test.ProofGraphPlan.classicalGoal reaches disallowed axioms [Classical.choice] -/
#guard_msgs in
#plan_status classicalGoal via Classical.byContradiction for classicalGoal

-- 4. A loose premise. A fixture goal states M7a–c; `m7_of_ledger` reduces it.
open Effect4.Program.Typed in
theorem m7Goal : Obligation (∀ (root : ProgramSource) (rootTy : Effect4.Program.EffTy) (fuel : Nat)
    (tape : List Effect4.Api.Decision),
    M7Exits root rootTy fuel tape ∧ M7Stores root rootTy fuel tape ∧
      M7NoHalt root rootTy fuel tape) := ⟨⟩

-- With only `loadsTyped` as a node, `DecisionKeeps` is loose: no checked edge, not ready, and
-- the loose premise is reported.
run_cmd liftTermElabM do
  let nodes ← #[``m7Goal, ``Effect4.Program.Typed.loadsTyped].mapM fun n => Node.ofName n
  let plan ← buildPlan nodes #[(``m7Goal, ``Effect4.Program.Typed.m7_of_ledger)]
  unless plan.status ``m7Goal == .declared do
    throwError "a loose premise left m7Goal {(plan.status ``m7Goal).word}"
  unless plan.edges.all (!·.checked) do throwError "an edge with a loose premise was checked"
  let loose := plan.loose
  unless loose.size == 1 do throwError "expected one loose premise, found {loose.size}"
  let matched := plan.edges.foldl (init := #[]) fun acc e =>
    e.premises.foldl (init := acc) fun acc m => match m.node with
      | some d => acc.push d
      | none => acc
  unless matched == #[``Effect4.Program.Typed.loadsTyped] do
    throwError "expected LoadsTyped matched by loadsTyped, found {matched}"
  unless plan.next #[``m7Goal] == #[``m7Goal] do throwError "m7Goal should be a next goal"

/-- error: plan: Test.ProofGraphPlan.m7Goal is declared, not ready -/
#guard_msgs in
#obligation_close m7Goal via Effect4.Program.Typed.m7_of_ledger for m7Goal
  from Effect4.Program.Typed.loadsTyped

-- With `decision_preserves` too, the edge is checked and the goal is ready; the closing command
-- applies the implication to both proofs and publishes a kernel-checked `m7Goal.checked`.
#obligation_close m7Goal via Effect4.Program.Typed.m7_of_ledger for m7Goal
  from Effect4.Program.Typed.loadsTyped Effect4.Program.Typed.decision_preserves

/--
info: 'Test.ProofGraphPlan.m7Goal.checked' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms m7Goal.checked

-- 5. Extraction: a proof sketch's holes become ledger goals, and the sketch the checked
-- reduction. The plan then walks the goal from reduced through ready to proved.
theorem sketched : Obligation (∀ n, C n) := ⟨⟩

/--
info: Test.ProofGraphPlan.sketched: 2 part(s), reduced by Test.ProofGraphPlan.sketched.reduce
  Test.ProofGraphPlan.sketched.part1 : ∀ (n : Nat), A n
  Test.ProofGraphPlan.sketched.part2 : ∀ (n : Nat), B n
-/
#guard_msgs in
#extract_obligations sketched using
  intro n
  refine ⟨?_, ?_⟩

/--
info: Test.ProofGraphPlan.sketched: reduced
  via Test.ProofGraphPlan.sketched.reduce (checked)
    Test.ProofGraphPlan.sketched.part1 ⊢ ∀ (n : Nat), A n
    Test.ProofGraphPlan.sketched.part2 ⊢ ∀ (n : Nat), B n
Test.ProofGraphPlan.sketched.part1: declared
Test.ProofGraphPlan.sketched.part2: declared
next goals: [Test.ProofGraphPlan.sketched.part1, Test.ProofGraphPlan.sketched.part2]
-/
#guard_msgs in
#plan_status sketched via sketched.reduce for sketched

theorem sketched.part1.checked : ∀ n, A n := fun _ => rfl
theorem sketched.part2.checked : ∀ n, B n := fun _ => rfl

#obligation_close sketched via sketched.reduce for sketched

/--
info: 'Test.ProofGraphPlan.sketched.checked' does not depend on any axioms
-/
#guard_msgs in
#print axioms sketched.checked

-- A script that reports an error is refused, never extracted from.
theorem broken : Obligation (∀ n, C n) := ⟨⟩

/-- error: extract: the script reported an error; extraction needs a script that elaborates -/
#guard_msgs (error) in
#extract_obligations broken using
  intro n
  exact ⟨?_, ?_⟩

-- A script that leaves nothing open is refused: the goal is proved directly instead.
theorem direct : Obligation (∀ n, A n) := ⟨⟩

/-- error: extract: the script closes Test.ProofGraphPlan.direct; prove it with #obligation_proved -/
#guard_msgs in
#extract_obligations direct using
  intro n
  rfl

end Test.ProofGraphPlan
