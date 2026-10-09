import Tools.LoadPaths
import Tools.S1LoadReview.Peer

/-!
Finite public-command controls for #landing_plan at 979be0ad.
Proof role: tooling evidence. Consumer: the S1 load review receipt and assertions below.
Reach: this loaded fixture, with no Effect4 semantic or host claim.
Requirement served: measured proof-planning evidence.
Theorems are trivial dependency controls, not general semantic proofs.
-/
namespace S1LoadReview.Local
open Lean Elab Command Tools.LoadPaths

theorem helperOne : True := S1LoadReview.External.sharedJoint
theorem helperTwo : True := S1LoadReview.External.sharedJoint
theorem topPair : True ∧ True := ⟨helperOne, helperTwo⟩

#landing_plan topPair
#load_report Tools.S1LoadReview.Local
#landing_plan topPair S1LoadReview.Peer.peerTop
#load_report Tools.S1LoadReview.Local Tools.S1LoadReview.Peer
#landing_plan helperOne helperTwo

run_cmd do
  let env ← getEnv
  let modules := [`Tools.S1LoadReview.Local]
  let pr := predict env modules #[``topPair]
  let g := buildGraph env
  let r := measure env g (roots env) (loadBearing g (roots env)) modules
  unless pr.joints.size == 1 && pr.localSteps.size == 2 && pr.owed.isEmpty do
    throwError "node controls changed: {pr.joints.size}, {pr.localSteps.size}, {pr.owed.size}"
  unless r.tree == 2 && r.local_ == 2 && r.ratio == 50 do
    throwError "edge controls changed: {r.tree}, {r.local_}, {r.ratio}"
  unless pr.joints.toArray.all (fun (_, k) => k == 1) do
    throwError "joint multiplicity changed"
  logInfo "PASS planning counts one shared joint, while the report counts two edges; ratios 33% and 50%"

proof_goal localGoal : True

theorem pendingHelper : True := localGoal
theorem localPendingTop : True := pendingHelper

#landing_plan localPendingTop

run_cmd do
  let env ← getEnv
  let pr := predict env [`Tools.S1LoadReview.Local] #[``localPendingTop]
  unless pr.localSteps.contains ``pendingHelper && pr.owed.contains ``localGoal do
    throwError "local pending controls changed"
  let some (status, _) := (ProofGraph.standing env ``pendingHelper).run' {} |
    throwError "standing walk exhausted"
  unless status.word == "modulo" do throwError "pending helper is not modulo its goal"
  logInfo "PASS the planner labels a modulo-goal helper proved while also reporting its goal"

theorem externalPendingTop : True := S1LoadReview.External.pendingJoint

#landing_plan externalPendingTop
#landing_plan S1LoadReview.External.pendingGoal

run_cmd do
  let env ← getEnv
  let pr := predict env [`Tools.S1LoadReview.Local] #[``externalPendingTop]
  unless pr.joints.contains ``S1LoadReview.External.pendingJoint && pr.owed.isEmpty do
    throwError "external pending controls changed"
  let some (status, _) := (ProofGraph.standing env ``externalPendingTop).run' {} |
    throwError "standing walk exhausted"
  unless status.word == "modulo" do throwError "external pending top is not modulo its goal"
  logInfo "PASS a top with external unfinished proof reports zero owed goals and 100% reuse"

#landing_plan Nat
#landing_plan Nat.zero

/-- An ordinary data declaration is not an admitted theorem top. -/
def dataTop : PLift True := ⟨S1LoadReview.External.sharedJoint⟩
#landing_plan dataTop

/-- error: Unknown constant `DefinitelyAbsentS1LoadReview` -/
#guard_msgs (error) in
#landing_plan DefinitelyAbsentS1LoadReview

run_cmd do
  for n in [``helperOne, ``helperTwo, ``topPair, ``S1LoadReview.Peer.peerTop,
      ``S1LoadReview.External.sharedJoint] do
    let axioms ← Lean.collectAxioms n
    unless axioms.isEmpty do throwError "proved fixture theorem {n} has axioms {axioms}"
  logInfo "PASS positive theorem controls have empty axiom sets"
  for n in [``pendingHelper, ``localPendingTop, ``externalPendingTop,
      ``S1LoadReview.External.pendingJoint] do
    let axioms ← Lean.collectAxioms n
    unless axioms == #[`sorryAx] do
      throwError "planned dependency control {n} has unexpected axioms {axioms}"
  logInfo "PASS unfinished controls depend on sorryAx through their tagged planned goals"
  let env ← getEnv
  unless (env.find? ``dataTop matches some (.defnInfo _)) do
    throwError "data input is not a definition"
  logInfo "PASS ordinary data and inductive inputs reach the public planning command"
end S1LoadReview.Local
