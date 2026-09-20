import ProofGraph.Search

/-! Finite controls for the search budget and speculative environment rollback.
The metaprogram stays inside run_cmd; only the kernel-checked True theorem is published.
The timeout advances Lean's allocation counter directly, without a wall-clock assumption. -/

set_option autoImplicit false
namespace Test.ProofGraphSearch
open Lean Meta Elab Command
open _root_.ProofGraph

run_cmd liftTermElabM do
  let before ← readThe Core.Context
  let checkRestored : TermElabM Unit := do
    let after ← readThe Core.Context
    unless maxHeartbeats.get after.options == maxHeartbeats.get before.options &&
        after.maxHeartbeats == before.maxHeartbeats &&
        after.initHeartbeats == before.initHeartbeats do
      throwError "search leaked its heartbeat context"
    if (← getEnv).contains `Test.ProofGraphSearch.transient then
      throwError "search leaked a speculative declaration"
  let capTactic (cap : Nat) : TermElabM Syntax := do
    let count := Syntax.mkNumLit (toString cap)
    return (← `(tactic|
      run_tac do
        let requested : Nat := $count:num
        let options ← getOptions
        let context ← readThe Core.Context
        unless maxHeartbeats.get options == requested do
          throwError "search did not install its requested heartbeat option"
        unless context.maxHeartbeats == requested * 1000 do
          throwError "search did not install its requested cached heartbeat limit"
        unless context.maxHeartbeats == Core.getMaxHeartbeats options do
          throwError "search option and cached limit disagree"
        addDecl <| .thmDecl
          { name := `Test.ProofGraphSearch.transient, levelParams := [],
            type := mkConst ``True, value := mkConst ``True.intro }
        Lean.Elab.Tactic.closeMainGoal `ProofGraphSearch (mkConst ``True.intro))).raw
  let proposition := mkConst ``True
  let result ← search proposition (← capTactic 40000) 40000
  checkRestored
  let proof ← match result with
    | .ok proof => pure proof
    | .error why => throwError "bounded search failed: {why}"
  discard <| addTheorem `Test.ProofGraphSearch.closed [] proposition proof
  let reference : ProofRef := ⟨`Test.ProofGraphSearch.closed, [], proposition⟩
  if let .error why ← reference.validate then throwError why

  -- Zero keeps Lean's unlimited setting; this control still runs only a finite proof.
  let unlimited ← search proposition (← capTactic 0) 0
  checkRestored
  if let .error why := unlimited then throwError "zero-cap finite search failed: {why}"

  let spend ← `(tactic|
    run_tac do
      addDecl <| .thmDecl
        { name := `Test.ProofGraphSearch.transient, levelParams := [],
          type := mkConst ``True, value := mkConst ``True.intro }
      IO.addHeartbeats (2000 * 1000 + 1)
      Core.checkMaxHeartbeats "ProofGraphSearch.forced"
      Lean.Elab.Tactic.closeMainGoal `ProofGraphSearch (mkConst ``True.intro))
  let exhausted ← search proposition spend 2000
  checkRestored
  let .error why := exhausted | throwError "search ignored its requested heartbeat cap"
  unless why.contains "(deterministic) timeout" &&
      why.contains "ProofGraphSearch.forced" && why.contains "(2000)" do
    throwError "search failed for a reason other than the requested timeout: {why}"

  -- This is the same command after spending over 2000; the next search needs a fresh origin.
  let recovered ← search proposition (← capTactic 2000) 2000
  checkRestored
  if let .error why := recovered then throwError "search after timeout failed: {why}"

#print axioms Test.ProofGraphSearch.closed
end Test.ProofGraphSearch
