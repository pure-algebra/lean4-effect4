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

-- Returned proofs must survive speculative declaration rollback.
run_cmd liftTermElabM do
  let originalAsync := Elab.async.get (← getOptions)
  let assertRemoved (names : List Name) : TermElabM Unit := do
    unless Elab.async.get (← getOptions) == originalAsync do
      throwError "search changed the caller's asynchronous elaboration option"
    for name in names do
      if (← getEnv).contains name || ((← getEnv).toKernelEnv.find? name).isSome then
        throwError "search leaked temporary declaration {name}"
  let requirePortable (result : Except String Expr) : TermElabM Expr := do
    let proof ← match result with
      | .ok proof => pure proof
      | .error why => throwError "portable search failed: {why}"
    for name in proof.getUsedConstants do
      unless ((← getEnv).toKernelEnv.find? name).isSome do
        throwError "search returned temporary dependency {name}"
    return proof

  let freshTheorem ← `(tactic|
    run_tac do
      addDecl <| .thmDecl
        { name := `Test.ProofGraphSearchPortability.transientTrue,
          levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
      Lean.Elab.Tactic.closeMainGoal `ProofGraphSearchPortability
        (mkConst `Test.ProofGraphSearchPortability.transientTrue))
  let proof ← requirePortable (← search (mkConst ``True) freshTheorem 20000)
  assertRemoved [`Test.ProofGraphSearchPortability.transientTrue]
  discard <| addTheorem `Test.ProofGraphSearchPortability.closed [] (mkConst ``True) proof

  let chain ← `(tactic|
    run_tac do
      let u := Level.param `u
      let equality := mkApp3 (mkConst ``Eq [u]) (mkBVar 1) (mkBVar 0) (mkBVar 0)
      let type := mkForall `α .implicit (mkSort u)
        (mkForall `x .default (mkBVar 0) equality)
      let value := mkLambda `α .implicit (mkSort u)
        (mkLambda `x .default (mkBVar 0)
          (mkApp2 (mkConst ``Eq.refl [u]) (mkBVar 1) (mkBVar 0)))
      addDecl <| .defnDecl
        { name := `Test.ProofGraphSearchPortability.transientId,
          levelParams := [`u], type, value, hints := .abbrev, safety := .safe }
      addDecl <| .defnDecl
        { name := `Test.ProofGraphSearchPortability.transientAlias,
          levelParams := [`u], type,
          value := mkConst `Test.ProofGraphSearchPortability.transientId [u],
          hints := .abbrev, safety := .safe }
      Lean.Elab.Tactic.closeMainGoal `ProofGraphSearchPortability
        (mkConst `Test.ProofGraphSearchPortability.transientAlias [Level.param `v]))
  let v := Level.param `v
  let polymorphicType := mkForall `α .implicit (mkSort v)
    (mkForall `x .default (mkBVar 0)
      (mkApp3 (mkConst ``Eq [v]) (mkBVar 1) (mkBVar 0) (mkBVar 0)))
  let polyProof ← requirePortable (← search polymorphicType chain 20000)
  assertRemoved [`Test.ProofGraphSearchPortability.transientId,
    `Test.ProofGraphSearchPortability.transientAlias]
  discard <| addTheorem `Test.ProofGraphSearchPortability.polymorphic [`v]
    polymorphicType polyProof

  let freshAxiom ← `(tactic|
    run_tac do
      addDecl <| .axiomDecl
        { name := `Test.ProofGraphSearchPortability.transientAxiom,
          levelParams := [], type := mkConst ``True, isUnsafe := false }
      Lean.Elab.Tactic.closeMainGoal `ProofGraphSearchPortability
        (mkConst `Test.ProofGraphSearchPortability.transientAxiom))
  let rejected ← search (mkConst ``True) freshAxiom 20000
  assertRemoved [`Test.ProofGraphSearchPortability.transientAxiom]
  let .error why := rejected | throwError "search accepted a temporary axiom"
  unless why.contains "non-value temporary declaration" do
    throwError "temporary axiom failed for the wrong reason: {why}"

  -- Assignment can bypass tactic-level type checking; the returned term must
  -- still inhabit the requested proposition under the kernel check.
  let wrongType ← `(tactic|
    run_tac do
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.assign (mkConst ``True.intro)
      Lean.Elab.Tactic.replaceMainGoal [])
  let mismatched ← search (mkConst ``False) wrongType 20000
  let .error mismatch := mismatched | throwError "search accepted a wrong-type assignment"
  unless mismatch.contains "type mismatch" do
    throwError "wrong-type assignment failed for an unrelated reason: {mismatch}"

  let missing ← tryCatchRuntimeEx
    (do
      discard <| axiomsOf (mkConst `Test.ProofGraphSearchPortability.nonexistent)
      pure (none : Option String))
    (fun ex => return some (← ex.toMessageData.toString))
  let some why := missing | throwError "axiom collection silently accepted an unknown constant"
  unless why.contains "axiom collection encountered unknown constant" do
    throwError "unknown constant failed for an unrelated reason: {why}"

  -- The body is harmless, but the stored proposition contains a forbidden
  -- axiom in an unused let. Rejection must happen before publication.
  let one := Level.succ Level.zero
  let witness := mkApp2 (mkConst ``Nonempty.intro [one]) (mkConst ``Nat) (mkNatLit 0)
  let choice := mkApp2 (mkConst ``Classical.choice [one]) (mkConst ``Nat) witness
  let typeOnly := Expr.letE `unused (mkConst ``Nat) choice (mkConst ``True) true
  let rejectedType ← tryCatchRuntimeEx
    (do
      discard <| addTheorem `Test.ProofGraphSearchPortability.rejectedTypeOnly []
        typeOnly (mkConst ``True.intro)
      pure (none : Option String))
    (fun ex => return some (← ex.toMessageData.toString))
  assertRemoved [`Test.ProofGraphSearchPortability.rejectedTypeOnly]
  let some why := rejectedType | throwError "publication accepted a type-only forbidden axiom"
  unless why.contains "disallowed axioms" && why.contains "Classical.choice" do
    throwError "type-only axiom failed for an unrelated reason: {why}"

  let existing ← `(tactic| run_tac do
    Lean.Elab.Tactic.closeMainGoal `ProofGraphSearchPortability
      (mkConst `Test.ProofGraphSearchPortability.closed))
  let existingProof ← requirePortable (← search (mkConst ``True) existing 20000)
  unless existingProof.getUsedConstants.contains `Test.ProofGraphSearchPortability.closed do
    throwError "search unfolded an existing theorem"

#print axioms Test.ProofGraphSearchPortability.closed
#print axioms Test.ProofGraphSearchPortability.polymorphic

end Test.ProofGraphSearch
