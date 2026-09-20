import ProofGraph.Proof

namespace ProofGraph
open Lean Elab Meta

/-- Remove temporary definitions and theorems from a speculative term. Existing
constants stay opaque. The existing maxRecDepth option bounds dependency expansion (zero keeps its
unlimited meaning); no temporary declaration is retained. -/
private def closeOverFresh (base : Kernel.Environment) (input : Expr) : TermElabM Expr := do
  let generated := (← getEnv).toKernelEnv
  let depthLimit := maxRecDepth.get (← getOptions)
  let mut depth := 0
  let mut proof := input
  let mut seen : ExprSet := {}
  while true do
    Core.checkSystem "ProofGraph.search.closeOverFresh"
    if seen.contains proof then
      throwError "search returned cyclic temporary declarations"
    seen := seen.insert proof
    let mut values : NameMap (List Name × Expr) := {}
    for name in proof.getUsedConstants do
      unless (base.find? name).isSome do
        match generated.find? name with
        | some (.defnInfo info) =>
          unless info.safety == .safe do
            throwError "search returned an unsafe temporary definition {name}"
          values := values.insert name (info.levelParams, info.value)
        | some (.thmInfo info) =>
          values := values.insert name (info.levelParams, info.value)
        | some _ => throwError "search returned a non-value temporary declaration {name}"
        | none => throwError "search returned an unknown constant {name}"
    if values.isEmpty then return proof
    if depthLimit != 0 && depth ≥ depthLimit then
      throwError "search temporary declaration closure exceeded maxRecDepth ({depthLimit})"
    depth := depth + 1
    if let some bad := proof.find? fun e =>
        match e with
        | .const name levels =>
          match values.find? name with
          | some (params, _) => params.length != levels.length
          | none => false
        | _ => false then
      throwError "search temporary declaration has mismatched universe arguments: {bad}"
    proof := proof.replace fun e =>
      match e with
      | .const name levels =>
        match values.find? name with
        | some (params, value) => some (value.instantiateLevelParams params levels)
        | none => none
      | _ => none
  throwError "search temporary declaration closure did not finish"

/-- Check a declaration synchronously without publishing the resulting environment.
Use only the remainder of the current search budget, without resetting its origin. -/
private def checkDeclaration (base : Kernel.Environment) (declaration : Declaration) : MetaM Unit := do
  Core.checkMaxHeartbeats "ProofGraph.search.checkDeclaration"
  let context ← readThe Core.Context
  let elapsed := (← IO.getNumHeartbeats) - context.initHeartbeats
  let remaining := context.maxHeartbeats - elapsed
  if context.maxHeartbeats != 0 && remaining == 0 then
    throwError "proof graph exhausted its requested heartbeat cap before kernel checking"
  match (Environment.ofKernelEnv base).addDeclCore remaining.toUSize
      (maxRecDepth.get context.options).toUSize declaration context.cancelTk? (doCheck := true) with
  | .ok _ => pure ()
  | .error ex => throwKernelException ex
  Core.checkMaxHeartbeats "ProofGraph.search.checkDeclaration"

/-- Check the closed term at the requested proposition after speculative state is
restored. The temporary check declaration never enters the elaborator environment. -/
private def checkPortable (base : Kernel.Environment) (type proof : Expr) : MetaM Unit := do
  for e in [type, proof] do
    if e.hasMVar || e.hasFVar || e.hasSorry then
      throwError "search returned an open or admitted term"
    for name in e.getUsedConstants do
      unless (base.find? name).isSome do
        throwError "search returned an unavailable constant {name}"
  let levels := (collectLevelParams (collectLevelParams {} type) proof).params.toList
  let name ← mkFreshUserName `_proofGraphSearchCheck
  checkDeclaration base <| .thmDecl
    { name, levelParams := levels, type, value := proof }

/-- Search is speculative. Temporary definition/theorem references are expanded
before rollback, and the closed term is then checked against the original kernel
environment. Speculative declarations and metavariable state are restored;
fresh-name counters may advance. The cap uses Lean's
`maxHeartbeats` units; zero means unlimited. -/
def search (type : Expr) (tactic : Syntax) (cap : Nat) : TermElabM (Except String Expr) :=
  withoutModifyingState do
    tryCatchRuntimeEx
      (withOptions (fun o => Elab.async.set (maxHeartbeats.set o cap) false) <|
        -- Lean caches this limit separately; withOptions does not refresh it.
        withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := Core.getMaxHeartbeats ctx.options }) <|
        withCurrHeartbeats do
          let base := (← getEnv).toKernelEnv
          let proof ← withoutModifyingState do
            let goal ← mkFreshExprMVar type
            let rest ← Tactic.run goal.mvarId! <|
              Tactic.withoutRecover (Tactic.evalTactic tactic)
            unless rest.isEmpty do throwError "search left goals open"
            let proof ← instantiateMVars goal
            if proof.hasMVar || proof.hasFVar || proof.hasSorry then
              throwError "search returned an open or admitted term"
            closeOverFresh base proof
          checkPortable base type proof
          return .ok proof)
      (fun ex => return .error (← ex.toMessageData.toString))

/-- Trust dependencies of a candidate term, before it has a declaration name. -/
def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let checked := (← getEnv).toKernelEnv
  let mut out : Array Name := #[]
  for c in e.getUsedConstants do
    unless (checked.find? c).isSome do
      throwError "proof graph: axiom collection encountered unknown constant {c}"
    for a in ← collectAxioms c do
      unless out.contains a do out := out.push a
  return out.qsort (·.toString < ·.toString)

/-- Dependencies of a theorem include both its stated proposition and proof. -/
def axiomsOfTheorem (proposition proof : Expr) : CoreM (Array Name) := do
  let mut out ← axiomsOf proposition
  for a in ← axiomsOf proof do
    unless out.contains a do out := out.push a
  return out.qsort (·.toString < ·.toString)

/-- Publish the exact searched term as a kernel-checked theorem under the semantic ceiling. -/
def addTheorem (name : Name) (levels : List Name) (proposition proof : Expr) : MetaM ProofRef := do
  if proposition.hasMVar || proposition.hasFVar || proposition.hasSorry ||
      proof.hasMVar || proof.hasFVar || proof.hasSorry then
    throwError "proof graph: cannot publish open evidence {name}"
  let extra := (← axiomsOfTheorem proposition proof).filter fun a =>
    ![``propext, ``Quot.sound].contains a
  unless extra.isEmpty do throwError "proof graph: {name} reaches disallowed axioms {extra}"
  let declaration := Declaration.thmDecl
    {name, levelParams := levels, type := proposition, value := proof}
  checkDeclaration (← getEnv).toKernelEnv declaration
  addDecl declaration
  let reference : ProofRef := ⟨name, levels, proposition⟩
  if let .error why ← reference.validate then throwError why
  return reference

end ProofGraph
