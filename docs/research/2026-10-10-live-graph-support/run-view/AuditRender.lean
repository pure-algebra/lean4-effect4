import Tools.View.Run
import ProofGraph.AxiomAudit
open Lean ProofGraph

-- These exact rendering declarations reach choice through String and graph layout.
-- This local receipt changes no trust-gate policy.
run_elab do
  let env ← getEnv
  let (facts, _, missing) := Audit.auditedFacts env (· == (``Tools.View.Run.prepare).getPrefix)
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  let rendering : Array Name := #[
    ``Tools.View.Run.prepare, ``Tools.View.Run.framePrepared,
    ``Tools.View.Run.frame, ``Tools.View.Run.framesBuilt, ``Tools.View.Run.frames,
    Name.str ``Tools.View.Run.framesBuilt "go",
    Name.str (Name.str ``Tools.View.Run.framesBuilt "go") "_f",
    Name.str (Name.str ``Tools.View.Run.framesBuilt "go") "_sunfold",
    Name.str (Name.str ``Tools.View.Run.framesBuilt "go") "_unsafe_rec"]
  for f in facts do
    unless f.safeRecursor do
      if f.isUnsafe || f.isPartial || f.isAxiom || f.isExtern || f.implementedBy ||
          f.bodilessOpaque || f.hasInitFn then throwError "forbidden declaration: {f.name}"
  let roots := facts.map (·.name)
  let (results, _) := reachedAxiomsMany env roots {} (isGoal env)
  let mut encountered : Array Name := #[]
  for (name, result) in roots.zip results do
    let some reached := result | throwError "walk exhausted: {name}"
    if reached.any (isGoal env) then throwError "planned goal reached: {name}"
    let allowed := if rendering.contains name then #[``propext, ``Quot.sound, ``Classical.choice]
      else #[``propext, ``Quot.sound]
    unless reached.all allowed.contains do throwError "outside axioms: {name}: {reached}"
    if rendering.contains name then
      unless reached.contains ``Classical.choice do throwError "unneeded rendering exclusion: {name}"
      encountered := encountered.push name
      logInfo m!"Rendering exclusion: {name}: {reached}"
  unless rendering.all roots.contains && encountered.size == rendering.size do
    throwError "rendering list does not name exactly the encountered exclusions"
  logInfo m!"PASS: {roots.size} declarations; {rendering.size} exact rendering exclusions; no goals or forbidden declarations."
