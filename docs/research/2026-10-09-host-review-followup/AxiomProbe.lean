import ProofGraph.Axioms
import Lean

open Lean Elab Command in
run_cmd do
  let base ← getEnv
  let addAxiom (env : Environment) (n : Name) (ty : Expr) : CommandElabM Environment := do
    let decl : AxiomVal := { name := n, levelParams := [], type := ty, isUnsafe := false }
    match env.addDeclCore 0 1000 (.axiomDecl decl) none with
    | .ok env => pure env
    | .error _ => throwError "local control axiom was refused"
  let typeName := `FollowupTypeControl.A
  let valueName := `FollowupTypeControl.a
  let env ← addAxiom base typeName (mkSort (.succ .zero))
  let env ← addAxiom env valueName (mkConst typeName)
  let some good := ProofGraph.exactAxioms env typeName | throwError "type control exhausted"
  unless good == #[typeName] do throwError "positive control failed"
  let some got := ProofGraph.exactAxioms env valueName | throwError "dependent control exhausted"
  unless got.contains valueName do throwError "direct axiom was omitted"
  let expected ← withEnv env <| Lean.collectAxioms valueName
  let (many, _) := ProofGraph.reachedAxiomsMany env #[typeName, valueName] {}
  unless many[1]! == some got do throwError "fresh and shared memo disagree"
  let (stopped, _) := ProofGraph.reachedAxiomsMany env #[valueName] {} (· == valueName)
  unless stopped[0]! == some #[valueName] do throwError "intentional stop leaf changed"
  unless ((← getEnv).find? typeName).isNone do throwError "a local control escaped"
  logInfo m!"type dependency found: {got.contains typeName}; agrees with acyclic Lean oracle: {got.qsort Name.lt == expected}; positive and stop controls passed"
