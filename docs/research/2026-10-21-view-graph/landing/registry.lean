import Tools.View.LayerGraph
import Tools.Document.Json
import Tools.Semantics

open Tools.Semantics

run_meta do
  let selected : Registry := {
    roots := [`Tools.View.LayerGraph]
    concepts := [{ id := "initial-algebras-folds", title := "Initial algebras and folds" }]
    claims := registry.claims.filter fun c =>
      ["layer-graph-glue", "layer-graph-merge", "document-json-fold-retraction"].contains c.id
    cuts := [] }
  match ← buildReport selected { decisions := #[], counterexamples := #[] } "landing" with
  | .ok report => Lean.logInfo m!"Accepted {report.claims.length} graph-slice claims with their declared evidence boundaries"
  | .error errors => throwError "graph-slice claims refused: {errors}"
