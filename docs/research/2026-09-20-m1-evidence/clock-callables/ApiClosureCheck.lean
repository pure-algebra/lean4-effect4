import Effect4.Api
import OCaml5.Lcnf.Translate
open Lean Elab Command OCaml5
run_cmd liftTermElabM do
  let result ← Lcnf.translateClosure #[`Effect4.Api.run, `Effect4.Api.replay] 2000
  logInfo m!"clock-api check: decls={result.decls.size}, missing={result.missing.size}, frontier={result.frontier.size}, todos={result.todos.size}"
  unless result.todos.isEmpty && result.missing.isEmpty && result.frontier.isEmpty do
    throwError "API closure refused: {result.todos}; missing {result.missing}; frontier {result.frontier}"
