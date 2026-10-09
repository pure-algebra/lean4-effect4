import Tools.Semantics
import Effect4.Laws.Program.Agreement.Segment

open Lean Elab Command Effect4.Laws.Auto in
run_cmd liftTermElabM do
  let env ← getEnv
  let segment := `Effect4.Laws.Program.Agreement.Segment
  let defaults := Tools.Semantics.registry.concepts.flatMap (·.defaultModules)
  unless defaults.contains segment do throwError "Segment remains omitted"
  let names := (semanticsTheorems env).filter fun n => semanticsModule env n == segment
  let selected := names.filter fun n => defaults.contains (semanticsModule env n)
  unless !names.isEmpty && selected == names do throwError "module selection failed"
  logInfo m!"Segment placement: available={names.size}; selected={selected.size}"
