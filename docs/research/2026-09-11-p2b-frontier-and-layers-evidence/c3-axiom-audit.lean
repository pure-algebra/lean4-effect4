import Effect4.Laws.Api.Guard
import Effect4.Laws.Api.Fuel
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command
private def environmentModule (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    let moduleName := (environmentModule env name).getD Name.anonymous
    if moduleName.toString.startsWith "Effect4.Laws.Program.Guard" ||
        moduleName.toString == "Effect4.Laws.Api.Guard" || moduleName.toString == "Effect4.Laws.Api.Fuel" then
      match info with
      | .thmInfo _ => some name
      | _ => none
    else none
  let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
  for name in names do
    let dependencies ← Lean.collectAxioms name
    unless dependencies.all (fun a => a == ``propext || a == ``Quot.sound) do
      throwError "Guard proof axiom ceiling exceeded: {name}: {dependencies}"
    elabCommand (← `(command| #print axioms $(mkIdent name)))
  logInfo m!"Guard theorem receipts: {names.length}"
