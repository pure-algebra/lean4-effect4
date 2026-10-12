import OCaml5.Lcnf.Externs
import Effect4.Machine.Fibers
open Lean OCaml5.Lcnf
run_cmd do
  let env ← getEnv
  let ex ← match Externs.parse "type Effect4.Machine.Dispatcher task D.t\n" with
    | .ok ex => pure ex
    | .error message => throwError "{message}"
  unless ex.fieldCarrierIn? env ``Effect4.Machine.RunFiber "dispatcher" == some "D.t" do
    throwError "the nominal dispatcher field lost its declared carrier"
  unless ex.fieldCarrierIn? env ``Effect4.Machine.RunFiber "children" == none do
    throwError "an ordinary list acquired the dispatcher carrier"
  let explicit := {ex with fieldCarrier := (ex.fieldCarrier.insert
    ``Effect4.Machine.RunFiber.dispatcher "Explicit.t")}
  unless explicit.fieldCarrierIn? env ``Effect4.Machine.RunFiber "dispatcher" == some "Explicit.t" do
    throwError "the explicit field row did not retain priority"
  unless ({} : Externs).fieldCarrierIn? env ``Effect4.Machine.RunFiber "dispatcher" == none do
    throwError "an undeclared carrier was inferred"
