import Effect4.Laws.Program.Typed.World
open Lean Elab Command
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

run_cmd liftTermElabM do
  let env ← getEnv
  let names := env.constants.toList.map (·.1) |>.filter
    (fun n => (`Effect4.Program.Typed).isPrefixOf n && !n.isInternal &&
      (n.toString.endsWith "Ok" || (`Effect4.Program.Typed.Columns).isPrefixOf n))
  let sorted := names.toArray.qsort (·.toString < ·.toString)
  logInfo m!"generated: {sorted}"

#print Effect4.Program.Typed.RunMachineOk
#print Effect4.Program.Typed.RunFiberOk
#print Effect4.Program.Typed.ScopeFrameOk
#print Effect4.Program.Typed.RaceOk
#print Effect4.Program.Typed.DeferredStoreOk
#print Effect4.Program.Typed.DeferredCellOk
#print Effect4.Program.Typed.MemoMapOk
#print Effect4.Program.Typed.MemoEntryOk
#print Effect4.Program.Typed.ScopeStoreOk
#print Effect4.Program.Typed.PendingOk
#print Effect4.Program.Typed.Columns.DeferredStore_cells
#check @Effect4.Program.Typed.RStateOk
