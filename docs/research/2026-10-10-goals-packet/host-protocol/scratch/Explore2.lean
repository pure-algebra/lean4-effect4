import Test.Dogfood.Scenario.Routing

open Effect4 Effect4.Machine Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def builtR : Option Api.Built := (Effect4.Api.Author.build (request "secret" 2 "2")).toOption

def showRunR (moves : List Move) : String :=
  match builtR with
  | none => "no build"
  | some b =>
    let s : Run := Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Routing.opened b) moves
    s!"exit={(s.exit.map fun e => match e with | .success v => s!"ok {repr v}" | .failure c => s!"fail {repr (c.reasons.length)}")} repo={repr (requestsOn s "UserRepo.findById")} \
      refusals={(refusals s).map (·.1)} phases={repr s.phases} journal={s.journal.map kindOf} \
      funded={Run.funded s} atRest={Run.atRest s} \
      tape={(Run.tapeOf s).length}"

#eval showRunR (failing "SqlError" "connection lost")

-- is the program in the row fragment?
#eval builtR.map fun b => (Effect4.Program.Denote.StraightRows b.table b.program,
  Effect4.Program.Denote.LoopedRows b.program)

-- record values: does admission take an int at a nat column?
#eval Effect4.Program.Val.hasTy (.negInt 5) .nat []
#eval Effect4.Program.Val.hasTy
  (Test.Dogfood.P2HandlerLayers.recordVal ["pageSize", "adminToken"] [.nat 20, .str "secret"]) Test.Dogfood.P2HandlerLayers.configTy []
#eval (Test.Dogfood.P2HandlerLayers.recordVal ["pageSize", "adminToken"] [.nat 20, .str "secret"]) == configOf "secret" 20
-- a raw frame with the fields in the other order
#eval Effect4.Program.Val.hasTy
  (Effect4.Machine.Record.frame [("pageSize", .nat 20), ("adminToken", .str "secret")])
  Test.Dogfood.P2HandlerLayers.configTy []
#eval Effect4.Program.Val.hasTy
  (Effect4.Machine.Record.frame [("adminToken", .str "secret"), ("pageSize", .nat 20)])
  Test.Dogfood.P2HandlerLayers.configTy []
#eval (Effect4.Machine.Record.frame [("adminToken", .str "secret"), ("pageSize", .nat 20)]) ==
  configOf "secret" 20
