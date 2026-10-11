import Test.Dogfood.Scenario.Timeout

open Effect4 Effect4.Machine Test.Dogfood.Scenario Test.Dogfood.Scenario.Timeout

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def built : Option Api.Built := (Effect4.Api.Author.build fetch).toOption

def fateStr : Fate → String
  | .live => "live"
  | .answered b => s!"answered {repr b}"
  | .failed t m => s!"failed {t} {m}"
  | .retired k => s!"retired {k}"
  | .other => "other"

def endStr : Ending → String
  | .running => "running"
  | .answered b => s!"answered {repr b}"
  | .failed t m => s!"failed {t} {m}"
  | .interrupted => "interrupted"
  | .other => "other"

def showRun (moves : List Move) : String :=
  match built with
  | none => "no build"
  | some b =>
    let s : Run := Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Timeout.opened b) moves
    let o := observe s
    s!"calls={(o.calls.map fateStr)} attempts={o.attempts} root={endStr o.root} \
      retriesDeclared={o.retriesDeclared} stale={o.staleNeverApplies} \
      refusals={(refusals s).map (·.1)} phases={repr s.phases}"

-- the scenario's parked state, then: the fibers of the machine
#eval match built with
  | none => "none"
  | some b =>
    let s : Run := Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Timeout.opened b)
      Test.Dogfood.Scenario.Timeout.parked
    s!"live={repr ((Test.Dogfood.Scenario.live s).map (fun (c : Seen) => c.key))} awaiting={repr (s.outstanding.map fun (a : Program.Await) => (a.fiber, a.token))} runnable={repr (Api.runnableFibers s.machine)} timers={repr s.work.timers}"

-- green: the 503 run
#eval showRun (script [parked, answer http (failed "HttpError" "503"), [.tick 100, .hold http],
      answer http (ok body2)])

-- candidate counterexample 1: the host interrupts fiber 3 before the reply
#eval showRun (script [parked, [.cancel ⟨3⟩, .receive http (ok body1), .apply http, .tick 2000,
  .tick 100, .flush, .hold http]])

-- candidate counterexample 2: interrupt fiber 4 instead
#eval showRun (script [parked, [.cancel ⟨4⟩, .receive http (ok body1), .apply http, .tick 2000,
  .tick 100, .flush, .hold http]])

-- candidate counterexample 3: a yield verdict on fiber 3 after the reply
#eval showRun (script [parked, [.receive http (ok body1), .apply http,
  .control (.yieldVerdict ⟨3⟩ true), .tick 2000, .tick 100, .flush, .hold http]])
