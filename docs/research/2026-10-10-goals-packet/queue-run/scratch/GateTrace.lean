import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: the trace of the decision that closes the pool. Does the gate resume the root
inside the worker's entry, and does the root's close interrupt that worker while it runs? -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace GTProbe

abbrev Event := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

def eventOf : Event → Option String
  | .started f => some s!"started {f.value}"
  | .parkedOn f _ => some s!"parked {f.value}"
  | .resumedWith f _ _ => some s!"resumed {f.value}"
  | .interruptRecorded _ t => some s!"interruptRecorded {t.value}"
  | .interruptDeferred t => some s!"interruptDeferred {t.value}"
  | .exited f (.success _) => some s!"exited {f.value} success"
  | .exited f (.failure _) => some s!"exited {f.value} failure"
  | .scheduledTask o _ _ => some s!"scheduled on {o.value}"
  | .ranTask o _ => some s!"ran task of {o.value}"
  | _ => none

def report : List String :=
  match (Effect4.Api.Author.build (crew 3)).toOption with
  | none => ["no build"]
  | some b =>
    let before := Test.Dogfood.Scenario.play (opened b) (script [blocked, [done w1, [.hold w1, .hold feederCall], failJob w2, [.hold w2]].flatten])
    let after := Test.Dogfood.Scenario.play before (done w1)
    let n := before.machine.trace.length
    (after.machine.trace.drop n).filterMap eventOf

end GTProbe

open GTProbe in
#eval IO.println (String.intercalate "\n" report)
