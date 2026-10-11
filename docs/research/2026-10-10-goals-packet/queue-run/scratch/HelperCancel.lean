import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: a host cancels a posted helper before it starts. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace HCProbe

def built : Option Api.Built := (Effect4.Api.Author.build (crew 3)).toOption

def summary (s : Run) : String :=
  let o := observe s
  s!"atRest={atRest s} funded={funded s} queue={repr (o.queue.view.map fun q => (q.buffered.length, q.offers.length, q.takers))} assignment={o.assignment.length} fed={o.fed.length} held={o.held.length} heldWithin={o.heldWithin} accounted={o.accounted} settled={o.settled} live=[{o.live 1},{o.live 2},{o.live 3}] calling=[{o.calling 1},{o.calling 2},{o.calling 3}] fibers={s.machine.fibers.map fun f => (f.id.value, f.exit.isSome)} armed={s.machine.armed.map (·.value)}"

def runs : List (String × List Move) :=
  [ ("fed (control)", script [parked, feed 1])
  , ("fed, cancel helper 4, flush", script [parked, answer feederCall (ok (.nat 1)), [.cancel ⟨4⟩, .flush]])
  , ("fed, cancel helper 5, flush", script [parked, answer feederCall (ok (.nat 1)), [.cancel ⟨5⟩, .flush]])
  , ("fed, cancel helpers 4 and 5, flush", script [parked, answer feederCall (ok (.nat 1)), [.cancel ⟨4⟩, .cancel ⟨5⟩, .flush]]) ]

def report : List String :=
  match built with
  | none => ["no build"]
  | some b =>
    runs.map fun (name, moves) =>
      let s := Test.Dogfood.Scenario.play (opened b) moves
      name ++ ": " ++ summary s

end HCProbe

open HCProbe in
#eval IO.println (String.intercalate "\n" report)
