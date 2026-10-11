import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout

/-! Scratch: the probe's static test `OncePlaced` on the four built programs, at the paths the
planned goals name, with red controls at nodes under a loop. A finite probe. The definitions are
copied from `Probe.lean`, section 3. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario

namespace Scratch.Static

def onceChild : Node NativeOp → Nat → Bool
  | .eff (.suspend _), 0 => true
  | .eff (.bind _ _), _ => true
  | .eff (.gen _), 0 => true
  | .eff (.catchCause _ _), _ => true
  | .eff (.matchCause _ _ _), _ => true
  | .eff (.onExit _ _), _ => true
  | .eff (.exit _), 0 => true
  | .eff (.uninterruptible _), 0 => true
  | .eff (.interruptible _), 0 => true
  | .eff (.withFiber _), 0 => true
  | .eff (.scoped _), 0 => true
  | .eff (.acquireRelease _ _), _ => true
  | .eff (.provideLayer _ _ _), 1 => true
  | .eff (.provideService _ _ _), 0 => true
  | .eff (.catchIf _ _ _), _ => true
  | .eff (.select _ _ _ _), _ => true
  | .eff (.restore _ _), 0 => true
  | .eff (.defs _ _ _ _), 1 => true
  | .action (.fork _ _), 0 => true
  | .action (.forkIn _ _ _), 0 => true
  | .action (.forkScoped _ _), 0 => true
  | .action (.raceAll _), 0 => true
  | .effs (.cons _ _), _ => true
  | .stmts (.cons _ _), _ => true
  | .stmt (.bindYield _), 0 => true
  | .stmt (.yieldDiscard _), 0 => true
  | .stmt (.ifElse _ _ _), _ => true
  | _, _ => false

def OncePlaced : Node NativeOp → List Nat → Bool
  | _, [] => true
  | n, i :: rest =>
    onceChild n i &&
      match n.child i with
      | some c => OncePlaced c rest
      | none => false

/-- The node's kind at a path, as a word. -/
def kindAt (root : Node NativeOp) (q : List Nat) : String :=
  match root.at_ q with
  | some (.eff (.acquireRelease _ _)) => "acquireRelease"
  | some (.eff (.onExit _ _)) => "onExit"
  | some (.eff (.iterate _ _ _ _ _ _)) => "iterate"
  | some (.eff (.bind _ _)) => "bind"
  | some (.eff (.perform _ _)) => "perform"
  | some (.eff (.scoped _)) => "scoped"
  | some (.action (.fork _ _)) => "fork"
  | some (.eff (.withFiber _)) => "withFiber"
  | some (.eff _) => "eff"
  | some _ => "other node"
  | none => "no node"

/-- The first loop on a path from the root: its path, or `none`. -/
def firstLoop (root : Node NativeOp) (q : List Nat) : Option (List Nat) :=
  ((List.range (q.length + 1)).find? fun k =>
    match root.at_ (q.take k) with
    | some (.eff (.iterate _ _ _ _ _ _)) => true
    | some (.stmt (.whileTrue _)) => true
    | _ => false).map q.take

def build? (m : Module NativeOp) : Option Api.Built := (Effect4.Api.Author.build m).toOption

def report (label : String) (m : Module NativeOp) (q : List Nat) : String :=
  match build? m with
  | none => s!"{label}: no build"
  | some b =>
    s!"{label}: kind {kindAt (Node.eff b.program) q}, once-placed \
      {OncePlaced (Node.eff b.program) q}, first loop on the path {repr (firstLoop (Node.eff b.program) q)}"

#eval [0, 1, 2, 3, 7].flatMap fun total =>
  [report s!"crew {total}, worker 1's acquireRelease" (Workers.crew total) [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
   report s!"crew {total}, worker 2's acquireRelease" (Workers.crew total) [1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0]]

#eval [1, 3].flatMap fun total =>
  [report s!"queue crew {total}, worker 1" (QueueWorkers.crew total) [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   report s!"queue crew {total}, worker 2" (QueueWorkers.crew total) [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   report s!"queue crew {total}, feeder" (QueueWorkers.crew total) [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
   report s!"queue crew {total}, red: the take's onExit under worker 2's loop" (QueueWorkers.crew total)
     [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0]]

#eval [ report "shop, request 1" (Atomic.shop .none) [1, 1, 1, 1, 0, 0, 0]
      , report "shop, request 2" (Atomic.shop .none) [1, 1, 1, 1, 1, 0, 0, 0]
      , report "shop, request 3" (Atomic.shop .none) [1, 1, 1, 1, 1, 1, 0, 0, 0]
      , report "shop, request 4" (Atomic.shop .none) [1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
      , report "shop, request 5" (Atomic.shop .none) [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
      , report "shop, request 6" (Atomic.shop .none) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
      , report "fetch, red: the attempt's onExit under the retry loop" Timeout.fetch
          [1, 1, 0, 0, 1, 0, 0, 0, 0, 0] ]

-- The fork records of the run `four` of the timeout scenario: child, parent, site.
def forksOfFour : List (Nat × Nat × List Nat) :=
  match Timeout.runsAndControls.1.find? (·.name == "four") with
  | some run => run.played.machine.forks.map fun (r : ForkRecord) => (r.child.value, r.parent.value, r.site)
  | none => []

#eval forksOfFour

end Scratch.Static
