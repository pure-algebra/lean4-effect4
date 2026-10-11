import Test.Dogfood.Scenario.QueueWorkers
import Std.Data.HashSet

/-! Scratch probe: the stage table as a classifier, checked on every state of the host-act
search. A stage is a frame signature: each frame's constructor with the path of its point. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace StageProbe

abbrev NF := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NC := Prim EffName EffThunk Val Err Defect FiberId Ann

/-- A frame's signature: its constructor and the path of the point that its name carries. -/
inductive Sig
  | awaitHint
  | external (origin : List Nat)
  | cancelAwait
  | mask (flag : Bool)
  | fin (path : List Nat)
  | cont (path : List Nat)
  | caught (path : List Nat)
  | loop (path : List Nat)
  | scopeExit
  | act (path : List Nat)
  | storeOp
  | other
deriving DecidableEq, Repr

def sig : NC → Sig
  | .async (.registerAwait _) _ _ => .awaitHint
  | .async (.external _ _ origin) _ _ => .external origin
  | .asyncFinalizer (.withWaiter (.cancelAwait _) _ _) => .cancelAwait
  | .setInterruptible flag => .mask flag
  | .onExit _ (.fin p) false => .fin p.path
  | .onSuccess _ (.cont p) => .cont p.path
  | .onFailure _ (.caughtError p) => .caught p.path
  | .whileLoop (.loop p) _ => .loop p.path
  | .onExit _ (.scopedExit _ _) false => .scopeExit
  | .withFiber (.act p) => .act p.path
  | .sync (.op _) => .storeOp
  | _ => .other

def fiberSig (f : NF) : List Sig := sig f.frame.current :: f.frame.stack.map sig

/-- The loop paths of the crew members, by fiber number. -/
def loopOf : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]
  | 2 => [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1]
  | 3 => [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1]
  | _ => []

/-- The fork paths of the crew members: their loop path less its last two steps. -/
def forkOf (n : Nat) : List Nat := (loopOf n).take ((loopOf n).length - 2)

def takingSig (L : List Nat) : List Sig :=
  [.awaitHint, .cancelAwait, .mask false, .fin (L ++ [0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0]),
   .cont (L ++ [0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0]), .loop (L ++ [0, 0, 1, 0, 1, 0]),
   .cont (L ++ [0, 0, 1, 0, 1]), .mask true, .cont (L ++ [0]), .loop L, .scopeExit]

def runningSig (L : List Nat) : List Sig :=
  [.external (L ++ [0, 1, 1, 0, 0]), .caught (L ++ [0, 1, 1, 0]), .cont (L ++ [0, 1, 1]), .loop L,
   .scopeExit]

def callingSig (F : List Nat) : List Sig :=
  [.external (F ++ [0, 0]), .cont (F ++ [0]), .loop F, .scopeExit]

def offeringSig (F : List Nat) : List Sig :=
  [.awaitHint, .cancelAwait, .mask false, .fin (F ++ [0, 1, 1, 0, 1, 1, 1, 1, 0]), .mask true,
   .loop F, .scopeExit]

def gateSig : List Sig := [.awaitHint, .cancelAwait, .scopeExit, .cont [1, 1, 1, 1, 1, 1]]

/-- A crew fiber's stage between rows of host acts. -/
inductive Stage
  | exited
  | rootGate
  | unstarted (member : Nat)
  | taking (worker : Nat)
  | running (worker : Nat)
  | calling
  | offering
  | helper
deriving DecidableEq, Repr

def isParked (f : NF) : Bool :=
  match f.parked with
  | .withGuard _ => true
  | .notParked => false

/-- The stage of a fiber by the table, or `none` where the fiber matches no row. -/
def hostStage (f : NF) : Option Stage :=
  let s := fiberSig f
  let n := f.id.value
  if f.exit.isSome then some .exited
  else if n == 0 && isParked f && s == gateSig then some .rootGate
  else if (n == 1 || n == 2 || n == 3) && !isParked f && s == [.act (forkOf n)] then
    some (.unstarted n)
  else if (n == 1 || n == 2) && isParked f && s == takingSig (loopOf n) then some (.taking n)
  else if (n == 1 || n == 2) && isParked f && s == runningSig (loopOf n) then some (.running n)
  else if n == 3 && isParked f && s == callingSig (loopOf 3) then some .calling
  else if n == 3 && isParked f && s == offeringSig (loopOf 3) then some .offering
  else if 4 ≤ n && !isParked f && !f.frame.interruptible && s == [.storeOp] then some .helper
  else none

/-- One move, with the tape's reading of its rows (seat WORKQ's `stepRead`). -/
def rowRead (s : Run) (c : Command) : Bool :=
  let phase := (Api.Runner.result s.runner c).phase
  phase != .frontier && (Effect4.Run.decisionOf s c phase).all (Effect4.Run.readsOn s)

def stepRead (state : Run × Bool) (move : Move) : Run × Bool :=
  (move.rows state.1).foldl (fun acc c => (acc.1.step c, acc.2 && rowRead acc.1 c)) state

structure Tally where
  nodes : Nat := 0
  classified : Nat := 0
  unclassified : List String := []
  stages : Std.HashSet String := {}

def judge (state : Run × Bool) (t : Tally) : Tally :=
  let fibers := state.1.machine.fibers
  let stages := fibers.map hostStage
  let t := { t with nodes := t.nodes + 1 }
  if stages.all Option.isSome then
    { t with classified := t.classified + 1,
             stages := stages.foldl (fun acc st => acc.insert (reprStr st)) t.stages }
  else
    let bad := (fibers.filter (fun f => (hostStage f).isNone)).map fun f =>
      s!"{f.id.value}: {reprStr (fiberSig f)}"
    { t with unclassified := if t.unclassified.length < 5 then t.unclassified ++ bad else t.unclassified }

def search (alphabet : List Move) : Nat → Run × Bool → Tally → Tally
  | 0, state, t => judge state t
  | depth + 1, state, t =>
    let t := judge state t
    alphabet.foldl (fun t move => search alphabet depth (stepRead state move) t) t

def hostAlphabet : List Move :=
  [ .flush, .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨3⟩, .cancel ⟨4⟩, .cancel ⟨5⟩
  , .hold feederCall, .hold w1, .hold w2
  , .receive feederCall (ok (.nat 7)), .receive feederCall (ok (.nat 8))
  , .receive w1 (ok .unit), .receive w2 (ok .unit)
  , .receive w1 (failed "JobFailed" "bad payload"), .receive w2 (failed "Boom" "other")
  , .apply feederCall, .apply w1, .apply w2 ]

def bases : List (List Move) :=
  [[.start], parked, running, blocked,
   script [parked, [.receive feederCall (ok (.nat 1)), .apply feederCall]],
   script [blocked, closing], script [running, cancelWaiting, afterWaiting]]

def run (depth : Nat) : Tally :=
  match (Effect4.Api.Author.build (crew 3)).toOption with
  | none => {}
  | some b => bases.foldl (fun t base => search hostAlphabet depth (base.foldl stepRead (opened b, true)) t) {}

end StageProbe

open StageProbe in
#eval do
  let t := run 3
  IO.println s!"host acts, depth 3, seven bases: nodes={t.nodes} classified={t.classified} stages={t.stages.toList}"
  IO.println s!"unclassified: {t.unclassified}"
