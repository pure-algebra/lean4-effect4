import Test.Dogfood.Scenario.QueueWorkers
import Std.Data.HashSet

/-! Scratch probe: the shapes of the crew's fibers between moves, on bounded scripts.

A shape is a fiber's current primitive and its stack, each frame as its constructor and the path
of the point its name carries. Values, handles, tokens and compile fuel are dropped. The census
also judges the three goals of the family on every funded state, and records the largest op count
of a fiber. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace CensusProbe

def nameShape : EffName → String
  | .cont p => s!"cont{p.path}"
  | .caught p => s!"caught{p.path}"
  | .onValue p => s!"onValue{p.path}"
  | .onCause p => s!"onCause{p.path}"
  | .fin p => s!"fin{p.path}"
  | .restore _ => "restore"
  | .merge _ => "merge"
  | .gen p pc _ => s!"gen{p.path}@{pc}"
  | .loop p => s!"loop{p.path}"
  | .registerAwait _ => "registerAwait"
  | .cancelAwait _ => "cancelAwait"
  | .withWaiter b _ _ => s!"withWaiter({nameShape b})"
  | .abort => "abort"
  | .reFail _ => "reFail"
  | .scopeOpen p => s!"scopeOpen{p.path}"
  | .scopeProvide p _ => s!"scopeProvide{p.path}"
  | .scopeBody p _ => s!"scopeBody{p.path}"
  | .scopedExit _ _ => "scopedExit"
  | .scopeClose _ => "scopeClose"
  | .restoreCtx _ => "restoreCtx"
  | .forkScopedIn p => s!"forkScopedIn{p.path}"
  | .constant _ => "constant"
  | .store _ => "store"
  | .acquireCtx p => s!"acquireCtx{p.path}"
  | .acquireIn p _ => s!"acquireIn{p.path}"
  | .acquired p _ _ => s!"acquired{p.path}"
  | .afterScopeAdd _ _ => "afterScopeAdd"
  | .releaseUnder p _ _ => s!"releaseUnder{p.path}"
  | .releaseBody p _ _ => s!"releaseBody{p.path}"
  | .external _ _ origin => s!"external{origin}"
  | .caughtError p => s!"caughtError{p.path}"
  | _ => "otherName"

def thunkShape : EffThunk → String
  | .pure p => s!"pure{p.path}"
  | .body p => s!"body{p.path}"
  | .op _ => "op"
  | .park _ => "park"
  | .act p => s!"act{p.path}"
  | .forkInAt p _ => s!"forkInAt{p.path}"
  | .getCtx => "getCtx"
  | .setCtx _ => "setCtx"
  | .closeScope _ _ => "closeScope"
  | .store _ => "storeThunk"
  | .acquireMasked p _ => s!"acquireMasked{p.path}"
  | .releaseMasked p _ => s!"releaseMasked{p.path}"
  | _ => "otherThunk"

def primShape : Prim EffName EffThunk Val Err Defect FiberId Ann → String
  | .success _ => "success"
  | .failure _ => "failure"
  | .sync t => s!"sync({thunkShape t})"
  | .suspend t => s!"suspend({thunkShape t})"
  | .withFiber t => s!"withFiber({thunkShape t})"
  | .yieldableError _ => "yieldableError"
  | .iterator g _ => s!"iterator({nameShape g})"
  | .onSuccess _ n => s!"onSuccess({nameShape n})"
  | .onSuccessConst _ _ => "onSuccessConst"
  | .onFailure _ n => s!"onFailure({nameShape n})"
  | .onSuccessAndFailure _ a b => s!"onSAF({nameShape a};{nameShape b})"
  | .exitFrame _ => "exitFrame"
  | .onExit _ f flag => s!"onExit({nameShape f},{flag})"
  | .setInterruptible flag => s!"setInterruptible({flag})"
  | .whileLoop l _ => s!"whileLoop({nameShape l})"
  | .yieldNowWith _ => "yieldNow"
  | .async r _ _ => s!"async({nameShape r})"
  | .asyncFinalizer n => s!"asyncFinalizer({nameShape n})"

abbrev NF := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

def parkShape : Parked → String
  | .notParked => "free"
  | .withGuard _ => "guard"

/-- The role of a fiber: the root, a worker, the feeder, or a helper. -/
def role (f : NF) : String :=
  match f.id.value with
  | 0 => "root"
  | 1 => "worker"
  | 2 => "worker"
  | 3 => "feeder"
  | _ => "helper"

def shapeOf (f : NF) : String :=
  s!"{role f} {parkShape f.parked} running={f.running} intr={f.frame.interruptible} deferred={f.frame.deferredInterrupt} pending={f.frame.interruptedCause.isSome} override={repr f.yieldOverride}\n    {primShape f.frame.current}" ++
    String.join (f.frame.stack.map fun fr => s!"\n    | {primShape fr}")

/-- One move, with the tape's reading of its rows (seat WORKQ's `stepRead`). -/
def rowRead (s : Run) (c : Command) : Bool :=
  let phase := (Api.Runner.result s.runner c).phase
  phase != .frontier && (Effect4.Run.decisionOf s c phase).all (Effect4.Run.readsOn s)

def stepRead (state : Run × Bool) (move : Move) : Run × Bool :=
  (move.rows state.1).foldl (fun acc c => (acc.1.step c, acc.2 && rowRead acc.1 c)) state

structure Tally where
  nodes : Nat := 0
  funded : Nat := 0
  rest : Nat := 0
  maxOps : Nat := 0
  runningBetween : Nat := 0
  shapes : Std.HashSet String := {}
  restShapes : Std.HashSet String := {}
  badWithin : List (List Nat) := []
  badAccounted : List (List Nat) := []
  badSettled : List (List Nat) := []

def keep (xs : List (List Nat)) (path : List Nat) : List (List Nat) :=
  if xs.length < 3 then path :: xs else xs

def judge (hostly : Bool) (state : Run × Bool) (path : List Nat) (t : Tally) : Tally :=
  let s := state.1
  let live := s.machine.fibers.filter (·.exit.isNone)
  let r := atRest s
  let o := observe s
  let t := { t with
    nodes := t.nodes + 1
    maxOps := live.foldl (fun acc f => max acc f.currentOpCount) t.maxOps
    runningBetween := t.runningBetween + (if live.any (·.running) then 1 else 0)
    shapes := live.foldl (fun acc f => acc.insert (shapeOf f)) t.shapes
    restShapes := if r then live.foldl (fun acc f => acc.insert (shapeOf f)) t.restShapes else t.restShapes }
  if state.2 then
    let t := { t with funded := t.funded + 1, rest := t.rest + (if r then 1 else 0) }
    let t := if !o.heldWithin then { t with badWithin := keep t.badWithin path } else t
    let t := if hostly && r && !o.accounted then { t with badAccounted := keep t.badAccounted path } else t
    let t := if hostly && r && !o.settled then { t with badSettled := keep t.badSettled path } else t
    t
  else t

def search (hostly : Bool) (alphabet : List Move) : Nat → Run × Bool → List Nat → Tally → Tally
  | 0, state, path, t => judge hostly state path t
  | depth + 1, state, path, t =>
    let t := judge hostly state path t
    (List.range alphabet.length).foldl (fun t i =>
      match alphabet[i]? with
      | some move => search hostly alphabet depth (stepRead state move) (path ++ [i]) t
      | none => t) t

/-- Host acts, with cancellations of the first helpers. -/
def hostAlphabet : List Move :=
  [ .flush, .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨3⟩, .cancel ⟨4⟩, .cancel ⟨5⟩
  , .hold feederCall, .hold w1, .hold w2
  , .receive feederCall (ok (.nat 7)), .receive feederCall (ok (.nat 8))
  , .receive w1 (ok .unit), .receive w2 (ok .unit)
  , .receive w1 (failed "JobFailed" "bad payload"), .receive w2 (failed "Boom" "other")
  , .apply feederCall, .apply w1, .apply w2 ]

/-- The moves that only `held_within_fed` admits: forced yields, firing, raw evaluation, the
middleware latch, and interruptions with an interruptor. -/
def extraAlphabet : List Move :=
  [ .control (.yieldVerdict ⟨1⟩ true), .control (.yieldVerdict ⟨2⟩ true)
  , .control (.yieldVerdict ⟨3⟩ true), .control (.yieldVerdict ⟨4⟩ true)
  , .control (.yieldVerdict ⟨0⟩ true)
  , .control (.fire ⟨1⟩), .control (.fire ⟨3⟩), .control (.fire ⟨4⟩)
  , .control (.evaluate ⟨4⟩), .control (.evaluate ⟨5⟩)
  , .control .installMiddleware
  , .control (.interruptFrom (some ⟨2⟩) .empty ⟨1⟩) ]

def build (total : Nat) : Option Api.Built := (Effect4.Api.Author.build (crew total)).toOption

def bases : List (String × List Move) :=
  [ ("start", [.start]), ("parked", parked), ("running", running), ("blocked", blocked)
  , ("inflight", script [parked, [.receive feederCall (ok (.nat 1)), .apply feederCall]]) ]

def runCensus (hostly : Bool) (alphabet : List Move) (depth : Nat) : Tally :=
  match build 3 with
  | none => {}
  | some b =>
    bases.foldl (fun t (_, base) =>
      search hostly alphabet depth (base.foldl stepRead (opened b, true)) [] t) {}

def report (label : String) (t : Tally) : String :=
  s!"{label}: nodes={t.nodes} funded={t.funded} atRest={t.rest} maxOps={t.maxOps} runningBetween={t.runningBetween} shapes={t.shapes.size} restShapes={t.restShapes.size} bad: within={t.badWithin} accounted={t.badAccounted} settled={t.badSettled}"

end CensusProbe

open CensusProbe in
#eval do
  let t := runCensus true hostAlphabet 3
  IO.println (report "host acts, depth 3" t)
  IO.println "--- shapes at rest"
  for s in t.restShapes.toList do IO.println s
  IO.println "--- shapes not at rest"
  for s in t.shapes.toList do
    if !t.restShapes.contains s then IO.println s

open CensusProbe in
#eval do
  let t := runCensus false (hostAlphabet ++ extraAlphabet) 2
  IO.println (report "every move kind, depth 2" t)
  IO.println "--- shapes the host acts did not reach at depth 3"
  let host := runCensus true hostAlphabet 3
  for s in t.shapes.toList do
    if !host.shapes.contains s then IO.println s
