import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: the frames of each crew fiber at named runs, as name paths. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace QRProbe

def pt (p : Point) : String := s!"{p.path}|e{p.env.length}|f{p.fuel}"

def nameInfo : EffName → String
  | .cont p => s!"cont {pt p}"
  | .caught p => s!"caught {pt p}"
  | .onValue p => s!"onValue {pt p}"
  | .onCause p => s!"onCause {pt p}"
  | .fin p => s!"fin {pt p}"
  | .restore _ => "restore"
  | .merge _ => "merge"
  | .gen p pc b => s!"gen {pt p} pc{pc} {b}"
  | .loop p => s!"loop {pt p}"
  | .registerAwait c => s!"registerAwait {c.index}"
  | .cancelAwait c => s!"cancelAwait {c.index}"
  | .withWaiter b w t => s!"withWaiter({nameInfo b}, {w.value}, {t})"
  | .abort => "abort"
  | .reFail _ => "reFail"
  | .scopeOpen p => s!"scopeOpen {pt p}"
  | .scopeProvide p s => s!"scopeProvide {pt p} s{s}"
  | .scopeBody p _ => s!"scopeBody {pt p}"
  | .scopedExit _ s => s!"scopedExit s{s}"
  | .scopeClose s => s!"scopeClose s{s}"
  | .restoreCtx _ => "restoreCtx"
  | .forkScopedIn p => s!"forkScopedIn {pt p}"
  | .constant _ => "constant"
  | .store _ => "store"
  | .acquireCtx p => s!"acquireCtx {pt p}"
  | .acquireIn p _ => s!"acquireIn {pt p}"
  | .acquired p _ s => s!"acquired {pt p} s{s}"
  | .afterScopeAdd _ _ => "afterScopeAdd"
  | .releaseUnder p _ _ => s!"releaseUnder {pt p}"
  | .releaseBody p _ _ => s!"releaseBody {pt p}"
  | .external op _ origin => s!"external {origin}"
  | .caughtError p => s!"caughtError {pt p}"
  | _ => "otherName"

def thunkInfo : EffThunk → String
  | .pure p => s!"pure {pt p}"
  | .body p => s!"body {pt p}"
  | .op _ => "op"
  | .park _ => "park"
  | .act p => s!"act {pt p}"
  | .forkInAt p s => s!"forkInAt {pt p} s{s}"
  | .getCtx => "getCtx"
  | .setCtx _ => "setCtx"
  | .closeScope s _ => s!"closeScope s{s}"
  | .store _ => "storeThunk"
  | .acquireMasked p _ => s!"acquireMasked {pt p}"
  | .releaseMasked p _ => s!"releaseMasked {pt p}"
  | _ => "otherThunk"

def primInfo : Prim EffName EffThunk Val Err Defect FiberId Ann → String
  | .success _ => "success"
  | .failure _ => "failure"
  | .sync t => s!"sync({thunkInfo t})"
  | .suspend t => s!"suspend({thunkInfo t})"
  | .withFiber t => s!"withFiber({thunkInfo t})"
  | .yieldableError _ => "yieldableError"
  | .iterator g _ => s!"iterator({nameInfo g})"
  | .onSuccess _ n => s!"onSuccess({nameInfo n})"
  | .onSuccessConst _ _ => "onSuccessConst"
  | .onFailure _ n => s!"onFailure({nameInfo n})"
  | .onSuccessAndFailure _ a b => s!"onSAF({nameInfo a}; {nameInfo b})"
  | .exitFrame _ => "exitFrame"
  | .onExit _ f flag => s!"onExit({nameInfo f}, {flag})"
  | .setInterruptible flag => s!"setInterruptible({flag})"
  | .whileLoop l _ => s!"whileLoop({nameInfo l})"
  | .yieldNowWith _ => "yieldNow"
  | .async r _ _ => s!"async({nameInfo r})"
  | .asyncFinalizer n => s!"asyncFinalizer({nameInfo n})"

def parkedInfo : Parked → String
  | .notParked => "-"
  | .withGuard t => s!"guard {t}"

def fiberInfo (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : List String :=
  [s!"fiber {f.id.value}: exit={f.exit.isSome} running={f.running} parked={parkedInfo f.parked} ops={f.currentOpCount} intr={f.frame.interruptible} deferred={f.frame.deferredInterrupt} disp={f.dispatcher.buckets.length}",
   s!"  current: {primInfo f.frame.current}"] ++
  f.frame.stack.map (fun fr => s!"  | {primInfo fr}")

def runInfo (s : Run) : List String :=
  [s!"armed={s.machine.armed.map (·.value)} nextId={s.machine.nextId} nextToken={s.machine.nextToken} atRest={atRest s} funded={funded s}"] ++
  (s.machine.fibers.filter (fun f => f.exit.isNone)).flatMap fiberInfo

def built : Option Api.Built := (Effect4.Api.Author.build (crew 3)).toOption

def at? (moves : List Move) : List String :=
  match built with
  | some b => runInfo (Test.Dogfood.Scenario.play (opened b) moves)
  | none => ["no build"]

end QRProbe

open QRProbe in
#eval IO.println (String.intercalate "\n" (at? parked))

open QRProbe in
#eval IO.println (String.intercalate "\n" (at? running))

open QRProbe in
#eval IO.println (String.intercalate "\n" (at? blocked))
