import Effect4.Run.Live
import Effect4.Run.Tape

/-!
# Run.View — the session's view: one first-order record a holder reads

Slice DM3 of the session note (`docs/research/2026-10-07-session-api-design.md` §3.3). The live
call view of the host-call note folds into it (HC-1, decisions row 373 (12);
`docs/research/2026-10-09-host-calls-and-cleanup.md` §6.3), with the internal waits of decisions
row 333 (3). `Live.view` reads a live run as one record, and `Live.at` reads it after a prefix of
its journal.

* **The calls the machine waits on** (`awaiting`). Each entry has three groups, and no lifecycle
  value is stored. The current request is the machine's: the key, the row and the request
  (`Await`). The checked source is the call table's: the call's address and its checked instance,
  the type a reply must meet, or `none` where the lookup fails. The binding is the ledger's: the
  call id, and the completion received and not applied.
* **The internal waits** (`waits`). A fiber parked on a guard, on no host call and on no timer,
  with what it parked through, as data (`WaitSite`): the deferred cell it awaits, or another
  registration. The compiler's continuation name stays inside the machine. `emptyFrontier` flags a live machine whose frontier
  names nothing: at a live, unfinished machine that is a deadlock (`frontier_empty_iff_deadlocked`,
  `src/Effect4/Laws/Api/Frontier.lean`). No frontier reason is added.
* **The run's own readings.** The protocol state, the outcome, the root's exit and the frontier
  reasons; the retired calls and the count of applications; the runnable fibers, the armed owners,
  the timers, the cells and each fiber's status; the number of run commands, `funded` and `atRest`.

`funded` is read off the session's bit and the journal's verdicts, with no replay: no reply
application was cut by its fuel (`Session.funded`, slice DM4), and no run command ended at a
frontier. It is `Run.funded` (`view_funded`, `src/Effect4/Laws/Api/Live.lean`). Where a reading had
two owners, the view keeps one: the session's
pending replies are the received completions of the awaited calls, since a held call is an awaited
call.

The view holds no machine and no function, so a generated codec can be written for it. Its
`Canonical` instance is the generator's (`tools/Effect4Gen/manifest.json`, the `Runner` group).

This file is no `module` file: it imports `Effect4.Run.Basic`, an importer of the specialization
sites of decisions row 202.
-/

set_option autoImplicit false

namespace Effect4

open Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Answer)

namespace Live

/-- The session's record of a call that it holds: the call id it bound the call under, and the
completion it received for the call and has not applied. -/
structure HeldCall where
  callId : Nat
  received : Option Answer
deriving DecidableEq

/-- **One call the machine waits on, as a host reads it** (the live call view, HC-1). -/
structure CallView where
  /-- The current request: the parked fiber, the guard token, the row and the request. -/
  await : Await
  /-- The address of the call in the program, which its registration keeps (`originOf`). -/
  origin : Option (List Nat)
  /-- The call's checked instance at that address: the type that a reply must meet. `none` where
  the lookup fails. -/
  checked : Option (CallInstance NativeOp)
  /-- The session's record of the call, when the session holds it. -/
  held : Option HeldCall
deriving DecidableEq

/-- **What a fiber in an internal wait parked through**, as first-order data: the deferred cell it
awaits, or a registration the view does not name (a race's count, a layer's build). -/
inductive WaitSite where
  | deferred (cell : DeferredKey)
  | other
deriving DecidableEq

/-- **A fiber in an internal wait** (decisions row 333 (3)): parked on a guard, on no host call and
on no timer. -/
structure WaitView where
  fiber : FiberId
  token : Nat
  /-- What it parked through, when its code is an `Async` (`WaitSite`). `none` for a park that the
  frame alphabet does not spell: a join. -/
  site : Option WaitSite
deriving DecidableEq

/-- **The session's view**: what a holder reads off a live run, as first-order content. -/
structure View where
  /-- The protocol state: idle, awaiting a host, parked, or terminated. -/
  state : Api.HostProtocol.State
  /-- Finished, a live frontier, or a state the runtime cannot reach. -/
  outcome : Api.Outcome
  /-- The root's exit, or `none` while it is live. -/
  exit : Option ExitV
  /-- Why the run is still live. -/
  reasons : List Api.FrontierReason
  /-- The calls the machine waits on, in the machine's order, each with its checked source and
  the session's record of it. -/
  awaiting : List CallView
  /-- The fibers in an internal wait, in the machine's order. -/
  waits : List WaitView
  /-- A live frontier that names nothing. -/
  emptyFrontier : Bool
  /-- The keys whose call was retired, in retirement order. -/
  retired : List Key
  /-- How many completions were applied. -/
  applied : Nat
  /-- The runnable fibers, in the machine's order. -/
  runnable : List FiberId
  /-- The armed owners, in arming order. -/
  queued : List FiberId
  /-- Each sleeping fiber with the clock reading it wakes at. -/
  timers : List (FiberId × ClockMillis)
  /-- The cells, in allocation order. -/
  cells : List Val
  /-- Every fiber with what holds it, in creation order. -/
  fibers : List (FiberId × Api.FiberStatus)
  /-- How many run commands the journal holds. -/
  steps : Nat
  /-- No task of the run was cut by its budget: `Run.funded`, read with no replay. -/
  funded : Bool
  /-- No runnable fiber and no armed owner (`Run.atRest`). -/
  atRest : Bool
deriving DecidableEq

end Live

namespace Run

open Live (CallView WaitSite WaitView View)

/-- The live call view of one call that the machine waits on: its request, its checked source and
the session's record of it. -/
def callView (s : Run) (call : Await) : CallView :=
  let key : Key := ⟨call.fiber, call.token⟩
  let origin := originOf s.machine call.fiber call.token
  { await := call
    origin := origin
    checked := origin.bind s.session.callInstance
    held := (s.session.active.find? (·.key == key)).map fun bound =>
      ⟨bound.call.callId,
        (Api.HostSession.readReply s.session.pending key).map (·.completion)⟩ }

/-- The wait site a registration names: a deferred's await is its cell. -/
def siteOf : EffName → WaitSite
  | .registerAwait cell | .awaitPromise cell => .deferred cell
  | .withWaiter base _ _ => siteOf base
  | _ => .other

/-- What a fiber parked through, when its code is an `Async`. -/
def waitSiteOf (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) :
    Option WaitSite :=
  match f.frame.current with
  | .async register _ _ => some (siteOf register)
  | _ => none

/-- The fibers in an internal wait: each live fiber parked on a guard, on no host call
(`requestOf`) and on no timer. -/
def internalWaits (m : Api.Machine) : List WaitView :=
  m.fibers.filterMap fun f =>
    match f.exit, f.parked with
    | none, .withGuard token =>
      if (requestOf m f.id token).isSome then none
      else if m.state.timers.wake.waiters.any (·.fiber == f.id) then none
      else some ⟨f.id, token, waitSiteOf f⟩
    | _, _ => none

/-- **The session's view of a run.** -/
def view (s : Run) : View :=
  let read := s.inspect
  { state := Api.HostProtocol.observe s.machine
    outcome := read.outcome
    exit := read.exit
    reasons := read.reasons
    awaiting := (awaits s.machine).map s.callView
    waits := internalWaits s.machine
    emptyFrontier := read.outcome == .frontier && read.reasons.isEmpty
    retired := s.session.retired.map (·.bound.key)
    applied := s.session.applied
    runnable := Api.runnableFibers s.machine
    queued := s.machine.armed
    timers := s.machine.state.timers.wake.waiters.map fun w => (w.fiber, w.payload)
    cells := s.machine.state.refs
    fibers := Api.fiberStatuses s.machine
    steps := s.journal.length
    funded := s.session.funded && !s.phases.any (· == .frontier)
    atRest := Run.atRest s }

end Run

namespace Live

/-- **The session's view of a live run** (decisions row 326 (1)). -/
def view (l : Live) : View := l.run.view

/-- The live run after the first `steps` run commands of its journal: the journal's prefix played
from the run's fresh open. -/
def upTo (l : Live) (steps : Nat) : Live :=
  ⟨(Run.openedOf l.run).play (l.run.journal.take steps),
    l.run.built, l.run.id, l.run.budget, l.run.profile, l.run.journal.take steps, rfl⟩

/-- **The view after the first `steps` run commands**: a run stepped and drawn one command at a
time (the session note §3.3). -/
def «at» (l : Live) (steps : Nat) : View := (l.upTo steps).view

end Live

end Effect4
