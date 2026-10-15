import Test.Dogfood.Scenario.QueueWorkers.Program

/-!
# The queue crew's observation and clause propositions

Decisions rows 254 and 275. The scenario and its proof modules share these definitions.
The declarations retain their original names and bodies.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.QueueWorkers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)

/-- The budgets of every run of this battery but the starved one: the first scenario's. -/
def budget : Api.Budget := { fuel := 1000, compileFuel := 2000 }

/-- A built program opened under the scenario's name, at a command budget and the battery's
compile budget. -/
def openedAt (fuel : Nat) (b : Api.Built) : Run :=
  Run.open b "queue-workers" { budget with fuel := fuel }

/-- A built program opened under the scenario's name and the battery's budgets. -/
def opened (b : Api.Built) : Run := openedAt budget.fuel b

/-- A move of a host: the root's start, a flush, a clock step, a cancellation, a held call, a
reply receipt of a completion, and a reply application. A raw row is none, and no other control
is one. -/
def Move.hostAct : Move → Bool
  | .control (.evaluate fiber) => fiber == Api.root
  | .control .flush => true
  | .control (.advance _) => true
  | .control (.interruptFrom none _ _) => true
  | .control _ => false
  | .hold _ => true
  | .receive _ (.ofExit _) => true
  | .receive _ _ => false
  | .apply _ => true
  | .wire _ => false

/-! ## 3. The observation -/

/-- The entries of a log cell. -/
def entries : Option Val → List Val
  | some (.list values) => values
  | _ => []

/-- The queue's cell up to its handles. A waiting taker's identity and its hint are `Deferred`
handles, and so are a pending offer's. The view keeps how many stand in the cell, and it leaves
out which handle stands where. -/
structure QueueView where
  /-- The capacity. -/
  capacity : Nat
  /-- The buffered jobs, the earliest first. -/
  buffered : List Val
  /-- Each pending offer, the earliest first: its batch flag, and the jobs not yet accepted. -/
  offers : List (Bool × List Val)
  /-- The count of the waiting takers. -/
  takers : Nat
deriving DecidableEq

/-- Whether a value is a `Deferred` handle. -/
def isDeferred : Val → Bool
  | .handle 3 _ => true
  | _ => false

/-- A pending offer's record up to its handles: its identity and its hint are `Deferred`
handles, and it holds a batch flag and a list. `none` for any other value. -/
def offerView (offer : Val) : Option (Bool × List Val) :=
  match Machine.Record.read false offer "batch", Machine.Record.read false offer "hint",
      Machine.Record.read false offer "id", Machine.Record.read false offer "rest" with
  | some (.bool batch), some hint, some id, some (.list rest) =>
    if isDeferred hint && isDeferred id then some (batch, rest) else none
  | _, _, _, _ => none

/-- Whether a value is a waiting taker's record: an identity and a hint, both `Deferred`
handles. -/
def isTaker (taker : Val) : Bool :=
  match Machine.Record.read false taker "hint", Machine.Record.read false taker "id" with
  | some hint, some id => isDeferred hint && isDeferred id
  | _, _ => false

/-- The view of a value that has the shape of the queue's cell. `none` for any other value. -/
def queueView (cell : Val) : Option QueueView :=
  match Machine.Record.read false cell "cap", Machine.Record.read false cell "msgs",
      Machine.Record.read false cell "offers", Machine.Record.read false cell "takers" with
  | some (.nat capacity), some (.list buffered), some (.list offers), some (.list takers) =>
    if takers.all isTaker then
      (offers.mapM offerView).map fun pending => ⟨capacity, buffered, pending, takers.length⟩
    else none
  | _, _, _, _ => none

/-- What a run shows of the queue's cell. -/
inductive QueueCell
  /-- The root has not made the cell. -/
  | unmade
  /-- The cell, up to its handles. -/
  | holds (view : QueueView)
  /-- A value that has not the shape of the queue's cell. -/
  | malformed
deriving DecidableEq

/-- The reading of the queue's cell, by its allocation index. -/
def queueCell : Option Val → QueueCell
  | none => .unmade
  | some cell =>
    match queueView cell with
    | some view => .holds view
    | none => .malformed

/-- The view that the clauses read. A cell that is not made holds nothing. -/
def QueueCell.view : QueueCell → Option QueueView
  | .unmade => some ⟨capacity, [], [], 0⟩
  | .holds view => some view
  | .malformed => none

/-- The jobs that the host fed: the success value of each applied reply on `Jobs.take`, in the
order of the reply applications. The value is the stored reply's, read at the accepted reply
receipt of the same key. -/
def fedOf (s : Run) : List Val :=
  (rows s).filterMap fun
    | (.apply key, .applied) =>
      match seenAt s key with
      | some seen =>
        if seen.row == "Jobs.take" then
          (rows s).findSome? fun
            | (.submit reply, .preflight) =>
              if reply.key == key then
                match reply.completion with
                | .ofExit (.success value) => some value
                | _ => none
              else none
            | _ => none
        else none
      | none => none
    | _ => none

/-- The scenario's one observation. -/
structure Observation where
  /-- The assignment of jobs to workers: each `[job, worker]` the `assigned` cell holds, in the
  order the workers noted them. -/
  assignment : List Val
  /-- The queue's cell, up to its handles. -/
  queue : QueueCell
  /-- The jobs that the host fed, in the order of the reply applications. -/
  fed : List Val
  /-- The accepted reply receipts, in order, on both host rows. -/
  receipts : List Seen
  /-- The reply applications the session applied, in order, on both host rows. -/
  applications : List Seen
  /-- The retired calls, each with whether a reply waited for it. -/
  retired : List (Seen × Bool)
  /-- The identities of the opened connections, in opening order. -/
  opened : List Val
  /-- The cleanup identities: the connections the `released` cell holds, in release order. -/
  cleanups : List Val
  /-- The count of finished jobs: the `count` cell. -/
  finished : Option Val
  /-- The root's exit, or `none` while it is live. -/
  rootExit : Option ExitV
  /-- The work left: runnable fibers, armed owners, live calls, stored replies and timers. -/
  workLeft : Run.Work
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { assignment := entries (cell s 3)
    queue := queueCell (cell s 0)
    fed := fedOf s
    receipts := receipts s
    applications := applications s
    retired := retired s
    opened := entries (cell s 1)
    cleanups := entries (cell s 2)
    finished := cell s 4
    rootExit := s.exit
    workLeft := s.work }

/-! ### The readings of the clauses -/

/-- The job of an entry of the `assigned` cell. -/
def jobOf : Val → Option Val
  | .list [job, _] => some job
  | _ => none

/-- The job that the root's poll took at its exit: the last part of the root's answer. -/
def Observation.leftover (o : Observation) : List Val :=
  match o.rootExit with
  | some (.success (.list [_, _, _, .some job])) => [job]
  | _ => []

/-- The jobs that the queue or a worker holds or held: the buffered jobs, the jobs of the
pending offers, the assigned jobs, and the job that the root's poll took. -/
def Observation.held (o : Observation) : List Val :=
  (match o.queue.view with
    | some q => q.buffered ++ q.offers.flatMap (·.2)
    | none => []) ++ o.assignment.filterMap jobOf ++ o.leftover

/-- Whether the crew member with an identity is alive: its connection is opened and not
released. -/
def Observation.live (o : Observation) (id : Nat) : Bool :=
  o.opened.contains (.nat id) && !o.cleanups.contains (.nat id)

/-- Whether the crew member with an identity waits on a host call. A member's identity is its
fiber's number. -/
def Observation.calling (o : Observation) (id : Nat) : Bool :=
  o.workLeft.awaiting.any fun call => call.fiber == ⟨id⟩

/-- Whether the crew member with an identity is idle: alive, and waiting on no host call. At
rest an idle worker waits at the queue, and an idle feeder waits in its offer. -/
def Observation.idle (o : Observation) (id : Nat) : Bool := o.live id && !o.calling id

/-- Whether no job is held more often than the host fed it. -/
def Observation.heldWithin (o : Observation) : Bool :=
  o.held.all fun job => decide (o.held.count job ≤ o.fed.count job)

/-- Whether each fed job is held, but for one job of a feeder that is gone: the count of the
fed jobs is at most the count of the held ones, plus one where the feeder is not alive. -/
def Observation.accounted (o : Observation) : Bool :=
  decide (o.fed.length ≤ o.held.length + (if o.live 3 then 0 else 1))

/-- Whether the queue is settled. Five parts.

1. The cell is not made, or it has the first profile's shape at the scenario's capacity: each
   pending offer holds one job and no batch.
2. The waiting takers are the idle workers, by their count.
3. One offer pends where the feeder is idle, and none otherwise.
4. No job is buffered while a taker waits.
5. An offer pends only at a full buffer, and the buffer is within its capacity. -/
def Observation.settled (o : Observation) : Bool :=
  match o.queue.view with
  | none => false
  | some q =>
    q.capacity == capacity && q.offers.all (fun offer => !offer.1 && offer.2.length == 1) &&
    q.takers == ([1, 2].filter o.idle).length &&
    q.offers.length == (if o.idle 3 then 1 else 0) &&
    (q.buffered.isEmpty || q.takers == 0) &&
    (q.offers.isEmpty || q.buffered.length == q.capacity) &&
    decide (q.buffered.length ≤ q.capacity)

/-- Whether no connection is released twice. -/
def Observation.releasedOnce (o : Observation) : Bool := decide o.cleanups.Nodup

/-- A `[job, worker]` entry of the `assigned` cell. -/
def gave (job worker : Nat) : Val := .list [.nat job, .nat worker]

/-- The executable check of the accepted terminal external-reply profile. -/
def terminalReplyRow : Api.Runner.Command × Api.HostSession.Phase → Bool
  | (.submit reply, .preflight) => match reply.completion with
    | .ofExit _ => true
    | .ofRefGet _ => false
  | _ => true

/-- The accepted reply profile, read directly from the recorded journal and verdicts. -/
def terminalRepliesCheck (s : Run) : Bool := (Scenario.rows s).all terminalReplyRow

/-- Accepted external reply receipts contain terminal exits.
The profile permits every control and every refused row. -/
def TerminalReplies (s : Run) : Prop :=
  ∀ reply : Api.HostSession.Reply,
    (Api.Runner.Command.submit reply, Api.HostSession.Phase.preflight) ∈ Scenario.rows s →
      ∃ exit, reply.completion = .ofExit exit

/-- The proposition of `held_within_fed`. -/
def HeldWithinFed : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    TerminalReplies (Scenario.play (openedAt fuel b) moves) →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).heldWithin = true

/-- The proposition of `fed_accounted`. -/
def FedAccounted : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b → moves.all Move.hostAct = true →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    atRest (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).accounted = true

/-- The proposition of `queue_settled`. -/
def QueueSettled : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b → moves.all Move.hostAct = true →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    atRest (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).settled = true

/-- The proposition of `releases_once`. -/
def ReleasesOnce : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).releasedOnce = true

end Test.Dogfood.Scenario.QueueWorkers
