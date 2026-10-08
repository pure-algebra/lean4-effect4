import Effect4.Run.Tape
import Effect4.Modules.Queue.Defs
import Effect4.Api.Author

/-!
# A finite probe: where a composed module meets the host session (seat HOST, 2026-10-08)

Research note `docs/research/2026-10-08-host-authoring-boundary.md`, sections 4 and 5. This file
is no battery: it is not reachable from `Test/All.lean`. Run it with
`scratch/lean-slot.sh lake env lean <this file>`. Each line is a finite evaluation on the frame
machine, at one budget and one script. The budget is the default (`Api.Budget`), below the
operation budget, so each run is budget-quiet by the SIM note's reading (its section 2.5).
Nothing here is a theorem.

* **Part A** (the note's question 3). A program installs the Queue's definitions
  (`Queue.Definitions`, `src/Effect4/Modules/Queue/Defs.lean`) and declares one host row. A
  child waits on the queue's internal hint while the root waits on the host. The probe reads
  what the session shows: the protocol state, the frontier reasons and the work view. A second
  program waits on the queue's hint alone. Its controls show that the session cannot answer an
  internal wait.
* **Part B** (the note's section 5.4). One client, filled two ways: the Queue's
  `offer` inline (no definition block) and as an invocation of the installed definitions (a
  block at the root). The client calls a template host row, `List<A>` to `Option<A>`, as
  `Test/Api/TypedReplies.lean` does. The probe reads the session's call table and the
  admission of the reply `some 1`, which only the call's checked instance admits (row 323). It
  also counts the addresses that the address table reaches in each filling.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Probe.HostBoundary

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-! ## Shared pieces -/

/-- The Queue's definitions at numbers, under one instance name. -/
def numbers := Queue.Definitions.make "numbers" .nat

/-- The budget of every run here: the default. -/
def budget : Api.Budget := {}

/-- A module that builds, opened under one name, with the root evaluated. -/
def startOf (m : Module NativeOp) : Option Run :=
  (Api.Author.build m).toOption.map fun b => (Run.open b "probe" budget).play Rows.start

/-- What holds each live fiber: `run` for a fiber with no park, `host` for a park on an
external row (the host can answer it), `internal` for any other park. -/
def holds (m : Api.Machine) : List (Nat × String) :=
  m.fibers.filterMap fun f =>
    if f.exit.isSome then none
    else match f.parked with
      | .notParked => some (f.id.value, "run")
      | .withGuard token =>
        some (f.id.value, if (requestOf m f.id token).isSome then "host" else "internal")

/-- The first live fiber parked on an internal wait, with its token. -/
def internalKey (m : Api.Machine) : Option Api.HostSession.Key :=
  m.fibers.findSome? fun f =>
    if f.exit.isSome then none
    else match f.parked with
      | .notParked => none
      | .withGuard token =>
        if (requestOf m f.id token).isSome then none else some ⟨f.id, token⟩

/-- The key of the first call the machine waits on: the session's own reading, never assumed. -/
def hostKey (s : Run) : Option Api.HostSession.Key :=
  s.outstanding.head?.map fun a => ⟨a.fiber, a.token⟩

/-- The work view as numbers: runnable fibers, armed owners, awaited calls' fibers, receipts,
timers. -/
def workOf (s : Run) : List Nat × List Nat × List Nat × Nat × Nat :=
  let w := s.work
  (w.runnable.map (·.value), w.queued.map (·.value), w.awaiting.map (·.fiber.value),
    w.pending.length, w.timers.length)

/-- The session's reading: protocol state, outcome and frontier reasons. -/
def readingOf (s : Run) : Api.HostProtocol.State × Api.Outcome × List Api.FrontierReason :=
  let o := s.observe
  (o.state, o.outcome, o.reasons)

/-! ## Part A, run 1: an internal wait beside a host wait -/

/-- One host row: the host answers a number. -/
def fetch : RowDef := Row.host "Host.fetch" .unit .nat

/-- A child takes from an empty queue and waits on its hint. The root calls the host, offers
the answer and joins the child. -/
def crewMain : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let t ← fork (numbers.take q)
  let x ← Row.call fetch unit
  let _ ← numbers.offer q x
  join t

def crew : Module NativeOp := { numbers.module crewMain with rows := [fetch] }

def crewStarted : Option Run := startOf crew

#eval crewStarted.map fun s => (readingOf s, holds s.machine, workOf s)

-- finite evaluation: the root waits on the host and the child on the queue's hint
#guard crewStarted.map (fun s => holds s.machine) = some [(0, "host"), (1, "internal")]
-- finite evaluation: the protocol reads `awaitingAsync`, and the reasons name the host call
-- alone: the child's internal wait is named by no reason
#guard crewStarted.map (fun s => (s.observe.state, s.observe.reasons)) =
  some (.awaitingAsync, [.awaitHost ⟨Api.root, 1⟩])
#guard crewStarted.bind hostKey = some ⟨Api.root, 1⟩
-- finite evaluation: the work view names the host call, and no runnable fiber or armed owner
#guard crewStarted.map workOf = some ([], [], [0], 0, 0)

/-- The host answers the root's call with 7, at the key the session names, and the dispatcher
is flushed twice. -/
def crewAnswered : Option Run :=
  crewStarted.bind fun s => (hostKey s).map fun k =>
    ((s.answer k (.ofExit (.success (.nat 7)))).play Rows.flush).play Rows.flush

#eval crewAnswered.map fun s => (readingOf s, holds s.machine, workOf s,
  s.phases.map fun p => reprStr p)

-- finite evaluation: the offer wakes the child through a posted helper, the child takes 7, and
-- the root's join answers it
#guard crewAnswered.map (fun s => decide (s.exit = some (.success (.nat 7)))) = some true

/-! ## Part A, controls: the session cannot answer an internal wait -/

/-- The child's internal park at run 1's start. -/
def childKey : Option Api.HostSession.Key := crewStarted.bind fun s => internalKey s.machine

#eval childKey.map fun k => (k.fiber.value, k.token)

-- control: no call stands at the child's key, so a receipt there plays no row
#guard (crewStarted.bind fun s => childKey.map fun k => (Api.HostSession.Call.at s k).isNone) =
  some true
#guard (crewStarted.bind fun s => childKey.map fun k =>
  (Rows.receive s k (.ofExit (.success .unit))).isEmpty) = some true
-- control: a forged claim at the child's key is refused as a stale call
#guard (crewStarted.bind fun s => childKey.map fun k =>
  (Api.HostSession.bindCall s.session
    ⟨Api.HostSession.version, s.id, s.built.table, s.session.nextCall, k.fiber, .external 0, .unit⟩
    k.token).phase) = some (.refused .staleCall)
-- control: the machine's admission names the park as no external call
#guard (crewStarted.bind fun s => childKey.map fun k =>
  Program.admit s.built.table s.machine (.answerAsync k.fiber k.token (.ofExit (.success .unit)))) =
  some (some (.notExternal ⟨1⟩ 0))
-- control: an answer given as a control is refused before it reaches the machine
#guard (crewStarted.bind fun s => childKey.map fun k =>
  (Api.HostSession.advance s.session budget.fuel
    (.answerAsync k.fiber k.token (.ofExit (.success .unit)))).phase) =
  some (.refused .directAnswer)

/-! ## Part A, run 2: an internal wait alone -/

/-- The root takes from an empty queue. Nothing else runs. -/
def lonelyMain : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  numbers.take q

def lonelyFlushed : Option Run := (startOf (numbers.module lonelyMain)).map (·.play Rows.flush)

#eval lonelyFlushed.map fun s => (readingOf s, holds s.machine, workOf s, s.exit.isSome,
  s.machine.finished)

-- finite evaluation: the protocol reads `parked`, the outcome is a frontier, and the frontier
-- names no reason. `frontier_empty_iff_deadlocked` (`src/Effect4/Laws/Api/Frontier.lean`)
-- reads this as a deadlock: live, unfinished, nothing armed, no host call, no timer
#guard lonelyFlushed.map readingOf = some (.parked, .frontier, [])
#guard lonelyFlushed.map (fun s => (holds s.machine, workOf s)) =
  some ([(0, "internal")], ([], [], [], 0, 0))
#guard lonelyFlushed.map (fun s => (s.machine.stuck.isNone, s.machine.finished)) =
  some (true, false)

/-! ## Part B: one client, filled two ways, against the session's typed replies -/

/-- The template row of decisions row 183: `List<A>` to `Option<A>`, as `Row.host` declares it. -/
def firstRow : RowDef := Row.host "L.first" (.list (.var 0)) (.option (.var 0))

/-- The list `[1]`. -/
def oneList : TermSrc := app "cons" [nat 1, nilT]

/-- The client: a queue, the host call on `[1]`, one offer, and the host's answer. The offer is
the filling: inline, or an invocation of the installed definitions. -/
def clientMain (offer : TermSrc → TermSrc → Src NativeOp) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let o ← Row.call firstRow oneList
  let _ ← offer q (nat 3)
  return o

/-- Filling 1: the library's `offer` inline, with no definition block. -/
def inlineClient : Module NativeOp :=
  { rows := [firstRow], main := clientMain (Queue.offer .nat) }

/-- Filling 2: the same client, invoking the installed definitions: a block at the root. -/
def definedClient : Module NativeOp :=
  { numbers.module (clientMain numbers.offer) with rows := [firstRow] }

def builtOf (m : Module NativeOp) : Option Api.Built := (Api.Author.build m).toOption

/-- The reply that only the call's checked instance admits, and the one every instance admits. -/
def some1 : Api.HostSession.Answer := .ofExit (.success (.some (.nat 1)))
def nothing : Api.HostSession.Answer := .ofExit (.success .none)

/-- The verdict of the receipt of one answer at the root's call: its last phase. -/
def receiptOf (m : Module NativeOp) (a : Api.HostSession.Answer) :
    Option Api.HostSession.Phase :=
  (startOf m).bind fun s => (hostKey s).bind fun k => (s.receive k a).phases.getLast?

/-- The session's reading of the call's instance: the call table's length, the registration's
address, and the instance's answer column at that address. -/
def instanceOf (m : Module NativeOp) : Option (Nat × Option (List Nat) × Option Ty) :=
  (builtOf m).bind fun b => (startOf m).bind fun s => (hostKey s).map fun k =>
    let origin := originOf s.machine k.fiber k.token
    ((Api.HostSession.callTable b.program b.table).length, origin,
      (origin.bind fun o => s.session.callInstance o).map (·.answer))

#eval (instanceOf inlineClient, instanceOf definedClient)
#eval ((receiptOf inlineClient some1).map reprStr, (receiptOf definedClient some1).map reprStr,
  (receiptOf inlineClient nothing).map reprStr, (receiptOf definedClient nothing).map reprStr)

-- finite evaluation: both fillings build, and each parks the root on the host call
#guard (startOf inlineClient).map (·.outstanding.length) = some 1
#guard (startOf definedClient).map (·.outstanding.length) = some 1
-- finite evaluation: filling 1's call table lists every `perform` with its instance (nine:
-- the inline `offer`'s native calls and the host call), and the host call at `[1, 0]` has the
-- instance `Option<number>`
#guard instanceOf inlineClient = some (9, some [1, 0], some (.option .nat))
-- finite evaluation: filling 2's call table is empty, so its host call at `[1, 1, 0]` (the
-- main program is child 1 of the block) has no instance
#guard instanceOf definedClient = some (0, some [1, 1, 0], none)
-- finite evaluation: `some 1` is admitted in filling 1, and refused in filling 2
#guard receiptOf inlineClient some1 = some .preflight
#guard receiptOf definedClient some1 = some (.refused .envelope)
-- control: the value every instance admits takes the row's own path in both fillings
#guard receiptOf inlineClient nothing = some .preflight
#guard receiptOf definedClient nothing = some .preflight
-- finite evaluation: in filling 1 the program answers what the host gave
#guard ((startOf inlineClient).bind fun s => (hostKey s).map fun k =>
  let r := (s.receive k some1).play [.apply k]
  decide (r.exit = some (.success (.some (.nat 1))))) = some true

/-! ## Part B, the reach of the same cause: the address table

The session's call table reads the focus function (`callAt`), and the address table reads the
same step (`Node.envAt`, `src/Effect4/Program/Typing/Table.lean`). So the probe counts, in each
filling, the addresses that have a typing environment, out of all addresses. -/

/-- The address table at the build's signature: the addresses with an environment, all
addresses, and the count of refusals. -/
def reachOf (m : Module NativeOp) : Option (Nat × Nat × Nat) :=
  (builtOf m).map fun b =>
    let t := Program.table (SigApp.signature ⟨b.table, []⟩) [] b.program
    ((t.filter fun e => e.env.isSome).length, t.length,
      (Program.refusals (SigApp.signature ⟨b.table, []⟩) [] b.program).length)

#eval (reachOf inlineClient, reachOf definedClient)

-- finite evaluation: in filling 1 every address has an environment, and nothing is refused
#guard (reachOf inlineClient).map (fun x => decide (x.1 = x.2.1 ∧ x.2.2 = 0)) = some true
/-- The refusals that the address table reports, at their paths, as text. -/
def refusalsOf (m : Module NativeOp) : Option (List (List Nat × String)) :=
  (builtOf m).map fun b =>
    (Program.refusals (SigApp.signature ⟨b.table, []⟩) [] b.program).map fun r =>
      (r.path, r.reason.head)

#eval refusalsOf definedClient

-- finite evaluation: in filling 2 only the block itself has an environment, and the table
-- reports one refusal, at the root, for a program that the build admitted
#guard (reachOf definedClient).map (fun x => (x.1, x.2.2)) = some (1, 1)

end Probe.HostBoundary
