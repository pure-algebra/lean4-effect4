import Effect4.Run.Basic

/-!
# Run.Event — one thing a caller hands a run, and the run commands it turns into

The session's events (decisions row 326 (1); slice DM1 of the session note,
`docs/research/2026-10-07-session-api-design.md` §3.2). They stood in the scenario driver
(`Test/Dogfood/Scenario.lean`) as `Move`. Three things changed on the way here.

* **A selector by key.** `Sel.key` names a call exactly, beside `Sel.fiber` and `Sel.row`.
* **Unresolved.** A selector that names two live calls names none (decisions row 326 (4)). The
  driver took the first in the machine's order, and no order of the machine chooses for a caller
  (`docs/core/api-surface.md` §1.1).
* **The raw row is `wire`.** A remote host's run command carries the claims that it wrote, and the
  session checks them.

What each part does:

* **The events.** A control, a hold, a reply receipt, a reply application and a remote host's run
  command. An event only turns into run commands (`Event.commands`). The journal stays
  `List Command` (row 326 (4)), so a run stores no event.
* **The selectors.** A selector is resolved against the calls the machine waits on (`live`). With
  none of them, it is resolved against the calls the host holds or held (`held`), for a late reply.
* **Feeding.** `feed` plays an event's commands through `Run.play`, so every law of rows holds of
  it (`feed_fst`). Its verdict is the phase of each command played, or the unresolved selector.

A local event's claims are built from what the machine holds (`Call.at`). So it never carries a
fiber number, a guard token or a call id that the caller wrote.

This file is no `module` file: it imports `Effect4.Run.Basic`, an importer of the specialization
sites of decisions row 202.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Phase Answer)
open Effect4.Api.Runner (Command)

/-! ## How an event names a call -/

/-- A call as the host sees it: the row's spelling, the request, and the key that selects it. -/
structure Seen where
  row : String
  request : Val
  key : Key
deriving DecidableEq

/-- How an event names a call. -/
inductive Sel
  /-- The call at this key: a fiber and the guard token it parked on. -/
  | key (key : Key)
  /-- The call this fiber is parked on. A fiber parks on one call at a time. -/
  | fiber (id : FiberId)
  /-- The call on the row with this spelling. -/
  | row (spelling : String)
deriving DecidableEq

/-- Whether a selector names a call. -/
def Sel.names (sel : Sel) (call : Seen) : Bool :=
  match sel with
  | .key exact => call.key == exact
  | .fiber id => call.key.fiber == id
  | .row spelling => call.row == spelling

/-- The calls the machine is waiting on, as the host sees them, in the machine's order. -/
def live (s : Run) : List Seen :=
  s.outstanding.filterMap fun await =>
    (s.rowOf await.op).map fun row =>
      ⟨row.spelling, await.request, ⟨await.fiber, await.token⟩⟩

/-- A journal row with its verdict. -/
def rows (s : Run) : List (Command × Phase) := s.journal.zip s.phases

/-- The calls' claims that the host holds or held: the accepted `bind` rows, in order, each with
its guard token. -/
def bound (s : Run) : List (Call × Nat) :=
  (rows s).filterMap fun
    | (.bind call token, .bound) => some (call, token)
    | _ => none

/-- A held call's claim as the host sees it. -/
def seenOf (s : Run) (entry : Call × Nat) : Option Seen :=
  (s.rowOf entry.1.op).map fun row =>
    ⟨row.spelling, entry.1.request, ⟨entry.1.fiber, entry.2⟩⟩

/-- The calls the host holds or held, in the order it got them. -/
def held (s : Run) : List Seen := (bound s).filterMap (seenOf s)

/-- The one live call that a selector names. `none` when it names no live call, or two. -/
def Sel.one (sel : Sel) (s : Run) : Option Seen :=
  match (live s).filter sel.names with
  | [call] => some call
  | _ => none

/-- The key that a selector names. It is the key of the one live call that the selector names.
With no such live call, it is the key of the latest call the host held that the selector names,
so a late reply can name a call the machine dropped. With two such live calls, it is `none`
(decisions row 326 (4)). -/
def Sel.resolve (sel : Sel) (s : Run) : Option Key :=
  match (live s).filter sel.names with
  | [call] => some call.key
  | [] => ((held s).reverse.find? sel.names).map (·.key)
  | _ :: _ :: _ => none

/-! ## The events -/

/-- One thing a caller hands a run (decisions row 326 (1)). -/
inductive Event
  /-- A control decision: evaluate, flush, a clock step, an interruption. -/
  | control (decision : Api.Decision)
  /-- The host takes the call and holds it: the session binds the call, with no reply. -/
  | hold (call : Sel)
  /-- The reply receipt: the session stores the host answer for the call. The machine does not
  run. -/
  | receive (call : Sel) (completion : Answer)
  /-- The reply application: the session applies the stored reply at the call's key. -/
  | apply (call : Sel)
  /-- A remote host's run command, with the claims that it wrote. The session checks them. -/
  | wire (command : Command)
deriving DecidableEq

/-- The root evaluated: the event that starts a run. -/
def Event.start : Event := .control Api.evaluate

/-- Every armed dispatcher drained. -/
def Event.flush : Event := .control Api.flush

/-- The logical clock advanced by `millis`. -/
def Event.tick (millis : Nat) : Event := .control (Api.TestClock.adjust (ClockMillis.ofNat millis))

/-- The host cancels a fiber: `interruptUnsafe` with no interruptor. -/
def Event.cancel (fiber : FiberId) : Event := .control (.interruptFrom none .empty fiber)

/-- The run commands that an event plays on a run, or its selector when the selector is
unresolved. A hold names a live call. A reply for a call the host holds or held is one `submit`
row against that call's claim. A reply for a live call the host does not hold is the two rows of
`Rows.receive`. -/
def Event.commands (s : Run) : Event → Except Sel (List Command)
  | .control decision => .ok [.control decision]
  | .hold call =>
    match call.one s with
    | none => .error call
    | some seen =>
      match Call.at s seen.key with
      | none => .error call
      | some claim => .ok [.bind claim seen.key.token]
  | .receive call completion =>
    match call.resolve s with
    | none => .error call
    | some key =>
      match (bound s).reverse.find? (fun entry => (⟨entry.1.fiber, entry.2⟩ : Key) == key) with
      | some entry => .ok [.submit (Rows.reply s entry.1 key completion)]
      | none => .ok (Rows.receive s key completion)
  | .apply call =>
    match call.resolve s with
    | none => .error call
    | some key => .ok [.apply key]
  | .wire command => .ok [command]

/-- The run commands that an event plays: none when its selector is unresolved. -/
def Event.rows (s : Run) (event : Event) : List Command :=
  match event.commands s with
  | .ok commands => commands
  | .error _ => []

/-! ## Feeding a run -/

/-- What feeding one event did. -/
inductive Verdict
  /-- The phase of each run command played, in order. -/
  | played (phases : List Phase)
  /-- The selector named no call, or two live calls: nothing was played. -/
  | unresolved (call : Sel)
deriving DecidableEq

/-- Feed one event: play its run commands and keep the phase of each. An unresolved selector
plays nothing. -/
def feed (s : Run) (event : Event) : Run × Verdict :=
  match event.commands s with
  | .error call => (s, .unresolved call)
  | .ok commands =>
    let after := s.play commands
    (after, .played (after.phases.drop s.phases.length))

/-- **Feeding plays the event's run commands.** The run after an event is the run that its
commands reach, and the same run when its selector is unresolved.

Placement: concept `host-session-protocol`. It is a step of the driver's laws `replays` (R13) and
`receipt_inert` (R6), whose consumer is every scenario of `Test/Dogfood/Scenario/`. Reach: every
run and every event. It says nothing of the verdicts of the commands. -/
theorem feed_fst (s : Run) (event : Event) : (s.feed event).1 = s.play (event.rows s) := by
  unfold feed Event.rows
  cases event.commands s with
  | error call => rfl
  | ok commands => rfl

end Effect4.Run
