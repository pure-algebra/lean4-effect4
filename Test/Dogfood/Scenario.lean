import Effect4.Laws.Run
import Effect4.Laws.Auto.Semantics
import ProofGraph.Goal

/-!
# Test.Dogfood.Scenario — the shared driver of the scenarios, and a scenario's record

Decisions row 254 (owner, 2026-10-05) asks for dogfooding that tests the semantics where features
compose, with no check outside a placed theorem or planned goal. A scenario is one unit with six
parts (`Test/Dogfood/README.md`): a program, a script, one named observation, a claim, the controls
and the lowered runs. This module holds what the scenarios share.

* **The script alphabet.** A `Move` is one thing a host does: a control decision, holding a call
  (`hold`), a reply receipt (`receive`), a reply application (`apply`), or one raw row for a red
  control. A script is a `List Move`: first-order data.
* **The driver.** `play` turns each move into rows of the run's own journal (`Move.rows`) and plays
  them through `Run.play`. It adds no scheduler and no program representation. The run it reaches
  is the run its journal reaches (`replays`), so a replay resolves no selector and calls no fixture.
* **Selection by key.** A move names a call by its fiber or by its row (`Sel`). The driver resolves
  the name to the key of a live call, and `Api.HostSession.Call.at` builds the call's claim.
* **Reply receipt and reply application apart.** `receive` plays the rows of `Rows.receive`, or the
  one `submit` row when the host already holds the call. `apply` plays the one row `.apply key`.
  The driver never plays `Rows.answer`: after a reply receipt it would bind and submit again.
* **The readers.** `receipts`, `applications`, `refusals` and `retired` read the session's part of
  an observation from the journal, its verdicts and the session's ledger.
* **The machine's tape.** `tapeFrom` reads the decisions that moved the machine off a journal:
  each control that progressed and each reply application. `machineView` is the machine's part
  of an observation. A lowered run replays the tape and compares that view (`tape_replays`).
* **The record.** A `Scenario` names its program, its observation and its claim as declarations.
  It lists the clauses of the claim and holds the controls. `#scenario_gate`, at the foot of a
  battery, refuses a name that does not resolve, a claim that is no theorem or has no placement, a
  clause without its green control or its red control, and a control that fails.

The laws of section 4 are the driver's contract, each with its placement (decisions row 207).
They hold for every run and every session. A scenario cites them as clauses, and adds the planned
goals of its own program.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## 1. How a script names a call -/

/-- A call as the host sees it: the row's spelling, the request, and the key that selects it. -/
structure Seen where
  row : String
  request : Val
  key : Key
deriving DecidableEq

/-- How a script names a call. A fiber parks on one call at a time, so a fiber names one call. -/
inductive Sel
  /-- The call this fiber is parked on. -/
  | fiber (id : FiberId)
  /-- The first call on the row with this spelling, in the machine's order. -/
  | row (spelling : String)
deriving DecidableEq

/-- Whether a selector names a call. -/
def Sel.names (sel : Sel) (call : Seen) : Bool :=
  match sel with
  | .fiber id => call.key.fiber == id
  | .row spelling => call.row == spelling

/-- The calls the machine is waiting on, as the host sees them, in the machine's order. -/
def live (s : Run) : List Seen :=
  s.outstanding.filterMap fun await =>
    (s.rowOf await.op).map fun row => ⟨row.spelling, await.request, ⟨await.fiber, await.token⟩⟩

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
  (s.rowOf entry.1.op).map fun row => ⟨row.spelling, entry.1.request, ⟨entry.1.fiber, entry.2⟩⟩

/-- The calls the host holds or held, in the order it got them. -/
def held (s : Run) : List Seen := (bound s).filterMap (seenOf s)

/-- The key a selector names: the live call it names. With no such live call it names the latest
call the host held, so a script can send a late reply for a call the machine dropped. -/
def Sel.key (sel : Sel) (s : Run) : Option Key :=
  match (live s).find? sel.names with
  | some call => some call.key
  | none => ((held s).reverse.find? sel.names).map (·.key)

/-! ## 2. The script alphabet and the driver -/

/-- One step of a script, by what the host does. -/
inductive Move
  /-- A control decision: evaluate, flush, a clock step, an interruption. -/
  | control (decision : Api.Decision)
  /-- The host gets the call and holds it: the session binds the call, with no reply. -/
  | hold (call : Sel)
  /-- The reply receipt: the session stores the host answer for the call. The machine does not
  run. -/
  | receive (call : Sel) (completion : Api.HostSession.Answer)
  /-- The reply application: the session applies the stored reply at the call's key. -/
  | apply (call : Sel)
  /-- One raw row, for a red control: a reply under another key, a row recorded earlier. -/
  | row (command : Command)
deriving DecidableEq

/-- The rows a move plays on a run. The claim of a live call comes from `Call.at`. A host answer
for a call the host holds or held is one `submit` row against that claim. A host answer for a live
call the host does not hold is the two rows of `Rows.receive`. -/
def Move.rows (s : Run) : Move → List Command
  | .control decision => [.control decision]
  | .hold call =>
    match (live s).find? call.names with
    | none => []
    | some seen =>
      match Call.at s seen.key with
      | none => []
      | some claim => [.bind claim seen.key.token]
  | .receive call completion =>
    match call.key s with
    | none => []
    | some key =>
      match (bound s).reverse.find? (fun entry => (⟨entry.1.fiber, entry.2⟩ : Key) == key) with
      | some entry => [.submit (Rows.reply s entry.1 key completion)]
      | none => Rows.receive s key completion
  | .apply call =>
    match call.key s with
    | none => []
    | some key => [.apply key]
  | .row command => [command]

/-- One move played: its rows go into the run's journal, each with its verdict. -/
def step (s : Run) (move : Move) : Run := s.play (move.rows s)

/-- A script played, move by move. -/
def play (s : Run) (moves : List Move) : Run := moves.foldl step s

/-- A host answer that succeeds with a value. -/
def ok (value : Val) : Api.HostSession.Answer := .ofExit (.success value)

/-- A host answer that fails with a tag and a message, the pair spelling of DB-15. -/
def failed (tag message : String) : Api.HostSession.Answer :=
  .ofExit (.failure (Cause.fail (.tagged tag message)))

/-- The root evaluated: the move that starts a run. -/
def Move.start : Move := .control Api.evaluate

/-- Every armed dispatcher drained. -/
def Move.flush : Move := .control Api.flush

/-- The logical clock advanced by `millis`. -/
def Move.tick (millis : Nat) : Move := .control (Api.TestClock.adjust (ClockMillis.ofNat millis))

/-- The host cancels a fiber: `interruptUnsafe` with no interruptor. -/
def Move.cancel (fiber : FiberId) : Move := .control (.interruptFrom none .empty fiber)

/-- A reply receipt, then its reply application: two moves, two verdicts. -/
def answer (call : Sel) (completion : Api.HostSession.Answer) : List Move :=
  [.receive call completion, .apply call]

/-- A script from its parts, in order. -/
def script (parts : List (List Move)) : List Move := parts.flatten

/-! ## 3. The session's part of an observation -/

/-- The call the host holds or held at a key. -/
def seenAt (s : Run) (key : Key) : Option Seen := (held s).find? (·.key == key)

/-- The accepted reply receipts, in order. -/
def receipts (s : Run) : List Seen :=
  (rows s).filterMap fun
    | (.submit reply, .preflight) => seenAt s reply.key
    | _ => none

/-- The reply applications the session applied, in order. -/
def applications (s : Run) : List Seen :=
  (rows s).filterMap fun
    | (.apply key, .applied) => seenAt s key
    | _ => none

/-- The kind of a row, as a word. -/
def kindOf : Command → String
  | .bind _ _ => "bind"
  | .submit _ => "submit"
  | .apply _ => "apply"
  | .control _ => "control"

/-- The refused rows, in order: the kind of each row and the session's reason. -/
def refusals (s : Run) : List (String × Api.HostSession.Refusal) :=
  (rows s).filterMap fun
    | (command, .refused why) => some (kindOf command, why)
    | _ => none

/-- Whether the session refused exactly these rows, in order. -/
def refused (s : Run) (expected : List (String × Api.HostSession.Refusal)) : Bool :=
  refusals s == expected

/-- The retired calls, in retirement order, each with whether a reply waited for it. -/
def retired (s : Run) : List (Seen × Bool) :=
  s.session.retired.filterMap fun call =>
    (seenOf s (call.bound.call, call.bound.token)).map fun seen => (seen, call.pending.isSome)

/-- The requests of the calls the host held on one row, in order. -/
def requestsOn (s : Run) (row : String) : List Val :=
  ((held s).filter (·.row == row)).map (·.request)

/-- The value a cell holds, by its allocation index: a program's log, read from the store. -/
def cell (s : Run) (index : Nat) : Option Val := s.machine.state.refs[index]?

/-! ## 4. The driver's contract -/

/-- Helper of `replays`: playing rows keeps the run's name. -/
theorem play_id (s : Run) (rows : List Command) : (s.play rows).id = s.id := by
  induction rows generalizing s with
  | nil => rfl
  | cons c rest ih => rw [Run.play_cons, ih, Run.step_id]

/-- Helper of `replays`: playing rows keeps the run's budget. -/
theorem play_budget (s : Run) (rows : List Command) : (s.play rows).budget = s.budget := by
  induction rows generalizing s with
  | nil => rfl
  | cons c rest ih => rw [Run.play_cons, ih, Run.step_budget]

/-- Helper of `replays`: playing rows keeps the run's profile. -/
theorem play_profile (s : Run) (rows : List Command) : (s.play rows).profile = s.profile := by
  induction rows generalizing s with
  | nil => rfl
  | cons c rest ih => rw [Run.play_cons, ih, Run.step_profile]

/-- Helper of `replays`: a script only plays rows, so it keeps what the run was opened with. -/
theorem play_opened (s : Run) (moves : List Move) :
    (play s moves).built = s.built ∧ (play s moves).id = s.id ∧
      (play s moves).budget = s.budget ∧ (play s moves).profile = s.profile := by
  induction moves generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons move rest ih =>
    obtain ⟨hb, hi, hf, hp⟩ := ih (step s move)
    exact ⟨hb.trans (Run.play_built s _), hi.trans (play_id s _), hf.trans (play_budget s _),
      hp.trans (play_profile s _)⟩

/-- Helper of `replays`: a script played from a recorded run reaches a recorded run. -/
theorem reached_play (s : Run) (moves : List Move) (h : Run.Reached s) :
    Run.Reached (play s moves) := by
  induction moves generalizing s with
  | nil => exact h
  | cons move rest ih => exact ih (step s move) (Run.Reached.play s _ h)

/-- **A script's run replays from its journal.** The run that a script reaches from an opened
program is reached again by playing the journal it recorded. The journal holds rows only, so the
replay resolves no selector and calls no fixture. Reach: any built program, name, budget and
script. It does not establish that two hosts choose the same rows, and it says nothing of a
lowered run. Consumer: every scenario of `Test/Dogfood/Scenario/`. It is `journal_replays`
(`src/Effect4/Laws/Run.lean`, R13's node) on the driver's scripts. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem replays (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move) :
    (Run.open b id budget profile).play (play (Run.open b id budget profile) moves).journal =
      play (Run.open b id budget profile) moves := by
  have recorded := Run.journal_replays _ (reached_play _ moves (Run.Reached.opened b id budget profile))
  obtain ⟨hb, hi, hf, hp⟩ := play_opened (Run.open b id budget profile) moves
  rw [hb, hi, hf, hp] at recorded
  exact recorded

/-! ### A reply receipt does not advance the machine -/

/-- What a row that is neither a reply application nor a control leaves alone in a session: the
machine, the count of applied replies, the consumed calls and the retired calls. -/
def SessionInert {program : Api.Program} {table : RowTable} (before after : Session program table) :
    Prop :=
  after.machine = before.machine ∧ after.applied = before.applied ∧
    after.consumed = before.consumed ∧ after.retired = before.retired

/-- The same four readings of two runs. A run's session is indexed by what was built, so the
runs are compared field by field. -/
def Inert (before after : Run) : Prop :=
  after.machine = before.machine ∧ after.session.applied = before.session.applied ∧
    after.session.consumed = before.session.consumed ∧
    after.session.retired = before.session.retired

/-- Helper of `receipt_inert`: binding a call is inert, accepted or refused. -/
theorem bindCall_inert {program : Api.Program} {table : RowTable} (s : Session program table)
    (call : Call) (token : Nat) :
    SessionInert s (Api.HostSession.bindCall s call token).session := by
  unfold Api.HostSession.bindCall
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- Helper of `receipt_inert`: a reply receipt is inert, accepted or refused. -/
theorem submit_inert {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : SessionInert s (Api.HostSession.submit s reply).session := by
  unfold Api.HostSession.submit
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- A row that holds a call or receives a reply. -/
def receiptRow : Command → Bool
  | .bind _ _ => true
  | .submit _ => true
  | _ => false

/-- Helper of `receipt_inert`: one such row is inert. -/
theorem step_receiptRow (s : Run) (c : Command) (h : receiptRow c = true) :
    Inert s (s.step c) := by
  cases c with
  | bind call token =>
    have inert := bindCall_inert s.session call token
    exact ⟨congrArg Session.machine (Run.step_session_bind s call token) |>.trans inert.1,
      congrArg Session.applied (Run.step_session_bind s call token) |>.trans inert.2.1,
      congrArg Session.consumed (Run.step_session_bind s call token) |>.trans inert.2.2.1,
      congrArg Session.retired (Run.step_session_bind s call token) |>.trans inert.2.2.2⟩
  | submit reply =>
    have inert := submit_inert s.session reply
    exact ⟨congrArg Session.machine (Run.step_session_submit s reply) |>.trans inert.1,
      congrArg Session.applied (Run.step_session_submit s reply) |>.trans inert.2.1,
      congrArg Session.consumed (Run.step_session_submit s reply) |>.trans inert.2.2.1,
      congrArg Session.retired (Run.step_session_submit s reply) |>.trans inert.2.2.2⟩
  | apply key => exact absurd h Bool.false_ne_true
  | control decision => exact absurd h Bool.false_ne_true

/-- Helper of `receipt_inert`: playing such rows is inert. -/
theorem play_receiptRows (s : Run) (rows : List Command) (h : rows.all receiptRow = true) :
    Inert s (s.play rows) := by
  induction rows generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons c rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hm, ha, hc, hr⟩ := ih (s.step c) h.2
    obtain ⟨fm, fa, fc, fr⟩ := step_receiptRow s c h.1
    rw [Run.play_cons]
    exact ⟨hm.trans fm, ha.trans fa, hc.trans fc, hr.trans fr⟩

/-- Helper of `receipt_inert`: the rows of `Rows.receive` hold a call and receive a reply. -/
theorem receive_receiptRows (s : Run) (key : Key) (completion : Api.HostSession.Answer) :
    (Rows.receive s key completion).all receiptRow = true := by
  unfold Rows.receive
  split <;> rfl

/-- The proposition of `receipt_inert`: holding a call and receiving a reply are inert. -/
def ReceiptInert : Prop :=
  ∀ (s : Run) (call : Sel) (completion : Api.HostSession.Answer),
    Inert s (step s (.hold call)) ∧ Inert s (step s (.receive call completion))

/-- **A reply receipt does not advance the machine.** When the host holds a call (`hold`) or the
session receives a reply (`receive`), four readings stay as they were: the machine, the count of
applied replies, the consumed calls and the retired calls. The session may accept the rows or
refuse them. Reach: any run and any selector, live or not. It does not establish that the session
accepts a reply receipt, and it says nothing of the reply application, a separate ordered step.
Consumer: the workers scenario's clause "receipt". It lifts `submit_machine`
(`src/Effect4/Laws/Api/HostSession.lean`) to the driver. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem receipt_inert : ReceiptInert := by
  intro s call completion
  refine ⟨play_receiptRows s _ ?_, play_receiptRows s _ ?_⟩
  · simp only [Move.rows]
    split
    · rfl
    · split <;> rfl
  · simp only [Move.rows]
    split
    · rfl
    · split
      · rfl
      · exact receive_receiptRows s _ completion

/-! ### A reply application consumes the selected call only -/

/-- The proposition of `applied_selects`: an applied reply consumes the call bound at the
selected key, and that call only. -/
def AppliedSelects : Prop :=
  ∀ {program : Api.Program} {table : RowTable} (s : Session program table) (key : Key) (fuel : Nat),
    (Api.HostSession.applyReply s key fuel).phase = .applied →
    ∃ selected, s.active.find? (fun b => b.key == key) = some selected ∧
      (Api.HostSession.applyReply s key fuel).session.consumed =
        s.consumed ++ [selected.call.callId] ∧
      (Api.HostSession.applyReply s key fuel).session.applied = s.applied + 1

/-- **A reply application consumes the selected call, and no other.** When the session applies
the reply stored at a key, that key has a live binding. The consumed calls gain that binding's
call and nothing else, and the count of applied replies grows by one. Reach: any session, key and
budget. It does not establish reply admission at the application, which is open R6 work
(`docs/core/host-boundary.md` §4.5), and it does not order two reply applications. Consumer: the
workers scenario's clause "selection". A refused reply application leaves the session as it was
(`applyReply_refused`, `src/Effect4/Laws/Api/Runner.lean`). A budget of zero leaves the reply
stored (`applyReply_zero`, `src/Effect4/Laws/Api/HostSession.lean`). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem applied_selects : AppliedSelects := by
  intro program table s key fuel h
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases hactive : s.active.find? (fun b => b.key == key) with
    | none =>
      simp only [Api.HostSession.applyReply, hactive] at h
      cases h
    | some selected =>
      cases hreply : Api.HostSession.readReply s.pending key with
      | none =>
        simp only [Api.HostSession.applyReply, hactive, hreply] at h
        cases h
      | some reply =>
        cases hpre : Api.HostSession.preflight s reply with
        | error why =>
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre] at h
          cases h
        | ok decision =>
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre] at h ⊢
          split at h
          · cases h
          · rename_i allowed
            split at h
            · rename_i removed
              refine ⟨selected, rfl, ?_, ?_⟩
              · rw [if_neg allowed, if_pos removed]
                rfl
              · rw [if_neg allowed, if_pos removed]
                rfl
            · cases h

/-! ### A control retires the calls whose guard it removed, and no other -/

/-- The proposition of `control_retires`: after an accepted control, a held call whose guard
survives stays active, and a held call whose guard is gone is retired with the reply that waited
for it. -/
def ControlRetires : Prop :=
  ∀ {program : Api.Program} {table : RowTable} (s : Session program table) (fuel : Nat)
    (decision : NativeDecision) (selected : BoundCall),
    selected ∈ s.active →
    (∀ why, (Api.HostSession.advance s fuel decision).phase ≠ .refused why) →
    ((Api.requestOf (Api.HostSession.advance s fuel decision).session.machine
          selected.call.fiber selected.token).isSome = true →
        selected ∈ (Api.HostSession.advance s fuel decision).session.active) ∧
      ((Api.requestOf (Api.HostSession.advance s fuel decision).session.machine
          selected.call.fiber selected.token).isNone = true →
        (⟨selected, Api.HostSession.readReply s.pending selected.key⟩ :
            Api.HostSession.RetiredCall) ∈
          (Api.HostSession.advance s fuel decision).session.retired)

/-- **A control retires exactly the held calls whose guard it removed.** After an accepted
control, a call the host holds whose guard the machine still has stays active. A held call whose
guard is gone is retired, with the reply that waited for it. Reach: any session, budget and
control decision that the session does not refuse. It does not establish which guards a decision
removes: one interruption may remove the guards of several fibers, and that is the machine's
step. The retirement edge of the host protocol stays open R6 work
(`docs/core/host-boundary.md` §4.2). Consumer: the workers scenario's clause "retirement", whose
finite runs show the machine's part. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem control_retires : ControlRetires := by
  intro program table s fuel decision selected held accepted
  rcases Run.advance_step s fuel decision with ⟨why, refused⟩ | ⟨_, stepped⟩
  · exact absurd (congrArg Api.HostSession.Result.phase refused) (accepted why)
  · rw [stepped]
    refine ⟨fun alive => List.mem_filter.mpr ⟨held, alive⟩, fun gone => ?_⟩
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨selected, List.mem_filter.mpr ⟨held, gone⟩, rfl⟩)

/-! ### The machine's part of a run, and its tape -/

/-- The machine's part of an observation: what a replay of the machine alone can show. The held
calls, the reply receipts, the retired calls and the stored replies are the session's, and no
part of them is here. -/
structure MachineView where
  /-- The root's exit, or `none` while it is live. -/
  rootExit : Option ExitV
  /-- The cells, in allocation order. -/
  cells : List Val
  /-- The calls the machine waits on. -/
  awaiting : List Await
  /-- The armed owners, in arming order. -/
  queued : List FiberId
  /-- The runnable fibers, in the machine's order. -/
  runnable : List FiberId
  /-- Each sleeping fiber with the clock reading it wakes at. -/
  timers : List (FiberId × ClockMillis)
deriving DecidableEq

/-- The machine's part of an observation, read from a machine. -/
def machineViewOf (m : Api.Machine) : MachineView :=
  { rootExit := (m.fiber? Api.root).bind RunFiber.exit
    cells := m.state.refs
    awaiting := awaits m
    queued := m.armed
    runnable := Api.runnableFibers m
    timers := m.state.timers.wake.waiters.map fun w => (w.fiber, w.payload) }

/-- The machine's part of a run's observation. -/
def machineView (s : Run) : MachineView := machineViewOf s.machine

/-- One position of a machine tape: the decision that moved the machine, and the run after the
row that gave it. -/
structure Position where
  decision : Api.Decision
  after : Run

/-- The decision a row gives the machine, read on the run before the row. `none` for a row that
leaves the machine as it was: a held call, a reply receipt, a refused row. A reply application
gives the answer decision of the stored reply. -/
def decisionOf (s : Run) (c : Command) (phase : Phase) : Option Api.Decision :=
  match c, phase with
  | .control decision, .progressed => some decision
  | .apply key, .applied =>
    (Api.HostSession.readReply s.session.pending key).map fun reply =>
      .answerAsync key.fiber key.token reply.completion
  | _, _ => none

/-- Whether the raw replay takes this decision and reads on: the machine is live, and the step
has enough command fuel (`Run.enoughFor`, `src/Effect4/Laws/Run.lean`). -/
def readsOn (s : Run) (decision : Api.Decision) : Bool :=
  s.machine.stuck.isNone &&
    Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision

/-- The machine tape of rows played from a run: the positions, and the rows left unread. The
tape stops at the first row that ends at a frontier, and at the first decision the raw replay
does not read past. A frontier is never turned into a reply application: its rows stay unread. -/
def tapeFrom (s : Run) : List Command → List Position × List Command
  | [] => ([], [])
  | c :: rest =>
    let phase := (Api.Runner.result s.runner c).phase
    if phase == .frontier then ([], c :: rest)
    else
      match decisionOf s c phase with
      | none =>
        let tail := tapeFrom (s.step c) rest
        (tail.1, tail.2)
      | some decision =>
        if readsOn s decision then
          let tail := tapeFrom (s.step c) rest
          (⟨decision, s.step c⟩ :: tail.1, tail.2)
        else ([], c :: rest)

/-- The proposition of `tape_replays`. -/
def TapeReplays : Prop :=
  ∀ (s : Run) (rows : List Command), (tapeFrom s rows).2 = [] →
    (s.play rows).machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        ((tapeFrom s rows).1.map (·.decision)) s.machine)

/-- **A journal's machine is the raw replay of its tape.** When the tape reads every row, the
machine that the journal leaves is the machine that the raw frame replay leaves on the tape's
decisions, at the same table and budgets. It is the machine clause of a lowered run: a replay of
the machine alone needs the tape, not the session. Reach: any run, any rows whose tape reads to
the end: no row at a frontier, and every decision taken at a live machine with enough fuel. It
does not establish equal session ledgers: the raw replay has none. It does not reach a journal
that stops at a frontier, and it says nothing of a lowered engine: that link is the finite
comparison of `ocaml/engine/test/test_scenarios.ml`. It extends `play_controls_eq_replay`
(`src/Effect4/Laws/Run.lean`) from control rows to reply applications. Concept
`translation-simulation`, R8. Consumer: the lowered runs of `Test/Dogfood/Scenario/Lowered.lean`,
whose finite runs check it at every position of every fixture. -/
@[semantics "translation-simulation" (requirement := R8)]
proof_goal tape_replays : TapeReplays

/-! ## 5. A scenario's record, and the gate at the foot of a battery -/

/-- One clause of a scenario's property, with the declaration that states it. -/
structure Clause where
  /-- The clause's name, one word. -/
  name : String
  /-- The theorem or the planned goal that states the clause. It carries its own placement. -/
  claim : Lean.Name

/-- One control of a clause. A green control is a run that the clause allows. A red control is a
fault made on purpose, which the session must refuse or the observation must tell apart. -/
structure Control where
  /-- The clause this run controls, by the clause's name. -/
  clause : String
  /-- `false` for a green control, `true` for a red control. -/
  isRed : Bool
  /-- What the run shows. -/
  name : String
  /-- Whether the run shows it: a comparison on the scenario's observation, decided by running. -/
  holds : Bool

/-- A green control of a clause. -/
def green (clause name : String) (holds : Bool) : Control := ⟨clause, false, name, holds⟩

/-- A red control of a clause. -/
def red (clause name : String) (holds : Bool) : Control := ⟨clause, true, name, holds⟩

/-- A scenario's record. The program, the observation and the claims are named as declarations,
so a name that no longer resolves fails where the record is written. -/
structure Scenario where
  /-- The scenario's name, as its row of `Test/Dogfood/README.md` quotes it. -/
  name : String
  /-- The program the scenario runs. -/
  program : Lean.Name
  /-- The one named observation every control compares. -/
  observation : Lean.Name
  /-- The claim: the theorem that assembles the clauses. Its standing is derived from its proof:
  proved, or proved modulo the clauses that are planned goals. -/
  claim : Lean.Name
  /-- The clauses of the claim. -/
  clauses : List Clause
  /-- The controls: for each clause a green control and at least one red control. -/
  controls : List Control

/-- What is wrong with a record as data, each finding in a sentence: a clause with no green
control or no red control, a control that names no clause, a control that fails. Empty for a
sound record. -/
def Scenario.problems (s : Scenario) : List String :=
  (s.clauses.flatMap fun clause =>
    [false, true].filterMap fun isRed =>
      if s.controls.any (fun control => control.clause == clause.name && control.isRed == isRed)
      then none
      else some (s.name ++ ": the clause \"" ++ clause.name ++ "\" has no " ++
        (if isRed then "red control" else "green control"))) ++
  s.controls.filterMap fun control =>
    if !s.clauses.any (·.name == control.clause) then
      some (s.name ++ ": the control \"" ++ control.name ++ "\" names no clause")
    else if !control.holds then some (s.name ++ ": the control \"" ++ control.name ++ "\" fails")
    else none

/-- The declarations a record names besides its claims. -/
def Scenario.declarations (s : Scenario) : List Lean.Name := [s.program, s.observation]

/-- The claims a record names: the scenario's claim, then each clause's. -/
def Scenario.claims (s : Scenario) : List Lean.Name := s.claim :: s.clauses.map (·.claim)

/-- `#scenario_gate S₁ … Sₙ`, at the foot of a battery, checks each scenario's record against the
environment and runs its controls once. It fails, naming every finding, when:

* the program or the observation does not resolve to a declaration;
* the claim, or a clause's claim, does not resolve to a theorem or a planned goal;
* such a claim has no placement: a declaration of a battery carries its own at a requirement
  (`@[semantics "concept" (requirement := Rn)]`, decisions row 207), and a theorem of the law
  graph (a module under `Effect4.Laws`) has the placement the semantics registry gives it;
* a clause has no green control, or no red control (`Scenario.problems`);
* a control names no clause of its scenario, or fails (`Scenario.problems`).

The command expands to one `run_cmd`, which leaves no declaration. The check reads the
environment, and no reader of the environment stays under the axiom ceiling
(`Test/Audit/AxiomGate.lean`). -/
syntax (name := scenarioGate) "#scenario_gate " ident+ : command

open Lean in
@[macro scenarioGate] def expandScenarioGate : Macro := fun stx => do
  let scenarios : Array (TSyntax `term) := stx[1].getArgs.map (⟨·⟩)
  `(run_cmd Lean.Elab.Command.liftTermElabM do
      let env ← Lean.getEnv
      let mut findings : Array String := #[]
      for scenario in ([$scenarios,*] : List Test.Dogfood.Scenario.Scenario) do
        for name in scenario.declarations do
          unless env.contains name do
            findings := findings.push s!"{scenario.name}: {name} does not resolve to a declaration"
        for name in scenario.claims do
          if (env.find? name) matches some (.thmInfo _) then
            let lawGraph := (env.getModuleIdxFor? name).any fun index =>
              (`Effect4.Laws).isPrefixOf env.header.moduleNames[index.toNat]!
            unless lawGraph || ((Effect4.Laws.Auto.semanticsAttribute.getParam? env name).bind
                (·.requirement)).isSome do
              findings := findings.push
                s!"{scenario.name}: the claim {name} has no placement at a requirement"
          else
            findings := findings.push
              s!"{scenario.name}: the claim {name} is no theorem and no planned goal"
        findings := findings ++ scenario.problems.toArray
      unless findings.isEmpty do
        throwError (String.intercalate "\n" findings.toList))

/-! ## 6. Controls of the gate

The fixtures name this module's own declarations, so they add no placed declaration. -/

namespace Fixture

/-- Green control: a claim and a clause that are placed theorems, and a clause that is a theorem
of the law graph, each with both controls. -/
def sound : Scenario :=
  { name := "sound", program := ``play, observation := ``receipts, claim := ``replays
    clauses := [⟨"inert", ``receipt_inert⟩, ⟨"law", ``Effect4.Run.journal_replays⟩]
    controls := [green "inert" "a run the clause allows" true, red "inert" "a fault" true,
      green "law" "a run the law allows" true, red "law" "a fault" true] }

/-- Red control: a program that names no declaration. -/
def unresolved : Scenario := { sound with name := "unresolved", program := `Nowhere.program }

/-- Red control: a claim that is a definition. -/
def noTheorem : Scenario := { sound with name := "noTheorem", claim := ``play }

/-- Red control: a clause whose claim is a battery's theorem with no placement. -/
def unplaced : Scenario :=
  { sound with
    name := "unplaced"
    clauses := [⟨"inert", ``play_id⟩]
    controls := [green "inert" "a run the clause allows" true, red "inert" "a fault" true] }

/-- Red control: a clause with no red control, a control of no clause, and a control that
fails. -/
def loose : Scenario :=
  { sound with
    name := "loose"
    clauses := [⟨"inert", ``receipt_inert⟩]
    controls := [green "inert" "a run the clause allows" true, red "other" "a stray run" true,
      green "inert" "a false run" false] }

end Fixture

-- One run of the gate over the five fixtures. The green control is that no finding names
-- `sound`; each red control is one finding or more, by its fixture's name.
/--
error: unresolved: Nowhere.program does not resolve to a declaration
noTheorem: the claim Test.Dogfood.Scenario.play is no theorem and no planned goal
unplaced: the claim Test.Dogfood.Scenario.play_id has no placement at a requirement
loose: the clause "inert" has no red control
loose: the control "a stray run" names no clause
loose: the control "a false run" fails
-/
#guard_msgs (error) in
#scenario_gate Fixture.sound Fixture.unresolved Fixture.noTheorem Fixture.unplaced Fixture.loose

#guard Fixture.sound.problems = []

end Test.Dogfood.Scenario
