import Effect4.Laws.Run
import Effect4.Api.Author
import Effect4.Laws.Auto.Semantics
import ProofGraph.Plan
import Tools.SemanticsRegistry

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
  A journal whose tape stops has a completed prefix, and that prefix and each position of the
  tape replay raw too (`tapeFrom_cut_replays`, `tapeFrom_position_replays`).
* **The record.** A `Scenario` names its program, its observation and its claim as declarations.
  It lists the assembled clauses, which the claim's proof uses, and the associated laws, which
  have controls only. `#scenario_gate`, at the foot of a battery, refuses a name that does not
  resolve, a claim that is no theorem or has no placement, a clause that the claim's proof does
  not reach, an entry without its green control or its red control, and a control that fails.
* **The named runs.** A scenario's record lists each of its scripts once, as a `NamedRun`: a
  name, the built program opened for a run, and the script. A control holds no script. It names
  the runs that its comparison reads, and the gate plays each named run once. The gate refuses a
  named run that no control reads. The host lane (`harness/truth/session/Keyed.lean`) and the
  engine's lane (`Test/Dogfood/Scenario/Tape.lean`) take their scripts from the same list, so
  no script is written twice.

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

/-- The answer decision of a stored reply, at the reply's own key. It is the decision that the
session hands the machine when it applies the reply: the session's preflight finds the call by
the reply's key, never by the key of the slot (`preflight_replyDecision`). `storeReply` writes
a reply only into the slot of its own key. -/
def replyDecision (reply : Reply) : Api.Decision :=
  .answerAsync reply.key.fiber reply.key.token reply.completion

/-- The decision a row gives the machine, read on the run before the row. `none` for a row that
leaves the machine as it was: a held call, a reply receipt, a refused row. A reply application
gives the answer decision of the stored reply (`replyDecision`). -/
def decisionOf (s : Run) (c : Command) (phase : Phase) : Option Api.Decision :=
  match c, phase with
  | .control decision, .progressed => some decision
  | .apply key, .applied => (Api.HostSession.readReply s.session.pending key).map replyDecision
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

/-! ### The proof of `tape_replays`

Each lemma below is a step of `tape_replays`, and that theorem is its one consumer. The first
three are facts of any session. The others read one row of a journal. -/

/-- Step of `tape_replays`: a successful preflight returns the reply's own answer decision. -/
theorem preflight_replyDecision {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : Api.HostSession.preflight s reply = .ok decision) : decision = replyDecision reply := by
  obtain ⟨bound, found, _, _, shape⟩ := Api.HostSession.preflight_envelope s reply decision h
  have test := List.find?_some found
  have same : bound.key = reply.key := of_decide_eq_true test
  rw [shape]
  show RunDecision.answerAsync bound.key.fiber bound.key.token reply.completion = _
  rw [same]
  rfl

/-- Step of `tape_replays`: an applied reply was stored at the key, and the machine it leaves is
the raw stepper's on that reply's answer decision. Retiring calls does not touch the machine. -/
theorem applyReply_applied_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (Api.HostSession.applyReply s key fuel).phase = .applied) :
    ∃ reply, Api.HostSession.readReply s.pending key = some reply ∧
      (Api.HostSession.applyReply s key fuel).session.machine =
        steppedBy program fuel table s.machine (replyDecision reply) := by
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
          have shape := preflight_replyDecision s reply decision hpre
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre] at h ⊢
          split at h
          · cases h
          · rename_i allowed
            split at h
            · rename_i removed
              refine ⟨reply, rfl, ?_⟩
              rw [if_neg allowed, if_pos removed, ← shape]
              rfl
            · cases h

/-- Step of `tape_replays`: a reply application ends at a frontier, applied or refused. -/
theorem applyReply_ends {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).phase = .frontier ∨
      (Api.HostSession.applyReply s key fuel).phase = .applied ∨
      ∃ why, (Api.HostSession.applyReply s key fuel).phase = .refused why := by
  cases fuel with
  | zero => exact Or.inl rfl
  | succ fuel =>
    cases hactive : s.active.find? (fun b => b.key == key) with
    | none =>
      exact Or.inr (Or.inr ⟨.noCall, by simp only [Api.HostSession.applyReply, hactive]⟩)
    | some selected =>
      cases hreply : Api.HostSession.readReply s.pending key with
      | none =>
        exact Or.inr (Or.inr ⟨.noCall, by
          simp only [Api.HostSession.applyReply, hactive, hreply]⟩)
      | some reply =>
        cases hpre : Api.HostSession.preflight s reply with
        | error why =>
          exact Or.inr (Or.inr ⟨why, by
            simp only [Api.HostSession.applyReply, hactive, hreply, hpre]⟩)
        | ok decision =>
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre]
          split
          · exact Or.inr (Or.inr ⟨.protocol, rfl⟩)
          · split
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl

/-- Step of `tape_replays`: a row that ends at no frontier and gives no decision leaves the
machine as it was. -/
theorem step_keeps_machine (s : Run) (c : Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = none) :
    (s.step c).machine = s.machine := by
  cases c with
  | bind call token =>
    exact (congrArg Session.machine (Run.step_session_bind s call token)).trans
      (bindCall_inert s.session call token).1
  | submit reply =>
    exact (congrArg Session.machine (Run.step_session_submit s reply)).trans
      (submit_inert s.session reply).1
  | apply key =>
    change ((Api.HostSession.applyReply s.session key s.budget.fuel).phase == Phase.frontier) =
      false at hfront
    change decisionOf s (.apply key)
      (Api.HostSession.applyReply s.session key s.budget.fuel).phase = none at hdec
    rcases applyReply_ends s.session key s.budget.fuel with hph | hph | ⟨why, hph⟩
    · rw [hph] at hfront
      cases hfront
    · obtain ⟨reply, hread, _⟩ := applyReply_applied_machine s.session key s.budget.fuel hph
      rw [hph] at hdec
      simp only [decisionOf, hread, Option.map_some] at hdec
      cases hdec
    · exact (congrArg Session.machine (Run.step_session_apply s key)).trans
        (congrArg Session.machine
          (Api.Runner.applyReply_refused s.session key s.budget.fuel why hph))
  | control decision =>
    change ((Api.HostSession.advance s.session s.budget.fuel decision).phase == Phase.frontier) =
      false at hfront
    change decisionOf s (.control decision)
      (Api.HostSession.advance s.session s.budget.fuel decision).phase = none at hdec
    rcases Run.advance_step s.session s.budget.fuel decision with ⟨why, refused⟩ | ⟨_, stepped⟩
    · exact (congrArg Session.machine (Run.step_session_control s decision)).trans
        (congrArg (fun r => r.session.machine) refused)
    · rw [stepped] at hfront hdec
      cases henough : Run.enoughFor s.built.program s.built.table s.budget.fuel s.session.machine
          decision with
      | true =>
        rw [henough] at hdec
        cases hdec
      | false =>
        rw [henough] at hfront
        cases hfront

/-- Step of `tape_replays`: a row that gives a decision leaves the machine that the raw stepper
leaves on that decision. -/
theorem step_takes_decision (s : Run) (c : Command) (decision : Api.Decision)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision) :
    (s.step c).machine =
      steppedBy s.built.program s.budget.fuel s.built.table s.machine decision := by
  cases c with
  | bind call token =>
    generalize (Api.Runner.result s.runner (.bind call token)).phase = phase at hdec
    cases phase <;> cases hdec
  | submit reply =>
    generalize (Api.Runner.result s.runner (.submit reply)).phase = phase at hdec
    cases phase <;> cases hdec
  | apply key =>
    change decisionOf s (.apply key)
      (Api.HostSession.applyReply s.session key s.budget.fuel).phase = some decision at hdec
    generalize hph : (Api.HostSession.applyReply s.session key s.budget.fuel).phase = phase at hdec
    cases phase with
    | applied =>
      obtain ⟨reply, hread, hmachine⟩ :=
        applyReply_applied_machine s.session key s.budget.fuel hph
      simp only [decisionOf, hread, Option.map_some, Option.some.injEq] at hdec
      rw [← hdec]
      exact (congrArg Session.machine (Run.step_session_apply s key)).trans hmachine
    | bound => cases hdec
    | preflight => cases hdec
    | progressed => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec
  | control d =>
    change decisionOf s (.control d)
      (Api.HostSession.advance s.session s.budget.fuel d).phase = some decision at hdec
    generalize hph : (Api.HostSession.advance s.session s.budget.fuel d).phase = phase at hdec
    cases phase with
    | progressed =>
      obtain ⟨_, _, hmachine⟩ := Run.advance_progressed s.session s.budget.fuel d hph
      simp only [decisionOf, Option.some.injEq] at hdec
      rw [← hdec]
      exact (congrArg Session.machine (Run.step_session_control s d)).trans hmachine
    | bound => cases hdec
    | preflight => cases hdec
    | applied => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec

/-- Step of `tape_replays`: the tape stops at a row that ends at a frontier. -/
theorem tapeFrom_frontier (s : Run) (c : Command) (rest : List Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = true) :
    tapeFrom s (c :: rest) = ([], c :: rest) := by
  rw [tapeFrom]
  exact if_pos hfront

/-- Step of `tape_replays`: the tape passes a row that gives no decision. -/
theorem tapeFrom_skip (s : Run) (c : Command) (rest : List Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = none) :
    tapeFrom s (c :: rest) = tapeFrom (s.step c) rest := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec]

/-- Step of `tape_replays`: the tape takes a decision that the raw replay reads past. -/
theorem tapeFrom_take (s : Run) (c : Command) (rest : List Command) (decision : Api.Decision)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision)
    (hreads : readsOn s decision = true) :
    tapeFrom s (c :: rest) =
      (⟨decision, s.step c⟩ :: (tapeFrom (s.step c) rest).1, (tapeFrom (s.step c) rest).2) := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec, hreads, if_true]

/-- Step of `tape_replays`: the tape stops at a decision that the raw replay does not read
past. -/
theorem tapeFrom_stop (s : Run) (c : Command) (rest : List Command) (decision : Api.Decision)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision)
    (hreads : readsOn s decision = false) :
    tapeFrom s (c :: rest) = ([], c :: rest) := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec, hreads]

/-- **A journal's machine is the raw replay of its tape.** When the tape reads every row, the
machine that the journal leaves is the machine that the raw frame replay leaves on the tape's
decisions, at the same table and budgets. It is the machine clause of a lowered run: a replay of
the machine alone needs the tape, not the session. Reach: any run, any rows whose tape reads to
the end: no row at a frontier, and every decision taken at a live machine with enough fuel. It
needs no premise on the session, because the tape holds the decision that the session hands the
machine: a reply's own answer decision (`replyDecision`). It does not establish equal session
ledgers: the raw replay has none. It does not reach a journal that stops at a frontier, and it
says nothing of a lowered engine: that link is the finite comparison of
`ocaml/engine/test/scenarios/test_scenarios.ml`. It extends `play_controls_eq_replay`
(`src/Effect4/Laws/Run.lean`) from control rows to reply applications. Concept
`translation-simulation`, R8. Consumer: the lowered runs of `Test/Dogfood/Scenario/Lowered.lean`,
whose finite runs check it at every position of every fixture. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem tape_replays : TapeReplays := by
  intro s rows h
  induction rows generalizing s with
  | nil => exact (Run.machineOf_nil _ _ _ _).symm
  | cons c rest ih =>
    rw [Run.play_cons]
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at h
      cases h
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at h ⊢
        rw [ih (s.step c) h, Run.step_built, Run.step_budget, step_keeps_machine s c hfront hdec]
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at h
          cases h
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at h ⊢
          have live : s.machine.stuck.isNone = true ∧
              Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision =
                true :=
            Bool.and_eq_true_iff.mp hreads
          rw [ih (s.step c) h, Run.step_built, Run.step_budget,
            step_takes_decision s c decision hdec, List.map_cons,
            Run.replayFrom_cons _ _ _ _ _ _ (Option.isNone_iff_eq_none.mp live.1) live.2]

/-! ### The journal's cut, and its positions

`tape_replays` reads a journal whose tape reads every row. The four laws below say what a
prefix of any journal gives. `tapeFrom` splits a journal into a completed prefix and the rows
that it leaves unread. That split is the journal's cut, and it is no cut of the semantics
registry.

* **A stopped row** is the first unread row. It ends at a frontier (`tapeFrom_frontier`), or
  it gives a decision that the raw replay does not read past (`tapeFrom_stop`). A control that
  progressed always reads on (`Run.advance_progressed`), so a row of the second kind is a reply
  application that the session applied. The record `cuts` holds one: the command budget did not
  cover its step.
* **The completed prefix** ends before the stopped row. It may end with rows that give no
  decision, after its last position.

Each law holds for every run and every list of rows: no premise asks for a recorded run, a
typed program or a tape that reads to its end. The stop conditions are `tapeFrom`'s own. A
stopped row may change the machine before it reports its frontier. No law here says what that
machine is, and a second run command on it is no continuation of the first (decisions row
226). Concept `translation-simulation`. The laws stand at R13, beside `journal_replays`
(`src/Effect4/Laws/Run.lean`): the rows of a journal's prefix give the raw replay's machine.
They serve R8's replay view, the views of a lowered run (`shown_views_opened`,
`Test/Dogfood/Scenario/Tape.lean`). Their controls are the record `cuts` of that module. -/

/-- **The tape of a journal in two parts.** When the tape of the first part reads every row,
the tape of `a ++ b` is the positions of `a`, then the tape of `b` from the run after `a`. When
the tape of `a` stops, the tape of `a ++ b` holds the same positions, and the rows of `b` join
the unread rows: no row of `b` is read. Reach: any run and any two lists of rows. It does not
establish what the machine is after a stopped row, and it reads no row after one. Concept
`translation-simulation`, R13: a journal's tape splits where `Run.play_append` splits its run.
Consumer: no theorem of this module uses it. It is the law of a driver that plays a script in
parts, and the record `cuts` (`Test/Dogfood/Scenario/Tape.lean`) holds its controls. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_append (s : Run) (a b : List Command) :
    tapeFrom s (a ++ b) =
      if (tapeFrom s a).2 = [] then
        ((tapeFrom s a).1 ++ (tapeFrom (s.play a) b).1,
          (tapeFrom (s.play a) b).2)
      else ((tapeFrom s a).1, (tapeFrom s a).2 ++ b) := by
  induction a generalizing s with
  | nil => rfl
  | cons c rest ih =>
    rw [List.cons_append, Run.play_cons]
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c (rest ++ b) hfront, tapeFrom_frontier s c rest hfront]
      exact (if_neg (List.cons_ne_nil c rest)).symm
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c (rest ++ b) hfront hdec, tapeFrom_skip s c rest hfront hdec]
        exact ih (s.step c)
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c (rest ++ b) decision hfront hdec hreads,
            tapeFrom_stop s c rest decision hfront hdec hreads]
          exact (if_neg (List.cons_ne_nil c rest)).symm
        | true =>
          rw [tapeFrom_take s c (rest ++ b) decision hfront hdec hreads,
            tapeFrom_take s c rest decision hfront hdec hreads, ih (s.step c)]
          split
          · rfl
          · rfl

/-- **The journal's cut.** A journal is a completed prefix, then the rows that its tape leaves
unread. The tape of the prefix alone holds the same positions, and it leaves no row unread. So
the positions of a journal are read from the completed prefix, and a stopped row is the first
row after it. Reach: any run and any rows. A journal whose tape reads every row is its own
completed prefix. It does not establish the machine after the prefix: `tapeFrom_cut_replays`
adds that clause. Concept `translation-simulation`, R13. Consumer: `tapeFrom_cut_replays`. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_cut (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, []) := by
  induction rows generalizing s with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c rest ih =>
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront]
      exact ⟨[], rfl, rfl⟩
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        obtain ⟨done, hrows, htape⟩ := ih (s.step c)
        rw [tapeFrom_skip s c rest hfront hdec]
        refine ⟨c :: done, congrArg (List.cons c) hrows, ?_⟩
        rw [tapeFrom_skip s c done hfront hdec]
        exact htape
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads]
          exact ⟨[], rfl, rfl⟩
        | true =>
          obtain ⟨done, hrows, htape⟩ := ih (s.step c)
          rw [tapeFrom_take s c rest decision hfront hdec hreads]
          refine ⟨c :: done, congrArg (List.cons c) hrows, ?_⟩
          rw [tapeFrom_take s c done decision hfront hdec hreads, htape]

/-- **The machine after the completed prefix is the raw replay of its tape.** A journal is a
completed prefix, then its unread rows (`tapeFrom_cut`). The machine that the prefix leaves is
the machine that the raw frame replay leaves on the decisions of the journal's positions, from
the run's own machine, at the same table and budgets. Reach: any run and any rows: the tape may
stop. It does not establish the machine after a stopped row. That row may change the machine
before it reports its frontier, and the completed prefix ends before it. It does not establish
equal session ledgers, since the raw replay has none. It says nothing of resumable ownership
(R12, decisions row 226) or of a generated engine. Concept `translation-simulation`, R13: it is
`tape_replays` on the completed prefix. Consumer: the controls of the record `cuts`
(`Test/Dogfood/Scenario/Tape.lean`), and later the laws of the scenario driver. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_cut_replays (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, []) ∧
      (s.play done).machine =
        Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
          ((tapeFrom s rows).1.map (·.decision)) s.machine) := by
  obtain ⟨done, hrows, htape⟩ := tapeFrom_cut s rows
  have replayed := tape_replays s done (congrArg Prod.snd htape)
  rw [htape] at replayed
  exact ⟨done, hrows, htape, replayed⟩

/-- Step of `tapeFrom_position_replays`: a prefix of the journal ends at the row of position
`i`. Playing that prefix reaches the position's own run, with every row of the prefix in its
journal: the rows that gave no decision are played too. The tape of the prefix alone is the
first `i + 1` positions, with no row unread. So `tape_replays` reads the machine off that
prefix, and the position law needs no second induction over replies. -/
theorem tapeFrom_position_prefix (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (found : (tapeFrom s rows).1[i]? = some position) :
    ∃ done tail, rows = done ++ tail ∧
      s.play done = position.after ∧
      tapeFrom s done = ((tapeFrom s rows).1.take (i + 1), []) := by
  induction rows generalizing s i with
  | nil => cases found
  | cons c rest ih =>
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at found
      cases found
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at found ⊢
        obtain ⟨done, tail, hrows, hafter, htape⟩ := ih (s.step c) i found
        refine ⟨c :: done, tail, congrArg (List.cons c) hrows, ?_, ?_⟩
        · rw [Run.play_cons]
          exact hafter
        · rw [tapeFrom_skip s c done hfront hdec]
          exact htape
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at found
          cases found
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at found ⊢
          cases i with
          | zero =>
            cases found
            refine ⟨[c], rest, rfl, rfl, ?_⟩
            rw [tapeFrom_take s c [] decision hfront hdec hreads]
            rfl
          | succ j =>
            obtain ⟨done, tail, hrows, hafter, htape⟩ := ih (s.step c) j found
            refine ⟨c :: done, tail, congrArg (List.cons c) hrows, ?_, ?_⟩
            · rw [Run.play_cons]
              exact hafter
            · rw [tapeFrom_take s c done decision hfront hdec hreads, htape]
              rfl

/-- **The machine after a position is the raw replay of the decisions up to it.** At position
`i` of a journal's tape, the machine of the run after the position's row is the machine that the
raw frame replay leaves on the first `i + 1` decisions. The replay starts at the machine of the
run that the tape was read from, at the same table and budgets. Reach: any run, any rows and any
position of the tape. The tape need not read every row: a later stopped row adds no position.
It does not establish the machine after a stopped row, equal session ledgers, or anything of a
generated engine. It replays from the run's own machine: a replay from a new load needs a fresh
open, which the consumer states. Concept `translation-simulation`, R13: it is `tape_replays` on
the prefix that ends at the position's row. Consumer: `shown_views_opened`
(`Test/Dogfood/Scenario/Tape.lean`), the views of a lowered run. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_position_replays (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (found : (tapeFrom s rows).1[i]? = some position) :
    position.after.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        (((tapeFrom s rows).1.take (i + 1)).map (·.decision)) s.machine) := by
  obtain ⟨done, tail, _, hafter, htape⟩ := tapeFrom_position_prefix s rows i position found
  have replayed := tape_replays s done (congrArg Prod.snd htape)
  rw [htape, hafter] at replayed
  exact replayed

/-! The axioms of the four laws and of the helper, then the standing of the four laws, as the
plan derives it from their proofs. `tape_replays` is named last, so that the plan shows which
laws rest on it. Each was a planned goal first, and each is proved in place with its statement
unchanged. -/

/-- info: 'Test.Dogfood.Scenario.tapeFrom_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tapeFrom_append

/-- info: 'Test.Dogfood.Scenario.tapeFrom_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tapeFrom_cut

/-- info: 'Test.Dogfood.Scenario.tapeFrom_cut_replays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tapeFrom_cut_replays

/-- info: 'Test.Dogfood.Scenario.tapeFrom_position_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tapeFrom_position_prefix

/-- info: 'Test.Dogfood.Scenario.tapeFrom_position_replays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tapeFrom_position_replays

/--
info: Test.Dogfood.Scenario.tapeFrom_append: proved; nearest []; 4 lemmas, 4 definitions
Test.Dogfood.Scenario.tapeFrom_cut: proved; nearest []; 4 lemmas, 4 definitions
Test.Dogfood.Scenario.tapeFrom_cut_replays: proved; nearest [Test.Dogfood.Scenario.tape_replays, Test.Dogfood.Scenario.tapeFrom_cut]; 0 lemmas, 5 definitions
Test.Dogfood.Scenario.tapeFrom_position_replays: proved; nearest [Test.Dogfood.Scenario.tape_replays]; 5 lemmas, 6 definitions
Test.Dogfood.Scenario.tape_replays: proved; nearest []; 11 lemmas, 6 definitions
next goals: 0
-/
#guard_msgs in
#plan_status tapeFrom_append tapeFrom_cut tapeFrom_cut_replays tapeFrom_position_replays
  tape_replays

/-! ### A funded run, and a machine at rest

A statement over a scenario's runs takes its budget as a premise. This section gives that
premise one name, `funded`, and ties it to a proved law of the driver. -/

/-- The run that a run started from: its own program, name, budgets and profile, opened fresh.
Playing a recorded run's journal from it reaches the run again (`Run.journal_replays`,
`src/Effect4/Laws/Run.lean`). -/
def openedOf (s : Run) : Run := Run.open s.built s.id s.budget s.profile

/-- The decisions of a run's tape: the decisions that moved the machine, read off the run's own
journal from its fresh open. -/
def tapeOf (s : Run) : List Api.Decision := (tapeFrom (openedOf s) s.journal).1.map (·.decision)

/-- **A funded run: no task of the run was cut by its budget.** The tape of the run's own
journal, read from the run's fresh open, leaves no row unread. So the journal holds no stopped
row: no row ends at a frontier, and each decision is taken at a live machine with enough command
fuel (`tapeFrom`, `readsOn`).

The journal's verdicts alone do not decide it. A reply application has the verdict `applied` as
soon as its call's guard is gone, whatever fuel its step had left (`applyReply`,
`src/Effect4/Api/HostSession.lean`). Only a control reports its sufficiency, as `progressed` or
`frontier` (`advance`, in the same file). The tape asks `Run.enoughFor` of each decision, so it
stops at an applied reply application that the budget cut (`tapeFrom_stop`).

It is the budget premise of a law of a whole run. Decisions row 226 excludes a cut inside an
owned operation from the first profile. The proposed claim `embedded-budget-sufficient` (an open
part of R12) is to supply the premise from a program's own bound. Until then a statement over
runs takes it by this one name. `funded_replays` says what the premise gives. -/
def funded (s : Run) : Bool := (tapeFrom (openedOf s) s.journal).2.isEmpty

/-- **The machine of a funded run is the raw replay of its tape's decisions.** For a recorded
run whose journal holds no stopped row, the machine is the machine that the raw frame replay
leaves on the decisions of the run's tape, from the program's own load, at the run's table and
budgets. Reach: any run that was opened and then played (`Run.Reached`), under `funded`. It is
one application of `tape_replays` at the run's fresh open, with `Run.journal_replays`. It does
not establish that a run is funded: that is the open claim `embedded-budget-sufficient`. It does
not establish equal session ledgers, and it says nothing of a run with a stopped row. Concept
`translation-simulation`, R8. Consumer: each statement over runs that takes `funded` as its
budget premise, the planned goals of `Test/Dogfood/Scenario/QueueWorkers.lean` first. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem funded_replays (s : Run) (recorded : Run.Reached s) (h : funded s = true) :
    s.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel)) := by
  have read : (tapeFrom (openedOf s) s.journal).2 = [] := List.isEmpty_iff.mp h
  have replayed := tape_replays (openedOf s) s.journal read
  rw [show (openedOf s).play s.journal = s from Run.journal_replays s recorded,
    show (openedOf s).machine = Api.load s.built.program s.budget.compileFuel from
      Run.open_machine s.built s.id s.budget s.profile] at replayed
  exact replayed

/-- info: 'Test.Dogfood.Scenario.funded_replays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms funded_replays

/-- **A machine at rest**: it names no runnable fiber and no armed owner. A host lets every
dispatcher run after each of its acts but the root's start, so a host reads a machine at rest
(`performable`, `harness/truth/session/Keyed.lean`). A fiber that a budget cut stays runnable
with no task, so a run with a stopped row is seldom at rest. -/
def atRest (s : Run) : Bool := s.work.runnable.isEmpty && s.work.queued.isEmpty

/-! ## 5. A scenario's record, and the gate at the foot of a battery -/

/-- One entry of a scenario's record: a clause of its claim, or a law beside it, with the
declaration that states it. -/
structure Clause where
  /-- The entry's name, as its controls quote it. -/
  name : String
  /-- The theorem or the planned goal that states the entry. It has a placement. -/
  claim : Lean.Name

/-- One named run of a scenario: one script on one program. A scenario's record lists each one
once, and every consumer of a script takes it from that list: the gate, the host lane
(`harness/truth/session/Keyed.lean`) and the engine's lane (`Test/Dogfood/Scenario/Tape.lean`).
A lane quotes a run as the scenario's name, a slash and the run's name (`Scenario.quote`). -/
structure NamedRun where
  /-- The run's name in its scenario. -/
  name : String
  /-- The built program, opened as its battery opens it: under its name and its budgets. -/
  opened : Run
  /-- The script. -/
  moves : List Move

/-- A named run, played: the run that its script reaches from the opened program. -/
def NamedRun.played (run : NamedRun) : Run := play run.opened run.moves

/-- One control of an entry. A green control is a run that the entry allows. A red control is a
fault made on purpose, which the session must refuse or the observation must tell apart. A
control holds no script: it names the runs that its comparison reads. -/
structure Control where
  /-- The clause or the law this run controls, by its name. -/
  clause : String
  /-- `false` for a green control, `true` for a red control. -/
  isRed : Bool
  /-- What the run shows. -/
  name : String
  /-- The named runs that the comparison reads, by their names in the scenario's record, in the
  order the comparison takes them. Empty for a control that compares no script's run. -/
  reads : List String
  /-- Whether the runs show it: a comparison on the scenario's observation, decided by running.
  The gate plays each named run once and hands the comparison the runs that `reads` names, in
  that order. -/
  holds : List Run → Bool

/-- A green control of an entry. -/
def green (clause name : String) (reads : List String) (holds : List Run → Bool) : Control :=
  ⟨clause, false, name, reads, holds⟩

/-- A red control of an entry. -/
def red (clause name : String) (reads : List String) (holds : List Run → Bool) : Control :=
  ⟨clause, true, name, reads, holds⟩

/-- A scenario's record. The program, the observation and the claims are named as declarations,
so a name that no longer resolves fails where the record is written. -/
structure Scenario where
  /-- The scenario's name, as its row of `Test/Dogfood/README.md` quotes it. -/
  name : String
  /-- The program the scenario runs. -/
  program : Lean.Name
  /-- The one named observation every control compares. -/
  observation : Lean.Name
  /-- The claim: the theorem whose proof assembles the clauses. Its standing is derived from its
  proof: proved, or proved modulo the clauses that are planned goals. -/
  claim : Lean.Name
  /-- The assembled clauses. The claim's proof uses the declaration of each, and rests on no
  planned goal besides them. The gate measures both, so the record says what the proof does. -/
  clauses : List Clause
  /-- The associated laws: laws that the scenario's runs control. The record claims no dependency
  of the claim on them, and the gate measures none. -/
  laws : List Clause := []
  /-- The named runs: each script of the scenario, once, on the program it runs on. A name
  stands once, and some control reads each run. The order is the order in which a lane performs
  the runs. -/
  runs : List NamedRun := []
  /-- The controls: for each clause and each law a green control and at least one red control. -/
  controls : List Control

/-- The named run of a record with this name. -/
def Scenario.run? (s : Scenario) (name : String) : Option NamedRun :=
  s.runs.find? (·.name == name)

/-- A run of a record as a lane quotes it: the scenario's name, a slash and the run's name. The
host lane and the engine's lane quote a run by this one function, so a name means one run on
both. -/
def Scenario.quote (s : Scenario) (run : NamedRun) : String := s.name ++ "/" ++ run.name

/-- The names that a record lists more than once, each once, in the record's order. -/
def Scenario.repeated (s : Scenario) : List String :=
  (s.runs.foldl (fun (state : List String × List String) run =>
    if !state.1.contains run.name then (state.1 ++ [run.name], state.2)
    else if state.2.contains run.name then state
    else (state.1, state.2 ++ [run.name])) ([], [])).2

/-- The named runs that no control reads, by name, in the record's order. The gate refuses such
a run: a lane would perform it, and no control of the battery would compare it. -/
def Scenario.unread (s : Scenario) : List String :=
  (s.runs.map (·.name)).filter fun name => !s.controls.any (·.reads.contains name)

/-- What is wrong with a record as data, each finding in a sentence: a clause or a law with no
green control or no red control, a run's name listed twice, a named run that no control reads, a
control that names no entry, a control that reads a run which the record does not list, a
control that fails. It plays each named run once, and it hands each control the runs that the
control reads. Empty for a record with no finding. -/
def Scenario.problems (s : Scenario) : List String :=
  let played := s.runs.map fun run => (run.name, run.played)
  let missing := fun (kind : String) (entries : List Clause) =>
    entries.flatMap fun entry =>
      [false, true].filterMap fun isRed =>
        if s.controls.any (fun control => control.clause == entry.name && control.isRed == isRed)
        then none
        else some (s.name ++ ": the " ++ kind ++ " \"" ++ entry.name ++ "\" has no " ++
          (if isRed then "red control" else "green control"))
  missing "clause" s.clauses ++ missing "law" s.laws ++
  s.repeated.map (fun name => s.name ++ ": the record lists the run \"" ++ name ++ "\" twice") ++
  s.unread.map (fun name => s.name ++ ": no control reads the run \"" ++ name ++ "\"") ++
  s.controls.filterMap fun control =>
    if !(s.clauses ++ s.laws).any (·.name == control.clause) then
      some (s.name ++ ": the control \"" ++ control.name ++ "\" names no clause and no law")
    else
      match control.reads.find? (fun name => !played.any (·.1 == name)) with
      | some name =>
        some (s.name ++ ": the control \"" ++ control.name ++ "\" reads the run \"" ++ name ++
          "\", which the record does not list")
      | none =>
        let runs := control.reads.filterMap fun name => (played.find? (·.1 == name)).map (·.2)
        if !control.holds runs then some (s.name ++ ": the control \"" ++ control.name ++ "\" fails")
        else none

/-- The declarations a record names besides its claims. -/
def Scenario.declarations (s : Scenario) : List Lean.Name := [s.program, s.observation]

/-- The claims a record names: the scenario's claim, then each clause's and each law's. -/
def Scenario.claims (s : Scenario) : List Lean.Name :=
  s.claim :: (s.clauses ++ s.laws).map (·.claim)

/-- Whether the semantics registry (`tools/Tools/SemanticsRegistry.lean`) places a declaration of
a module. A requirement lists it as a top node, or a registry claim points at it, or its module
is a default module of a concept: an untagged theorem of that module inherits the concept. -/
def registered (name module : Lean.Name) : Bool :=
  let registry := Tools.Semantics.registry
  registry.requirements.any (·.top.contains name) ||
    registry.claims.any (fun claim =>
      match claim.pointer with
      | .witness witness => witness == name
      | .refutedBy _ witness => witness == name
      | _ => false) ||
    registry.concepts.any (·.defaultModules.contains module)

/-- `#scenario_gate S₁ … Sₙ`, at the foot of a battery, checks each scenario's record against the
environment. It plays each named run once and judges each control on the runs that the control
reads. It fails, naming every finding, when:

* the program or the observation does not resolve to a declaration;
* the claim, a clause's claim or a law's claim does not resolve to a theorem or a planned goal;
* such a claim has no placement. A declaration of a battery carries its own at a requirement
  (`@[semantics "concept" (requirement := Rn)]`, decisions row 207). Any other declaration
  carries `@[semantics …]`, or the semantics registry places it (`registered`);
* the claim's proof does not reach an assembled clause. The measure is the planning graph
  (`ProofGraph.buildPlan`, `tools/ProofGraph/Plan.lean`) over the placed claims and their placed
  clauses. A planned goal is reached when the claim rests on it (`Node.restsOn`). A theorem is
  reached when the walk from the claim's proof reaches it through the batteries' declarations
  (`Node.nearest`);
* the claim rests on a planned goal that no clause names;
* a clause or a law has no green control, or no red control (`Scenario.problems`);
* the record lists one run's name twice (`Scenario.problems`);
* no control reads a named run of the record (`Scenario.unread`, `Scenario.problems`);
* a control names no clause and no law of its scenario, reads a run that the record does not
  list, or fails (`Scenario.problems`).

An associated law gets no dependency check: the record claims none. A claim with no placement
stays out of the plan, and the gate measures no dependency of it or on it. The plan refuses a
node above the semantic axiom ceiling by an error of its own, which fails the command
(`Test/Audit/ProofGraphPlan.lean` holds that control). The command builds one plan, with an axiom
memo of its own. It expands to one `run_cmd`, which leaves no declaration. The check reads the
environment, and no reader of the environment stays under the axiom ceiling
(`Test/Audit/AxiomGate.lean`). -/
syntax (name := scenarioGate) "#scenario_gate " ident+ : command

open Lean in
@[macro scenarioGate] def expandScenarioGate : Macro := fun stx => do
  let scenarios : Array (TSyntax `term) := stx[1].getArgs.map (⟨·⟩)
  `(run_cmd Lean.Elab.Command.liftTermElabM do
      let env ← Lean.getEnv
      let scenarios : List Test.Dogfood.Scenario.Scenario := [$scenarios,*]
      let unplaced := fun (name : Lean.Name) =>
        let module := Effect4.Laws.Auto.semanticsModule env name
        let tag := Effect4.Laws.Auto.semanticsAttribute.getParam? env name
        if !((env.find? name) matches some (.thmInfo _)) then
          some s!"the claim {name} is no theorem and no planned goal"
        else if (`Test).isPrefixOf module then
          if (tag.bind (·.requirement)).isSome then none
          else some s!"the claim {name} has no placement at a requirement"
        else if tag.isSome || Test.Dogfood.Scenario.registered name module then none
        else some s!"the claim {name} has no placement: no semantics attribute and no row of the semantics registry"
      let placed := fun (name : Lean.Name) => (unplaced name).isNone
      let nodes := (scenarios.flatMap fun scenario =>
        if placed scenario.claim then
          scenario.claim :: (scenario.clauses.map (·.claim)).filter placed
        else []).eraseDups
      let plan ← if nodes.isEmpty then pure { nodes := #[] }
        else ProofGraph.buildPlan [`Test] nodes.toArray (← IO.mkRef {})
      let mut findings : Array String := #[]
      for scenario in scenarios do
        for name in scenario.declarations do
          unless env.contains name do
            findings := findings.push s!"{scenario.name}: {name} does not resolve to a declaration"
        for name in scenario.claims do
          if let some finding := unplaced name then
            findings := findings.push s!"{scenario.name}: {finding}"
        if placed scenario.claim then
          let mut reached : Array Lean.Name := #[scenario.claim]
          for _ in plan.nodes do
            for node in plan.nodes do
              if reached.contains node.name then
                for next in node.nearest ++ node.restsOn do
                  unless reached.contains next do reached := reached.push next
          for clause in scenario.clauses do
            if placed clause.claim && !reached.contains clause.claim then
              findings := findings.push
                s!"{scenario.name}: the proof of {scenario.claim} does not reach the clause \"{clause.name}\" ({clause.claim})"
          for goal in ((plan.find? scenario.claim).map (·.restsOn)).getD #[] do
            unless scenario.clauses.any (·.claim == goal) do
              findings := findings.push
                s!"{scenario.name}: the claim {scenario.claim} rests on the planned goal {goal}, which no clause names"
        findings := findings ++ scenario.problems.toArray
      unless findings.isEmpty do
        throwError (String.intercalate "\n" findings.toList))

/-! ## 6. A log's note

A scenario's program keeps a log in a cell: the assignments, the released connections, the
cleanups. Each battery wrote the same append under the fixed name `xs` for the cell's value. A
row elaborates its whole binder term under that name, so a caller's variable `xs` inside the
entry would read the log. The batteries' entries hold no such variable, so their trees are the
same under either helper. The one helper here mints the name
(`Ref.updateWith`, `src/Effect4/Program/Authoring/Rows.lean`).

Placement of the controls. They are finite controls of `var_push_minted`
(`src/Effect4/Laws/Program/Author.lean`): a minted binder leaves a variable that an author wrote
reading what it read. That law serves the claim `operation-data-scoped` (concept
`initial-algebras-folds`, requirement R4). The promise is for a variable that the caller reads
through `var`. A source term that inspects its scope in another way is outside it. The two
helpers have one type, so the controls compare a value: typing cannot see the capture. -/

section Note

open Effect4.Program.Authoring

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. The name of the
cell's current value is minted, so a variable that the caller reads through `var` keeps its
reading inside the entry. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.updateWith log fun xs => app "append" [xs, app "cons" [x, app "nil" []]]

/-! The collision's control. Its pieces stand in a namespace of their own, so that no battery
of this folder reads one by accident. -/

namespace Collision

/-- The helper that each battery wrote before: the same append under the fixed name `xs`. It
stays as the red control of the collision. -/
def noteFixed (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log

/-- The list of the given numbers, as a term. -/
def numbers : List Nat → TermSrc
  | [] => app "nil" []
  | n :: rest => app "cons" [nat n, numbers rest]

/-- Codex's collision case. An outer variable, under the name `outer`, holds `[7, 8]`. The log
holds `[100]`. The entry is the length of the outer variable. The module answers the log. -/
def program (outer : String) (noteWith : TermSrc → TermSrc → Src NativeOp) : Module NativeOp :=
  { main := bindName outer (succeed (numbers [7, 8])) fun _ =>
      bindName "log" (Ref.make (numbers [100])) fun log =>
        andThen (noteWith log (app "length" [var outer])) (Ref.get log) }

/-- The log that a collision module answers. -/
def logged (m : Module NativeOp) : Option ExitV :=
  (Effect4.Api.Author.build m).toOption.map (·.runSync)

-- Green: under the minted name the entry reads the outer `xs`, of length 2.
#guard logged (program "xs" note) = some (.success (.list [.nat 100, .nat 2]))
-- Red: under the fixed name the entry reads the log itself, of length 1. Both modules build:
-- the two lists have one type.
#guard logged (program "xs" noteFixed) = some (.success (.list [.nat 100, .nat 1]))
-- A name that does not collide: the two helpers elaborate one tree, and it answers `[100, 2]`.
#guard decide (elaborateModule (program "ys" note) = elaborateModule (program "ys" noteFixed))
#guard logged (program "ys" noteFixed) = some (.success (.list [.nat 100, .nat 2]))

end Collision

end Note

end Test.Dogfood.Scenario
