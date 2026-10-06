import Effect4.Run.Tape
import Effect4.Laws.Run
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Run.Rows — what a row of a run keeps, and what it changes

General facts of a session's rows and of a run's rows. Each holds for every session or every
run, and none names a scenario. They came from the scenario support
(`Test/Dogfood/Scenario.lean`), each with its statement and its proof unchanged (decisions
row 284, point 5).

* **Playing rows keeps what a run was opened with** (`play_id`, `play_budget`, `play_profile`),
  beside `play_built` (`src/Effect4/Laws/Run.lean`).
* **A receipt row is inert** (`bindCall_inert`, `submit_inert`, `step_receiptRow`,
  `play_receiptRows`, `receive_receiptRows`). Holding a call and receiving a reply leave four
  readings as they were: the machine, the count of applied replies, the consumed calls and the
  retired calls.
* **A reply application consumes the selected call only** (`applied_selects`).
* **A control retires the held calls whose guard it removed** (`control_retires`).

Placement. The concept is `host-session-protocol`. `applied_selects` and `control_retires` are
nodes of R6 by their tags. The inertness laws are steps of `receipt_inert`, the driver's law of
the same requirement (`Test/Dogfood/Scenario.lean`). The three keeping laws are steps of
`replays`, the driver's law at R13 in that battery. No law here establishes reply admission,
the order of two reply applications, or which guards a decision removes.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## Playing rows keeps what a run was opened with

The three laws are steps of `replays` (`Test/Dogfood/Scenario.lean`), through its helper
`play_opened`. -/

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

/-! ## A receipt row is inert

The laws of this section are steps of `receipt_inert` (`Test/Dogfood/Scenario.lean`): a reply
receipt does not advance the machine. `bindCall_inert` and `submit_inert` are steps of
`tape_replays` too (`src/Effect4/Laws/Run/Tape.lean`). The rows are those that `receiptRow`
tells (`src/Effect4/Run/Tape.lean`). -/

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

/-! ## A reply application consumes the selected call only -/

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

/-! ## A control retires the calls whose guard it removed, and no other -/

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

end Effect4.Run
