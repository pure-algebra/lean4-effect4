import Effect4.Laws.Run.Journal
import Effect4.Laws.Api.HostSession

/-!
# Run.Payload — the exact receipt at each reply application

The payload ledger of a recorded run (`PayloadLedger`): every reply that the session stores is an
accepted receipt of the run's own journal, at its own key. So a reply application applies that
receipt's complete completion at the call bound to its key (`application_payload`). The session's
`preflight` admitted the receipt first, and the machine was not stuck (`application_live`).

The ledger and `application_payload` moved here unchanged from the timeout battery
(`Test/Dogfood/Proofs/HostPayloads.lean`, where they landed on 2026-10-11). The law graph reads
them here: the typed replay's law applies them (`Live.replay_at_call_instance`,
`src/Effect4/Laws/Api/Live.lean`; decisions rows 98 and 373 (8)). The battery keeps its own
readers and names the moved declarations from here.

Placement: concept `host-session-protocol`, R6. The ledger is a step of `stale_never_applies`
clause four, whose consumer is the timeout body's value-flow invariant. It is a step of the
proposed claim `replay-at-call-instance` too. Reach: every recorded run (`Run.Reached`), table,
budget and raw command. It does not establish the origin of a program's returned value, progress,
or a host implementation's behaviour.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

/-- The current journal's accepted reply receipts, with their complete payloads. -/
def acceptedReplies (s : Run) : List Reply :=
  (journalRows s).filterMap fun
    | (.submit reply, .preflight) => some reply
    | _ => none

/-- Every pending payload is its own key's accepted receipt in the current prefix. -/
def PendingFrom (receipts : List Reply) (slots : List ReplySlot) : Prop :=
  ∀ slot ∈ slots, ∀ reply, slot.reply = some reply →
    reply ∈ receipts ∧ reply.key = slot.key

theorem PendingFrom.mono {a b : List Reply} {slots : List ReplySlot}
    (h : PendingFrom a slots) (sub : a ⊆ b) : PendingFrom b slots :=
  fun slot hs reply hr => ⟨sub (h slot hs reply hr).1, (h slot hs reply hr).2⟩

theorem PendingFrom.filter {receipts : List Reply} {slots : List ReplySlot}
    (h : PendingFrom receipts slots) (p : ReplySlot → Bool) :
    PendingFrom receipts (slots.filter p) :=
  fun slot hs reply hr => h slot (List.mem_filter.mp hs).1 reply hr

theorem PendingFrom.emptySlot {receipts : List Reply} {slots : List ReplySlot}
    (h : PendingFrom receipts slots) (key : Key) :
    PendingFrom receipts (slots ++ [⟨key, none⟩]) := by
  intro slot hs reply hr
  rcases List.mem_append.mp hs with hs | hs
  · exact h slot hs reply hr
  · rw [List.mem_singleton.mp hs] at hr
    cases hr

theorem PendingFrom.store {receipts : List Reply} {slots : List ReplySlot}
    (h : PendingFrom receipts slots) (r : Reply) :
    PendingFrom (receipts ++ [r]) (storeReply slots r) := by
  intro slot hs reply hr
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
  by_cases hk : old.key = r.key
  · rw [if_pos hk] at hr ⊢
    cases hr
    exact ⟨List.mem_append_right _ (List.mem_singleton_self _), hk.symm⟩
  · rw [if_neg hk] at hr ⊢
    exact ⟨List.mem_append_left _ (h old hold reply hr).1, (h old hold reply hr).2⟩

/-- The payload ledger reads the run's journal rather than future replies. -/
def PayloadLedger (s : Run) : Prop :=
  s.journal.length = s.phases.length ∧ PendingFrom (acceptedReplies s) s.session.pending

theorem acceptedReplies_step (s : Run) (c : Command)
    (len : s.journal.length = s.phases.length) :
    acceptedReplies (s.step c) = acceptedReplies s ++
      (match c, (Api.Runner.result s.runner c).phase with
        | .submit reply, .preflight => [reply]
        | _, _ => []) := by
  unfold acceptedReplies
  rw [rows_step s c len, List.filterMap_append, filterMap_singleton]
  generalize (Api.Runner.result s.runner c).phase = phase
  cases c <;> cases phase <;> rfl

theorem payload_step (s : Run) (c : Command) (h : PayloadLedger s) :
    PayloadLedger (s.step c) := by
  refine ⟨lengths_step s c h.1, ?_⟩
  cases c with
  | bind call token =>
    rw [acceptedReplies_step s (.bind call token) h.1, List.append_nil]
    rcases bindCall_cases s.session call token with ⟨why, hr⟩ | ⟨_, _, hr⟩
    · rw [Run.step_session_bind, hr]
      exact h.2
    · rw [Run.step_session_bind, hr]
      exact h.2.emptySlot _
  | submit reply =>
    rcases submit_cases s.session reply with ⟨same, ne⟩ | ⟨phase, hr⟩
    · rw [Run.step_session_submit, same, acceptedReplies_step s (.submit reply) h.1]
      have ph : (Api.Runner.result s.runner (.submit reply)).phase ≠ .preflight := ne
      cases hp : (Api.Runner.result s.runner (.submit reply)).phase with
      | preflight => exact (ph hp).elim
      | _ => simpa only [List.append_nil] using h.2
    · rw [Run.step_session_submit, hr, acceptedReplies_step s (.submit reply) h.1]
      have ph : (Api.Runner.result s.runner (.submit reply)).phase = .preflight := phase
      rw [ph]
      exact h.2.store reply
  | apply key =>
    rw [acceptedReplies_step s (.apply key) h.1, List.append_nil]
    rcases applyReply_cases s.session key s.budget.fuel with ⟨same, _⟩ |
      ⟨fuel, decision, _, hr⟩ | ⟨fuel, decision, bound, _, _, _, hr⟩
    · rw [Run.step_session_apply, same]
      exact h.2
    · rw [Run.step_session_apply, hr]
      exact h.2
    · rw [Run.step_session_apply, hr]
      exact (h.2.filter _).filter _
  | control decision =>
    rw [acceptedReplies_step s (.control decision) h.1, List.append_nil]
    rcases Run.advance_step s.session s.budget.fuel decision with ⟨why, hr⟩ | ⟨_, hr⟩
    · rw [Run.step_session_control, hr]
      exact h.2
    · rw [Run.step_session_control, hr]
      exact h.2.filter _

theorem payload_open (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    PayloadLedger (Run.open b id budget profile) :=
  ⟨rfl, fun _ hs _ _ => absurd hs List.not_mem_nil⟩

theorem payload_reached (s : Run) (reached : Run.Reached s) : PayloadLedger s :=
  Keeps.reached (fun s c _ h => payload_step s c h) payload_open s reached

/-- Reading a pending payload recovers its complete receipt at the same key. -/
theorem readReply_from {receipts : List Reply} {slots : List ReplySlot}
    (h : PendingFrom receipts slots) (key : Key) (reply : Reply)
    (read : readReply slots key = some reply) : reply ∈ receipts ∧ reply.key = key := by
  induction slots with
  | nil => cases read
  | cons slot rest ih =>
    unfold readReply at read
    split at read
    · rename_i hk
      exact ⟨(h slot List.mem_cons_self reply read).1,
        (h slot List.mem_cons_self reply read).2.trans hk⟩
    · exact ih (fun x hx r hr => h x (List.mem_cons_of_mem _ hx) r hr) read

/-- Successful application selects the current prefix's exact accepted receipt at its own key.
The machine receives that receipt's complete completion, including arbitrary causes.
This is a step of the timeout body's value-flow invariant, not its returned-value conclusion, and
a step of `Live.replay_at_call_instance`. -/
theorem application_payload (s : Run) (reached : Run.Reached s) (key : Key)
    (applied : (Api.Runner.result s.runner (.apply key)).phase = .applied) :
    ∃ reply bound,
      reply ∈ acceptedReplies s ∧ reply.key = key ∧
      readReply s.session.pending key = some reply ∧
      s.session.active.find? (fun b => b.key == key) = some bound ∧
      preflight s.session reply =
        .ok (.answerAsync bound.call.fiber bound.token reply.completion) ∧
      (s.step (.apply key)).machine =
        steppedBy s.built.program s.budget.fuel s.built.table s.machine
          (.answerAsync bound.call.fiber bound.token reply.completion) := by
  have ledger := (payload_reached s reached).2
  change (applyReply s.session key s.budget.fuel).phase = .applied at applied
  cases hfuel : s.budget.fuel with
  | zero => rw [hfuel] at applied; cases applied
  | succ fuel =>
    rw [hfuel] at applied
    cases hfind : s.session.active.find? (fun b => b.key == key) with
    | none => simp only [applyReply, hfind] at applied; cases applied
    | some bound =>
      cases hread : readReply s.session.pending key with
      | none => simp only [applyReply, hfind, hread] at applied; cases applied
      | some reply =>
        cases hpre : preflight s.session reply with
        | error why => simp only [applyReply, hfind, hread, hpre] at applied; cases applied
        | ok decision =>
          obtain ⟨member, sameKey⟩ := readReply_from ledger key reply hread
          obtain ⟨bound', hb, _, _, hd⟩ := preflight_envelope s.session reply decision hpre
          rw [sameKey, hfind] at hb
          cases hb
          subst decision
          simp only [applyReply, hfind, hread, hpre] at applied
          split at applied
          · cases applied
          · rename_i protocol
            split at applied
            · rename_i gone
              refine ⟨reply, bound, member, sameKey, rfl, rfl, hpre, ?_⟩
              change (applyReply s.session key s.budget.fuel).session.machine = _
              rw [hfuel]
              simp only [applyReply, hfind, hread, hpre, if_neg protocol, if_pos gone]
              rfl
            · cases applied

/-! ## A reply application is taken at a machine that is not stuck

Steps of `Live.replay_at_call_instance` (`src/Effect4/Laws/Api/Live.lean`): the session's
`preflight_success_prepared_fits` asks that the machine is not stuck, and a reply application
that the session applied meets it. -/

/-- Step of `application_live`: at a stuck machine, an answer decision leaves the machine as it
was, at every command budget. -/
theorem steppedBy_answer_stuck (program : NativeEff) (fuel : Nat) (table : RowTable)
    (m : NativeMachine) (fiber : FiberId) (token : Nat) (answer : Answer)
    (stuck : m.stuck.isSome = true) :
    steppedBy program fuel table m (.answerAsync fiber token answer) = m := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    unfold steppedBy
    simp only [stepDecisionState, prepareAsyncAnswer, stuck, if_true, stepDecisionState.loop]
    letI := evaluatorFor program table
    exact congrArg Prod.fst (driveState_stuck _ _ _ _ stuck)

/-- **A reply application that a recorded run applied was taken at a machine that is not stuck.**
The session's `preflight` found the bound call's guard live before the step, and the step removed
it. At a stuck machine an answer decision changes nothing (`steppedBy_answer_stuck`), so the guard
would have stayed.

Placement: concept `host-session-protocol`, R6; a step of the proposed claim
`replay-at-call-instance`, whose consumer `Live.replay_at_call_instance` hands it to
`preflight_success_prepared_fits`. Reach: every recorded run and every reply application that the
session applied. It does not establish that a later step leaves the machine live. -/
theorem application_live (s : Run) (reached : Run.Reached s) (key : Key)
    (applied : (Api.Runner.result s.runner (.apply key)).phase = .applied) :
    s.machine.stuck = none := by
  obtain ⟨reply, bound, _, sameKey, _, found, accepted, machine⟩ :=
    application_payload s reached key applied
  cases hstuck : s.machine.stuck with
  | none => rfl
  | some why =>
    exfalso
    obtain ⟨bound', selected, _, envelope, _⟩ := preflight_envelope s.session reply _ accepted
    rw [sameKey, found] at selected
    cases selected
    have held : Program.requestOf s.machine bound.call.fiber bound.token ≠ none := by
      rcases envelope with envelope | envelope <;>
        exact fun gone => Option.some_ne_none _ (envelope.2.1.symm.trans gone)
    have selects := List.find?_some found
    have hkey : bound.key = key := beq_iff_eq.mp selects
    rw [← hkey] at found applied machine
    have gone := applied_guard_absent s.session s.budget.fuel bound found applied
    have same : (applyReply s.session bound.key s.budget.fuel).session.machine = s.machine := by
      change (s.step (.apply bound.key)).machine = s.machine
      rw [machine]
      exact steppedBy_answer_stuck _ _ _ _ _ _ _ (by rw [hstuck]; rfl)
    rw [same] at gone
    exact held gone

end Effect4.Run
