import Test.Dogfood.Proofs.HostPayloads
import Test.Dogfood.Proofs.HostTimeoutSource
import Test.Dogfood.Proofs.HostJournal
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.LinkedRows

/-!
Concept: host-session-protocol, R6, the applied-body clause of the timeout claim.
Question: an applied successful receipt appears in the current call observation.
Consumer: the native returned-body proof of `Timeout.stale_never_applies`.
Reach: every recorded fetch run, including arbitrary raw rows and incomplete commands.
The ledger retains actual binding records and receipt payloads. It proves no value flow or progress.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostAppliedObservation
open Effect4 Effect4.Machine Effect4.Program Effect4.Run
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario
open Test.Dogfood.Proofs.HostPayloads

/-- Each live association comes from its exact accepted binding row. -/
def ActiveFrom (s : Run) : Prop :=
  ∀ entry ∈ s.session.active, (entry.call, entry.token) ∈ bound s

/-- A received payload keeps its binding and the declared row selected by preflight. -/
def ReceiptFrom (s : Run) (reply : Reply) : Prop :=
  ∃ call token row, (call, token) ∈ bound s ∧ reply.key = ⟨call.fiber, token⟩ ∧
    s.rowOf call.op = some row

/-- Exact associations and accepted receipts are read from the current journal prefix. -/
def Holds (s : Run) : Prop :=
  s.journal.length = s.phases.length ∧ ActiveFrom s ∧
    ∀ reply ∈ acceptedReplies s, ReceiptFrom s reply

theorem bound_step (s : Run) (c : Command) (len : s.journal.length = s.phases.length) :
    bound (s.step c) = bound s ++
      (match c, (Api.Runner.result s.runner c).phase with
        | .bind call token, .bound => [(call, token)]
        | _, _ => []) := by
  unfold bound rows
  change (Run.rows (s.step c)).filterMap _ = _
  rw [rows_step s c len, List.filterMap_append, filterMap_singleton]
  generalize (Api.Runner.result s.runner c).phase = phase
  cases c <;> cases phase <;> rfl

theorem rowOf_step (s : Run) (c : Command) (op : NativeOp) :
    (s.step c).rowOf op = s.rowOf op := by
  cases op <;> rfl

theorem receipt_mono (s : Run) (c : Command) (len : s.journal.length = s.phases.length)
    (reply : Reply) (held : ReceiptFrom s reply) : ReceiptFrom (s.step c) reply := by
  obtain ⟨call, token, row, recorded, key, declared⟩ := held
  refine ⟨call, token, row, ?_, key, ?_⟩
  · rw [bound_step s c len]
    exact List.mem_append_left _ recorded
  · rw [rowOf_step]
    exact declared

/-- Preflight uses a declared external row at the exact association it selects. -/
theorem preflight_row (s : Run) (reply : Reply) (decision : NativeDecision)
    (accepted : preflight s.session reply = .ok decision) :
    ∃ entry row, entry ∈ s.session.active ∧ reply.key = entry.key ∧
      s.rowOf entry.call.op = some row := by
  obtain ⟨entry, found, _, envelope, _⟩ := preflight_envelope s.session reply decision accepted
  have matched := List.find?_some found
  have key : entry.key = reply.key := beq_iff_eq.mp matched
  rcases envelope with ordinary | instanceCase
  · obtain ⟨index, request, row, actual, declared, _⟩ := admitted_row _ _ _ _ _ ordinary.2.2
    rw [ordinary.2.1] at actual
    have op := congrArg Prod.fst (Option.some.inj actual)
    change entry.call.op = .external index at op
    refine ⟨entry, row, List.mem_of_find?_eq_some found, key.symm, ?_⟩
    rw [op]
    exact declared
  · obtain ⟨index, row, _, _, op, declared, _⟩ := instanceCase.2.2
    change entry.call.op = .external index at op
    refine ⟨entry, row, List.mem_of_find?_eq_some found, key.symm, ?_⟩
    rw [op]
    exact declared

/-- An accepted receipt has an actual preflight witness. -/
theorem submit_preflight (s : Run) (reply : Reply)
    (accepted : (submit s.session reply).phase = .preflight) :
    ∃ decision, preflight s.session reply = .ok decision := by
  unfold submit at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i decision checked
      exact ⟨decision, checked⟩

/-- The binding records survive every session edit while active associations may be removed. -/
theorem active_step (s : Run) (c : Command) (len : s.journal.length = s.phases.length)
    (held : ActiveFrom s) : ActiveFrom (s.step c) := by
  cases c with
  | bind call token =>
    rcases bindCall_cases s.session call token with ⟨why, result⟩ | ⟨_, _, result⟩
    · have phase : (Api.Runner.result s.runner (.bind call token)).phase = .refused why := by
        change (bindCall s.session call token).phase = _
        rw [result]
      unfold ActiveFrom
      rw [Run.step_session_bind, result, bound_step s (.bind call token) len, phase]
      exact fun entry present => List.mem_append_left _ (held entry present)
    · have phase : (Api.Runner.result s.runner (.bind call token)).phase = .bound := by
        change (bindCall s.session call token).phase = _
        rw [result]
      unfold ActiveFrom
      rw [Run.step_session_bind, result, bound_step s (.bind call token) len, phase]
      intro entry present
      rcases List.mem_append.mp present with old | new
      · exact List.mem_append_left _ (held entry old)
      · rw [List.mem_singleton.mp new]
        exact List.mem_append_right _ (List.mem_singleton_self _)
  | submit reply =>
    unfold ActiveFrom
    rw [bound_step s (.submit reply) len, List.append_nil]
    rcases submit_cases s.session reply with ⟨same, _⟩ | ⟨_, same⟩
    · rw [Run.step_session_submit, same]
      exact held
    · rw [Run.step_session_submit, same]
      exact held
  | apply key =>
    unfold ActiveFrom
    rw [bound_step s (.apply key) len, List.append_nil]
    rcases applyReply_cases s.session key s.budget.fuel with ⟨same, _⟩ |
      ⟨fuel, decision, _, same⟩ | ⟨fuel, decision, entry, _, _, _, same⟩
    · rw [Run.step_session_apply, same]
      exact held
    · rw [Run.step_session_apply, same]
      exact held
    · rw [Run.step_session_apply, same]
      exact fun entry present => held entry (List.mem_filter.mp (List.mem_filter.mp present).1).1
  | control decision =>
    unfold ActiveFrom
    rw [bound_step s (.control decision) len, List.append_nil]
    rcases Run.advance_step s.session s.budget.fuel decision with ⟨why, same⟩ | ⟨_, same⟩
    · rw [Run.step_session_control, same]
      exact held
    · rw [Run.step_session_control, same]
      exact fun entry present => held entry (List.mem_filter.mp present).1

/-- A newly accepted receipt retains the exact binding and row used by preflight. -/
theorem receipt_new (s : Run) (reply : Reply) (active : ActiveFrom s)
    (accepted : (Api.Runner.result s.runner (.submit reply)).phase = .preflight) :
    ReceiptFrom s reply := by
  obtain ⟨decision, checked⟩ := submit_preflight s reply accepted
  obtain ⟨entry, row, present, key, declared⟩ := preflight_row s reply decision checked
  exact ⟨entry.call, entry.token, row, active entry present, key, declared⟩

/-- Every recorded row retains both association and receipt provenance. -/
theorem holds_step (s : Run) (c : Command) (held : Holds s) : Holds (s.step c) := by
  refine ⟨lengths_step s c held.1, active_step s c held.1 held.2.1, ?_⟩
  intro reply present
  rw [acceptedReplies_step s c held.1] at present
  rcases List.mem_append.mp present with old | new
  · exact receipt_mono s c held.1 reply (held.2.2 reply old)
  · cases c with
    | submit offered =>
      cases phase : (Api.Runner.result s.runner (.submit offered)).phase with
      | preflight =>
        rw [phase] at new
        have same := List.mem_singleton.mp new
        subst reply
        exact receipt_mono s (.submit offered) held.1 offered (receipt_new s offered held.2.1 phase)
      | _ => rw [phase] at new; cases new
    | _ => cases new

/-- Recorded runs contain no receipt without the binding and declared row that admitted it. -/
theorem holds_reached (s : Run) (reached : Run.Reached s) : Holds s := by
  apply Keeps.reached (fun s c _ held => holds_step s c held) ?_ s reached
  intro b id budget profile
  refine ⟨rfl, ?_, ?_⟩
  · intro entry present
    cases present
  · intro reply present
    cases present

/-- The exact accepted receipts have precisely the journal's accepted receipt keys. -/
theorem accepted_keys (s : Run) : (acceptedReplies s).map Reply.key = submittedKeys s := by
  unfold acceptedReplies submittedKeys
  rw [List.map_filterMap]
  congr 1
  funext entry
  obtain ⟨command, phase⟩ := entry
  cases command <;> cases phase <;> rfl

/-- A unique key selects exactly its payload. Consumer: `stored_receipt`. -/
theorem keyed_payload {α β γ : Type} [DecidableEq β] (key : α → β) (value : α → γ)
    (entries : List α) (selected : α) (unique : (entries.map key).Nodup)
    (member : selected ∈ entries) :
    (entries.filterMap fun entry => if key entry = key selected then some (value entry) else none) =
      [value selected] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
    have keys := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | tail
    · subst selected
      rw [List.filterMap_cons, if_pos rfl]
      have empty : (rest.filterMap fun entry =>
          if key entry = key first then some (value entry) else none) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro entry present
        apply if_neg
        intro equal
        exact keys.1 (List.mem_map.mpr ⟨entry, present, equal⟩)
      rw [empty]
    · have different : key first ≠ key selected := by
        intro same
        exact keys.1 (List.mem_map.mpr ⟨selected, tail, same.symm⟩)
      rw [List.filterMap_cons, if_neg different]
      exact ih keys.2 tail

/-- The observation's stored payload is the unique accepted receipt at its key. -/
theorem stored_receipt (s : Run) (reached : Run.Reached s) (reply : Reply)
    (member : reply ∈ acceptedReplies s) :
    Timeout.storedAt s reply.key = some reply.completion := by
  have unique : ((acceptedReplies s).map Reply.key).Nodup := by
    rw [accepted_keys]
    exact (ledger_reached s reached).submittedNodup
  have selected := keyed_payload Reply.key Reply.completion (acceptedReplies s) reply unique member
  have same : ((rows s).filterMap fun
      | (.submit r, .preflight) => if r.key == reply.key then some r.completion else none
      | _ => none) =
      (acceptedReplies s).filterMap (fun r => if r.key = reply.key then some r.completion else none) := by
    unfold acceptedReplies
    rw [List.filterMap_filterMap]
    congr 1
    funext entry
    obtain ⟨command, phase⟩ := entry
    cases command <;> cases phase <;> dsimp only
    all_goals simp only [beq_iff_eq, Option.bind_none, Option.bind_some]
  exact congrArg List.getLast? (same.trans selected)

/-- An accepted receipt's key remains visible among the actual held binding records. -/
theorem receipt_seen (s : Run) (reached : Run.Reached s) (reply : Reply)
    (member : reply ∈ acceptedReplies s) :
    ∃ seen, seenAt s reply.key = some seen ∧ seen ∈ held s ∧ seen.key = reply.key := by
  obtain ⟨call, token, row, recorded, key, declared⟩ := (holds_reached s reached).2.2 reply member
  let witness : Seen := ⟨row.spelling, call.request, ⟨call.fiber, token⟩⟩
  have present : witness ∈ held s := by
    apply List.mem_filterMap.mpr
    exact ⟨(call, token), recorded, by simp only [seenOf, declared, Option.map_some, witness]⟩
  cases found : seenAt s reply.key with
  | none =>
    have absent := List.find?_eq_none.mp found witness present
    exact False.elim (absent (beq_iff_eq.mpr key.symm))
  | some seen =>
    exact ⟨seen, rfl, List.mem_of_find?_eq_some found, HostJournal.seenAt_key s reply.key seen found⟩

/-- An applied key contributes its current binding observation. -/
theorem application_seen (s : Run) (key : Key) (seen : Seen)
    (applied : key ∈ appliedKeys s) (found : seenAt s key = some seen) : seen ∈ applications s := by
  obtain ⟨⟨command, phase⟩, present, selected⟩ := List.mem_filterMap.mp applied
  apply List.mem_filterMap.mpr
  refine ⟨(command, phase), present, ?_⟩
  cases command <;> cases phase <;> cases selected
  exact found

/-- Every successful applied receipt determines an answered held call in the current observation. -/
theorem body_fate (s : Run) (reached : Run.Reached s) (body : Val)
    (member : body ∈ appliedBodies s) :
    ∃ seen ∈ held s, Timeout.fateOf s seen = .answered body := by
  obtain ⟨reply, received, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · rename_i applied
    obtain ⟨seen, found, present, key⟩ := receipt_seen s reached reply received
    have actual := application_seen s reply.key seen applied found
    have stored := stored_receipt s reached reply received
    refine ⟨seen, present, ?_⟩
    unfold Timeout.fateOf
    rw [if_pos (List.contains_iff_mem.mpr actual), key, stored]
    cases completion : reply.completion with
    | ofExit exit =>
      rw [completion] at selected
      cases exit with
      | success value => cases selected; rfl
      | failure cause => cases selected
    | ofRefGet cell => rw [completion] at selected; cases selected
  · cases selected

/-- Every declared row of the concrete fetch uses the observed HTTP spelling. -/
theorem fetch_rows : Timeout.fetch.table.all (fun row => row.spelling == "Http.getQuote") = true := by
  kernel_rfl

/-- A held call of the actual fetch has its declared HTTP row spelling. -/
theorem held_fetch_row (s : Run) (table : s.built.table = Timeout.fetch.table)
    (seen : Seen) (present : seen ∈ held s) : seen.row = "Http.getQuote" := by
  obtain ⟨⟨call, token⟩, _, found⟩ := List.mem_filterMap.mp present
  unfold seenOf at found
  cases declared : s.rowOf call.op with
  | none => rw [declared] at found; cases found
  | some row =>
    rw [declared] at found
    cases found
    obtain ⟨index, _, external⟩ := Run.rowOf_external s call.op row declared
    obtain ⟨raw, entry, _, _, same⟩ := externalRow_raw external
    rw [table] at entry
    have named := List.all_eq_true.mp fetch_rows raw (List.mem_of_getElem? entry)
    rw [same]
    exact beq_iff_eq.mp named

/-- Applied successful bodies appear in the original timeout call observation, for every script.
This reader uses no restriction on moves and no native value-flow assumption. -/
theorem applied_body_seen (b : Api.Built) (fetchBuilt : Api.Author.build Timeout.fetch = .ok b)
    (moves : List Move) (body : Val)
    (member : body ∈ appliedBodies (Scenario.play (Timeout.opened b) moves)) :
    (Timeout.observe (Scenario.play (Timeout.opened b) moves)).calls.contains (.answered body) = true := by
  let s := Scenario.play (Timeout.opened b) moves
  have reached : Run.Reached s := Scenario.reached_play _ moves (Run.Reached.opened _ _ _ _)
  obtain ⟨seen, present, fate⟩ := body_fate s reached body member
  have table : s.built.table = Timeout.fetch.table := by
    change (Scenario.play (Timeout.opened b) moves).built.table = _
    rw [(Scenario.play_opened (Timeout.opened b) moves).1]
    exact (HostTimeoutSource.built_fetch fetchBuilt).2
  have spelling := held_fetch_row s table seen present
  apply List.contains_iff_mem.mpr
  apply List.mem_map.mpr
  exact ⟨seen, List.mem_filter.mpr ⟨present, beq_iff_eq.mpr spelling⟩, fate⟩

end Test.Dogfood.Proofs.HostAppliedObservation
