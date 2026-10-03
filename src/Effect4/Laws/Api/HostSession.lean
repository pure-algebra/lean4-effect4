import Effect4.Api.HostSession
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Program.Typed.Admission

/-! Checked host protocol laws. Receipt commutation is equality of sessions, including
stored replies and the unchanged machine. Answer application is a separate ordered step.
Authority: Test/contracts/foundation-wave2.contract.md, T-09 / T-12 amendment. -/
set_option autoImplicit false
namespace Effect4.Api.HostSession
open Effect4 Effect4.Program

/-- Successful preflight proves the existing envelope for the association selected by key. -/
theorem preflight_envelope {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : preflight s reply = .ok decision) :
    ∃ bound, s.active.find? (fun b => b.key == reply.key) = some bound ∧
      reply.callId = bound.call.callId ∧ Envelope table s.machine (bound.record reply) ∧
      decision = .answerAsync bound.call.fiber bound.token reply.completion := by
  unfold preflight at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i bound hbound
        split at h
        · cases h
        · rename_i hid
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i d hd
              cases h
              exact ⟨bound, hbound, by simpa using hid,
                acceptReply_envelope table s.machine (bound.record reply) decision hd,
                acceptReply_decision table s.machine (bound.record reply) decision hd⟩

theorem storeReply_commute (slots : List ReplySlot) (a b : Reply) (h : a.key ≠ b.key) :
    storeReply (storeReply slots a) b = storeReply (storeReply slots b) a := by
  simp only [storeReply, List.map_map]
  congr 1
  funext slot
  by_cases ha : slot.key = a.key <;> by_cases hb : slot.key = b.key <;>
    simp_all

/-- Writing one key leaves every other key's stored completion unchanged. -/
theorem readReply_store_other (slots : List ReplySlot) (reply : Reply) (key : Key)
    (h : key ≠ reply.key) : readReply (storeReply slots reply) key = readReply slots key := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    change readReply ((if slot.key = reply.key then { slot with reply := some reply } else slot) ::
      storeReply rest reply) key = readReply (slot :: rest) key
    by_cases ha : slot.key = reply.key
    · have hk : slot.key ≠ key := fun hk => h (hk.symm.trans ha)
      rw [if_pos ha]
      simp only [readReply, hk, if_false, ih]
    · rw [if_neg ha]
      by_cases hk : slot.key = key <;> simp only [readReply, hk, if_true, if_false, ih]

@[simp] theorem storeReply_keys (slots : List ReplySlot) (reply : Reply) (key : Key) :
    (storeReply slots reply).any (fun slot => slot.key == key) =
      slots.any (fun slot => slot.key == key) := by
  simp only [storeReply, List.any_map]
  congr 1
  funext slot
  by_cases h : slot.key = reply.key <;> simp [h]

@[simp] theorem preflight_pending {program : Api.Program} {table : RowTable}
    (s : Session program table) (slots : List ReplySlot) (reply : Reply) :
    preflight { s with pending := slots } reply = preflight s reply :=
  by aesop

private theorem bool_false_of_not_true (b : Bool) (h : ¬b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

private theorem bool_true_of_not_neg (b : Bool) (h : ¬(!b) = true) : b = true := by
  cases b with
  | false => exact False.elim (h rfl)
  | true => rfl

/-- The exact preconditions established by a successful receipt. -/
theorem submit_conditions {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (h : (submit s reply).phase = .preflight) :
    (readReply s.pending reply.key).isSome = false ∧
    (∃ d, preflight s reply = .ok d) ∧
    s.pending.any (fun slot => slot.key == reply.key) = true ∧
    HostProtocol.allows (HostProtocol.observe s.machine) (.submit reply.key)
      (HostProtocol.observe s.machine) = true := by
  unfold submit at h
  split at h
  · cases h
  · rename_i hp
    split at h
    · cases h
    · rename_i d hd
      split at h
      · cases h
      · rename_i hs
        split at h
        · cases h
        · rename_i hl
          exact ⟨bool_false_of_not_true _ hp, ⟨d, hd⟩,
            bool_true_of_not_neg _ hs, bool_true_of_not_neg _ hl⟩

/-- Two accepted receipts for distinct keys commute as whole sessions. The machine,
active calls, call IDs, consumed ledger, and retired ownership are unchanged in either
order. This is receipt/storage only, not `answerAsync` continuation execution. -/
theorem reply_commute {program : Api.Program} {table : RowTable}
    (s : Session program table) (a b : Reply) (different : a.key ≠ b.key)
    (ha : (submit s a).phase = .preflight) (hb : (submit s b).phase = .preflight) :
    (submit (submit s a).session b).session = (submit (submit s b).session a).session := by
  obtain ⟨hpa, ⟨da, hda⟩, hsa, hla⟩ := submit_conditions s a ha
  obtain ⟨hpb, ⟨db, hdb⟩, hsb, hlb⟩ := submit_conditions s b hb
  simp [submit, hpa, hpb, hda, hdb, hsa, hsb, hla, hlb,
    readReply_store_other _ _ _ different, readReply_store_other _ _ _ (Ne.symm different),
    storeReply_commute _ _ _ different]

/-- The named fiber-disjoint specialization of the stronger key-disjoint receipt law. -/
theorem reply_commute_disjoint {program : Api.Program} {table : RowTable}
    (s : Session program table) (a b : Reply) (different : a.key.fiber ≠ b.key.fiber)
    (ha : (submit s a).phase = .preflight) (hb : (submit s b).phase = .preflight) :
    (submit (submit s a).session b).session = (submit (submit s b).session a).session :=
  reply_commute s a b (fun h => different (congrArg HostProtocol.Key.fiber h)) ha hb

theorem readReply_store_self (slots : List ReplySlot) (reply : Reply)
    (present : slots.any (fun slot => slot.key == reply.key) = true) :
    readReply (storeReply slots reply) reply.key = some reply := by
  induction slots with
  | nil => cases present
  | cons slot rest ih =>
    change readReply ((if slot.key = reply.key then { slot with reply := some reply } else slot) ::
      storeReply rest reply) reply.key = some reply
    by_cases h : slot.key = reply.key
    · rw [if_pos h]
      simp only [readReply, h, if_true]
    · rw [if_neg h]
      simp only [readReply, h, if_false]
      apply ih
      simpa [List.any_cons, h] using present

/-- Within one key, a second receipt cannot replace an accepted pending completion. -/
theorem submit_duplicate {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (h : (submit s reply).phase = .preflight) :
    (submit (submit s reply).session reply).phase = .refused .pendingReply := by
  obtain ⟨hp, ⟨d, hd⟩, hs, hl⟩ := submit_conditions s reply h
  simp [submit, hp, hd, hs, hl, readReply_store_self s.pending reply hs]

/-- Receipt leaves the outstanding set and every other key's stored reply unchanged. -/
theorem submit_key_independence {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (key : Key) (different : key ≠ reply.key)
    (h : (submit s reply).phase = .preflight) :
    (submit s reply).session.active = s.active ∧
    readReply (submit s reply).session.pending key = readReply s.pending key := by
  obtain ⟨hp, ⟨d, hd⟩, hs, hl⟩ := submit_conditions s reply h
  simp [submit, hp, hd, hs, hl, readReply_store_other s.pending reply key different]

/-- Receipt never executes the machine, including on refusal. -/
theorem submit_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) : (submit s reply).session.machine = s.machine := by
  unfold submit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem submit_refusal_retains {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (why : Refusal)
    (h : preflight s reply = .error why) : (submit s reply).session = s := by
  unfold submit
  split
  · rfl
  · rw [h]

theorem applyPending_zero {program : Api.Program} {table : RowTable}
    (s : Session program table) : applyPending s 0 = ⟨.frontier, s⟩ :=
  by aesop

theorem applyReply_zero {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) : applyReply s key 0 = ⟨.frontier, s⟩ :=
  by aesop

theorem advance_answer_refuses {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (fiber : FiberId) (token : Nat) (reply : Answer) :
    advance s fuel (.answerAsync fiber token reply) = ⟨.refused .directAnswer, s⟩ :=
  by aesop

/-- The consumption receipt is absence of the exact applied guard, independently of
whether the subsequent command loop had enough fuel to finish. -/
theorem applied_guard_absent {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (bound : BoundCall)
    (ha : s.active.find? (fun b => b.key == bound.key) = some bound)
    (h : (applyReply s bound.key fuel).phase = .applied) :
    requestOf (applyReply s bound.key fuel).session.machine bound.call.fiber bound.token = none := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases hp : readReply s.pending bound.key with
    | none => simp [applyReply, ha, hp] at h
    | some reply =>
      cases hd : preflight s reply with
      | error why => simp [applyReply, ha, hp, hd] at h
      | ok decision =>
        simp only [applyReply, ha, hp, hd] at h ⊢
        split at h
        · cases h
        · rename_i protocol
          split at h
          · rename_i removed
            simp [protocol, removed, retire]
          · cases h

theorem applied_reply_refused {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (bound : BoundCall) (reply : Reply)
    (ha : s.active.find? (fun b => b.key == bound.key) = some bound)
    (h : (applyReply s bound.key fuel).phase = .applied) :
    acceptReply table (applyReply s bound.key fuel).session.machine (bound.record reply) = none :=
  acceptReply_none_of_unparked table _ _ (applied_guard_absent s fuel bound ha h)

/-- Every accepted application is an edge of the projected protocol over the actual
before/after machine observations. The selected decision is still justified by Envelope. -/
theorem applyReply_conforms {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (applyReply s key fuel).phase = .applied) :
    HostProtocol.allows (HostProtocol.observe s.machine) (.answer key)
      (HostProtocol.observe (applyReply s key fuel).session.machine) = true := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases ha : s.active.find? (fun bound => bound.key == key) with
    | none => simp [applyReply, ha] at h
    | some bound =>
      cases hp : readReply s.pending key with
      | none => simp [applyReply, ha, hp] at h
      | some reply =>
        cases hd : preflight s reply with
        | error why => simp [applyReply, ha, hp, hd] at h
        | ok decision =>
          simp only [applyReply, ha, hp, hd] at h ⊢
          split at h
          · cases h
          · rename_i hl
            split at h
            · rename_i removed
              have allowed : HostProtocol.allows (HostProtocol.observe s.machine) (.answer key)
                  (HostProtocol.observe (steppedBy program (fuel + 1) table s.machine decision)) = true := by
                simpa using hl
              simpa [hl, removed, retire] using allowed
            · cases h

/-- Accepted scheduler/clock/cancellation controls follow a projected protocol edge over
actual machine observations. A stuck or forbidden control is a refusal, not an edge. -/
theorem advance_conforms {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (decision : NativeDecision)
    (h : (advance s fuel decision).phase = .progressed) :
    HostProtocol.allows (HostProtocol.observe s.machine) (HostProtocol.controlLabel decision)
      (HostProtocol.observe (advance s fuel decision).session.machine) = true := by
  cases decision <;> simp only [advance] at h ⊢
  all_goals try cases h
  all_goals
    split at h
    · cases h
    · rename_i live
      split at h
      · cases h
      · rename_i allowed
        simp_all [retire]

/-! ## Accepted successful replies and the actual prepared value

Concept 9 (host-answer admission) meeting concept 1 membership; proposed T4 contributor
`session-success-prepared-membership`. `PreparedWanted` records the exact local question,
and `submit_success_prepared_fits` is its session API consumer. Placement and boundaries:
`docs/research/2026-10-03-session-work/t4-plan.md`, decisions 97–99, 117, 138–139 and 152.
This is not `AnswerOk`, whole-session typing, or a failure/handle admission theorem.
-/

/-- The selected association, parked row and actual successful preparation, with value
membership on the shape-decided fragment. No token declaration in a typed world is inferred. -/
def PreparedSuccess {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision) : Prop :=
  ∃ bound i request row result,
    s.active.find? (fun b => b.key == reply.key) = some bound ∧
    reply.callId = bound.call.callId ∧
    decision = .answerAsync bound.call.fiber bound.token reply.completion ∧
    requestOf s.machine bound.call.fiber bound.token = some (.external i, request) ∧
    externalRow table i = some row ∧
    (Machine.prepareAsyncAnswer (interpOf program table) s.machine bound.call.fiber bound.token
      reply.completion).2 = .success result ∧
    ∀ w : Typed.World, Typed.shapeDecides row.answer = true → Typed.Fits w result row.answer

/-- A session-accepted successful completion prepares the actual row-typed value. Membership
requires the selected row's shape-decided answer column; failures, world-reading columns and
token-world correlation remain outside this theorem. The session is not executed here. -/
theorem preflight_success_prepared_fits {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision) (value : Machine.Val)
    (live : s.machine.stuck = none)
    (success : reply.completion = .ofExit (.success value))
    (accepted : preflight s reply = .ok decision) : PreparedSuccess s reply decision := by
  obtain ⟨bound, selected, callId, envelope, decisionEq⟩ :=
    preflight_envelope s reply decision accepted
  have admitted : admit table s.machine
      (.answerAsync bound.call.fiber bound.token (.ofExit (.success value))) = none := by
    simpa only [BoundCall.record, success] using envelope.2.2
  obtain ⟨i, request, row, result, parked, rowAt, prepared, typed⟩ :=
    external_prepared_answer_typed program table s.machine bound.call.fiber bound.token value
      live admitted
  refine ⟨bound, i, request, row, result, selected, callId, decisionEq, parked, rowAt, ?_, ?_⟩
  · simpa only [success] using prepared
  · intro w decided
    exact Typed.fits_of_hasTy_shapeDecides w row.answer decided result _ typed

/-- A cause with no reserved defect satisfies the typed exit judgment's defect exclusion at
every type (`NoShapeDefect` reads exactly `badName` and `notImplemented`). -/
theorem noShapeDefect_of_reservedFree (ty : EffTy) (c : Machine.CauseV)
    (free : c.reasons.any reservedDie = false) : Typed.NoShapeDefect ty (.failure c) := by
  intro reason hmem
  have notAny : ¬ c.reasons.any reservedDie = true := by
    rw [free]
    exact Bool.false_ne_true
  cases reason with
  | die defect _ =>
    show defect ≠ .badName ∧ defect ≠ .notImplemented
    refine ⟨fun h => notAny (List.any_eq_true.mpr ⟨_, hmem, ?_⟩),
      fun h => notAny (List.any_eq_true.mpr ⟨_, hmem, ?_⟩)⟩
    · subst h; rfl
    · subst h; rfl
  | fail _ _ => trivial
  | interrupt _ _ => trivial

/-- **An accepted failing reply has no shape defect** (decisions row 191, `E4-HOST-CE-008`):
executable admission refuses the reserved defects (`admit_failure_reservedFree`), so a
session-accepted failure satisfies `NoShapeDefect` at every type. This is the failure half of
`admit_sound`, executable admission implying the ghost `AnswerOk`; the value half waits on
row 97's handle declarations, and the cause's membership in the error column is
`external_error_typed`. -/
theorem preflight_failure_noShapeDefect {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision) (c : Machine.CauseV)
    (failed : reply.completion = .ofExit (.failure c))
    (accepted : preflight s reply = .ok decision) (ty : EffTy) :
    Typed.NoShapeDefect ty (.failure c) := by
  obtain ⟨bound, _, _, envelope, _⟩ := preflight_envelope s reply decision accepted
  have admitted : admit table s.machine
      (.answerAsync bound.call.fiber bound.token (.ofExit (.failure c))) = none := by
    simpa only [BoundCall.record, failed] using envelope.2.2
  exact noShapeDefect_of_reservedFree ty c
    (admit_failure_reservedFree table s.machine _ _ c admitted)

/-- A received successful completion carries the same exact preparation witness as preflight.
Receipt stores the reply; this theorem neither applies it nor proves the whole machine typed. -/
theorem submit_success_prepared_fits {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (value : Machine.Val)
    (live : s.machine.stuck = none)
    (success : reply.completion = .ofExit (.success value))
    (received : (submit s reply).phase = .preflight) :
    ∃ decision, preflight s reply = .ok decision ∧ PreparedSuccess s reply decision := by
  obtain ⟨_, ⟨decision, accepted⟩, _, _⟩ := submit_conditions s reply received
  exact ⟨decision, accepted, preflight_success_prepared_fits s reply decision value
    live success accepted⟩

end Effect4.Api.HostSession
