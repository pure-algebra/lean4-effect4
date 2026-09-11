import Effect4.Api.HostSession

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
    preflight { s with pending := slots } reply = preflight s reply := rfl

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
    (s : Session program table) : applyPending s 0 = ⟨.frontier, s⟩ := rfl

theorem applyReply_zero {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) : applyReply s key 0 = ⟨.frontier, s⟩ := rfl

theorem advance_answer_refuses {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (fiber : FiberId) (token : Nat) (reply : Answer) :
    advance s fuel (.answerAsync fiber token reply) = ⟨.refused .directAnswer, s⟩ := rfl

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

end Effect4.Api.HostSession
