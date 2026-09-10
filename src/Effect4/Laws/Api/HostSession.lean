import Effect4.Api.HostSession

/-! Exact protocol claims; these do not establish host execution or whole-machine typing.
The program/table certificate is retained, and the existing envelope is reused verbatim. -/

set_option autoImplicit false
namespace Effect4.Api.HostSession
open Effect4 Effect4.Program

/-- A successful preflight identifies the active association and proves the exact recorded
reply's envelope and returned decision. No consumption or progress follows from this law. -/
theorem preflight_envelope {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : preflight s reply = .ok decision) :
    ∃ bound, s.active = some bound ∧ reply.callId = bound.call.callId ∧
      Envelope table s.machine (bound.record reply) ∧
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
          · rename_i d hd
            cases h
            exact ⟨bound, hbound, by simpa using hid,
              acceptReply_envelope table s.machine (bound.record reply) decision hd,
              acceptReply_decision table s.machine (bound.record reply) decision hd⟩

/-- Zero driver fuel cannot drop a pending reply or mutate execution/ownership ledgers. -/
theorem applyPending_zero {program : Api.Program} {table : RowTable}
    (s : Session program table) : applyPending s 0 = ⟨.frontier, s⟩ := rfl

/-- A malformed completion changes neither execution state nor the protocol ledger. -/
theorem submit_refusal_retains {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (why : Refusal)
    (h : preflight s reply = .error why) : (submit s reply).session = s := by
  unfold submit
  split
  · rfl
  · rw [h]

/-- A direct answer has no route around recorded-reply validation. -/
theorem advance_answer_refuses {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (fiber : FiberId) (token : Nat) (reply : Answer) :
    advance s fuel (.answerAsync fiber token reply) = ⟨.refused .directAnswer, s⟩ := rfl

/-- The old guard is absent after an application classified as applied. This is the
consumption receipt; a command loop's Boolean sufficiency is deliberately not its premise. -/
theorem applied_guard_absent {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (bound : BoundCall)
    (ha : s.active = some bound) (h : (applyPending s fuel).phase = .applied) :
    requestOf (applyPending s fuel).session.machine bound.call.fiber bound.token = none := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases hp : s.pending with
    | none => simp [applyPending, ha, hp] at h
    | some reply =>
      cases hd : preflight s reply with
      | error why => simp [applyPending, ha, hp, hd] at h
      | ok decision =>
        by_cases hu : requestOf (steppedBy program (fuel + 1) table s.machine decision)
            bound.call.fiber bound.token = none
        · simpa [applyPending, ha, hp, hd, hu] using hu
        · simp [applyPending, ha, hp, hd, hu] at h

/-- Once the wrapper reports application, the original reply's existing envelope check
refuses it, independently of session bookkeeping. -/
theorem applied_reply_refused {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (bound : BoundCall) (reply : Reply)
    (ha : s.active = some bound) (h : (applyPending s fuel).phase = .applied) :
    acceptReply table (applyPending s fuel).session.machine (bound.record reply) = none :=
  acceptReply_none_of_unparked table _ _ (applied_guard_absent s fuel bound ha h)

end Effect4.Api.HostSession
