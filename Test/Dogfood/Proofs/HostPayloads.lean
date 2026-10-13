import Effect4.Laws.Run.Payload

/-!
# Exact receipt payloads at reply application: the applied bodies

Placement: `host-session-protocol`, R6, a step of `stale_never_applies` clause four.
The consumer is the timeout body's value-flow invariant through `application_body`.
The payload ledger and `application_payload` moved into the law graph on 2026-10-13
(`src/Effect4/Laws/Run/Payload.lean`), where the typed replay's law reads them too. This module
names them under its own namespace for its readers, and keeps the applied bodies.
The reach includes every recorded run, table, budget and raw command.
This ledger does not establish the origin of a program's returned value.
It establishes neither progress nor a host implementation's behavior.
-/

set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostPayloads
open Effect4 Effect4.Machine Effect4.Program Effect4.Run
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

export Effect4.Run (acceptedReplies PendingFrom PayloadLedger acceptedReplies_step payload_step
  payload_open payload_reached readReply_from application_payload)

/-- Successful receipts whose own keys have an actual application in this journal prefix. -/
def appliedBodies (s : Run) : List Val :=
  (acceptedReplies s).filterMap fun reply =>
    if reply.key ∈ appliedKeys s then
      match reply.completion with
      | .ofExit (.success body) => some body
      | _ => none
    else none

/-- Enlarging the receipt and application prefixes retains every applied body. -/
theorem appliedBodies_mono (s t : Run)
    (receipts : acceptedReplies s ⊆ acceptedReplies t)
    (keys : appliedKeys s ⊆ appliedKeys t) : appliedBodies s ⊆ appliedBodies t := by
  intro body member
  obtain ⟨reply, hr, hb⟩ := List.mem_filterMap.mp member
  refine List.mem_filterMap.mpr ⟨reply, receipts hr, ?_⟩
  split at hb
  · rename_i applied
    rw [if_pos (keys applied)]
    exact hb
  · cases hb

/-- Every recorded row retains the current prefix's applied successful bodies. -/
theorem appliedBodies_step (s : Run) (reached : Run.Reached s) (c : Command) :
    appliedBodies s ⊆ appliedBodies (s.step c) := by
  have len := (payload_reached s reached).1
  apply appliedBodies_mono
  · rw [acceptedReplies_step s c len]
    exact List.subset_append_left _ _
  · rw [appliedKeys_step s c len]
    exact List.subset_append_left _ _

/-- An actual successful application adds its exact receipt body to the applied-body prefix.
The source-flow invariant uses this set, which excludes every receipt without an application. -/
theorem application_body (s : Run) (reached : Run.Reached s) (key : Key)
    (applied : (Api.Runner.result s.runner (.apply key)).phase = .applied)
    (body : Val) (read : (readReply s.session.pending key).map (·.completion) =
      some (.ofExit (.success body))) : body ∈ appliedBodies (s.step (.apply key)) := by
  obtain ⟨reply, _, member, same, selected, _, _, _⟩ :=
    application_payload s reached key applied
  rw [selected, Option.map_some] at read
  have completion := Option.some.inj read
  have len := (payload_reached s reached).1
  unfold appliedBodies
  rw [acceptedReplies_step s (.apply key) len, List.append_nil]
  refine List.mem_filterMap.mpr ⟨reply, member, ?_⟩
  rw [appliedKeys_step s (.apply key) len, applied]
  change (if reply.key ∈ appliedKeys s ++ [key] then _ else none) = some body
  have hkey : reply.key ∈ appliedKeys s ++ [key] := by
    rw [same]
    exact List.mem_append_right _ (List.mem_singleton_self key)
  rw [if_pos hkey, completion]

end Test.Dogfood.Proofs.HostPayloads
