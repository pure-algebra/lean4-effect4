import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-008 — interruption admits nothing

FAIL-CLOSED over the remote machine driven by the interruption event:
the hypothesis is "no operation is in flight under this identifier,"
and when it fails — an operation IS interrupted — the step resolves as
a typed give-up and the admission measure (cache, confirmed,
published) is frozen: no partial node is admitted, no root is
published, and the operation's in-flight entry is cleared, which is
what lets the shell release its resources without semantic residue.
The negative kit is a free identifier, whose interruption is absorbed
without any rejection — the rejection is not universal.
-/

namespace Effects.Conformance

open Effects.Remote

private def interruptLoading : MachineState Nat (List UInt8) :=
  { rmtEmpty with
    inFlight := (∅ : Std.HashMap OpId _).insert 1 (.loading 2) }

/-- RMT-008: at any interruption point, nothing partial is admitted
and no root publishes. -/
def rmt008 : FailClosed (MachineState Nat (List UInt8)) OpId
    (MResult Nat (List UInt8)) where
  id := "RMT-008"
  sentence := "When an interruption arrives for an operation in flight, the step resolves as a typed give-up with the cache, confirmed, and published sets exactly as they were — no partial node is admitted, no root is published, and the in-flight entry is cleared so resources release without semantic residue."
  wf := fun _ => True
  hyp := fun s id => s.inFlight[id]? = none
  step := fun s id =>
    ((Effects.Remote.step rmtParams s (.fromWire id .interrupted)).result,
      (Effects.Remote.step rmtParams s (.fromWire id .interrupted)).state)
  isRejection := fun r =>
    match r with
    | .transportFailed _ => true
    | .batchFailed => true
    | .publishFailed _ => true
    | _ => false
  measure := fun s => s.cache.size + s.confirmed.size + s.published.size
  law_reject := fun s id _ hn => by
    match hst : s.inFlight[id]? with
    | none => exact absurd hst hn
    | some st =>
      cases st <;>
        simp [Effects.Remote.step, hst, loadEvent, uploadEvent,
          batchEvent, publishEvent]
  law_frozen := fun s id _ hn => by
    match hst : s.inFlight[id]? with
    | none => exact absurd hst hn
    | some st =>
      obtain ⟨hc, hcf, hp, -, -⟩ :=
        RMT_008_interrupt_admits_nothing rmtParams s id st hst
      simp only [hc, hcf, hp]
  posState := interruptLoading
  posInput := 1
  pos_wf := trivial
  pos_nohyp := by simp [interruptLoading]
  negState := rmtEmpty
  negInput := 1
  neg_hyp := by simp [rmtEmpty]

end Effects.Conformance
