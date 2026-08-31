import Effects.Conformance.Schema.TraceExcludes
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-007 — children upload before parents, the root publishes last

TRACE-EXCLUDES over the remote machine at the decision-tag projection:
the guarded mode is "the pending input is NOT an entitled publish
request" — the identifier is taken, or the root and its declared
closure do not all stand confirmed — and inside it no step ever issues
a publish command; the refusal is the typed ordering refusal with the
state untouched. Server acceptance never implies closure: the
acknowledgment half is the named theorem showing a publish
acknowledgment grows the published set only, while `confirmed` grows
solely at verified upload acknowledgments and verified loads. The
negative kit is an entitled publish of a confirmed root, which does
issue — the gate is not vacuous.
-/

namespace Effects.Conformance

open Effects.Remote

private def confirmedState : MachineState Nat (List UInt8) :=
  { rmtEmpty with
    confirmed := ((∅ : Std.HashSet Nat).insert 2).insert 3 }

/-- RMT-007: no root publish issues before its closure stands
confirmed. -/
def rmt007 : TraceExcludes
    (MachineState Nat (List UInt8) × MInput Nat (List UInt8))
    Unit RTag Bool where
  id := "RMT-007"
  sentence := "When the pending input is not an entitled publish request — the root and every key of its declared closure confirmed by verified acknowledgments or loads, on a free identifier — no step ever issues a publish command: children upload before parents, the root publishes last, the refusal is a typed ordering refusal, and server acceptance of any upload confirms exactly that key, never its children."
  modeOf := fun p => publishRequestEntitled p.1 p.2
  guarded := false
  decisions := fun p _ =>
    ((Effects.Remote.step rmtParams p.1 p.2).decisions).map fun d => d.2.tag
  bad := .issuedPublish
  law := fun p _ h => RMT_007_publish_only_entitled rmtParams p.1 p.2 h
  posState := (rmtEmpty, .request 1 (.publishRoot 2 [3]))
  posInput := ()
  pos_mode := by simp [publishRequestEntitled, publishEntitled, rmtEmpty]
  negState := (confirmedState, .request 1 (.publishRoot 2 [3]))
  negInput := ()
  neg_mode := by
    simp [publishRequestEntitled, publishEntitled, confirmedState, rmtEmpty]
  neg_bad := by
    have hin : confirmedState.inFlight[(1 : OpId)]? = none := by
      simp [confirmedState, rmtEmpty]
    have hent : publishEntitled confirmedState 2 ([3] : List Nat) = true := by
      simp [publishEntitled, confirmedState, rmtEmpty]
    simp [Effects.Remote.step, hin, hent, RDecision.tag]

end Effects.Conformance
