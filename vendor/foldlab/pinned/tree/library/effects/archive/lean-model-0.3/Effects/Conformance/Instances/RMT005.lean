import Effects.Conformance.Schema.TraceExcludes
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-005 — presence is planning, never admission

TRACE-EXCLUDES over the remote machine at the decision-tag projection,
state paired with pending input: the guarded mode is "the input answers
an in-flight find-missing operation," and inside it the cache decision
never occurs — the backing theorem also excludes returns and publish
issuance and freezes the cache, confirmed, and published components,
so a presence answer (even one carrying bytes) can neither admit,
deliver, nor publish. Negative semantic caching does not exist at all:
the reported-missing set is planning data with no admission reading.
The negative kit is an entitled load delivery, which does cache — the
mode guard is not vacuous.
-/

namespace Effects.Conformance

open Effects.Remote

/-- Whether the pending input answers an in-flight find-missing. -/
def batchAnswering (s : MachineState Nat (List UInt8))
    (i : MInput Nat (List UInt8)) : Bool :=
  match i with
  | .fromWire id _ =>
    match s.inFlight[id]? with
    | some (.findingMissing _) => true
    | _ => false
  | _ => false

private def batchState : MachineState Nat (List UInt8) :=
  { rmtEmpty with
    inFlight := (∅ : Std.HashMap OpId _).insert 1 (.findingMissing [2, 3]) }

private def loadingState : MachineState Nat (List UInt8) :=
  { rmtEmpty with
    inFlight := (∅ : Std.HashMap OpId _).insert 1 (.loading 2) }

/-- RMT-005: no admission or publication decision is taken on a
presence answer alone. -/
def rmt005 : TraceExcludes
    (MachineState Nat (List UInt8) × MInput Nat (List UInt8))
    Unit RTag Bool where
  id := "RMT-005"
  sentence := "When the pending input answers an in-flight find-missing operation, no step ever caches: a presence answer is planning data that steers upload scheduling and nothing else — it admits nothing, returns nothing, publishes nothing, and absence is never negatively cached, because no admission reading of the reported-missing set exists at all."
  modeOf := fun p => batchAnswering p.1 p.2
  guarded := true
  decisions := fun p _ =>
    ((Effects.Remote.step rmtParams p.1 p.2).decisions).map fun d => d.2.tag
  bad := .cached
  law := fun p _ h => by
    match p, h with
    | (s, .fromWire id e), h =>
      match hm : s.inFlight[id]? with
      | some (.findingMissing keys) =>
        exact (RMT_005_presence_never_admits rmtParams s id keys e
          hm).2.2.2.1
      | some (.loading key) => simp [batchAnswering, hm] at h
      | some (.uploading key bytes) => simp [batchAnswering, hm] at h
      | some (.publishing key) => simp [batchAnswering, hm] at h
      | none => simp [batchAnswering, hm] at h
    | (s, .request id op), h => simp [batchAnswering] at h
  posState := (batchState, .fromWire 1 (.batchResult [.missing 2, .missing 3]))
  posInput := ()
  pos_mode := by simp [batchAnswering, batchState]
  negState := (loadingState, .fromWire 1 (.ok 2 [7, 7]))
  negInput := ()
  neg_mode := by simp [batchAnswering, loadingState]
  neg_bad := by
    simp [Effects.Remote.step, loadingState, rmtEmpty, rmtParams,
      loadEvent, RDecision.tag]

end Effects.Conformance
