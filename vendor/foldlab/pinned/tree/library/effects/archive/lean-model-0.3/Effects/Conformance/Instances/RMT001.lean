import Effects.Conformance.Schema.TraceExcludes
import Effects.Conformance.Rider
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-001 — nothing reaches the cache or the caller without admission

TRACE-EXCLUDES over the remote client machine at the decision-tag
projection, with the state paired with its pending input so the guard
can read both: the guarded mode is "not entitled" — the pending event
does not answer an in-flight operation with bytes that pass the budget
and verify for its key — and the excluded decision is the cache tag.
The backing theorem is the conjunction covering both halves of the
obligation: neither `cached` nor `returned` (the caller's mirror of
delivery) is reachable without entitlement; the instance's `bad` is the
cache tag, and the return half is carried structurally by the sentence
rider below, beside the mutant and the vectors. The negative kit is an
entitled load response, which does cache — the guard is not vacuous.
-/

namespace Effects.Conformance

open Effects.Remote

private abbrev StI :=
  MachineState Nat (List UInt8) × MInput Nat (List UInt8)

private def loading2 : MachineState Nat (List UInt8) :=
  { rmtEmpty with inFlight := (∅ : Std.HashMap OpId _).insert 1 (.loading 2) }

/-- RMT-001: no remote-loaded node reaches the cache or the caller
without passing standard admission. -/
def rmt001 : TraceExcludes StI Unit RTag Bool where
  id := "RMT-001"
  sentence := "When the pending input is not entitled — its bytes do not answer an in-flight operation, pass the declared budget, and verify for that operation's key — no step ever emits a cache decision or a return to the caller: a wire-supplied digest is a routing hint, never an identity, and only verification admits a remote-loaded node in either direction."
  modeOf := fun p => entitledToCache rmtParams p.1 p.2
  guarded := false
  decisions := fun p _ =>
    ((Effects.Remote.step rmtParams p.1 p.2).decisions).map fun d => d.2.tag
  bad := .cached
  law := fun p _ h =>
    (RMT_001_no_cache_or_return_without_admission rmtParams p.1 p.2 h).1
  posState := (loading2, .fromWire 1 (.ok 2 [7]))
  posInput := ()
  pos_mode := by simp [entitledToCache, loading2, rmtEmpty, rmtParams]
  negState := (loading2, .fromWire 1 (.ok 2 [7, 9]))
  negInput := ()
  neg_mode := by simp [entitledToCache, loading2, rmtEmpty, rmtParams]
  neg_bad := by simp [Effects.Remote.step, loading2, rmtEmpty, rmtParams,
    loadEvent, RDecision.tag]

/-- The sentence's return half: `bad` carries the cache tag, and the
same admission theorem's second conjunct excludes the caller's mirror. -/
def rmt001ReturnRider : SentenceRider :=
  .of "RMT-001"
    "no step ever emits a return to the caller without entitlement"
    (fun (s : MachineState Nat (List UInt8)) (i : MInput Nat (List UInt8))
        (h : entitledToCache rmtParams s i = false) =>
      (RMT_001_no_cache_or_return_without_admission rmtParams s i h).2)

end Effects.Conformance
