import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-006 — batch accounting fails closed

FAIL-CLOSED over the remote machine with a find-missing operation in
flight: the hypothesis is exact per-key accounting — the results
answer the requested keys one for one, in request order — and when it
fails the whole batch is rejected with the typed result and the
admission measure (cache, confirmed, published) frozen: no per-key
answer is partially applied and nothing substitutes across keys. The
negative kit is an exactly-accounted response, which is answered —
rejection is not universal.
-/

namespace Effects.Conformance

open Effects.Remote

private def batchState' : MachineState Nat (List UInt8) :=
  { rmtEmpty with
    inFlight := (∅ : Std.HashMap OpId _).insert 1 (.findingMissing [2, 3]) }

/-- RMT-006: a batch response accounts for every requested key or the
batch fails closed. -/
def rmt006 : FailClosed (MachineState Nat (List UInt8))
    (List (KeyStatus Nat (List UInt8))) (MResult Nat (List UInt8)) where
  id := "RMT-006"
  sentence := "When a batch response fails exact per-key accounting — every requested key answered once, in request order, nothing extra — the whole batch is rejected with the typed batch rejection and the cache, confirmed, and published sets stay exactly as they were: no per-key answer is partially applied and no answer substitutes across keys."
  wf := fun s => s.inFlight[1]? = some (.findingMissing [2, 3])
  hyp := fun _ results => accountsFor [2, 3] results = true
  step := fun s results =>
    ((Effects.Remote.step rmtParams s (.fromWire 1 (.batchResult results))).result,
      (Effects.Remote.step rmtParams s (.fromWire 1 (.batchResult results))).state)
  isRejection := fun r => decide (r = .batchRejected)
  measure := fun s => s.cache.size + s.confirmed.size + s.published.size
  law_reject := fun s results hwf hn => by
    have hacc : accountsFor (K := Nat) (B := List UInt8) [2, 3] results = false := by
      simpa using hn
    rw [RMT_006_batch_fail_closed rmtParams s 1 [2, 3] results hwf hacc]
    simp
  law_frozen := fun s results hwf hn => by
    have hacc : accountsFor (K := Nat) (B := List UInt8) [2, 3] results = false := by
      simpa using hn
    rw [RMT_006_batch_fail_closed rmtParams s 1 [2, 3] results hwf hacc]
  posState := batchState'
  posInput := [.missing 9]
  pos_wf := by simp [batchState']
  pos_nohyp := by decide
  negState := batchState'
  negInput := [.missing 2, .missing 3]
  neg_hyp := by decide

end Effects.Conformance
