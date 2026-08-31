import Effects.Conformance.Schema.ExactStep
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-004 — an already-present exact-digest upload transfers nothing

EXACT-STEP over the remote client machine with the state paired with
its accumulated command stream, so the measured quantity is the number
of wire commands issued. Under the dedup hypothesis — the request
uploads a key already admitted in the cache with content that verifies,
within budget, not integrity-rejected, on a free identifier — one step
changes the issued-command count by exactly zero, backed by the named
full-output law: the step resolves as success with the state unchanged
and only the verification decision. The negative kit is the same upload
against an empty cache — a fresh upload, where the hypothesis fails and
a transfer is exactly what must happen.
-/

namespace Effects.Conformance

open Effects.Remote

private abbrev StC :=
  MachineState Nat (List UInt8) × List (OpId × Command Nat (List UInt8))

/-- The command-accumulating step: run the machine, append its issued
commands. -/
private def stepC (p : StC) (i : MInput Nat (List UInt8)) : StC :=
  let o := Effects.Remote.step rmtParams p.1 i
  (o.state, p.2 ++ o.commands)

/-- The kit state with key 2 already admitted in the cache. -/
private def cached2 : MachineState Nat (List UInt8) :=
  { rmtEmpty with cache := (∅ : Std.HashSet Nat).insert 2 }

/-- RMT-004: an already-present exact-digest upload resolves as success
with zero additional transfer commands. -/
def rmt004 : ExactStep StC (MInput Nat (List UInt8)) where
  id := "RMT-004"
  sentence := "When an upload request names a key already admitted in the cache with content that verifies for it — within the byte budget, not integrity-rejected, its identifier free — one machine step changes the issued-command count by exactly zero: an already-present exact-digest upload resolves as success with no transfer, and duplicate content never becomes duplicate wire traffic."
  wf := fun _ => True
  hyp := fun p i =>
    match i with
    | .request id (.upload key bytes) =>
        p.1.inFlight[id]? = none ∧
        p.1.cache.contains key = true ∧
        ¬ rmtParams.size bytes > rmtParams.budgets.maxBytes ∧
        p.1.rejected.contains (key, bytes) = false ∧
        rmtParams.verify key bytes = true
    | _ => False
  step := stepC
  measure := fun p => p.2.length
  delta := 0
  law := fun p i _ h => by
    match i, h with
    | .request id (.upload key bytes),
      ⟨hflight, hcache, hsize, hrej, hver⟩ =>
      simp [stepC, RMT_004_present_upload_needs_no_transfer rmtParams p.1
        id key bytes hflight hsize hrej hver hcache]
  posState := (cached2, [])
  posInput := .request 1 (.upload 2 [7, 7])
  pos_wf := trivial
  pos_hyp := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [cached2, rmtEmpty, rmtParams]
  negState := (rmtEmpty, [])
  negInput := .request 1 (.upload 2 [7, 7])
  neg_hyp := by
    intro h
    exact absurd h.2.1 (by simp [rmtEmpty])

end Effects.Conformance
