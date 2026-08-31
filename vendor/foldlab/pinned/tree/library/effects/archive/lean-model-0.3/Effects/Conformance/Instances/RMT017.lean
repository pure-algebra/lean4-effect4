import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Rider
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-017 — attested presence confirms for publish

FAIL-CLOSED over the machine's wire-less attest step: the hypothesis is
the full attestation entitlement — the bytes verify locally AND the peer
reported the key present. When either half fails the step refuses with a
typed result and the confirmed count is unchanged; downloading the node
instead would prove only that the peer held it at confirmation time,
which is the same retention exposure the presence claim already carries.
The kit's positive case attests without any presence report; the
negative case attests a reported-present key whose bytes verify. The
sentence's confirmation and cache-non-admission conjuncts are carried
structurally by the riders below.
-/

namespace Effects.Conformance

open Effects.Remote

private abbrev St := MachineState Nat (List UInt8)
private abbrev AttestIn := Nat × List UInt8

private def attestStep (s : St) (i : AttestIn) :
    MResult Nat (List UInt8) × St :=
  let o := Effects.Remote.step rmtParams s (.request 1 (.attest i.1 i.2))
  (o.result, o.state)

private def isAttestRefusal : MResult Nat (List UInt8) → Bool
  | .attestRefused _ => true
  | _ => false

private def presentState : St :=
  { rmtEmpty with reportedPresent := (∅ : Std.HashSet Nat).insert 3 }

/-- RMT-017: unsolicited attestation fails closed. -/
def rmt017 : FailClosed St AttestIn (MResult Nat (List UInt8)) where
  id := "RMT-017"
  sentence := "When an attestation is not entitled — the peer never reported the key present, or the held bytes fail local verification — the step refuses with a typed result and the confirmed count is unchanged; an entitled attestation confirms the key for publication without admitting anything to the cache."
  wf := fun s => s.inFlight[1]? = none
  hyp := fun s i =>
    rmtParams.verify i.1 i.2 = true ∧ s.reportedPresent.contains i.1 = true
  step := attestStep
  isRejection := isAttestRefusal
  measure := fun s => s.confirmed.size
  law_reject := fun s i hwf hn => by
    by_cases hv : rmtParams.verify i.1 i.2 = true
    · have hp : s.reportedPresent.contains i.1 = false := by
        by_cases hp' : s.reportedPresent.contains i.1 = true
        · exact absurd ⟨hv, hp'⟩ hn
        · simpa using hp'
      simp [attestStep,
        RMT_017_attest_refused_without_presence rmtParams s 1 i.1 i.2 hwf hp,
        isAttestRefusal]
    · have hv' : rmtParams.verify i.1 i.2 = false := by simpa using hv
      simp [attestStep,
        RMT_017_attest_refused_without_verification rmtParams s 1 i.1 i.2 hwf hv',
        isAttestRefusal]
  law_frozen := fun s i hwf hn => by
    by_cases hv : rmtParams.verify i.1 i.2 = true
    · have hp : s.reportedPresent.contains i.1 = false := by
        by_cases hp' : s.reportedPresent.contains i.1 = true
        · exact absurd ⟨hv, hp'⟩ hn
        · simpa using hp'
      simp [attestStep,
        RMT_017_attest_refused_without_presence rmtParams s 1 i.1 i.2 hwf hp]
    · have hv' : rmtParams.verify i.1 i.2 = false := by simpa using hv
      simp [attestStep,
        RMT_017_attest_refused_without_verification rmtParams s 1 i.1 i.2 hwf hv']
  posState := rmtEmpty
  posInput := (3, [1, 2, 3])
  pos_wf := by simp [rmtEmpty]
  pos_nohyp := fun h => by simp [rmtEmpty] at h
  negState := presentState
  negInput := (3, [1, 2, 3])
  neg_hyp := ⟨rfl, by simp [presentState]⟩

/-- The entitled direction: verified bytes plus a presence report step
to exactly the confirmed-and-attested machine state. -/
def rmt017ConfirmsRider : SentenceRider :=
  .of "RMT-017"
    "an entitled attestation confirms the key for publication"
    (@RMT_017_attest_confirms)

/-- Presence stays non-admission for reads: attestation never touches
the cache, entitled or not. -/
def rmt017CacheRider : SentenceRider :=
  .of "RMT-017" "without admitting anything to the cache"
    (@RMT_017_attest_never_caches)

end Effects.Conformance
