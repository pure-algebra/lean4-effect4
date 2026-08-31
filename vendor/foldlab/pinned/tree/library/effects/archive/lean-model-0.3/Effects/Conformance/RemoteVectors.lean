import Effects.Conformance.Manifest
import Effects.Remote.Machine

/-!
# The remote vector environment

The shared carrier for every remote schedule family and for the
instances that must speak about it: full-width addresses under the
declared toy digest, canonical admitted-node byte fixtures from the
ratified CAS codec, and the machine environment the vectors run in.
Extracted from the family emitter at R2 so the AGREEMENT instance can
state the machine-to-store tie without importing the emitter.
-/

namespace Effects.Conformance.Manifest

open Effects.Remote Effects.Cas

instance : Hashable Addr32 := ⟨fun a => hash a.val⟩

abbrev RSt := MachineState Addr32 Bytes
abbrev RIn := MInput Addr32 Bytes
abbrev RStep := RSt → RIn → Effects.Remote.StepOut Addr32 Bytes

/-- The declared toy digest: a 32-lane byte fold over the input — not
cryptographic, deliberately, per the abstract-hash posture. -/
def toyAddr (bs : Bytes) : Addr32 :=
  ⟨(List.range 32).map fun i =>
      UInt8.ofNat ((bs.foldl (fun a b => a + b.toNat * (i + 3))
        (i + bs.length)) % 256),
    by simp⟩

/-- The vector environment: byte budget forty (the small canonical
encodings fit; the two-reference encoding cannot), sizes by length, and
verification recomputing the toy digest over received bytes. -/
def vecParams : Params Addr32 Bytes :=
  { budgets := ⟨40, 4⟩
    size := List.length
    verify := fun k b => decide (toyAddr b = k) }

/-- The machine state with nothing in flight, cached, or rejected. -/
def vecEmpty : RSt :=
  { inFlight := ∅, cache := ∅, rejected := ∅, reportedPresent := ∅
    reportedMissing := ∅, confirmed := ∅, published := ∅ }

/-! ## Canonical-byte fixtures (from the ratified CAS codec) -/

def smallBytes : Bytes := encodeAdmitted cas001PosNode
def goodBytes : Bytes := encodeAdmitted payloadNode
def bigBytes : Bytes := encodeAdmitted multiRefNode

def kGood : Addr32 := toyAddr goodBytes
def kSmall : Addr32 := toyAddr smallBytes
def kBig : Addr32 := toyAddr bigBytes

end Effects.Conformance.Manifest
