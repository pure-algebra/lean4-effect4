import Effects.Remote.Machine

/-!
# The shared remote kit environment

The concrete machine environment every remote instance's kit runs in,
extracted from the first remote instance so the instance files import
this peer directly instead of chaining through one another: byte
budget eight, key budget four, a key verified exactly when it equals
the content length — the abstract verification oracle at its simplest
honest instantiation. The vector families use the canonical-bytes
toy-digest oracle instead; the tie to the full CAS admission judgment
is the refinement obligation's.
-/

namespace Effects.Conformance

open Effects.Remote

/-- Concrete machine environment for the remote kits. -/
def rmtParams : Params Nat (List UInt8) :=
  { budgets := ⟨8, 4⟩
    size := List.length
    verify := fun k b => b.length == k }

/-- The machine state with nothing in flight, cached, or rejected. -/
def rmtEmpty : MachineState Nat (List UInt8) :=
  { inFlight := ∅, cache := ∅, rejected := ∅, reportedPresent := ∅
    reportedMissing := ∅, confirmed := ∅, published := ∅ }

end Effects.Conformance
