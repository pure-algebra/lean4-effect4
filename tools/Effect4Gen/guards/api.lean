/-! P2b carrier acceptance: round trips, exact decoding and generated shapes. -/
namespace ApiAcceptance
open Effect4 Effect4.Machine Effect4.Api

def fibers : List FiberId := [⟨0⟩, ⟨1⟩, ⟨37⟩]
def keys : List HostProtocol.Key := [⟨⟨0⟩, 0⟩, ⟨⟨1⟩, 7⟩]
def exhaustion : List Exhaustion := [.fuel, .tape]
def reasons : List FrontierReason :=
  [.commandFuel, .compileFuel ⟨0⟩, .awaitHost ⟨⟨1⟩, 7⟩, .awaitTimer ⟨2⟩ 19, .awaitDecision]

#guard fibers.all fun x => Canonical.decode (α := FiberId) (Canonical.encode x) = some x
#guard keys.all fun x => Canonical.decode (α := HostProtocol.Key) (Canonical.encode x) = some x
#guard exhaustion.all fun x => Canonical.decode (α := Exhaustion) (Canonical.encode x) = some x
#guard reasons.all fun x => Canonical.decode (α := FrontierReason) (Canonical.encode x) = some x
#guard reasons.all fun x => Canonical.decode (α := FrontierReason) (Canonical.encode x ++ [0]) = none
#guard reasons.all fun x => (Canonical.shape FrontierReason).accepts (Canonical.toVal x)
#guard Canonical.decode (α := Exhaustion) [] = none
#guard Canonical.decode (α := HostProtocol.Key) [] = none

end ApiAcceptance
