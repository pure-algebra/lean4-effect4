# Contract packets

Every semantic implementation slice begins with a breaker-authored packet in
this directory. A packet states its algebraic laws, preconditions,
postconditions, decrease arguments, frame, executable falsifiers, and the
counterexample rows it exercises. The breaker commits the packet and red
battery before the builder changes the implementation.

Packets of a second kind describe integration claims and say so in their own introductions:
`faces.contract.md` (DI-50) states what the nine representations of one `Eff`
program claim about each other, with the evidence word of each claim, the side
conditions of the two round-trip theorems, and the quantifiers on the truth
harness's differential. It adds no battery — it names the ones that exist — so
it is a statement of the layer's claims, not a red battery a builder turns
green.

`foundation-wave2.contract.md` freezes the owner-approved cross-slice amendments to the
existing model, target and compatibility contracts. Its per-slice proof graphs and independent
controls are retained in the delivery records; the amendment text is not a passing battery.
