import Cas.Backend.Universal

/-!
Effect Core v1 — exact axiom receipt for the inherited fixed-fuel boundary.

This file introduces no declaration. It imports the canonical theorem owner
and prints the two receipts cited by `EC1-CE002`.

Run from `library/cas`:

  lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/FixedFuel.lean
-/

#print axioms Cas.Lang.run_has_no_composition_law
#print axioms Cas.Lang.run_composite_outruns_its_parts
