# Checked multiplication judgment

Keep the existing integer addition claim and its statement unchanged.
Add `profile-mul-exact` as the multiplication compatibility claim under translation-simulation, R8.
Its pointer is `mulIn_eq_some_iff` in `src/Effect4/Laws/Machine/IntegerProfile.lean`.

The proof-side function `scaleIn` tests a quotient before multiplying.
It returns exactly the natural product when that product lies within the supplied bound.
Its zero branch avoids division by zero.
`scaleIn_eq_some_iff` connects that precondition to the exact reference product.
`mulIn_eq_some_iff` reads the represented `NativeAtom.mul` operation through that connection.

This extends the existing profile judgment; it adds no program syntax or evaluator.
The claim serves the numeric target boundary of M7 and requirement R8.
It proves no correspondence with OCaml or JavaScript execution.
Those rows remain trusted implementations with finite boundary controls.
The target still requires representable natural arguments at its incoming-value boundary.

Build the changed law module and its concrete reader.
Audit both modules with `#axiom_audit`.
Retain controls for zero, the largest admitted product, and the first refused product.
Regenerate the TypeScript prelude and OCaml outputs from their owners.
Run reached behavior comparisons at the planned sweep.
