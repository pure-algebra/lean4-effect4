# Multiplication within the numeric profile

The shared multiplication judgment and its actual atom reader compile and pass the axiom audit.
This proof does not establish the target implementations' behavior.

## Placement

Concept: translation-simulation, R8.
Question: `profile-mul-exact`, a compatibility claim in `tools/ProofGraph/Registry.lean`.
Pointer: `mulIn_eq_some_iff` in `src/Effect4/Laws/Machine/IntegerProfile.lean`.
Consumer: the represented multiplication's numeric boundary in M7.
Reach: natural operands, any natural bound, and the actual `NativeAtom.mul` result.
The target still needs representable inputs; the target rows remain trusted implementations with finite controls.
This proof establishes neither host admission nor whole-program agreement.

## Change

`scaleIn` checks a quotient before computing the product, with a separate zero branch.
`scaleIn_eq_some_iff` proves that this precondition admits exactly products within the bound.
`mulIn_eq_some_iff` connects it to the existing represented atom.
The existing addition judgment and its compatibility claim remain unchanged.
No program syntax or executable machine definition changes.

The reader applies the law at the declared profile's largest product.
Controls retain zero, the first outside product, and the rounding counterexample's exact reference product.

## Evidence

Base: `f41efe42c`.
`MultiplicationLawEvidence.json` records the changed paths and hashes.

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.IntegerProfile Test.Machine.NaturalProfile ProofGraph.Registry
LEAN_NUM_THREADS=1 lake env lean /private/tmp/ProfileScaleLawAudit.lean
git diff --check
```

The final build passes with 67 jobs.
The audit checks 94 declarations within `[propext, Quot.sound]`, with no planned goals or dependencies on them.
The first build identifies the reader's missing explicit profile import.
The second build includes that import and passes the same targets.
The retained build and audit files contain the results.

## Remaining work

The exact reference multiplication mark, checked target row, and generated outputs land in the accompanying numeric repair.
The TypeScript and OCaml implementations require their finite boundary controls and the reached behavior sweep.
The original application obligations remain open.
