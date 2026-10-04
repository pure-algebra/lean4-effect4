# Record term proof integration

The term proofs and focused record fixture pass their Lean checks.
The native typing checkpoint is `7d6fe00d`.

Base: `fc83e7d3`, including the checked source dependencies from the other seats.
The commit containing this receipt supplies its head.

## Placement

Concepts: Store Typing & Value Membership and Residual Program Typing (`docs/core/semantics.md`).
Role: helpers for registry claim `denote-typed` and the existing native term contracts.
Requirement: R3, on the M5 path.

`evalTerm_fitsAll` and `evalTerm_progress` retain their world membership premises.
The first retains actual successful evaluation as a premise.
The second supplies the returned value for a term admitted by the type checker.
Neither theorem states whole-program termination or eventual external replies.
Their owner is the existing term semantics.

Concept: Reactive Scheduling & Machine Invariants.
Role: value-operation helpers for handle registration and the native value invariant.
Requirement: R4, on the value side of the M5 to M6 path.

`RecordHandles.build`, `RecordHandles.read`, and `RecordHandles.set` retain only raw handles from their inputs.
The raw observation includes unknown kind bytes and every allocation index.
`evalTerm_keys` and `RawHandles.evalTerm_handles` consume those helpers for the new syntax.
`RawHandles.evalTerm_registered` remains their conditional registration consumer.
`evalTerm_validIn` derives store validity from raw handle containment and its valid-environment premise.
Containment alone establishes neither registration nor allocation validity.

The host boundary remains in `docs/core/host-boundary.md`.
No target execution claim follows from these term proofs.

## Files

- `src/Effect4/Laws/Program/Typed.lean` proves named pairing directly, avoiding a broad machine-proof import.
- `src/Effect4/Laws/Program/Typed/RecordOperations.lean` owns the term-membership mutual block after the operation bridges.
- `src/Effect4/Laws/Program/Typed/Membership.lean` retains the value-membership theory.
- `src/Effect4/Laws/Program/Typed/Admission.lean` imports the new owner of `evalTerm_fitsAll`.
- `src/Effect4/Laws/Program/Typed/Denotation.lean` connects the new term constructors to world membership and evaluation.
- `src/Effect4/Laws/Program/Handles/Term.lean` checks raw handles and decoded keys.
- `src/Effect4/Laws/Program/MeaningSound.lean` consumes raw handle containment for store validity.
- `Test/Program/RecordOperations.lean` checks examples and queries theorem axioms.

## Statement and dependency checks

A source comparison checks 15 existing theorem headers against `82d34358`.
Every compared header remains unchanged.
The source import check finds no cycle in the 198 reachable modules of the three consumer roots.

The compared declarations include both forms of term typing and evaluation.
They include world progress, keys, raw handles, registration, and store validity.
The roots are `RecordOperations`, `Typed.Denotation`, and `MeaningSound` under `Effect4.Laws.Program`.

## Checks

The focused integration checks compile `RecordOperations`, `Handles.Term`, `Typed.Denotation`, and `MeaningSound`.
The final denotation command reports `Build completed successfully (395 jobs)`:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Denotation
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/RecordOperations.lean
```

The fixture passes its empty construction, required read, absent optional read, overwrite, and unknown-kind raw handle controls.
All 34 axiom queries report subsets of `[propext, Quot.sound]`.
These queries cover native typing, world membership, term evaluation, keys, raw handles, registration, and store validity.
The controls remain finite evidence about the listed values.
The queried theorems retain their universal statements and existing premises.

`external_arm` also reads the revised `rowTy` result through `rowTy_instantiated_formed`.
Successful typing discharges the formation guard without a new premise.

The integration reveals a concrete `fold_of` failure in `Membership.lean`.
The new metadata imports expose both `Store.Val` and `Ty` as generated families.
The old first-argument selection chooses `Store.Val`, although `itemFitters` only traverses types.
The separate fold-family receipt records the inference repair and its consumer checks.

No full battery, host compiler, or runtime comparison runs in this proof slice.
