# Shared fragment classification receipt

The cleanup retains the public predicates and existing proof bodies.
It changes no active host-call or session proof file.
The integration base is `1f4ee194deef717a374e348c3bf42fbeebe44d80`.
The branch is `codex/fragment-classification`.

## Implementation

`tools/Effect4Gen/Fragments.lean` owns one constructor classification table.
It reads constructor arguments through `LayerView.readBlock` in `tools/Effect4Gen/LayerView.lean`.
The existing manifest driver generates direct recursive predicates.
Their early rejection and conjunction order remain unchanged.
Their existing `fold_of` connections remain unchanged.

The generated predicates live in `src/Effect4/Program/Fragment.lean` and `src/Effect4/Laws/Program/Fragment{Looped,Rows}.lean`.
`Looped` and `StraightRows` keep their placement outside the core import graph, as decisions row 59 requires.
`dataRow` moves unchanged to `src/Effect4/Laws/Program/FragmentRowAdmission.lean`.
`Test/Program/FragmentCensusContract.lean` uses the generated constructor inventory, including definition blocks.
It checks each visited child position and the differing operation, loop, and conditional-handler rules.

## Proof placement and evidence

`PLAN.md` places the obligations before implementation.
`Baseline.lean` retains independent definitions from the integration base.
Its equality proofs compare the generated algebras through the existing fold uniqueness theorem.
They quantify over every program and, for the row fragment, every row table.
`baseline.log` records their axiom dependencies.
`Boundary.lean` checks the core import graph.
It requires `Straight` and refuses the presence of the three declarations used only by proofs.
The allowed dependencies are `propext` and `Quot.sound`.

The helpers serve `hom-eq-cata-eff` and the premises of `run-eq-meaning`, `loop-agreement`, and `rows-denotation-session`.
Their role is compatibility evidence.
Their observation is the fragment predicate's Boolean answer.
They establish no additional execution or host claim.

`verification.json` records commands, results, and changed-file hashes.
`verification-build-green.log` records the focused build.
`cases.log` records the constructor-policy gate.
The focused gate runs through `scripts/check-conform.py cases`, including its declared build prerequisites.
The earlier `make check-cases` attempt stopped when its prerequisite started the default build.
The interrupted build supplies no verification claim.
The receipt reports focused checks only.
`verify_codegen.py` reuses manifest commands and checks all three owned outputs against fresh generation.
`codegen-check.json` records the byte comparisons.

## Refusal scope

The generator rejects missing, duplicate, and obsolete constructor classifications.
It rejects recursive children in accepted leaves and unsupported child families in recursive rules.
Operation rules require an operation field and a request field.
It does not reject every change to constructor arguments whose sorts are already known.
The existing program typing and execution obligations remain separate.

## Separate generated drift

The required derived generation run also changes `src/Effect4/Laws/Program/TyView.lean`.
Its unchanged producer emits `sizeOf_field_lt_record` and updates one use.
`unrelated-generator-drift.json` retains that difference.
The cleanup restores that file to the integration base and excludes it from the change.
The focused byte comparison checks the owned fragment outputs separately.
No whole-repository drift claim follows from that comparison.
