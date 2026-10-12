# Shared list relation: caller receipt

The slice removes the private reading relation and retains the named reading and typing theorems.
The only theorem-header substitutions replace `Pointwise` with the existing `Effect4.ListRel`.
No runtime definition changes.

Base: `c31acf15b`.
Source head: `245130eca`.

## Placement

Proof role: shared instances.
Evidence status: checked reader build and axiom gate.
Scope: step-language reading and typing, and Pool's resource construction.

The [plan](MachinePointwisePlan.md) records the five-part placement before source changes.
`ReadsAll` and `TypesAll` consume the shared relation at their existing entry predicates.
`Pool.make_makes` consumes `reads_initial`, `reads_itemsFrom` and `reads_stampsFrom`.
Its placement remains `translation-simulation`, requirement R10.
The typing callers serve `step-language-typed`, requirement R4.

## Changed files

- `src/Effect4/Laws/Data/ListRel.lean`
- `src/Effect4/Laws/Data/ListRelConnectors.lean`
- `src/Effect4/Laws/Step/Reading.lean`
- `src/Effect4/Laws/Step/Checking.lean`
- `src/Effect4/Laws/Library/Pool/Ops.lean`

## Representation and statements

`Effect4.ListRel` remains the only shared list relation.
`Modules.Pointwise` and its two constructors go.
`Pointwise.of_map` retains its name and delegates to `ListRel.of_map_left`.
`Data.pointwise_iff` retains its name and becomes reflexive.
`Program.Fits` and `Data.fits_iff` remain unchanged.

The header inventory measures 248 existing declarations.
Of these, 235 keep their exact header text.
Twelve only substitute the authorized shared relation.
One is the deleted private relation definition.
The inventory separately records each substitution in `MachinePointwiseHeaders.json`.
The comparison asserts no new declaration name and no other header change.

The five files contain 2,831 lines before the slice and 2,814 after it.
The measured source diff adds 25 lines and removes 42, for 17 fewer lines.
The connector loses its two list inductions.
The map helper loses its separate recursive proof.

## Checks

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Step.Reading Effect4.Laws.Step.Checking Effect4.Laws.Library.Pool.Ops Effect4.Laws.Data.ListRelConnectors Test.Program.StepConstruction Test.Program.PoolOps
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/MachinePointwiseAudit.lean
python3 docs/research/2026-10-11-machine-models/codex/MachinePointwiseHeaderCompare.py 245130eca
python3 scripts/check-language.py --strict docs/research/2026-10-11-machine-models/codex/MachinePointwisePlan.md docs/research/2026-10-11-machine-models/codex/MachinePointwiseReceipt.md
```

Result: the narrow build passes 1,035 jobs.
The seven-module axiom gate passes 396 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.
The strict language check passes both the plan and receipt.
`MachinePointwiseBuild.log` and `MachinePointwiseAudit.log` retain the exact output.

`Test.Program.StepConstruction` applies the populated-record reader and exact field-typing rule at real source terms.
`Test.Program.PoolOps` checks the actual Pool construction and run controls.
No battery statement changes.

## Limits and next step

This slice adds no planned goal.
It states no new progress, whole-run or host result.
The existing scenario statements remain unchanged.
The next validity slice must remove the `Names` to `StoresLaws` dependency cycle before moving callers.
Its dependency plan remains separate from this accepted caller slice.
