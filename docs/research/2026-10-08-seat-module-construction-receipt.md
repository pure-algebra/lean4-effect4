# Shared module construction laws

## Integration requirement

Import `Effect4.Laws.Modules.Construction` from the Step law module when its construction cases land.
Root the module and its battery at the coordinator's anchors.
This branch changes no roots or registries.

## Base and files

Base: `ca688ee029a7381d7709bb4aa0da400a9d800221`.
Head: the commit carrying this receipt.
Branch: `codex/module-construction`.

- `src/Effect4/Laws/Modules/Construction.lean`
- `Test/Program/StepConstruction.lean`
- this receipt

## Interfaces and placement

The plan places these helpers before their implementation:
`docs/research/2026-10-08-seat-module-gaps-plan.md`.

| Helpers | Concept and claim | Reach | Consumer |
| --- | --- | --- | --- |
| `zipNames_entries`, `build_entries_image`, `reads_record_image` | `translation-simulation`, `step-language-sound`, R10 | Full field columns, canonical names, every identity interpretation and scope | Step record construction, then module agreement and store-attempt laws |
| `check_declared_normal`, `types_record_declared` | `store-typing`, `step-language-typed`, R4 | Exact declared field types, canonical names, formation and normality | Step record construction typing, then module typing and `step_keeps_cell` |
| `reads_nil_ascribe`, `reads_none_ascribe` | `translation-simulation`, `step-language-sound`, R10 | Every declared type and scope | Step empty-value reading |
| `types_nil_ascribe`, `types_none_ascribe` | `store-typing`, `step-language-typed`, R4 | Explicit normality, formation and subtype checks | Step empty-value typing |

The declarations live in `Effect4.Modules`, in `src/Effect4/Laws/Modules/Construction.lean`.
The implementation reuses `entries_names`, `entries_ascending`, `entries_nodup`, and `image_record`.
It reuses `Program.Record.check_declared`, `reads_record`, `types_record`, and the existing ascription laws.
It adds no carrier representation or program constructor.
The generic record helpers accept a supplied carrier; they invent no optional-field carrier.
The planned Step constructor supports required fields only.

These helpers establish no membership, allocation, run, progress, liveness, or native compatibility result.

## Verification

Commands run in the isolated construction worktree:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Construction
LEAN_NUM_THREADS=3 lake env lean Test/Program/StepConstruction.lean
LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-construction-axioms.lean
```

The module build passes with no warnings.
The battery passes with no diagnostics.
The scratch audit checks all nine new helpers.
Each helper uses only `propext` or `propext` with `Quot.sound`.
No helper uses `sorryAx` or `Classical.choice`.

The battery reads the laws at a populated two-field record and both typed empty forms.
Its negative controls cover repeated names, wrong supplied types, unsorted construction, and normal but unformed type variables.
These controls are finite checks, not host results.

The initial proof reduction and subtype readers failed during development.
The final commands above pass after explicit reduction and existing subtype lemmas replace those failed attempts.

## Remaining work

The coordinator integrates the Step constructors and their laws.
The coordinator roots this module and battery.
No full sweep or push runs here.
