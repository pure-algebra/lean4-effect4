# Independent graph packing receipt

The packer moves independent rendered envelopes and retains their original array occurrences.
It changes no connected-node routing, component geometry or semantic graph.
The coordinator's gallery consumes the occurrence index to recover each original component.

## Commits and files

- Base: `5cd537aef9838da43d4f9377d033028bddf7403a`.
- Source head: `f32fcdf1e2aab8da201f2361026bbecf40a15811`.
- Branch: `codex/graph-packing`.
- Worktree: `C:/Users/kokok/Dev/effect4-graph-performance`.

The source commit adds these files:

- `tools/Tools/View/GraphPacking.lean`.
- `tools/view/GraphPackingProbe.lean`.
- `docs/research/2026-10-13-graph-packing-plan.md`.

## API and policy

Packing assigns an independent rectangle envelope to a position in a canvas.
A shelf is one horizontal run of those rectangles.
The caller supplies natural widths and heights in `GraphPacking.Size`.
`GraphPacking.Options` supplies the target width and natural gap.
`GraphPacking.pack` returns `GraphPacking.Packed`.
All declarations live in `tools/Tools/View/GraphPacking.lean`.

The packer retains original array positions before the stable height sort.
Each placement holds its original occurrence, kit `IBox`, shelf number and oversize flag.
The result holds the actual canvas, placements, shelf count, item area and oversize count.
An oversized rectangle occupies its own shelf and widens the actual canvas.
The next rectangle starts another shelf after an oversized rectangle.
Zero dimensions remain empty rectangles with their own occurrence identities.
The actual canvas includes no unused target-width padding or trailing gap.

The source performs one stable sort and one shelf-frontier fold.
The fold retains a reverse placement list and reverses it once for the output array.
The runtime performs no pairwise overlap check.
The complexity observation concerns comparisons and placement steps, without a bit-complexity or allocator claim.

The kit search finds fixed rows, columns and stacks in `Whatwg/Svg/Scene/Layout.lean`.
Its `Whatwg/Svg/Scene/Strip.lean` places time-lane runs.
The search finds no target-width shelf packer in the kit's scene or geometry modules.
The new module reuses the kit's `IBox`, `IVec`, containment and disjointness definitions.

## Proof placement

Proof role: tool laws under decisions row 334 (3).
Evidence status: proved within `[propext, Quot.sound]`.
Scope: every finite array of natural sizes, target width and natural gap.

The placement plan precedes proof work.
It serves concept 7's folding construction and R14's live authoring view.
`pack_inside` states that each returned rectangle lies inside the actual canvas.
`pack_disjoint` states pairwise `IBox.Disjoint` for the returned rectangles.
A zero gap permits touching sides.
`pack_occurrences` states that the returned indices are a permutation of the original array positions.
All three laws live in `tools/Tools/View/GraphPacking.lean`.

The shelf-frontier invariant supplies the next rectangle's separation without a runtime scan.
Its placement-step proof and fold proof serve both geometry laws.
The occurrence fold helper serves the identity law.
The laws establish no optimal area, font metric, connected-node relation or rasterization observation.
The host boundary remains the boundary in `docs/core/host-boundary.md`.

## Commands and results

The commands run under PowerShell with `LEAN_NUM_THREADS=3`.

```powershell
lake build Tools.View.GraphPacking
lake build ProofGraph.AxiomAudit
lake env lean -DwarningAsError=true --run tools/view/GraphPackingProbe.lean controls
lake env lean -DwarningAsError=true --run tools/view/GraphPackingProbe.lean
python scripts/check-language.py --strict docs/research/2026-10-13-graph-packing-plan.md
```

The narrow build and plan language check pass.
The probe's audit reports:

```text
#axiom_audit: 199 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The finite controls check containment, dimensions, occurrence identities, gaps and pairwise disjointness.
They include exact shelf coordinates, equal-height stability, oversized rectangles, zero dimensions and target width zero.
They also include a natural width beyond a machine word.
Only small controls perform pairwise checks.

## Retained measurements

Evidence status: consumed finite measurements on Lean 4.33.1, Windows x86-64.
Scope: `lake env lean --run`, including input generation, sorting, packing and output digest.
The timer excludes compilation, the module audit and the independent validation of the sample.
Each timed call varies its input through the repetition index and uses `@[noinline]`.
Those calls prevent closure construction from precomputing the measured result.

The retained outputs are:

- `docs/research/2026-10-13-graph-packing-trial-1.csv`.
- `docs/research/2026-10-13-graph-packing-trial-2.csv`.
- `docs/research/2026-10-13-graph-packing-trial-3.csv`.

Each run records its input count, repetitions, duration, shelf count, canvas, item area and digest.
The repeated runs retain identical digests.
`docs/research/2026-10-13-graph-packing-summary.json` derives average durations from these outputs.
These measurements establish no native renderer latency or optimal packing quality.

Reproduce the averages with this PowerShell command:

```powershell
Get-ChildItem docs/research/2026-10-13-graph-packing-trial-*.csv | ForEach-Object {
  $packingTrial = $_.Name
  Get-Content -LiteralPath $_.FullName | Select-Object -Skip 2 | ConvertFrom-Csv | ForEach-Object {
    [PSCustomObject]@{
      Trial = $packingTrial
      Count = [int]$_.count
      Repetitions = [int]$_.repetitions
      AverageMs = [math]::Round([double]$_.elapsed_ns / [double]$_.repetitions / 1e6, 4)
      Checksum = $_.checksum
    }
  }
}
```

## Open work

The geometry and occurrence observations have no open proof obligations.
The coordinator integrates the frozen API into the compound graph gallery.
The caller remains responsible for the supplied rendered envelope sizes, including any unmeasured text metrics.
No outside-implementation behaviour gate reaches this view-only packing slice.
Lake retains the existing `whatwg` manifest warning.
This slice changes no pin or external publication.
