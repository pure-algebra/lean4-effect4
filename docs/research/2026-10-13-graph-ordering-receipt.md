# Graph ordering receipt

Cherry-pick the implementation before this receipt.
The implementation changes rank ordering and moves its declarations into `tools/Tools/View/GraphOrdering.lean`.
The declaration names retain the `Tools.View.Graph` namespace.

## Commits and files

- Base: `d6285ddf8ab54ef7d5fc3bb32a23831173e45afe`.
- Implementation head: `1df1cc46ab7184c01fe26f9562ce07f6c51d2afd`.
- Branch: `codex/graph-ordering-performance`.
- Worktree: `C:/Users/kokok/Dev/effect4-graph-performance`.

The implementation changes these files:

- `tools/Tools/View/Graph.lean`.
- `tools/Tools/View/GraphOrdering.lean`.
- `tools/view/GraphOrderingAudit.lean`.
- `tools/view/GraphOrderingProbe.lean`.
- `docs/research/2026-10-13-graph-ordering-plan.md`.

## Placement and observation

Proof role: tool law under decisions row 334 (3).
Evidence status: proved by `Graph.reorder_eq` in `tools/Tools/View/GraphOrdering.lean`.
Scope: every order, beside order and neighbour function, with no distinctness or order assumptions.

The observation is the exact key list returned by the original stable sort comparator.
The theorem retains duplicate keys, first positions, absent neighbours and stable ties.
The placement plan records concept 7, fold congruence and R14 before proof work.
`Graph.orders` in `tools/Tools/View/Graph.lean` consumes the implementation.
`Run.page` in `tools/Tools/View/Run.lean` consumes the resulting layout.

## Commands and results

The commands run with `LEAN_NUM_THREADS=3` under PowerShell.
The dependency package trees are ordinary copies, without symlinks.
Lake restores the available artifacts into this worktree's build directory.

```powershell
lake build Tools.View.GraphOrdering Tools.View.Graph Tools.View.Page Tools.View.GraphCheck Tools.Document.Figure Tools.View.Run Tools.View.Motion
lake env lean -DwarningAsError=true tools/view/GraphOrderingAudit.lean
lake env lean -DwarningAsError=true --run tools/view/GraphOrderingProbe.lean quick
lake env lean -DwarningAsError=true --run tools/view/GraphOrderingProbe.lean
python scripts/check-language.py --strict docs/research/2026-10-13-graph-ordering-plan.md
```

The narrow build passes.
The plan passes the controlled-English check.
The probe passes its order controls and exact synthetic layout comparisons.
Each timed pair returns matching checksums.
The timed calls vary their input through the repetition index and carry `@[noinline]`.
This prevents closure construction from computing the measured result before the timer starts.

The ordering module's axiom output is:

```text
#axiom_audit: 5 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The whole graph module's audit refuses its existing rendering dependencies.
`Graph.boxWidth` reaches `Classical.choice` through `String.length`.
`Laid.organicCalls` reaches it through `Grow.seedOf` and `String.foldl`.
The audit reports eight declarations above these paths.
The sorting declarations appear in no refusal.

Lake also reports the existing `whatwg` manifest revision warning.
This slice changes no manifest or dependency revision.

## Measurements

Evidence status: finite paired measurements on Lean 4.33.1, Windows x86-64.
Scope: `lake env lean --run`, with two synthetic ranks and three edges per source.
The results do not measure native renderer latency, film serialization or scheduler execution.

The probe retains these command outputs:

- `docs/research/2026-10-13-graph-ordering-quick-1.csv`.
- `docs/research/2026-10-13-graph-ordering-quick-2.csv`.
- `docs/research/2026-10-13-graph-ordering-quick-3.csv`.
- `docs/research/2026-10-13-graph-ordering-full.csv`.

The quick runs retain the same direction of change at every tested width.
The full run includes the largest ordering input.
`docs/research/2026-10-13-graph-ordering-summary.json` derives durations and ratios from the full output.

Reproduce the summary with this PowerShell command:

```powershell
$rows = Get-Content docs/research/2026-10-13-graph-ordering-full.csv | Select-Object -Skip 1 | ConvertFrom-Csv
$rows | ForEach-Object {
  [PSCustomObject]@{
    Case = $_.case
    Width = $_.width
    BeforeMs = [math]::Round([double]$_.baseline_ns / 1e6, 2)
    AfterMs = [math]::Round([double]$_.candidate_ns / 1e6, 2)
    Ratio = [math]::Round([double]$_.baseline_ns / [double]$_.candidate_ns, 2)
  }
} | ConvertTo-Json
```

## Remaining work

The theorem states no crossing, separation or runtime observation.
The synthetic layout checks remain finite probes.
The view introduces no Effect judgment, interpreter or generated-code relation.
No outside-implementation behaviour gate reaches this sorting slice.
The ordering observation has no open proof obligation.

The predecessor scans, rank list indexing and placement passes retain their current algorithms.
The whole graph module retains the rendering dependencies reported above.
The host boundary remains the boundary in `docs/core/host-boundary.md`.
