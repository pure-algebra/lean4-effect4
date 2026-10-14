# One connector perimeter receipt

The coordinator must migrate `Laid.organicCalls` before the new geometry changes displayed calls.
The current slice retains the old producer during that migration.
The next adapter consumes the kit's strict integer outline owner.

Base: `98d32093df7bc3f7a0a670c727e14800cf28b6d4`.
Implementation head: `1b0284dc2a62c630985d91e5fcd306ec19641062`.
Branch: `codex/continuous-connector`.

## Files and interface

`tools/Tools/View/Connector.lean` owns neck reservation and paired noisy sides.
`Connector.Dock` contains relative surface offset and radius in thousandths.
`Connector.stroke` accepts seed, organic settings, width, logical cubics, tip, source dock, and target dock.
`Connector.Body.edges` pairs left and right cubics in forward order.
The pair structure prevents silent truncation of an independently supplied side.

The perimeter runs along the right side, crosses the end, returns along the left side, and crosses the start.
Reversal swaps existing controls without another interpolation.
`Connector.capSegments` and `Connector.smoothJoins` expose structural indices.
Neither function filters by whether a tangent check passes.

Only `Organic.noise` and `Organic.wave` affect this computation.
The graph resolves width and requested flare radius before it calls the connector.
The coordinator owns the memo, callers, renderer, and actual SVG checks.

## Placement

The prior brief is `docs/research/2026-10-13-connector-plan.md`.
The concept is `initial-algebras-folds`, serving R14 live authoring.
The role is a tool geometry helper under decisions row 334(3) and row 336(8).
The observation is integer cubic controls at intended side joins.
The consumer is `Laid.organicCalls` in `tools/Tools/View/Graph.lean` after migration.

`Connector.catmull_shared` establishes equal integer handles at adjacent forward Catmull–Rom segments.
`Connector.pinStart_handle` and `Connector.pinEnd_handle` establish the prescribed vertical body handles.
Their nonzero-radius premise remains explicit.
Finite controls check their composition with the flares and emitted perimeter.
No global theorem claims absence of intersections, exact circles, or scheduler meaning.

## Commands and evidence

Run these commands from the worktree root with `LEAN_NUM_THREADS=3`.

```powershell
lake build Tools.View.Connector
lake env lean docs/research/2026-10-13-connector-evidence/Controls.lean
lake env lean docs/research/2026-10-13-connector-evidence/Audit.lean
git diff --check
```

The narrow build passes with five jobs.
The controls pass for 64 seeds at six route shapes.
The shapes include straight, bumpY, linear, stepY, short, and duplicate-control curves.
Additional controls cover partial tips, unequal offsets, zero wave, tiny radius, empty route, and zero width.
A damaged control retains endpoint contact but fails the exact tangent check.

The tangent check requires equal nonzero integer handles at every intended side join.
Thus these finite cases establish exact C1 handles, stronger than an angular tolerance.
The caps remain deliberate corners.
This evidence does not establish a global C1 theorem for every request.

Retained outputs reside in `docs/research/2026-10-13-connector-evidence/`.
The strict audit reports:

```text
#axiom_audit: 137 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The dependency manifest warning precedes each run.
It reports the existing coordinator repin mismatch.
This slice changes no manifest or dependency configuration.

## Kit boundary and open work

The provisional rational adapter reaches `Classical.choice` through `Vec.mid`, `Rat.instAdd`, and toolchain proposition decisions.
That adapter and its rational import leave the production module before this commit.
The kit permits this rational boundary under its R-11 policy.
The Effect4 connector retains the strict integer ceiling.

The kit agent prepares `Whatwg.Svg.Scene.Ribbon` with paired integer cubics and the same outline recipe.
The next slice replaces the local perimeter assembly with that owner.
The coordinator runs actual SVG closure, tangent, cache, and visual checks after caller migration.
Neither this receipt nor the finite source controls claims those checks already pass.
