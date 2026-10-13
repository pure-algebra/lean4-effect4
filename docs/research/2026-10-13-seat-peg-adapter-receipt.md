# Peg adapter receipt

Merge this slice after the kit publishes `Whatwg.Svg.Scene.Belt`, `Skeleton`, and `PegFigure` with `Belt.ONE = 1000000000`.
The coordinator owns the dependency pin.

Base: `1362c236d900873c947fe611fd61b94e674c0716`.
Code head: `a079215704a0d88c7abd9ac61afa1746f7cbf9bf`.
Branch: `codex/peg-geometry`.

## Change

The kit owns all peg, skeleton, and figure carriers.
Effect4 aliases those carriers and keeps the final SVG renderer.
`PegBridge` converts tuple vectors and pen cubics at that renderer's boundary.
No duplicate peg, skeleton, or figure structure remains.

Changed files:

- `tools/Tools/View/Tube/PegBridge.lean`
- `tools/Tools/View/Tube/Belt.lean`
- `tools/Tools/View/Tube/Skeleton.lean`
- `tools/Tools/View/Tube/PegFigure.lean`
- `tools/Tools/View/Tube/PegRender.lean`
- `tools/Tools/View/Tube/PegChecks.lean`
- `docs/research/2026-10-13-peg-adapter-plan.md`

`Glyphs.lean` remains unchanged in this slice.
The local dependency directory receives the kit's frozen sources for verification.
Those copies and their build outputs remain untracked.

## Proof placement

Concept: initial algebras and folds, concept 7 in `docs/core/semantics.md`.
Proof role: tool laws under decisions row 334, point 3.
Requirement served: R14's inspection tool boundary.
Placement: `docs/research/2026-10-13-peg-adapter-plan.md`.

`normal_inset` and `normal_move` in `tools/Tools/View/Tube/Belt.lean` transport the kit's exact integer normal laws.
Their consumers are casing construction and figure placement.
Their observations remain optional integer normal equality.

`Skeleton.tour_move` in `tools/Tools/View/Tube/Skeleton.lean` reexports the kit's exact translation observation.
`Skeleton.walk_head`, `Skeleton.walk_last`, and `Skeleton.walk_closed` in that module reexport the kit's rooted-walk observations.
They establish no curve topology or Effect semantics.

## Verification

Run from `C:/Users/kokok/Dev/lean4-effect4-peg-geometry`:

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.Tube.PegChecks Tools.View.Tube.GlyphPage
lake env lean .lake/peg-adapter-audit.lean
lake env lean .lake/peg-adapter-compatibility.lean
git diff --check
```

The final narrow build passes with 448 jobs.
Its direct consumers include `Glyphs`, `Score`, `Sheet`, and `GlyphPage`.
The final compatibility probe passes without diagnostics.
The final diff check passes.

The audit input imports `Tools.View.Tube.PegChecks` and `ProofGraph.AxiomAudit`.
Its command is:

```lean
#axiom_audit Tools.View.Tube.PegBridge Tools.View.Tube.Belt
  Tools.View.Tube.Skeleton Tools.View.Tube.PegFigure
  Tools.View.Tube.PegGlyphs Tools.View.Tube.PegChecks
```

Measured output:

```text
#axiom_audit: 79 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

## Finite transfer evidence

The compatibility probe reads the original belt source through this command:

```powershell
git show 36d5b01401ce451a00b39c008679cc6d8388bb4d:tools/Tools/View/Tube/Belt.lean
```

It changes only that source's namespace to `FrozenPeg` and opens `Tools.View.Tube.ONE`.
It uses the original `pegOutlines` computation with tuple peg scaling.
It compares that computation with the kit adapter on every authored body and unit contour.
The comparison uses full cubic record equality at step 12000 and inset `LINE`.
It passes for the 37 authored shapes.
This evidence is finite and does not establish universal arithmetic agreement.

The landed controls also compare the kit's normal scale with the pen's scale.
They check cubic record conversion on every authored outline and casing.
All previous contour, rounding, containment, and branch-revisit controls still pass.

## Remaining boundary

There are no open proof obligations in this slice.
The kit pin remains the coordinator's integration action.
No reached Effect runtime behaviour gate changes.
The original SVG boundary still reaches `Classical.choice` through the kit's typed node carrier.
The strict audit therefore covers geometry and adapters, excluding the existing SVG rendering declarations.
The first geometry receipt names those declarations and their dependency route.
This slice adds no broader rendering trust claim.
