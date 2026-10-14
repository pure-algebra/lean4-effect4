# Graph library admission receipt

The checker passes its strict audit. The layout producer inherits the existing text-measurement trust boundary.
The new entry point does not establish painted bounds or collision freedom during motion.

Base: `d6285ddf8ab54ef7d5fc3bb32a23831173e45afe`.
Head: the commit containing this receipt.

## Changes

| Path | Change |
| --- | --- |
| `tools/Tools/View/GraphCheck.lean` | Edge-key checks and a producer-independent checked value |
| `tools/Tools/View/GraphLayout.lean` | Input admission, one layout computation, allocation admission, and returned evidence |
| `tools/Tools/View/Specimen.lean` | Checked frame producer with shared page construction |
| `tools/view/GraphLibraryProbe.lean` | Positive and negative finite controls |
| `docs/research/2026-10-13-graph-library-plan.md` | Placement before implementation |
| `docs/research/2026-10-13-graph-library-evidence/` | Probe output and rendering audit |

`GraphCheck.Checked` records `InputOK` and `LaidOK`, as defined in `tools/Tools/View/GraphCheck.lean`.
It records no relationship to a particular layout algorithm.
`GraphLayout.checked` in `tools/Tools/View/GraphLayout.lean` computes the existing `Graph.layout` after input admission.
It checks the resulting allocation before returning it.
This separates the reusable checker from layout's text measurement.
`Specimen.checkedFrames` in `tools/Tools/View/Specimen.lean` supplies the driver's admitted specimen pages.

The input check now refuses empty or repeated edge keys.
Parallel edges with distinct keys remain admitted.
Refusals follow phases: node keys, edge keys, endpoint positions, then layout checks.
The finite controls pin this order.

## Proof placement

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Question: `view-graph-renderability-check`, proposed under decisions row 334 (3).
Role: decidability of the named finite observations.
Requirement: R14, through graph rendering.
The certificate consumes the existing `input_iff` and `laid_iff` laws in `tools/Tools/View/GraphCheck.lean`.
No new theorem or planned goal enters the library graph.

## Commands and evidence

```powershell
$env:LEAN_NUM_THREADS='3'
lake build Tools.View.GraphLayout Tools.View.Specimen ProofGraph.AxiomAudit
lake env lean -DwarningAsError=true --run tools/view/GraphLibraryProbe.lean
lake env lean docs/research/2026-10-13-graph-library-evidence/RenderingAudit.lean
```

The narrow builds and finite controls pass.
`docs/research/2026-10-13-graph-library-evidence/Controls.txt` records the strict checker audit and measured specimen counts.
The existing Flow specimens pass allocation admission.
Checked generic specimen layouts match the previous producer's layouts in the finite control.
The collision control passes input admission and fails layout admission at the generated duplicate placed key.

The rendering audit returns an error, retained in `docs/research/2026-10-13-graph-library-evidence/RenderingAudit.txt`.
Its reported paths reach `Classical.choice` through `Graph.boxWidth` and Lean's `String.length`.
The previous `Specimen.frames` producer has the same text-measurement dependency.
The new checked producer inherits that boundary.
The strict checker audit is not evidence for the producer's whole import closure.
No axiom exemption changes in this slice.

The tool-only change reaches no Effect runtime, codec, compiler, or TypeScript behaviour gate.
Lake reports the existing kit manifest revision mismatch.
No dependency configuration changes.

## Open obligations

The loop control demonstrates that allocation admission excludes painted route bounds.
The certificate establishes no scheduler behaviour, program typing, semantic projection, or moving-frame validity.
The coordinator owns registration of the proposed tool question and any rendering exemption decision.
The driver's prepared-motion slice adopts `Specimen.checkedFrames` at both specimen call sites.
