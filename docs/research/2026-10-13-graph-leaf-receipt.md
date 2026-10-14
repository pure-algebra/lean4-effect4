# Graph content and typography receipt

The new content and text modules pass the strict axiom gate.
The graph module retains the same eight String-related findings as its measured baseline.
This landing changes no trust exemption.

## Revisions and files

Base: `f30913ad3`.
Code head: `030ad73990eff05e8ba688e537a6b15fabcb9cb2`.
Branch: `codex/pegs-port`.
Worktree: `C:/Users/kokok/.codex/worktrees/pegs-port/lean4-effect4`.
The attached `2026-10-13-graph-leaf-evidence/ChangedPaths.txt` lists the changed paths.
The kit stays at `e51195721f47fa767fb84f918dc439e76d83071f`.

`GraphContent` in `tools/Tools/View/GraphContent.lean` projects constructor names, ordered arguments, and source addresses through the generated layer.
It joins address-local typing and declared operation rows.
Child arguments retain their sort without storing another program tree.
The content receipt records the API's evidence limits.

`GraphText.Style` in `tools/Tools/View/GraphText.lean` selects the two row faces.
`none` retains the existing cell renderer.
A selected face uses text within an explicit row clip.
Selecting the data face explicitly does not select the cell renderer.

`Laid.boxCalls`, `Laid.callsCached`, and `Laid.calls` in `tools/Tools/View/Graph.lean` accept an optional final style argument.
Existing calls retain their defaults.
The body, hit rectangle, and connector construction share their existing implementation.
The study changes labels before layout, so different content can change allocated widths.
Changing only the face does not change allocation.

## Research and visual decisions

The research note is `2026-10-13-graph-semiotics-research.md`.
The library review is `2026-10-13-graph-typography-audit.md`.
Both distinguish primary evidence from local design proposals.

The study compares existing labels, operation with arguments, and operation with type.
Code emphasis and the existing book face remain selectable.
The inspector retains optional argument absence, declared operation spelling, exact constructor identity, and separate A, E, and R fields.
Typing refusal, unavailable typing, and the type `never` remain distinct.
No runtime result or execution badge is inferred from the static program.
Selection uses a separate dashed outline.

The generated page is `tools/view/out/graph-leaves/index.html`.
The inspected screenshot is `tools/view/out/graph-leaves/inspection.png`.
Eight programs produce 24 checked SVG files.
The output generator owns these untracked artifacts.

## Commands and results

Commands run from the worktree with `LEAN_NUM_THREADS=3`.

```text
lake build Tools.View.GraphContent Tools.View.FlowSpecimen Tools.View.LiveChecks Tools.View.GraphBounds Tools.View.GraphCheck
lake env lean tools/view/GraphTextProbe.lean
lake env lean tools/view/GraphContentProbe.lean
lake env lean docs/research/2026-10-13-graph-leaf-evidence/ContentTextAudit.lean
lake env lean docs/research/2026-10-13-graph-leaf-evidence/GraphAudit.lean
lake env lean --run tools/view/GraphLeafStudy.lean tools/view/out/graph-leaves
python tools/view/graph_leaf_study.py tools/view/out/graph-leaves
python -m py_compile tools/view/graph_leaf_study.py
python scripts/check-language.py --strict docs/research/2026-10-13-graph-typography-plan.md docs/research/2026-10-13-graph-leaf-receipt.md
git diff --check
```

The narrow build passes with 428 jobs.
It reaches each direct importer of the graph module and the existing live checks.
The content probe's 37 guards pass, including parity across 16 existing flow specimens.
The text probe's four guards pass.
They cover default row budgets, explicit clipping, zero room, and the existing growth threshold.
The combined new-module gate passes 101 declarations with zero planned goals.
Its checked dependency snapshot contains 3651 constants and only `propext` and `Quot.sound`.
The attached text files retain the probe and gate output.

The full graph gate refuses eight of 461 declarations before and after this landing.
Both runs name the same declarations and the same two minimal causes.
`Laid.organicCalls` reaches `Grow.seedOf`, then `String.foldl`.
`Graph.boxWidth` reaches `String.length`.
Both paths reach `Classical.choice` through toolchain constants.
The graph report is not a strict pass.
The baseline report lives in `2026-10-13-graph-typography-evidence/BaselineGraphAudit.txt`.

Each gallery layout passes `GraphCheck.laid` before drawing.
Each emitted SVG passes `SvgOut.fileText`.
Python parses each SVG root and checks positive dimensions before embedding it.
The manifest check confirms argument-kind alignment and matching node keys across all three modes.
Python compilation and the whitespace check pass.

## Host inspection

Browser inspection covers both faces, both looks, an unresolved wait, a declared Ref operation, and a long operand containing markup characters.
The loop inspector shows its absent optional type as `none`.
The three comparison crops use the same scale.
The graph overview caps enlargement at 1.5 times its logical size.
The actual-size mode permits scrolling for wide graphs.
The narrow viewport is 390 by 844 pixels.
Its document has no horizontal overflow.
Embedded SVG identifiers remain unique across all four views.
The browser reports loaded fonts.
The final exported HTML is reloaded and inspected.

These observations are host evidence, not Lean theorems about glyph ink or reader comprehension.

## Open work and placement

This slice adds passive projection and style data with finite controls.
It states no new semantic theorem or registry claim.
The content plan records its concept 7 and R14 scope.

`SvgOut.shown` in `tools/Tools/View/SvgOut.lean` still truncates by code point.
Semantic-piece fitting needs explicit piece identities and width bounds before adopting the kit's `Label` operations.
Font ascent, descent, and shaping remain host inputs.
A clip contains visible text but can cut a glyph; it does not prove font fitting.
Native and SVG text abbreviation remain different.
Binding navigation and variable-height leaves need separate consumers and geometry contracts.
Runtime styling needs an identified run observation.

The slice reaches no Effect runtime comparison gate.
No dependency update, whole-tree battery, push, or default typography switch runs.
