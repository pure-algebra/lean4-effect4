# Graph bounds: allocation and drawing geometry

`Call` in `tools/Tools/View/Picture.lean` stores resolved drawing geometry.
Its curve controls use logical pixels.
Its filled shape controls use thousandths of a logical pixel.
`lowerCall` in the same file snaps curve weight to one device pixel at least.

The bounds seam reuses `IBox` and `Boxed` from `Whatwg/Svg/Scene/Extent.lean` in the pinned kit.
`SceneBridge.cubic` in `tools/Tools/View/SceneBridge.lean` converts local controls without rounding.
The kit's integer control hull states no curve or rasterization theorem.
The new seam retains that scope.

## Placement before proof work

| Field | Placement |
| --- | --- |
| Concept | `initial-algebras-folds`, concept 7 in `docs/core/semantics.md` |
| Required property | Fold congruence and list aggregation, applied to the view tool |
| Question and role | Bounds collection contains every reported call envelope, a tool law under decisions row 334 (3) |
| Consumer | `GraphBounds.viewport` in `tools/Tools/View/GraphBounds.lean`, then graph exports and page panels |
| Exact observation | Reported integer envelopes and their stored control hulls, including stroke margins and outward unit conversion |
| Hypotheses | Every call list, with nonnegative optional halo margins |
| Scope limit | No text ink, font metric, clipping intersection, antialiasing, curve sampling or rasterization theorem |
| Requirement | R14's live authoring view, without an Effect judgment or registry claim |

`PaintBounds` in `tools/Tools/View/PaintBounds.lean` collects the resolved call envelopes.
Its report marks text metrics as unmeasured.
Its aggregate envelope ignores clip and hit calls because those calls paint no geometry.
Ignoring clipping gives a conservative envelope of the geometry calls.

`GraphBounds` combines the allocated canvas with the geometry report for a chosen look.
It returns a translation and size for a fitted viewport.
The halo argument adds a caller-selected margin without changing connector geometry.
The look affects the actual call list before the bounds are collected.

Both graph producers retain their original routing width in `Laid.routingWidth`.
They extend allocated width for self-loop control hulls.
Back lanes continue to use the retained routing width.
The allocated rectangles and the geometry envelopes remain separate observations.

## Validation

Build the changed modules and their direct consumers with three Lean threads.
Audit the new pure helper module with `#axiom_audit`.
Run finite controls for loops, back routes, organic noise, large stroke styles, negative geometry and overshoot.
Check that a viewport change leaves route segments unchanged.
Report text metrics as unmeasured in every viewport result that contains text calls.
