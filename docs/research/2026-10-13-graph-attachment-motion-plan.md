# Graph attachment motion plan

Production motion aligns attached points with their sampled mark.
The policy changes the legacy observation during a transition.
The endpoint remains the exact target layout.

Base: `26436e791`.
Owned files: `tools/Tools/View/GraphMotion.lean`, `tools/Tools/View/Motion.lean`, `tools/Tools/View/GraphAttachmentMotion.lean`, and `tools/view/GraphTransitionProbe.lean`.
The coordinator supplies graph attachment and routing-span metadata.
The connector formula remains unchanged.

## Placement before proof

1. Concept: `initial-algebras-folds`, concept 7 of `docs/core/semantics.md`.
   The required tool property is coherent finite rendering observation under graph motion.
   R14 view navigation supplies the consumer.
2. Questions: the production endpoint is the exact target, and every aligned point meets its named current mark.
   `GraphAttachmentMotion.dock_bar` and `dock_diamond` state local attachment observations.
   `GraphMotion.Prepared.sample_end` states target-layout equality at the endpoint.
   `GraphMotion.prepare_legacySample_eq_legacyReference` retains agreement for the separately named legacy policy.
   Proof roles: preservation for attachment observations and compatibility for legacy agreement.
   Evidence status: proposed before implementation.
   Rows 334 (3) and 336 (8) place these named tool laws outside registry claims.
3. Reach: endpoint equality covers arbitrary prepared data, including malformed metadata.
   Local attachment laws require a point rather than a node.
   The bar law requires ordered current bar bounds.
   Neither local law proves that caller metadata resolves or names the intended point.
   The legacy law observes full equality after its explicitly named metadata extension.
4. Limits: the policy establishes no scheduler meaning, routing collision freedom, canvas containment, or new connector geometry.
   Missing or unresolved metadata admits no attachment claim.
   Constructor changes between bars and diamonds use the target mark form.
5. Consumers: prepared production sampling aligns graph ports before route drawing.
   Existing graph exporters and the motion inspector read the resulting layouts.
   The coordinator records named law placement under the existing R14 view plan.

## Data and policy

`PortAttachment` names an existing placement key and an existing mark key.
Its arrows are lookups into existing finite layout data.
It adds no program representation.
The supported producer assigns at most one mark to each point.
Unchecked duplicates retain first-lookup behavior.

Preparation matches marks and regions by their explicit keys.
A kept mark interpolates coordinates when both endpoint constructors agree.
A changed constructor uses the target form.
An added mark starts at its target geometry.
A removed mark remains until the transition endpoint.
Kept regions interpolate origin and size.
Removed regions remain until their leaving graph retires.

Mark and region movement uses progress clipped to `[0,1000]`.
That policy prevents easing overshoot from reversing a valid bar interval or region size.
The legacy placement sampler retains its existing position and growth arithmetic.
An attached kept point takes the current mark height and a clamped current horizontal position.
An entering or leaving point maps its endpoint mark-relative position onto the current mark.
A diamond attachment takes the current diamond centre.
A node attachment or unresolved attachment keeps the legacy placement.

Source attachments remain available only for points absent from the target layout.
Kept points without target incidence detach and move freely.
Target attachments take precedence for shared placement keys.
No operation parses a key spelling to discover an attachment.
Before the endpoint, routing width uses the greater endpoint routing span.
Canvas width remains independent of that routing span.
At or after the endpoint, production sampling returns the entire target layout.

## Legacy observation

`GraphMotion.reference` retains the original display computation.
`GraphMotion.legacyReference` extends it with target attachment metadata and the separately retained routing span.
`GraphMotion.Prepared.legacySample` agrees with that extended observation.
`GraphMotion.Prepared.sample` uses the new production policy.
No all-input legacy agreement theorem names production sampling.

## Controls

Finite controls cover moving bars, inserted and deleted attached ports, moved diamonds, and interpolated regions.
They also cover removed marks, unresolved metadata, constructor changes, and malformed endpoint metadata.
Endpoint checks compare whole layout data rather than only coordinates.
The strict audit checks each new pure module.
The narrow builds check existing motion endpoint laws and direct callers.
The coordinator owns complete export comparisons and the separate movement-separation policy.

## Separation policy placement before proof

The prepared policy records direct motion or an endpoint-family fallback with its reason.
Reasons name changed node membership, potentially overshooting movement, or a conservative swept-box conflict.
A matched point-to-node or node-to-point change forces endpoint-family fallback.
Otherwise, an empty endpoint node family permits growth at fixed endpoint positions.
Production growth is clipped to `[0,1000]`.
Matching nonempty node families can travel directly only under a bounded easing form and clear conservative sweeps.
Other nonempty families shrink the old scene, relocate while hidden, and grow the target scene.
The policy always selects marks, routes, regions, attachments, and routing span from the same endpoint family.

Concept: `initial-algebras-folds`; requirement R14; proof role preservation; evidence status proposed.
`GraphMotion.family_growth_le` bounds every generated growth value.
`GraphMotion.family_boxes_inside` serves fallback box-separation through endpoint box containment.
The exact local statement requires a nonnegative allocated width and height.
The coordinator's `GraphSeparation.fallback_clear` supplies separation for disjoint endpoint envelope families.
No theorem here identifies every supplied endpoint as valid or separated.
No box observation establishes clearance of routes, regions, marks, text, or arbitrary overshooting motion.
