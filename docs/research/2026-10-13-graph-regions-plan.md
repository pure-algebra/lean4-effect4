# Explicit graph regions and display quotient

The module projects existing displayed adjacency through explicit region membership.
It keeps every edge occurrence and its original endpoints.
It establishes no semantic reduction or path agreement.

Base: `5cd537aef`.
Files: `tools/Tools/View/GraphRegions.lean` and `tools/view/GraphRegionsProbe.lean`.
The coordinator owns Graph, Flow, checker, producer, and gallery changes.
`Eff` remains the only program IR.

## Existing evidence

`Flow.region` (`tools/Tools/View/Flow.lean`) brackets an existing view projection.
`Flow.RegionFrame.items` in that file holds all item positions below the region.
`Flow.RegionFrame.inner` holds all descendant frame keys, not immediate children.
`Flow.framed` assigns both lists while folding the body.
`Flow.Box.append` shifts item positions when it composes parts.
`Flow.layout` drops these memberships and retains only region rectangles.

`Tools.View.Region` (`tools/Tools/View/Graph.lean`) carries geometry and a label.
A rectangle or key spelling does not establish membership.
Generic graph groups remain explicit caller data.
The Flow producer can record direct parent and direct owner during its fold.
Equal-member nested wrappers prevent reliable parent inference from item-set inclusion.
The existing descendant list must not be read as direct parents.

## Representation and interface

`RegionDecl` has a key and an optional earlier parent ordinal.
`Membership` has an ordered region array and one optional direct owner ordinal per existing vertex.
Its arrows are parent incidence and vertex-to-region incidence.
A single direct owner and an acyclic parent forest define laminar transitive member sets.
No program constructor or runtime state enters this representation.

`Representative` is a tagged original vertex ordinal or region ordinal.
Tags keep region identity distinct from original vertex identity.
`prepare` validates the finite metadata and selected-flag length.
It computes each region's outermost selected ancestor in declaration order.
An ancestor selection takes precedence over every selected descendant.
Selection therefore presents an effective antichain without refusing redundant descendant selections.

`Prepared.visible` follows first source-vertex occurrence order.
Effective selected regions without members append in declaration order.
`Prepared.nodeMap` maps each original vertex to its visible ordinal.
`Prepared.members` lists original vertex ordinals per visible ordinal.
The member lists keep source order.
`Prepared.outer` retains each region's selected ancestor answer.

`project` accepts an existing edge array and explicit endpoint readers.
`EdgeOccurrence` keeps the original payload, occurrence ordinal, and original endpoint ordinals.
Its source and target fields name visible ordinals.
An edge hides only when both endpoints map to the same selected region.
An ordinary uncollapsed self-loop remains visible.
Parallel edges remain separate occurrences.
Internal edges remain available as provenance while hidden.

## Refusals and cost

Preparation refuses empty or repeated region keys, a parent not earlier than its child, and an owner outside the region array.
It refuses a selected-flag array whose length differs from the region array.
Projection refuses every endpoint outside the original vertex array.
It also refuses unresolved visible ordinals in an arbitrary manually constructed prepared record.
Every refusal carries its region, vertex, or edge occurrence position.
No unresolved edge is dropped.

Region ancestor preparation uses one pass over parent-before-child declarations.
Vertex projection and edge projection use ordinal arrays.
Representative creation uses arrays indexed by region ordinal.
A source vertex is copied into exactly one member list.
These passes perform work proportional to the supplied array lengths under ordinary array-operation costs.
Region-key validation also hashes and compares key bytes through the existing `KeyMap`.
No theorem establishes a runtime complexity or collision bound.
Benchmarks use projection directly at 100, 1000, and 10000 vertices.
The measured operations include clock-dependent input rotation to prevent compiler hoisting.
They exclude full `Graph.layout` and its separate input checker.

## Placement before proof

1. Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
   The required tool property is occurrence-preserving finite display projection for R14 navigation.
2. Questions: accepted finite observations exactly describe admission; accepted edge projection retains every original payload and occurrence order.
   `GraphRegions.checks_iff` serves preparation admission.
   `GraphRegions.project_originals` serves the original-payload observation.
   `GraphRegions.project_provenance` also observes original endpoints and occurrence ordinals under that same placement.
   `GraphRegions.project_indices` and `project_size` read ordinal and size observations from that provenance law.
   Helper statements serve those laws and the actual graph adapter consumer.
   Proof roles: decidability for admission and preservation for edge provenance.
   Evidence status: proposed before implementation.
   Rows 334 (3) and 336 (8) place these named tool laws outside registry claims.
3. Reach: finite supplied metadata, selected flags, existing edge arrays, and explicit endpoint readers.
   Payload preservation is conditional on successful projection.
   No theorem identifies a caller's metadata with a program's semantic regions.
   Invalid raw prepared records receive no member-partition guarantee.
4. Limits: a region quotient can create displayed paths absent from the original graph.
   The red control has an edge into one member and an edge out of an unrelated member.
   Collapsing their shared region creates a displayed two-edge path.
   Edge provenance alone does not justify composing those edges as an original path.
5. Consumers: the production gallery and `GraphRegionsView` adapter materialize visible nodes through retained ordinal maps.
   Rich labels remain adapter policy.
   The graph operation changes display structure only.

## Controls

Controls use three nested groups, parallel boundary edges, internal edges, and an original self-loop.
They cover outer-versus-inner selection, empty selected groups, invalid metadata, and unresolved endpoints.
They show the false path created by arbitrary collapse.
The narrow build and strict module audit precede explicit-path commits.
