# Explicit graph regions receipt

This operation is a display quotient over supplied adjacency.
It retains original edge provenance and does not establish path agreement.
The Flow producer still needs explicit direct membership metadata.

Base: `5cd537aef`.
Core source: `b1247fdae264c9ce8d502ecfb8ed86d41f238cd6`.
Proof and probe delta: `ba9d9fd01f5308f4ac982094c2584177f5730b47`.
Branch: `codex/graph-regions`.

## Interface and consumers

`GraphRegions.RegionDecl` (`tools/Tools/View/GraphRegions.lean`) has a key and optional earlier parent ordinal.
`GraphRegions.Membership` in that file supplies those declarations and one optional direct owner per source vertex.
The parent and owner arrows are explicit incidence data.
`prepare` refuses malformed declarations, owner bounds, keys, and selected-flag length.
Outermost selected ancestors take precedence.

`GraphRegions.Prepared` in that file retains visible representatives, source-to-visible ordinals, member lists, and selected ancestor answers.
Visible representatives follow first source occurrence order.
Empty effective selected regions append in declaration order.
Their member lists are empty.
Tagged representatives distinguish original vertex identity from region identity.

`GraphRegions.project` in that file reads existing edges through explicit endpoint readers.
Its `EdgeOccurrence` retains the occurrence ordinal, original payload, original endpoints, visible endpoints, and hidden flag.
It refuses an out-of-bounds endpoint rather than dropping the edge.
It also refuses unresolved visible ordinals in forged prepared records.
A repeated original payload remains a separate occurrence.
An uncollapsed self-loop remains visible.
An internal collapsed edge remains in the retained array while hidden.

The production adapter and gallery consume the retained ordinal arrays.
Their files and observations belong to the coordinator and adapter seat.
The primitive introduces no new program IR and changes no `Eff` declaration.

## Producer distinction

Generic graph grouping is caller data.
The primitive does not infer membership from rectangles or key spelling.
`Flow.RegionFrame.items` (`tools/Tools/View/Flow.lean`) holds transitive item membership.
`Flow.RegionFrame.inner` in that file holds all descendant frame keys.
It does not identify immediate parents.

The Flow producer can record direct parent and owner while folding `Flow.region` in that file.
Nested regions can hold exactly the same items.
Set inclusion alone cannot reconstruct their direct parent relation.
`Flow.layout` currently drops that membership and retains drawing rectangles.
A later producer slice must retain explicit incidence before offering automatic Flow collapse.

## Proof placement and scope

Concept: `initial-algebras-folds`, concept 7 in `docs/core/semantics.md`.
Requirement: R14 view navigation.
Placement precedes proof in `docs/research/2026-10-13-graph-regions-plan.md`.
Rows 334 (3) and 336 (8) place these named tool laws outside registry claims.

| Declaration in `tools/Tools/View/GraphRegions.lean` | Proof role | Observation |
| --- | --- | --- |
| `checks_iff`, `prepare_iff` | Decidability | Preparation accepts exactly its named finite structural observations |
| `project_provenance` | Preservation | Successful projection retains the complete original occurrence, payload, and endpoint tuple sequence |
| `project_originals` | Preservation | Original edge payloads read back in source order |
| `project_indices` | Preservation | Retained occurrence ordinals equal the complete zero-based source sequence |
| `project_size` | Preservation | Hidden and visible occurrences together retain the source array size |

Projection laws require successful projection.
They hold even when original payload values repeat.
The ancestry preparation function remains private.
Public raw `Prepared` records are unchecked caches.
Projection bounds checks do not validate forged ancestry, member partitions, or intended grouping.
No general theorem in this slice establishes those prepared-table invariants.

A collapse can create a displayed path absent from original adjacency.
The red control enters one region member and leaves an unrelated member.
After collapse, the shared surrogate connects the two displayed edges.
The retained originals show why that displayed path has no original witness.
No proof describes the quotient as a semantic reduction or interprets its paths as execution.

## Commands and results

Each Lake command exports `LEAN_NUM_THREADS=3` in PowerShell.
The commands run serially in the lane worktree.

| Command | Result |
| --- | --- |
| `lake build Tools.View.GraphRegions` | Pass after the final proof delta |
| `lake env lean -DwarningAsError=true --run tools/view/GraphRegionsProbe.lean` | Pass; finite controls and three bounded projection measurements |
| `lake env lean .lake/graph-regions-audit.lean` | Pass; strict checked audit of the complete module |
| `git diff --check` | Pass |

`Audit.txt` in `docs/research/2026-10-13-graph-regions-evidence/` reports 324 declarations under `[propext, Quot.sound]`.
It reports zero goals and zero declarations modulo goals.
The checked walk compares its answers at 2212 captured constants.
Its labels contain only the two allowed axioms.

`ControlCount.json` in that directory records 27 guard commands.
`Controls.txt` retains their successful run and benchmark output.
The controls cover three nested groups, parallel edges, repeated payloads, hidden internal edges, and an original self-loop.
They cover empty groups, invalid metadata, invalid endpoints, and forged ordinal maps.
They also exhibit the false displayed path.

`Benchmarks.jsonl` supplies plain tracked measurement rows for the gallery presenter.
The rows contain 100, 1000, and 10000 source vertices with ten region declarations.
They retain 200, 2000, and 20000 edge occurrences respectively.
Each prepared projection has ten visible representatives.
The probe forces preparation and projection through `IO.Ref` before reading their timestamps.
It consumes results through conservation checks and a checksum.

These measurements run through `lake env lean --run`.
They exclude graph layout, rendering, browser interaction, and generic graph input admission.
They establish no runtime complexity or key-hash collision bound.
No broader benchmark or outside-runtime behavior gate is required by this pure view slice.
The coordinator owns integration audits and production gallery verification.
