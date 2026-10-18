# The view seat's receipt: the wipe, the proof graph's measurement, the kit's page (2026-10-18)

Status: a seat's receipt (history, not authority). Seat: view and docs. Worktree
`/Users/pooks/Dev/wt-view-seat`, branch `seat/view-unify`. Brief: [seat-brief.md](seat-brief.md),
narrowed by the coordinator's relay of the owner's redirect (2026-10-18): cleanup and
unification only, stop after V2.

## 1. The one thing to know before merging

V1 stopped at its measurement, so the d3-dag page stays as it was. `Graph.layout` does not lay out
the map's proof graph within ten seconds. The reach of 6 of the 14 requirements, 546 nodes, takes
28 seconds compiled. Nearly all of it is `Place.conflicts`: 28.7 of `Place.centres`' 29.6 seconds,
in a run that times the steps apart.

Two more items for the merge:
- `docs/core/decisions.md` cites the deleted `docs/design/design-language.md` at rows 354, 366,
  367 and 380. `python3 scripts/check-docs.py --fix` repairs them to `git:4a81cc034`.
- The header comment of `ocaml/engine/kit/dune` still names `Kit_view`. The brief kept my edit of
  that file to its `modules` line.

## 2. Commits

Base: `refactor/phase1-phase3` at `4a81cc034`. Head: the commit that adds this receipt, on `9a04ea172`.

| Slice | Commit | Status |
| --- | --- | --- |
| V0, the wipe | `d8416c1f7` | landed |
| V1, the proof graph as a figure | none | stopped at the measurement (section 4) |
| V2, the kit's page goes | `9a04ea172` | landed |
| V3 to V7 | none | dropped by the owner's redirect |
| this receipt | the head | the evidence of section 4 beside it |

## 3. The files changed

V0 (`d8416c1f7`):
- deleted: `docs/design/` (10 files); the 19 probes `tools/view/Graph*.lean`; the 10 studies
  `check_connectors.py`, `check_smoothness.py`, `curvature_study.py`, `d3_curve_study.py`,
  `d3_curve_study.mjs`, `graph_contracts.py`, `graph_leaf_study.py`, `graph_regions.py`,
  `inspect_svg.py` and `motion_inspector.py`;
- added: `Test/Audit/GraphControls.lean`, imported from `Test/All.lean` after
  `Test.Audit.GlyphControls`;
- edited: `tools/Tools/View/Glyph.lean` (a docstring citation), `tools/Tools/ArchitectureRoles.lean`
  (the `docs/design` area goes), `tools/view/README.md` (one paragraph).

V2 (`9a04ea172`):
- deleted: `ocaml/engine/kit/kit_view.ml`;
- edited: `ocaml/engine/kit/dune`, its `modules` line;
- edited: `ocaml/engine/kit/bin/eff.ml`: the `view` command goes, and the header points at
  `tools/view/v`;
- edited: `ocaml/engine/test/kit/test_kit.ml`: T12, the page's three checks, goes with the page;
- edited: `ocaml/README.md`, the kit's row.

The receipt (the head): this file, `proof-graph-layout-timer.lean.txt` and
`proof-graph-ranks.py.txt`, force-added.

## 4. V1: the proof graph, measured

**The graph.** It is the one the d3-dag page draws by default (`tools/Tools/ProofGraphView.js`,
`visible` and `reduce`). Its nodes are the 14 requirements and the 1,543 plan nodes they reach.
Its edges are each requirement's to its top and placed nodes, and the covering edges among the
plan nodes. The nodes stand in a topological order, requirements first, so every edge is
forward.

**The input.** `.lake/gen/semantics-report/semantics.json`, copied from the coordinator's checkout
(written 2026-10-18 02:57), SHA-256 `f87ea34e…aeec3c40`.

**The timer.** A module called from the `architecture-map` executable, compiled, never committed:
[proof-graph-layout-timer.lean.txt](proof-graph-layout-timer.lean.txt) holds it, its hook and the
commands. A requirement count `k` takes the reach of the first `k` requirements.

| k | nodes | edges | items | orders | `Graph.layout` | canvas |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 140 | 276 | 515 | 5 ms | 67 ms | 8,992 × 1,488 px |
| 3 | 207 | 402 | 884 | 15 ms | 301 ms | 13,920 × 1,488 px |
| 4 | 372 | 861 | 1,890 | 79 ms | 3,477 ms | 34,128 × 1,488 px |
| 6 | 546 | 1,351 | 3,264 | 223 ms | 28,250 ms | 150,096 × 1,488 px |
| 14 | 1,557 | 3,940 | 13,161 | 3,193 ms | unfinished: stopped after 598 s of CPU, and again after 240 s | none |

An item is a node, or a point where a long edge crosses a rank. Every graph has 21 ranks. The
`Graph.layout` column includes the ranks and orders that it computes again.

**Where the time goes** (`--stages`, compiled):

| k | items | links | `Place.conflicts` | `Place.centres`, which calls it |
| --- | --- | --- | --- | --- |
| 4 | 1,890 | 2,379 | 3,370 ms | 3,605 ms |
| 6 | 3,264 | 4,069 | 28,725 ms | 29,564 ms |

- `Place.conflicts` (`tools/Tools/View/Place.lean`) marks Brandes and Köpf's first-type conflicts.
  It scans every rank for every pair of an outer and an inner link, and returns a list.
- From k = 4 to k = 6, the items grow 1.73 times and the layout time 8.1 times: about the 3.8th
  power of the items.
- The widest rank of the whole graph holds 1,575 items (rank 2;
  [proof-graph-ranks.py.txt](proof-graph-ranks.py.txt), which reproduces Lean's item counts).
- 32 of the requirements' 1,532 listed edges repeat, since a node can be both a top and a placed
  node. The timed graphs keep both, so 3,908 of the 3,940 edges are distinct. A figure keeps one
  of each pair, since both draw the same relation.
- The interpreted run (`lake env lean --run`) of the whole graph was stopped after 312 s of CPU.

**What it does not establish.** The times are one machine's, under the shared build slots. The
k = 14 entry is a lower bound, not a time. The power is a fit of two points, not a complexity
bound.

**The decision, for the owner** (ruling 1 of 2026-10-18 stands: Lean's layout only):
- (a) Make `Place.conflicts` near linear inside the graph interface's work. Brandes and Köpf's
  first step does it in one sweep per pair of ranks, with positions by a map and marks in a set.
  Then measure again, and land V1 as briefed if the whole graph lays out within ten seconds.
- (b) Show the whole reach as a table, as row 365 (2) already rules for a requirement's reach.
  Draw only bounded figures, such as a requirement's open spine.
- (c) Keep the d3-dag page until the proposal decides (what this branch does now).

Recommendation: (a), since any graph beyond about 400 nodes meets the same cost. The proposal
should also decide the reach's form, since a rank of 1,575 items stays wide at any speed: (b) is
the fallback.

## 5. Commands and results

All from `/Users/pooks/Dev/wt-view-seat`; Lean through `python3 /private/tmp/seams-lean-one.py`.

| Command | Result |
| --- | --- |
| `lake build Drivers.View Drivers.Site Drivers.GlyphSheet Drivers.Live Drivers.DocSpecimen` at the base | 672 jobs, exit 0 |
| `lake build Drivers.View Drivers.Site Drivers.GlyphSheet Drivers.Live Drivers.DocSpecimen Tools.View.Glyph Tools.ArchitectureRoles Tools.Architecture Test.Audit.GraphControls` (V0) | 677 jobs, exit 0 |
| `lake env lean` over `#axiom_audit` and `#axiom_audit checked` of `Test.Audit.GraphControls` | section 6 |
| `python3 scripts/check-language.py --show tools/view/README.md` | the 2 findings of the studio's older sentences; none in the new paragraph |
| `python3 scripts/check-docs.py` after V0 | FAIL: 8 stale references, all in `docs/core/decisions.md`; 4 are the `docs/design` citations, 4 predate this branch |
| `lake build architecture-map` with the timer's hook | 47 jobs, exit 0 (the hook is not committed) |
| `architecture-map --measure-proof-graph … k`, k = 1, 3, 4, 6, 14 | section 4 |
| `architecture-map --stages … k`, k = 4, 6 | section 4 |
| `lake build architecture-map` from the committed source, after the timings | 10 jobs, exit 0; the hook is gone |
| `opam exec --switch=effect4 -- dune build engine/kit engine/test/kit` (V2, in `ocaml/`) | exit 0 |
| `make check-ocaml` (V2) | exit 0: native and compiler reuse shared passes (`a4e24ff31017`, `89da8fa87d3e`); ocaml runs and records `ae613baff3be` (50.9 s); `test_kit`: 48 checks, 0 failures; the sealing check refuses its 12 hostile clients; no tracked file regenerated |

## 6. Axiom output

`#axiom_audit Test.Audit.GraphControls`: 29 declarations within `[propext, Quot.sound]`, 0 of them
modulo planned goals; 0 planned goals. The checked mode agrees with the walk at 1,864 constants.
No module under `src/` changed.

## 7. Pictures

No picture changed. V3, the slice whose specimen the brief asked to draw before and after, is
dropped. V1 shipped no figure.

## 8. The controls moved from the probes

Each probe was read before it was deleted. A probe that held the only control of a law left one
line in `Test/Audit/GraphControls.lean`; the line names the probe at `git:4a81cc034`.

| Law | Module | The control | From |
| --- | --- | --- | --- |
| `movingEnvelope_contains` | `GraphSeparation` | an origin past both endpoints lies outside the envelope | `GraphSeparationProbe` |
| `firstFrameOverlap_none_iff` | `GraphSeparation` | two swapping boxes are apart in both frames and collide between them | `GraphSeparationProbe` |
| `input_iff`, `laid_iff` | `GraphCheck` | a node keyed as a long edge's point passes input and is refused at layout | `GraphLibraryProbe` |
| `reserveCanvas_notShrink` | `PaintBounds` | a self-loop's hull passes the routing width, and the canvas holds it | `GraphLibraryProbe` |
| `prepare_legacySample_eq_legacyReference` | `GraphMotion` | the legacy sample draws two boxes over each other; the production sample keeps them apart | `GraphTransitionProbe` |
| `project_provenance` | `GraphRegions` | a collapsed region joins a path that no original path matches | `GraphRegionsProbe` |

The other probes held readers, finite evaluations, timings and audits. `GraphOrdering.reorder_eq`,
the packing laws and the attachment index laws have no premise a probe tested. `GraphContent`,
`GraphContact`, `GraphText` and `GraphBounds` state no law.

## 9. Proposed decisions rows

The register is the coordinator's. Three rows are proposed.

1. **Rows 369, 370 and 374 superseded.** The tube language's removal (`595c0cb1d`, tag
   `archive/tube-language`, 2026-10-14) retired the tube body, its styling and its pegs. The
   owner's ruling of 2026-10-18 (the backlog note's section 7, ruling 3) wipes `docs/design/`
   (`d8416c1f7`). Row 354 (1), one design-language authority in `docs/core/`, is withdrawn by the
   same ruling: no new authority document is written. The rulings that stand are rows 354 (2) to
   (10), 362 to 365 and 380, and the looks' token files.
2. **The view pared back** (the owner, 2026-10-18, relayed by the coordinator). The view keeps one
   graph layout, `Tools.View.Graph.layout`. A run, the journal's or the host's, is a plain table,
   not a graph. The graph's interface is designed before anything new is drawn. Row 380 (3), the
   fork and join marks, and row 380 (8), the view from the language's objects, wait on that
   design. `Kit_view` and `eff view` are deleted (`9a04ea172`), as ruling 1 asks.
3. **The proof graph's layout, measured** (this receipt's section 4). The map's proof graph does
   not lay out in under 10 s, so the d3-dag page stays. The owner chooses among section 4's
   options (a), (b) and (c).

## 10. What is open, and what evidence is bounded

- V1 waits on the decision of section 4. `tools/Tools/ProofGraphView.js` and `.css`, their jsdelivr
  imports of d3 and d3-dag, and `scripts/check-proofgraph-input.mjs` stay.
- 24 force-added research notes cite `docs/design/`. They are history, and this branch leaves them.
- `docs/STATE.md` (its section on the design language of documents) still lists slice D1, which
  ruling 3 withdraws. The brief leaves STATE to the coordinator.
- The six battery lines are finite controls. They establish no law.
- The timings are host measurements on one machine (section 4).
- `make check-ocaml` covers the kit's library and its test. No outside oracle reads the deleted
  page.
