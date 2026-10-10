# The live view: its theory, what the probes measured, and a kit to land (2026-10-10)

## The one thing

The checker is already live: a fill splices its table in 1 to 4 ms. The view is not. It runs as
one batch process per sequence and redraws every frame whole, with quadratic passes. It writes
every picture of motion whole too. Its picture is already a fold with rigid parts, and its
structured part never crosses. So the live loop needs no new theory of the picture. It needs
four facts, each probed here:

- **an edit leaves most of the page standing**;
- **a moved part draws the same, moved**;
- **a patch reproduces the next frame exactly**;
- **the page's own columns must not look ahead**.

`LANDING.md` holds the kit: eight modules, each checked equal to the tree's function it replaces.

## 1. The experience, as a contract

Each requirement is a formal property of the loop: edit, check, page, layout, drawing calls,
device rows, pixels.

| Requirement | Formal property | Literature (from memory, not filed) | State at the start of this note |
| --- | --- | --- | --- |
| immediate | an edit reaches the screen within one perceptual moment, about 100 ms | Card, Moran and Newell; Tanimoto's levels of liveness | batch: 5 to 9 s a sequence, 0.1 to 1.6 s a frame in the interpreter |
| local | the work of an edit is proportional to what it changes | Reps, Teitelbaum and Demers 1983 (incremental attribute evaluation); Acar 2005 (self-adjusting computation) | the checker is local; the view redraws everything |
| stable | an unchanged part keeps its place up to one rigid move; the page's parameters are causal | Misue, Eades, Lai and Sugiyama 1995 (the mental map); Diehl and Görg 2002 (dynamic graph drawing) | rigid, measured; the columns look ahead |
| exact motion | a moved part's drawing is its old drawing, moved | equivariance of a drawing under translation | `lowerCall_move` proved; strokes measured |
| truthful | a crossing marks a crossing in the program | series-parallel drawings (Bertolazzi, Cohen, Di Battista, Tamassia and Tollis 1994); book embeddings (Bernhart and Kainen 1979) | measured: only non-nested joins cross |
| invariant runs | a run's picture does not depend on a schedule that the observation does not see | Mazurkiewicz traces; stuttering (Lamport); event structures (Winskel) | measured: histories differ by stuttering |

## 2. What the probes measured before any change

The programs are the wire corpus (`Effect4.Program.Wire.Corpus.all`) and three generated families:

- `chain n`: n forks, each awaited at once;
- `forksThen n`: n forks, awaited last first;
- `forksInOrder n`: n forks, awaited first first.

All timings are Lean's interpreter (`lake env lean`), on a shared machine at load 5 to 9. So the
ratios within one run carry the evidence, not the sizes. The probes are in `probes/measure/`,
with their outputs.

| Fact | Evidence | Number |
| --- | --- | --- |
| the checker is local | `measure/Live.lean` | 1 to 4 ms for an edit's answer |
| the frame is not | `measure/Live.lean` | chain 12, last frame: page 38 ms, flow 63 ms, drawing calls 713 ms, device rows 169 ms |
| motion multiplies the cost | `tools/Drivers/View.lean`, `writeFrames` | 19 whole pictures between two frames by default |
| unchanged parts move rigidly | `measure/Live.lean` | 0 of 1,056 parts split across or down (chain 12) |
| the batch's columns look ahead | `Build.frames`, `ownGutter` | the gutter changes 12 to 24 times as a program grows |
| organic strokes cost most | `measure/Split.lean` | routes 4.5 to 32× the plain strokes; `Grow.isqrt` starts Newton's steps from `n` |
| strokes commute with a move | `measure/Equi.lean` | 160 of 160 cases, at the stroke's thousandths |
| the structured part never crosses | `measure/Cross.lean` | 0 crossings of two forward routes in 12 programs |
| crossings mark non-nested joins | `measure/Cross.lean` | `forksInOrder 3`: 2 lane routes, 2 crossings; `forksThen 5`: no lane |
| run histories differ by stuttering | `measure/Pomset.lean` | children equal; root 25 against 21 frame events; traces 61 against 53 |

## 3. The theory, finding by finding

### 3.1 An edit leaves most of the page standing

A node's own text depends on its constructor and its arguments that are no child. An edit at `a`
changes neither at any node outside the subtree at `a`, ancestors included. An await's targets
depend on the binders along its address. An edit adds or removes binders only inside its
subtree, and their scope does not leave it. So the page's lines and the flow need new work only
under `a` (`probes/src/ProbeView/Inc.lean`).

This is the view's twin of the table's splice (`Sketch.table_fill`). The splice stops where the
focus keeps its type; the view's folds stop where the subtree ends. Both are the quiescence of an
attribute grammar's change propagation. It is Codex's page-update square
(`docs/research/2026-10-10-live-graph-support/THEORY.md` §3), now concrete. `checks/IncCheck.lean`
finds the incremental lines, waits and flow equal to the fresh ones at every step of every build.

### 3.2 A moved part draws the same, moved

The layout lays each part at the origin and lets its parent move it, so parts move rigidly
(§2). The drawing commutes with a move. The lowering does by `lowerCall_move`
(`tools/Tools/View/Picture.lean`). The organic stroke does by a finite check: `Grow.stroke` on
moved segments is the stroke moved by 1,000 times as much, in thousandths. Every step of a stroke is a
difference of points, so a law `stroke_move` holds by the same arithmetic.

Three things follow:

- a stroke can be kept by its segments moved to the origin (`StrokeCache`), and served moved;
- an object can be kept relative to its anchor, and a moved object needs no new calls;
- a panel can be kept relative to its origin, and a panel that moves down moves as one.

### 3.3 A patch reproduces the next frame exactly

A picture read as objects keeps one object per maximal run of calls under one key. Each object
stands in a group, at an anchor, with its calls relative to the anchor. A frame then differs
from the one before by a patch:

- put an object;
- move an object;
- drop an object;
- shift a group;
- insert new objects in the order of painting.

Two checks hold on every step:

- **in Lean**: the old scene, patched, flattens to the new picture (`checks/RetainedCheck.lean`);
- **in C**: a retained store applies the patch rows and writes the frame's stream, byte for
  byte, under the address and behaviour sanitizers (`probes/c/scene.h`, `scene_test`).

### 3.4 The page's columns must not look ahead

`Build.frames` fixes the gutter and the code's column at the widest of the whole sequence. A live
session does not know its future. A causal column grows when it must, in steps, and never
narrows. `Live.ratchet` is proved to cover the page's need (`ratchet_ge_own`) and never to narrow
(`ratchet_ge_before`). It cuts the page's moves across by a third at a step of 8 cells (chain 18:
25 against 37). The gutter grows because an address grows with depth. A bound on the gutter's
text would end those moves, for example an address shown by its last parts. It is a ruling of
how an address reads.

### 3.5 A crossing marks a crossing in the program

The flow is series-parallel apart from its waits and its loops (`Flow.lean`'s own docstring). Its
forward routes never crossed in the probe. A wait that the structure nests (fork, then await,
last forked first awaited) becomes part of the series-parallel flow and draws no lane. A wait
that does not nest (first forked first awaited) draws a lane at the right, and the lanes cross.

This is the correspondence of nested pairs and planar arcs. Two arcs that interleave cross once
on one side of a page, and not at all on opposite sides. So assigning each lane to the left or
right margin by a two-colouring of the interleaving graph removes every crossing of two
interleaved waits. What remains, an odd cycle of interleavings, measures how far the program's
joins are from structured concurrency. This is a proposal: no left lane is drawn yet, and a new
mark waits for the owner.

### 3.6 A run's picture and its schedule

The schedule-independence note (`docs/research/2026-10-10-schedule-independence/README.md`)
shows that independent fibers' decisions commute up to the trace and the minted names. This
probe looks at the histories. Each child's frame events are the same under both orders. The
root's are not: when a child has already exited, the root's join answers at once; otherwise it
parks and resumes. A park followed by its resume, with nothing observed between, is a
stuttering step. So a run's picture that does not depend on the schedule draws the run modulo
stuttering, and modulo commuting decisions. Its frames are then the steps of the run's
dependence order (Foata's normal form), not the decisions of one tape. The machine records no
program address for a fiber: the visual pipeline's gap of V2. So the picture needs each fiber's
point before it can light where a fiber is.

## 4. The kit, in one table

`LANDING.md` gives each module's place in the tree, the declarations it replaces, its check and
its command. Measured within one run of `probes/results/`:

| Module | Replaces or adds | Check | Measured |
| --- | --- | --- | --- |
| `Fast` | `Grow.isqrt`; `Laid.calls` with a key index and a stroke cache | equal on every frame, two looks, one cache over a sequence | a sequence of frames 4.5 to 7.3× faster |
| `Layout` | `Flow.kahn`, `orders`, `preparePlacement`, `placeWith`, `layout` | equal on every intermediate sketch | 1.5 to 11× faster; linear in the items |
| `Inc` | the page's lines, the flow and its waits along an edit | equal to the fresh folds at every step | lines 16 to 23×, waits 16 to 26×, flow about 10× |
| `Retained` | a picture as groups and objects; diff, apply, flatten | the old scene patched is the new picture | 2.3 to 3.2× fewer rows than whole streams on the larger programs |
| `Live` | the resident step: one request in, one patch out | the scene flattened is the tree's `pageCalls` of the same page | 2.2 to 2.6× faster than the batch on the larger programs; mean 37 to 113 ms an edit, interpreted |
| `c/scene.h` | the C side: a retained store, patch rows in, a stream out | byte equality with Lean's stream, under two sanitizers | 59 frames agree; chain 6's patches 5.5× fewer bytes |

## 5. What remains on the way to 100 ms

`checks/StageBench2.lean` times one live step's stages after the kit (chain 24, 193 lines):

| Stage | ms | What would cut it |
| --- | --- | --- |
| the session's answer | 2.2 | nothing: the splice |
| lines and waits | 3.3 | nothing: incremental |
| page and flow | 12.4 | a fold of the page entries along the edit |
| code (the TypeScript print) | 31.6 | the print splice of the tangible authoring note |
| layout | 11.8 | stays linear; a dependency-ordered update after Codex's index |
| drawing calls in groups | 25.0 | build each object once per edit, not each frame |
| scene and diff | 44.5 | build the scene by the same fold, not from a flat list |
| patch rows | 89.0 | compiled code; rows only for what changed |

All of it is interpreted. A compiled driver, a `lean_exe` in `lakefile.toml`, is the largest
unmeasured factor, and it is the coordinator's to add.

## 6. The next slices of theory

1. **Motion in C from data.** A move is a translation, and the C side can interpolate it at
   display rate. Lean writes only the two ends and the choreography, as data it already has
   (`Look.motion`, CSS easings). The law to state: the C side's moment at `t` of a moved object
   is `Tools.View.sample`'s at `t`. New objects keep Lean's enter. This removes the 19 whole
   pictures per step.
2. **Keys that survive a structural edit.** Fill and omit keep every address outside the edit. A
   wrap, an extract or an insertion into a list moves addresses. Each edit then answers its
   tracking map of addresses (origin tracking, van Deursen, Klint and Tip 1993; from memory). The
   patch's ids follow the map, so a moved statement slides instead of leaving and entering.
3. **The run modulo stuttering**, with each fiber's point, and its frames as dependence steps
   (§3.6).
4. **Two-sided lanes** by the two-colouring of interleaved waits (§3.5).
5. **Fill and resume.** A hole is a host row, and a run waits at it. Filling the hole the run
   waits at should resume it with the fill's run, as Hazel's fill-and-resume does (Omar and
   others 2019; from memory). It is the substitution law of an operation handled by a program, and
   R14's `fill-by-term`.

## 7. What the owner must decide

- **A compiled live driver**: a `lean_exe` for `tools/Drivers/Live.lean` in `lakefile.toml`.
- **The C side interpolates moves**, under an agreement law with Lean's `sample`. Today the C
  side decides nothing; it would then compute the moments of a translation.
- **How an address reads** in the gutter, so the gutter stops growing with depth.
- **Code lines keyed by their text**, so the code panel keeps unchanged lines. Only keys change.
- **Lanes on both sides** for interleaved waits: a new mark.

## 8. What this note does not establish

- **The timings are the interpreter's** on a loaded machine. Only ratios within one run are
  evidence. No compiled timing exists.
- **The equalities are finite checks** on the corpus and three generated families of programs. The
  laws they point to (`stroke_move`, the patch law, the incremental folds' law, the layout's
  agreement) are not proved, except the ratchet's two.
- **The C store's agreement is byte equality on 59 frames.** It is no proof about every patch.
- **The lane and run proposals are designs.** Neither is drawn.
- **Placement**: the view's layout is a tool's (decisions row 334, point 3), so its laws are
  statements of the tool, not registry claims. The run view's stuttering projection and fill and
  resume touch the semantics, and are placed as claims when they are worked.

## 9. Evidence

| Item | Command | Result |
| --- | --- | --- |
| the measurements before the kit | `lake env lean probes/measure/NAME.lean` | `probes/measure/*.out` |
| the kit's modules | `sh probes/run.sh` | built into `probes/build/` |
| the kit's checks and timings | `sh probes/run.sh FastCheck LayoutCheck IncCheck RetainedCheck LiveBench StageBench2 PatchFiles` | `probes/results/*.out`, every one exit 0 |
| the C store | `sh probes/c/check.sh` | `probes/results/scene_test.out`: 59 frames agree |
| the base | `git rev-parse --short HEAD` | `probes/results/env.txt` |
