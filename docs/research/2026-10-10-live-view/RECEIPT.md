# 2026-10-10 live-view seat receipt: slices LV-0 to LV-7

**The one thing to know before merging:** `play --live` (`tools/view/play.c`) is not compiled
against SDL3 here. SDL3's first build fetches its source over the network
(`vendor/SDL3-3.4.16/fetch.sh`), and I did not run that fetch without the owner's yes. So
`v -w` and every window of `v` are not run. Before the merge, run `tools/view/build.sh play` and
`tools/view/v -w pFork` once. Every other part of the seven slices is built and checked:

- each planned law is proved within `[propext, Quot.sound]`;
- the batch driver writes the base's bytes on 19 runs;
- C's store writes Lean's streams byte for byte on 118 frames.

## Base and head

- Branch `claude/live-view`, worktree `/Users/pooks/Dev/lean4-effect4-wt/live-view`.
- Base `c5841c4a6`. Head: the commit that adds this receipt, after `51ffbf08c`.

| Slice | Commit | What it lands |
| --- | --- | --- |
| LV-0, LV-1 | `2cff0c00a` | equality instances; `Grow.isqrt` from above the root; running lengths in reverse |
| LV-2 | `ae862def3` | the graph's calls on a key index and a stroke cache; `Grow.stroke_move` |
| LV-3 | `171399304` | the layout's tables; `ordersTable_eq`, `assignTable_eq`, `heightTable_eq` |
| LV-4 | `901da444d` | the folds along an edit, with Codex's repair LV-OW-01; the text law |
| LV-5 | `b82df687f` | the retained scene; `of_flatten`, `apply_diff` |
| LV-6 | `0a0c0c463` | the live step and its driver |
| LV-7 | `d862eb6d6` | `scene.h`, `scene_test.c`, `play --live`, `v -w`, `v -c` |
| after LV-7 | `51ffbf08c` | `v` builds only what a mode needs; the probes lose LV-0's equality instances |
| receipt | the head | this receipt |

## Changed files

| File | Slice | What changed |
| --- | --- | --- |
| `tools/Tools/View/Picture.lean` | 0, 2, 5 | `Call`, `Keyed` derive `DecidableEq`, `Cubic` derives `Hashable` (LV-0); `Cubic.move_move`, `Cubic.move_zero` (LV-2); `Call.move_move`, `Call.move_zero` (LV-5) |
| `tools/Tools/View/Graph.lean` | 0, 2 | six types derive `DecidableEq`; `Laid.Ix`, `StrokeKey`, `StrokeCache`, `cachedStroke`, `callsCached`; `segments`, `organicCalls` and `routeCalls` read a `find` and an `onBar`; `calls` is `callsCached` on a fresh cache |
| `tools/Tools/View/Flow.lean` | 0, 3, 4 | `Flow` derives `BEq`, `PreparedPlacement` derives `DecidableEq`; `kahnTable`, `ordersTable`, `assignTable`, `heightTable`, `heightIn`; `orderFor`, `preparePlacement`, `placeWith` and `layout` read them; `flowLayer` is `flowLayerWith` at a computed leaf text |
| `tools/Tools/View/FlowLaws.lean` | 3 | the three connectors and their steps; new proofs of `orderFor_serves`, `preparePlacement_height`, `place_placed`, statements unchanged |
| `tools/Tools/View/Organic.lean` | 1, 2 | `isqrt` from `2 ^ (log₂ n / 2 + 1)`; `steps`, `runningLengths`; the stroke split into `samples`, `sidePoint`, `outline`, `through`; the move law |
| `tools/Tools/View/KeyMap.lean` | 2, 5 | new: a table by key on `Tools.Graph.Index`, and `Index.modifyBucket`, with their lookup laws |
| `tools/Tools/View/Page.lean` | 2 | `graphCallsCached`, `pageCallsCached`; `graphCalls` and `pageCalls` draw on a fresh cache |
| `tools/Drivers/View.lean` | 2 | `writePage` and `writeFrames` thread one stroke cache through the frames and the moments of motion |
| `tools/Tools/View/Inc.lean` | 4 | new: the memo, the lines and the flow along an edit, and their laws |
| `tools/Tools/View/Retained.lean` | 5 | new: objects, groups, scenes, the patch, and their laws |
| `tools/Tools/View/Program.lean` | 6 | `sessionPageOf` takes the lines; `sessionPage` gives it its sketch's |
| `tools/Tools/View/Live.lean` | 6 | new: the live step, `ratchet` and its two laws, the patch rows |
| `tools/Drivers/Live.lean` | 6 | new: the live driver |
| `tools/Tools/View/LiveChecks.lean` | 2 to 6 | new: each slice's checks at every frame of the view's builds, with their controls |
| `tools/view/scene.h`, `scene_test.c` | 7 | new: the probe's store and its check, their comments set to the tree |
| `tools/view/replay.h` | 7 | `replay_file`; `replay_stream` and `replay_memory` read through it |
| `tools/view/play.c` | 7 | `play --live`; `show_surface` shared by both modes |
| `tools/view/build.sh` | 7 | named targets; `scene_test` with the two sanitizers |
| `tools/view/v` | 7, after | `-w`, `-c`; each mode builds only the program it runs |
| `tools/view/README.md`, `.gitignore` | 7, after | the live loop, its modules and its laws; what needs SDL3; the check's build products |
| `docs/research/2026-10-10-live-view/probes/…` | after | LV-0's equality instances removed from `ProbeView.Fast`, `LayoutCheck` and `IncCheck`, as LANDING.md says |
| `…/probes/checks/Landed*.lean`, `…/probes/results/Landed*.out`, `LayoutCheck.head.out` | receipt | the benches of this receipt's timings at the landed modules, and their outputs |

Three Lean files outside the slices' named targets changed, each for a named step:

- `Page.lean` threads the cache (`pageCallsCached`) for `writeFrames`.
- `Program.lean` holds `sessionPageOf`, which LANDING.md lists under LV-6, beside `sessionPage`.
- `KeyMap.lean` gives the laws a table whose lemmas stay within the ceiling.

`Std.HashMap.getElem?_insert` reaches `Classical.choice` on this toolchain (tested by the axiom
walk), so the laws cannot use `Std.HashMap`.

## How LV-4 takes Codex's repair LV-OW-01

Codex's review (`docs/research/2026-10-10-live-view-invalidation-review/README.md`) asks for five
things. Each landed as follows:

| The review asks | Where it landed |
| --- | --- |
| keep the cached texts | `Inc.Memo` keeps each line's own text by its address; `Inc.lines` reads it outside the edit |
| recompute the waits after every edit | `Inc.flow` takes its waits from `Flow.waits` at every edit |
| keep text validity and wait validity apart | `Inc.MemoValid` speaks of texts alone; no property of waits exists, since none is cached |
| remove the wait cache's fields | `Inc.Memo` has one field, `texts` |
| expose no parameter that claims to control reuse | `Inc.lines` and `Inc.flow` take the memo and the edited address, nothing else |

`SiblingWait.lean`'s controls run as `#guard`s in `Tools.View.LiveChecks`:

- the spliced edit at `[0]`, with the await kept at `[1]`;
- the stale edge and the missing edge, each a flow with the other program's waits;
- the flow along the edit, both ways, equal to the fresh flow;
- the text law's premise: a memo from the other program gives other lines.

## Commands and results

All runs were in the worktree, one Lean process at a time, with `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build` of each touched module and its dependents, after each slice | `Build completed successfully` each time, warnings as errors |
| the batch driver's 19 runs at the base and after LV-2, LV-3, LV-4 and LV-6 (below) | 0 runs differ; 6949 files and 19 logs equal |
| `tools/view/v -c NAME` for the eight corpus programs | 37 frames agree |
| `tools/view/v -c -f chain6.jsonl`, `-c -f forks4.jsonl`, `-c -l classic pFork` | 44, 30 and 7 frames agree |
| `play.c` type-checked, strict warnings, against a header that declares the SDL3 functions it calls | the base's `play.c` and the new one pass |
| the live loop without a window over pFork's rows, against `draw --png` of Lean's streams | 7 of 7 PNG files equal |
| `tools/view/v -t pFork` at the head | 7 frames, 19 pictures between each two, the frames printed |
| `tools/view/v -p -F` at the head | 10 frames, 181 PNG files |
| `sh docs/research/2026-10-10-live-view/probes/run.sh` at the head | the five probe modules build |
| `sh …/probes/run.sh IncCheck LayoutCheck` at the head | IncCheck's guard passes; LayoutCheck: equal on 4 of 4 |
| `#axiom_audit` and the theorem walk at the head (below) | every theorem within the ceiling |
| `#closure_audit` over the ten touched modules | 2749 declarations; none binds a table before a returned closure |
| `lake env lean` on `probes/checks/LandedLiveBench.lean`, `LandedStageBench.lean`, `LandedCacheBench.lean` at the head | the timings below |
| `python3 scripts/check-language.py --strict` on this receipt and `tools/view/README.md` | no finding |

The 19 batch runs are `lake env lean --run tools/Drivers/View.lean` at the default motion:

- `build NAME` for each corpus program, `specimen`, `flows`, `run pFork`, `run pScope`;
- `--look classic build pFork`, `--look classic build pScope`, `--look orthogonal build pFork`,
  `--look straight build pAwait`;
- `session` of the request files of `chain 6` and of `forksInOrder 4`, and the latter at
  `--look classic`.

After LV-0 and LV-1, 13 of the 19 runs ran and agreed. I edited the driver while the run went on,
and the other six failed to start. Each later comparison covers them.

The brief asks that `v -t pFork` and `v -F` play after LV-2 and LV-3. At those commits `v` built
`play` before every mode, so even `v -t` would have fetched SDL3. The batch runs `build pFork`
and `flows` stand in for them there: after LV-2 and LV-3 they wrote the base's bytes. At the head,
`v -t pFork` and `v -p -F` run, and `v -F` in a window waits for SDL3.

## Axiom output

`#axiom_audit` at the head, each module in turn, in one file that imports `Tools.View.LiveChecks`:

| Module | Result |
| --- | --- |
| `Tools.View.Picture` | 516 declarations within `[propext, Quot.sound]` |
| `Tools.View.KeyMap` | 62 within |
| `Tools.View.FlowLaws` | 368 within |
| `Tools.View.FlowOrder` | 66 within |
| `Tools.View.FlowPath` | 70 within |
| `Tools.View.Retained` | 407 within |
| `Tools.View.Organic` | 1 of 120 refused: `Grow.seedOf`, through `String.foldl`, as at the base |
| `Tools.View.Graph` | 8 of 479 refused: the base's seven rendering definitions and `Laid.callsCached`, through `seedOf` and `String.length` |
| `Tools.View.Flow` | 8 of 504 refused: the base's seven and `flowLayerWith`, through `ownText` and `String.length` |
| `Tools.View.Inc` | 2 of 236 refused: `Inc.lines` and `Inc.flow`, which apply `ownText` |
| `Tools.View.Live` | 7 of 79 refused: rendering definitions, through strings, `Lean.Json` and `Inc.lines` |

`Tools.View.Retained` audited alone gives 408. The 408th name, `Tools.View.KeyMap.get?.congr_simp`,
is listed again by `Tools.View.Graph`. The audit gives it to the later module (`auditedFacts`,
`tools/ProofGraph/Audit.lean`), so it is audited there.

The theorem walk (`ProofGraph.reachedAxiomsMany`, the gate's walk) covers every declaration of
fourteen modules. They are the twelve that the landing touched or added, and `FlowOrder` and
`FlowPath`, which import `Flow`:

- 1301 theorems of 3301 declarations; no theorem reaches an axiom outside the ceiling;
- no declaration rests on a planned goal;
- 67 definitions reach `Classical.choice`, every one through a string function or `Lean.Json`.

The 67 are 43 rendering definitions of the base and 24 new ones that call them. The new ones are
`Laid.callsCached`, `graphCallsCached`, `pageCallsCached`, `Flow.flowLayerWith`, `Inc.lines`,
`Inc.flow`, seven of `Live` and eleven of `LiveChecks`.

## Timings

Every time is of Lean's interpreter (`lake env lean`) on this machine, 8 cores, while other
sessions built. The load average ran from 3 to 60, so a ratio within one process means more than
a size. Each bench is a file `docs/research/2026-10-10-live-view/probes/checks/NAME.lean`, and its
output is `probes/results/NAME.out`. I ran each with `lake env lean` at the head. The command
`sh docs/research/2026-10-10-live-view/probes/run.sh NAME` runs it the same way, after the probe
modules build.

### The live step against the batch frames

`LandedLiveBench`, the probe's `LiveBench` at the landed modules, in one process. The batch draws
each frame whole: `Build.frames`, `pageCalls`, `lowerAll`, `stream`. The live loop runs `Live.step`
once a request. The load average was 3.2 at the start and 14 at the end.

| Program | Frames | Batch | Live | Mean step | Worst step | Stream rows | Patch rows |
| --- | --- | --- | --- | --- | --- | --- | --- |
| pFork | 7 | 107 ms | 37 ms | 5.3 ms | 7.4 ms | 747 | 674 |
| chain 6 | 44 | 1072 ms | 739 ms | 16.8 ms | 35.5 ms | 16470 | 8367 |
| chain 12 | 86 | 4893 ms | 4031 ms | 46.9 ms | 152.9 ms | 58965 | 25992 |
| chain 18 | 128 | 43563 ms | 18887 ms | 147.6 ms | 407.4 ms | 128278 | 53700 |

The batch here runs the landed modules, so it has LV-2's and LV-3's gains. The landed step keys
every code line `""`, so it writes more patch rows on the chains than the probe did. The probe keyed
them by text (LV-8): 7207 patch rows on chain 6.

### The live step's stages

`LandedStageBench`, in one process, load average 6.7. Each stage runs alone on the last request of
a build, in milliseconds. The fresh lines and the waits are for comparison: the step runs neither
alone.

| Stage | chain 12 (97 lines) | chain 18 (145 lines) | chain 24 (193 lines) |
| --- | --- | --- | --- |
| the session's answer | 0.4 | 0.6 | 1.1 |
| the lines along the edit (`Inc.lines`) | 0.7 | 1.3 | 2.2 |
| the fresh lines (`Program.lines`) | 1.4 | 2.0 | 3.0 |
| the session page (`sessionPageOf`) | 1.1 | 2.7 | 6.1 |
| the code panel (`codePanel`) | 8.0 | 12.7 | 18.6 |
| the waits (`Flow.waits`), inside the flow | 1.0 | 2.6 | 5.5 |
| the flow along the edit (`Inc.flow`) | 2.1 | 4.5 | 8.6 |
| the layout (`Flow.layout`) | 4.4 | 7.1 | 10.3 |
| the groups (`pageGroups`) | 7.5 | 12.4 | 18.8 |
| the scene (`Scene.ofGroups`) | 6.8 | 10.3 | 14.6 |
| the diff (`diff`) | 4.7 | 7.1 | 10.4 |
| the patch rows (`patchRows`), and their count | 11.4 (197) | 24.3 (311) | 43.8 (439) |
| the whole step (`Live.step`) | 51.3 | 89.4 | 147.0 |

The writing of the patch rows is the largest stage at every size. The code panel and the groups
come next.

### The layout against the probe's

`LayoutCheck` at the head runs the landed `Flow.layout` beside the probe's `FastLayout.layout`, in
one process (`results/LayoutCheck.head.out`):

| Flow | Placed | Landed | Probe's | Base (the probe's run) |
| --- | --- | --- | --- | --- |
| chain 12 | 121 | 7.4 ms | 4.6 ms | 31.2 ms |
| chain 24 | 241 | 15.5 ms | 9.8 ms | 81.5 ms |
| chain 48 | 481 | 35.7 ms | 20.0 ms | 281.5 ms |
| forksInOrder 12 | 87 | 14.7 ms | 12.8 ms | 17.6 ms |

The base column is `results/LayoutCheck.out`, another run at another load. Twice the items take 2.1
to 2.3 times as long in the landed layout, and 2.6 to 3.5 times in the base's. The landed layout
takes 1.2 to 1.8 times the probe's. I did not profile that gap.

### The batch driver at the base and the head

The driver ran `session` of chain 6's request file at the base and the head, alternating. Lake
restored each build from its cache first. Other sessions' builds held the load average between 8
and 20.

| Run | Base | Head |
| --- | --- | --- |
| wall clock, default motion, first round | 181.0 s | 186.6 s |
| wall clock, default motion, second round | 234.8 s | 136.8 s |
| user time, frames only (`--motion 1`), first round | 7.0 s | 10.2 s |
| user time, frames only, second round | 15.4 s | not run |
| user time, default motion, first round | 151.9 s | 171.6 s |

Two runs of one commit differ by up to 2.2 times. So these runs show no ratio between the base and
the head, and I stopped the second round of user times.

### The stroke cache in the batch's pictures

`LandedCacheBench` draws the pictures that `writeFrames` writes, in one process. It draws each on a
fresh cache (`pageCalls`) or on one cache carried along (`pageCallsCached`), then lowers and streams
it. The two ways alternate, two rounds; the load average ran from 18 to 49.

| Build | Pictures | Fresh | Carried | Fresh, again | Carried, again | Strokes kept |
| --- | --- | --- | --- | --- | --- | --- |
| pFork, motion 20 | 121 | 1951 ms | 1781 ms | 2428 ms | 4331 ms | 69 |
| chain 6, frames only | 44 | 7639 ms | 3408 ms | 2961 ms | 2266 ms | 100 |
| chain 4, motion 20 | 581 | 38569 ms | 28046 ms | 34968 ms | 23483 ms | 408 |
| chain 6, motion 20 | 861 | 71309 ms | 39505 ms | 192420 ms | 90163 ms | 614 |

Both ways write the same rows on every build, a check of the bench. On the chains the carried cache
takes 0.45 to 0.77 of the fresh time. On pFork the second round reverses, under a rising load. The
cache keeps every stroke it draws: 614 strokes and 11052 segments after chain 6's 861 pictures.

## Evidence

- **Proved**: each law in the next section, by name, within `[propext, Quot.sound]`.
- **Tested**: no picture of the batch changed, by a byte comparison of 19 driver runs with the
  base's (6949 files). This is finite: the corpus, two generated families and four looks.
- **Tested**: C's store writes Lean's stream of the same page byte for byte on 118 frames, under
  the address and undefined-behaviour sanitizers. No law covers C.
- **Tested**: `Tools.View.LiveChecks` at every frame of the corpus, of `chain 4` and of
  `forksInOrder 3`. It reads each law at real carriers, and checks what no law covers (below).
- **Tested**: the probes' `IncCheck` and `LayoutCheck` against the head.
- **Reading**: `Program.ownText` reads no child, since `argText` answers `none` at a child.
- **Not run**: `play --live`, `v -w` and every window of `v`. Each needs SDL3, and SDL3's first
  build fetches over the network.

## Landed theorems and their placement

Every law below is a tool's, not a registry claim (decisions row 334, point 3).

### The move law of a stroke (LV-2)

`Grow.stroke_move` (`tools/Tools/View/Organic.lean`), with its steps `samples_move`,
`runningLengths_shift`, `side_shift`, `through_shift`, `outline_shift` and `stroke_organic`.

- Concept: `initial-algebras-folds`; property: the drawing commutes with a move, as
  `lowerCall_move` says of the lowering.
- Question: tool law; consumer: `Laid.cachedStroke_eq`.
- Reach: every seed, organic settings, width, centre line and tip, at every move by whole logical
  pixels.
- Does not establish: anything of the collars, which the drawing places outside the stroke.
- Unlocks: R14's live authoring: a stroke kept at the origin serves every frame.

### The index and the stroke cache (LV-2)

`Laid.Ix.find_of`, `Laid.Ix.onBar_of`, `Laid.cachedStroke_eq`, `Laid.cachedStroke_valid`,
`Laid.StrokeCache.valid_empty` (`tools/Tools/View/Graph.lean`), with the steps `Cubic.move_move`
and `Cubic.move_zero` (`tools/Tools/View/Picture.lean`).

- Concept: `initial-algebras-folds`; property: a cache of a fold's answers answers the fold.
- Question: tool laws; consumer: `Laid.callsCached`, which `writeFrames` and the live step thread.
- Reach: every laid graph and key, and every valid cache. A cache is valid when each stroke kept
  is its key's stroke, at any organic settings with the key's noise and wave.
- Does not establish: that `callsCached` as a whole is the drawing on the scans. That rests on
  reading its code, the frames' byte comparison, and the cache check at every frame.
- Unlocks: R14's live authoring.

### The key table (LV-2, LV-5)

`KeyMap.get?_empty`, `get?_insert`, `get?_erase`, `getD_insert`, `contains_insert`, and
`Tools.Graph.Index.bucket_modifyBucket` (`tools/Tools/View/KeyMap.lean`).

- Concept: `initial-algebras-folds`; property: a lookup after an update answers as an
  association list does.
- Question: tool laws; consumers: the cache's, the memo's and the scene's laws.
- Reach: every key type with decidable equality and a hash.
- Does not establish: any bound on time.
- Unlocks: R14's live authoring.

### The layout's connectors (LV-3)

`ordersTable_eq`, `assignTable_eq`, `heightTable_eq` (`tools/Tools/View/FlowLaws.lean`), with
the steps `before_posFrom`, `nodup_posFrom` and `firstAt_positionsOf`.

- Concept: `initial-algebras-folds`; property: the layout's laws (`place_descends`,
  `place_apart`, `place_keeps_order`) hold of the layout the view draws.
- Question: tool laws; consumers: `orderFor_serves`, `preparePlacement_height`, `place_placed`.
- Reach: every order, a repeat included, and every list of edges; every newest-first list of
  heights.
- Does not establish: that `kahnTable` is `kahn`. That is a finite check on every sketch of the
  view's builds; `orderFor` checks the order, so no law needs it.
- Unlocks: R14's live authoring: the layout's time grows about as its items do.

### The text law and the memo (LV-4)

`Inc.linesWith_eq` and `Inc.next_valid` (`tools/Tools/View/Inc.lean`), with `linesWith_map`, the
bridge `child_view` (the layer view's children are `Node.child`'s) and `nodeText_outside`.

- Concept: `initial-algebras-folds`; property: a fold along an edit is the fold, as the table's
  splice (`Sketch.table_fill`) is the check.
- Question: tool laws; consumer: `Live.page`, so `Live.step`.
- Reach: every text of a line that reads no child (`ChildBlind`), and every program. It covers
  every edit `Node.replaceAt a r`, so every fill and every omit, and every memo valid outside `a`.
- Does not establish:
  - the instance at `ownText` as a theorem: its statement reaches `Classical.choice` through
    string functions;
  - that the flow along an edit is the fresh flow, which a check covers at every step;
  - any saving of work.
- Unlocks: R14's live authoring.

### The retained scene (LV-5)

`Retained.of_flatten`, `Retained.apply_diff`, `Retained.ofGroups_wf`
(`tools/Tools/View/Retained.lean`), with `Call.move_move` and `Call.move_zero`.

- Concept: `initial-algebras-folds`; property: the patch from one frame gives the next frame exactly.
- Question: tool laws; consumer: `Live.step`, whose rows C's store applies.
- Reach: `of_flatten` for every picture read as one group at the origin; `apply_diff` for every
  two well-formed scenes (`Scene.WF`); `ofGroups_wf` for groups with distinct names.
- Does not establish:
  - C's store, which byte checks cover;
  - that `patchRows` writes `diff`, which C's check covers;
  - that a page's groups flatten to `pageCalls`, which a check covers at every step.
- Unlocks: R14's live authoring.

### The causal column (LV-6)

`Live.ratchet_ge_own`, `Live.ratchet_ge_before` (`tools/Tools/View/Live.lean`), the probe's two.

- Concept: `initial-algebras-folds`; property: a column covers the page's need and never narrows.
- Question: tool laws; consumer: `Live.step`.
- Reach: every step, earlier column and need.
- Does not establish: which step the owner wants (LV-8).
- Unlocks: R14's live authoring.

## The lakefile lines I propose

The live driver runs under `lake env lean --run` today. A compiled one needs this in
`lakefile.toml`:

```toml
[[lean_exe]]
name = "view-live"
srcDir = "tools"
root = "Drivers.Live"
moreLeanArgs = ["-M6144", "-DwarningAsError=true"]
```

## Open obligations

- `ChildBlind ownText` as a theorem: its statement reaches `Classical.choice`. It stands as a
  reading and as the checks.
- The flow along an edit is the fresh flow: checked at every step. Codex's dependency design
  (`docs/research/2026-10-10-live-view-invalidation-review/DESIGN.md`) states the path to a law.
- `kahnTable` is `kahn`: a finite check.
- A graph's calls commute with a move (`Laid.calls` at an offset): checked through the live step's
  scene at every step; no law.
- C's store against Lean's rows: byte checks. `play --live` is uncompiled until SDL3 is built.
- The stroke cache keeps every stroke it draws, so a long live session's cache grows without
  bound. Two generations, the drawing before's strokes and the drawing's own, would bound it under
  the same laws. I did not land it: chain 6's 861 pictures kept 614 strokes.
- `draw --count` counts shape rows as no call (`tools/view/draw.c`, `count`), at the base too. I
  left it.

## What remains for LV-8

- Code lines keyed by their text: the live step keys every code line `""`, the tree's key. So a
  change of the code puts the whole code panel again.
- Columns: `Live.Settings.columnStep` is 1, the batch's rule read causally, the widest so far. A
  larger step, and whether the batch takes it, wait for the owner.
- How an address reads in the gutter, so the gutter stops growing with depth.
- README §6's next slices: motion in C, keys across structural edits, the run modulo stuttering,
  lanes on two sides, fill and resume.

## Proposed decisions rows (proposals only)

None. LV-8's three rulings stand in LANDING.md.
