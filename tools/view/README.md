# The view

Frames of a program as it is built and as it runs, in a window, a terminal or files. A picture
is data computed in Lean (`tools/Tools/View/`). The C programs here replay it and decide nothing.
The design and its rulings: `docs/research/2026-10-09-visual-pipeline.md` and decisions row 336.

## Prerequisites (macOS)

- Lean through elan: `lake` on the `PATH`. The command `v` also finds `~/.elan/bin` itself.
- From Homebrew: `pkg-config`, `cairo`, `pango` and `cmake`.
- The network, once: the first build fetches SDL3's pinned source, verifies it and builds it
  (`vendor/SDL3-3.4.16/build.sh`, about 40 seconds).

## Commands

Run from the repository's root. `v` builds what is stale, writes the frames to
`tools/view/out/`, and shows them.

```sh
tools/view/v pFork          # build a corpus program top-down, in a window
tools/view/v -r pFork       # run it step by step: the program and its graph of fibers
tools/view/v -g             # the graph specimen: a graph built one edge at a time
tools/view/v -t pFork       # the frames in this terminal
tools/view/v -p pFork       # a PNG of every frame and every picture of motion
tools/view/v -f FILE        # the frames of a session request file
tools/view/v -P -m 1 pLoop  # no marks; no motion
```

In the window: Right or Space plays the motion to the next frame, Left steps back, Home and End
go to the ends, Q quits. The corpus programs are `p42`, `pBind`, `pFork`, `pAwait`, `pGen`,
`pLoop`, `pCatch` and `pScope` (`Effect4.Program.Wire.Corpus.all`).

## What lives where

| Path | What it holds |
| --- | --- |
| `tools/Tools/View/Picture.lean` | drawing calls and device calls, each with a key; the lowering; the stream and SVG outputs; the move law |
| `tools/Tools/View/Grid.lean` | the grid and every constant a picture is placed by |
| `tools/Tools/View/Page.lean` | a page of lines, its marks, and its terminal form |
| `tools/Tools/View/Graph.lean` | a graph's layout: back edges by the order, ranks, order, places, routes |
| `tools/Tools/View/Motion.lean` | the data join, transitions, easings and the choreography; `sample` and its end law |
| `tools/Tools/View/Program.lean`, `Build.lean`, `Run.lean` | the frames of a program built by edits, and of a run |
| `tools/Tools/View/Specimen.lean` | the graph specimen |
| `tools/Drivers/View.lean` | the driver: frames to `.draw`, `.svg` and text |
| `draw.c`, `play.c`, `replay.h`, `paint.h` | the replay to PNG, the window, the shared replay, the painter |
| `build.sh`, `v` | the C build (every warning an error), and the one command |

## The laws of the picture

Proved in `tools/Tools/View/`, each resting on `[propext, Quot.sound]` or less:

- `lower_key`: each device call keeps its call's key.
- `lowerCall_move`, `lower_move`, `lowerAll_move`: a move by whole pixels commutes with the
  lowering.
- `ranks_forward`: every forward edge of a graph descends a rank.
- `join_new`, `join_old`: every element of two frames is entered, updated or exited.
- `Ease.at_start`, `Ease.at_end`, `Transition.within_at_end`: motion starts at 0 and ends at 1.
- `sample_end`: a step's moment at its end is the next frame.

The layout is a tool's (decisions row 334): these laws are statements of the tool, not registry
claims.
