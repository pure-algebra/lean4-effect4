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
tools/view/v -l paper pFork # in a look of tools/view/looks/
tools/view/v -L             # every look side by side: tools/view/out/looks/index.html
```

## Looks

Every choice of style is data (`tools/Tools/View/Look.lean`). A look holds the colour of each role,
the faces, the weight of each stroke, the form of an edge, and the timing of motion. A look is a file of
the W3C design-token format, 2025.10, that names only what it changes from the dark look, the
base (`tools/view/looks/`). A token the look does not have, or a value out of its range, is
refused with its path and the reason.

From one look come three outputs, so the native view and the web agree:

- the stream's look rows, from which `paint.h` takes every colour and face; it holds none;
- the SVG's classes (`e4-fill-<role>`, `e4-stroke-<role>`, `e4-face-<face>`) beside the look's
  values;
- CSS custom properties (`--e4-color-ink`, `--e4-motion-move-easing`, …), with the class rules
  that restyle any picture's SVG on a web page.

An edge's form is a curve of d3-shape (`bumpY`, `linear`, `stepY`). An easing is written as CSS's
`linear()` easing function, exact at twenty-one points, and as the nearest cubic Bézier, fitted
by least squares (`Ease.bezier`). Durations are milliseconds; the window paces a step by the
look's step. `v -L` writes each look's whole token file and CSS, and reports whether each look
comes back from its own written file (`look-round-trip`).

A page of a program shows its code beside its tree: the TypeScript the code generator prints for
it, laid out at 80 columns. While a program is built, the code grows with the tree, and each hole
is a call the host answers until it is filled.

The code generator's output, as files to read:

```sh
lake env lean --run tools/Drivers/Emit.lean OUT   # OUT/README.md indexes every program
```

Each program has a module (`OUT/corpus/NAME.ts`) and its tree (`NAME.tree.txt`). A module imports
exactly the names it uses, and its header carries its program's address and type. It is laid out
at Effect's own width, 120 columns. The index says whether the core's reading boundary admits each
module as written.

In the window: Right or Space plays the motion to the next frame, Left steps back, Home and End
go to the ends, Q quits. The corpus programs are `p42`, `pBind`, `pFork`, `pAwait`, `pGen`,
`pLoop`, `pCatch` and `pScope` (`Effect4.Program.Wire.Corpus.all`).

## What lives where

| Path | What it holds |
| --- | --- |
| `tools/Tools/View/Picture.lean` | drawing calls and device calls, each with a key; the lowering; the move law |
| `tools/Tools/View/Look.lean` | the look: palette, faces, strokes, the form of an edge, easings, transitions and the choreography |
| `tools/Tools/View/Tokens.lean` | a look as design tokens (written and read over a base) and as CSS |
| `tools/Tools/View/Output.lean` | the stream and SVG of a picture, in a look |
| `tools/view/looks/` | the looks besides the dark one, as token files |
| `tools/Tools/View/Grid.lean` | the grid and every constant a picture is placed by |
| `tools/Tools/View/Page.lean` | a page of lines, its marks, and its terminal form |
| `tools/Tools/View/Graph.lean` | a graph's layout: back edges by the order, ranks, order, places, routes |
| `tools/Tools/View/Motion.lean` | the data join and the moments of a step; `sample` and its end law |
| `tools/Tools/View/Program.lean`, `Build.lean`, `Run.lean` | the frames of a program built by edits, and of a run |
| `tools/Tools/View/Specimen.lean` | the graph specimen |
| `tools/Tools/Code/Doc.lean` | a document and its layout at a width: groups lie flat when they fit |
| `tools/Tools/Code/TypeScript.lean` | printed TypeScript as a document, case by case with the pinned renderer |
| `tools/Tools/Code/Module.lean` | a generated module: its exact imports, its header, its checks; the code plane |
| `tools/Drivers/Emit.lean` | the driver: the generated folder |
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
- `undo_layout`: undo the breaks a layout took, and the flat print comes back, at every width.
- `Ts.flat_expr`: the flat print of a printed expression is the pinned house print. It rests on
  `Classical.choice` through the pinned renderer it is stated about (`TypeScript.Render.expr`),
  whose character folds the axiom gate exempts by name.

The layout is a tool's (decisions row 334): these laws are statements of the tool, not registry
claims.
