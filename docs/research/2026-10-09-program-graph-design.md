# The program's own graph: design, an agent's place, and the data under it

The owner's request of 2026-10-09, by voice: decide how the program's own graph is shown, from
the visual design literature. Keep the information organized without overwhelming the reader. Give
it coherent semantics, so that a person sees what an agent is doing and where it operates. Choose
the data structures that make this quick, efficient and provable.

Decisions row 337, point 9, rules the graph's meaning. `bind` and statements stand in series. The
branches of `raceAll` and `awaitAll`, and a forked fiber beside its parent, stand in parallel. An
await across branches is a cross edge. This note designs the rest and places its laws. The view's rule
stands: every channel is the image of a fold (`docs/research/2026-10-09-visual-language-theory.md`).

## 1. What the literature says

| Source | Its finding | What we take |
| --- | --- | --- |
| Furnas, generalized fisheye views (1986, recalled) | a node's degree of interest is its own importance less its distance from the focus | an interest per node, computed from the focus |
| Card and Nation, degree-of-interest trees (AVI 2002); Heer and Card, DOITrees revisited (AVI 2004), [paper](https://homes.cs.washington.edu/~jheer/files/2004-DOITree-AVI.pdf) | four tactics: hide low-interest nodes, size by interest, zoom content by size, and show an elided subtree by an aggregate | collapse below a threshold, and draw a collapsed subtree by its summary |
| Shneiderman's mantra (1996, recalled) | overview first, zoom and filter, then details on demand | the graph is the overview; the focus is the zoom; the tree and the code are the details |
| Hazelnut, Omar et al. (POPL 2017), [paper](https://arxiv.org/abs/1607.04180); Hazel, live programming with typed holes (POPL 2019), [paper](https://arxiv.org/abs/1805.00155) | a structure editor's cursor is Huet's zipper; every edit state has a type, holes stand where work is unfinished, and evaluation proceeds around holes | the focus is a zipper over the program; holes are first-class places in the graph |
| Codellaborator (arXiv 2502.18658, 2025), [paper](https://arxiv.org/abs/2502.18658) | an agent's presence, after social transparency theory: a caret at its position, a separate cursor for its attention, a short status beside it | an agent's mark at its address, its attention apart from its edit, and a status line |
| RECAP, git-ai and related tools (2026, vendors' claims) | attribution badges per file, timelines with colours per actor, replayable sessions | the journal as a timeline, each command by its agent |
| Eio's trace viewer, [README](https://ocaml.org/p/eio-trace/0.1/README.html) | fibers as bars, a line from parent to child at each fork, cancellation contexts as brackets | regions drawn as brackets; forks as joins of lines |
| Diehl and Görg; Misue et al.; Steiger et al. on dynamic graph drawing (surveyed, [Steiger](https://otik.zcu.cz/bitstream/11025/6990/1/Steiger.pdf)) | a full relayout breaks the mental map; animation helps when clusters move rigidly; a subgraph should look the same at every visit | layout by fold, so an unchanged subtree keeps its drawing exactly, and moves rigidly |
| Mokhov, algebraic graphs (Haskell Symposium 2017), [paper](https://doi.org/10.1145/3122955.3122956) | every graph is built from empty, vertex, overlay and connect, under eight axioms; no malformed graph exists | the graph as a free algebra, and the program's graph as a fold into it |
| Didimo, Liotta et al., rectilinear drawings of series-parallel graphs, [paper](https://arxiv.org/pdf/2205.07500) | a decomposition tree's bottom-up visit tests and its top-down visit draws, in linear time | sizes as a synthesized fold, places as an inherited one |
| Goodrich, Johnson and Torres, Knuthian drawings of series-parallel flowcharts (arXiv 1508.03931) | loop-free flowcharts are series-parallel, and draw with good aspect ratios and few bends | the same class as a loop-free program's graph |

The finding that matters most: a program's graph needs no general graph drawing. Its
decomposition tree is the program's own syntax tree, which the fold already walks.

## 2. What the graph shows

**Marks.** One node for each leaf operation and each hole, a box as today. Series stacks
downward. Parallel stands side by side between a **fork bar** and a **join bar**, the bars of a
parallel gateway. Alternatives (`catchCause`, `matchCause`, `select`) stand side by side below a
**choice point**, a small diamond, since exactly one of them runs. A loop is a back edge. A
region opens at `scoped`, a fork's fiber, `uninterruptible` and `provideLayer`. It is a
**bracket** around its subgraph, one level deeper on the Z-plane, as Eio draws a cancellation
context.

**Density.** The graph is the overview. Each node has an interest: its region's importance less its
distance from the focus, in the tree. A subtree below the threshold collapses to one box that
shows its **type**. The type is the checker's own summary of what the subtree does, fails with and
needs. So
abstraction in the view is the typing fold's abstraction. The focused subtree is drawn whole.
The tree's lines and the code plane give the details of the focus.

**Two graphs, linked.** The program's graph and the run's graph of fibers stand side by side,
each keyed by address. A fiber's node names its fork site, which is an address of the program
(`ForkRecord.site`). Pointing at either lights both: linked views.

## 3. Where an agent works

An agent's place is a **focus**, a zipper over the program: the subtree at an address and the path
back to the root. It is drawn as a caret on that node, in the agent's mark. A second mark shows
its attention, the node it reads, apart from the node it edits. A status line beside it says what
it does, in the session's own words ("fill [1 0]: checking").

Each edit is a command of the journal, and the journal is a word of the monoid that acts on the
session (`journal_replays`). The view draws it as a timeline under the graph, one row of commands
for each agent. A node an edit touched carries recency on the Z-plane, fading over two steps (row
337, point 2). Several agents are several foci, each with its own mark. With the hue on, each
agent takes a hue; with it off, a shape.

## 4. The data, and the laws that make it quick and safe

| Structure | What it gives | Its law |
| --- | --- | --- |
| **The algebraic graph**: empty, vertex, overlay, connect, with Mokhov's axioms as equalities of edge sets | a graph with no malformed edge, composed as the program composes | each axiom holds of the edge-set model; the program's graph is a fold, so a composite's graph is built from its parts' |
| **The program's graph as a fold** of `Eff` into the algebraic graph | series and parallel by construction; regions and alternatives as labels | its decomposition is the program's tree; no search for one |
| **The layout as two folds**: sizes up (width, height, ranks by `max` and `+`), places down (an inherited offset), as `Program.lines` takes its address | layout in time linear in the program | boxes stand apart, and every edge stays inside its composition's box: no crossing, by fold induction (`cata_keeps`) |
| **Equivariance** of the layout, as `lines_at` is of the lines | a subtree draws the same at every place, moved | a splice redraws its own subtree and shifts its siblings rigidly: the mental map holds by proof |
| **Memoized folds by content address** (the store's SHA-256 of each subtree) | each distinct subtree laid out once; shared pieces cost nothing twice | the cached fold equals the fold (uniqueness, `hom_eq_cata_eff`) |
| **The zipper** over the program, its path an address | moving the focus and editing at it in constant time; refolding only the path to the root | a zipper's plug gives back the program; the focus is always a valid address |
| **Interest as a fold** with the focus inherited | collapse and summary computed with the layout, in one product fold (`cata_prod`) | a collapsed subtree shows its checked type |
| **The journal** as a monoid word, its prefixes the frames | replay, attribution by agent, timelines | the frames of a journal are its prefixes' sessions |

Each structure is first-order data, and each operation is a fold or a step of the session. So an
agent's tools, the view and the proofs read one representation. The MCP design (seat MCP, in
progress) takes the same structures as its surface.

## 5. Slices

| Slice | What | Consumer |
| --- | --- | --- |
| D1 | the algebraic graph: its four constructors, its edge-set model, and Mokhov's axioms proved of the model | every graph the view draws |
| D2 | the program's graph as a fold of `Eff`, row 337's reading, with regions and alternatives as labels | the program graph page |
| D3 | the layout as two folds; boxes apart and edges inside, by fold induction; equivariance | the drawing, the splice's motion |
| D4 | interest and collapse, in a product with the layout; a collapsed box shows its type | density |
| D5 | the focus as a zipper, an agent's marks and status, from the session's journal | presence, and the MCP surface |
| D6 | memoized folds by content address, with the agreement law | speed on large programs |
| D7 | the linked views with the run's graph | understanding a run against its program |

D1 to D3 come first; they need no new mark beyond the fork and join bars.

**Landed (2026-10-09)**: D2 and D3, with every wait handled (`tools/Tools/View/Flow.lean`). Across,
the layout is a fold. Down, it is the longest path over the flow's edges and its waits, so an
await stands below the fiber it waits for. A wait the parent's series makes is a join; any other
is a cross edge in a lane, with an arrowhead. Variables are de Bruijn levels, read through the
binder table, with a closed child starting an empty environment. The specimen (`v -F`) draws
each case. D1 (the algebraic graph with its laws) and D3's laws are next.

## 6. Rulings the owner must make

The owner chose to go with the recommendations on open decisions (row 337). These are the new
marks this note recommends, for confirmation:

1. **Parallel and choice**: a fork bar and a join bar around parallel branches; a small diamond
   above alternatives.
2. **Regions**: a bracket around a region's subgraph, one level deeper on the Z-plane.
3. **Collapse**: a subtree below the interest threshold drawn as one box with its type; the
   threshold a token of the look.
4. **An agent**: a caret at its focus, a separate attention mark, and a status line. Each agent
   takes a hue only when the hue is on.
5. **Two graphs**: side by side, linked by address.

## 7. What this note does not establish

- The literature rows marked "recalled" are from memory; the others cite the page read, as
  abstracts and excerpts, not whole papers.
- No law of section 4 is proved yet. Each is placed with its consumer; the layout's laws are a
  tool's (decisions row 334, point 3).
- Series-parallel holds for the loop-free fragment. A loop's back edge and an await across
  branches fall outside it, and draw as a back edge and a cross edge.
