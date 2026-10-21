# 2026-10-21 The view as graphs: the derivation and the brief

Status: a design note and a brief. It rules nothing. The evidence words are those of `docs/core/controlled-english.md` §3.8.
The prove-out is `probe-view.lean`, run with `lake env lean` against the built tree on 2026-10-21.
Its outputs are in `out/`: one Markdown file, one JSON file, and a TSV and an SVG for each figure. `out/figures.jpg` is the page as the browser drew it.
The literature is under `sources/`, with its index in `sources/README.md`.

## 1. The one thing to know

One value, folded three ways, is the whole deliverable. The value is a `Tools.Document.Document` (`tools/Tools/Document.lean`) whose blocks are a table and five graphs.
The Markdown fold writes the table and a Mermaid diagram for each graph. The JSON fold writes the rows. The HTML fold draws each graph through the view's one layout, `Tools.View.Graph.layout`, to an SVG.
All three folds exist (decisions row 365). The prove-out used them unchanged, and the drawings in `out/figures.jpg` are theirs.

What the tree lacks is the derivation: the folds from a program's data into the graph blocks. The brief adds those folds, their laws, and the command that writes the three forms. It adds no drawer and no carrier.

## 2. The derivation

### 2.1 The data a graph is read from

A graph is read from a program object and nothing else.

- A `Built` (`src/Effect4/Api/Built.lean`): its program, with the definitions and their roles, and its application, with the row table and the named types.
- The checked call table, `Api.HostSession.callTable` (`src/Effect4/Api/HostSession.lean`): every call instance by its address, with its operation. An operation is a call of a definition or an external row.
- A `LayerTerm` (`src/Effect4/Program/Eff.lean`): Effect's layer calculus as data, one constructor per combinator, each citing its line of `vendor/effect-4.0.0-rc.112/src/Layer.ts`.
- The namespace of a row is the part of its spelling before the dot. The rows of one namespace are one host's typing signature. A service is the name a `serviceMethod` role carries.

### 2.2 Three graphs, each a fold

**The boundary, G∂.** Its vertices are the hosts, the service blocks and the main program. Its edges go from a provider to a consumer.
The fold reads the call table. A body's call of a row gives an edge from the row's host to the body's service. A body's call of a definition of another service gives an edge from that service to the body's service. The main program's calls give edges into `main`.
`probe-view.lean` reads it as `boundary`. On the session object of the to-do it has four vertices and three edges (`out/boundary-plain.gen.tsv`).

**The inside, G∘.** Its vertices are the definitions and the rows, and its edges are the call table's edges. `probe-view.lean` reads it as `callGraph`, and `out/calls.gen.tsv` lists its fourteen edges.
It is the picture of one box of G∂ opened.

**The layer term, Gλ.** Its vertices are the constructor occurrences of a `LayerTerm`, keyed by path, and its edges go from a term to its children. A `ref` is a vertex whose detail names its target, so sharing is visible.
`probe-view.lean` reads it as `termGraph`, by a hand match. The slice writes it with `cata_layer` (`src/Effect4/Program/Fold.lean`).

A run is not a graph. Decisions row 413 shows the journal, the host's calls and the fibers as tables, and this note keeps that.

### 2.3 Composition is overlay

The tree holds Mokhov's algebraic graph, `Tools.View.AGraph` (`tools/Tools/View/AlgGraph.lean`), with its edge-set model and the eight axioms proved of the model.
Its four constructors are the empty graph, a vertex, the overlay of two graphs and the connection of two. Overlay is commutative, associative and idempotent.

Read G∂ in the hypergraph form of Fong 2015 and of Bonchi, Sobociński and Zanasi 2016. A wire is a vertex of its own, named by its tag. A box is a vertex with an edge from each input wire and an edge to each output wire.
Then every layer combinator is overlay.

- `effect(tag, body)` is the box of its service: an edge from each tag the body requires, an edge to `tag`.
- `provide(self, that)` is the overlay of the two graphs. The wires they share by name are one vertex, so the output of `that` meets the input of `self` with no extra rule. That is the pushout of Fong's cospans, read on names.
- `merge(left, right)` is the overlay too. Two boxes into one wire show where last-wins applies (`Context.mergeAll`, `Layer.ts:1600`).
- `provideMerge` is `provide` with the shared wires kept on the outer boundary.
- The boundary itself is the pair of wire sets a term exposes: the inputs it requires and the outputs it provides. `provide` hides the shared wires; `provideMerge` keeps them. The boundary is data beside the graph, the two legs of the cospan, and the graph does not change.

`out/hypergraph.gen.tsv` is this form of the to-do: seven vertices, six edges, three of the vertices wires.

The box form of G∂, the first drawing, is the hypergraph with each wire contracted to an edge. Contraction is a graph operation on the data, so the two drawings are one value read two ways.

### 2.4 The laws, placed

Each law below is placed before it is worked (`AGENTS.md`, Trust). The concept is concept 7 of `docs/core/semantics.md`, `initial-algebras-folds`, where the algebraic graph's laws already sit. The consumer is the `inspect` command of §5 and the site's figures.

| Law | Statement | Kind | Reach |
| --- | --- | --- | --- |
| G1 glue | the hypergraph of `provide(self, that)` is the overlay of the hypergraphs of `self` and `that` | by definition of the fold, a `simp` lemma | every `LayerTerm` |
| G2 merge | the hypergraph of `merge(l, r)` equals that of `merge(r, l)` in the edge-set model | `AGraph.overlay_comm`, already proved | every `LayerTerm` |
| G3 contract | the box form is the wire contraction of the hypergraph form | a definition and a finite check on the to-do | the to-do, then a theorem |
| G4 closure | every row vertex of G∘ lies under a host vertex of G∂ exactly when `ServiceSession.foreign` is empty | a finite check on the to-do, tied to `Built.session_ok_iff` (`src/Effect4/Laws/Api/Session.lean`) | the to-do, then a theorem |
| G5 order | the nodes of a graph block are in Kahn's order of its edges | a definition over `Tools.View.FlowOrder.orderFor`, and the law that the layout's ranks go forward (`Tools.View.Graph.ranks_forward`) | every graph block |
| G6 rows | the JSON fold reads back: `Document.ofJson (Document.json d) = .ok d` | an exact embedding, retraction half; `Tools.Document.Json` holds both maps | every document |

What the drawing does not show: the tensor's left priority (`Reactor.tensor`, `src/Effect4/Run/Runner.lean`). Overlay is commutative and the tensor is not where two reactors answer one row. The picture is of disjoint rows, and a figure's caption says so.

G5 is evidence from the prove-out. Its first hypergraph drawing listed the wires after `main`. The layout routed three edges back up and around. That drawing was replaced by the sorted one. `Block.graph` takes its nodes in the order the drawing ranks them (decisions row 365), so the derivation sorts.

### 2.5 The three forms from the one value

| Form | Fold | Output | Today |
| --- | --- | --- | --- |
| the table | `Document.markdown` on a `Block.table` | `todo.gen.md`, the mapping of our words to Effect's and the algebra's | `out/todo.gen.md` |
| the rows | `Tools.Document.Json.Document.json` | `todo.gen.json`, every node with its key, label, status and detail, every edge by key | `out/todo.gen.json`; the TSV is a projection of it |
| the drawing | `Tools.Document.Figure.picture` through `Graph.layout` and `Tools.View.SvgOut.fileText` | one `.gen.svg` a figure; Mermaid from `Tools.Document.mermaid` in the Markdown | `out/*.gen.svg`, `out/figures.jpg` |

No hand-written drawing. The look is the view's look (`tools/view/out/looks/looks.css`, `tools/Tools/Document/page.css`).

## 3. The candidate drawings

The owner asked to see the representations the literature gives and then choose. `out/figures.jpg` shows four, all from one value.

| Drawing | Literature | What it shows well | What it hides | Cost in the tree |
| --- | --- | --- | --- | --- |
| D1 boxes with dependency edges | Mokhov 2017; the layout the tree has | who provides to whom, at a glance; the cached block with the same boundary | the tag on a wire; where two providers meet | none |
| D3 hypergraph, wires as vertices | Fong 2015, Baez–Fong 2015, BSZ 2016 | the tag on every wire; composition as overlay; last-wins as two boxes into one wire | twice the vertices | none; G3 relates it to D1 |
| D2 the layer term as a term graph | Hasegawa 1997 for sharing; Mokhov 2017 for the expression | the syntax of a composition, `fresh` and `ref` included | the wires | `cata_layer` |
| S string diagram with ports | Selinger 2010; Joyal–Street 1991 | the order of ports on a box; the identity of a wire through a box | nothing the others show, at a layout cost | `Tools.View.GraphAttachment` has port attachments; not proved out |

The recommendation is a proposal, not a ruling. D3 is the semantic form, because composition is overlay there and the laws are the algebraic graph's. D1 is its contraction, for reading. D2 is the syntax. S waits for the handler slice, where ports carry meaning.

## 4. The reuse pass

| Exists | Where | The slice uses it as |
| --- | --- | --- |
| the figure graph as data | `Tools.Document.Block.graph`, `GraphNode` | the one carrier of a graph block |
| the three folds | `Document.markdown`, `Tools.Document.Json.Document.json`, `Tools.Document.Html.algebra` | the three forms |
| the one layout and the SVG | `Tools.View.Graph.layout`, `Tools.Document.Figure.picture`, `Tools.View.SvgOut.fileText` | the drawing |
| the algebraic graph and its laws | `Tools.View.AGraph`, `AlgGraph.lean` | the model G1 and G2 are stated in |
| the call table and its law | `Api.HostSession.callTable`, `callInstance_callTable` | the source of G∂ and G∘ |
| the layer fold | `cata_layer`, `Fold.lean` | the source of Gλ |
| Kahn's order | `Tools.View.FlowOrder.orderFor` | G5 |
| the read-back | `Tools.Document.Json.Document.ofJson` | G6 |
| the inspect command | `Compiler.inspect`, `tools/Compiler/Inspect.lean` (decisions row 435) | the home of the new forms |

Nothing new is drawn. `probe-view.lean` is 150 lines, and its three readers are the slice's three folds.

## 5. The slice

Base: `e16ea6ed4` or later on `refactor/phase1-phase3`. One seat, one branch. Commits by explicit paths after a narrow build.

1. **The folds.** A module `tools/Compiler/Graphs.lean` with `boundary : Api.Built → Block`, `calls : Api.Built → Block` and `layers : Api.Built → List Block`, each a `Block.graph`.
   `boundary` reads the call table as §2.2 says, in the hypergraph form, with the box form as its contraction (G3). `layers` folds each layer term of the block with `cata_layer` (Gλ). Every node list is in Kahn's order (G5). No `partial`, no hand match over `LayerTerm`.
2. **The command.** `inspect --what boundary | calls | layers` beside the existing `graph`, with `--form md | json | svg`. Markdown and JSON are the document folds. SVG is `Figure.picture` through `SvgOut.fileText`, one file a figure. The JSON is the one the site reads (`effect4-document/1`).
3. **The table.** The mapping table of `out/todo.gen.md` becomes a `Block.table` the command writes with the figures. Its rows are read from the same data. One row stands for a host, a block or a main, and one row for a combinator the layers use.
4. **The laws.** G1 and G2 as theorems in `tools/Tools/View/` beside `AlgGraph.lean`, placed under concept 7. G3, G4 and G5 as finite checks in a battery under `Test/`, reachable from `Test/All.lean` at the anchor the coordinator names. Each line is a reader, a control or a finite evaluation. G6 as a theorem if `Tools.Document.Json` admits it in a day. Else a finite check and a planned goal with its claim.
5. **The generated group.** `generated/graphs/todo.gen.md` and `todo.gen.json` for the dogfood to-do, written by `python3 scripts/generate.py --only graphs` through the command. `docs/GENERATED.md` lists the group with its producer, its inputs and the check that a rerun changes no byte.
6. **The receipt.** Folded into the push's note. It gives the one thing to know, base and head, the files, the commands and their results. It gives `#axiom_audit` over the touched modules, the open obligations, and what is bounded to the to-do.

Gates: `LEAN_NUM_THREADS=3 lake build <Module>` per touched module; `#axiom_audit` over them; `make batteries-touched BASE=<rev>`; `python3 scripts/check-language.py --strict` on the documents; the generated group's rerun check.

Not in this slice: a string diagram with ports, motion, a run as a graph, and a drawing of handler composition. Also not in it: any change to `Graph.layout`, `SvgOut` or the look, and any second graph carrier.

## 6. What this note does not establish

The prove-out is a finite probe on the session objects of the to-do, plain and cached. No theorem of §2.4 is proved here; G2 is the existing `overlay_comm`. The drawings are the view's, unchanged, so nothing is claimed about their layout beyond `ranks_forward`.
Effect's side is cited by line and checked by the behaviour gates, not proved. Hasegawa 1997 is not vendored, so sharing graphs are cited by title.
