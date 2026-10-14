# 2026-10-07 The forms of a program, linked: the gaps as tables, marks for the rows, and a graph that answers the hand

Status: research note (history, not authority). Base: `de7b4044`, with the uncommitted work of
the working tree. Nothing tracked is edited. This note continues
`docs/research/2026-10-06-native-view-p1.md`. The probe is the same folder,
`docs/research/2026-10-06-native-view-probe/`. Its `round2/` holds the viewer and the export of
the earlier note. `docs/research/2026-10-07-native-view-schemas-and-lowering.md` continues this
note. It changes the canvas's contract C6 and the rule of a click, so the counts of finding 9
are those of round 3.

## Question

The owner asked five things by voice on 2026-10-07. The text is the coordinator's reading.

1. Go deeper into the gaps. Say what landing the new forms looks like.
2. Attend to the design system. The rows of the operations table want small marks that tell
   the operations apart.
3. Draw a basic graph well, and let the reader's hand move it. Say what that takes in C, and
   which kinds of rendering it meets.
4. Give one easy command that runs the view from the console.
5. Look for the gaps of the authoring too. Take no shortcut.

One phrase is read by ear: "have it come up in my console". The reading here: one command
in the console opens the view, and the same command can write a page into the console.

The owner added four things while the pass ran.

6. Go through the design in detail: how it joins the algebra, what the gaps are, and which
   implementation is needed.
7. Name the data structures and the abstractions that would remove the gaps of the authoring.
8. Make the canvas of the pan and the zoom professional C, generated or not.
9. Let another instance work on the details alone: the marks, the look and the painter.

The reading of the ninth: a second instance of the assistant takes that pass. It worked in
`docs/research/2026-10-07-native-view-details/`, and finding 11 reports it.

## What was read or run

| Item | Evidence |
| --- | --- |
| `src/Effect4/Program/Authoring.lean`, `src/Effect4/Program/Authoring/Lifts.lean` and `Sugar.lean` there: `Src`, `Env`, `elaborateModule`, `expandDoElems` | reading |
| `src/Effect4/Program/Typing/Table.lean` and `Focus.lean` there: `table`, `refusals`, `focusAt` | reading, then tested through the export |
| `src/Effect4/Program/Sketch.lean`: `omitAt`, `Row.hole` | reading, then tested through the export |
| `src/Effect4/Program/Eff.lean`: `Row`, `RowKind`, `RowShape`, `Registration`, `arms`; `src/Effect4/Program/Native.lean`: `NativeOp.spelled` | reading |
| `docs/research/2026-09-08-design-language.md`, sections 2, 3 and 7 | reading |
| `Lines.lean` of the probe, round 3: the export of p1 and of the 79 corpus programs (`export-run.txt`) | tested |
| `view.c` of the probe, round 3: 28 frames of a fixed script, twice (`frames-run.txt`) | tested |
| The same viewer under the address and undefined-behaviour sanitizers (`asan-run.txt`) | tested |
| Paint times on seven pages and on a tree of 32,767 boxes (`bench-run.txt`, `window-run.txt`) | tested |
| `canvas.c` of the probe against its eight contracts, on 800,801 random cases (`canvas-test-run.txt`) | tested |
| The receipt of the detail pass, `docs/research/2026-10-07-native-view-details/receipt.md`, and its sheets | reading; its own runs are not run again here |
| The advance of a glyph of the data face under two sets of text options (`advance-run.txt`) | tested |
| `src/Effect4/Codegen/Forms.lean`: `Form`, `Template`; `src/Effect4/Program/AtomInventory.lean`: `NativeAtom.all` | reading |
| The three hues of an agent against the palette validator of the session's chart skill (`hues-run.txt`) | tested |
| The works on tree layout and on layered graphs that finding 6 names | by name |

## Findings

### 1. Three links between the forms of p1 are computed today

The earlier note found three links absent. The probe now computes each one, with no edit of
the tree. Each computation names what the tree lacks.

| Link | How the probe computes it | Count on p1 |
| --- | --- | --- |
| a place of the authored source to a stored node | a marked copy of the battery's definitions; one authoring elaboration for each mark | 58 places; 51 of 56 nodes have one |
| a stored node to its span of the printed TypeScript | the node is omitted, and the two texts are compared | 48 of 48 programs |
| a stored node to its type | the tree's own address table | 48 of 56 addresses; the other 8 are no programs |
| a fiber to the node of its fork | the fork record's site | 12 of 12 |
| a call to its row, and so to the row's nodes | the call's operation | 6 of 6 |

**1.1 The origin of a node.** A source is a function of the scope and of the path (`Src`,
`src/Effect4/Program/Authoring.lean`). So a source is handed the path of the node that it
builds. The probe reads that path out in three steps.

```mermaid
flowchart LR
  F["the battery's file"] -->|"parse, in the probe's scope"| C["a copy of 7 definitions"]
  C -->|"a mark around each application and each statement"| M["152 marks, each with its place"]
  M -->|"one mark is the trap; elaborate"| R["a refusal that carries the path and the marks around it"]
  R --> T["the origin table: 58 rows"]
```

1. The command `instrument_defs` parses `Test/Dogfood/P1HttpCache.lean`, and Lean elaborates a
   copy of seven definitions. A mark stands around each application and each `eff` statement.
2. A mark is the identity on a source (`OriginProbe.trap`). It adds one frame to the scope:
   its number and the path.
3. One mark at a time is the trap. It refuses, and the refusal carries the frames. One
   elaboration answers one occurrence.

The copy builds the same stored program and the same table as the battery's definition. That
is one finite check (`C p1-origin-copy`). The five nodes with no place are two `fork` actions,
two cells of a race's list and its end. A lift builds each of them inside its own code.

A node's row of the table is a chain. The node at `[1 1 0 0]` reads, innermost first:
`bindName at retryForm 93:2`, `retryForm at fetchQuote 164:2`, `fetchQuote at program1 179:21`.
So the chain is the route from the stored node up through the forms to the program's own line.

The computation names four gaps.

- The `eff` macro keeps no place of a statement. Its lifts carry the place of the whole
  block (`expandDoElems`, by reading). The probe copies the macro's cases to add the marks.
- The carrier has one way out for a path: a refusal. The probe uses a refusal as a reader.
- No definition is known as a form. The probe is told seven names.
- A place is a line and a column of one file. Nothing ties it to a revision.

**1.2 The span of a node in the printed text.** `Sketch.omitAt` puts a hole in a node's place
(`src/Effect4/Program/Sketch.lean`). The hole's row declares the node's type, which the address
table answers. The printer prints the sketch. The two texts differ at one stretch, where the
sketch holds the hole's call. The program's text at that stretch is the node's span.

The export accepts a span under two checks: the hole's call stands at the first difference,
and the text after it is equal. All 48 programs of p1 pass, in 360 ms for 48 prints. No law of
the tree says that the printer composes this way.

**1.3 A form's region.** A mark whose head is one of the seven definitions is an application
of a form. Its path roots a subtree. The origins page lists three.

| Application | Its place | The subtree |
| --- | --- | --- |
| `fetchQuote` | `program1` 179:21 | at `[1 1 0 0]`, 46 of 56 nodes |
| `retryForm` | `fetchQuote` 164:2 | at `[1 1 0 0]`, 46 of 56 nodes |
| `timeoutForm` | `fetchQuote` 165:5 | at `[1 1 0 0 0 0 1 0 0]`, 31 of 56 nodes |

So one authored line, `let body ← fetchQuote (str "EFX")`, stands for 46 of the 56 stored
nodes. This region is a derived view in the sense of row 281, point 3: the stored program
holds no marker.

### 2. One key for each object joins the pages

Round 2 linked two lines of one page by a pair of indices. Round 3 gives each object a key,
and a mark may refer to other keys.

| Key | Object | Marks that carry it |
| --- | --- | --- |
| `n:<program>:<path>` | a node of a stored program | a line, a box, a span of the authored source, a span of the printed text, a row of the origins |
| `r:<program>:<position>` | a row of the table | the row's head; a `perform` line refers to it |
| `op:<index>` | a native operation | the same, in `NativeOp.spelled`'s order |
| `c:<program>:<index>` | a command of the journal | a line; it refers to its call, its row and its fiber |
| `f:<program>:<id>` | a fiber | a box; it refers to the node of its fork |
| `k:<program>:<id>` | a call | a box; a `bind`, a `submit` and an `apply` refer to it |
| `s:<program>:<line>` | a line of the authored source | a line; it refers to the nodes whose syntax starts there |

The reader selects one key. A mark is lit when it carries that key, refers to it, or is
referred to by it. One pass over every mark of every page finds them. Return opens the next
page that shows the same object. Tab follows the first reference.

p1 has ten pages. The node at `[1 1 0]` stands on six: the program, the origins, both graphs,
the printed text and the authored source. One selection lights all six.

This is the second half of the native form. The first half is the earlier note's: the stored
tree is a trie, and a column is a table keyed by a path. The second half is objects and
references: a row of the input is a mark with a key and a list of keys.

### 3. The gaps again: each is a column, a written form or a row

| Gap of 2026-10-06 | State on 2026-10-07 | What landing looks like |
| --- | --- | --- |
| No type at a node | filled by the tree: `table` and `focusAt` (slice TABLE). The export copies it. The module says that it is slow; p1's table takes 31 ms | the pass that checks each node once, which that module names as its next slice |
| A refusal's path | filled by the tree: `refusals` lists each one. The viewer still shows the first | the page shows each refusal |
| A stored node has no origin | computed by the probe (finding 1.1) | a table beside the built program; proposal B below |
| The printed text has no spans | computed by the probe (finding 1.2) | spans from the printer's own document, and a law of composition |
| No written form of a term, an operation, an exit | open. The export derives `Repr` for 16 types and writes six forms by hand | one generated written form for each sort |
| A decision cannot be written whole | open | a written form that names a point by its path |
| The trace has no rows | open | the trace's events as rows, in the library |
| A call does not name its site | open. The join goes through the row. `sleep` is performed at 2 nodes, and its call cannot say which | the path of the `perform` node, in the call |
| A variable is a position | open. The lifts take each name as a text and drop it | a table of names at each binding child, by the origin table's route |
| A row has three names; a key has no name; the host is local; the profile is empty | open, as on 2026-10-06 | as on 2026-10-06 |

The pages of round 3 show five more.

| New gap | Where it was met | What would fill it |
| --- | --- | --- |
| `registration` has a value at a row that is no async row | 21 of the 23 native rows are `sync`, and each says `registration deferred` | the registration as a part of the async kind |
| The kind `program` has no row | 0 of 23 native rows, 0 of 6 rows of p1 | a ruling: the kind is live, or it retires |
| The `eff` macro keeps no place of a statement | finding 1.1 | a mark at each statement's lift |
| The groups of the constructors are comments | `Eff`'s source says "exits", "thunks", "masks"; `arms` has no such field | a field of `Arm`, if a node's sort is to be drawn |
| The printer breaks no line inside an expression | p1 prints in 15 lines; the longest holds 980 characters | the document algebra of the visual-plane plan |

So a landed form is one of three things.

```mermaid
flowchart TD
  P["stored program: a trie of paths"]
  C["a column: a table keyed by a path, beside the program"] -->|"joined by path"| V["a page: objects in an order"]
  W["a written form: one text for each value of a sort"] --> V
  S["a stream of rows: a journal or a trace, which only grows"] --> V
  P --> C
  P -->|"one generic layer, folded"| V
  K["keys and references"] --> V
```

- **A column** stands beside the stored program and never inside it. `Built.rowNames` is the
  tree's own precedent (`src/Effect4/Api/Built.lean`). The types and the refusals are columns
  that the tree has. The origins, the spans, the names and the regions are columns that it
  lacks.
- **A written form** is one text for each value of a sort. The dictionary's exact embedding is
  its shape: a write, a read and their three laws.
- **A stream of rows** is the journal today. The trace is the stream that the tree lacks.

### 4. The gaps of the authoring

p1's authored text is 109 lines for the two forms and the program. The origin probe and a
reading of those lines give seven gaps.

1. **No place.** The macro and the lifts record no place of the source (finding 1.1).
2. **Names are dropped.** `store`, `cached` and `retry.last` are in the source. The stored tree
   holds positions, and the page shows `(var 2)`.
3. **A form has no identity.** `timeoutForm` and `retryForm` are Lean functions of one battery.
   The battery's own header says that they meet lexical well-scoping alone, of R10's six duties.
   The region of finding 1.3 is a first answer to two of them: the identity is the definition's
   name, and the expansion is the subtree.
4. **A term is written as texts of atoms.** The 109 lines hold 53 applications of an atom by
   its text. 19 of them are `fst` or `snd`: the retry's cursor is a nested pair.
5. **A bind takes no pattern.** The macro refuses one by a message (by reading).
6. **A form's types are stated by hand.** `retryForm` takes the answer's type and the error's
   type as arguments (DI-91).
7. **The host is local.** `Script`, `Driver`, `step` and `drive` are in the battery.

The battery's own header lists what the language refuses of the rc.112 original. That list
stands, and this note adds nothing to it.

### 5. The design system: one grid, two faces and four marks

**The grid.** A cell is 8 px wide and 24 px tall: one base unit by three. The data face is
sized so that its advance is one cell, which is 13.288 px for Menlo. Each mark stands at a
whole cell. So the layout is integer arithmetic, and no width of a text places another mark.
A terminal shows the same columns.

**The faces.** Data is in the monospace face. A name is in the display face, and a label or a
remark is in its italic. Round 2 dropped the italic, because cairo's own text call does not
kern. Round 3 shapes text with pango, which was on the machine. The italic is back.

**A row of the table.** The earlier page wrote twelve field lines for each row. Round 3
writes a head line and eight labelled lines, and no field is dropped.

| Line | The fields it holds |
| --- | --- |
| the head | the position, the mark, the name, the count of nodes that perform it |
| asks, answers, fails | `request`, `answer`, `error` |
| printed | the form that the row prints as, then `shape`, `spelling`, `trailing`, `typeArgs` |
| answered | `kind`, `registration` |
| requires, declared, cites | `requires`, the declared name, `cite` |

With the runs folded, the page is a table of one line for each row. With the types shown, a
head line holds the row's protocol in the design language's marks:
`! string  ? string  × readonly [string, string]`.

**The four marks.** A mark tells how a row is answered. It is a function of two fields,
`kind` and `registration`. Each part is a mark that the design language already has.

| Row | Mark, in a terminal | Parts | The design language's row |
| --- | --- | --- | --- |
| `sync` | `■` | a filled square | a promise kept; here, within the step |
| `async`, `deferred` | `□┄┄■` | hollow, dots, filled | the park and the resume: one hollow, one filled |
| `async`, `external` | `□┄┄┃■` | hollow, dots, a bar, filled | the same, and the bar line of a decision of the host |
| `program` | `═╤═` (two rules, the second indented, in the window) | an indented line | a program node |

The same mark stands wherever the operation stands. It stands at the row's head, at a
`perform` line, in a `perform` box and at the commands of a call. A `bind` takes the hollow square and an
`apply` the filled one. A call with no reply keeps its hollow square. An exit is written as
the design language writes it: `‖ success`, `‖ × fail`, `‖ ⊣ interrupt`.

**Hue.** The base stays black and white. The bar tells an external row from a deferred one,
so no fact rests on a hue. `--hue` draws the host's bar and a refusal's box in their agent's
hue. The palette validator checked the hues on both grounds.

| Three hues | Ground | Result |
| --- | --- | --- |
| the design language's: `#a86b00`, `#b0342c`, `#2e6e4e` | its paper | two checks fail and one warns: chroma, the distance of two hues, and separation under a colour-vision deficiency |
| the probe's: `#a97416`, `#ac312a`, `#349470` | its paper | each check passes |
| the probe's: `#c0851f`, `#bd3931`, `#359b75` | the dark ground | each check passes |

The failing result is a third defect in the design documents, beside the two of the first
note.

### 6. A graph that answers the hand: what it takes in C

The graph pages of round 2 moved by a drag and nothing else. Round 3 answers a list of needs.
Each row names the answer and its measure.

| Need | The probe's answer | Measure |
| --- | --- | --- |
| a layout | Lean places each box in cells. Two layouts stand, each a fold over a tree in preorder | below |
| a camera | an offset and a zoom for each page; the zoom keeps the point under the pointer | — |
| sharp rules | a rule's ends go to device pixels and are rounded; a rule is one pixel at every zoom | the frames |
| readable text, or none | a text is drawn where its face has 6.5 px or more | the frames |
| cost that follows the window | the boxes are sorted by row and column; a row is searched by halving; thin boxes that touch are one rule | 32,767 boxes: a zoom takes 1.40 ms a frame, and 4.81 ms without the merging |
| cheap text under a zoom | the zoom stands on steps of an eighth of an octave, so few sizes are made | the run graph: 1.26 ms a frame on steps, 4.06 ms off them |
| picking | the pointer goes back through the camera to a row, then by halving to a box | — |
| moves along the tree | the arrow keys go to the parent, the first child and the siblings | — |
| stillness | the window waits for an event; twice a second it reads the files' dates | — |
| equal frames | a fixed script calls the window's own handlers | 28 of 28 frames equal over two runs |
| memory safety | one arena for a load's texts; a reload frees and reads again | 7 commands under two sanitizers: 0 findings |

The camera, the index and the level of detail are one module since this pass (finding 9).

A paint takes 1.08 ms as the mean of the 28 frames, at 2560 by 1600 pixels. The window
paints a frame in 2.1 to 3.4 ms. The largest paint of a bench is the first one, where the
faces load. It takes 17 to 33 ms. These are the numbers of the last run, after finding 11's
merge.

**Two layouts of one tree.** Neither is a layout engine. Each reads the tree and the boxes'
widths.

| Layout | Rule | Extent of p1's 56 boxes |
| --- | --- | --- |
| first | a parent over the middle of its children, left to right | 792 cells by 18 levels: 6384 by 1432 px |
| second | a node's last child below it, its other children at its right | 248 cells by 33 levels: 2032 by 2512 px |

In a window of 1280 by 800 px the first fits at a zoom of 0.19 and the second at 0.27. At
a zoom of 1 the first is five windows wide, and the second is 1.6 wide and 3.3 high. The second
takes 56 % of the first's area. Its rule reads the order of the children and nothing else. On a `bind` it puts the rest of the program below, so a
chain reads down the page. That is the sequence view that the first note left for a ruling.
The works on tidy trees and on drawings with one child below are named here, not read.

**The kinds of rendering.**

| Kind | What draws | Text | It fits | State |
| --- | --- | --- | --- | --- |
| a vector raster on the processor, into one texture | cairo fills an image; SDL shows it | pango shapes, cairo keeps the glyphs | still frames; the marks of one window; PNG, SVG and PDF from the same paint | the probe |
| triangles on the graphics processor | quads through SDL's renderer or sokol | an atlas of glyphs, with a second way to write a vector page | motion in each frame, or far more marks in one window | not built |
| a kept scene | a list of marks, compared between frames | a kept layout for each mark | free marks with no grid | not needed: on a grid of cells, picking is arithmetic |
| cells of a terminal | characters and box-drawing rules | the terminal's | a console, a note, a difference of two runs | built: `--text` |

**What a graph that is no tree asks.** The estate has three: the plan, the references between
layers, and a run's causal order. None is drawn. A layered drawing ranks the nodes, orders each
rank and routes the edges. Round 1 ran `dot` for that, in 120 ms on the plan's 575 nodes.
A first step with no engine is a rank by the longest path, which is a fold.

### 7. One command

`v`, in the probe folder, is 57 lines of shell. `check.sh` beside it runs each check of finding 6 and finding 9.

1. It exports the rows when the export or one of its two sources is newer than the rows.
   An export takes 8.7 s, and Lean's elaboration of the file is 8.0 s of that.
2. It builds the viewer when `view.c` is newer than the binary.
3. It opens the window at the first page whose name holds each word. With `-t` it writes
   the page into the console, and a wide page opens in `less`.

A window that is open reads new rows by itself. So an export in one console changes the view
in the other.

### 8. The design against the algebra, part by part

Each part of the view is a function of one object of the tree. The table names the object,
its declaration and the state of the join.

| Part of the view | It is a function of | Declaration | State |
| --- | --- | --- | --- |
| a line of a program | one layer of the syntax signature, folded | `EffAlgebra.ofLayer`, `cata_eff` | the fold is the tree's; the layer is the probe's |
| a line's place and its key | the path, which is the key of the trie | `Node.at_`, `Node.addresses` | the tree's |
| the indent, the fold of a run, the rule along a run | the prefix order of the paths | the export's run check: 429 of 429 paths | a finite check; no law |
| a type beside a line | the address table | `table` | the tree's |
| the box at a refusal | the located refusal | `refusals`, `Api.explain` | the tree's |
| a row's mark | `Row.kind` and `Row.registration` | `Row` | the tree's |
| a row's protocol | `Row.request`, `Row.answer`, `Row.error` | `Row` | the tree's |
| a hollow and a filled square on the journal | the `bind` and the `apply` of one call | `Runner.Command` | the tree's |
| the glyphs of an exit | the list of a cause's reasons | `Cause`, `Exit` | the tree's; the written form is the probe's |
| a box's place in a graph | a fold over the tree and the boxes' widths | `ViewGraph.tidy`, `ViewGraph.lastBelow` | the probe's |
| a link from a fiber | the site of its fork record | `ForkRecord` | the tree's |
| a link from a place of the source | the path that a source is handed | `Src` | computed by the probe |
| a link to a printed span | the difference of two prints | `Sketch.omitAt`, `Api.printModule` | computed by the probe |
| a page at one command of the journal | the replay of a prefix of the journal | `Run.play` | the tree's; not drawn |
| the lit marks | one key and its references | the fields above | the probe's |

Two readings follow. First, where the state is "the tree's", the view copies a field and
decides nothing. Second, each row with "the probe's" is a piece for the tree to own. Those
pieces are the layer, the written forms, the layouts and the keys.

### 9. The canvas is a module with eight contracts

`canvas.h` and `canvas.c` hold the camera, the index of the boxes and the level of detail, in
123 and 198 lines. They name no drawing library. The viewer calls them for each pan, zoom,
fit, pick and paint of a graph.

| Contract | In words |
| --- | --- |
| C1 | the map to the window and the map to the world are inverse |
| C2 | a zoom about a point keeps the world point under it |
| C3 | the zoom stands on a step, and small factors add up between steps |
| C4 | after a fit the whole world is in the view, and one step more would not fit |
| C5 | after a pan, a margin of the world stays in the view |
| C6 | a pick answers what a scan of every box answers |
| C7 | a visit sees exactly the boxes that meet the view; merged runs cover them and do not overlap |
| C8 | a snapped coordinate is a whole device pixel |

`canvas_test.c` holds each contract on random cases from a fixed seed: 800,801 cases, and 8 of
8 hold. Each test compares the canvas with the plainest computation of the same answer. The
module builds with no warning under five sets of warnings, and the test runs under two
sanitizers.

One test failed at first. A fit of a wide world stopped at the smallest zoom. The
smallest zoom is now 1 in 65,536, and C4 states that bound.

No line of the canvas is generated. The index and the pick are whole-number work on a sorted
array. A Lean function with a proof that a pick equals a scan could replace them, by round 1's
route of a lowered function. The camera is arithmetic on floating-point numbers, and a test
holds it.

### 10. The abstractions that would remove the gaps of the authoring

Each gap of finding 4 has one abstraction that fills it. The tree holds a part of each.

| Gap | The abstraction | What the tree has of it | What is new |
| --- | --- | --- | --- |
| no place | a mark on a source, and the origin table as a column | the path in `Src`; `Built.rowNames` as a table beside the program | the mark, the macro's marks, the table |
| names are dropped | the context at an address: a name and a type for each variable | the names in the authoring's `Env`; the types in `Node.envAt` | the names kept at each binding child; `focusAt` then answers both |
| a form has no identity | a form as data: a template with slots, whose application is a region | `Codegen.Forms`: 19 forms, each a `Template`; `Sketch.fillAt` with its replacement law | a template for more constructors, or a command that defines a form |
| a term is texts of atoms | one generated lift for each atom | `NativeAtom.all`: 43 atoms in a generated list | the lifts, with each atom's arity in Lean's types |
| a bind takes no pattern | a bind of a tuple or of a record, as sugar | `tuple` and `tupleAt` of the authoring | the macro's case: a pattern becomes projections |
| the host is local | a host policy as data | the battery's `Script`: a call's ordinal to an answer | the policy and its drive in the library, with a stop at the exit |

The third row holds a choice. `Template` has 12 cases. It has no case for `iterate`, `catchIf`,
`select` or a race, so neither form of p1 can be written as a template today. A form as a Lean
function reaches every constructor, and its identity is then the origin table's to give.

### 11. The detail pass: a second instance on the marks and the painter

A second instance worked on details alone, in its own folder. Its receipt holds each number
behind a command of its own. Three results bear on this note.

**A defect of round 3's grid.** The viewer sized the data face under one set of text options
and drew under another. One glyph then advanced 8.026 px, where a cell is 8 px. A text left
the grid by one pixel in 37 characters, and pango cut a text that filled its room. Frame 19 of
the first run showed `select (var 1) opti…` in a box that holds the whole text. The coordinator
measured the two advances again: 60.000 px and 60.205 px for a face of 100 px
(`advance-run.txt`). The size whose advance is one cell is 13.288 px, and the earlier text of
this note said 13.333 px.

**A painter and two tables.** `paint.h` holds the grid, the tokens, the faces and each drawing
call, on whole device pixels. `marks.h` holds the marks as data: five parts, and six words
over the parts. A terminal's characters stand in the same table, so the two cannot drift.

| Word | Its parts | It is a function of |
| --- | --- | --- |
| sync | filled | `Row.kind` is `sync` |
| async, deferred | hollow, dots, filled | `Row.kind` is `async` and `Row.registration` is `deferred` |
| async, external | hollow, dots, bar, filled | `Row.kind` is `async` and `Row.registration` is `external` |
| program | indent | `Row.kind` is `program` |
| hollow | hollow | a `bind` of the journal; a call with no reply |
| filled | filled | an `apply` of the journal; a call with its reply |

The pass reports 2,720,209 cases of whole-pixel drawing with no failure, and 19 red controls
that fail as they must. Those runs are the pass's own.

**The merge.** The viewer now draws through that painter and reads its marks from that table.
`view.c` fell from 1,206 lines to 1,104. With the merge, 28 of 28 frames are equal over two
runs, and the two sanitizers find nothing. The merge took these measures from the pass.

| Detail | Round 3 before | After the merge |
| --- | --- | --- |
| a mark's square | 8 px, its middle 0.89 px above the middle of the letters | 7 px, on the baseline |
| the dots of a wait | four dashes of 2 px | five dots of 1 px, at one pitch at every zoom |
| the host's bar | 18 px high | 15 px high, so that bars of two rows do not touch |
| the label column of a field | 12 cells | the longest label and two cells: 10 on the operations page |
| the band of a lit row | the rule's tone at 0.60 | at 0.50: midway between the ground and a rule |
| the reader's bar | 2 by 18 px, with a gap to the run's rule | 2 by 24 px, one line with the rule |
| a row's baseline; the heads; the head rule; the foot | 16.5; 92; 99; 11 px from the bottom | 16; 88; 96; 12 px |

The pass leaves two findings for the layout and the canvas. A stem under a box of odd width
stands half a cell left of the middle: 82 of p1's 131 boxes. The canvas and the painter round
a half pixel in two ways, and they differ at one negative coordinate.

## Proposals (not rulings)

**A. Meanings for the owner to rule.** Each is drawn, and each has a flag or a key that draws
the page without it.

1. The four marks of a row (frames 05 and 06; `--plain` or M removes them).
2. The protocol of a row in the marks `!`, `?` and `×` (frame 08b; T shows it).
3. An exit in the design language's notation, in a box of the run graph (frame 22).
4. The three validated hues, at the host's bar and at a refusal's box (frames 04 and 07; H).
5. The second layout as the graph of a program (frame 20, against frame 18).
6. The type at each node as a column (frame 11; T). It is off at the start.
7. The reader's marks: a band at a lit mark, a bar at the cursor, a rule along its run.
8. The cell of 8 by 24 px, with the data face at 13.288 px.

The detail pass asks six more, each with a sheet in its `sheets/` folder.

9. The mark of `program`: an indented line in the window and `═╤═` in a terminal are two
   pictures (`q1-program-mark.png`).
10. The glyphs `‖` and `⊣` are not in the data face. The painter can draw them, or the rows
    can spell them in plain characters (`q2-exit-characters.png`).
11. The display face has old-style figures, so a `0` in a label reads as an `o`
    (`q3-figures.png`).
12. A mark's place in its slot: at the left, or lined up on the filled square
    (`q4-mark-alignment.png`).
13. The host's bars of two rows: apart in the window, joined in a terminal
    (`q5-bar-across-rows.png`).
14. The weight of the type: the system's smoothing draws it 16 to 20 % heavier than plain
    grey (`q6-type-weight.png`).

**B. The origin table, landed.** The probe shows the data. Four parts would give it to the
tree, and the placement of each is owed before any work.

1. A mark `at`, the identity on a source, with a place. Its candidate law: a marked source
   elaborates to the same stored program. Today that is one finite check.
2. The `eff` macro puts a mark at each statement. It has the syntax in hand.
3. A command `form def` defines a form: it marks each application of the body and records the
   definition's name. A region is then a derived view, as row 281 rules.
4. `Author.build` answers the table beside the program, as it answers `rowNames`.

One choice is open: how the paths leave the elaboration. The probe uses a refusal, once for
each occurrence. A writer in the carrier answers all at once and changes each lift. A second
carrier over the same generated syntax signature changes no lift. It asks each form to be
written over both.

**C. The implementation that is needed, in an order.** Each line is one slice. Its placement
in the theory is owed before its work.

| Part | Slice | It removes |
| --- | --- | --- |
| core | the generic layer and one written form for each sort | the export's six forms by hand and its 16 derived instances |
| core | the origin table of B, with the names of binders by the same route | the copy of the macro's cases; the trap; `(var 2)` on a page |
| core | a form as data, by the choice of finding 10 | the seven names that the probe is told |
| core | spans from the printer, with a law that a child's span lies in its parent's | the 48 prints by omission |
| core | the trace as rows, and the site in a call | the join of a call through its row |
| core | the registration inside the async kind | the field with no meaning at 21 rows |
| core | a generated lift for each atom, and a pattern in a bind | 53 atoms written as texts in 109 lines |
| tools | the export as a driver of the tools library, with one gate: each key resolves, and each reference names a key | the hand probe `Lines.lean` |
| viewer | the canvas and the painter as they stand; one rounding rule for both; then the two layouts lowered to C | the layouts' second home in the export |
| viewer | a reader of a stream of splices | a whole reload at each change |

**D. Vendoring still waits for the owner's leave.** Round 3 uses pango, which was installed.
It brings glib with it. A text stack to vendor is smaller: a rasterizer and a shaper.
No file was fetched.

## What this does not establish

- No theorem is stated or proved. Each count is a finite check on one program.
- The canvas's contracts are tests on random cases. None is a proof.
- The detail pass's own checks were not run again here. Its sheets were read by the coordinator, and by no other person.
- The merge was checked by the frames and the sanitizers. No frame was compared with the pass's sheets pixel by pixel.
- The origin table rests on a copy of the macro's cases. The copy is the probe's, and a
  change of the macro would not reach it.
- A mark stands at an application and at a statement. A node that a lift builds in its own
  code has no place: 5 of 56 here.
- A place is a line and a column of today's file.
- A span rests on how one hole prints. Another printer could break the two checks.
- The hues passed one tool's thresholds. No person with a colour-vision deficiency read a
  frame.
- No person used the window in this pass. The handlers ran under a fixed script, and the
  window ran for 120 frames on three pages.
- The pinch of a trackpad is not handled. The zoom is on keys and on the wheel with a
  modifier key.
- The sanitizers saw the script's commands and no hand's input.
- Each time is one machine's, with another build running beside it at times.
- A graph with a shared node or a cycle is not drawn.
- The works on layout are named by name. No paper was read.
- One dogfood program is drawn, under one script.

## Commands

Run each from the root of the tree. `v` runs the first two steps when they are due.

```sh
docs/research/2026-10-06-native-view-probe/v                      # the window, at the contents
docs/research/2026-10-06-native-view-probe/v p1 operations        # the window, at a page
docs/research/2026-10-06-native-view-probe/v -t p1 operations -- --fold --types
docs/research/2026-10-06-native-view-probe/v -t p1 run graph      # a graph, as characters
docs/research/2026-10-06-native-view-probe/v -x                   # export again, then the window
docs/research/2026-10-06-native-view-probe/v -s                   # the frames of the fixed script
docs/research/2026-10-06-native-view-probe/check.sh --window     # each check, with its evidence file

LEAN_NUM_THREADS=3 lake env lean --run docs/research/2026-10-06-native-view-probe/Lines.lean \
  docs/research/2026-10-06-native-view-probe/programs.lines.tsv \
  docs/research/2026-10-06-native-view-probe/p1.lines.tsv --times
cd docs/research/2026-10-06-native-view-probe
./build.sh
./view --page 'p1 · run graph' --bench p1.lines.tsv
python3 big_tree.py /tmp/big.tsv && ./view --page 'big tree' --bench /tmp/big.tsv
./view --page 'p1 · program graph · last child below' --png frames/p1-program-graph-second.png p1.lines.tsv
```

The keys of the window:

| Key | What it does |
| --- | --- |
| the arrows | move the cursor: by line on a page of lines, along the tree on a graph |
| Space, O | fold the cursor's run; fold each run |
| Return | open the next page with the same object |
| Tab, Backspace | follow a reference; go back |
| T, G, H, M | show the types; the indent rules; the hues; hide the marks |
| `[`, `]` | change the page |
| `+`, `-`, `0`, F | zoom a graph; the whole graph |
| `,`, `.` | move a page of lines sideways |
| R, Q | read the files again; leave |
