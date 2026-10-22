# Tools cleanup, 2026-10-22

The tools-and-view cleanup seat. Its estate is `tools/Tools/**`, `tools/Compiler/**`,
`tools/Drivers/**`, `tools/view/**`, `generated/graphs/**`, `docs/GENERATED.md` and the targets
that run these drivers. Base `afe86b819`, branch `claude/tools-cleanup-05167a`.

## 1. The census

Every number below comes from a command in this section. The import graph is the header of every
`.lean` file under `tools/`, `src/` and `Test/`, read by `scripts/lib/lean_imports.py` (1,890
modules). A module's reachers are the modules with no importer whose import closure holds it. The
in-tree form of one closure is `python3 scripts/lean-imports.py --closure <Module>`.

`Tools.View.FlowReach` and the claim `view-reachability-summary-exact` compute the reach of a
flow's edges, not of modules. They are an anchor here: the proof graph's registry names
`Tools.View.FlowReach` and `Tools.View.LayerGraph` as pointer modules
(`tools/ProofGraph/Registry.lean`), so their closures stay.

### 1.1 `tools/Tools/View`: 53 modules, 13,903 lines

Command: `cat tools/Tools/View/*.lean | wc -l`.

The kept path is the closure of `Compiler.Exe`, with the anchors `Tools.View.FlowReach` and
`Tools.View.LayerGraph`, and the document drivers `Drivers.Site` and `Drivers.DocSpecimen`.

| group | modules (lines) | reachers |
| --- | --- | --- |
| the kept path | `Algebra` 132, `Connector` 251, `ConnectorMemo` 77, `Flow` 872, `Glyph` 438, `Graph` 787, `GraphBounds` 34, `GraphOrdering` 43, `GraphText` 23, `Grid` 100, `KeyMap` 225, `Look` 396, `Organic` 518, `Page` 396, `PaintBounds` 118, `Picture` 399, `Place` 154, `Program` 292, `SceneBridge` 41, `SvgOut` 188 | `Compiler.Exe` and every driver |
| the kept path, not the compiler | `Tokens` 484 | `Drivers.Site`, `Drivers.DocSpecimen`, `Drivers.View`, `Drivers.Live`, `Drivers.GlyphSheet` |
| the proof graph's anchors | `FlowLaws` 1,618, `FlowReach` 195, `LayerGraph` 65, `AlgGraph` 219 | `Test.All`, `tools/ProofGraph/Registry.lean` by name |
| the frames | `Build` 168, `Run` 165, `Motion` 210, `Output` 83, `GraphMotion` 323, `GraphAttachment` 47, `GraphAttachmentMotion` 141, `GraphSeparation` 216, `GraphCheck` 165, `GraphLayout` 23, `Decision` 26 | `Drivers.View`, `Drivers.Live`; `Test/Audit/GraphControls.lean` reads four |
| the live loop | `Live` 191, `Inc` 440, `Retained` 921 | `Drivers.Live` |
| the specimens | `Specimen` 72, `FlowSpecimen` 92 | `Drivers.View` |
| the cell and glyph sheets | `Cell` 317, `CellSheet` 144, `GlyphSheet` 152, `Measure` 134 | `Drivers.GlyphSheet` |
| reached by a battery only | `GraphRegions` 327 | `Test/Audit/GraphControls.lean`, `GraphRegionsView` |
| reached by nothing | `FlowOrder` 439, `FlowPath` 162, `GraphContact` 110, `GraphContent` 104, `GraphPacking` 216, `GraphRegionsView` 69, `LiveChecks` 381 | none |

The seven unreached modules hold 1,481 lines. No module imports them, and no file names them,
except `tools/view/README.md` and two docstrings for `LiveChecks`. Command:
`grep -rln "Tools\.View\.<M>\b" tools src Test scripts Makefile docs/core lakefile.toml .claude`.

`Tools.View.Tokens` imports `Compiler.Code.Doc`: the drawing depends on the command line's folder.

### 1.2 The drivers: 17 drivers, 5,406 lines

Command: `cat tools/Drivers/*.lean | wc -l`, and a search of `Makefile`, `scripts/`, `tools/view/v`,
`lakefile.toml`, `.claude/launch.json` and `ocaml/` for each path and module name.

| driver | lines | what runs it |
| --- | --- | --- |
| `CodecValues` | 217 | nothing; the `Makefile` records that the codec lane stays in the tree, run by no gate (2026-10-18) |
| `Corpus` | 159 | `make corpus` |
| `DocSpecimen` | 47 | `tools/view/v -d` |
| `Emit` | 120 | nothing; `lake exe effect4 emit --group corpus` writes the same group |
| `GlyphSheet` | 68 | `tools/view/v -V`, through the lake executable `view-pages` |
| `KernelReplay` | 112 | `make check-kernel`, through the lake executable `kernel-replay` |
| `Live` | 107 | `tools/view/v -w`, `v -c`; the lake executable `view-live` |
| `ProgramStructureCheck` | 28 | the `tools` check of the `Makefile` |
| `Semantics` | 26 | `make gen-semantics`, through `semantics-report` |
| `SemanticsControls` | 413 | nothing; the lake executable `semantics-controls` has no target |
| `Site` | 144 | `make site` |
| `StyleSyntax` | 269 | imported by `Styles` and by `Test/Codegen/FormsContract.lean` |
| `Styles` | 200 | imported by `Corpus` |
| `Truth` | 1,467 | `make gen-truth-corpus` |
| `TsGen` | 1,373 | `scripts/generate.py`, family `ts` |
| `View` | 601 | `tools/view/v` in every frame mode, `-G`, `-L` |
| `Workspace` | 55 | `ocaml/engine/test/kit/test_tool.ml` names it as the producer of its pinned replies |

### 1.3 The C programs

Command: `wc -l tools/view/*.c tools/view/*.h tools/view/build.sh tools/view/v`, and
`git log -1 --format='%h %ad' -- tools/view/draw.c tools/view/play.c`.

| file | lines | run by |
| --- | --- | --- |
| `draw.c` | 155 | `v -p`, `v -k`, `v -L` |
| `play.c` | 254 | `v NAME`, `v -w` |
| `scene_test.c` | 90 | `v -c` |
| `paint.h` | 606 | `draw.c`, `play.c` |
| `replay.h` | 194 | `draw.c`, `play.c` |
| `scene.h` | 335 | `play.c`, `scene_test.c` |
| `build.sh` | 46 | `v` |
| `v` | 179 | a person |

The C totals 1,634 lines; with `build.sh` and `v`, 1,859. The last commit to `draw.c` and `play.c`
is `6b9c0a89c` of 2026-10-12. In the main checkout the binaries `draw`, `play` and `scene_test`
date from 2026-10-10 and 2026-10-12. This worktree has none built.

Vendored by pin for the C programs (command: `git ls-files vendor/<d> | wc -l` and the bytes):

- `vendor/SDL3-3.4.16`: 8 files, 13,509 bytes; `play` links it.
- `vendor/termbox2-2.5.0`: 4 files, 129,072 bytes; no C file includes it. Only
  `Tools.ArchitectureRoles` names it.
- `vendor/freetype-2.15.0` (8 files), `vendor/harfbuzz-14.6.0` (5) and `vendor/thorvg-1.1.2` (5):
  no tracked file outside `vendor/` names them.

### 1.4 The words of the generated documents

Command: an `awk` scan for string literals with three or more words, outside comments and
docstrings, over the eight files of the brief (130 literals). The prose that reaches a program's
document is all in `Compiler.Graphs`:

| declaration | literal | role |
| --- | --- | --- |
| `Compiler.Graphs.document` | "The program as relations and graphs" | the title |
| `Compiler.Graphs.document` | "Node addresses name stored syntax. Call addresses name …" | an introductory paragraph |
| `Compiler.Graphs.document` | "The program and its boundary" | the mapping part's title |
| `Compiler.Graphs.mapping` | "ours", "Effect TypeScript", "algebra", "comodel of the row operation syntax signature", "handler with one program per method", "term over the handled methods", … | a table of the writer's reading |
| `Compiler.Graphs.calls` | "Calls from definitions and main to definitions and host rows." | the `calls` caption |
| `Compiler.Graphs.boundary` | "Boundary incidence: shared service wires join providers to consumers; no execution order is claimed." | the `boundary` caption |
| `Compiler.Graphs.boxes` | "The boundary with each service wire contracted." (twice) | the `boundary-boxes` caption |
| `Compiler.Graphs.layers` | "This program has no stored layer constructors." and "Stored layer constructor positions …" | the `layers` caption |
| `Compiler.Graphs.wiring` | "This program's layer term provides no service." and "The layer term's wiring: …" | the `wiring` caption |
| `Tools.Document.Html.algebra` | "The figure in words" | the heading of a figure's description |

The scan finds 20 such literals in `tools/Compiler/Graphs.lean` and one in
`tools/Tools/Document/Html.lean`.

The other literals are not a writer's prose on a program's page:

- refusals and their reasons: `Tools/Document.lean` 6, `Document/Json.lean` 12,
  `Document/Markdown.lean` 12, `Document/Sheet.lean` 5, `Compiler/InspectDocument.lean` 4,
  `Compiler/Inspect.lean` 2;
- the site's navigation labels, five in `Tools/Site.lean`, such as "Skip to the content" and
  "On this page";
- the document specimen's sample text, `Document/Specimen.lean`, 24 literals;
- the studio's labels, CSS and JavaScript, 38 literals in `Drivers/View.lean`. An example is
  "dark beside paper".

`Compiler.Report` is out of scope: its words are the vocabulary of row 444.

### 1.5 The typography and the look

The page's rules are `tools/Tools/Document/page.css` (179 lines). Its colours and families are the
look's custom properties, which `Tools.View.Tokens.declarations` writes from `Tools.View.Look`.

| where | what it sets |
| --- | --- |
| `Look.lean`, the dark look | data: JetBrains Mono, Menlo, DejaVu Sans Mono, monospace, 13.288 px, 400; name: Source Serif 4, Georgia, serif, 15 px; label: the same, 13.5 px, italic; title: the same, 20 px |
| `page.css` | `@font-face` for Source Serif 4 (normal and italic) and JetBrains Mono; a scale from 17 px by 1.2 (`--s0` to `--s5`, 42.3 px); `h1` at `clamp(--s3, 5vw, --s5)`; `h2` `--s3` (29.4 px); `font-weight: bolder` twice; `font-optical-sizing: auto`; italic labels through `--e4-font-label-style` |
| `tools/view/looks/sans.tokens.json` | name, label and title: Avenir Next, Helvetica Neue, sans-serif, with weight 500 and "semi-bold" |
| the other nine look files | no face |
| `vendor/fonts/` | Source Serif 4 normal 122,360 bytes, italic 130,188 bytes, licence 4,314; JetBrains Mono 40,404 bytes, licence 4,524; `README.md` 1,332 |

Command: `wc -c vendor/fonts/*/*`. The brief places the fonts under `tools/Tools/Document/fonts`;
they are under `vendor/fonts/`, and `Drivers.Site` copies them into the site.

Where the faces disagree:

- A figure sets every text in the data face at the look's 13.288 px (`Tools.Document.Figure`). The
  page sets prose in the name face at the page's own 17 px, not at the look's 15 px.
- The page's headings take the title face at up to 42.3 px. The look's title is 20 px.
- A label is italic serif on a page and in a figure's description. A figure's own text is upright
  monospace.

### 1.6 `tools/Tools`, the top level: 23 modules, 5,826 lines

| module | lines | purpose | reachers |
| --- | --- | --- | --- |
| `Architecture` | 732 | the architecture map, measured from the tree | `make gen-architecture` |
| `ArchitectureRoles` | 355 | the map's one hand-written input | `Architecture`, `Exposure` |
| `Catalogue` | 149 | what an agent may write, read from the tables | nothing |
| `Document` | 324 | a generated document as data | the compiler, the site, the report |
| `Exposure` | 74 | the import report of row 332 (`#exposure_report`) | nothing |
| `Form` | 45 | the forms of a figure's node | `Document`, `View.Graph` |
| `HostProtocol` | 61 | the host protocol's schema | `make` `host-protocol` |
| `JsonBridge` | 256 | Lean's JSON and the tree's JSON | `Catalogue`, `WireText`, a battery |
| `LoadPaths` | 318 | which theorems carry load | a battery |
| `ProfileJson` | 102 | JSON views of type and row data | `Truth`, `TsGen`, OCaml5 |
| `ProgramStructure` | 82 | selected source families | `Effect4Gen`, OCaml5 |
| `RowTypes` | 226 | each row's target signature | `make` `target` |
| `RunChecks` | 293 | a recorded run's checks | a battery |
| `RunRecord` | 34 | one recorded host call | `RunChecks`, a battery |
| `Semantics` | 695 | the semantics report's model | `Drivers.Semantics` |
| `SemanticsDisplay` | 20 | display bytes of a statement | `Semantics` |
| `SemanticsDocument` | 434 | the report as a document | `Drivers.Semantics` |
| `Site` | 418 | the documentation site as one value | `Drivers.Site`, `Drivers.DocSpecimen` |
| `TyVectors` | 188 | the assignability pairs | `make` `target` |
| `TypeSpelling` | 30 | a type as a module spells it | `RowTypes`, `TyVectors` |
| `Variances` | 754 | declaration-site variance | `scripts/generate.py` |
| `WireTags` | 193 | the wire's tags | `Effect4Gen`, OCaml5 |
| `WireText` | 43 | the tool's wire as text lines | `Drivers.View`, `Drivers.Live`, two batteries |

Two modules for one thing:

- `Tools.Site` and `Tools.Document.Html` do not own one thing. `Html` is one of the four folds of the
  document algebra, beside `Markdown`, `Json` and `Figure`. `Site` is the shell of a set of pages:
  the head, the navigation, the contents and the footer. A merge moves the shell into the folds'
  folder or the fold out of it, and buys no line. They stay apart.
- `SemanticsDisplay` (20 lines) has one importer, `Semantics`. It merges by a move, but the
  semantics report is the proof graph seat's reader, so the merge waits for that seat.
- `RunRecord` (34) and `RunChecks` (293) are one recorded run. `Compiler.Run` reaches `RunRecord`
  alone, so they stay apart.

`Compiler.Page` (74 lines) is reached by one battery only (`Test/Codegen/CompilerGraphs.lean`). No
command of `Compiler.Main` writes the object page.

### 1.7 The proposal, in priority order

1. Cut the writer's prose from a program's document (`Compiler.Graphs`). The title becomes
   `todo · relations`. The introduction and the mapping part go. A caption becomes the figure's
   key, and "The figure in words" becomes `description`. A page then shows only the program.
2. Take one typography from the look. The base faces become a system sans stack and JetBrains
   Mono. `page.css` loses the serif `@font-face` rules, the 42 px `h1`, the `clamp` and `bolder`.
   The Source Serif 4 files go: 256,862 bytes with the licence.
3. Delete the unreached modules: the seven of §1.1 (1,481 lines), `Tools.Catalogue` (149),
   `Tools.Exposure` (74) and `Drivers.Emit` (120). Together, 1,824 lines.
4. Keep three drivers, and name each for a ruling:
   - `Drivers.CodecValues`: a recorded ruling keeps it;
   - `Drivers.SemanticsControls`: a lake executable of the coordinator's `lakefile.toml`;
   - `Drivers.Workspace`: the OCaml test's producer.
5. The pare-back of §3: the frames, the live loop, the specimens, the sheets and the C programs.
