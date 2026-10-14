# Graph typography source audit

The smallest production change selects a face for each existing graph row and clips that row explicitly.
Keep the third level, the typed observation, in the specimen's inspector.
The graph retains its two strings, box dimensions, placements and connector construction.

Typography means the choice of font, size, weight, baseline and text fitting in this note.
A grapheme means a reader-visible character that can contain several Unicode code points.
An advance means the distance to the next character position, rather than the full painted glyph bounds.

## Scope and evidence

Proof role: no new theorem or proof obligation.
Evidence status: source audit.
Scope: the graph, page, SVG exporter, native painter and pinned SVG kit at the commits below.

- Effect4 base: `f25c74f3e2c6acd2bf4ad85c7cbd205dcc8952e0`.
- Branch: `codex/graph-typography-audit`.
- Worktree: `C:/Users/kokok/Dev/effect4-graph-performance`.
- Kit pin and installed package head: `e51195721f47fa767fb84f918dc439e76d83071f`.
- Kit source root: `.lake/packages/whatwg`.
- Lean toolchain: `leanprover/lean4:v4.33.1`, from `lean-toolchain`.

The audit changes only this note.
It measures no font, browser image, native image or accessibility consumer.
Source differences below establish different instructions to the renderers, without a measured pixel discrepancy.
The handoff at `docs/research/2026-10-13-codex-view-handoff.md` supplies historical context, not the current dependency pin.

## Existing text contracts

| Owner | Declaration and path | Current contract |
| --- | --- | --- |
| Font choices | `Font`, `Faces`, `Faces.of`, `Look.dark` in `tools/Tools/View/Look.lean` | Family list, milli-pixel size, weight and italic flag. No metrics or line height. |
| Font tokens | `readFont`, `readLook` in `tools/Tools/View/Tokens.lean` | Reads family, size and weight. The extension carries style. Refuses line height and letter spacing. |
| Drawing calls | `Call.cells`, `Call.text` in `tools/Tools/View/Picture.lean` | Cell text carries a natural cell budget. Face text carries an integer pixel budget. Neither carries a semantic text role. |
| Grid | `CELL`, `ROWH`, `BASE`, `BOXROWS`, `cellsAt`, `textAt` in `tools/Tools/View/Grid.lean` | Cells are 8px. Rows are 24px. Baselines are 16px. Graph boxes contain two rows. |
| Graph content | `GNode`, `Graph.boxWidth`, `Laid.boxCalls` in `tools/Tools/View/Graph.lean` | Two strings and `lit`. Width counts string code points. Both rows use the data face. |
| Flow content | `flowLayerWith`, `Flow.relabel`, `ofPage`, `WIDEST`, `nodeWidth` in `tools/Tools/View/Flow.lean` | Produces or replaces two strings. Width caps at 30 cells, or 240px. |
| Page content | `Line`, `lineEnds`, `lineCells`, `lineCalls` in `tools/Tools/View/Page.lean` | Text consumes room before its type. Notes use the proportional label face. |
| Checked type source | `sessionPageOf` in `tools/Tools/View/Program.lean` | Reads the checked result at the node path. An `ok` result supplies `Line.type`. |
| Geometry bounds | `PaintBounds.call` in `tools/Tools/View/PaintBounds.lean` | Text supplies no measured geometry and sets `unmeasuredText`. |

The default data face uses JetBrains Mono at 13.288px.
The default name face uses Source Serif 4 at 15px.
The default label face uses italic Source Serif 4 at 13.5px.
The default title face uses Source Serif 4 at 20px.
Each face also names fallback families in `Look.dark`.

`Laid.boxCalls` places its baselines at 16px and 40px within a 48px box.
The grid supplies no ascent or descent bound for the selected font.
Changing box height changes connector endpoints through `Laid.boxBounds`, `entryAt` and `exitAt` in `tools/Tools/View/Graph.lean`.
The specimen therefore needs face selection within the current rows, rather than a third graph row.

## Confirmed source gaps

### Width budgets differ between renderers

`SvgOut.flat` discards the width argument of `Call.text` in `tools/Tools/View/SvgOut.lean`.
It emits the entire string through `SvgOut.textNode`.
`paint_text` in `tools/view/paint.h` gives a positive width budget to Pango and requests an ending ellipsis.
A nonpositive native budget means unlimited width.
Explicit `Call.cut` and `Call.uncut` calls contain both renderers' output within a row rectangle.
They establish containment instructions, rather than equal truncation or equal glyph placement.

`SvgOut.textNode` always uses `Look`'s ink paint.
`paint_text` also selects the ink tone in `tools/view/paint.h`.
A face change cannot express a failure, resource or host text role.
Any later semantic text color needs explicit source metadata and a role-bearing drawing call.

### Cell counts differ from reader-visible characters

Lean's `String.length` counts Unicode code points, not bytes or UTF-16 code units.
The toolchain defines it through the character list in `Init/Data/String/Length.lean`.
`SvgOut.shown` truncates with `String.take` and appends an ellipsis in `tools/Tools/View/SvgOut.lean`.
The native `paint_cells` path also truncates by code-point count in `tools/view/paint.h`.
Neither path selects grapheme boundaries.
A combining sequence or joined emoji can therefore lose part of its sequence.
This consequence follows from the truncation rule, without a rendered Unicode probe.

`paint__to_cells` adjusts Pango cluster advances to the cell grid in `tools/view/paint.h`.
`SvgOut.textNode` emits font attributes without `textLength` or `lengthAdjust` in `tools/Tools/View/SvgOut.lean`.
The SVG exporter therefore supplies no instruction matching the native cluster advance adjustment.
Fallback or wide glyphs remain a host-dependent rendering risk.

### Data face size has different meanings

`paint_faces_open` calibrates the data face to `PAINT_CELL` in `tools/view/paint.h`.
It does not read that face's requested absolute size.
`SvgOut.textNode` emits the requested `Font.size` as SVG `font-size` in `tools/Tools/View/SvgOut.lean`.
Changing the data size token therefore changes the SVG instruction without changing the native calibration target.
Keep the data size fixed during the first typography specimen.

### Types and notes have no protected room

`Page.lineEnds` reserves room for text before calculating the type budget in `tools/Tools/View/Page.lean`.
A long text can leave no room for its type.
`Page.lineCells` adds the note's code-point count despite drawing the note in a proportional face.
That count supplies an allocation estimate, rather than a measured proportional width.
`GraphBounds.viewport` and `PageDrawing` retain `unmeasuredText` in `tools/Tools/View/GraphBounds.lean` and `tools/Tools/View/Page.lean`.
Neither fitted viewport establishes text ink containment.

### Font availability and accessible names remain external

`vendor/fonts/README.md` records the vendored font files, licenses and hashes.
`tools/Tools/Document/page.css` supplies the matching font-face rules with `font-display: swap`.
`tools/Drivers/Site.lean` copies those assets for the document site.
`SvgOut.picture` supplies font family names without embedding or loading font assets in `tools/Tools/View/SvgOut.lean`.
A standalone SVG can therefore use a different installed or fallback face.

`SvgOut.picture` and `linkedPicture` supply neither title nor description nodes in `tools/Tools/View/SvgOut.lean`.
`SvgOut.fileText` checks the HTML content context and XML serialization.
Those checks establish neither an accessible name nor font fitting.
This finding concerns these standalone exporter constructors, rather than every document wrapper.

## Pinned kit features to reuse

These paths resolve beneath `.lake/packages/whatwg` at the exact pin above.

| API | Primary source | Use and boundary |
| --- | --- | --- |
| `Metrics`, `width`, `Fits`, `FitsRow` | `Whatwg/Svg/Scene/Metrics.lean` | Host-supplied milli-unit advance and height bounds. The module measures no font. |
| `Metrics.any` | `Whatwg/Svg/Scene/Metrics.lean` | Joins supplied fallback bounds. It does not discover installed fonts. |
| `fits_draws`, `fitsRow_iff`, `fits_any`, `fitsRow_any` | `Whatwg/Svg/Scene/Metrics.lean` | Conditional fitting laws. The host must satisfy the supplied bounds and the `Draws` assumptions. |
| `Metrics.codes` | `Whatwg/Svg/Scene/Metrics.lean` | UTF-8 decoding without a correctness law. Code points do not establish grapheme boundaries. |
| `Piece`, `Shown`, `Label.fit` | `Whatwg/Svg/Scene/Label.lean` | Caller-defined pieces with width, priority and break metadata. Bounded row fitting and explicit cut, sign or none results. |
| `Label.fitAll`, `fitAll_distinct` | `Whatwg/Svg/Scene/Label.lean` | Fits a collection while distinguishing different piece lists when both appear as text. |
| `fit_fits`, `fit_subsequence`, `fit_mono`, `broken_balanced` | `Whatwg/Svg/Scene/Label.lean` | Existing fitting, retained-piece, room-growth and balanced-break laws under their stated assumptions. |
| `Layout` | `Whatwg/Svg/Scene/Layout.lean` | Reuses row, column, inset and stack construction for an inspector content block. |
| `Svg.titled`, `Svg.Frame.titled`, `titleNode`, `descNode` | `Whatwg/Html/Node/SvgDefs.lean` | Adds title, description and their ARIA references. The caller supplies a unique identifier stem. |
| Typed reference checks | `Whatwg/Html/Node/SvgDocument.lean` | Supplies document-level reference checks beyond content grammar and XML serialization. |
| Typography example | `workshop/LabelProbe.lean` | Splits qualified names into meaningful pieces and contrasts independent fitting with collection fitting. |

`LabelProbe` uses declared monospaced metrics, rather than measured proportional font metrics.
`Metrics.Draws` models one advance per code point.
The module explicitly excludes unsupported direction or shaping assumptions.
Advance fitting alone does not bound every horizontal glyph overhang.
`Label` searches possible breaks and cuts, so this audit makes no large-label performance claim.
Use short operation pieces first, rather than arbitrarily long program strings.

The schema accepts `textLength` and `lengthAdjust` in `Whatwg/Svg/Schema/Attributes.lean`.
Their presence does not justify scaling glyphs to force backend agreement.
The first specimen needs clipping and explicit face choices before that separate rendering decision.

## Proposed smallest production slice

The coordinator proposes `TextStyle` with `row1` and `row2` as `Option Face`.
`none` retains the existing cell text call.
`some face` selects proportional text within an explicit row clip.
`Laid.boxCallsWithText` shares the existing body and hit-box construction.
`Laid.boxCalls` remains its default wrapper.
`callsCachedWithText` and `callsWithText` carry the style through the existing graph drawing preparation.
These proposed declarations belong in `tools/Tools/View/Graph.lean`.

The allocation contract stays the current `Placed` values and the 48px height.
The routing contract stays the current connector calls and `Laid.routeWidth`.
Clipping contains text outside the row, but does not establish that every intended glyph remains visible.
The existing baselines provide no font-height theorem.

| Level | First specimen | Source |
| --- | --- | --- |
| Operation title | First graph row, `.name`; compare `.title` separately in the inspector | Project the operation constructor before `ownText` flattens its arguments. |
| Operands or code | Second graph row, existing `.data` cells | Project source arguments or an explicit type display. Retain the full string in the inspector. |
| Typed observation | Inspector block, `.label`, with visible judgment wording | Use `sessionPageOf`'s checked result and node key, or equally explicit checked metadata. |

`flowLayerWith` already receives the constructor and arguments before producing `ownText` in `tools/Tools/View/Flow.lean`.
Do not reconstruct those fields by parsing the flattened string.
The first specimen can supply projected labels and inspector metadata by the existing key.
It needs no new program syntax or third `GNode` string.
Do not infer success, refusal or runtime behavior from a face, a color or the operation name.

Use `Svg.Frame.titled` for the specimen's accessible picture name and full description.
Keep untruncated operation, operand and checked-type text in the inspector.
Give repeated pictures distinct stems and check their document references.

## Later seam, only when needed

A prepared text row can carry face, room, baseline, semantic pieces and its fitting result as data.
The caller can provide `Metrics` once for a named font profile.
Convert existing pixel budgets to milli-units before calling `Label.fit` or `Metrics.FitsRow`.
Do not treat `Font.size` as ascent or descent.
Prepare each row once and share the result between bounds and drawing consumers.
Any cache key must include the font profile, pieces, room, row count and relevant styling.

`Label.fitAll` becomes useful when independent abbreviation hides distinctions between operation names.
Semantic text roles become useful when checked metadata requires more than the current ink tone.
Both changes need named observations and narrow proof placement before theorem work.
This note adds no theorem and proposes no dependency update.

## Receipt

Read-only inspection uses `rg`, `Get-Content` and `git rev-parse` over the source paths above.
`git rev-parse HEAD` reports the Effect4 base above.
`git -C .lake/packages/whatwg rev-parse HEAD` reports the exact manifest pin above.
No unchanged source build or test runs in this slice.
The following commands pass:

```powershell
python scripts/check-language.py --strict docs/research/2026-10-13-graph-typography-audit.md
git diff --cached --check
```

The commit names only this research note.
