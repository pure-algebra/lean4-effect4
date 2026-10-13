# Seat brief: the vocabulary of marks as tubes

Status: brief (history, not authority). 2026-10-13. Base `25c798d50` on `refactor/phase1-phase3`.
The coordinator dispatches it, reviews the branch and merges it.

**The one thing to know first.** Every one of the 37 marks of `Tools.View.Glyph.Shape` becomes a
figure of tubes, drawn by the tube pen, so that any mark turns into any other by the morph of its
tubes, and every moment of that morph keeps the bend law. The forms carry meaning; they are never
an illustrated mechanism.

## The owner's words

- Literal drawn mechanisms look like "crappy physics drawings from a high school test". Wanted:
  solid bodies or curves, one line style "thicker smooth", pipes with weight, bending and stress,
  plumbing fittings, hydrology for flow, "simple consistent reducible integer filling".
- The reason for one thick-pipe body: solid-body transitions can turn any glyph into any other,
  "a latch or a right"; so "build your glyphs all to be provably transformable in that way".
- "plumbing drawing precision but designed emphasized deliberately as a custom drawing does".
  Not a hand drawing.

## Read first

1. `docs/research/2026-10-13-tube-language/README.md`, the whole note.
2. `docs/core/decisions.md` rows 354, 367 and 369. Hue only for the four agents; status by shape,
   hollow promised and filled kept; width carries share; nothing loops.
3. `tools/Tools/View/Glyph.lean`: `Shape` (37 marks), `Shape.means`, `Kind` (seven kinds),
   `Shape.kind`, `Kind.grammar`, `table`, `sorts`, `check`. `tools/Tools/View/GlyphSheet.lean`:
   how the current page draws them.
4. `tools/Tools/View/Tube/`: `Form.lean` (the tube, the bend law, `Tube.mix_ok`, `straight`,
   `Tube.reverse`, `Tube.cut`), `Draw.lean` (the pen: `bodyOf`, `unitOf`, `hollowOf`, `plugOf`,
   `collarOf`, `Mark`, `Mark.gone`, `still`, the layers), `Motion.lean` (`Picture`, `Picture.step`,
   `film`), `Sheet.lean` (the plates and films as examples of use).
5. `docs/research/2026-10-12-visual-semantics/gemini-review.md`: an earlier review of the marks,
   with the seven kinds.
6. The pictures: `docs/research/2026-10-13-tube-language/review-input/tubes-still.png` (the tube
   page) and `glyphs.png` (the marks as they are drawn now).

## What to build

### Stage 1: the figures, with their laws

A new module `tools/Tools/View/Tube/Glyphs.lean`:

- **One family per kind.** For each `Kind`, a builder of tube figures, and a docstring that says
  what the family is in plumbing terms and what its contents mean. A starting point, which you may
  change with a reason: a body is contents (a pill, or a plug of the wall's tone); a vessel is a
  short closed vessel of one unit, its unit hollow (promised) or filled (kept); a container is a
  tube that encloses, open where a close is owed; a wire is a pipe that carries; a bond is a
  fitting that joins tubes (a tee conserves, a manifold copies, and the two must look unlike); a
  force is a surge that a plug stops; a cadence is a collar or a plug across a pipe that carries
  nothing.
- **One figure per mark**: `figure : Shape → List Mark`, in one cell of the page (the coordinator
  suggests 96 by 96 pixels at one pixel to the pixel, a ladder bore; your call). The marks of a
  figure carry keys by role (`wall`, `lumen`, `unit`, `plug`, …) shared across figures, so that the
  kit's join matches the parts that persist when one mark turns into another, and the rest enter
  or leave from their root.
- **The laws.** Every tube of every figure keeps the bend law: a theorem by `decide` if it is
  fast, else a `#guard` over the decidable `Tube.ok` with a comment why. Then the statement that
  matters: any two figures morph lawfully at every moment, from `Tube.mix_ok`, `pad_ok` and
  `Piece.zero_ok` (the root of an entering or leaving tube). Place it as the note's §3 places
  `Tube.mix_ok`.
- **Discriminability.** A `#guard` that no two shapes have the same figure. If you can state a
  cheap measure of how far apart two figures are (pieces that differ, the units' count), guard the
  pairs that `Glyph.check` must keep apart within one sort.

### Stage 2: the page

A new module `tools/Tools/View/Tube/GlyphPage.lean`, its blocks and css, and a page
`tube-glyphs.html` from `tools/Drivers/GlyphSheet.lean` (one import and one `page` line) and a
branch `tube-glyphs` in `tools/view/v` beside `tubes`. The page shows:

- each kind's family: its rule in one sentence and its marks as figures;
- every sort of `Glyph.sorts`, each constructor with its figure, small;
- films of the morphs that a run makes: a promise kept (hollow to filled), a scope closed (open
  bracket to bracket), a fork joined (arrow to spider), an interrupt held by a rail and landing at
  its end, a hole filled by a value. Use `film` and the kit's join as `Sheet.lean` does.

### Stage 3: the semiotics

A Gemini seat reviews the semiotics of the tube language at the same time
(`docs/research/2026-10-13-tube-language/semiotics.md`, when it exists). The coordinator sends you
its verdicts when they arrive. Take them up where they hold against the code, and say in the
receipt which you took and which you did not, with the reason.

### Stage 4: the note and the receipt

- `docs/research/2026-10-13-tube-language/glyphs.md`: each kind's family and why, a table of the
  37 marks (mark, kind, figure in words, the marks it turns into), the laws with their paths, what
  the laws do not establish, what the tube language lacked and what you added locally, and how
  the other pictures (the program's process diagram, the cell, the frames, the journal) would take
  these figures up in the decomposition pass. Mermaid for any order or pipeline.
- `docs/research/2026-10-13-seat-glyphs-receipt.md`: first the one thing the coordinator must know
  before merging; then the base and head commits, the changed files, the exact commands and their
  results, the axiom output, the open obligations, and what is bounded.

## Boundaries

- **Your files**: `tools/Tools/View/Tube/Glyphs.lean`, `tools/Tools/View/Tube/GlyphPage.lean`, the
  one import and line in `tools/Drivers/GlyphSheet.lean`, the branch in `tools/view/v`, and the two
  Markdown files above. Force-add the Markdown (`git add -f`).
- **Not yours**: `Form.lean`, `Draw.lean`, `Motion.lean`, `Queue.lean`, `Sheet.lean`, `Trig.lean`,
  `Marking.lean`, `Glyph.lean`, `lakefile.toml`, `docs/core`. The coordinator runs the styling
  pass on `Draw.lean` at the same time: `Mark` may gain fields with defaults, and its tones and
  layers may change; `still`, `film`, `bodyOf`, `unitOf`, `hollowOf`, `plugOf` and `collarOf` keep
  their signatures. A primitive you need in `Form.lean` or `Draw.lean` goes in your module under a
  heading "to move into Form" (or Draw), and the receipt names it.
- **No literal mechanism.** Every mark is tubes, their contents and their fittings: no circle, no
  rectangle, no arrowhead, no text inside a figure.
- **Crispness.** Every width a whole, even number of pixels; straight runs on whole-pixel axes; a
  picture at one pixel to the pixel; open ends cut, closed ends round.

## Rules of the tree

- Work in your own worktree on your own branch. Copy the packages copy-on-write first:
  `cp -c -R /Users/pooks/Dev/lean4-effect4/.lake/packages .lake/packages`, then build; Lake's
  artifact cache restores what the main checkout already built.
- Build narrowly, one `lake` at a time: `LEAN_NUM_THREADS=3 lake build Tools.View.Tube.Glyphs`,
  then the page module and `lake build view-pages`, then
  `.lake/build/bin/view-pages tools/view/out/docs`. Never `lake build` with no target, never
  `make`.
- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error. A hand `simp` is `simp only [...]`; no `simp_all`, `first`, or `try`.
- After the last stage, audit your modules with a scratch file outside the tree:
  `import Tools.View.Tube.GlyphPage`, `import ProofGraph.AxiomAudit`,
  `#axiom_audit Tools.View.Tube.Glyphs Tools.View.Tube.GlyphPage`, run by `lake env lean FILE`.
  Report what reaches `Classical.choice`; the SVG writers reach it through the kit's `SvgNode`.
- Look at what you draw. Render the page with headless Chrome into your scratch directory and read
  the picture: `"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new
  --hide-scrollbars --window-size=1100,6000 --screenshot=OUT.png file://PAGE`. Add
  `--force-prefers-reduced-motion` to see every film at its end, and `--virtual-time-budget=N`
  (milliseconds) to see a film part way. Fix what the picture shows wrong.
- Commit at the end of each stage, by named paths, with a message that says what and why, ending
  with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Never push. Never edit
  `tools/view/make_videos.py`.
- Markdown follows `docs/core/controlled-english.md`: one idea per sentence, the present tense,
  declarations cited by name and path, never by line.
- Disk: the data volume is nearly full. Run `df -h /System/Volumes/Data` before the first build;
  if less than 5 GiB is free, stop and report.

## Stop rules

Stop and hand back, with the receipt, at any of these: a false statement you cannot repair; a
change you need in a file that is not yours; a question of meaning, domain or representation for
the owner; less than 5 GiB free; four hours of work.
