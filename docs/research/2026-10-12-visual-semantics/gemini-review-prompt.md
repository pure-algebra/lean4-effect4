You are the visual-semantics reviewer of Effect4's vocabulary of marks. Work in the checkout at /Users/pooks/Dev/lean4-effect4. Another agent changes the code in the same checkout at the same time, so you write only the files named under "Output". The owner thinks some marks are questionable and wants each one reviewed, sorted by how it behaves, and redrawn where it fails.

## What the vocabulary is

Effect4 draws its language by folds: one picture for each sort (a program, a value, the machine's frames, a fiber, the run's journal), and every picture draws a constructor by the same mark. The table of marks is data, and a check holds it to Moody's semiotic clarity: every constructor has one mark, no two constructors of one sort are drawn alike, and no word is drawn by two marks. The marks will move: a machine step's motion is the change of the picture.

## Read first, in this order

1. docs/research/2026-10-12-visual-semantics/README.md: the plan (one picture algebra per sort; frames as holes; the vocabulary for concurrency; text linked to marks).
2. docs/core/decisions.md, rows 354, 365, 366 and 367: the rulings. Status is shown by shape, hollow promised and filled kept. Hue belongs only to the four agents. A motion is one first-order value per key, made only of translate, scale about a point, clip inset and opacity, which CSS states exactly. Nothing loops, nothing moves between two concurrent events, and a reader who prefers reduced motion sees the end frames. Time is one equal beat per machine command.
3. docs/design/design-language.md: §2 (Bertin's variables, assigned), §3 (the notation), §4 (time and causality), §5.1 (the force-dynamic words, after Talmy), §7 (palette, type, grid, motion), §9 (string diagrams: the runtime wire, the spider, the named discard, three wire grades).
4. docs/research/2026-10-09-visual-language-theory.md: §3 (a graph's properties as semantics), §4 (depth), §5 (motion with weight), §6 (a module's characteristic motion).
5. tools/Tools/View/Glyph.lean: `Shape` (30 marks), `Shape.means`, `Shape.glyph`, and `table` (147 rows: constructor, mark, variant, word, what it draws). tools/Tools/View/GlyphSheet.lean: `Shape.parts`, each mark's SVG on a grid of 24.
6. Look at the pictures, and judge them by eye: docs/research/2026-10-12-visual-semantics/review-input/marks.png (the marks large, then the vocabulary table, at twice the size) and review-input/sheet.png (the whole sheet, with every sort's constructors and their marks). The live page is http://localhost:8783/tools/view/out/docs/glyphs.html.

## The task

### Part A: review each of the 30 marks

For each mark, say:
- transparency: whether its form suggests what it draws, and the convention it borrows (music, chess, circuits, flowcharts, typography, string diagrams, maps);
- confusion: the marks a reader could take it for at 24 pixels, at 12 pixels and in monochrome. Look hard at these families: `box`, `call` and `library`; `hollowBox`, `filledBox` and `bracket`; the dashed ones, `rest`, `region`, `hole` and the dashed arm of `alternative`; `arrow` and `enter`; the straight strokes, `rail`, `barLine` and `exitBar`;
- fit with the design language: hollow promised and filled kept, value for the order of states, numerals for identity, hue for agents only;
- its rows: whether every constructor drawn with it fits. Look hard at the reads drawn as `probe`, `Eff.service` as `port`, `onExit` as `hollowDot`, every `ScopeState` arm as `bracket`, every `RunDecision` as `barLine` with its verb as the variant, and `CauseTerm.both` as `series`;
- a verdict: keep, adjust or redraw, with the reason.

### Part B: sort the marks by behaviour, their imagined physics

The owner's words: mark and categorize them by their behaviour, their imagined physics, so that the representation translates into animated visual semantics. Give each mark a physical kind, so that its motion follows from its kind and is never drawn case by case.

1. Propose a small set of kinds, about five to eight. A starting point that you may change: a body (a thing with an identity that persists and moves: a token, a value); a container (it holds others, and some must close: a scope, a region, a rail); a wire (it carries a value along a path: a sequence, a loop); a force (it acts and is spent: an interrupt, a host's decision); a bond (it relates bodies: a fork's arrow, the spider's legs); a vessel (it is promised hollow and kept filled); a mark in time (a bar line, an exit's bar, a fermata, a caesura). Justify the set from the sources: Talmy's force dynamics, Tversky's congruence, Heer and Robertson's staging, Lasseter's weight, Bertin's variables.
2. For each kind, give its motion grammar in the four primitives: how it enters, how it changes, how it leaves. For example, a container enters by a clip inset that opens from its start edge, a vessel is kept by the opacity of its fill, a body moves by a translation along an arc with the settling easing, and a bond grows by a clip along its direction (row 354, point 4: a route's reveal is a clip along its direction).
3. Give every mark its kind, and every row of the table whose kind differs from its mark's.
4. Write a storyboard, beat by beat, for each scene the owner named. One beat is one machine command, and each beat names the marks that move, their kind and their primitive:
   - a fork; a join and an await; a race, where the first exit settles and the others take `⊣`;
   - an interrupt outside an uninterruptible region, and one inside it, where the interrupt is recorded and deferred, never dropped: it waits over the rail and lands at the rail's end;
   - a frame pushed and popped: a hole opens, and a value flows into it; a failure's walk, where the cursor leaves holes until a frame takes the failure;
   - a scope that closes: its finalizers are kept in the reverse order of their registration;
   - a queue's offer and take: a box joins the end, the first leaves, and the rest slide forward;
   - a frontier: the fermata, where nothing moves.

Rules for motion: nothing loops; nothing moves between two concurrent events; a reader who prefers reduced motion sees the end frame of each beat; no motion stands for a duration, since the semantics has no physical clock (DESIGN-BASIS DB-04).

### Part C: redraw what fails

For each mark you judge "adjust" or "redraw", draw a proposal as SVG on the same grid of 24, as `Shape.parts` does: no fill, the stroke `currentColor` at width 1.5, round caps and joins, and a filled part with `fill="currentColor"`. Keep the family's logic: one stroke weight, one grid, and each promise-and-keeping pair as one form, hollow and filled. If a kind from Part B suggests a family of forms (every container closed on all sides, every force ending at a bar), redraw the family together.

## Output

Write two new files and nothing else:

1. docs/research/2026-10-12-visual-semantics/gemini-review.md, in this order:
   - the five findings that matter most, first;
   - Part A as a table: mark, transparency, confused with, rows that do not fit, verdict;
   - Part B: the kinds with their motion grammar, each mark's kind, the rows whose kind differs, and the storyboards;
   - Part C: each proposal with its reason and its SVG code;
   - the changes to the table, as a list: constructor, then its new mark or variant;
   - questions for the owner, on meaning, domain or representation only;
   - the sources you used. Cite what you read in this repository by its path. Mark anything recalled and not read as "recalled".
2. docs/research/2026-10-12-visual-semantics/gemini-proposals.html: a self-contained page, with no script and no external file (one small style element is fine). For each mark: the current drawing (copied from `Shape.parts`) beside your proposal, at 72 pixels and at 16 pixels, on the dark ground (ground #14110d, ink #ece6dc) and on paper (ground #f7f4ee, ink #1b1f2a), with the mark's name, its kind and one line of reason. Marks you keep appear once.

When the page is written, render it and look at it before you finish:

"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new --hide-scrollbars --window-size=1280,4000 --screenshot=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-12-visual-semantics/review-input/proposals.png file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-10-12-visual-semantics/gemini-proposals.html

The command asks for approval in your tab. Fix what the picture shows wrong, then write "Review complete." as the last line of gemini-review.md.

## Rules

- Write only the two files above and the screenshot. Never edit Lean, the Makefile, docs/core, generated files or the registers. Never run lake or make. Never commit.
- Ground each claim about the language in a named file or declaration. Never invent a constructor.
- Hue belongs to the four agents (machine ink, host amber, failure madder, resource verdigris). Propose no new hue and no hue for an identity.
- Write plain English: one idea per sentence, the present tense, no question put to the reader. Leave out the words powerful, seamless, robust, leverage, delve, comprehensive, unlock and journey.
- If a question needs the owner, write it in the review's questions and go on.
