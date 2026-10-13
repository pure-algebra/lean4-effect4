You are the visual reviewer of Effect4's living-quantities language. Work in the checkout at /Users/pooks/Dev/lean4-effect4. Another agent changes the code in the same checkout at the same time, so you write only the files named under "Output". The owner wants numbers and quantities drawn as a visual language of flow and change, organic, with a feeling of life, made by nature-inspired algorithms modelled in Lean, and fast. A first version exists. Review it hard, and propose what makes it better.

## What exists

1. The language, sketched by hand: docs/research/2026-10-13-living-quantities/README.md (four layers: units in places, flows along channels, the run as one level, totals as channels) and sketch.html. A picture of the sketch: review-input/sketch.png.
2. The first derived version, every picture computed from the Queue's real steps: the page http://localhost:8783/tools/view/out/docs/living.html, and its picture review-input/living.png. Its code:
   - tools/Tools/View/Living/Physarum.lean: Tero et al.'s adaptation (Science 327:439, 2010, equation 1 and p. 441), dD/dt = f(|Q|) − D with f(q) = q²/(1 + q²), folded over the run, with three proved laws.
   - tools/Tools/View/Living/Soft.lean: Wyvill's soft objects as a field on a grid, marching squares, Catmull-Rom closing; the membrane is the band between two levels of one field.
   - tools/Tools/View/Living/Organism.lean: the Queue's places (world, inlet, vessel, outlet, world), the marking of each frame, the flux of each channel from the keyed join of two markings, the channels' widths from the conductivity's fourth root (Hagen–Poiseuille), the units on top.
3. The scene's values: tools/Tools/View/CellSheet.lean (the Queue at capacity 2, nine steps, each its own step term evaluated) and the page http://localhost:8783/tools/view/out/docs/cells.html.
4. The rules every picture keeps: docs/core/decisions.md rows 354, 366, 367 and 368 (status by shape, hollow promised and filled kept; hue only for the four agents; motion only by translate, scale, clip and opacity, nothing loops, nothing pulses, one equal beat per command, reduced motion shows the end frame; no ornament without a meaning), and docs/design/design-language.md §2, §5.1, §7, §9.
5. The marks and their physical kinds: tools/Tools/View/Glyph.lean (`Kind`, `Kind.grammar`) and the review that set them: docs/research/2026-10-12-visual-semantics/gemini-review.md.
6. The package that will carry the general abstractions: the asks W16 to W22 in docs/research/2026-10-12-whatwg-requests.md.

## The task

### Part A: review what is drawn

Look at living.png and sketch.png as a designer and as a reader who must understand a queue. For each layer and each mark, say what reads, what misleads and what is missing:
- Does a reader see capacity, held, offers waiting and takers waiting, and their relation, without reading a number?
- Does a channel's width mislead? Its width is the history of use (conductivity), not the flux of this step. Say whether a reader can tell the two apart, and how.
- Is the membrane honest? It swells with what it holds; say whether a swelling could be read as a quantity it is not.
- Hierarchy, contrast, density, rhythm, the arcs, the captions, the empty space. Be concrete: name the frame and the place.
- Fit with the rules of item 4. Name every place that breaks one.

### Part B: nature-inspired algorithms

The owner: "look for some advanced nature inspired algorithms we could easily consign for this task… we can model basically anything in Lean, that's the point… and we can make them fast." For each candidate, say what it would draw here, what semantics it carries (it must mean something in the Queue, Semaphore, Pool, PubSub or Stream: no ornament), how to make it exact and fast (whole numbers, no square root in an inner loop, a grid or a list, a fold), and which law would make it trustworthy. Consider at least: space colonization (Runions, Prusinkiewicz), Murray's law and the pipe model, the constructal law, Vogel's phyllotaxis for units in a round place, Lloyd relaxation and Voronoi cells for packing, reaction–diffusion, differential growth, L-systems, flocking, river networks (Horton–Strahler ordering), and anything better you know. Rank them for this task. Mark what you recall and did not read as "recalled".

### Part C: storyboards and proposals

1. Storyboard the motion of three beats on the organism (offer 30 when full, take 4 that lets the waiting offer in, offer 40 that wakes taker 7): which bodies move, along which path, by which primitive, with what easing, and what the membrane and the channels do in the beat. Keep every rule of item 4.
2. Draw proposals as a self-contained page: what you would change in the organism, and how the run's level (sketch section 3) and the totals (sketch section 4) should be drawn with the same algorithms. Draw on the dark ground (ground #14110d, ink #ece6dc, rule #48433c) with no hue. Every proposal names the algorithm that would compute it.

## Output

Write these files and nothing else:

1. docs/research/2026-10-13-living-quantities/gemini-review.md, in this order: the five findings that matter most; Part A; Part B as a ranked table with the reasons after it; Part C's storyboards; the changes you propose to Organism.lean, Soft.lean and Physarum.lean, as a list (what, where, why); questions for the owner on meaning, domain or representation only; the sources you used, each read one by its path or URL, each recalled one marked "recalled".
2. docs/research/2026-10-13-living-quantities/gemini-proposals.html: a self-contained page with no script and no external file (one small style element is fine).

When the page is written, render it and look at it before you finish:

"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new --hide-scrollbars --window-size=1200,3200 --screenshot=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-13-living-quantities/review-input/proposals.png file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-10-13-living-quantities/gemini-proposals.html

Fix what the picture shows wrong, then write "Review complete." as the last line of gemini-review.md.

## Rules

- Write only the files above and the screenshot. Never edit Lean, the Makefile, docs/core, generated files or the registers. Never run lake or make. Never commit.
- Ground each claim about the language in a named file or declaration. Never invent a constructor or a step of the Queue.
- Hue belongs to the four agents. Propose no new hue.
- Write plain English: one idea per sentence, the present tense, no question put to the reader. Leave out the words powerful, seamless, robust, leverage, delve, comprehensive, unlock and journey.
- If a question needs the owner, write it in the review's questions and go on.
