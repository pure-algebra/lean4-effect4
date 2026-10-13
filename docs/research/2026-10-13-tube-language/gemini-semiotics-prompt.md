You are the semiotics reviewer of Effect4's tube language. Work in the checkout at /Users/pooks/Dev/lean4-effect4. Two other agents change code at the same time (one in this checkout, one in a worktree), so you write only the files named under "Output". The owner asked for a seat on the semiotics of the tube language: what each form of it signifies, why, and where a reader would misread it.

## What the tube language is

Every glyph of Effect4's visual language is now one body: a tube, a centreline swept by one width, drawn with one pen in cased layers (walls, then lumens, then plugs, then contents). Any glyph turns into any other by a morph of its tubes, and every moment of a morph keeps one bend law, so the transitions are lawful by construction. The pipework is the program's invariants; the contents are the run's state. The owner rejected literal drawn mechanisms (gears, ratchets: "crappy physics drawings from a high school test") and asked for solid bodies, one thick smooth line style, pipes with weight, bending and stress, plumbing fittings, and hydrology for flow. The next look is "plumbing drawing precision but designed emphasized deliberately as a custom drawing does, with simple algorithms for known techniques of depth, shading and noise". It is not a hand drawing.

## Read first, in this order

1. docs/research/2026-10-13-tube-language/README.md: the whole note. §4 (plumbing semantics) and §10 (effects, each for a meaning) list the signs as they stand.
2. docs/core/decisions.md, rows 354, 367 and 369 (search for "| 354 |", "| 367 |", "| 369 |"): the rulings. Hue belongs only to the four agents (machine ink, host amber, failure madder, resource verdigris). Status is shown by shape: hollow promised, filled kept. Width carries share; depth moves to tone and to haloed gaps at crossings. The default look sets noise to zero, and a look may turn it on. Nothing loops; a reader who prefers reduced motion sees the end frames; one beat per machine command.
3. docs/design/design-language.md: §2 (Bertin's variables, assigned), §3 (the notation), §4 (time and causality), §5.1 (the force-dynamic words, after Talmy).
4. docs/research/2026-10-12-visual-semantics/gemini-review.md: your own earlier review of the marks, with its seven physical kinds. tools/Tools/View/Glyph.lean: `Shape` (37 marks), `Shape.means`, `Kind` (body, vessel, container, wire, bond, force, cadence), `Kind.grammar`, and `table` (one row per constructor).
5. The code of the tube language, for what each sign is exactly: tools/Tools/View/Tube/Form.lean (the tube and its bend law), Draw.lean (the pen, the layers, the unit's one area, the pill, the hollow, the plug, the collar), Motion.lean (the step, the stroke changes, the swell), Queue.lean (the Queue as plumbing: vessel, float valve, backwater on a sagging inlet, surge, stagger, bubbles), Sheet.lean (every plate and film with its caption).
6. Look at the pictures: docs/research/2026-10-13-tube-language/review-input/tubes-still.png (the tube page, every film at its end), tubes-moving.png (the same page early in its films), glyphs.png (the current vocabulary of marks, not yet in tubes). The live pages are http://localhost:8783/tools/view/out/docs/tubes.html and http://localhost:8783/tools/view/out/docs/glyphs.html.

## The task

### Part A: the sign inventory

List every signifier the tube language has now, read from the code, not from the note alone: the tube, a straight piece, an arc, the bend radius, the bore and its ladder (4, 6, 8, 12, 16 px), the length of a vessel, the wall, the lumen, the three tones, an open end cut square, a closed end rounded, a junction (one lumen), a collar, a plug, a pill, a hollow pill (a bubble), a swell, a surge, a sag and its overshoot, a stagger, a valve's staging, an overflow, a relief, a circuit, a branch that grows from its root, the world off the page's edge. For each one give:

- what it signifies now, with the declaration that makes it;
- its mode after Peirce: icon (it resembles), index (it is caused by what it shows) or symbol (by convention);
- its precedent: the convention it borrows, from P&ID symbols (ISA-5.1, ISO 10628), engineering drawing (ISO 128), hydrology, transit maps, anatomy, or none;
- what a reader could take it for instead, at full size, at a third of the size, and in monochrome.

Then judge the inventory by Moody's principles ("The Physics of Notations", 2009): semiotic clarity, perceptual discriminability, semantic transparency, complexity management, cognitive integration, visual expressiveness (Bertin's variables, and which variables are still free), dual coding, graphic economy, cognitive fit. Name each conflict: one form with two meanings, two forms for one meaning, a form with a meaning a reader cannot recover, and a form that claims a law that does not hold (a tee claims conservation, so a broadcast drawn as a tee lies).

### Part B: the kinds and the marks as tubes

The vocabulary of marks (`Shape`, 37 marks over 7 kinds) must be redrawn as tubes. A second agent builds the forms; you give their meaning. For each kind, propose its tube family: what plumbing element it is, what its contents mean, how its ends are made, and what stays fixed when one of its marks turns into another. Then, for each of the 37 marks, give:

- its tube form in words, after its kind's family (for example: a hollow dot is a short closed vessel of one unit, its unit hollow; a filled dot is the same vessel with its unit kept);
- why the form signifies its meaning, and its precedent;
- the marks it must stay distinct from, and the one feature that tells them apart;
- the marks it turns into during a run (a promise kept: hollow to filled; a scope closed: open bracket to bracket; a fork joined: arrow to spider), so that the morph between them is short: the two forms should differ in as few pieces as possible.

Look hard at these: the cadence marks (a bar line, an exit bar, a fermata, a caesura), which stand in time and carry nothing; the force (an interrupt, `⊣`), which must read as an impulse that is spent and that a rail can hold back; the containers (a scope's bracket, a region, a rail, a record, a list), which enclose; and the bodies that are not contents (an operation, a call, a library, a probe). A tube that carries nothing must still read as a tube of the same family.

### Part C: a grammar of motion

List the verbs of motion the tube language may use: flow along a tube, fill, drain, swell, sag, surge, a valve that opens and closes, a branch that grows or withdraws, a morph of a whole tube, a hollow that fills. For each verb give its meaning, the condition under which it may appear, and the law it shows (continuity, conservation, cause before effect, first in first out). Then give the rules that keep motion from becoming decoration: what never moves (the pipework, unless the program changes), what moves only with a command, and what may never move at the same time.

### Part D: what the look may mean

The styling pass adds depth, shading, noise and stress. For each, say what it may signify and what it must not:

- depth: which tube passes over which at a crossing, and the order of tone from near to far;
- shading: a lit side and a shaded side on a tube, and on a unit, after the shade-line convention of patent and engineering drawings (light from the upper left, heavier edges on the shaded side);
- noise: a grain on the walls (the metal, the invariants) and none on the contents, or another rule;
- stress: the pressure behind a closed valve (Barlow, hoop stress `σ = p r / t`) shown on the wall by value, never by hue.

Keep to row 354: no new hue, value for the order of states, width for share. Recommend one rule for each technique.

### Part E: the composed drawing

How does a reader read a whole drawing of tubes? Give the conventions a schematic needs: the direction of flow, where the world enters and leaves, a legend, which text appears and where (dual coding), and how a drawing of many modules stays readable (complexity management). Draw on P&ID and transit-map practice.

## Output

Write three files and nothing else:

1. docs/research/2026-10-13-tube-language/semiotics.md, in this order:
   - the five findings that matter most, first;
   - Part A as a table, then the judgment by Moody's principles;
   - Part B: the kinds' families, then a table of the 37 marks (mark, kind, tube form, why, distinct from, turns into);
   - Part C, Part D, Part E;
   - the changes you propose to the language, as a list, each with its reason;
   - questions for the owner, on meaning, domain or representation only;
   - the sources you used. Cite what you read in this repository by its path. Mark anything recalled and not read as "recalled".
2. docs/research/2026-10-13-tube-language/semiotics-sketches.html: a self-contained page, with no script and no external file (one small style element is fine). For each kind, its family; for each mark, your proposed tube form, at 96 pixels and at 32 pixels, on the dark ground (ground #14110d, ink #ece6dc) and on paper (ground #f7f4ee, ink #1b1f2a). Draw every sketch with the tube pen only, as the code does: for a tube with contents 12 px wide, first its wall, a stroke 22 px wide in the wall tone (the ink mixed 32% into the ground); over it its lumen, a stroke 16 px wide in the lumen tone (ink 8% into ground); over that a unit, a stroke 12 px wide in the ink with round caps. A closed end is round (`stroke-linecap: round`), an end open to the world is cut (`butt`). Every bend has a radius of at least 15 px. No other shape: no circle, no rectangle, no arrowhead, no text inside a mark. A mark's name, kind and one line of reason go under it as text.
3. A screenshot of that page: render it and look at it before you finish:

"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new --hide-scrollbars --window-size=1280,6000 --screenshot=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-13-tube-language/review-input/sketches.png file:///Users/pooks/Dev/lean4-effect4/docs/research/2026-10-13-tube-language/semiotics-sketches.html

The command asks for approval in your tab. Fix what the picture shows wrong, then write "Review complete." as the last line of semiotics.md.

## Rules

- Write only the three files above. Never edit Lean, the Makefile, docs/core, generated files or the registers. Never run lake or make. Never commit.
- Ground each claim about the language in a named file or declaration. Never invent a constructor or a sign the code does not have; a sign you propose is marked "proposed".
- Hue belongs to the four agents. Propose no new hue and no hue for an identity or a status.
- No literal mechanism: no gear, ratchet, spring or lever drawn as a picture. Everything is a tube, its contents and its fittings.
- Write plain English: one idea per sentence, the present tense, no question put to the reader. Leave out the words powerful, seamless, robust, leverage, delve, comprehensive, unlock and journey.
- If a question needs the owner, write it in the questions and go on.
