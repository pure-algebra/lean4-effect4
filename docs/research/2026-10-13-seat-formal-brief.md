# Seat brief: the tube language as a diagram algebra (seat FORMAL, research with a probe)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it.

**The one thing to know first.** The owner asked whether the design language should be formal
within our algebra, "with a goal of simplifying, deepening representations". The vocabulary has
settled (decisions rows 369, 370 and 371), so the meaning layer can be stated now; the geometry
stays the pen's. Write the algebra, test a fragment of it in Lean, and say what it would replace.

## The hypothesis to test (the coordinator's reading, not a ruling)

1. **Correct encoding** is two laws. Mackinlay ("Automating the design of graphical presentations
   of relational information", 1986): a picture expresses all the facts and only them. Kindlmann
   and Scheidegger ("An algebraic process for visualization design", 2014): no two data draw alike,
   and a change of the data shows as a matching change of the picture. For us: the fold that draws
   a program is injective on its constructors, and drawing then stepping equals stepping then
   drawing (row 371 (3): fills follow the machine).
2. **The vocabulary is a string-diagram language.** Joyal and Street; Selinger's survey of
   graphical languages for monoidal categories. A tube is a wire, a fitting a box, one after
   another is composition, side by side with an air gap is the tensor, a loop is a trace, and a cut
   end is an open boundary (row 371 (2)). Row 367 already names monoidal streams for feedback.
3. **Two spiders.** Bonchi, Sobociński and Zanasi ("Interacting Hopf algebras"; graphical linear
   algebra): a copying spider is our broadcast (taps an air gap apart, each its own copy); an adding
   spider is our solid wye (amounts sum). Their bialgebra laws become equations between figures.
4. **Effects need a threaded wire.** Jeffrey ("Premonoidal categories and a graphical view of
   programs", 1997); Román ("Promonads and string diagrams for effectful categories", 2022). The
   fiber's control is a wire through each effect in order: the staff of the run's score
   (`tools/Tools/View/Tube/Score.lean`).
5. **State is a Petri net.** Meseguer and Montanari ("Petri nets are monoids", 1990); Baez and
   Master ("Open Petri nets"). Vessels are places, units tokens, a module's steps transitions; the
   conservation of units is a place invariant. A run's score is a process of the net.
6. **Motion is a change structure.** Cai, Giarrusso, Rendel and Ostermann ("A theory of changes
   for higher-order languages", 2014): a film is the derivative of the picture fold; the kit's
   keyed join implements it (the view model note, `docs/research/2026-10-11-view-model/`).

Verify every citation from a primary source you can reach, and mark any you cannot. Refute or
amend any point the literature or our tree does not bear out.

## Read first

- The tube language: `docs/research/2026-10-13-tube-language/README.md`, `glyphs.md`,
  `semiotics.md`, `fills.md`, `graph-alignment.md`, `algorithms.md`; decisions rows 336, 337, 354,
  362 to 371.
- The pen and its laws: `tools/Tools/View/Tube/` (`Form.lean`, `Draw.lean`, `Motion.lean`,
  `Glyphs.lean`: the 37 figures, `figure_ok`, `step_ok`, `morph_ok`; `Score.lean`) and
  `tools/Tools/View/Glyph.lean` (the marks and the sorts they draw).
- Our algebras: `docs/core/controlled-english.md` §3.5 (free object, algebra, fold, agreement of
  folds), `EffAlgebra` and `cata_eff` (search `src/Effect4/`), `hom_eq_cata_eff`; the view algebra
  and view model notes of 2026-10-09 and 2026-10-11; the kit's join and `Motion.Respects` under
  `.lake/packages/whatwg/Whatwg/Svg/Scene/`.
- The motion plan `docs/research/2026-10-13-motion-everywhere/README.md` (M3's role tables, M5).

## What to write: `docs/research/2026-10-13-tube-algebra/README.md`

1. **The signature.** The generators (the coordinator guesses about eight: pipe, series, air-gap
   tensor, adding spider, copying spider, vessel, valve, loop, port), each with its type, its
   picture and its meaning in the operational semantics; and the equations between them.
2. **The derivation of the vocabulary.** Each of the 37 figures, and each graph mark of
   `graph-alignment.md`, as a term of the signature, or a named gap where none fits.
3. **The fold.** The program's picture as one algebra over `Eff`'s signature, its fold a monoidal
   functor (or premonoidal, with the threaded wire); the two laws of point 1, stated.
4. **The token semantics.** Module cells as nets from row 367 (5)'s roles; conservation as an
   invariant; the run's score as a process.
5. **Motion.** The film as the derivative of the fold; the commuting square as a law that the
   pictures and the machine's steps satisfy.
6. **What it replaces and what it costs.** Which declarations and guards it would cut or turn into
   theorems, which slices of the motion plan it changes, and what stays the pen's (geometry).
7. **Questions for the owner**, at most eight, each with a recommendation.

Put a probe beside the note, `docs/research/2026-10-13-tube-algebra/Probe.lean`: a free signature
of the generators, an algebra into the pen's marks, and the fold over a five-constructor fragment
of `Eff` (pure, bind, fork, await, a cell's write), with `#guard`s of the two laws on a few
programs. It is a finite probe: say so.

Gemini contributes the sign side in its own file of the same folder,
`gemini-semiotics.md`: read it if it exists when you finish, and answer its points.

## Boundaries

- Write only the note and the probe (create the folder). Never edit the tree's code; never commit.
- Run the probe alone, with `LEAN_NUM_THREADS=2 lake env lean <probe>` from the checkout; no
  `lake build` and no `make`. Other seats build on this machine.
- Plain English, one idea a sentence, the dictionary's words (`docs/core/controlled-english.md`).
  Cite declarations by name and path, decisions by row. Mark a guess as a guess.
- Stop at about four hours. Reply with the signature, the two laws as stated, what the probe
  showed, and the questions.
