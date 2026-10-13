# Seat brief: pictures and motion for every construct and the docs (seat MOTION, a plan)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it. A planning
seat: it reads code and writes one note; it changes no code.

**The one thing to know first.** The owner: "we need to look out an bigger picture and not just
queue so we can properly generate animations for everyting and the docs". The tube language, its
pen and its physics exist for one module's film (the Queue). This seat plans how every construct
of a program, and every figure of the docs, gets a picture and a film from the same parts.

## Read first

- The tube language: `docs/research/2026-10-13-tube-language/README.md` (§13 the styling pass),
  `glyphs.md`, `semiotics.md`, and the briefs `seat-kit-brief.md` and `seat-kit-s24-brief.md`.
- The pen and its motion as built: `tools/Tools/View/Tube/Draw.lean`, `Motion.lean`,
  `Physics.lean` (units carried by the Intelligent Driver Model), `Queue.lean`, `Sheet.lean`,
  `Glyphs.lean`, `GlyphPage.lean`, and the kit's `Whatwg/Svg/Geometry/Tube/` and
  `Whatwg/Svg/Scene/` under `~/Dev/lean4-effect4/.lake/packages/whatwg/`.
- Every other producer of pictures: `tools/Tools/View/` (the graph and flow layouts, the program
  graph, the run views, cells, the glyph sheet, the live view, `Organic.lean`, `Picture.lean`,
  `SvgOut.lean`, `Page.lean`) and `tools/Tools/Document/` (the documents and the site's figures).
  The viewer script `tools/view/v` names what each page shows.
- The design notes: `docs/research/2026-10-11-docs-design-language/README.md`,
  `2026-10-11-view-model/README.md`, `2026-10-09-visual-pipeline.md`,
  `2026-10-12-designer-workflow/README.md`; decisions rows 337, 354 and 360 to 370 in
  `docs/core/decisions.md`.
- What a program is and does: `docs/core/semantics.md` (the ten concepts), `docs/core/system-map.md`,
  `docs/core/machine-state.md`; the machine's moves and their events (search `FrameMove` under
  `src/Effect4/`).
- The prototypes the owner has seen: `tools/view/out/proto/physics.html`, `fills.html`,
  `ratios.html` (plain HTML; read them as text or render them with headless Chrome).

## What to write: `docs/research/2026-10-13-motion-everywhere/README.md`

1. **The census of pictures.** Every producer: what it draws, from what data, which pen, what
   motion today, its page size and its generation time where you can measure them cheaply.
2. **The census of constructs.** Every construct a program holds or a run does (each concept, each
   module of the factory: Queue, Semaphore, Pool, Latch, Deferred, Scope, Stream, Channel, fork,
   join, race, timeout, schedule, the host's calls), with the states a reader must tell apart and
   the changes between them.
3. **One pipeline from a run to a film.** How a run's events (the machine's moves and logs) become
   pictures and steps by the kit's data join, the pen, the physics and the SMIL writer, so any
   program animates and not only the Queue. Say what is general already and what is
   Queue-specific today.
4. **The mapping.** For each construct and change: its tube figure, its fill (Gemini is reviewing
   the fill vocabulary in `fills.md`; cite it if it has landed), and its motion (a morph, a carry,
   a swell, a parting, a blend, a coalescence).
5. **The docs.** How the site's figures (the proof graphs, the open work, the concept pages) take
   the same pen, with stills for reduced motion and films where a figure shows a change; and how
   the graph figures' edges become tubes (slice S24 of the kit).
6. **Budgets.** Page size and generation time per figure and per page, and the sampling rules
   that hold them (moments per change, shared paths by `use`).
7. **The slices**, ordered, each with what it delivers, the files it touches, what it needs from
   the kit, and how it is checked. Mark which can run in parallel.
8. **Questions for the owner**, one sentence each.

## Boundaries

- Read anything; write only the one note (create its folder). Never edit code, never run `lake`
  builds of the tree (reading files and rendering existing pages with headless Chrome is fine),
  never commit. The coordinator reviews and commits.
- Plain English, one idea a sentence, the dictionary's words (`docs/core/controlled-english.md`).
  Cite declarations by name and path, decisions by row.
- Stop at about four hours, or at a question only the owner can answer; reply with a summary of
  the plan's first slices and the questions.
