Round two of your semiotics review, in this same conversation: the graph figures and the tube
language as one design language.

Since your first round, the owner ruled the tube language's styling (decisions row 370), the
motion plan and the open mark (row 371), and a planning seat wrote how every construct and every
docs figure gets a picture and a film (`docs/research/2026-10-13-motion-everywhere/README.md`).
The kit's slice S24 draws graph edges as tubes: routes of straight stubs and arcs, splits by
Murray's angle and da Vinci's widths, and arrivals docked on a frame
(`Whatwg/Svg/Geometry/Tube/Route.lean` in the kit at `~/Dev/lean4-whatwg-svg`). The owner's
word now: "align visual semantics between graph representations and tube design language".

You write one new file only: `docs/research/2026-10-13-tube-language/graph-alignment.md` in the
checkout at `/Users/pooks/Dev/lean4-effect4`. Never edit any other file; another Gemini session
writes `fills.md` at this moment. Never run lake, make or git. Never commit.

## Read first

1. The graph figures as built: `tools/Tools/Document/Figure.lean` (the site's figures),
   `tools/Tools/View/Graph.lean` and `tools/Tools/View/Organic.lean` (the layout and its organic
   strokes), `tools/Tools/View/Program.lean` and the `Flow*.lean` modules (the program's graph),
   and `fiberGraph` in `tools/Tools/View/Run.lean` (the run's graph of fibers).
2. The rows that rule them: `docs/core/decisions.md` rows 336, 337, 354, 365, 368, 369, 370, 371.
3. The tube language: `README.md`, `glyphs.md`, your `semiotics.md`, `fills.md` (round three, as
   committed) and `algorithms.md` parts C and D (branching, merging, arrival), all in
   `docs/research/2026-10-13-tube-language/`.
4. The motion plan, §4 (the mapping), §5.2 (one pen for the site's figures) and §5.5 (edges as
   tubes); and the score of a run, `tools/Tools/View/Tube/Score.lean`.

## What to write

1. **The census.** Every mark of every graph figure today: node shapes, edge kinds (data, control,
   fork, exit, back edge, relation), arrowheads, labels, clusters, status marks, emphasis. For
   each: what it means, which figures use it, and the row that rules it.
2. **The mapping.** For each mark, its tube form: which glyph family and figure, which join (a
   solid join that shares fluid, or an air gap that shares nothing), which contents state, and its
   motion. Mark each kept, changed (to what) or left different on purpose, with the reason.
3. **One sign for one meaning.** Every place where a graph figure and a tube figure would show one
   meaning two ways, or one way for two meanings. Propose one rule each. Row 371 (2) already keeps
   two signs for "open" on purpose: say whether any other pair should differ the same way.
4. **Edges.** Which edge kinds become tubes that carry (data, an exit to its waiter) and which stay
   relations that carry nothing; how a direction reads (row 371 took the recommendation: a smaller
   flare at the target than at the source); where a split shares fluid and where it parts.
5. **The node.** Row 371 rules that a node shows its status as a contents state. Say how a node
   becomes a vessel or a body without losing its label, and how a cluster becomes a container.
6. **Questions for the owner**, at most eight, each one sentence with your recommendation.

## How to work

- Pass 1: write the file. Pass 2: re-read every source you cited and correct the file. Then stop
  and reply with what changed in pass 2.
- Plain English: one idea a sentence, at most 25 words, active voice, the dictionary's words
  (`docs/core/controlled-english.md` §3). Cite a declaration by name and path, a decision by row.
- Accord with the program's operational semantics (row 371 (3)): a mark shows what the machine
  or the program does. Where a figure must simplify, name the simplification.
- State no fact you cannot point to in a source. Mark a guess as a guess. Two tones only.
