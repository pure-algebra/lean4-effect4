# The visual semantics: one picture algebra per sort, folded from the language (2026-10-12)

Status: research note for a design grill (history, not authority). The owner, 2026-10-12, by
voice: give a visual language to every operation of Effect and to the machine; draw interruption,
fork and join with one consistent design; compose it into the Queue, the Pool and the streams;
derive it mechanically from the code, each module carrying its own derivation; draw the frames of a
continuation; link every picture with its text; render text well. And: "don't be afraid of
representing every abstraction ... make it a fold of the language: isn't that the most
estate-native?"

## 1. Know this first

- **The answer is a fold.** The tree already rules that every visual channel is the image of a
  fold (`docs/research/2026-10-09-visual-language-theory.md`, section 1). This note extends that
  rule to every sort: one picture algebra for each free object (the program, a value and its type,
  the machine's frames, a fiber, the run's journal), and a module's picture made from its cell's
  type, its steps and its model. A picture composes as its sort composes, because a fold is a
  homomorphism.
- **The words are a second algebra on the same keys.** A picture and its text are two folds of one
  value, and every mark and every sentence carries the key of the node it comes from (a path). So
  a sentence and its mark are linked by construction, not by a hand-written table.
- **Motion is the change of a fold.** A step of the machine changes the run; its motion is the
  change of the picture, timed per key (row 354, point 4; the view model,
  `docs/research/2026-10-11-view-model/README.md`, R-V1 and R-V2).
- **Semiotic clarity can be a check.** Moody's first principle asks that each symbol name one
  construct and each construct have one symbol. With the signature as data, the map from
  constructors to marks is data too, and "total and one to one" is decidable.
- **Most of the vocabulary exists.** `docs/design/design-language.md` (2026-09-08) assigned
  Bertin's variables, the score, the glyphs and the hues; its section 9 folded in string diagrams.
  What is missing is the folds that draw values, frames and fibers, and the module derivation.

## 2. What exists

| Layer | Where | State |
| --- | --- | --- |
| The vocabulary: score, lanes, bar lines, rests, the hollow and the filled mark, `×` `#` `⊣`, the bracket of a scope, the double rail of a mask, the fermata, the caesura; hue only for the four agents | `docs/design/design-language.md` §2, §3 | ruled in parts (rows 354, 366); the glyph table is prose |
| The string-diagram frame: the runtime wire, the spider (one completion, many resumes), the named discard, three wire grades | `docs/design/design-language.md` §9, `docs/design/string-diagrams-notes.md` | prose |
| The program's lines, a fold of the generic layer | `tools/Tools/View/Program.lean` (`EffAlgebra.ofLayer`) | landed |
| The program's flow: series, parallel, alternatives, regions, loops, as a fold; algebraic graphs | `tools/Tools/View/Flow.lean`, `AlgGraph.lean` | landed (rows 337, 365) |
| The laws every channel composes by: fusion, the product, fold induction | `tools/Tools/View/Algebra.lean` (`cata_fusion`, `cata_prod`) | landed |
| A run's frames: the program's lines and the graph of fibers per control | `tools/Tools/View/Run.lean` | landed; no machine frame, mask, scope or decision strip |
| The motion value and its two folds (sampled frames, CSS) | row 354 (4); lean4-whatwg S17–S19 (`Play`, `Step.sheet`) | the package has it; Effect4's port waits (P5) |
| The algebras of the core | `EffAlgebra` (generated), `TyAlgebra` (`src/Effect4/Program/Fold.lean`), `ValAlgebra` (`src/Effect4/Store/Carrier/Fold.lean`) | landed |
| A frame's algebra | `Prim` (`src/Effect4/Machine/Frames.lean`) | none |
| A fiber's life | five flags of `RunFiber`; the machine models note proposes one sum type `Life` (R4) | proposed |

## 3. The sorts and their pictures

| Sort | Free object | Its picture | What composition the picture keeps |
| --- | --- | --- | --- |
| program | `Eff` and its families | the process diagram: boxes for operations, wires for values, regions for a scope, an uninterruptible span and a provided layer; the runtime wire through every effectful box | `bind` is series, a fork beside its parent is parallel, a handler is an alternative; a spliced subprogram brings its own picture |
| type and value | `Ty`, `Val` | a value drawn by its type: a record a panel of fields, a list a row of boxes, an option a box that may be empty, a handle a tag on a tether, a `Deferred` the hollow mark that fills, a bounded number a gauge | a field's picture is its type's; a value of a record type is a panel of its fields' pictures |
| frames | the stack, a list of `Prim` | each frame a one-hole context of the program picture: the place its result returns to. The stack is the chain of holes, top first; the cursor stands in the innermost | a frame pushed by `bind` encloses the hole of its first part; a pop moves the cursor out one hole |
| fiber | `RunFiber`, `FrameFiber` | a lane with its life (running, parked on a token, pending, finalizing, exited) and its mask as a rail | the life a sum, the picture one mark per arm |
| run | the journal, `List Command`, acting on the run; the trace | the score: one column per step, a lane per fiber, the decisions as bar lines | the journal is a monoid: the score of a journal and its extension is the score extended |
| module | its `Cell` (a record type), its `Steps` (pure terms over the cell), its `Model` | the cell drawn by its type; a step's motion is the join of the cell before and after, keyed by the identities it holds (a request's `Deferred`); the model's picture beside it | no module draws its own motion: two modules with one shape of change move alike |
| stream | `Pull`, `Channel`, `Stream` | a wire observed over the journal (a marble line: a mark per element, `‖` at its end, the reasons at a failure); for composition, the process diagram with feedback | monoidal streams: a stream processor is a box with feedback (Di Lavore, de Felice and Román, 2022) |

**A frame is a hole.** A continuation is the rest of a program with a hole where the current
computation stands. Román names a diagram with a hole a monoidal context, and the design language
already calls a frontier "a run with the runtime wire dangling". So the frames need no new
picture: on the program's picture, the stack is drawn as the holes it will fill, innermost first,
each keyed by the `Point` path its frame names. A failure's walk is the cursor leaving holes until
a frame declares the failure arm (`ContAnswer.frame`); a mask frame (`setInterruptible`) is a rail
boundary on the same picture. A column beside lists the frames as text (Python Tutor's pattern:
the code pane, the state pane, a step control).

**A fiber's life needs one sum.** Its picture should be a fold, one mark per arm. Today the life is
five flags in many combinations. Either the view classifies the flags (a total function, its cases
named), or the machine gains `Life` (machine models R4) and the view folds it.

## 4. One vocabulary for concurrency

Every construct draws the same mark in the program's picture, the score and a module's motion.

| Construct | Mark | Where it comes from |
| --- | --- | --- |
| fork | an arrow from the parent's lane to the child's; the parent continues; a daemon dashed | design language §2 |
| join, await | the spider: one exit fused to every waiter; each leg fills as its exit arrives | §9.2; `Observer.resumeAwait`, `countdown` |
| race | a spider whose first exit settles; each loser receives `⊣` from the winner | `Race`, `raceSettled`, `cancelRace` |
| interrupt | `⊣who`: the blocked arrow (Talmy's Antagonist), from the interruptor or the host's bar line | §2, §5.1 |
| mask | the double rail; a recorded interrupt hovers above it until the rail ends (deferred, never dropped) | `FrameFiber.deferredInterrupt` |
| park, resume | the hollow box with its token, the filled box with the same token | `Parked`, `Cmd.resume` |
| scope, finalizer | the bracket `[k … k]`; the hollow then filled dot | `ScopeState`, `finalizerProgram` |
| exit | `‖` and the reasons in order: `×` fail, `#` die, `⊣` interrupt | `Exit`, `Cause` |
| frontier, halt | the fermata with the awaited row; the caesura with the reason | `Outcome`, `Stuck` |

The stream's marbles agree with this table: ReactiveX writes an error as `X` and an end as `|`; here
an end is `‖` and a failure is its reasons.

**Semiotic clarity as a check** (Moody, "The Physics of Notations", IEEE TSE 2009). Four anomalies:
redundancy (two marks, one construct), overload (one mark, two constructs), excess (a mark with no
construct), deficit (a construct with no mark). The generated signature lists every constructor of
every sort, so a glyph table keyed by constructor can be checked total (no deficit) and one to one
(no overload, no redundancy), and every mark of a picture can be checked to come from a constructor
(no excess). Moody's other principles (discriminability, transparency, complexity management,
cognitive integration, dual coding, graphic economy, cognitive fit) stay review points.

## 5. Text with the picture

- **Dual coding and contiguity.** Mayer's principles (spatial and temporal contiguity, signalling)
  ask that a word stand near its mark and play with it. A figure already carries its words
  (`Tools.Document.Figure`, the figure in words). The words become an algebra over the same keys,
  so each sentence names its node and the page can light the mark of the sentence a reader is on.
- **Linking with no script.** The site serves `script-src 'none'`. CSS can link by key:
  `:target` lights the mark of the part a link reached, and `:has()` lights a mark while its
  sentence is hovered, by one generated rule per key, as lean4-whatwg S19 writes one rule per
  moving thing under `[data-track]`.
- **Text quality.** The web faces are vendored (row 366, point 1); SVG text takes the same faces.
  The C player is first class (row 363, point 5) and draws text itself, so it needs a shaper and a
  rasterizer of its own (FreeType, with HarfBuzz for shaping), or a glyph atlas written by the
  build. That is a representation choice for the player.

## 6. Motion

A step's motion is the change of the picture under one command, timed per key. Each construct's
motion follows from its mark: a fork's child lane enters from the arrow; a spider's legs fill as
exits arrive; a race's losers take `⊣` and close; an interrupt under a mask hovers over the rail and
lands at its end; a take from a queue removes the first box and the rest slide forward. Time is
logical: one beat per command, equal, never a wall clock (DB-04; design language §4.1). A reader
who prefers reduced motion sees the end frames (row 354, point 5).

## 7. Examples

- The truth corpus: 93 programs with rc.112's verdicts (`harness/truth/corpus.json`,
  `result.json`), among them the six on masks and interruption (the understanding note, §5.3).
- Effect's own documentation examples, ported to the authoring surface.
- Row 366 (9): animations defined in code, perhaps derived from tests. A battery's finite run is a
  journal, so its score and its motion are folds of data the tree already has.

## 8. Prior art, and what it teaches

- **Visual Effect** (Kit Langton; `effect.kitlangton.com`, fork `github.com/effect-native/visual-effect`):
  animated nodes per combinator, with sound; a wrapper tracks an effect's state (idle, running,
  completed, failed, interrupted, died). It teaches that a per-combinator animation is engaging.
  Its timing is a wall clock and each combinator is drawn by hand, so it is not derived.
- **Effect-viz** (topheman): a fiber tree, a timeline and a log of a running program. Its timeline
  is proportional, which design language §8 rejects (no physical clock).
- **Python Tutor** (Guo, SIGCSE 2013): the code pane, the state pane of frames and objects, and a
  step control forward and back; about forty earlier tools share that design. The program
  picture, the stack of holes and the score are that design with a semantics under it.
- **Marble diagrams** (ReactiveX): a stream as a line over time, marks for elements, a bar for the
  end, `X` for an error.
- **Monoidal streams** (Di Lavore, de Felice and Román, LICS 2022; LMCS 2025): stream processors
  as a feedback monoidal category, drawn as string diagrams with feedback.

## 9. Slices, if the rulings go as recommended

1. **VS-1 the glyph table as data**: one row per constructor of `Eff`, the action terms, `Prim`,
   `RunEvent` and `RunDecision`, with its mark and its spoken word; the semiotic-clarity check.
2. **VS-2 the value picture**: a `TyAlgebra` and a `ValAlgebra` into pictures; the Queue's cell
   drawn by its type. Landed 2026-10-13: `Tools.View.Cell` (`typed`, a `TyAlgebra` into readers;
   `raw`, a `ValAlgebra`; parts put together by lean4-whatwg's `Scene.Layout`), the marks `panel`,
   `cells`, `slot`, `tag`, `atom` with rows for the sorts `type` and `value`, and the page
   `cells.html` (`v -V cells`): nine steps of the Queue, each its own step term evaluated.
3. **VS-3 a step's motion**: the join of two cell pictures keyed by handles; the Queue's six steps.
4. **VS-4 the stack of holes**: a `Prim` fold to holes on the program picture, keyed by `Point` paths.
5. **VS-5 the fiber's life**: the view's classification, or `Life` in the machine.
6. **VS-6 the score**: the journal's fold, the vocabulary of section 4, the decisions as bar lines.
7. **VS-7 the words**: the words algebra on the same keys, and the CSS that links them.
8. **VS-8 lessons**: the six mask and interruption programs as the first lesson pages.

## 10. Questions for the owner

Meaning, domain and representation only; the grill asks them.

1. The architecture: one picture algebra per sort, the words a second algebra on the same keys, the
   motion the change of the fold.
2. The program's picture: the process diagram with regions, or nested blocks, or the indented tree.
3. The frames: holes on the program's picture with a column of text beside, or a separate stack.
4. The fiber's life: classified in the view now, or a sum in the machine first.
5. A module's picture: derived from its cell's type alone, or with roles declared per field.
6. The vocabulary: section 4 as the one table, with the semiotic-clarity check.
7. Linking text and picture with no script, by CSS.
8. The C player's text: a shaper and a rasterizer, or an atlas from the build.

## 11. What this note does not establish

- No picture here was drawn or measured; the slices draw them.
- The literature is cited from search summaries and the projects' own pages, not read in full:
  Moody 2009, Mayer's principles, Guo 2013, the marble notation, Di Lavore and others 2022.
- Visual Effect's representation is read from its README and a mirror of its documentation, not
  from its source.
- A frame as a one-hole context is a reading of `Prim` against the program's picture; no theorem
  relates a frame to a hole yet. `Point` paths make the link plausible, not proved.
