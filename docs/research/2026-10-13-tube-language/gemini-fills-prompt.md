You are the semiotics reviewer of Effect4's visual language, a second round. In the first round you
wrote `docs/research/2026-10-13-tube-language/semiotics.md`; the coordinator took most of it. This
round is about **fills**: what the inside of a tube means, for every kind of object a program
holds, and whether one vocabulary serves them all.

You write one file only: `docs/research/2026-10-13-tube-language/fills.md` in the checkout at
`/Users/pooks/Dev/lean4-effect4`. Create it, then improve it in passes. Never edit any other file.
Never run lake, make or git. Never commit: the coordinator reviews and commits your file. Another
agent changes code in the same checkout, and a second Gemini session writes `docs/site/`; stay in
your file.

## The owner's words (2026-10-13)

- "i think we also need o consider semantics of filled tubes that may need to change for different
  structures and semantics to represent all objects"
- "for fill vocab again do a gemini review of semiotics ensuring everything about the data is
  consistent and accords to programs semantics and semiotics iteratiovely adding, keep trying to
  unify design language and detailing"
- "we need to look out an bigger picture and not just queue so we can properly generate animations
  for everyting and the docs"

## Read first, in this order

1. The coordinator's proposal, `tools/view/out/proto/fills.html` (read it as text): seven fill
   states (empty, units, promised, level, full, open, failed), each echoing a status mark of the
   docs (● ◐ ○ ◌ ×), a table of what each means in each of the seven glyph families, and four
   questions.
2. `docs/research/2026-10-13-tube-language/README.md` (the tube language; §13 the styling pass),
   `glyphs.md` (the 37 marks as tube figures, the seven families), and your `semiotics.md`.
3. The pen as built: `tools/Tools/View/Tube/Draw.lean` (the proportion: a 2 px line, a 3 px
   margin, units as circles of 10, bodies 10, 14, 20, 28 px stepping by √2; `Fill`, `Tone`,
   `unitOf`, `hollowOf`, `plugOf`), `tools/Tools/View/Tube/Glyphs.lean` (the families' builders),
   and `tools/Tools/View/Glyph.lean` (the vocabulary of marks: `Shape`, `Kind`, the sorts each
   mark draws).
4. What the program's data is: `docs/core/semantics.md` (the ten concepts), `docs/core/system-map.md`
   (the sorts and arrow kinds, §2 to §4), `docs/core/machine-state.md` (what the machine holds:
   fibers, frames, scopes, handles, stores, logs), and `docs/core/controlled-english.md` §3 (the
   dictionary: use its words in their one meaning).
5. The docs' own marks: `docs/core/decisions.md` rows 354 (status by shape), 362 to 370 (the
   studio, the glyphs, the tube language, the pen).

## What to write

1. **The objects.** List every kind of object a picture must show, from the semantics and the
   machine: values, promises and deferreds, fibers, frames, scopes and their finalizers, resources
   and handles, stores and cells, queues, semaphores and pools, streams and channels, failures and
   causes, interrupts, the host's calls and replies, decisions and frontiers. For each: what it is
   (cite the core document), its states over a run, and which states a reader must tell apart.
2. **The fills.** For each object and state, the fill that shows it, from the seven states or a
   change you propose. Say why: the meaning it accords with, and its sign class (icon, index or
   symbol). Check every cell of the proposal's family table against the objects; mark each cell
   kept, changed (to what) or dropped, with the reason.
3. **Consistency.** Find every place where one fill would mean two things, or one meaning would
   take two fills, across the families, the docs' status marks and the graph figures. Propose one
   rule for each.
4. **Change as motion.** For each change of state (a promise kept, a scope closed, a failure
   raised, a resource released, a unit taken), how the fill changes in a film: fills in place,
   drains, cracks, parts by an air gap, merges. Keep each motion one that the tube language can
   draw (a morph of tubes, a unit carried by its law, a swell, a parting, a blend).
5. **Unity of the design language.** Where the tube figures, the docs' graph figures and the
   status marks should share one rule of line, fill, join and motion, and where they differ on
   purpose.
6. **The four questions** of the proposal, each with your recommendation and its reason.
7. **Open questions for the owner**, at the end, each one sentence.

## How to work

- Pass 1: write the whole file. Pass 2: re-read every source you cited and correct the file.
  Pass 3: check every table cell against the objects of part 1 and the 37 marks. Then stop and
  say so in your reply, with a list of what changed in passes 2 and 3.
- Write plain English: one idea a sentence, at most 25 words, active voice, the dictionary's
  words. Cite a declaration by its name and path, a decision by its row, a document by its path.
- State no fact you cannot point to in a source. Mark a guess as a guess.
- Two tones only, ink and ground, as the pen draws. No colour, no grey, no hatching unless you
  argue for it against row 370.
