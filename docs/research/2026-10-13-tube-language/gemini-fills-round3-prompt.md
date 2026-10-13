You are the semiotics reviewer of Effect4's visual language, round three of the fill review. In
round two you wrote `docs/research/2026-10-13-tube-language/fills.md`; the coordinator committed it
(`360f58acc`). Since then a planning seat wrote how every construct gets a picture and a film:
`docs/research/2026-10-13-motion-everywhere/README.md`. This round makes the two agree, and fills
the gaps the coordinator found in yours.

You write one file only: `docs/research/2026-10-13-tube-language/fills.md` in the checkout at
`/Users/pooks/Dev/lean4-effect4`. Improve it in place. Never edit any other file. Never run lake,
make or git. Never commit: the coordinator reviews and commits your file. Other agents work in the
same checkout; stay in your file.

## The owner's words (2026-10-13)

- "for fill vocab again do a gemini review of semiotics ensuring everything about the data is
  consistent and accords to programs semantics and semiotics iteratiovely adding, keep trying to
  unify design language and detailing"
- "we need to look out an bigger picture and not just queue so we can properly generate animations
  for everyting and the docs"

## Read first, in this order

1. Your `fills.md`.
2. The motion plan `docs/research/2026-10-13-motion-everywhere/README.md`: §2 (the constructs),
   §3.3 (the machine's moves and logs as pictures), §4 (the mapping: figure, contents, motion for
   each construct and change; §4.4 reads your verdicts), §5.2 (the docs' figures in one pen) and §8.
3. `docs/research/2026-10-13-tube-language/algorithms.md`, part E (units: a pill as a cut of its
   tube, impact as a swell of the wall, coalescence with a neck that grows as the square root of
   time), and parts G and H (the detailing of strokes and of motion).
4. `tools/Tools/View/Tube/Physics.lean` (units carried by the Intelligent Driver Model, stretched
   by speed with their area kept) and `tools/Tools/View/Tube/Queue.lean` (`OVERSHOOT`, the
   swells, the impact).
5. `docs/core/decisions.md` rows 354 and 370, read whole.

## What to change in `fills.md`

1. **The missing table.** Round two audits the family table but never maps each object to its
   fills. Add one table: for each of the fourteen objects of your §1, one row per state a reader
   must tell apart, with its figure (the glyph family and the mark's name in
   `tools/Tools/View/Glyph.lean` or `Tube/Glyphs.lean`), its contents state, and the change that
   enters it. Then compare every row with the motion plan's §4: mark it agrees, or differs, and for
   each difference propose one answer with its reason.
2. **Row 354 against your open verdict.** Row 354 (2) rules the docs' status "open" as a dashed
   outline. Your §6.3 refuses a dashed line on a tube. State the conflict plainly. Give the two
   answers: the tubes follow the docs' dashed mark, or the docs keep ◌ and the tubes draw open by
   a square end on purpose. Recommend one, and say what each costs. Do not rule: the owner does.
3. **Motion as built.** Rewrite your §4 on the nine motions of the plan's §4 table (grow, shrink,
   morph, carry, swell, parting, blend, coalescence, keep). Each change of state names its motion
   and the declaration that draws it today, or "planned" with the kit slice. Drop every law you
   cannot point to in a source. Check each constant you keep (`STAGGER`, `IMPACT`, `OVERSHOOT`,
   `SHEAR`) against its file. A queue's units now move by the driver model, not by a fixed stagger.
4. **Status alignment.** Check your §5.1 word by word against row 354 (2): proved filled, modulo
   half filled, a planned goal hollow, open a dashed outline, refuted the cross.
5. **The node as a contents state.** The plan's §8 question 7 proposes that a docs figure's node
   shows its status as a contents state in a small vessel. Say whether that makes one sign of the
   status marks and the fills, and where it would overload a mark.
6. **Plain marks.** Write ×, #, ● and the rest as plain characters, never as TeX.
7. **Questions.** End with one list of open questions for the owner, each one sentence: yours of
   round two and new ones, with no question the motion plan already asks.

## How to work

- Pass 1: make the changes. Pass 2: re-read every source you cited and correct the file. Pass 3:
  check every row of the new table against the plan's §4 and the glyph table. Then stop and say so
  in your reply, with a list of what changed in each pass.
- Plain English: one idea a sentence, at most 25 words, active voice, the dictionary's words
  (`docs/core/controlled-english.md` §3). Cite a declaration by its name and path, a decision by its
  row, a document by its path.
- State no fact you cannot point to in a source. Mark a guess as a guess.
- Two tones only, ink and ground, as the pen draws.
