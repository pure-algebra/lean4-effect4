Round five, in this same conversation: a second look at the language's authoring obligations.
This round leaves the tube language and reads the language itself.

The owner builds this language for agents. An agent writes programs as first-order data, checks
them, composes them, states and proves claims about them, runs them against hosts, and ships them.
The coordinator wrote `docs/research/2026-10-13-authoring-obligations/README.md`: eight
obligations (O1 to O8), the mathematics of each, and an order. Read it whole, then check it
against the tree and the sources it names.

You write one new file only: `docs/research/2026-10-13-authoring-obligations/gemini-second-look.md`
in the checkout at `/Users/pooks/Dev/lean4-effect4`. Never edit any other file. Never run lake,
make or git. Never commit.

## What to write

1. **Each obligation checked.** For O1 to O8: is its statement right, and is its "today" true of
   the tree? Cite the declarations you read, by name and path. Say where the note is wrong.
2. **What is missing.** An obligation an agent needs that the note lacks, or one it should split.
   For each, the judgment or law it would be, and the requirement (R1 to R14,
   `docs/core/system-map.md` section 8) it serves.
3. **Reuse.** For each obligation, the existing abstraction it should reuse (for example the loop's
   convergence laws in `src/Effect4/Laws/Program/IterLimit.lean` for a definition block), and any
   place where the plan would build a second mechanism beside one that exists.
4. **Parallel work.** Which obligations can run at once, by the files each touches, and which must
   wait for another. Three are running now: PROC-5 (the coordinator), the claim records (seat
   CLAIMS, `docs/research/2026-10-13-seat-claims-brief.md`) and the checked replay (seat REPLAY,
   `docs/research/2026-10-13-seat-replay-brief.md`). Name the next two to start, and any collision.
5. **The mathematics.** For each object the note names (initial algebra, free monad and handlers,
   recursive handlers, weakest preconditions, graduality, higher-order effects, simulation), say
   whether the tree's literature marks point to a text under `docs/research`, and mark each
   reference read or recalled.
6. **Questions for the owner**, at most five, each one sentence with your recommendation.

## How to work

- Pass 1: write the file. Pass 2: re-read every source you cited and correct the file. Then stop
  and reply with what changed.
- Plain English: one idea a sentence, at most 25 words, active voice, the dictionary's words
  (`docs/core/controlled-english.md` section 3). Cite a declaration by name and path, a decision by
  row. Plain characters, never TeX. No line numbers.
- State no fact you cannot point to in a source. Mark a guess as a guess.
