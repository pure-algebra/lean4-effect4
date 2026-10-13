Round six, in this same conversation. First, your second look's errors, checked against the tree.
Then one focused task.

## Your errors

1. PROC-5 landed (`4e75f71a4`) in `src/Effect4/Laws/Effects/Mrec.lean` and
   `src/Effect4/Laws/Program/Block.lean`. You named `src/Effect4/Laws/Program/DenoteDefs.lean` and
   "fragment definitions". No file of that name exists, and PROC-5 touched no fragment: its laws
   have no fragment premise. Invocations are read as rows appended after the host's, so the block
   reuses `denoteRows` with no copied arm.
2. Your sequencing says PROC-6, HO-4, HO-5, G10 and the fragment widening wait for PROC-5. PROC-5
   has landed, so those waits are gone. G10 (SynchronizedRef from Ref and Semaphore) never waited
   on it: it composes existing modules.
3. You picked the next tasks without the proof graph. `#goal_impact` at this head ranks the open
   planned goals by what they block. `Evaluating.countdown_parks_positional` blocks 11 claims and
   R1, R6 and R9: all of M7. Read `docs/research/2026-10-13-open-goals-probe/README.md`.
4. Your content-store finding is right in substance: no `Content` instance for `Eff` exists. The
   generated instances live in `src/Effect4/Store/Domain/Derived/*.lean`, not `Node.lean`.

Your other checks held: the session tool's application is the empty one (`tools/Tools/Session.lean`);
rows 373 (4), 373 (6) and 336 (7) say what you quoted.

## The task: a reuse census for six seats

The owner's rule: the proof graph is dense, so every new definition or lemma must first be searched
for. A duplicate is a defect. Six seats run or start now. Their briefs:

- `docs/research/2026-10-13-seat-claims-brief.md` (CLAIMS: the application and claim records)
- `docs/research/2026-10-13-seat-replay-brief.md` (REPLAY: the checked replay route)
- `docs/research/2026-10-13-seat-flow-brief.md` (FLOW: the answer-flow history producer)
- `docs/research/2026-10-13-seat-appcheck-brief.md` (APPCHECK: checking at a real application)
- `docs/research/2026-10-13-seat-address-brief.md` (ADDRESS: the address algebra and `rebaseRefs`)
- `docs/research/2026-10-13-seat-countdown-brief.md` (COUNTDOWN: the countdown goal)

For each seat, write:

1. **What it must reuse.** The existing declarations it builds on, each by name and path, found by
   searching `src/`, `tools/ProofGraph/Registry.lean` and the aesop banks
   (`src/Effect4/Laws/Auto/RuleSets.lean`). Search by the concept, not only the brief's words.
2. **What it might duplicate.** Each definition or lemma its brief implies that already exists
   under another name, with both names.
3. **What aesop can do.** The rule sets that fit its proofs, and any lemma that belongs in a bank
   so that later proofs close by search.

You write one new file only: `docs/research/2026-10-13-authoring-obligations/gemini-reuse-census.md`.
Never edit any other file. Never run lake, make or git. Never commit.

## How to work

- Search the tree for each item; cite only what you opened. Mark a guess as a guess.
- Pass 1: write the file. Pass 2: re-open every declaration you cited and correct the file. Then
  stop and reply with what changed.
- Plain English, one idea a sentence, at most 25 words. Cite a declaration by name and path. Plain
  characters, never TeX. No line numbers.
