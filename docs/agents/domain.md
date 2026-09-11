# Domain docs

How the engineering skills consume this repo's domain documentation. Nothing new is created
for them: the glossary and the decision record already exist under other names.

## Before exploring, read these

- `AGENTS.md`: the router and the authority map. Read it in full.
- `docs/DESIGN-MAP.md`: the framework and the vocabulary, layers L1 to L5, the
  representations, the conversions and the grade of evidence each carries. Cited by section.
  This is the glossary.
- `docs/ARCHITECTURE.md`: the tree, the module boundaries, the dependency direction, the
  API seam.
- `docs/DESIGN-BASIS.md` (`DB-nn`, settled) and `docs/DESIGN-ISSUES.md` (`DI-nn`, open): the
  decision record.
- `docs/GENERATED.md`: the generated families and their gates.
- The relevant `docs/research/` notes: the history of design and discussion. The entry point
  for any dispatched seat is `docs/research/2026-09-05-dispatch-brief.md`.

## What is not here, deliberately

No `CONTEXT.md`, no `docs/adr/`. Do not create them. When `domain-modeling` resolves a term,
it proposes the wording for `docs/DESIGN-MAP.md` inside the current research note; when it
records a ruling, it names the `DI` row the ruling belongs to. The owner writes both into the
tracked files.

## Use the estate's vocabulary

- Evidence words are **proved**, **reproduced**, **tested**, **stamped** (DI-32). Never
  "sound", "equivalent", "preserves" or "complete" without the exact judgment, theorem or
  gate (`AGENTS.md` § Trust).
- Register rows by id. Layers by the map's names. An rc.112 behaviour by the vendor line it
  transcribes.
- The standing design rule: whatever the first implementation instinct is, go one level
  higher in Lean, closer to the algebra, and reach for metaprogramming; project mechanically
  and never take on extension or reimplementation debt. Survey the math in the tree before
  recommending.

## Truth and history

Truth is the Lean model under `src/Effect4/` and `Effect4.Laws`, the algebra in the `effects`
package, and the design record above; a little of the lineage is in `~/Dev/foldlab`. History
is `docs/research/` (gitignored). When a note and the Lean disagree, the Lean is right and
the note receives a correction line.

## Flag conflicts

If your output contradicts a `DB` row, say so explicitly with the row id rather than silently
overriding it.
