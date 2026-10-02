# Brief for Gemini, part two: the words (2026-10-01, ~23:10)

Part one (`seat-B/brief-gemini-implementation.md`) is the slice: the registry module, the
attribute and census, the producer, the schema, five commits. This brief is the writing that the
slice leaves open on purpose (spec v3 §1 "Not built": "no `docs/core/semantics.md`", "no
literature locators"), and it is the part the owner wants from you: definitions in precise
language, copy a reader can trust, every citation read off a vendored page. Codex's audit
(`docs/research/2026-10-01-metaprogramming-audit/brief-codex-metaprogramming.md`) covers only
Lean's own metaprogramming layers; it writes none of this.

Order: part one's C1–C3 and C5 first (the registry file and the driver must exist); then the
registry content (§1 below) in the same branch; the prose (§2–§4) may start at any time under
`docs/research/`. Base and rules as part one, with the coordinator's amendment at its end.

## The one rule that caused v2's errors

Nothing is written from memory. A theorem's statement is printed from the environment, never
typed as a "formal judgment" (v2's `seq_typed` dropped the world and the `Fits` premise; v2's
`denoteR_typed` judgment was not the statement). A name is written only after `grep` finds it in
the declaring module, with its namespace as declared (`Effect4.Program.Typed.seq_typed`, not
`Effect4.Laws.…`). A locator (chapter, section, page, theorem number) is written only as a row of
`docs/research/2026-10-01-semantics/citations-audit.md` gives it, with status `verified` or
`corrected`; an `unverifiable` locator is written as `assumed` with "owner's copy owed". A
register id is written only if `Test/Counterexamples/REGISTER.md` has the row. A decisions row is
cited by number only after reading it.

## 1. The registry's full content (`tools/Tools/SemanticsRegistry.lean`, after part one's C2)

The slice holds one concept and four claims (spec v3 §9.1). Fill the registry for the ten concepts
of v2 §3 (`store-typing`, `residual-program-typing`, `scope-lifetime-finalization`,
`reactive-scheduling`, `exact-codecs`, `subtyping-algebra`, `initial-algebras-folds`,
`context-requirements`, `host-session-protocol`, `translation-simulation`), re-cutting your
`gemini/lemma-census.md` and `chapter-table.md` as claims:

- One `Claim` per lemma of each concept's standard list (the owner's roles: inversion, canonical
  forms, weakening, substitution, progress, preservation, monotonicity, transitivity,
  antisymmetry, decidability; plus adequacy, simulation, compatibility, fundamental property),
  with `title` in words and `pointer` one of: `witness` (the theorem exists; the driver prints
  its statement and checks the ceiling), `goal` (a ledger goal; the driver reads wanted/proved),
  `refutedBy` (a register row and its witness), `absent` (a required claim no declaration
  states: the reason says whether it is owed, with the decisions row, or does not apply, with
  why), `assumed` (an external statement with no local evidence). The `absent` entries are the
  point of the exercise: they are the bound the owner asked for, visible before any Lean is
  written.
- `contestedBy`: every register row whose attacked statement is the claim's (as `denoteR_typed`
  has CE-020, -021, -022).
- `literature`: `LiteratureRef`s whose `work` is a key of `sources/README.md` and whose `locator`
  is an audit row; `relation` one of the five words. A claim with no verified literature has an
  empty list, not a guess.
- `Cut`s: rows 163 (function values), 128 (exact embeddings and templates), 138, 117 (closed
  requirement rows) and the others the owner's §7 names (status note §7, lines 133–183), each
  with `excluded` and `reason` in one sentence.
- `defaultModules` per concept, from your tagging plan (`note.md` §4), checked against the tree.

Then run the producer. Every dangling name, unknown register id and unknown source key is a
refusal with a location; fix the registry, not the driver. Commit as C6 (`tools/Tools/SemanticsRegistry.lean`,
`generated/semantics.json`, `generated/semantics.md`) after `python3 scripts/check-semantics.py`.

## 2. `docs/core/semantics.md` v1, concept-first, as a draft under `gemini/semantics-v1.md`

The one new authority of the owner's plan (status note §7: "owning the judgments and their
metatheory"; the system map keeps the goal, sorts, arrows and requirements and points to it; the
decisions register keeps the decisions and points to it; no fact owned twice). Rewrite your
`gemini/semantics-draft.md` (seventeen chapters, five subsections each) as ten concept sections
in spec v3's order, each with:

1. **What the judgment says**, in words, naming the judgment and its file:line.
2. **What the literature demands** for a system with this feature: the standard lemma list,
   cited by audit row (TAPL chapter and page as the contents give them; ATTAPL ch. 6 Crary for
   logical relations, ch. 3 Henglein–Makholm–Niss for effect types, ch. 8 is modules and is not
   cited for relations; PFPL ch. 28 for control stacks, chs. 39–41 for concurrency).
3. **Our cut**, the applicability decision by decisions row, one paragraph (row 163: no
   function values, so no arrow clause in `Fits` and no step index is needed for *this*
   membership relation; say that, not "step-indexing is unnecessary": Codex review §7).
4. **The claims**: a pointer to the generated table (`generated/semantics.md`, the concept's
   section), never a hand-written status. Prose names the theorems, the table carries the
   status.
5. **Open obligations and the rows they wait on**: by ledger scope and decisions row.

Apply Codex review §7's corrections as a checklist, each in the section it concerns: a machine
transition is a small step on a configuration (code, frames, stores, queues); `TypedProg` is a
world-indexed residual typing judgment, "weakest precondition" only as a proposed claim;
`inhabited` is a fold over finite syntax, not recursive-type unfolding; `hom_eq_cata_eff` is
provable pointwise equality, not definitional; `machineTyped_not_halted` projects a maintained
invariant and is not progress; the M7 fragment's empty-host-table restriction stays visible on
every summary; `Ty` has no record or app constructor today. Nothing the system map or the
register owns is restated: point to it by section.

## 3. The glossary (a section of §2's draft; the object-language half)

The owner's concern (~22:00): our documents say "syntax", "elaborate", "print" and "read" for
our objects, and Lean has `Syntax`, elaboration (`TermElabM`, `CommandElabM`), the delaborator
and the formatter. Write the table: our word → what it denotes here (the free object, the arrow
kind) → our type and file:line → Lean's layer with the same word → the same thing or not. At
least: **syntax** (our free objects `Eff`, `Ty`, `Term`, `Store.Val`, `Representation`; Lean's
`Syntax` is the host's concrete syntax, used only by the authoring sugar and the commands);
**elaborate** in its three senses today (Lean's; the authoring surface's `elaborate`/`elaborateModule`,
`Authoring.lean:306`, total by refusal; `denoteR` as hefty-algebra elaboration, system map
§9 line 284) with a proposed distinct word for each where a document blurs them; **print**,
**render**, **read** (the exact embeddings, Rendel–Ostermann) against Lean's delaborate and
format; **lift** and **sugar** (the authoring macros); **census** and **gate** (the commands).
Codex's audit supplies the Lean-layer column's facts in its note (A8); draft the table from
the tree now and mark that column `reading` until Codex's note lands; the coordinator merges.

## 4. The bibliography

`sources/README.md` is the record of what is vendored; the registry's `LiteratureRef`s are the
citations. Propose in the receipt how `generated/semantics.md` renders a bibliography from the
registry (one entry per `work` key, with the constructions of ours that cite it), so the
document's bibliography is measured, not drawn; implement it in the driver only if it is one
function and one table.

## 5. A definitions pass (proposals only; the coordinator lands)

Read `AGENTS.md`'s Vocabulary bullets and `docs/core/system-map.md` §§4–5 and §9 as a reader
who must apply them. Where a definition is loose, propose the tighter sentence in a table:
current sentence (file:line) → proposed sentence → what it rules in or out that the current one
does not → the theorem or definition that justifies the change. At most twenty rows. Do not edit
those files. Also list the system map §9 literature marks you can verify from the vendored
texts (the audit §5 names three that hold) and the ones that need the owner's copies.

## Produce

`gemini/semantics-v1.md` (§2 with §3 inside it), the registry content as commit C6 (§1), the
proposals of §4 and §5 in `gemini/receipt-documentation.md` with the receipt (AGENTS.md's
format: the one thing first; files; commands and results; the evidence class of every section;
what is bounded or assumed). The coordinator reviews the draft against the tree, promotes it
to `docs/core/semantics.md`, and points the system map, the register and `docs/STATE.md` at it.
