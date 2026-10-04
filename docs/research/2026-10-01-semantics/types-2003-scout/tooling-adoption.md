# Make the theory visible through the existing semantics report

The existing tooling is a useful foundation: it reads propositions from Lean, validates evidence
and emits a strict Effect Schema report. Two small documentation slices would expose the
literature more reliably. A later dependency slice can use the existing graph checker. These
are adoption instructions, not changes made to Gemini's active branch.

## Measured boundaries at a8cc8866

The isolated Lean probe imports the actual `Tools.Semantics` and `ProofGraph.Ledger` artifacts.
Ten source/import matches and 26 saved artifacts were checked against their build traces before
execution. Lean 4.33.1 ran with `-j1 -M4096 -DwarningAsError=true` and a 90-second bound; exit 0,
8.359 seconds. The trivial control witness uses no axioms. These are finite tooling controls,
not new M5 or runtime evidence. The first probe draft failed to elaborate; its source/log and the
corrected passing run are retained separately in the temporary evidence folder.

| Control | Observed result | Consequence |
| --- | --- | --- |
| Extract two declared goals with `readGoal`, check valid evidence | Accepted; zero registered edges | Exact evidence checking does not infer a dependency plan. |
| Supply one dependency explicitly | Accepted; one edge retained | Existing `Goal.dependencies` and graph checks are usable. |
| Supply a cycle, an unknown dependency, or the wrong theorem proposition | Each refused for its intended reason | Retain this checker; another proof ledger is unnecessary. |
| Build a report with a nonexistent nonblank source key and locator | Accepted; citation retained in JSON | Source existence is currently outside the producer's check. |
| Render that report as Markdown | Citation absent | Even supplied citations are invisible in the generated chapter report. |
| Supply a blank work or invalid relation | Refused | The boundary is content resolution, not missing shape checking. |

The companion Bun runtime probe used the current `ts/eff/semantics.ts` and Effect 4.0.0-rc.112.
Six controls agreed: the existing report and three proposed citation shapes decode; blank work,
unknown relation and an extra `verified` flag are rejected; a fabricated source still decodes in
the full report. No TypeScript compiler ran; this is runtime decoder evidence. No generators,
installations or full builds ran.

Relevant source owners:

- `tools/ProofGraph/Ledger.lean:26`: `readGoal` initializes empty dependencies.
- `src/Effect4/Laws/Auto/Obligations.lean:46`: the collector retains those goals unchanged, then
  calls `ProofGraph.check` at `:88`.
- `tools/ProofGraph/Ledger.lean:72`: evidence, edge references and cycles are checked.
- `tools/Tools/Semantics.lean:218`: nonblank work/locator and allowed relation checks.
- `tools/Tools/Semantics.lean:321`: Markdown renderer, currently without literature output.
- `ts/eff/semantics.ts:48`: the existing three-field `LiteratureRef` schema.

## Slice V1: make source keys resolve

This is already assigned in `brief-gemini-proofs.md`, under “One small tooling slice, any time”.
Do not duplicate that assignment. Supply the three audited book rows from `book-scout.md` to it.

Keep `sources/README.md` as the source-index owner and `citations-audit.md` as the locator/audit
owner. Add the planned Key column, preserving the actual author, edition, copy path/checksum and
whether the evidence is full text, contents-only or an unavailable cited work. The producer must
refuse an unknown work key. An explicitly indexed unavailable work remains a valid citation;
it must not be described as a verified theorem body. This does not require another source registry.

For new book citations, use the proposed audit rows `TYPES-A1`, `TYPES-B1`, `TYPES-W1`. Do not
pretend all existing free-form locators are already stable audit IDs: the current registry mixes
raw section/page strings and `audit Pn`. Preserve that distinction during migration. Work-key
validation is a complete small first slice; exact locator resolution is a separately bounded
extension using the same existing audit, not an unreviewed parser of arbitrary citation prose.

**Completion.** Known key passes; unknown key refuses with claim/key location; indexed
contents-only and unavailable sources keep their evidence limits. Index/audit inputs participate
in the existing freshness checks (`SEMANTICS_INPUTS` and the script's `INPUTS`). Retain stale-key,
unknown-key and duplicate-key controls. Keep semantic statuses unchanged. No literature claim is
certified merely because its string resolves.

## Slice V2: show citations beside the evidence

Extend the current `renderMarkdown` rather than authoring another evidence table by hand. Below
each selected claim's printed statement, render its literature entries: source, locator and
relation, with links into the existing source index/audit where resolved. Also cover claims
without a theorem statement, such as absent and assumed claims. Empty literature lists need no
placeholder prose. Keep multiple citations on a claim, and distinguish `analogy`, `proofTechnique`
and `adaptedResult` visibly.

The existing three-field schema suffices for this display. Do not add a boolean `verified` to a
reference: verification of a filename, contents locator, theorem body and local adaptation are
different claims. Any future report-shape change must update producer, Effect Schema and format
contract together; the strict decoder correctly rejects unmodeled keys.

**Completion.** The exact citation retained in JSON also appears in Markdown; multiple citations
and all current relation variants display; absent/assumed entries remain visible; punctuation,
pipes and backticks do not corrupt Markdown. The two existing byte-stability runs and strict
Effect Schema checks pass. Counts, propositions and proof statuses remain unchanged. Publish the
short book-method discussion in `docs/core/semantics.md`; keep extracted facts in the report.

## A later graph slice: expose real dependencies without inventing evidence

For the next actual assembly, first express the intermediate result as a named conditional Lean
theorem. Its type is mechanically checked and visibly retains its hypotheses. Then discharge
those arguments with actual evidence before closing the frozen capstone. This already supplies
robust composition without introducing a planning language.

If showing ledger prerequisites is useful at that consumer, populate existing `Goal.dependencies`
from one authored owner before `ProofGraph.check`. A list of names alone does not prove that
those dependencies suffice; the conditional assembly theorem is that check. The current checker
expects every dependency in the same submitted goal set, whereas obligation censuses run per
scope. Do not bolt cross-scope edges onto one scope and manufacture duplicate goals to satisfy
it. A cross-scope view needs the exact union of existing goals, preserving identity and evidence;
that is a separate integration change, not needed for the three small proof cards.

Distinguish three displays: kernel theorem references already used by a proof, explicit planned
prerequisites for an open goal, and scheduling recommendations. Label them. A dependency-free
collection is not a proof that a theorem has no semantic prerequisites. A rejected graph cycle
is not evidence that the intended mathematics is true.

**When implemented.** Test a real consumer and prerequisite, retained binders/universes,
undeclared prerequisite, stale identity and cycle. Keep open nodes open; never claim a theorem
only because every neighbor is green. Reuse the existing evidence and report owners.

## Publication contract for each proof slice

1. In `docs/core/semantics.md`, explain the source theory, local adaptation, assumptions/cuts,
   short argument and what the result enables. Cite an inspected locator, with the proper relation.
2. In the existing registry, name the exact witness or original ledger goal. Do not hand-author
   the theorem statement or create a duplicate status field. A helper may remain a linked detail
   under an existing selected claim.
3. In generated JSON/Markdown, show actual evidence, statement, role, citation and its relation.
   The exact statement includes premises omitted from any informal summary.
4. In the receipt, name the revision, controls, commands, permitted axioms, actual consumer and
   remaining gap. A proof-method citation explains the construction; it does not enlarge the
   theorem's fragment or establish host behavior.

This is enough to keep theory, implementation and visibility aligned. A separate ontology,
proof-sketch parser, automatic theory matching, global modal framework, or new status dashboard
would add work before the next useful proof lands.
