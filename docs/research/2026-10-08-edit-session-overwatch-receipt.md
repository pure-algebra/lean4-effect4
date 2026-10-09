# Edit-session overwatch

Defer the fallback annotation in `EditSession.feed` before relying on its local-check path.
The landed implementation computes the full candidate table even when it returns a splice.
A review-only candidate removes that computation from the splice branch and returns exactly the same results.

## Checkpoint and ownership

Previous primary checkpoint: `cb1478a4f5a8d3c7c17f31a1c424d0e67aef794c`.
Reviewed feature: `ff87466d42813a02e5f89c2c9a653b15ebd1669c`.
Reviewed base: `fdbae937259f2516645147a045a2d7ce9beaee5e`.
Review branch: `codex/edit-session-overwatch`.
Measured checkpoint: 2026-10-09 02:56:16 UTC.

The primary checkout still holds the reviewed base at the final inspection.
Its working changes belong to Claude: address laws, printer-law imports, parts-table code and laws, root imports, and the semantics registry.
The active session is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50.jsonl`, under the repository-specific Claude directory.
A bounded recent tail confirms its working directory as `/Users/pooks/Dev/lean4-effect4`.
The session reports that the parts-table core builds; this review does not reproduce that in-progress build.
Internal thinking fields are excluded from the review.
No message goes to Claude or the organization seat.

The review changes only this receipt and `docs/research/2026-10-08-edit-session-overwatch/`.
This review changes no production, tests, generated projections, or owner rulings.
The earlier rendering branch remains at `9fbff639`.
The PartitionedSemaphore implementation checkpoint remains `98e5d6f8`, with receipt `08431c4e`; integration and its waiting work remain open.

Completion criteria: reproduce each actionable issue, check the proposed repair, inspect the proof dependencies, and retain exact evidence.
The review uses codebase-design, lean-reification-audit, and lean-reification-breaker.
Two independent GPT-6.1 Sol reviewers inspect the API and the proof chain.

## EDIT-OW-01: the splice branch computes the whole annotation

Priority: P2.
Kind: implementation cost mismatch.
Source: `EditSession.feed`, `src/Effect4/Program/Edit.lean`, at the reviewed feature.

The local `rechecked` value contains `annotate l.sig l.env p'`.
Lean evaluates that value before either table lookup selects the splice branch.
The generated C calls `Program_annotate`, then `Table_typedAt`, then the replacement's `Annotate_check`.
The successful splice discards the fully annotated fallback result.

Thus a small edit still checks the entire candidate, then checks its replacement again.
This contradicts the module's claim that a splice checks the new sub-program and nothing else.
The retained compiler output establishes call placement; it supplies no latency measurement or compiler-correctness theorem.

The smallest repair delays the fallback:

```lean
let rechecked : Unit → EditSession Op × Edit.Delta := fun _ =>
  ({ l with program := p', table := annotate l.sig l.env p' }, .rechecked)
-- Each fallback branch uses `rechecked ()`.
```

[The candidate](2026-10-08-edit-session-overwatch/Probe.lean) retains every other branch.
Lean checks by `rfl` that it returns the same session and delta for every session and edit.
Its generated C returns from the splice branch before the annotation block.
Only the four fallback branches enter that block.
The existing coherence and undo statements therefore need no amendment for this candidate.

The finite controls cover spliced, rechecked, and unchanged results, plus growing and shrinking replacements.
They also cover an inline Semaphore caller and a declared hole with its retained typing signature.
Their guard count comes from the retained [evidence record](2026-10-08-edit-session-overwatch/evidence.json).

Table lookup and splice still traverse parts of a list.
Removing the extra checker traversal establishes no constant-time edit or general subtree-sized running-time claim.
Production remains unchanged; the candidate is a concrete repair for the implementation owner.

## EDIT-OW-02: the author entries omit the edit session

Priority: P2.
Kind: public-interface integration gap.
Sources: `src/Effect4/Author.lean` and `src/Effect4/Laws/Author.lean`, at the reviewed base.

The five documented entry modules expose `Api.Author.program`.
Together they expose none of `EditSession.open`, `feed`, `view`, or `reached_view`.
[The import control](2026-10-08-edit-session-overwatch/EntrySurface.lean) confirms this in Lean.
Direct internal imports expose those declarations and compile in the other retained controls.

The feature currently requires an internal import, outside the author interface of decisions row 332.
Add the core session to `Effect4.Author` and its laws to `Effect4.Laws.Author` when exposing this authoring feature.
Add one entry-only acceptance caller that opens, edits, and views a module program.
This requires no new author knob, wrapper, program representation, or proof statement.

## Proof review

| Registered question | Pointer | What the statement establishes | Important limit |
| --- | --- | --- | --- |
| `edit-session-coherent`, preservation, R14 | `EditSession.reached_view` | After opening and sequential edits, the view agrees with the structural checker's refusals and type | No cost, rendered page, execution, or full definition-block observation |
| `edit-session-undo`, compatibility, R14 | `EditSession.feed_undo` | Immediate restoration of the old focused program restores a coherent session and its table | Requires coherence, the old focus, and successful replacement |
| `edit-repaint-set`, preservation, R14 | `EditSession.feed_repaint` | A splice reports new subtree addresses; surviving entries outside that list occur in the old table | No deleted-key list, layout, pixels, or device-call result |

All three questions belong to `initial-algebras-folds`.
The compiled audit checks their exact semantics-registry pointers and finds no open proof dependency.
It audits 459 compiled declarations across the edit core, edit laws, touched splice laws, and edit battery.
Every audited declaration stays within `[propext, Quot.sound]`.
The actual core import closure reaches the edit session and reaches no Laws module.
This is a scoped audit, not the whole-tree axiom gate.

The representation remains the existing `Eff` plus its derived address table.
The session now retains its signature and root environment across edits.
This gives sequential edits the checking context that the earlier rendering review required.

Two descriptions need correction with the repair:

- The `reached_view` docstring says the session checks only changed material, even for rechecked edits.
- The law module's placement header and `run_coherent` docstring still name `run_coherent` as the claim pointer.

Qualify the first description to the corrected splice branch.
Name `reached_view` as the semantics-registry pointer and `run_coherent` as its helper.

## Forward boundaries, not regressions

A shrinking replacement removes an old descendant address that the new-address list does not contain.
The retained control replaces the suspension at `[0]` with a leaf.
It reports `[[0]]`, and `[0, 0]` disappears from the table.
A view consumer must replace the addressed subtree or compare the old and new address sets.
It must not treat the reported addresses as all changed or deleted display objects.

The repaint claim explicitly excludes a page drawn from the table.
The earlier rendering finding still applies: unchanged table entries can acquire new positions or widths.
Prefer table-splice language for this API until a separate rendering contract defines invalidation.

Edits currently form a local sequential fold.
They carry no expected revision and establish no stale-message rejection across an MCP connection.
A transport adapter still needs snapshot identity and evidence of `EditSession.Coherent` for its program and typing signature.
The public structure permits arbitrary cached tables; only coherent sessions and sessions reached through `open` receive the proved view guarantees.

A refused candidate becomes the next draft and exposes refusals.
That behavior is intentional; `rechecked` does not mean admitted for execution.
Existing hole rows work when opening with the extended signature.
Adding a new hole row requires reopening or a future context-changing event because `feed` keeps the signature fixed.

Root definition blocks and the optimized whole-program table remain the next slice.
Queue and Semaphore definition instances exercise that explicitly deferred boundary.
The current inline Semaphore control succeeds without a definition block.
No unlanded parts-table obligation is reported as a regression.

## Evidence and commands

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.EditControls` | Pass, 776 jobs |
| `LEAN_NUM_THREADS=3 lake build Effect4 Effect4.Laws.Author ProofGraph.Registry ProofGraph.Audit` | Pass, 639 jobs |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true -c docs/research/2026-10-08-edit-session-overwatch/Probe.c docs/research/2026-10-08-edit-session-overwatch/Probe.lean` | Pass; kernel equality and 15 finite guards |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-edit-session-overwatch/EntrySurface.lean` | Pass; confirms the public-entry gap |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-edit-session-overwatch/Audit.lean` | Pass; scoped compiled audit |
| `python3 docs/research/2026-10-08-edit-session-overwatch/capture.py` | Pass; 13 pinned source inputs and original/candidate compiler output |

The packet retains logs, the candidate source and C, both feed function bodies, and source hashes.
The compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
No TypeScript execution, MCP transport, renderer run, full sweep, merge, or push occurs.
No behavior-specification or owner-ruling amendment is needed for the two proposed repairs.

The compiler emits trailing spaces in `Probe.c`, `landed-feed.c.txt`, and `candidate-feed.c.txt`.
Those three files retain the compiler's exact bytes.
The whitespace check excludes trailing spaces only for those files, through a command-local Git option.
The ordinary staged whitespace check covers every other file.
No repository whitespace rule changes.
