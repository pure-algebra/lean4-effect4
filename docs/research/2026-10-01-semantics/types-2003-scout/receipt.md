# TYPES 2003 scouting and documentation receipt

**Before adoption:** this packet changes documentation and retains isolated probes only. Gemini's
active source and generated report are unchanged. Source-key validation is already assigned to
Gemini; this refines that task rather than dispatching another implementation. The new visibility
finding is that citations retained in report JSON are omitted from its Markdown renderer.

## Revisions and ownership

- Codex branch base: `4fd7bc69321e72081ca38f6e5970fe8556b1dea7`, `codex/metaprogramming`,
  `/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`.
- Reviewed Gemini: `a8cc886697e173e28a7cf67eca0f49566164b0d8`, `gemini/proofs`, clean before/after.
- Coordinator checkout: `01e3118065e64ddc5f9d28f0a0d982b5f8c647cd`, clean before/after.
- Packet commit is the commit containing this receipt; its exact head is recorded outside the
  repository in `/private/tmp/codex-second-eyes-2026-10-01/types-2003-scout/completion.json`.
  No push or integration merge. Adopt this documentation slice through the coordinator's process;
  the Codex checkout is not a replacement for Gemini's current source tree.

Changed existing files: `docs/core/semantics.md` adds the cited proof-construction discussion;
`brief-gemini-proofs.md` links the ordered cards and tooling slices;
`kripke-adoption/brief.md` withdraws the tentative term-existence gap. New files in this folder
are the three notes, three schema-shaped references, isolated Lean/host probes and saved receipts.
The owner-supplied PDF, whole-chapter extracts and failed draft remain outside the commit.

## Read and independently reviewed

Read all of Adams pp. 1–16, Ballarin pp. 34–50 and Wiedijk pp. 378–393. Book edition, checksum,
exact locators, adaptations and limits are in `book-scout.md`. Two existing focused reviewers
checked the literature and proof cards separately, then reviewed the drafted packet. The second
review caught two diagram edges: the load connector consumes DenotesTyped plus noMarker, and M7
consumes LoadsTyped plus its remaining premises. Both were corrected. The literature review
found no material correction in the final draft.

These are source readings and proposed proof plans. No reference-read, service or exit theorem
was added. Their suggested positive/refusing controls have not been run. The existing term
progress and race-marker exclusion lemmas remove proposed work instead of adding obligations.

## Commands and observed results

1. `python3 /private/tmp/codex-second-eyes-2026-10-01/types-2003-scout/run_probe.py`
   verified 10 imported source matches and 26 saved artifacts against Lake traces, then ran:
   `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -j1 -M4096 -DwarningAsError=true --setup=/private/tmp/codex-second-eyes-2026-10-01/types-2003-scout/VisibilityProbe.setup.json /private/tmp/codex-second-eyes-2026-10-01/types-2003-scout/VisibilityProbe.lean`.
   Passing run exit **0**, **8.359 seconds**, **90-second bound**. See `lean.log` and
   `lean-receipt.json`. First draft exited 1 for probe syntax/typing mistakes; the corrected
   source and passing result are not substituted for that failed history. First-attempt files
   are retained under `attempt-1-*` in the same temporary folder.
2. `/Users/pooks/.local/share/mise/shims/bun /private/tmp/codex-second-eyes-2026-10-01/types-2003-scout/schema-probe.mjs`.
   Exit **0**, **0.169 seconds**, **45-second bound**, Effect **4.0.0-rc.112**. Six runtime
   decoder controls agree (`schema.log`, `schema-receipt.json`); no TypeScript compiler run.
3. `python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`
   in the Codex worktree: **PASS**, 60 document locators. It still reports the known 14 pending
   source keys. This check does not resolve them and is not an evidence-status recount.
4. The retained `validation.json` records **25 declaration locators**, checked at the reviewed
   Gemini revision, the matching PDF checksum and agreement of the saved probe results.
5. `git diff --check`: **PASS** before staging; staged whitespace and allowed-path checks are
   recorded in the completion file. Main and Gemini remained at the heads above with no changes.

## Strongest justified result

The existing tooling checks supplied graph edges, detects cycles/missing nodes, and rejects a
wrong theorem proposition. The current obligation collector does not supply planning edges.
The report producer and Effect Schema reject malformed citation shapes but accept nonblank
unknown source keys; Markdown drops those citations. These are tested documentation/metadata
boundaries, not proof unsoundness or runtime failures.

The proposed changes reuse the existing ledger, registry, Effect Schema, report renderer,
source index and citation audit. They add no second status authority. Proofs remain scoped to
their exact definitions and premises; the book's methodological results do not certify Effect4
execution, a general modal logic, lowering correctness or liveness.
