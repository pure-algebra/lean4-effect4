# Metaprogramming audit — closing receipt

**Before merging:** this branch provides the shared goal reader that Gemini's semantics driver should reuse. It also adopts Lean's existing parser APIs in two places, with baseline and rejecting controls. No theorem statement, stored representation, generated output, root import, or trust-gate policy was changed. The documentation contribution corrects the active Gemini draft's conflation of stored `Eff` trees and function-bearing `RProgram` semantics.

Branch: `codex/metaprogramming`, private worktree `/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`.
Coordinator base: `8c9be2588332d9f9094c5a6ecd7d9e3af8a0ac55`.
Delivery head before this receipt: `982a0e3367260658ac7a4b535d5199581108596d`; the commit containing this receipt is the closing commit. Nothing was pushed or merged into the active integration tree.

The finishing criteria were: an audit against pinned Lean source; narrow, tested cleanups with unchanged judgments and diagnostics; measured proposals for the three coordinator-owned choices; a reconciled Gemini documentation contribution from the two requested GPT-6.1 Sol reviewers; and retained commands, failures, bounds and source/artifact checks. These are complete within the bounds below.

## Commits and changes

| Commit | Result |
| --- | --- |
| `7856a055` | Initial source-grounded audit and glossary |
| `45e9b532` | Shared axiom filter and obligation reader; existing validators retained |
| `0cdd8c98` | Five handle tactic grammars reuse Lean's `simpArg` production |
| `9190c779` | Authoring do-sequences use Lean's typed parser API and quotation |
| `0fce3447` | Measured fallback arms, display controls and module ownership proposals |
| `982a0e33` | Two Sol reviews reconciled into one Gemini prose contribution |

The original audit/A4 commits `b7f2a10b` and `3640adcb` were rebased to `7856a055` and `45e9b532` after the owner dropped DI-18's import-Lean ban. Earlier receipts preserve their original base as history. Relevant source and toolchain inputs were unchanged by the new documentation-only base.

Production and test changes: nine files, 136 inserted lines and 37 removed lines:

- `tools/ProofGraph/Proof.lean`, `Ledger.lean`, `Search.lean`;
- `src/Effect4/Laws/Auto/Obligations.lean`;
- `src/Effect4/Laws/Machine/Handles.lean`;
- `src/Effect4/Program/Authoring/Sugar.lean`;
- `Test/Audit/ProofGraph.lean`, `Test/Machine/Runtime/HandlesContract.lean`, `Test/Program/AuthoringScope.lean`.

Other changes are research notes and retained evidence in this audit folder and `docs/research/2026-10-01-semantics/codex-sol-review/`. Claude's active tree and seats, Gemini's drafts, coordinator registers and protected roots were read-only.

## Verification

Exact commands, working directories, bounds, exits, timing, source snapshots and complete output are in the per-run JSON/log pairs under `evidence-A1/`, `evidence-A2/`, `evidence-A3/`, `evidence-A4/`, `evidence-A5/` and `evidence-A7/`. Lean 4.33.1 ran serially with `-j1 -M4096 -DwarningAsError=true` and a process timeout. There was no concurrent compiler in this worktree. The private cache is an APFS copy, not a shared symlink or hard link.

- **A4:** changed modules and selected direct consumers compiled; ProofGraphSearch, ProofGraph and Obligations tests passed. Controls preserve polymorphic goal binders/universes and reject invalid markers and hidden forbidden axioms. The helper and elementary witnesses have no axioms; the deliberate propext witness has exactly `propext`. See [receipt-A4.md](receipt-A4.md).
- **A2:** 57 grammar cases passed against original and revised parsers: 37 accepting and 20 rejecting. Handles, its six non-umbrella direct consumers and HandlesContract passed. Handles exceeded the initial 180-second limit; a bounded 600-second retry passed in 352.389 seconds. No fallback body or theorem was changed. See [receipt-A2.md](receipt-A2.md).
- **A1:** five new baseline/revised macro controls, four direct consumers, AuthoringScope, BlameContract and TestClockContract passed. All 28 unchanged authoring-only guards from AuthoringContract passed. Three inspected sugar helpers have `[propext]`. See [receipt-A1.md](receipt-A1.md).
- **A3:** seven instrumentation controls passed. Baseline and instrumented Approximation/Scheduling copies compiled. All 303 and 168 current-file theorem type/value fingerprints matched respectively; stripping wrappers restored baseline bytes. All five requested macro families, 22 arms and nine proof call sites were measured. Counts are retained selections, not attempted-search totals or independent steps. See [results](evidence-A3/RESULTS.md).
- **A5:** a finite options probe changed rendered bytes under `pp.notation`; actual generator entry points start with fresh options, so no supported-CLI nondeterminism was demonstrated. A local display prototype changed one of two existing diagnostic fixtures; adapted controls and six unchanged axiom lists passed. Recommendation: no production unexpander. See [display and printing evidence](evidence-A5/README.md).
- **A7:** a retained source-graph command counted 475 project modules, root closures and caller sites. This is project-source dependency evidence; external package closure was not measured. See [ownership measurement](evidence-A7/README.md).
- The final scoped source/artifact validation checked **1,094 hashes across 406 modules**, with zero mismatches. Rebuilt modules use fresh compiler receipts rather than stale trace claims.
- Both **GPT-6.1 Sol** documentation reviewers independently inspected the new Gemini draft. Parent verification checked 64 input hashes and recorded exact excerpts with no differences. These are source-reading checks, not a semantics-producer test. See [the reconciled contribution](../2026-10-01-semantics/codex-sol-review/review-and-additions.md).

Initial harness mistakes and expected refusing controls are retained and identified in their receipts. Final relevant checks passed; failed harness attempts are not counted as passing tests. No new semantic proof obligation was introduced. Documentation links resolve. `git diff --check 8c9be258..HEAD -- . ':!*.log'` passed; the unfiltered check identifies only five whitespace-only lines emitted by Lean in the retained display-control log. Those raw diagnostic bytes are preserved rather than cosmetically rewritten.

## Boundaries and remaining decisions

No whole-library build, full Test battery, whole-tree trust gate, generator, TypeScript compiler, installation or runtime-backend claim is included. Full AuthoringContract was deliberately not used: its unrelated LayerSharingContract import had a copied artifact from dirty integration source. The clean authoring prefix was tested with that import removed; its exact extraction is retained.

The coordinator still owns fallback policy and any module relocation. The measured proposal keeps narrow trace/queue selectors distinct, considers two delegation simplifications, and does not infer global redundancy from zero observed firings. Other fallback wrappers were source-read but not dynamically measured. The import ban is already ruled away; the audit does not reopen it. A6 retains the custom closed-expression quotation because the pinned compiler has no appropriate matching instance; general derivation would change its refusal boundary.

The Gemini addition keeps the current API, concept-first structure, registry and literature relation vocabulary. It clarifies authored associations, cut applicability, census population and bounded semantic claims. It remains proposed prose for the active author's reconciliation. The semantics driver/report were not implemented by this task and were absent at the reviewed snapshot.

The glossary is included in the audit and the Gemini contribution; no competing `CONTEXT.md`, ADR register or authoritative status table was created. This receipt closes the authorized audit and its safe cleanups. Further policy changes and integration belong to the coordinator's existing process.
