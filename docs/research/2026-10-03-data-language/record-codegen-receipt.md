# Record term target reconstruction receipt

The core stage and proof continuation belong together.
The continuation restores the relocated leaf and row declarations, including the original scope-only term round trip.
The coordinator must add the Laws import to `Test/Schema/DialectContract.lean` for its existing `keyFromText_print` consumer.

Core stage: `7854b07dec84076bb60aef70f69d62fe80967581`.
Checked proof continuation: `e3f987a4e0fb280ef7fbeaaecddd82db5da5268f`.
Branch: `codex/record-contracts`.
Worktree: `/Users/pooks/.codex/worktrees/record-contracts/lean4-effect4`.
The stages use the coordinator's stored syntax, fold, formation, typing and canonical codec dependencies.
Those dependency commits are `70d35a9d`, `33b5d1e2`, `128fec34`, `91d7ffd2` and `81d31d3d`.
The record operation dependencies are `6a02b2b8` and `5b074be3`.
The exact wrapper dependencies are recorded in the preceding wrapper and update receipts.

## Changes

The core stage changes `Codegen/Record.lean`, `Codegen/PrintLeaf.lean`, `Codegen/Read.lean` and the wrapper brief.
Construction, explicit field access and update now use the exact wrappers in the term TypeScript printer and reader.
The recursive reader uses the recovered-child size facts instead of assuming that a recognized wrapper exposes a syntactic child directly.

`Record.helperNames` is the one list of runtime helper bindings.
Row spellings, trailing names and export names exclude those bindings.
The program-head alphabet remains separate.
Raw atom calls with those names retain their original structural reading because the new wrappers have generic heads.

The proof continuation adds `Laws/Codegen/ReadLeaf.lean` and `Test/Codegen/RecordTerms.lean`.
It updates `Laws/Codegen/Record.lean`, the import in `Laws/Codegen/Read.lean`, and the brief.
It moves the proof-only leaf and row section out of the core reader.
The declaration-name comparison found all 79 original reader theorem names, with none missing or added in that set.
Runtime definitions and readability predicates remain in the core module.
The core reader imports no Laws module.

## Proof placement

Concept: Exact Codecs & Data Plane Embeddings.
Registry claim served: `printed-modules`, through the existing leaf judgments and their table-reader consumers.
These obligations serve R2 and R3.

`readTerm_printTerm` still requires only `Term.scoped n t = true`.
`readTerms_printTerms` still requires only the corresponding list scope check.
They now cover every raw stored record declaration and supplied argument list, including malformed or unsupported declarations and unequal lengths.
The laws add no formation, target support, typing, or value-validity premise.

`readTerm_exact` and `readTerms_exact` still require only the successful structural read in their statements.
They reconstruct the exact target expression or list.
The three wrapper disjointness helpers feed the term retraction proof.
The shared identifier characterization now serves row reconstruction without repeating every term constructor there.

These laws do not establish source-text parsing, target assignment, generated JavaScript execution or a program simulation.
The public host boundary remains unchanged.
The coordinator's checked target-entry restrictions are separate from these raw reconstruction laws.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Codegen.PrintLeaf Effect4.Codegen.Read` | Passed 93 jobs, including Templates and Print as direct consumers. |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Codegen.ReadLeaf` | Passed 265 jobs. |
| `LEAN_NUM_THREADS=3 lake env lean Test/Codegen/RecordTerms.lean` | Passed the focused controls and axiom queries. |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Codegen.Read Effect4.Laws.Codegen.ReadPrint` | Passed 268 jobs. |
| `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-wrapper-brief.md` | Passed before the proof continuation commit. |
| `git diff --cached --check` | Passed before both code commits. |

The five focused axiom queries each reported `[propext, Quot.sound]`:

```text
readTerm
readTerm_printTerm
readTerm_exact
readTerms_printTerms
readTerms_exact
```

The first proof checks exposed dependent-match rewriting and missing list substitutions in the proof bodies.
The repair used the existing successful-read equations directly and made the size substitutions explicit.
No statement or premise changed.

The concrete controls are finite Lean checks beside the universal laws.
They cover normal and raw records, nested updates, both field modes, out-of-scope rejection, all helper-named legacy calls and helper-name exclusions.
An independent source audit found no discriminator gap or additional moved-proof consumer beyond the named fixture import.

No full battery, target compiler, runtime, generator or full axiom gate ran for this codegen proof slice.
The shared Lean slot was explicitly returned to the operations seat after the direct consumer build passed.

## Integration

The coordinator imports the new focused fixture through the Test root.
`Laws.Codegen.Read` already imports the new proof companion, so the existing Laws root reaches it.
The coordinator owns case and traversal census integration, the target runtime helpers, source parser changes and checked-entry restrictions.
The raw reader's scope-only law remains independent of those target restrictions.
