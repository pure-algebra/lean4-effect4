# Structural record wrapper receipt

The coordinator can integrate the wrapper without strengthening the existing term round-trip premise.
Its core module also supplies the smaller-child facts needed by the recursive reader.

Starting base: `5a5527e2d2bbae06538131accc1e2e96c4a95b54`.
Integrated dependency: coordinator type projection `8e247ce1`, cherry-picked locally as `aa80048e`.
Checked code head: `b4a1eadcd156edc7b7e7c6f49d34de75c990a08c`.
Branch: `codex/record-contracts`.
Worktree: `/Users/pooks/.codex/worktrees/record-contracts/lean4-effect4`.
This receipt is a documentation-only follow-up to the checked code commit.

## Changed files

- `src/Effect4/Codegen/Record.lean`
- `src/Effect4/Laws/Codegen/Record.lean`
- `Test/Codegen/Record.lean`
- `docs/research/2026-10-03-data-language/record-wrapper-brief.md`
- This receipt

The writer selects one structural image for every raw record declaration, supplied name list and child expression list.
It uses `recordValue` with a target annotation and `objectWith` when the annotation exists and the lists align.
It uses `recordRaw` otherwise.
The raw image retains both unequal-length directions and unsupported annotations.
The exact type metadata retains the original declaration, including optional flags and raw field order.

The literal's key form follows decisions row 196 for the whole object.
Every normal literal uses `objectWith`, as row 164 requires.
Required field reads use canonical dot or bracket access.
Optional reads use a separate `recordOptional` image that retains the requested key twice and checks that the two names agree.

## Proof placement

Concept: Exact Codecs & Data Plane Embeddings (`docs/core/semantics.md`).
Registry claim served: `printed-modules`.
Role: helper exact embeddings for the planned record cases of `readTerm_printTerm` and `readTerm_exact`.
The claim serves R2's representation boundary and R3's data language.

| Theorem | Judgment and consumer |
| --- | --- |
| `readRecord_writeRecord` | Every raw record component triple returns unchanged through the structural writer and reader; consumed by the record term round trip. |
| `readRecord_exact` | Every accepted record wrapper equals its canonical writer image; consumed by the record term exactness proof. |
| `readField_writeField` | Every mode, name and target returns unchanged; consumed by the field term round trip. |
| `readField_exact` | Every accepted field access equals its canonical writer image; consumed by the field term exactness proof. |
| `readRecord_size` | Successful reading bounds the whole recovered child-expression list below the wrapper; consumed by termination of `readTermList`. |
| `readField_size` | Successful reading bounds the recovered target below the field expression; consumed by termination of `readTerm`. |

The laws quantify over structural TypeScript expressions.
They have no formation, scope, list-length, target-profile, or value-validity premise.
The exactness and size directions assume only the successful read named in their statements.
The list and metadata inversion helpers in the Laws module feed the four exact embedding theorems.
`readProperties_size` in the core module feeds `readRecord_size`.

These laws do not establish target assignment, source-text parsing, JavaScript execution, machine typing, or program simulation.
The public host boundary stays where `docs/core/host-boundary.md` places it.
The runtime presence helper remains a separate obligation.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Codegen.Record Effect4.Laws.Codegen.Record` | Passed after repairing proof bodies without changing the statements. |
| `LEAN_NUM_THREADS=3 lake env lean Test/Codegen/Record.lean` | Passed all structural controls and axiom queries. |
| `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-wrapper-brief.md` | Passed. |
| `git diff --cached --check` | Passed before the code commit. |

The focused axiom queries reported these dependencies:

```text
TypeRef.beq, TypeRef.beq_iff, TypeRef.beq_self: [propext]
writeRecord, readRecord: [propext, Quot.sound]
readRecord_size, readField_size: [propext, Quot.sound]
readRecord_writeRecord, readRecord_exact: [propext, Quot.sound]
readField_writeField, readField_exact: [propext]
```

No theorem relies on Boolean equality for arbitrary expressions.
The existing proved type-annotation comparison stays within the allowed assumptions.

The concrete controls are finite Lean checks alongside the universal theorems.
The successful normal-image check requires the real record type projection, so the raw fallback cannot make that control pass.
Controls cover both length mismatches, unsupported declarations, duplicate supplied names in order and all key modes.
Refusal controls cover alternate object constructors, spreads after valid properties, wrong annotations, changed optional flags, non-string raw names and inconsistent optional keys.
The raw spelling is refused for aligned inputs with a supported target annotation.
It is accepted when the target declaration is unsupported.

The shared Lean slot was explicitly returned after the successful focused test.
No target compiler, runtime, generator, full battery or full gate ran for this wrapper slice.

## Integration and remaining work

The coordinator adds the core, Laws and Test imports at its chosen anchors.
The coordinator integrates the new structural recognizers with the case and traversal censuses.
The core size helpers are available without importing the Laws graph.

The coordinator connects the wrappers to the new term constructors and registers the target helpers in the prelude.
The source-text reader must normalize a parsed legacy object node to `objectWith` only in the record wrapper context.
The structural reader deliberately refuses legacy object constructors.
Target assignment and runtime presence checks remain separate from this structural exact embedding.
