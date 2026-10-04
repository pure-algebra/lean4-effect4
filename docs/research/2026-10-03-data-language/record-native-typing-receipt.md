# Record native typing receipt

The native term typing and evaluation theorems compile for all three record constructors.
The follow-up receipt is `docs/research/2026-10-03-data-language/record-term-proof-receipt.md`.

Base: `a9340668`.
The commit containing this receipt supplies its head.

## Placement

Concept: Store Typing & Value Membership (`docs/core/semantics.md`).
Role: helpers for the existing term contracts and registry claim `denote-typed`.
Consumer: `evalTerm_hasTy` and `evalTerm_isSome` in `src/Effect4/Laws/Program/Typed.lean`.
Requirement: R3, on the M5 path.

The `nativeSignature` value and fitting environment remain premises.
The successful-value theorem retains its actual evaluation premise.
The evaluation theorem concludes only that a pure typed term returns a value.
Neither theorem establishes whole-program termination or host execution.

`RecordChecks` supplies construction, required and optional reads, and overwrite at the Boolean value check.
The checked type may join alternatives from a union.
The existing world membership laws remain separate.

## Files

- `src/Effect4/Program/Typed.lean` owns the unchanged `NamedFit` definition.
- `src/Effect4/Laws/Program/Typed/RecordValues.lean` owns the shared named-frame laws.
- `src/Effect4/Laws/Program/Typed.lean` connects Boolean record checks to the existing term theorems.
- `src/Effect4/Laws/Program/Typed/Membership.lean` imports the relocated facts.
- `src/Effect4/Laws/Program/Typed/RecordOperations.lean` imports the relocated facts.
- `docs/research/2026-10-03-data-language/record-operations-brief.md` places the remaining term work.

The two world modules only relocate unchanged helper bodies in this commit.
Their fresh integration checks remain pending.
The term-membership mutual block keeps its old owner until the next checked integration.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.RecordValues Effect4.Laws.Program.Typed`
checks the shared facts and reports one missing list-relation import in the native proof module.

After adding its existing law dependency, this command passes:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed
Build completed successfully (257 jobs).
```

The subsequent world and handle check stops in three dependencies before checking those modules.
The coordinator supplies the generated canonical program update.
The other seats supply their record cases.

The follow-up queries report `[propext, Quot.sound]` for the native term and record-operation theorems.
The follow-up proves paired lookup directly and removes the temporary machine-proof dependency.
No whole-library check, host compiler, or runtime comparison runs in this stage.
