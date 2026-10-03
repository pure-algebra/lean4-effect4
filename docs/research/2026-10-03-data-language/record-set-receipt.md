# Structural record update receipt

The independent update wrapper is ready for the term reader and TypeScript printer.
Its agreed target image is `recordSet<"key">()({ ...target, key: replacement })`.

Base: `d6e089d2`.
Checked code head: `593a7cbb9fbb03ed51aa5e5bb2bca76961e0e39e`.
Branch: `codex/record-contracts`.
This receipt follows the checked implementation without changing it.

## Placement

The concept is Exact Codecs & Data Plane Embeddings.
The three helpers serve `printed-modules` through the new update cases of the existing term reader, round-trip law and exactness law.
They serve R2 and R3.

`readSet_writeSet` recovers every string key and both arbitrary child expressions.
`readSet_exact` identifies every successfully read expression with that writer image.
`readSet_size` bounds both recovered children below the wrapper on successful reading.
It lives in the core module for the recursive core reader.
The two equality laws live in the Laws module.

These structural judgments require no formation, scope, typing or target support premise.
Successful reading is the premise of exactness and the size bounds.
The target execution and host boundaries remain separate.
No machine typing or target runtime claim follows from these laws.

## Changes and checks

The code commit changes `Codegen/Record.lean`, `Laws/Codegen/Record.lean`, `Test/Codegen/Record.lean` and the wrapper brief.
The writer places exactly one target spread before exactly one replacement property.
The reader refuses a different key, different key form, reordered entries and additional entries.
The key form follows decisions row 196, including computed `__proto__`.
The generic helper head stays distinct from a legacy unparameterized atom call.

These commands passed:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Codegen.Record Effect4.Laws.Codegen.Record
LEAN_NUM_THREADS=3 lake env lean Test/Codegen/Record.lean
PYTHONDONTWRITEBYTECODE=1 python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-wrapper-brief.md
git diff --cached --check
```

The focused axiom queries reported `readSet_size: [propext, Quot.sound]`.
Both `readSet_writeSet` and `readSet_exact` reported `[propext]`.
The first size proof let arithmetic automation split its conjunctive conclusion and reached `Classical.choice`.
Splitting the two conclusions explicitly removed that dependency without changing the statement.

The controls are finite Lean checks beside the universal laws.
They include plain, quoted and computed keys; wrong literal keys; extra and reordered entries; and a legacy atom call.
The shared Lean slot was explicitly released after those checks.
No target compiler, runtime, full battery or full gate ran for this independent wrapper.

## Integration

The coordinator supplies the matching constant-type-preserving runtime identity and target compiler controls.
Term printer and reader integration follows the staged stored syntax and regenerated fold companions.
The expanded wrapper brief records that continuation and the approved proof-only relocation out of the core reader.
