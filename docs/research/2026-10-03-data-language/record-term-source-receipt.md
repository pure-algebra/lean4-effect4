# Record term source stage

This is an integration stage, not the completed record slice.
The coordinator must regenerate `Fold` before building dependent typing or target modules.
The stored syntax, its raw evaluator and its weakening definition compile together.

Base dependencies: admission `128fec34`, receipt `5208a4f3`, plan `ae89c2dd`, bootstrap `c1bc710b` and `220f947d`, operations `6a02b2b8` and `5b074be3`.
Local cherry-pick head before this stage: `9b48d17f`.
Branch: `codex/data-admission`.

Changed source: `Machine/Term.lean` and the term weakening section in `Program/Eff.lean`.
The new `FieldReadMode` and three term constructors follow the approved record contract.
The constructors append to the old term alphabet.
Metadata stays fixed under weakening; all term children move by the existing variable rule.
The evaluator calls the checked record value helpers and evaluates children in stored order.
The type metadata adds only `TyEq` below the machine, not the checker or Laws graph.

The expanded brief assigns authoring builders and their scope proofs before implementation.
`Test/Program/RecordTerms.lean` currently imports only `Program.Eff`.
It checks raw evaluation, explicit read modes, malformed value columns, child scope and metadata-retaining weakening.
Later commits add typing and authoring fixtures after generated companions return.

## Verification

```text
LEAN_NUM_THREADS=3 lake build Effect4.Program.Eff
PASS: 25 jobs

LEAN_NUM_THREADS=3 lake env lean Test/Program/RecordTerms.lean
PASS: exit 0

git diff --check
PASS

python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-term-brief.md
PASS
```

The axiom queries reported:

```text
Effect4.Program.evalTerm: [propext]
Effect4.Program.Term.weaken_eq_lit: [propext]
Effect4.Program.instDecidableEqTerm: [propext]
```

The evaluator is executable evidence for raw terms; the operations seat still owns the typed progress and handle-containment extensions.
No full battery, root axiom gate, generator or target check ran in this source stage.
The shared Lean slot is released after the source fixture.

An initial fixture invocation was blocked by automatic approval review because the first slot grant named only `Program.Eff`.
The coordinator then explicitly authorized this fixture before fold regeneration. The command above ran once under that expanded grant and passed.

## Next dependency

Regenerate group `Fold` from the new `Term` declarations before compiling `Formation` or term typing.
The later Program codec group needs `FieldReadMode` and `Ty` before `Term` in its manifest order.
This stage edits no generated file, root import, manifest or policy.
