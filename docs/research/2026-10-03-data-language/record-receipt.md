# Record contract receipt

The coordinator must retain full declared type metadata in the canonical TypeScript print image.
A TypeScript annotation alone loses the distinction between `nat`, `int` and `number`.

Base: `82d34358e84f0e823be24ba895aa382092c1754c`.
Branch: `codex/record-contracts`.
Worktree: `/Users/pooks/.codex/worktrees/record-contracts/lean4-effect4`.
Checked code head: `e237599b` (`Specify record operations and prove named value helpers`).
This receipt is a documentation-only follow-up to that commit.

## Scope

The owned files are:

- `docs/research/2026-10-03-data-language/record-contract.md`
- `docs/research/2026-10-03-data-language/record-receipt.md`
- `src/Effect4/Laws/Program/Typed/RecordValues.lean`
- `Test/Program/RecordValues.lean`

The contract fixes the proposed record syntax signature, observation, checker premises, canonical target image and acceptance controls.
It records the proof placement before proof work.
It leaves generated files, roots, the lakefile and decisions register to the coordinator.

## Authority amendment proposal

Amend row 167 within row 195's approved printer policy.
Choose one key form for the whole literal: computed if it contains `__proto__`, quoted if any name is not an identifier, otherwise plain.
The exact reader accepts the chosen whole-literal form, including quoted identifiers when that form is quoted.
The target profile accepts all string names.

## Evidence

Source inspection confirms the existing named record layout and optional-field membership.
`TyEq` imports only `TyCore`, which imports nothing.
The proposed metadata dependency therefore introduces no import cycle at this base.
`TypeScript.Expr.objectWith` has one key form per literal at the pinned package version.
`TypeRef` rendering does not distinguish `nat`, `int` and `number`.
An import-closure script found no `Effect4.Codegen` module in `Store.Domain.Derived.Program`'s dependency closure.
The generated codec must move its `Ty` block before its `Term` block when terms acquire type metadata.

`python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-contract.md docs/research/2026-10-03-data-language/record-receipt.md` passed before the proof checks.
The isolated worktree's dependencies were cloned with `cp -c -R`, as `AGENTS.md` requires.

## Narrow verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.RecordValues` | Passed after repairing two projection rewrites. The theorem statements did not change. |
| `LEAN_NUM_THREADS=3 lake env lean Test/Program/RecordValues.lean` | Passed after correcting the test's `Store.Val` namespace. |
| `python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-contract.md docs/research/2026-10-03-data-language/record-receipt.md` | Passed. |
| `git diff --cached --check` | Passed before the checked code commit. |

The test command printed these axiom dependencies:

```text
'Effect4.Program.Typed.namedFit_lengths' depends on axioms: [propext]
'Effect4.Program.Typed.namedFit_required_pair' depends on axioms: [propext]
```

Both helpers are kernel-checked theorems of their unchanged statements.
The concrete absence examples are finite Lean controls.
Their code stores no rendered target text.
No generator, target compiler, full battery or full gate ran for this receipt.
No executable policy-family match changed, so this slice did not require `make check-cases`.
The shared Lean slot was returned to the coordinator after the successful test.

## Integration

The helper module imports only the existing membership module.
The coordinator imports it from the consuming term proof module when that slice lands.
The coordinator adds `Test.Program.RecordValues` to `Test/All.lean` at its chosen anchor.
This branch changes neither root nor the axiom gate.

## Remaining obligations

The coordinator implements the stored constructors and their generated consumers after row 194's bootstrap change.
The term and decision proofs extend the existing M5 consumers.
The target implementation supplies the presence helper and exact metadata reconstruction.
Finite target controls use the pinned tsgo 7 compiler.
This receipt claims no general target execution theorem, liveness result or host execution agreement.
