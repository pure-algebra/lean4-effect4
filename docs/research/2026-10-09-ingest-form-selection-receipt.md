# Shared derived-form selection receipt

Integrate this slice after the shared TypeScript boolean printer repair on the same branch.
The form expansion entrypoint replaces string identifiers with recognized heads and argument classes.
The source recognition branches and generated tables stay unchanged.

## Commits and ownership

Base: `e5a5a41b98ecc63f3c2ca64915b157ad9d8a1174`.
Implementation and evidence: `5a6ac751e461be05a62232e71e2e52a0e2c945d1`.
Branch: `codex/authoring-branches`.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
The design is `docs/research/2026-10-09-ingest-form-selection-plan.md`.
The primary checkout, Claude's files, owner rulings and STATE remain outside this slice.
No merge, push, package installation, Lake command or full sweep runs for this TypeScript slice.

The production paths are `ts/eff/ingest/forms.ts`, `ts/eff/ingest/ck.ts` and `ts/eff/ingest/oxc.ts`.
The controls live in `ts/eff/ingest/test/forms.test.ts`.
The inventory is `docs/research/2026-10-09-module-authoring-inventory.md`.
The evidence directory is `docs/research/2026-10-09-ingest-form-selection-evidence/`.

## Interface and semantics

`expandForm` chooses one generated row by its head and ordered argument classes.
It then uses the existing `expandTemplate` fold.
`FormSelection` exposes the required input, with its argument-class type derived privately from the generated table.
No second expansion route or argument-class enumeration enters the interface.
An absent or ambiguous selection returns an internal refusal before expansion.
Existing missing-slot and binder-insertion checks remain.

Each reader retains its TypeScript syntax checks, captures and refusal ordering.
Neither reader constructs derived-form identifiers by hand.
The generated table owns each selection's expansion and inserted binders.
Zero-parameter `tap` arrows keep their effect classification.
Zero-parameter `andThen` arrows keep their thunk classification.
Handler argument classes remain separate from the expansion's effect and term slots.
Explicit fork options and two-parameter release keep their existing paths.

Decisions row 168 retains one parser and two separate walks.
Agreement between these readers does not establish parser independence.
The generated form and canonical-template tables are byte-identical to the base.
The core `Eff` representation and the Forms-to-Eff route stay unchanged.

## Reproduced checks

`verification.json` records source hashes, compiler versions, commands and per-reader counts.
The implementation commit's four TypeScript files match those retained hashes.
The compiler is tsgo `7.0.0-dev.20260629.1`; Bun is `1.4.2`; the installed Effect pin is `4.0.0-rc.112`.
The snapshots name the pre-commit HEAD; the retained source hashes identify the tested implementation.

| Check | Reproduced result |
| --- | --- |
| Eight focused test files, command below | 250 tests and 1782 expectations pass |
| Pinned tsgo command below | The TypeScript package compiles |
| `compare.ts after` | Full per-reader verdicts match the frozen before snapshot on 28 tracked fixtures and 56 authored probes |
| Generated selection controls | All 19 selections have independent expected results; wrong classes, order, arity and ambiguity refuse |
| Existing source controls | Captured and inserted binders retain their expected trees at depths zero, one, two and five |
| Source review by a separate GPT-6.1 Sol agent | No actionable issue in the final four-file diff |
| `python3 scripts/check-docs.py` | References in 84 authority documents resolve |
| Scoped strict language check | The plan and updated inventory pass |
| `git diff --check` | Passes before staging and on the staged patch |

From `ts/eff`:

```sh
bun --no-install test ingest/test/forms.test.ts ingest/test/printer.test.ts ingest/test/foreign.test.ts ingest/test/refusals.test.ts ingest/test/properties.test.ts ingest/test/services.test.ts ingest/test/packages.test.ts ingest/test/gate.test.ts
node node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tsconfig.json
```

From the worktree root:

```sh
bun --no-install docs/research/2026-10-09-ingest-form-selection-evidence/compare.ts after
bun --no-install docs/research/2026-10-09-ingest-form-selection-evidence/canonical-gaps.ts
```

Each frozen source produces its full serialized verdict independently for each reader.
The comparison retains program data, keys, layers, wire bytes, source positions and refusal details.
The retained inputs include direct, data-last and pipe forms, malformed arities, shadowing and nested captures.
The temporary duplicate-row control restores the generated table in a `finally` block.
The before snapshot refuses overwriting; replay changes only the after snapshot.

## Proof placement and limits

This slice changes no Lean declaration or proof obligation.
The design names the existing R10 Forms typing consumers and the separate R8 reconstruction claim.
No new axiom output is owed for these TypeScript-only edits.
The earlier branch receipt owns that slice's scoped compiled audit and axiom output.
These finite checks establish neither universal foreign source admission nor target simulation.
The independent expected trees supplement the two walks' agreement.
They do not turn the shared generated implementation into an independent behavior specification.

## Retained reader gap and next consolidation

The separate `canonical-gaps.ts` probe confirms a printed-source mismatch.
CK rejects `optionCase` and `caseTag` expressions that OXC and the canonical reader accept.
Both accepted readers recover the same trees.
Four neighboring controls pass through all three readers, including the option and tag payload constructors.
The observation uses closed expressions and an empty row table.
It concerns reading TypeScript syntax, with no typing or execution claim.
The foreign `recognizeSource` entrypoint is absent from this probe.

The smallest next repair gives CK those canonical selection heads through a named printed-image contract.
The broader consolidation candidate makes `exprForms` consume the generated canonical templates instead of copying their spellings.
A shared result constructor can own wire encoding and generated refusal details after that.
Each reader must retain its own refusal selection and source walk.
The inventory records these candidates without changing their source domains in this slice.
