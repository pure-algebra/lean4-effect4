# Checked record boundaries

Checked TypeScript production and source admission now refuse unsupported stored annotations, including records discarded before the program returns.
Raw TypeScript printing and reading retain their existing reconstruction domain.

Base: `244b7fb4`. Branch: `codex/data-language-wave`.
The commit containing this receipt records the source and proof changes.

## Changes

`annotationRefusal` in `src/Effect4/Codegen/Print.lean` reads the existing generated program annotation fold.
`printEntry` checks these annotations before producing a declaration block.
`Api.printDecl` in `src/Effect4/Api.lean` applies the same check.

`ModuleReading` in `src/Effect4/Codegen/Admit.lean` retains the successful annotation check.
`admitModule` returns its existing `unrepresentable` refusal when the check fails.
Raw formation, typing, profile support and lexical binding remain separate checks.

`Laws/Codegen/Module.lean` now imports the relocated reader proof companion directly.
`Test/Schema/DialectContract.lean` receives the same import correction.

## Proof placement

Concept: Exact Codecs and Data Plane Embeddings. Registry claim: `printed-modules`. Requirements: R2 and R3.
`printEntry_checks` and `printEntry_annotations` serve the checked module production and source admission laws.
Their premise is successful `printEntry` on the indexed program, table, name and result type.
Their conclusion includes stored-annotation profile support.
They establish no TypeScript execution, package meaning, source import origin or host-session property.

`ModuleReading.recheck`, `admitModule_complete` and `ModuleEmission.admit` retain the additional check through the certificate.
The conditional theorems `emitModule_complete` and `Api.printDecl_erasure` now name stored-annotation support explicitly.
The production-to-admission theorem obtains this premise from the production equation.
The raw scope-only term reconstruction theorems keep their statements.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Api.ModuleReadable Effect4.Laws.Codegen.Admit Test.Codegen.RecordEmission Test.Api.ApiContract Test.Schema.DialectContract` | Passed 353 jobs. |
| `LEAN_NUM_THREADS=3 lake env lean /private/tmp/effect4-record-boundary-axioms.lean` | Five queries report `[propext, Quot.sound]`. |
| `python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-source-brief.md` | Passed. |

The axiom queries name `ModuleReading.recheck`, `ModuleEmission.admit`, `admitModule_complete`, `emitModule_complete` and `Api.printDecl_erasure`.
The focused fixture also queries `annotationRefusal`, `printEntry_checks` and `printEntry_annotations`.
Each reports `[propext, Quot.sound]`.

The fixture checks successful record production and source admission with explicit ambient imports.
Its rejected program discards a record containing an absent optional field with an unresolved nominal application type.
That program passes raw formation and core typing, and returns a natural number.
Both checked production paths and checked source admission refuse its unsupported stored annotation.
The raw printer still produces its structural image.

These are finite controls beside conditional universal theorems.
No full battery, full axiom gate or general target simulation runs in this slice.
The integration receipt owns the remaining root imports, generated reports and record consumer checks.
