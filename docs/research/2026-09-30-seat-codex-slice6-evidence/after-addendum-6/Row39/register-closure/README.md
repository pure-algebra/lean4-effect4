# Row 39 register closure

The two patches retire 21 registered attack rows in the same slices that delete their named batteries. They preserve every moved row verbatim, including status and forced repair, and pin the source files at `d554cd7194f54c1ed2ffd020b4dc59d573bc1c34`. They make no semantic ruling and do not mark a row repaired. Two rows with explicitly named surviving witnesses stay live; only their deleted evidence path becomes historical.

The captured live registers are from HEAD `abc7b12401b22112ef29df886237a3d0024b33d6`, with the root's first source-deletion slice in progress. The H2 changes to CE-003, CE-007 and CE-008 are preserved. This is a register-only supplement to the four source patches, not a replacement for them. No repository file was written by this preparation.

## Apply with the corresponding slice

1. `01-effectful-field/register.patch`: apply alongside source stage 1. Moves **E4-SCHEMA-CE-049–055** (7 rows). It changes only `Test/Counterexamples/REGISTER.md` and `Test/Counterexamples/Archive/REGISTER.md`.
2. `02-check-accepts-image/register.patch`: apply after the first register patch, alongside source stage 2. Moves **E4-SCHEMA-CE-018–022, 043–048, 056–058** (14 rows). It changes the same two files and pins the retired evidence paths in retained live rows **017** and **059**.

The first patch has passed `git apply --check` against the live worktree. Both patches have passed `git apply --check` and actual application in order **only inside `register-closure/projected/`**. The original source patches do not modify these register files, so the two register supplements are independent of their source hunks. Stage 2's register patch requires stage 1's register patch.

## Exact migration inventory

| Slice | IDs | Deleted registered witness |
| --- | --- | --- |
| 1 | 049–052 | `Test/Counterexamples/Schema/EffectfulField.lean` |
| 1 | 053–055 | `Test/Counterexamples/Schema/EffectfulFieldProperties.lean` |
| 2 | 018 | `Test/Counterexamples/Schema/WireSpellingDrift.lean` |
| 2 | 019 | `Test/Counterexamples/Schema/CensusCoverage.lean` |
| 2 | 020 | `Test/Counterexamples/Schema/KindAlphabetSeparation.lean` |
| 2 | 021 | `Test/Counterexamples/Schema/NoNullLiteralKind.lean` |
| 2 | 022 | `Test/Counterexamples/Schema/NoLocalSymbolPropertyKey.lean` |
| 2 | 043 | `Test/Counterexamples/Schema/RecursiveElimination.lean` |
| 2 | 044–048 | `Test/Counterexamples/Schema/AnnotationDataPlane.lean` |
| 2 | 056–058 | `Test/Counterexamples/Schema/Codec.lean` |

All IDs in this table have prefix `E4-SCHEMA-CE-`. Each source pin was verified by `git cat-file -e`; the immutable blob IDs are recorded in each inventory and `manifest.json`. Original row bytes and captured line numbers are retained in `original-rows.json`.

## Rows kept live and existing archived rows

- **017** explicitly also names the exact recursor snapshot in retained `Test/Schema/RepresentationContract.lean`. Keep the row; replace only the deleted `SemanticTagSeparation.lean` path with its full `git:d554…:path` pin.
- **059** explicitly also names the retained empty-list/empty-Cause ambiguity in `Test/Codegen/SchemaGenerationContract.lean`. Keep the row; pin only the deleted `Codec.lean` path.
- **E4-TARGET-CE-005–008** are already archived at `Archive/REGISTER.md` lines 96–99, with their original `git:c407ab7:Effect4Test/Counterexamples/Target/EffectfulField.lean` pin. Stage 1 does not move or duplicate them. Their current Codegen battery and harness retire with stage 1, while the already archived rows remain historical.

The migration criterion is the **attack battery registered in each row**, not absence of every related guard. Retained `Test/Schema/SubAlphabetContract.lean` still pins exact kind censuses; `PayloadContract.lean` has value-layer companions for 020–022; and `SchemaGenerationContract.lean` retains natural-precision and snapshot refusal controls related to 056/058. Those controls are not silently substituted for the specifically registered separation/impossibility witnesses. The archive section expressly avoids claiming that every related check disappeared.

## Archive format and checks

The archive already supports five-column row tables in dated sections (`Conform integration controls (2026-09-10)` and `Conditional-handler target control (2026-09-10)`), immutable `git:<rev>:<path>` references, and dated retirement notes. The patches follow that format with two dated row-39 sections before `Historical notes`. A small header correction describes 2026-09-13 as the first split and allows later dated retirements. The original live-register historical split counts remain untouched.

`checks.json` records these completed static checks:

- 21 rows removed from the live register and reproduced byte-for-byte exactly once in the archive;
- every moved ID and each mixed row appears exactly once across the two resulting registers;
- no live row retains a bare reference to any file deleted by source stages 1 or 2;
- all source pins resolve at the full immutable revision;
- both sequential patch applications pass in the temporary projection;
- stage 1 passes live `git apply --check`;
- repository register bytes remain unchanged by this preparation.

No Lean, lake, build, generator, or runtime command ran for this register-only proposal. The row statuses are historical text; recording an archival source pin does not relabel a historical `SEEDED` row as `PINNED`.
