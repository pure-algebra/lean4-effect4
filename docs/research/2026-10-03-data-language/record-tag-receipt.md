# Whole-record tag selection receipt

## Integration note

The coordinator must integrate the row 198 target dependency `094772ea` with the structural helper checkpoint `8df2537d`.
The former required-read and spread-update spellings are no longer the canonical target image.
The runtime helper keeps its assertion inside the target boundary; emitted programs receive no unchecked assertion.
Add `Test.Program.RecordTag` and `Test.Codegen.RecordTag` to the battery root.
`Laws.Program.RecordTag` is reached through `Laws.Program.Decision`.
The coordinator owns the decision/register entries, roots, generated inventory and aggregate case check.

## Commits and scope

The source base is `28dffc13`, following the earlier record contracts, value helpers and exact metadata work on `codex/record-contracts`.
The tag source checkpoints are `1ae90df2` and `ea6d8b86`.
The coordinator supplied generator bootstrap `b2e9e02c` and generated tag companions `a8eecf93`.
The initial finite target helper checkpoint is `762c19c5`; the current target dependency is `094772ea`.
The row 198 structural wrapper checkpoint is `8df2537d`.
The checked membership, handle and codegen proof checkpoint is `75d9927f`.
The final checked source and fixture head is `9b8f5b4a`.

The source changes add `Decision.recordTag`, its record type partition and raw decision.
Typing diagnostics, template classification, `printArg` and `readLeaf` cover the new decision.
The codegen wrapper changes affect required reads, optional reads and single-field replacement.
Proof changes cover the record membership helper, coarse and world-indexed decision laws, bound handle keys, exact term reconstruction and readable-program printing.
Focused Lean and TypeScript controls accompany these changes.
No new `Eff`, `Term`, value or type representation is added by this tag slice.

## Contract retained

Every normalized input alternative has a required literal `_tag` field.
A successful selection binds the original whole record on either side.
Hit and miss types retain all alternatives on their respective sides, including distinct alternatives with the same literal.
An empty side is `never`; an absent requested literal is accepted.
Missing, optional, broad-string and union-valued discriminants refuse the type rule.
Malformed raw values take the miss and retain the whole input.
Legacy pair-tag selection still extracts its payload.

The new record operations retain literal generic key markers and refuse mismatches.
They retain the existing scope-only raw term reconstruction statements.
The target required read, optional read and overwrite retain `never` for impossible receivers.
The overwrite helper copies the target before replacement evaluation.
E4-RECORD-CE-013/014/015 retain the former failing target spellings and the core typing witnesses.

## Theorem placement

1. Residual Program Typing, helper of `denote-typed`, fundamental property: `Record.lookup_required_hasTy`, `tagOf_lookup`, `tagHit_eq_isTag` and `tagArms_hasTy` feed `Decision.decide_typed` and `Typed.decide_fits`.
   They quantify over the existing allocation table or world, successful arm computation, and input membership in the required literal-record fragment.
   They do not prove scheduler progress, host replies or target execution.
   They serve R3 on the existing M5 to M6 to M7 route.
2. Scope Lifetime and Finalization, helper of `m7-exit-handles-valid`, preservation: `Decision.decide_bound_keys` uses the identity of the selected record value.
   Its record-tag case covers every successful raw decision, including malformed inputs that take the miss.
   It proves no new resource lifetime or allocation property.
   It serves R3 and the existing M7 handle conclusion.
3. Exact Codecs and Data Plane Embeddings, helper of `printed-modules`: wrapper retraction, exactness and successful-read size facts feed `readTerm_printTerm`, `readTerm_exact`, `read_print`, `read_exact` and module reading.
   The public statements retain their previous scope, readability and `Signature` hypotheses.
   Wrapper laws still quantify over arbitrary child expressions and raw metadata.
   The internal argument-kind helper now distinguishes string captures for pair tags from expression captures for record tags; `argKind_of_selected` feeds `kinds_of_printArgs` and `print_of_readable`.
   These structural facts establish no rendered-source or JavaScript execution theorem.
   They serve R2 and R3.
4. Residual Program Typing, helper of `denote-typed`, compatibility: `Decision.arms_length` covers the new one-value extension on both sides.
   Its hypothesis is successful arm computation.
   It introduces no substitution framework or new authoring representation.
   It serves the existing checker and generated authoring lifts, R1 and R3.

## Evidence

The narrow source and helper builds passed before their checkpoints.
The final command passes with 415 jobs:

```sh
lake build Effect4.Laws.Program.Decision Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Handles.Hooks Effect4.Laws.Codegen.PrintReadable Test.Codegen.Record Test.Codegen.RecordTerms Test.Codegen.RecordTag Test.Program.RecordTag Test.Codegen.RecordEmission
```

The fixture checks both selected payload types in a composed program and repeated literal tags on distinct records.
It covers hit, miss, all-hit, absent-tag and empty columns, invalid discriminants, whole-value identity and nested handles.
It also retains the three core typing witnesses with bottom receivers.
The composed example uses the selected binder at slot 1 after its outer bind occupies slot 0.
The first fixture draft used slot 0 and correctly refused; the corrected fixture checks the exact joined result type.
An unnecessary concrete kernel-reduction example was replaced with a finite membership guard; the universal allocation-table theorem and its statement remain unchanged.

`git diff --check` passes.
`python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/record-tag-brief.md docs/research/2026-10-03-data-language/record-tag-receipt.md` checks the placement and receipt.
All queried new helpers, decision membership laws, handle laws and structural reconstruction laws use only `[propext, Quot.sound]` or a subset.

The finite target evidence is recorded in `record-target-receipt.md`.
The coordinator reports 376 passing Bun tests with 1384 assertions.
Both pinned tsgo projects pass at version `7.0.0-dev.20260629.1`.
A repeated TypeScript generation run leaves all nine outputs unchanged.
This is finite target evidence, not a general simulation theorem.

## Limits

No whole-battery, full trust-gate or full build sweep was run for this slice.
The coordinator performs the root and generated-output integration checks.
No theorem premise was strengthened to exclude bottom receivers or raw stored syntax.
The existing host boundary remains in place.
No push was made.
