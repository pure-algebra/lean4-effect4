# Foundations slices 3 and 4: execution record

Base: `641a0feabe8ff7c3899396cd2144380d6d8cf53c`.
Branch: `codex/foundations-slices-3-4`; checkout: `/private/tmp/effect4-foundations-slices`.
Owner dispatch: land the next two slices, using the additional adversarial review as input.
No push. The original checkout and its local document edits are retained.

## Completion criteria and order

1. Declare slice 3 data validity and transport obligations in `Typed/Validity.lean`,
   with an exact open ceiling; retain the existing `WorldWanted.park_extension` statement.
2. Fill those obligations, prove initialization of the ghost tables, and retain positive
   and negative controls for spelling, fresh keys, tokens and dangling completions.
   Narrow builds, the trust audit, `make build` and `make check` must pass before closure.
3. Validate the new review's proposed strong-exit and interrupt-delivery contracts before
   freezing slice 4. A checked counterexample stops the dependent contract work under
   brief §2. Keep unrelated safe work separate; no silent weakening or runtime changes.
4. Slice 4 completion requires certificate protocols, source/control admission, the
   dependent answer inventory and its negative controls, and the settling cases in §4.
   Named open later-stage obligations are allowed; a placeholder is not proof of its payload.
5. Record exact statements, open names, commands, evidence and commit boundaries in each
   slice receipt. Abstract representation laws must name their observation and host boundary.

The new adversarial audit is an input report, not a proof receipt. In particular, its
`DeliveryStateOk`, `StrongExit` exclusion, and claims about future infrastructure must be
checked against current source before promotion. The earlier research probes remain bounded
controls or conditional theorems at their stated scopes.

## Statement checkpoint

`lake build Effect4.Laws.Program.Typed.Validity` passed (360 jobs).
`Effect4.Program.Typed.M2Validity`: 15 open, 0 proved, ceiling 15.
This checkpoint establishes elaboration of declarations, not their payloads.
