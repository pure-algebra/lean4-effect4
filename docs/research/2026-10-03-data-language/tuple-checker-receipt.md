# Tuple checker checkpoint

Regenerate the canonical Program, refusal and PreludeAtoms groups before combining this checkpoint with their downstream consumers.
Both membership proof families and the target reader remain separate, uncommitted work at this checkpoint.

Base: `a3a3f13f`, following source checkpoint `e9878e6e` on `codex/data-admission`.
The obligation placements are in `tuple-brief.md`.

## Changes

The variadic tuple atom answers its normalized exact positional type.
`Tuple.typeAt` normalizes the target and selects the requested tuple or product column.
Every remaining normalized union alternative must contain that position.
Explicit bottom answers bottom; the rule does not decide general inhabitance.
Lists and unknown types remain outside static tuple projection.
The new authoring builders resolve names through the existing scope reader.

The existing diagnostic fold now returns a record or tuple refusal.
A tuple refusal retains the raw index, nested term address and reason.
Cause refusals retain their separate cause address.
Record-only `locate` and `locateCause` keep their public result types.
The checker still accepts only through `termTy` or `causeTy`; the diagnostic fold supplies no type.
`TypeReason.tupleTerm` and `tupleCause` are appended after the existing cases.

## Checked evidence

- `LEAN_NUM_THREADS=3 lake build Effect4.Program.Typing.Rules Effect4.Program.Native Effect4.Program.Checker Effect4.Program.Authoring.Tuples`: passed, 54 jobs.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/TupleRefusals.lean`: passed, 19 finite guards, two theorem applications and six axiom queries.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/tuple-record-compat.lean`: passed, all 28 existing record refusal guards and the existing checker projection example.
- `git diff --check`: passed.

The record compatibility driver copies `Test/Program/RecordRefusals.lean` with core-only imports.
It removes five axiom queries that need the pending `Laws.Program.Signature` proof graph; it changes no finite guard or theorem application.
Its first check exposed two remaining unavailable query names; removing those queries made the core-only check pass.
The unchanged original fixture remains queued with the `Laws.Program.Signature` proof stage.

`tagTest?_weaken` uses `propext`.
The other five tuple queries and both retained record queries use `propext` and `Quot.sound`.
Logs: `/private/tmp/tuple-checker-build.log`, `/private/tmp/tuple-refusals.log`, `/private/tmp/tuple-record-compat.log`.
These are Lean source checks and finite diagnostic controls, not target execution evidence.

## Integration and remaining work

New passive carriers are `TupleTypingReason`, `TupleTermRefusal`, `TupleCauseRefusal`, `TermTypingRefusal` and `CauseTypingRefusal`, all under `Effect4.Program`.
The first three are reachable from the appended `TypeReason` cases.
The final two are the diagnostic fold's sums.
The native scheme also appends `NativeAtom.CustomScheme.tuple`.
The coordinator owns canonical generation, manifests, root imports and the Diagnostics target-code cases.

`Effect4.Program.Authoring.Tuples` is the public builder import.
`Program.Tuple` is already reachable through Rules.
The final proof checkpoint will include `Effect4.Laws.Program.Authoring.Tuples` and the TupleTyping and AuthoringTuples fixtures.
Existing value membership, progress, handle containment and `Laws.Program.Signature` theorem statements remain unchanged in the prepared proof draft.
They are not claimed checked here.
No generated file or coordinator-owned integration file was edited by this seat.
The preexisting FormationContract draft remains unchanged and unstaged.
