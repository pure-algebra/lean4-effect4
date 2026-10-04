# Tuple coarse typing and scope proofs

World-aware membership and handle containment still need the regenerated Program codec before their prepared proofs can compile.
This checkpoint proves coarse tuple evaluation, scope-aware authoring and agreement of diagnostics when the typing signature is extended.
It does not close the whole tuple slice.

Base: `c29f5c3e`, branch `codex/data-admission`.
The five-part placements remain in `tuple-brief.md`.

## Landed proof consumers

- `Fits.tuple`, `tupleItem_typed`, `tupleAt_typed`, `Tuple.project_typed` and `Tuple.typeAt_typed` serve `denote-typed` through `NativeAtom.sound`, `evalTerm_hasTy` and `evalTerm_isSome`.
- The existing `Tuple.project.eq_cata` generation pattern ties projection to the `Ty` fold; the traversal owner remains `Laws/Program/Folds/Ty.lean`.
- `Authoring.tuple_scoped` and `tupleAt_scoped` serve the existing authoring scope judgment; they certify no typing or bounds condition.
- `termDiagnostic_ext` serves checker/refusal agreement through the unchanged `termRefusal_ext`, `term?_ext` and `cause?_ext` statements.

Coarse projection retains the allocation table and produces an actual result whenever its input fits its admitted type.
Union alternatives use the existing membership rules for canonical joins.
Only explicit bottom is ignored; the rule does not decide general inhabitance.
Existing theorem statements and hypotheses are unchanged.
No scheduler progress, host liveness or target execution follows from these term proofs.

## Commands and results

The first command requested the tuple fold, coarse typing, membership, denotation and authoring law modules.
It built `Folds.Ty`, `Authoring.Tuples` and `Signature`, but the aggregate failed on stale generated Program cases and three incorrect namespace qualifiers.
The qualifiers were corrected without changing any statement.
Generated Program remains coordinator-owned.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed`: passed, 249 jobs, including the tuple fold connector.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/TupleTyping.lean`: passed, 24 guards, one theorem application and eight axiom queries.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/AuthoringTuples.lean`: passed, six guards, two theorem applications and two axiom queries.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/RecordRefusals.lean`: passed unchanged, 28 guards, one theorem application and seven axiom queries.
- `git diff --check`: passed.

`Fits.tuple` and `tupleItem_typed` use `propext`.
The other six coarse queries, both authoring queries and all seven record queries use `propext` and `Quot.sound`.
No query exceeds the existing ceiling.
Logs are `/private/tmp/tuple-proof-build.log`, `/private/tmp/tuple-coarse-build.log`, `/private/tmp/tuple-coarse-fixture.log`, `/private/tmp/tuple-authoring.log` and `/private/tmp/tuple-record-full.log`.

The exact initial command was:
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed Effect4.Laws.Program.Folds.Ty Effect4.Laws.Program.Typed.Membership Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Authoring.Tuples`.
The stale generated cases were in `Store/Domain/Derived/Program.lean` at the writer, retraction and exactness consumers of `Term`.
Membership reaches them through `Typed.Validity → RuntimeR → Api → ProgramWire`.
No generated case was edited by hand.

## Integration boundary

Add the public law import `Effect4.Laws.Program.Authoring.Tuples` and tests `Test.Program.TupleTyping` and `Test.Program.AuthoringTuples`.
The final prepared fixtures are split into `TupleMembership` and `TupleHandles` so their dependency boundaries remain visible.
They are not part of this checked checkpoint.
The final raw-handle extension should make the existing straight-meaning proof work without adding another meaning-specific case split.
That consumer remains unverified until its final check.
No full sweep or push was run.
The preexisting FormationContract draft is unchanged and excluded from the commit.
