# Record refusal proof stage

The diagnostic source stage now has checked proof consumers and its permanent fixture.
The earlier public entry-point fixture still waits for the coordinator's refusal regeneration and target integration.

Base: `c322e6d1`. Branch: `codex/data-admission`.
This stage changes `Laws/Program/Typing/CheckInversion.lean`, `Laws/Program/Signature.lean` and `Test/Program/RecordRefusals.lean`.
The five-part placements are in `record-refusal-brief.md`.

The term and cause inversion helpers use the existing checker rule bank.
They state that a successful located check is exactly a successful existing typing rule.
The original `term?_ext` statement is unchanged.
The new diagnostic extension helper serves it and the cause-check extension helper.
The latter is consumed by the existing checker algebra agreement.
All existing typing signature extension premises remain required.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typing.CheckSound Effect4.Laws.Program.Signature
PASS: 248 jobs

LEAN_NUM_THREADS=3 lake build Test.Program.RecordRefusals Test.Program.CheckerRulesRed
PASS: 250 jobs
```

Both batches passed on their first attempt.
The permanent fixture contains 28 finite guards and one general projection example.
It covers each field reason, both mismatch directions for column lengths, nested term and cause paths,
first-failure fallback, literal discriminants and successful neighbors.
The existing checker-bank negative control also passes.

Each queried declaration reports `[propext, Quot.sound]`:
`Checker.toOption_term?`, `Checker.term?_eq_ok`, `Checker.toOption_cause?`, `Checker.cause?_eq_ok`,
`termRefusal_ext`, `cause?_ext` and `term?_ext`.
Logs: `/tmp/record-refusal-laws.log` and `/tmp/record-refusal-fixtures.log`.
No theorem premise was weakened.
The reason payload controls are finite evidence; the projection and extension laws are general Lean proofs.
No full battery, generator, target execution check or root axiom gate ran.
The Lean slot is released to the coordinator.

The coordinator still owns the refusal carriers, target diagnostic cases and root imports listed in the source-stage receipt.
The remaining local edit is `Test/Program/FormationContract.lean`, extending the existing checked-entry controls to record metadata.
