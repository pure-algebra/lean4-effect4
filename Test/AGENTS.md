# Effect4 Lean-test routing

This boundary contains executable Lean attacks, examples, compatibility
checks, and proof receipts. The repository root rules remain in force;
`docs/AGENT-ROUTING.md` defines the shared type-assurance and counterexample
route.

## Breaker ownership

A breaker freezes a contract and its red battery before the corresponding
implementation. A builder may repair test elaboration without changing the
attacked statement, witness, or acceptance condition, but does not weaken or
delete a breaker-owned test.

Every counterexample that can alter a declaration or cutover decision receives
a stable ID in `test/counterexamples/REGISTER.md`. Put the executable Lean
witness under `Effect4Test/Counterexamples/<Area>/` and link it from the
registry and owning contract. Keep the witness after the implementation
rejects it so the repair remains testable.

## Evidence classes

Tests distinguish theorem evidence, finite executable probes, model checks,
and host observations. A passing example does not become a general law. A
compile-time rejection records the exact rejected declaration or term rather
than relying on an error-message substring unless the diagnostic text itself
is the contract.

Axiom reports cover every exported theorem named by a graph trust edge or leaf
receipt set and record the actual dependencies. Compatibility tests name both
observations being compared and any loss admitted by the bridge. Creating a
test does not by itself force a proof graph: passive finite alphabets and value
records remain on the leaf-receipt route unless they acquire a semantic or
cutover-bearing claim.

## Runtime coverage witnesses

`Effect4Test/Audit/RuntimeCoverage.lean` is the numerator of the Effect
runtime coverage metric: one frozen row per census behaviour, its disposition,
coverage state, witnesses with axiom receipts, and every witness statement
frozen by `#check (@name : proposition)` ascription. A witness is a `theorem`
whose receipt stays inside `propext`/`Quot.sound`; a row is `green` only when
every clause of its census summary is a named theorem. Add witnesses, update
`snapshotWitnesses` in the same order, keep the totals true, and run
`scripts/check-effect-runtime-census.sh`. `docs/RUNTIME-COVERAGE.md` owns the
rules; the `runtime-coverage` skill is the checklist.

Before handoff, run the narrow file directly and the default Lake build. Link
the exact command and result to the affected proof-graph edge or leaf receipt;
do not mark the whole type closed from one green test.
