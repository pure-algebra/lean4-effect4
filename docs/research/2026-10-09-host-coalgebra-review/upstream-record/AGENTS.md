# Effects — agent operating rules

This file is the always-loaded router for work in this repository. Read it in
full, then open only the documents named for the current task.

## Authority map

| Path | Owns |
| --- | --- |
| `docs/CLAIM-BOUNDARY.md` | what the library claims and does not claim |
| `docs/DESIGN-BASIS.md` | the adopted carrier and universe policy |
| `test/contracts/` | breaker-authored contracts and executable falsifiers |
| `test/counterexamples/` | the counterexample register and durable witnesses |
| `docs/ALGEBRA-DAG.md` | the proof graph of the nine algebra modules |
| `generated/` | the parity receipt against the lean4-effect4 source commit |
| `Effects/` | library declarations and proofs |
| `Effects/Experimental/` | generic algebra with receipts but no contract; `import Effects` does not reach it |
| `EffectsTest/` | Lean tests, attacks, and proof receipts |

If two files appear to own the same fact, stop and repair the ownership map.
Until slice S4 of the split lands, `docs/EFFECTS-SPLIT-PLAN.md` in
lean4-effect4 is the plan of record for this repository.

## Development order

1. Freeze the public declaration record and the assurance route.
2. A breaker, in a separate process, commits the contract and red battery and
   lists the battery in `test/fixtures/trust-gate/known-red.txt`.
3. The builder implements without editing that packet or battery, and removes
   the `known-red.txt` entry the moment the battery is green.
4. Run the narrow test, the default Lake build (which runs the axiom gate),
   and `./scripts/test-trust-gate.sh`.
5. An independent reviewer checks model intent, proof trust, and claim scope.

## Representation rules

- `Program` is the well-founded higher-order proof carrier. Continuations are
  Lean functions. It has no serialization, content identity, or decidable
  equality, and none is added here.
- A signature has operations and answer types. It has no equation field.
  Laws that a particular signature's operations satisfy are stated by the
  consumer over an interpretation, not in this library.
- Composition is proved at `interpret`. Nothing in this library assigns a
  bind law to a fuel-indexed evaluator.
- Universe policy: operation and answer universes are independent; program
  results live in the answer universe; there is no implicit universe lift.
- No third-party Lake dependency. The toolchain, core, and Std are the
  substrate.
- The library compiles with `autoImplicit` and `relaxedAutoImplicit` off. A
  new module binds its universes and variables explicitly. The nine
  `Effects/Algebra/` modules restore both options for one stated reason,
  `generated/algebra-parity.tsv`, and their headers carry it.

## Claims

Do not say "sound", "equivalent", "preserves", or "complete" without naming
the exact theorem, its target-monad hypotheses, and what is compared. Two
handlers for the same signature do not share theorems merely by sharing it;
`docs/CLAIM-BOUNDARY.md` owns the boundary.

## Trust gate

`EffectsTest.lean` ends with `#effects_axiom_gate`. The gate walks every
`.lean` file under `Effects/` and `EffectsTest/`, refuses an authored trust
token — `unsafe`, `partial`, `sorry`, `axiom`, `native_decide`, `extern`,
`implemented_by`, and `admit` should a toolchain make it a keyword — anywhere
in the source including inside an `example`, refuses an `opaque` with no body,
refuses any declaration outside the axiom ceiling, and refuses a file the test
root does not reach. It is kept in step with lean4-effect4's
`Effect4Test/Audit/AxiomGate.lean`; a hardening lands in both. `Classical.choice` is
admitted only in the gate module itself; adding another admission requires an
authored entry in `docs/CLAIM-BOUNDARY.md` and an exact-module entry in the
gate, which fails when the entry goes stale.

## Handoff

Every handoff records base and head commits, file fence, changed files, exact
commands and results, public declarations, axiom output, and the
counterexamples exercised.
