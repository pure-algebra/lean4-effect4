# Effect4

Effect4 is a standalone Lean 4 library for modeling closed-alphabet effectful
programs, their denotational and operational semantics, and checked lowering
to selected host profiles such as Effect TypeScript.

Current state: **pre-release development**. The generic effect algebra is
the [Effects](https://github.com/pure-algebra/lean4-effects) package, pinned at
`v0.1.0`. First-order Flow admission, canonical rows, Context keys, the representative
fiber scheduler and binary race, the persisted Schema carrier and annotation
data plane, raw Schema TypeScript generation, and the first annotated-field
Effect TypeScript API are implemented with focused proof and counterexample
batteries. Layer, runtime, channels, stateful primitives, schedules,
transactions, classification, and the full TypeScript simulation bridge are
still being opened in successive packets. No full-effect, cutover, or release
claim is available yet.

The toolchain is pinned by `lean-toolchain`. Build the production library with:

```text
lake build Effect4
```

This repository deliberately permits a frozen breaker battery to be red before
its builder lands. The exact expected-red set is
`test/fixtures/trust-gate/known-red.txt`; it is checked in both directions.
Run the green remainder, the declaration-closure checks, and the source trust
mutations with:

```text
./scripts/test-trust-gate.sh
```

The host harnesses add direct Effect rc.112 type, diagnostic, runtime,
mutation, and language-service evidence without replacing the Lean judgments.
See [harness/README.md](harness/README.md) for the current entry points.

See [PLAN.md](PLAN.md) for the phased cutover and
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for module ownership. The
literature and Lean API decisions are in
[docs/DESIGN-BASIS.md](docs/DESIGN-BASIS.md); the first-class Schema ruling is
in [docs/SCHEMA-CUTOVER.md](docs/SCHEMA-CUTOVER.md); and all declaration-changing
counterexamples receive stable IDs in
[test/counterexamples/REGISTER.md](test/counterexamples/REGISTER.md).
