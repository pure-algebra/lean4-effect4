# Effect4

Effect4 is a standalone Lean 4 library for modeling closed-alphabet effectful
programs, their denotational and operational semantics, and checked lowering
to selected host profiles such as Effect TypeScript.

This repository is being extracted additively from Foldlab. Foldlab remains
unchanged while shared algebra is moved here and related by explicit
compatibility theorems. The extraction does not copy the incompatible
workshop carriers from Foldlab's Effect Core experiments.

Current state: the generic signature/program/handler algebra is implemented
and kernel-checked. The first-order Flow admission contract is frozen and red;
Schema, environment, layer, runtime, fiber, target, and Foldlab adapter modules
remain breadth stubs whose declarations open only behind their breaker
packets. No full-effect or cutover claim is available yet.

The build is pinned by `lean-toolchain`:

```text
lake clean && lake build
```

The default build enumerates every `Effect4.*` and `Effect4Test.*` module,
rejects source files not reachable from the roots, checks exact algebra
signatures, executes the counterexample battery, rejects authored `unsafe` and
`partial` declaration modifiers, distinguishes safe structural recursion from
compiled partial definitions, and enforces the current axiom ceiling.
The host harness will add direct Effect rc.112 type, diagnostic, runtime,
mutation, and replay gates without replacing the Lean judgments.

See [PLAN.md](PLAN.md) for the phased cutover and
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for module ownership. The
literature and Lean API decisions are in
[docs/DESIGN-BASIS.md](docs/DESIGN-BASIS.md); the first-class Schema ruling is
in [docs/SCHEMA-CUTOVER.md](docs/SCHEMA-CUTOVER.md); and all declaration-changing
counterexamples receive stable IDs in
[test/counterexamples/REGISTER.md](test/counterexamples/REGISTER.md).
