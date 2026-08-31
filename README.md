# Effect4

Effect4 is a standalone Lean 4 library for modeling closed-alphabet effectful
programs, their denotational and operational semantics, and checked lowering
to selected host profiles such as Effect TypeScript.

This repository is being extracted additively from Foldlab. Foldlab remains
unchanged while shared algebra is moved here and related by explicit
compatibility theorems. The extraction does not copy the incompatible
workshop carriers from Foldlab's Effect Core experiments.

Current state: project bootstrap and architecture freeze. No semantic carrier
has been admitted yet.

The build is pinned by `lean-toolchain`:

```text
lake build
```

See [PLAN.md](PLAN.md) for the phased cutover and
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for module ownership.
