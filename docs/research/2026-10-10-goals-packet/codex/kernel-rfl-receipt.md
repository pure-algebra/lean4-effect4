# Kernel reflexivity receipt

The coordinator must add the exact tactic module to the audit implementation list before the final gate repair.
The module contains no theorem.
Its Lean metaprogramming reaches `Classical.choice` through `Lean.instantiateMVars`.
The fixture's checked theorem reaches no axiom outside `[propext, Quot.sound]`.

Base: `b74ebab6f2b3f39f0c60d04b25014488b274f197`.
Branch: `codex/symbolic-programs`.

Changed files:

- `src/Effect4/Laws/Auto/KernelRfl.lean`: the shared tactic.
- `Test/Program/KernelRfl.lean`: a symbolic reader and a false-equation rejection control.
- `docs/research/2026-10-10-goals-packet/codex/KernelRfl.lean`: the fixture audit.

Commands and results:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Auto.KernelRfl`: passes.
- `LEAN_NUM_THREADS=3 lake build Test.Program.KernelRfl`: passes, 612 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/KernelRfl.lean`: passes.
- `#axiom_audit Test.Program.KernelRfl`: one declaration within `[propext, Quot.sound]`, zero modulo goals, zero goals.

The kernel rejects the control `n + 1 = n` with a declaration type mismatch.
The reader proves `n + 0 = n` for every natural number.
Neither statement claims a machine or host observation.

Deferred coordinator hooks: `Effect4.Laws` import, `Test.All` import, and the exact audit implementation module entry.
No behaviour gate runs in this slice.
No runtime definition changes.
