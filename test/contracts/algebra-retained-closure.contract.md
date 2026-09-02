# Retained algebra closure contract

Status: **MOVED** to lean4-effects `v0.1.0` (`5611c3a`) in slice S4 of
`docs/EFFECTS-SPLIT-PLAN.md`, 2026-09-02. The packet text, its battery
`EffectsTest/Algebra/RetainedClosureContract.lean`, and its counterexample rows live in that
repository at `test/contracts/algebra-retained-closure.contract.md`. Effect4 consumes the algebra through the
`effects` dependency pinned in `lakefile.toml`; the move changed nothing but
the declaration namespace, and `generated/algebra-parity.tsv` there is the
byte-identical receipt against Effect4 commit `217d3e4`.
