# Record term typing signature proof stage

The operations seat can now build its world-membership consumers.
The existing signature congruence statement is unchanged; its proof covers the three new record term constructors.

Base: `91d7ffd2`. Branch: `codex/data-admission`.
Changed source: `src/Effect4/Laws/Program/Signature.lean`.
The five-part placement is in `record-term-brief.md`, under signature extension.
The helpers serve the existing residual program typing claim and `SigExtends.termTy`.
They require equal atom typing and constant flags. They do not change row or service premises.

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Signature
PASS: 247 jobs

LEAN_NUM_THREADS=3 lake env lean /tmp/record-term-signature-axioms.lean
PASS
```

The axiom queries name `argTy_congr`, `argsTy_congr`, `termTy_congr` and `SigExtends.termTy`.
Each reports `[propext, Quot.sound]`.
Logs: `/tmp/record-term-signature-build.log` and `/tmp/record-term-signature-axioms.log`.
No target dependency was needed for this narrow check.
No full battery, generator or root axiom gate ran.
The Lean slot is released to the target seat.

`Test/Program/FormationContract.lean` remains an uncommitted entry-point fixture extension.
Its final check still needs the target and canonical Program dependencies.
