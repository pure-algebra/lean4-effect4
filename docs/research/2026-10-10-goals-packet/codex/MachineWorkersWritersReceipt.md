# Workers release writer probe

The probe proves the actual writer equations. It leaves history slot ownership and one-write permission open.

Concept: scope-lifetime-finalization, R11.
Question: the helpers serve `Workers.Assertions.logs_step`, the original preservation claim.
Reach: both actual acquisition and release sources, every total, and arbitrary matching native command residue.
Limit: the command consumer requires its explicit saved environment, heap read, budget and interrupt premises.
Unlock: a shared answer contract can connect actual acquired values and saved release slots to this writer.

Base: `2c68c616c`.
The changed files are this receipt, `MachineWorkersWriters.lean` and `MachineWorkersWritersAudit.lean` in this directory.

The four `#reduce` displays use total one. The source lookup, compiler and expression theorems quantify over every total.
`release_one_command` applies the shared actual native command law. It retains other fibers and unfinished commands.
Both release expressions append their acquired literal once. The store operation answers unit.

Commands:

```
LEAN_NUM_THREADS=3 lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineWorkersWriters.olean docs/research/2026-10-10-goals-packet/codex/MachineWorkersWriters.lean
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineWorkersWritersAudit.lean
```

Both commands pass. The audit reports 13 declarations, zero declarations modulo planned goals, and zero planned goals.

The actual history must retain the first five root bindings and each acquired literal.
The first four bindings need exact allocation keys. A source environment length does not establish those keys.
A release start must create one writer permission. The actual writer must consume it.
No behavior implementation changes. The whole-run log observation remains open.
