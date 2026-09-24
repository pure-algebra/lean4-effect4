# Slice 5 contract ruling: evidence

Companion to `../2026-09-23-foundations-slice5-contract-ruling.md`.

- `TruePostProbe.lean`, log `true-post.log`: the join-all park code `interpR` installs is
  untypable at answer `nat` under both the protocol judgment the M3a `TypedProg` conjoined
  and the landed one judgment, because a `True` post demands a typed continuation for every
  answer. Finite probe; both theorems at `[propext, Quot.sound]`. Run from the root:
  `lake env lean -DwarningAsError=true docs/research/2026-09-23-foundations-slice5-ruling-evidence/TruePostProbe.lean`.
- `make-check.log.gz`: the `make check` sweep at the final tree (exit 0; the module and axiom gate checked 487 modules and 67,461 declarations at `[propext, Quot.sound]`) (the build with its axiom audit,
  the fresh root elaboration, the generated-file drift).

The checked controls are in the tree, not here: `Test/Program/TypedControl.lean` (the repaired
counterparts) and `Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean` (the three
old contracts, still refuted).
- `Audit.lean`, log `ledger-and-axioms.log`: the unique production ledger (342 total, 333
  proved, 9 open, the same nine names) and every compiled declaration of the counterexample
  and control modules (85) at `[propext, Quot.sound]`. Adapted from Codex's slice 5 audit.
