# Behavior pass after the first-exit landing

Every behavior gate reached by this landing passes.
The universal scenario proofs still have named open obligations.
These finite comparisons do not establish those obligations.

## Commits and files

The packet base is `b74ebab6f2b3f39f0c60d04b25014488b274f197`.
The pre-landing head is `dd7dedb93`.
The landing commit owns this receipt and its explicit file list.

The OCaml projections now contain the first-exit race.
The conversion preserves constructor ordinal seventeen; the earlier ordinals keep their meanings.
The new `pRaceFirst` golden covers failure beside success.
The existing ordinal and randomized wire tests include the new constructor.
The scenario fixture generator updates the timeout fixture from the current admitted source.
No generated file receives a manual edit.

The roots reach `ReleaseCustody.Execution` and `HostTimeoutSource`.
The source import walk finds no new orphan and no Laws import from the core root.
The semantics generator records the integrated proof statuses.

## Commands and results

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers Test.Dogfood.Proofs.HostTimeoutSource OCaml5.Eff.Goldens` passes.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Dogfood.Proofs.HostTimeoutSource` passes.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/IntegratedBehaviorAudit.lean` passes.
- `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only lcnf` passes.
- The same generator command with `eff`, `wire` and `cas` passes in dependency order.
- `make check-ocaml` regenerates the fixtures and passes.
- `make check-ts-reader check-native check-compiler` passes.
- `make check-corpus check-tsdiag` passes.
- `make gen-semantics` passes.

The reader run passes 765 tests with 3809 assertions.
The native and compiler profiles publish passing receipts under `.lake/conform/`.
The OCaml replay comparison checks 508 programs, 3248 tapes and 72840 positions, with no divergence.
The new race golden agrees between both generated-engine instances.
The corpus matches all 400 committed results, including its 25 registered disagreements.
The diagnostics gate finds no typed program refused by the pinned tsgo 7 compiler.

The previous gate receipt records passing truth, keyed host and target checks.
The timeout host observation still waits on selected entrant identity and some timers.
This landing does not broaden that observation claim.

## Axiom output and open work

`IntegratedBehaviorAudit.out` retains the checked output.
The custody group contains 668 declarations, two modulo declarations and two planned goals.
The host-source group contains 71 declarations with no planned goals or dependencies on them.
Both groups stay within `[propext, Quot.sound]`.

The command and scheduler-edit custody obligations remain open.
Source placement, source-state preservation and scenario-specific history obligations remain open.
The whole battery and whole-tree axiom sweep remain owner-triggered checks.
Nothing is pushed.
