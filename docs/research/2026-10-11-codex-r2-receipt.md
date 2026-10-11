# R2 message design receipt

Apply messages after the local write-back and before the outcome disposition.
The countdown observer also needs an ordered edit after its own waiter write-back.
The probe does not change core code.

Base: `4b6645156`.
Head: the commit containing this receipt.
Design: `docs/research/2026-10-11-codex-r2-message-plan.md`.
Evidence kind: Lean proofs, compiling finite cuts, and finite pin evaluations.

## Changed files

All files live under `docs/research`.
The slice adds the plan and this receipt.
The `MachineEditMessages` Lean probe defines the first-order payload and generic core interpreter prototype.
Its audit reader checks the newly compiled probe module.
The pin script checks the same self-target cases using the installed runtime.
The output files retain the exact successful results.

## Placement

Concept: reactive-scheduling, R4/R11, serving the proposed `command-moves` structure.
Reach: actual native producer functions at concrete machine records, plus the retained admitted CE046 program.
Consumer: the R2 migration and shared interference/frame/ledger consumers.
Limit: no new history, liveness, or full runtime correspondence theorem.
Workers log debit and the other original open endpoints remain open.

## Commands and results

Run with `LEAN_NUM_THREADS=3` in the managed machine-structure worktree.

- `lake env lean -R docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineEditMessages.olean docs/research/2026-10-10-goals-packet/codex/MachineEditMessages.lean`: passes.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineEditMessagesAudit.lean`: passes.
- `lake build Test.Counterexamples.Machine.Semantics.SelfInterrupt`: passes, 157 jobs.
- `bun docs/research/2026-10-10-goals-packet/codex/MachineEditMessagesPin.mjs /Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect`: passes.

The prototype audit reports 82 declarations within `[propext, Quot.sound]`, zero goals, and zero modulo goals.
The library classification reader reports 232 declarations under the same bounds.
No new proof rests on an open goal.

The pin script checks package version `4.0.0-rc.112` before evaluation.
Self join, self countdown, open self link, and countdown callback each retain one observer.
Closed self link and self interruption exit with `Failure`.
The retained CE046 source exits interrupted before its log write: child `Failure`, reason `Interrupt`, log zero.

The Lean cuts distinguish each erased field from its retained message result.
The nonalias join retains the exact settled result by `rfl`.
The cause-payload record operation equals the existing generic interrupt record operation by `rfl`.
Applying the interrupt after complete parked settlement produces idle `evaluate`, rather than the required deferred `loop`.

## Size and remaining work

This slice adds research probes only.
It removes no library source lines and introduces no library evaluator or command census.
The implementation and its shared-law migration remain open.
Root owns labelled moves and footprint changes.
The exact R2 executable partition requires coordinator review of the plan.
Behaviour gates wait for that implementation and its coordinated sweep.
