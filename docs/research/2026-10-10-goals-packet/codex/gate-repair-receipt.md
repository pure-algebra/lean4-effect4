# Deferred gate repair

The scenario gate now accepts clause proofs that depend on named planned goals.
It still refuses a top theorem with an unlisted dependency or an unused clause.
This repair does not complete the remaining scenario obligations.

## Commits and scope

The packet base is `b74ebab6f2b3f39f0c60d04b25014488b274f197`.
The pre-landing head is `da872a016`.
The landing commit owns this receipt and its explicit file list.

The library roots now reach the landed proof modules and fixtures.
The core root still reaches no Laws module.
The meta-only kernel tactic has an exact module exemption beside its kernel rejection fixture.
The proof ceiling remains `[propext, Quot.sound]`.

The registry places finalizer funding, source placement, admitted histories and recorded call prefixes.
The generated semantics report derives their statuses from their proof terms.
The timeout counterexample has stable ID `E4-HOST-CE-009`.
The contract note records the owner's completed-timeout ruling.

## Checked commands

- `LEAN_NUM_THREADS=3 lake build OCaml5.Eff.Goldens Effect4.Laws Test.Dogfood.Scenario.Gate` passes, with 1331 jobs.
- `LEAN_NUM_THREADS=3 lake env lean harness/truth/session/Keyed.lean` passes.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/GateRepairAudit.lean` passes.
- `make gen-semantics` passes.
- `make check-truth` passes: 81 programs, with ten signed divergences.
- `make check-host-protocol` passes: 57 keyed host runs and 72 scenario scripts across 267 host runs.
- `make check-target` passes: 102 target cases and 600 assignability pairs.

`GateRepairAudit.out` retains the axiom output.
The three audit groups contain 2099, 254 and 429 declarations.
Their modulo counts are zero, seventeen and zero.
The middle group contains two intentional planned goals in the gate fixture.

## Behavior repairs

The cells reader encodes stored failed exits through the native cause image.
It refuses unsupported errors, annotations and interruptors with no recorded identity.
Lean and TypeScript controls pin the same tagged-failure image.
The race premise refuses the fibers reader for both race forms.

The timeout observation includes completed forms in its transport.
The host has no reader for selected entrant identity, so that field waits in all fourteen scripts.
Timers still wait in five scripts.
The host gate reports those limits; it claims no whole timeout observation agreement.

The seeded corpus keeps its existing stream.
The first-exit race has dedicated source, codec and foreign-reader controls, outside randomized coverage.
The OCaml golden writer now accepts the new constructor.
Its narrow build passes; projection regeneration and the reader rerun follow this landing.

## Open work

The TypeScript reader, native, compiler, OCaml, corpus and diagnostics gates remain in this repair pass.
The remaining scenario proofs retain their original quantification and named dependencies.
The whole battery and whole-tree axiom sweep remain owner-triggered checks.
No output from this landing is pushed.
