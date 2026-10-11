# Saved-answer mask hooks

The actual mask hook retains ordered answer classes; pending causes still need their explicit admissibility premise.

Base: `34165e835`.
The landing commit records the head and changed paths.

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Consumers: Workers log history, Timeout cleanup ordering, and the shared typed-pop proof.

`AnswerFlowHooks.lean` proves identity mask contracts and transports the saved suffix through actual `Prim.ensure`.
A replacement failure uses the actual pending cause and the selected saved frame's cause transport.
Native finalizer installation retains the suffix after its actual mask hook.
`Test/Machine/AnswerFlow.lean` applies these facts to native mask and finalizer operations.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.AnswerFlowHooks`: passed, 176 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Machine.AnswerFlow`: passed, 237 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AnswerFlowHooksAudit.lean`: passed.

The audit reports 93 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.
The adjacent output retains the exact audit result.

The full typed-pop connection, native command history, and original scenario goals remain open.
This landing changes proofs only and reaches no behaviour gate.
No runtime agreement or progress follows from these conditional laws.
