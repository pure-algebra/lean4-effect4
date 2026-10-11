# Actual value selection

Value selection now retains its callback contract and older saved suffix through the actual pop.
Replacement causes and failure-handler discards still need their separate admissibility laws.

Base: `09dd148dc`.
The landing commit records the head and changed paths.

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Consumers: Workers saved callbacks, Timeout cleanup ordering, and native finalizer installation.

`AnswerFlowPop.lean` proves the scratch-drain facts from the existing hook shape theorem.
Its induction follows the existing `popFrom`; it introduces no new transition or program representation.
`getCont_value_selected` retains the selected frame's input class and the remaining stack's class.
`resumeValue_selected` invokes the actual selected arm and attaches its returned frames to that suffix.
Its supplied exit is absent or describes the same successful answer.
`getCont_value_finalizer` invokes the selected saved frame's native program clause after the actual mask hooks.

The native reader passes a mask and a missing value arm before resuming the real constant callback.
The finite control records a pending mask interruption replacing that callback selection.

Command: `LEAN_NUM_THREADS=3 lake build Test.Machine.AnswerFlow`.
Result: passed, 238 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AnswerFlowPopAudit.lean`.
Result: 103 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.
The adjacent build log and audit output retain these results.

Cause selection, replacement-cause admissibility, complete command history, and the original scenario obligations remain open.
This proof-only landing reaches no behaviour gate and establishes no runtime agreement or progress.
