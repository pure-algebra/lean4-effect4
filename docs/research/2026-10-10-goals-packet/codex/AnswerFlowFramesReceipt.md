# Saved callback composition

Failure delivery retains its no-deferred-interrupt and no-skipped-handler premises.
Constant callbacks require their code only in future states admitting the incoming answer.
The checked control rejects unrestricted transport of transient current code.

Base: `03e2a32c6`.
Head: the commit containing this receipt.

## Placement

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Question: the state-indexed saved-answer contract serves Workers logs and Timeout cleanup and retry.
The original scenario statements remain unchanged.

`AnswerFlowFrames` extends the existing model without adding stored syntax or a second evaluator.
Saved lists compose through their intermediate classes.
An actual callback's pushed frames attach to its older saved suffix.
Failure and constant frames have saved, push, and actual resume readers.
Native finalizer installation reads the exact model program for the same captured exit.
Its caller supplies the saved suffix after the finalizer's mask hook.

The laws supply no source, allocation, state-transition, or whole-history producer.
They establish no cleanup count, progress, or outside-runtime behavior.
The Workers and Timeout lanes retain those concrete obligations.

## Files and checks

New source: `src/Effect4/Laws/Machine/AnswerFlowFrames.lean`, 175 lines.
New fixture: `Test/Machine/AnswerFlow.lean`, 59 lines.
The Laws and Test roots import their respective files.
The fixture applies the laws to the actual native interpreter.
Its controls check an incompatible later state and an enabled interruption that skips a handler.

Commands use `LEAN_NUM_THREADS=3`:

- `lake build Effect4.Laws.Machine.AnswerFlowFrames`: passes, 175 jobs.
- `lake build Test.Machine.AnswerFlow`: passes, 236 jobs.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/AnswerFlowFramesAudit.lean`: passes.

Audit: 85 declarations within `[propext, Quot.sound]`, zero modulo planned goals, zero planned goals.
The adjacent build logs and audit output retain the results.
This proof-only landing changes no runtime or generated output and owes no behavior gate.
