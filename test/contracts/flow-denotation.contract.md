# Contract: the algebraic denotation of a checked flow (D1)

Light ceremony by operator ruling D2: contract, battery and code land together.
Packet D1 of `docs/research/2026-09-03-reification-plan.md`, specified in
`docs/research/2026-09-03-algebra-denotation.md` §1 and §4 rows 1–2. Effects
pin: v0.6.0 (`2447edd`).

## Frozen surface

| Name | Module | Shape |
| --- | --- | --- |
| `Effects.FlowAlphabet.toAlphabet` | `Effect4/Semantics/Denotation.lean` | the flow alphabet minus its identity and lookup; `-- upstream: lean4-effects` |
| `Effect4.Flow.Fam`, `Sig` | same | `alphabet.toAlphabet.toFamily (fun _ => Val)` and its signature |
| `Effect4.Flow.DecSig` | same | `⟨DecisionId × Bool, fun _ => Unit⟩` — the answer is `Unit`, the tape fixed the branch |
| `Effect4.Flow.FullSig` | same | `Sig alphabet ⊕ₛ DecSig` |
| `Effect4.Flow.FlowService.toService` | same | a `FlowService` is already a `Family.Service`; `pure` is a tracing policy, not semantics |
| `Effect4.Flow.denoteFuel` | same | structural on fuel, mirrors `plan`/`loop` case for case |
| `Effect4.Flow.denoteGo`, `denote` | same | fuel-free, well-founded on `(tape.length, (raw.reachSet block).length)` |
| `Effect4.Flow.tracedFlowService` | same | `Family.Service.traced` with the runner's `pure` guard |
| `Effect4.Flow.decisionHandler`, `traceHandler` | same | `(guarded).toHandler.sum decisionHandler` into `RunM M` |
| `Effect4.Flow.outcomeRows`, `close`, `interpretRun` | same | the `done`/`frontier` rows and the closed interpretation |
| `Effect4.Flow.WritesLog` | same | a handler into `RunM M` only appends |

## Laws

| Theorem | Statement |
| --- | --- |
| `reachSet_length_lt_of_edge` | across a declared non-`choose` edge the reachable set strictly shrinks (`CyclesWF`); the measure lemma `denote` needs |
| `edgeNoChoose_of_plan_jump`, `edgeNoChoose_of_plan_perform` | a `jump` or a `perform` travels a declared non-`choose` edge |
| `tape_length_of_plan_choose` | a `choose` consumes exactly one tape entry |
| `denoteGo_eq` | one layer of the fuel-free denotation, with the block resolved |
| `interpret_log_append`, `interpret_log_of_nil` | the log is a writer: a run from `before ++ log` appends `before` to the run from `log` |
| **T1** `loop_eq_interpretRun`, `runTape_eq_interpretRun` | `(runTape fuel …).run log = (interpretRun service nameOf (denoteFuel fuel …)).run log`, for `[Monad M] [LawfulMonad M]`; one induction on fuel generalised over block, environment, tape and log |
| **T2** `denoteFuel_eq_denoteGo`, `denoteFuel_eq_denote` | `fuelFor flow.erase tape ≤ fuel → denoteFuel fuel … = denote flow tape input`; carried by the `LoopBudget` invariant of `Effect4/Semantics/Fuel.lean` |
| `runTape_eq_interpretRun_denote`, `runDefault_eq_interpretRun_denote` | T1 ∘ T2: at the allotted fuel the runner is `interpret` of the fuel-free denotation |
| `runDefault_no_fuel_frontier` | this packet's name for `runDefault_finishes` (`Effect4/Semantics/Fuel.lean`), whose direct proof landed first |

Axiom receipts: `Effect4Test/Semantics/DenotationAxiomReport.lean`, within
`propext` and `Quot.sound`.

## Semantics pinned

- **The denotation is tape-indexed and fuel-free.** `Program` is inductive, so
  every branch is finite, while an admitted flow may cycle (`chosenLoop`). The
  tape is the termination measure and `fun tape => denote flow tape input` is
  DB-03's relational denotation. Admission enters `denote` at exactly one point:
  `CyclesWF`.
- **`decide` is an operation, `done` and `frontier` are not.**
  `Family.Service.traced` writes `op` and `answer` only; `decide` is recovered by
  the `DecSig` summand, whose answer is `Unit` so that both summands write the
  same `StateT Effect4.Trace.Log`. `done` and `frontier` have no former in the
  algebra at all: they are a function of the `RunResult` the denotation returns,
  supplied by `outcomeRows` and appended by `close`. T1 is therefore
  `runner = interpret ∘ denote`, closed by the outcome rows — not
  `runner = interpret ∘ denote` on the nose.
- **The `pure` guard is tracing policy.** `tracedFlowService` suppresses
  `op`/`answer` for the atoms `FlowService.pure` marks, exactly as `step` does;
  `Family.Service.traced` logs unconditionally and is not used here.
- `FullSig` is `Sig ⊕ₛ DecSig` definitionally (`example … := rfl` in the
  battery). Because `Signature.sum` is a plain definition upstream, its `.Answer`
  does not reduce at the transparency `rw` and `simp` match at; the two `rfl`
  lemmas `traceHandler_run_inl`/`traceHandler_run_inr` are the only place that
  reduction is needed.

## What this does not claim

- Nothing about the host. T1 and T2 relate two Lean objects.
- `denote` is well-founded, so it does not reduce in the kernel: every `#guard`
  receipt is taken at `denoteFuel (fuelFor …)`, and T2 is what moves it onto
  `denote`.
- Regions (`Effect4/Flow/Region.lean`) are out of scope: their `enter`, `leave`
  and `finalizer` rows need a third summand and a stateful upper handler
  (packet D2 of the reification plan).
- The straight-line `Script` embedding is not related to the denotation here
  (packet D5).

## Acceptance

```text
lake build Effect4
lake env lean Effect4Test/Semantics/DenotationContract.lean
lake env lean Effect4Test/Semantics/DenotationAxiomReport.lean
./scripts/test-trust-gate.sh
```
