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
- Regions (`Effect4/Flow/Region.lean`) are out of scope *for D1*: their `enter`,
  `leave` and `finalizer` rows need a third summand and a stateful upper
  handler. That is packet D2, landed 2026-09-03 — see the amendment below.
- The straight-line `Script` embedding is not related to the denotation here
  (packet D5).

## Acceptance

```text
lake build Effect4
lake env lean Effect4Test/Semantics/DenotationContract.lean
lake env lean Effect4Test/Semantics/DenotationAxiomReport.lean
./scripts/test-trust-gate.sh
```

## Amendment: the region denotation (D2), 2026-09-03

`Effect4/Semantics/RegionDenotation.lean` extends this packet to admitted region
flows. Nothing above is rewritten; the region layer is a third summand and a
stateful handler over the same run monad.

### Frozen surface

| Name | Module | Shape |
| --- | --- | --- |
| `Effect4.Flow.RegionFam`, `RegionOpSig` | `Effect4/Semantics/RegionDenotation.lean` | the fallible twin of `Fam`/`Sig`: a `RegionService` answers `Except Val Val` |
| `Effect4.Flow.RegionService.toService` | same | a `RegionService` is already a `Family.Service` for `RegionFam` |
| `Effect4.Flow.Stack` | same | `List (Frame alphabet)`, the runner's open regions, innermost first |
| `Effect4.Flow.ScopeName`, `ScopeName.Param`, `ScopeName.Answer`, `ScopeFam`, `ScopeSig` | same | `enter : RegionId → Unit`, `acquire op release : Val → Option (Except Val Val)`, `leave : Val → Option Failures`, `fail : Val → Failures` |
| `Effect4.Flow.RegionSig` | same | `ScopeSig a ⊕ₛ (RegionOpSig a ⊕ₛ DecSig)` |
| `Effect4.Flow.ScopeM` | same | `StateT (Stack a) (RunM M)` — the only stateful part of the interpretation |
| `Effect4.Flow.Handler.overStack` | same | `StateT.lift` on every clause; the hand-rolled stand-in for `Handler.mapHom (MonadHom.stateT …)`, which lean4-effects v0.3.1 does not have |
| `Effect4.Flow.regionTracedService`, `regionTraceHandler` | same | `logOperation` in place of `Family.Service.traced`, with the same `pure` guard |
| `Effect4.Flow.scopeHandler` | same | its `leave` arm **is** `closeFrame`; its `fail` arm **is** `unwind` |
| `Effect4.Flow.regionHandler` | same | `scopeHandler.sum (overStack (regionTraceHandler.sum decisionHandler))` |
| `Effect4.Flow.denoteRegionsFuel`, `denoteRegions` | same | structural on fuel, mirrors `regionLoop` case for case |
| `Effect4.Flow.closeCause`, `interpretRegionsFrom`, `interpretRegions` | same | D1's `outcomeRows` over the failure-carrying pair, from a given stack and from the empty one |
| `Effect4.Flow.AllPlain`, `allPlain_of_all`, `FlowService.toRegionService` | same | the region-free fragment, and a total `FlowService` read as a `RegionService` |

### Laws

| Theorem | Statement |
| --- | --- |
| `regionHandler_run_*` (eight) | what one operation of each shape runs to, in the goal's own spelling |
| `interpretRegionsFrom_run_handled_pure`, `_handled_bind` | one `vis` with its handler run supplied as a hypothesis — how the dependent `.Answer` is kept out of `rw` |
| `interpretRegionsFrom_run_*` (eight) | the arm lemmas the induction consumes |
| `fail_eq_interpret`, `stuck_eq_interpret` | the runner's `fail` and its stuck frontier, read through the algebra |
| **T1 for regions** `regionLoop_eq_interpret` | `(regionLoop … fuel block env tape stack).run log = (interpretRegionsFrom service nameOf stack (denoteRegionsFuel flow fuel block env tape)).run log`, for `[Monad M] [LawfulMonad M]`; one induction on fuel generalised over block, environment, tape, stack and log |
| `runRegionsCause_eq_interpret`, `runRegions_eq_interpret`, `runRegionsDefault_eq_interpret` | the public faces, run from the empty stack |
| `lookupBlock_erase`, `block?_id` | resolving a block in the erasure is resolving it in the region flow and erasing the terminator |
| `regionLoop_erase`, **`runRegions_erase`** | on a flow whose every block is `plain`, the region runner and the plain runner of `Runs.lean` agree — same result, same unconsumed tape, same log |

Axiom receipts: `Effect4Test/Semantics/RegionDenotationAxiomReport.lean`, within
`propext` and `Quot.sound`; no `Classical.choice`.

### What the amendment does not claim

- **No fuel-free region denotation.** `denoteRegions` is `denoteRegionsFuel` at a
  supplied fuel. The region twin of T2 — *"for every admitted region flow, tape
  and input, `denoteRegionsFuel flow (fuelFor flow.erase tape) flow.entry [input]
  tape` equals a fuel-free `denoteRegionsGo` well-founded through `CyclesWF`"* —
  is not proved and is owed.
- **No stack invariant.** `acquire` and `leave` answer an `Option` because
  `regionLoop` refuses on an empty stack. Region admission should make that
  refusal unreachable; that is not proved, and nothing here assumes it.
- Nothing about the host, and nothing about the frame machine's finalizers (D4).

### Acceptance

```text
lake build Effect4
lake env lean Effect4Test/Semantics/RegionDenotationContract.lean
lake env lean Effect4Test/Semantics/RegionDenotationAxiomReport.lean
lake env lean --run harness/trace/Generate.lean region-oracle
```
