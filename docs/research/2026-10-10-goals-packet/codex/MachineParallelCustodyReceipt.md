# Parallel-close accounting control

The internal per-iteration accounting assertion fails at actual parallel cleanup. The control does not refute admitted histories or Workers.

Base: 2cc2e79e. No library statement changes.

## Placement

1. Concept: scope-lifetime-finalization, serving R11.
2. Question: evaluator accounting supplies `Execution.history`, then unchanged `Workers.Assertions.releases_step`.
3. Reach: one constructed native configuration, one foreign finalizer reservation, actual `evaluateNative`, and actual selected-fiber installation.
4. Limit: the configuration has no admitted-history witness. This is a finite projection control, not an application counterexample.
5. Unlock: the census must exclude this cut by discharged application facts or change internal queue accounting before asserting universal debit.

## Observation

The initial configuration has one registration and one reservation. Parallel cleanup starts one child and retains the caller's old cleanup code.

The child and caller each hold one reservation until `closeParAwait` replaces the caller's code. The command queue contains actual child evaluation followed by that overwrite.

The compiled control proves initial `Funded`, negated actual `IterDebit`, and negated funding after selected-fiber installation.

## Route comparison

Workers uses authored `scope`. `enterScoped` allocates sequential scope strategies. Its source has no layers.

A narrower application route needs allocation provenance, sequential stored scopes, and exclusion of residual parallel cleanup. Existing `OpAt` and `ScopesAt` do not provide these facts.

The broad route needs queue-aware accounting which discounts dead caller code only under actual command ownership. This would change the common scalar interfaces.

The coordinator selects the sequential application route first. The original scenario claims retain every premise and conclusion.

## Evidence

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineParallelCustody.lean` passes.

The actual command-list equality checks by reduction. The control propositions check with Lean's ordinary decision procedure.

The imported NativeAccounting audit reports 105 declarations, zero planned goals, and zero declarations modulo goals. It does not audit the control declarations.

Open work: admitted sequential allocation and residual control provenance, complete evaluator debit, and original history closure.
