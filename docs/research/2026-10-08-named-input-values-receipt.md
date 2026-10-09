# Named input values receipt

The authoring syntax removes positional value tuples from the PartitionedSemaphore proof callers.
It changes no stored step, theorem statement, or identity interpretation.

Base: `08431c4e81c5f48be2ae8ba810e4fecad8c58139`.
The plan is `docs/research/2026-10-08-module-catalogue-expansion-plan.md`.

## Interface

```lean
input_values% (Data.RequestInputs) (Leaves.refused) {
  cell := encoded state, requested := amount
}
```

The existing named declaration determines the values, source inputs, and step variables.
The Lean elaborator checks each value against its carrier type.
The explicit interpretation keeps contextual identities separate from natural numbers.
The names disappear after Lean elaboration.

## Placement

The source is `src/Effect4/Step/Elab/Inputs.lean`.
The shared name-ordering function serves source inputs and value inputs.
The production consumers are the PartitionedSemaphore value and reading laws in `src/Effect4/Laws/Library/PartitionedSemaphore/`.
Their consumer remains `partitioned-semaphore-bookkeeping`, with its existing simulation role and R10 scope.
The syntax adds no semantic claim, proof premise, or axiom exception.

## Checked evidence

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.StepInputs Test.Program.PartitionedSemaphoreBookkeeping` | Pass |
| `LEAN_NUM_THREADS=3 lake build Test.Program.StepInputs` after the final negative-control repair | Pass |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-named-input-values-audit.lean` | Pass: 35 compiled declarations, permitted axioms only |

Five new positive controls cover reordered contexts, generic payloads, empty inputs, and deferred identities.
Seven negative controls cover repeated, missing, unknown, malformed-declaration, wrong-value, wrong-identity, and wrong-expected-type inputs.
Existing source-input controls still pass.

The first compiled audit detected an erroneous declaration inside a negative `#guard_msgs` control.
The final controls use `#check`, so rejected terms create no declarations.
The repeated audit passes at `[propext, Quot.sound]`.

No emitted bytes change in this slice.
No host comparison, allocation theorem, or module scheduling claim follows.
No full sweep, primary-checkout integration, or push runs.
