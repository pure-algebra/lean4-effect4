# Machine behavior contract

Nodes: BEH/obs and BEH/tape. Implementation: `src/Effect4/Machine/Behaviour.lean`.
Battery and receipts: `Test/Machine/Runtime/BehaviourContract.lean` and
`Test/Machine/Runtime/BehaviourAxiomReport.lean`.

## Required statements

1. `Obs` records all fiber IDs with their optional exits, and the stores. The trace
   is excluded. Equality is decidable at the existing axiom ceiling.
2. `Obs.le` retains completed exits and orders store allocation by `Stores.le`.
   It is reflexive and transitive; it does not compare mutable cell contents.
3. `Beh` observes a fixed initial machine on a fixed decision tape with a
   `Suffices` witness. `Beh_fuel_irrelevant` equates any two sufficient command
   budgets. This does not vary the program's compile budget.
4. `obs_mono_of_le_terminal` transports `ReplayResult.le` for terminal results,
   which that relation requires to be equal.

## Counterexamples and unresolved projection

`BEH-FB-TRACE-ORDER`, row `E4-BEH-CE-001`: the worksheets' unrestricted
`obs_mono_of_le` is false. A frontier with one allocated cell and an empty trace
is related to a frontier with no cells and the same trace. Its cell handle is
lost, violating `Obs.le`. `frontier_projection_false` proves the negation of the
proposed quantified statement. No reachability or same-run condition was present
in that statement. A future projection needs an execution relation or a stronger
order; the trace order is unchanged here.

Row `E4-BEH-CE-002`: `Suffices` holds for an empty tape at zero command fuel,
while a loaded fiber has not run and the outcome is `frontier`. Sufficiency means
that the supplied tape's work settled, not that all fibers terminated. The W1
stopping change must retain this distinction or explicitly change the contract.

These are statements about the Lean machine. Runtime agreement and host
correspondence remain outside this packet.
