# Cause selection and interrupted handlers

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Questions: Workers log history and Timeout cleanup require cause selection through the actual saved stack.

The actual failure pop can discard an existing failure handler after its hook runs.
The saved contract currently describes missing failure arms, which does not cover this case.
Extend that same contract with an explicit discard clause.
Require an actual failure arm, an interrupted hook result, and the actual `skippedCause` equation.
The resulting cause must satisfy the older stack's incoming class in the same world.

This strengthens a proof premise and changes no runtime definition or original scenario statement.
Protected finalizers cannot satisfy the interrupted-hook premise.
The application instances must prove their actual sanitizer and heap premises.
No additional saved-stack representation is introduced.

Then prove cause selection by induction over the actual `popFrom`.
A pushed restoring mask cannot select a failure handler and retains the carried cause when discarded.
Connect the selected callback and finalizer consumers to the same `StackAt` relation.
Pending replacement and deferred causes retain explicit admissibility obligations.

Build the shared consumers, migrate both application instances, and audit every changed module.
This proof-only slice reaches no behaviour gate.
