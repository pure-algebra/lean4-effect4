# Module catalogue expansion

Base: `08431c4e81c5f48be2ae8ba810e4fecad8c58139`.
The owner requests more module work and shared authoring tools.
The primary checkout remains with the active editor and organization seats.

## Scope

Independent scouts inspect PubSub, SynchronizedRef, and the Pull, Channel, and Stream modules.
Each scout proposes a bounded implementation before writing it.
The module catalogue and decisions rows 330, 331, 333, and 335 govern each slice.
The coordinator records each accepted slice and its proof placement before integration.

## Shared input values

PartitionedSemaphore supplies source inputs by name, but its value proofs still construct positional tuples.
The new `input_values% (Context) (leaves) {name := value}` syntax uses the existing input declaration.
It orders and types carrier values as `Effect4.Modules.Inputs`, declared in `src/Effect4/Step.lean`.
The explicit identity interpretation remains outside stored steps.
The syntax adds neither a carrier nor stored program syntax.

The Lean elaborator rejects missing, repeated, unknown, and wrongly typed inputs.
An empty declaration produces the existing unit value.
A parameterized declaration retains its type parameters.
The shared name-ordering helper also serves `input_sources%`.

The existing `step-language-sound` and `step-language-typed` claims remain the consumers.
Their meanings and premises stay unchanged.
PartitionedSemaphore provides a production consumer of the named value syntax.
Finite controls exercise input reordering, generic payloads, and deferred identities.
No new semantic theorem or trust exception belongs to this syntax change.

## Completion

The accepted module slices expose useful operations through the public entry modules.
Independent models state their observations and source profiles.
Every new proof names its claim, hypotheses, exclusions, and consumers.
Focused builds, positive controls, and negative controls exercise the changed interfaces.
A scoped audit checks compiled declarations, root reachability, and the core/law import boundary.
The receipt records shared authoring friction and the remaining wrapper obligations.
Commit explicit paths in isolated worktrees.
Run no full sweep and push nothing.
