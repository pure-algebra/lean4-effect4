# Named Pool list authoring

Pool's authored bodies now use named inputs and the common list builders.
The six operation agreement statements retain their independent model and original hypotheses.
The six typing statements retain the generic resource type and original formation premises.

Base Pool checkpoint: 722d72ea.
Shared helpers: fca76c16, e36c40e4, and 04a936ca.
Named authoring prerequisites: 56c2326a, 30fe0e2f, and b024f2ef.
Interpretation prerequisites: 47f9eb3f, 43f3b82e, and 643de404.
The shared list composition prerequisite is 1e1d5819.
The head is the explicit-path commit containing this receipt.

Changed files: Modules.Pool.Data, Passes, and Steps; Laws.Modules.Pool.Data, Passes, Reading, Typing, and Ops; Test.Program.PoolData.
Each named context declares its input names and types once.
Step inputs and source applications consume the same context.
Generic pass operands are Step trees.
Item bodies use item_step and read the item and outer values alone.
Map, filter, removal, any, and headOr expand to existing Step data.
The authored bodies contain no positional input or binder expressions.
The low-level name-derived Input aliases remain in the Laws graph for existing readers.
The Laws graph supplies Input-to-Step compatibility for those readers alone.
No production input getter remains.

Placement: Translation Simulation, pool-steps-agree, requirement R10.
The pass equations consume the shared list equations before connecting to Pool's independent model.
The selected-lease connector consumes Step.Lists.filter_map_eq_flatMap.
The retired front-fold helper has no remaining consumer.
Step-language-sound supplies source reading; Step-language-typed supplies operation typing, requirement R4.
Step.scoped supplies operation construction scope.
Identity removal retains table injectivity and the deferred identity interpretation.
These conditional laws establish no allocation, membership, progress, cost, or host execution claim.

Commands and results:

- `LEAN_NUM_THREADS=3 lake build Effect4.Modules.Pool.Steps`: passed after named source migration.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Ops Test.Program.PoolData`: passed with the named sources, then passed with named Step operands and common lists.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Ops Test.Program.PoolData Test.Program.PoolAgreement`: passed after the shared list composition integration, 904 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Program.PoolData`: the reordered waiter control passed, 864 jobs.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/pool-data-trust.lean`: passed for 700 final compiled Pool declarations.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/step-lists-control.lean`: shared finite controls and focused trust passed.
- `git diff --check`: passed.

The Pool battery compares all six operations on four retained cells with the independent model.
The new control reverses the two same-typed waiter inputs and supplies source arguments by name.
The shared finite control checks both nonempty and empty head defaults beside map, filter, removal, and any.
The trust controls use auditedFacts and reachedAxiomsMany.
They reject unsafe, partial, axiomatic, external, replaced, and bodyless declarations.
They permit only propext and Quot.sound.
No declaration rests on an admitted proof.

Intermediate checks exposed anonymous Input arguments after the operand change.
The final proofs supply explicit Step variables or named specializations.
The head helper's retained scope assumption has an unused name because the implementation no longer folds.
No statement loses that assumption.
The private generic filter-map proof is removed after the shared helper lands.
All checks run serially in the isolated worktree with LEAN_NUM_THREADS=3.
No whole battery, root gate, target compiler, or external host run is claimed.
Roots, registers, and generated reports remain coordinator-owned.
