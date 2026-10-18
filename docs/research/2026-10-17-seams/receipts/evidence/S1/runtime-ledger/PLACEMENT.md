# S1 runtime undo ledger

This supplement retains the planned single document action interpreter.
It changes no persisted representation: the accepted action history remains the load input.

Concept: initial-algebras-folds; source-session-coherent and document replay, R14.
Question: `Doc.step_replay`, compatibility; retain the complete existing public observation.
Reach: every sealed document carries the full replay state, including its derived undo entries.
`Doc.replayed` projects the exact existing source-session replay equation.
`Doc.sealRuntime` extends that witness through one `DocInternal.apply` call.
These helpers serve document step and ST4's single traversal of accepted actions.
They establish no host execution, hash property, or constant-time cost for an individual edit.

The earlier preparation reconstructs the entire document history when a revert needs its undo entries.
A repeated revert therefore repeats old checker asks, even though Tool advances one action at a time.
Retain the old trace control as evidence before replacing that reconstruction with the witnessed runtime ledger.
The corrected step still applies every new inverse through the same policy feed.
The ledger stays inside the sealed in-memory document and is rebuilt during accepted-action replay.
