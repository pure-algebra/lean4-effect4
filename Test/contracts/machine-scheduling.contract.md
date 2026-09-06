# Finite scheduling contract

LIVE/fair. Implementation: `Machine/Scheduling.lean`. Battery and receipts:
`Test/Machine/Runtime/SchedulingContract.lean` and `SchedulingAxiomReport.lean`.

`QueueKeeps` says the old armed queue is a prefix of the new one. Every helper
reached by the concrete frame evaluator, and then `driveState` and a dispatcher
snapshot's tasks, keeps that prefix. Only entering a callback disarms its owner;
newly armed owners join behind the existing queue.

`FiredWithin` follows the actual `flushAllState` control path, using its shared
`fireState` and receipts. It counts callbacks entered, including empty dispatch
snapshots, and stops at the same stuck or fuel boundary. It does not count an
unknown owner as a callback.

`flush_fair` states that every initially armed owner is entered within a round
bound at least the initial queue's length. Its premises are a duplicate-free
initial queue and `FlushReady` for that length: each required callback has a real
owner, no stuck marker and sufficient command fuel. Callback rearming does not
invalidate the bound. This does not guarantee that the entire flush terminates.

`FairTape` requires each armed owner at an executable, non-stuck prefix to have
a later decision that actually services it. A syntactic flush after a fuel
frontier does not satisfy the requirement.

`E4-LIVE-CE-001` / `LIVE-FB-FUEL`: two valid armed owners and two rounds do not
service both at command fuel one. The first command loop exhausts its budget,
leaving the second owner queued. The battery proves the negation of the
unconditional round-bound claim. At fuel forty both owners are serviced.

`E4-LIVE-CE-002` / `LIVE-FB-UNKNOWN-OWNER`: a queue headed by nonexistent owner
seven cannot advance to its real owners. These premises are necessary, not
implicit host assumptions. No host fairness or infinite-run theorem is asserted.
