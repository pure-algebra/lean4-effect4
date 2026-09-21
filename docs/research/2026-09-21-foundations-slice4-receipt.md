# Foundations slice 4 preflight receipt: held

Slice 4 is not implemented or complete. Its dependent residual/control contract is held
because checked counterexamples refute the supplied interrupt repair. The user has been
asked whether to land its independent protocol/storage foundations or hold the whole slice;
no answer has yet been received. This file records the exact checkpoint, not a partial
implementation presented as completion.

Base for dispatch: `641a0feabe8ff7c3899396cd2144380d6d8cf53c`.
Preflight head: the commit carrying this receipt; slice 3's checked statement checkpoint is
`cd769650`. Branch: `codex/foundations-slices-3-4`. Nothing pushed.

The stop comes from dispatch §2: “Stop the slice, record the smallest amendment, and
continue other work on: a checked counterexample to a frozen statement”. Exact old/proposed
contracts, counterexamples and the smallest reopening are recorded in
`2026-09-21-foundations-contract-preflight-amendment.md` and the amended dispatch.

Checked controls:
- `E4-SCHED-CE-006`: entry correlation, provenance and proposed catch premises hold, while
  restoration inside the walk makes the catch skip and falsifies the proposed output clause.
- `E4-SCHED-CE-007`: deferred interruption does not replace a failing exit in deliverR.
- `E4-TYPED-CE-003`: the proposed strong cause formula still admits badShapeExit for every
  stronger value predicate.

All controls compile at `[propext, Quot.sound]`, are imported by Test.All, and participate
in slice 3's full verification. The source/state equations are exact; no whole-run
reachability proof is claimed. Production `Typed/Contracts.lean` is unchanged.

Pending work remains D12 certificate protocols and compatibility, C2 indexed heap
preservation, concrete strong values/source admission/control typing, the 31+40 answer
manifest and its checks, actual-delivery adequacy, interpreter hook contracts and the
settling program cases. C3/C4 remain on the separate representation track. The historical
research statements are still available as prototypes, not proofs or backend instances.
No false popR target is inserted into the production obligation ledger. The unique ledger
at the accompanying slice 3 landing is 324 total, 315 proved, 9 pre-existing open obligations;
it does not claim to count undeclared future interfaces.
