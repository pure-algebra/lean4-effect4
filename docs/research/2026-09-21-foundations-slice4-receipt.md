# Foundations slice 4 receipt: independent foundations

Merge note: D12 and C2–C4 are proved and checked. The dependent M3a residual/control
contracts and slice 5 stack theorem remain held. This landing completes the independent
subset the owner selected after slice 3; it does not complete all of the original slice 4.

Base: `5d63f91d6baf46ef4a448e616200ec4325e2b234` (the checked slice 3 landing).
Head: the commit carrying this receipt (`git log -1 --format=%H -- <this path>`).
Branch: `codex/foundations-slices-3-4`; checkout: `/private/tmp/effect4-foundations-slices`.
Nothing pushed. The original checkout and its local document edits are retained.

The scope and acceptance criteria were written in
`2026-09-21-foundations-slice4-independent-plan.md` before implementation. The supplied
probe is retained in `2026-09-21-foundations-independent-input.md`; its corrections and
six finite vendor controls are explained in
`2026-09-21-foundations-independent-probe-disposition.md`.

## Statements and proof boundaries

| Ledger | Statements | Final gate |
| --- | --- | --- |
| `Effect4.Laws.Effects.D12` | `mono`, `bind`, `widen`, `inl`, `inl_inv`, `inr_inv`, `pure_inv`, `plain_iff` | 0 open, 8 proved |
| `Effect4.Machine.RefKernelObligations` | `refWriteBack_peek_other`, `indexed_ref_step_preserves` | 0 open, 2 proved |
| `Effect4.Machine.Refinement.CompositionObligations` | `projects_compose`, `projects_induces_refines` | 0 open, 2 proved |

Each declaration has an exact `#obligation_proved` reference. D12's backing laws live at
`Effect4.Laws.Effects.Typed`; C2's laws at `Effect4.Machine`; C3/C4 at
`Effect4.Machine.Refinement`. All three final ceilings are zero. The new companion module
`Laws/Effects/ProtocolObligations.lean` keeps the reusable Protocol module dependent only
on the pinned Effects algebra, while the companion owns the project ledger.

The retained pre-fill checkpoint has eleven open declarations: eight D12, one C2, two
C3/C4. Its exact sources and hashes are in `statement-snapshot/` and `statement-sha256.json`;
`statements.log` records their successful narrow build. Seven adapted generic protocol
proofs already existed at that checkpoint, but were not yet connected to the new ledger.
It is a declaration checkpoint, not proof of the eleven payloads. The extra lookup helper
was declared and checked during the C2 implementation. This independent landing retains
the checkpoint as evidence in one commit; unlike slice 3, it has no separate production
statement commit. No main C2/C3/C4 statement was weakened during proof filling.
The snapshots and full build/check logs are compressed without changing their bytes.

D12 selects a ghost certificate at each operation. Its precondition, every promised answer
and every future-world continuation use that same certificate. Monotonicity requires
transport of each certified precondition and of the result predicate. It does not assert
global store validity is monotone. `Protocol.plain` uses unit certificates; `Typed.plain_iff`
proves compatibility with the former certificate-free rules for every world, predicate and
program. `PlainTyped` is a comparison predicate on the existing Program, not another IR.

C2 proves indexed heap and answer predicates, unchanged length and exact lookup equality
at every other index, from an actual `refStep` row and its selected-cell kernel premise.
It covers writes and no-write results. It excludes `refMake`, whose kernel is `none`.
The implementation brief now uses `refMake_extension` for allocation and C2 for the
subsequent read or update; the earlier allocation walkthrough could not meet C2's premise.

C3 carries both concrete and intermediate validity through composition. C4 retains concrete
validity in the graph relation and matches successful answers and concrete-none frontiers.
These are generic conditional theorems over deterministic Option steps with the same
operation/answer carriers. They provide no initial-state witness, host-memory instance,
compiler connection, relational stuttering theorem or whole-machine lifting. The OCaml,
C and TypeScript distinctions and implementation evidence grades remain those in the
monotonicity/refinement review §3.

## Controls and trust

`Test/Program/ProtocolCertificates.lean` checks certificate consistency, refusal of an
exchanged certificate, future-world transport, sequencing/widening, both coproduct branches
and their inversions, and both directions of unit-certificate compatibility.

`Test/Machine/Runtime/RepresentationFoundations.lean` checks mixed Nat/Bool cells, writes,
reads, absent keys, unchanged lookups and the allocation exclusion. An executable wrong
write fails the required kernel premise. A nontrivial projection chain checks both success
and frontier observations; dropping the middle invariant, dropping relation validity or
changing the answer is refuted. The indexed rule closes with `Effect4.Stores`; the identical
goal without that bank is a checked `#guard_msgs (error)` control.

The existing `E4-SCHED-CE-006`, `E4-SCHED-CE-007` and `E4-TYPED-CE-003` controls pass unchanged.
They still refute the earlier supplied scheduler and defect-typing claims. The new vendor
probe calls the pinned implementation directly on six manual starting states. It is finite
host evidence, and it does not establish reachability or whole-language conformance.

The final axiom report checks all twelve backing proofs. D12's eight laws and C4 require no
axioms. C2 stays within `[propext, Quot.sound]`; its lookup helper and C3 use only `propext`.
The full repository trust gate adds no implementation exception in this slice.

## Verification

All commands run from this worktree; full logs and the audit driver are retained in
`2026-09-21-foundations-slice4-evidence/`.

- `lake build Effect4.Laws.Effects.ProtocolObligations Effect4.Laws.Machine.RefKernel Effect4.Laws.Machine.Refinement`: statement checkpoint, exit 0, 210 jobs.
- `lake build Test.Program.ProtocolCertificates Test.Machine.Runtime.RepresentationFoundations Test.Counterexamples.Machine.Semantics.InterruptDelivery Test.Counterexamples.Machine.Semantics.StrongExitDefect`: exit 0, 280 jobs.
- `make build`: exit 0, 699 jobs. The trust gate checks 478 modules and 67021 declarations; the closure gate checks 138 API/utility and 201 Laws-only modules, with no core-to-Laws import.
- `make check`: exit 0. Fresh root elaboration and generated-byte drift checks pass.
- `lake env lean -DwarningAsError=true docs/research/2026-09-21-foundations-slice4-evidence/FinalAudit.lean`: exit 0. The binder audit reports 256 paired, 80 without a namesake, zero mismatches. Explicit checked references account for non-namesake proofs.
- `bun docs/research/2026-09-21-foundations-slice4-evidence/VendorInterruptProbe.ts`: exit 0, six passing finite controls.
- `python3 docs/research/2026-09-21-foundations-slice4-evidence/verify-receipt.py`: exit 0; all source/snapshot hashes match, eleven checkpoint statements are unchanged, the nine open names match slice 3, and the source fence holds.

No OCaml estate changed, and no OCaml/C backend tests or `make check-full` claim is made.
Source hashes include the new Lean files and the unchanged held-contract/evaluator/
counterexample files. No runtime, generated representation, checker, root API import or
axiom-allowlist change is included.

## Remaining work

Unique production ledger: **336 total; 327 proved; 9 open**. The nine open names are unchanged
from slice 3:

- `Effect4.Api.M1Origin.source_fork_site`
- `Effect4.Api.TraceFacts.M1Trace.step_agrees`
- `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
- `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
- `Effect4.Api.M1Origin.source_two_race_sites`
- `Effect4.Api.M1Origin.source_forkScoped_site`
- `Effect4.Api.M1Origin.source_race_site`
- `Effect4.Api.M1Origin.source_forkIn_site`
- `Effect4.Run.M1Trace.observe_replace_trace`

The dependent M3a design remains unimplemented: strong values and source/control admission,
concrete `TypedProg`, the 31+40 answer manifest and its checks, actual-delivery adequacy,
interpreter hook contracts and the settling program cases. `FrameAccepts.resume` is unchanged,
and no false `popR_typed` target is inserted into the ledger. An undeclared future interface
is not a proved obligation or an empty-payload placeholder. The replacement delivery
contract must resolve the visited-mask/finalizer cases described in the preflight amendment
and the new probe disposition before the dependent work resumes.
