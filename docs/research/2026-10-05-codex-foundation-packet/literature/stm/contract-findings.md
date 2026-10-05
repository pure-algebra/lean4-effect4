# STM contract findings

Primary sources support retry alternatives with branch rollback and combined retry dependencies.
They do not establish rollback for arbitrary Effect code.
This note proposes contracts and changes no repository ruling.

Evidence status: source checked.
Proof role: design input and proposed obligations.
Scope: memory transactions under a named program-admission profile, followed by a separate target agreement claim.

## Sources and decisions

### Harris, Marlow, Peyton Jones and Herlihy

[Composable Memory Transactions](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/2005-ppopp-composable.pdf), PPoPP 2005.
The retained PDF identifies itself as the post-publication version dated August 18, 2006.

- Section 3.1 separates STM operations from irreversible IO.
- Section 5, Figure 4, rules OR1–OR3 make fallback depend on retry, not an exception.
- Section 6.4 restores the enclosing state before the second branch.
- Section 6.4 combines both dependency sets when both alternatives retry.
- Appendix A replaces the earlier exception semantics with rules XSTM1–XSTM3.
- Rule XSTM2 discards writes inside the caught region before invoking its handler.
- Allocation survives when an escaping exception can contain a newly allocated reference.
- Section 6.5 explicitly permits starvation.

Recommendation: retain retry-only alternatives and both-retry dependency union.
Keep allocation and exception recovery outside the first program-admission profile.
If exception recovery later enters that profile, decide its rollback boundary explicitly.
The appendix gives a composability reason for region-local rollback.
The existing Effect probes instead witness retained writes after a caught inner failure.
That difference needs a named target profile.

### Pinned GHC reference implementation

The reference is the `ghc-9.12.2-release` tag, not floating development documentation.

[Sync.hs](https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/libraries/ghc-internal/src/GHC/Internal/Conc/Sync.hs)
contains `atomically`, `retry`, `orElse`, `catchSTM` and `unsafeIOToSTM`.

`atomically` inside another `atomically` raises an exception.
Composition instead combines STM actions under one outer boundary.
`catchSTM` discards the caught region's writes and retains earlier writes.
`unsafeIOToSTM` documents repeated effects, aborted resource acquisition and observable inconsistent reads.

[STM.c](https://raw.githubusercontent.com/ghc/ghc/ghc-9.12.2-release/rts/STM.c)
contains `stmAbortTransaction`, `merge_read_into` and `stmWait`.
An aborted nested transaction contributes its reads to its parent.
`stmWait` validates and retains ownership until registration and parking are established.
This is implementation evidence for dependency retention and the lost-wake boundary.
It is not a GHC execution test or a refinement proof.

Recommendation: distinguish flat composition, alternative-local rollback, and exception-local rollback.
The first does not provide either of the latter automatically.
Do not call a nested Effect `tx` wrapper a GHC nested `atomically`.

### Guerraoui and Kapalka

[On the Correctness of Transactional Memory](https://kapalka.eu/files/opacity-ppopp08.pdf), PPoPP 2008.

Section 5.2, Definition 1 defines opacity through a legal sequential history respecting transaction real-time order.
It includes committed, aborted and live transactions through the defined completion relation.
The following discussion requires each generated history prefix to satisfy the criterion.
Section 3.1 explains why correct transaction endpoints alone miss inconsistent reads inside attempts.
Section 7 separates opacity from progress and discusses extensions for nested transactions.
Section 5.4, Theorem 2 gives a graph characterization, whose proof belongs to the cited extended report.
This audit does not use that theorem as a proved project result.

Recommendation: observe read results if the desired contract promises a consistent view throughout each attempt.
The retained TX4 observation `(0, -1)` fails that candidate contract when the only committed pairs are `(0, 0)` and `(1, -1)`.
A later result of `0` does not repair that observation.
State weaker endpoint agreement separately when that is the intended target contract.
No opacity claim supplies fairness, termination, or rollback of external effects.

## Proposed placement before proof work

These claim names are proposals.
They are not declarations or registered goals.
The coordinator must place each selected claim before dispatching its proof.

| Proposed claim | Concept and property | Consumer | Premises | Observation | Exclusions | Immediate prerequisite |
| --- | --- | --- | --- | --- | --- | --- |
| `tx_body_access_frame` | `residual-program-typing`; proposed transaction admission and dependency property | Atomic attempt and its queue bodies; R4/R10 | First-order admitted body; immutable payloads; all accesses tracked; closed transitive calls | Exit and dependency trace under stores agreeing on observed cells | Arbitrary host functions, alias mutation, untracked reads | Freeze `TxBody` and its evaluator; place a new registry claim |
| `tx_choice_rollback_union` | `translation-simulation`; proposed alternative-composition property | `takeEither` and later transactional modules; R8/R10 | One enclosing attempt; checkpoint before the left branch; retry distinct from failure | Returned value, tentative writes, and both-retry dependency union | Savepoints for arbitrary effects; exception recovery; allocation | Freeze retry-only branch rules and the dependency observation |
| `tx_retry_no_lost_wake` | `reactive-scheduling`; proposed retry-registration invariant serving `scheduler-progress` | Shared wait wrapper and queue quiet-state law; R12 | Validation and enrollment cannot interleave with a relevant commit; cancellation removes registrations | Waiting, runnable, registered and canceled requests | Eventual scheduling, eventual enablement, starvation freedom | Freeze registration, cancellation and posted-delivery states |
| `tx_profile_refines_snapshot` | `translation-simulation`; proposed target adequacy property | First transaction target adapter and composed queue; R8/R10 | `TxBody` admission; immutable values; explicit Effect version; sufficient embedded budget; transitive non-reentrancy | Named exits, stores and wakes; read histories only if required | Unrestricted Effect bodies; hosts; general concurrency; liveness | Decisions 79/80/84; frozen observation and behavioral direction |

The first profile can omit alternatives while their contract remains designed.
It can compose bodies admitted by `TxBody` flatly under one transaction boundary.
Versions, locks and log layouts remain implementation choices after the observation and program-admission contracts are fixed.
A whole-store snapshot does not justify erasing them from an unrestricted preemptible Effect profile.

## Provenance and verification

`downloads.json` records exact URLs, retrieval times, response metadata, sizes and SHA256 hashes.
The manifest check found no STM entry in `vendor/refs/MANIFEST.tsv`.
`pdftotext -layout` extracted both papers for section and rule inspection.
The download command returned exit code 0.
No package installation, build, repository edit or new runtime probe occurred.
The earlier finite probes remain the evidence for Effect behavior.
