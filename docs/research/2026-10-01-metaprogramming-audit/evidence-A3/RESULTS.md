# A3 tested fallback-arm measurement

Base `8c9be258`, implementation branch at `9190c779`; Lean 4.33.1. All source copies
and instrumentation are temporary evidence, not production edits. `README.md` records
preparation; this file supersedes its pending compiler status.

The seven expected logger controls passed: failed attempts emit no retained message;
a locally successful arm abandoned by a later failure is rolled back, including across
multiple goals. Nested-family messages deliberately overlap and cannot be added as
independent proof steps. A partially successful tactic return is separately identified.

Approximation and Scheduling each passed as baseline and instrumented copies. Both versions
used the same temporary path and same instrumentation declarations. Removing the arm wrappers
reproduces each baseline byte-for-byte. The first Approximation baseline reached the end of its
proofs but failed the reporting footer's inferred counter type; declaring Nat fixed the harness.

The complete current-file theorem name sets and type/value fingerprints match: **303** in
Approximation, **168** in Scheduling. This includes generated local theorem declarations.
Fingerprint agreement is a finite control, not a theorem of syntactic equality. The original
source statements and arm bodies were not edited. Cache verification checked **1,094** hashes
in a 406-module closure with zero mismatches. No full battery, generator or trust gate ran.

## Selected arms

These are retained successful selections in the exact source revision, across all nine proof
call sites of the five requested macro families. Not attempted-search totals, timing benchmarks,
or claims about future callers. `results.json` retains each declaration and temporary position;
`census.json` carries original-source locations. Parent/child selections overlap.

| Family | Arm | Selected |
| --- | --- | ---: |
| hops_leaf | 1:spawn_grows | 1 |
| hops_leaf | 2:start_grows | 4 |
| hops_leaf | 3:interruptEach_grows | 2 |
| hops_leaf | 4:countdownPark_grows | 11 |
| hops_leaf | 5:linkScope_grows | 4 |
| hops_leaf | 6:forkFinalizers_grows | 1 |
| hops_observers | 1:hops_leaf | 2 |
| hops_observers | 2:fireObserver_fold_grows | 0 |
| hops_cmd | 1:hops_observers | 2 |
| hops_cmd | 2:drainOwed_grows | 1 |
| hops_cmd | 3:fireObserver_grows | 2 |
| hops_cmd | 4:launchEntrant_grows | 0 |
| hops_cmd | 5:exitFiber_grows | 1 |
| hops_cmd | 6:settle_grows | 1 |
| hops_loop | 1:hops_cmd | 0 |
| hops_loop | 2:drive_extends | 4 |
| queue_hops | 1:spawn_queue | 0 |
| queue_hops | 2:start_queue | 4 |
| queue_hops | 3:interrupts_queue | 4 |
| queue_hops | 4:countdown_queue | 11 |
| queue_hops | 5:link_queue | 4 |
| queue_hops | 6:forkFinalizers_queue | 1 |

## Proposal for the coordinator

- `hops_leaf`: keep a named, strict theorem selector with explicit fixtures. All six arms
  fire. It closes a narrow Extends/Grows judgment, unlike the permissive leaf wrappers.
- `hops_cmd`: keep the domain-specific selector or give these lemmas a dedicated named bank
  when the policy is ruled. Five of six arms fire here. Do not put generic transitivity in
  a global bank; it belongs in the chain caller.
- `queue_hops`: keep a separate selector for QueueKeeps (five of six arms fire). Combining
  queue and trace relations into one global bank would widen search and obscure which
  judgment the proof is establishing.
- `hops_observers`: consider inlining its delegation at current callers. Only its hops_leaf
  arm fires; its observer-fold arm does not. This is a small source simplification proposal,
  not proof that the unused arm is redundant for external/future callers.
- `hops_loop`: consider an explicit drive_extends hop at the current call site. All four
  retained selections choose that arm. Retest any proposed edit before landing it.

No fallback-policy change is landed. The coordinator still owns whether these become named
instruments, aesop banks or explicit calls. Approximation's trace_leaf/trace_chain, Scheduling's
queue_leaf/queue_chain and inline selectors, Handles' fallbacks, and the additional scoped
macros are identified in the audit but are not dynamically measured by these five-family
counts. In particular, this result does not approve silent skip/try branches or exempt macros
from the standing rule. Their normalization and transitivity behavior needs its own controls.
