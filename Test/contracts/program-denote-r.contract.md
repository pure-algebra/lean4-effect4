# Program denotation over stores and fibers

Status: FROZEN / GREEN, amended for R3/R4. On 2026-09-06 the owner authorized retaining
handler and cleanup boundaries after a probe against `c462cd1` showed that
the former denotation erased a difference observable under interruption.
Design and evidence: `docs/research/2026-09-06-r3-r4-implementation.md`.
The earlier fuel and answer corrections remain recorded in
`docs/research/2026-09-06-w3-r2-continuation.md`.

Implementation: `src/Effect4/Program/DenoteR.lean`, with the answer and frontier
amendments in `src/Effect4/Program/Sched.lean`. Tests and dependency receipts:
`Test/Program/DenoteRContract.lean`, `Test/Program/DenoteRAxiomReport.lean`, and
the existing scheduler signature battery. The obligations below are proved;
whole-tree integration and the R3/R4 runtime gate also pass. Final receipt:
`docs/research/2026-09-06-r3-r4-implementation.md`.

## Frozen corrected meaning

`denoteR root n e p : Effects.Program RSig ExitV` is a bounded unfolding of
`e` at `p`. `n` bounds the recursive unfolding, independently of the compile
budget `p.fuel`. The compiler's actual address and environment conventions
remain authoritative. `Eff` is the only stored program representation.

`guardR kind body` retains the boundary of a success continuation, failure
handler, both-arm handler, or exit finalizer. `guard_ kind` answers `none`
to enter the body and `some exit` to resume outside its saved boundary;
`unguard exit` closes the normal body path. `onExitR` retains the finalizer
boundary and ends with `finishFinalizer exit` after the finalizer result is
merged. The evaluator owns interruption and mask restoration at these markers.

`controlErasure` removes only these control markers: entry answers `none`,
and the closing markers answer with their carried exit. It retains every
other store and fiber operation. `eraseControl` interprets that handler and
commutes with `pure` and `bind`. This erasure is the observation used by the
straight-fragment theorem; it is not an interruption or scheduler semantics.

`pending reason resumeAt` is a visible frontier operation, never a pure exit.
Its data records whether compile fuel, unfolding fuel, a choice, or support
for a source form is missing. It also records the program point, generator
program counter/environment/scan budget, or loop cursor. The later scheduler
must not answer a frontier with a default exit. The existing placeholder
handler is outside this meaning.

Mask, scope, winner and effect-join operations answer with `ExitV`. Async, scoped
forks and scope close also answer with exits because their computations can
fail. Value operations retain `Val`; boundary entry uses `Option ExitV`.
Fork and mask bodies use the first-order `Body`: an existing source point,
a store finalizer name with an exit, or a list of fibers to interrupt. Other
source bodies keep their points. A scoped node carries the allocated
scope id, and a `forkIn` node carries the actual link key. The existing exit
encoding was already reversible; the scout's collision claim was false.

The generator walker navigates the existing root using `blockAt`, `blockExit`
and `loopExit`. An inline source success consumes scan fuel; a resumed yield
resets scan fuel from the generator's saved point. `sync` is not classified
as an inline source success even when its denotation is pure. The source
classifier `inlineYield` must equal the immediate-exit projection of
`compileEff` for every source term and point.

## ENSURES

1. `denoteR_zero` and `denoteR_compile_zero` retain live frontiers.
2. `denoteR_bind`, `denoteR_branch`, `denoteR_choose`, `denoteR_withFiber`,
   `denoteR_gen` and `denoteR_whileLoop` expose the structural unfolding at
   positive compile fuel. The bind equation retains `guardR .onSuccess`.
   Choice consumes a Boolean but not compile fuel.
3. `inlineYield_eq_headExit` agrees with the compiler's immediate exit head.
4. `eraseControl_pure`, `eraseControl_bind`, `eraseControl_guardR` and
   `eraseControl_onExitR` give the control-erasure equations. In particular,
   a guarded body erases to the erased body; an exit finalizer erases to
   sequential body/finalizer interpretation and `restoreAfterFinalizer`.
5. `denoteR_straight`: for all `root`, `e`, `n`, `p`, if `Straight e = true`,
   `Agreement.depth e ≤ n` and `Agreement.depth e ≤ p.fuel`, then
   `eraseControl (denoteR root n e p) = Effects.Program.inl (denote e p.env)`.
   The depth hypotheses are unchanged; the raw term now retains control
   boundaries needed by the scheduler.
6. `meaning_denoteR_straight`: under the same premises, interpreting
   `eraseControl (denoteR root n e p)` with `rHandler` gives
   `meaning e p.env stores`. This corollary applies only after erasure and
   the straight restriction eliminate all fiber operations.

## Falsifiers and boundary

Retain `E4-SCHED-CE-002` (the scout's encoding claim disproved) and
`E4-SCHED-CE-003` (zero-fuel failure and unrestricted straight agreement
disproved). Finite batteries cover both choices, branch paths, fork addresses
and link keys, scope ids, success-valued errors versus failures, async
decoding, store updates before a failure/finalizer, malformed terms, generator
scope exit and break, inline versus resumed yield budgets, and loop cursors.

`cleanup_boundary_distinct` proves that the unfolded `onExit (yieldNow 0)
cleanupUnit` differs from `bind (yieldNow 0) cleanupUnit`. Raw guards inspect
their distinct `onExit` and `onSuccess` markers, while the erased terms are
equal. This is the contract repair prompted by the reference machine running
cleanup after interruption only in the first program. The store observer now
erases control markers explicitly; separate raw probes confirm that erasure
retains yield, other fiber operations and live frontiers.

`RDEN-FB-HANDLER`: `rHandler` is a placeholder on fibers and frontiers.
`RDEN-FB-SCHEDULER`: R2 constructs the operation tree. It does not implement
the later scheduler's mask, scope, interruption, cancellation or fairness
rules, or prove any general relation to machine execution. Those rules and
the general machine simulation remain R3 and later obligations. The
erased straight restriction is the only execution-meaning theorem here.
`RDEN-FB-UNSUPPORTED`: program-kind operations and acquisition/release remain
frontiers, as they are in `compileEff`; this packet adds no support for them.

Gate: all batteries reachable from `Test/All.lean`, whole-tree
`lake build Effect4 Test`, no new axiom allowances. Expected ceiling:
`[propext, Quot.sound]`. No host equivalence or coverage increase is claimed.
