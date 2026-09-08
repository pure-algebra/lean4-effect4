# Program denotation over stores and fibers

Status: FROZEN / GREEN, amended for R3/R4. On 2026-09-06 the owner authorized retaining
handler and cleanup boundaries after a probe against `c462cd1` showed that
the former denotation erased a difference observable under interruption.
Design and evidence: `docs/research/2026-09-06-r3-r4-implementation.md`.
The earlier fuel and answer corrections remain recorded in
`docs/research/2026-09-06-w3-r2-continuation.md`.

Implementation: `src/Effect4/Laws/Program/DenoteR.lean`, with the answer and frontier
amendments in `src/Effect4/Laws/Program/Sched.lean`. Tests and dependency receipts:
`Test/Program/DenoteRContract.lean`, `Test/Program/DenoteRAxiomReport.lean`, and
the existing scheduler signature battery. The obligations below are proved;
whole-tree integration and the R3/R4 runtime gate also pass. Final receipt:
`docs/research/2026-09-06-r3-r4-implementation.md`.

## Frozen corrected meaning

`denoteR root e p : Effects.Program RSig ExitV` is structural on `e` at `p`
(P2, 2026-09-06). The compile budget `p.fuel` is its only budget, spent as
`compileEff` spends it; the former unfolding budget and its frontier reason are
gone, because loops and generators are the runtime operations `loop` and `gen`
whose later iterations the evaluator runs inside the body's delivery
(`program-runtime-r.contract.md`). The compiler's actual address and environment
conventions remain authoritative. `Eff` is the only stored program representation.
The counted checkpoints the host spends where the term has no work of its own are
explicit: `suspendR` in front of a suspension, a decided branch, a yieldable
error's failure and the generator and loop entries, and `sync` for a pure thunk's
value. Under source-repairs §12, `scoped` is one fiber entry at its eager body
point. The runtime installs the existing OnExit guard, restores context in its
exit callback and distinguishes unsafe close's absent and returned effects.

Since 2026-09-06 (`E4-CHECK-CE-001`) `exit b` folds to the reified exit when
`inlineYield` classifies `b` at the child point as an immediate exit, as the
pinned `Effect.exit` folds an `Exit` body (`internal/effect.ts:3621-3622`);
only a body that is not one keeps the both-arm boundary. `inlineYield` itself
classifies `exit` through its body and never classifies a `whileLoop`, whose
compile is now a `Suspend` (`E4-CHECK-CE-003`).

`guardR kind body` retains the boundary of a success continuation, failure
handler, both-arm handler, or exit finalizer. `guard_ kind` answers `none`
to enter the body and `some exit` to resume outside its saved boundary;
`unguard exit` closes the normal body path. `onExitR` retains the finalizer
boundary. Under the D4 source correction, its cleanup has an ordinary success
guard, with an inner failure guard only when the body failed. Successful
cleanup ends through `finishFinalizer`; propagated cleanup failure passes the
success guard and consumes the saved mask in the existing pop. This retains
the false cleanup delimiter and the erased `restoreAfterFinalizer` meaning.
The evaluator owns interruption and mask restoration at these markers.

`controlErasure` removes control markers and checkpoints: entry answers `none`,
closing markers answer with their carried exit, suspend answers unit, and sync
answers its carried value. D5's construction query answers the empty view.
It retains the other store and fiber operations. `eraseControl` interprets that handler and
commutes with `pure` and `bind`. This erasure is the observation used by the
straight-fragment theorem; it is not an interruption or scheduler semantics.

`pending reason at_` is a visible frontier operation, never a pure exit. Its
data records whether compile fuel, a choice, or support for a source form is
missing, and the program point. A generator's scan exhaustion is a runtime
frontier of the evaluator's walk, under its saved generator slot. The scheduler
must not answer a frontier with a default exit. The existing placeholder
handler is outside this meaning.

Mask, scope, winner and effect-join operations answer with `ExitV`. Async, scoped
forks and scope close also answer with exits because their computations can
fail. Value operations retain `Val`; boundary entry uses `Option ExitV`.
Fork and mask bodies use the first-order `Body`: an existing source point,
a store finalizer name with an exit, or the race whose settled cleanup the
masked body runs (`Body.raceCleanup`, denoted by the store's `cancelRace`
program; source-repairs §16 D6a). Other
source bodies keep their points. A scoped entry carries its body point; its
administrative exit callback carries the allocated scope and previous context.
A `forkIn` node carries the actual link key. The existing exit
encoding was already reversible; the scout's collision claim was false.

The generator walk (`InterpR.walkR`, the term instance of the compile's
`runStmts`) navigates the existing root using `blockAt`, `blockExit` and
`loopExit`. An inline source success consumes scan fuel; a resumed yield resets
scan fuel from the generator's saved point. `sync` is not classified as an
inline source success even when its denotation is pure. The source classifier
`inlineYield` must equal the immediate-exit projection of `compileEff` for every
source term and point.

## ENSURES

D5 construction amendment (2026-09-06): `Point.completed` is a captured,
first-order list of completed fiber exits. Both `denoteR.awaitFiber` and
`inlineYield` use `Point.awaitExit`, matching the compiler's eager join/await
fold. An Async built while its target was live keeps its registration and
subsequent exit checkpoint even if the target later finishes.

`constructR` requests a fresh view only at source suspension, selected branch,
success/cause callback and finalizer invocation. `prepareR` structurally
answers such queries and prepares a guard's eager body branch; it retains
the saved exit callback and stops at counted operations. Eager mask/fork
bodies retain their captured view. Generator/loop hooks take the same fresh
view before constructing and classifying the next body. The root's view is
empty. `eraseControl_constructR` answers `[]`, so `denoteR_straight` and
`meaning_denoteR_straight` retain their exact statements and assumptions.

The public straight-run proof port and full D5 repaired-tree gate pass:
282 jobs, fresh audit of 276 modules / 39,483 declarations at the unchanged
ceiling, forced census and the nine-program emitted truth battery. The wider
P3 simulation and remaining source repairs are still open.

1. `denoteR_zero` retains the compile-fuel frontier at the point.
2. `denoteR_bind`, `denoteR_suspend`, `denoteR_branch`, `denoteR_exit`,
   `denoteR_choose`, `denoteR_withFiber`, `denoteR_gen` and `denoteR_whileLoop`
   expose the structure at positive compile fuel. The bind equation retains
   `guardR .onSuccess`; the exit equation folds an immediate exit and otherwise
   retains `guardR .all`; the suspension, branch, generator and loop equations
   carry `suspendR`, and the generator and loop equations end in the entry
   operations. Choice consumes a Boolean but not compile fuel.
3. `inlineYield_eq_headExit` agrees with the compiler's immediate exit head,
   `headExit_eq_asExit?` identifies that head with the machine's `Prim.asExit?`,
   and `denote_of_inlineYield` says a straight form classified as an immediate
   exit denotes to exactly that exit; the straight theorem's `exit` case uses it.
4. `eraseControl_pure`, `eraseControl_bind`, `eraseControl_guardR`,
   `eraseControl_onExitR`, `eraseControl_suspendR` and `eraseControl_sync` give
   the erasure equations. In particular, a guarded body erases to the erased
   body; an exit finalizer erases to sequential body/finalizer interpretation and
   `restoreAfterFinalizer`; a checkpoint erases to what follows it.
5. `denoteR_straight`: for all `root`, `e`, `p`, if `Straight e = true` and
   `Agreement.depth e ≤ p.fuel`, then
   `eraseControl (denoteR root e p) = Effects.Program.inl (denote e p.env)`.
   The unfolding premise is gone with the budget; the raw term retains the
   control boundaries and checkpoints the scheduler needs.
6. `meaning_denoteR_straight`: under the same premises, interpreting
   `eraseControl (denoteR root e p)` with `rHandler` gives
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
their distinct `onExit` and `onSuccess` markers, while the erased runs agree:
the same yield first, and once the yield answers the void value the same
cleanup, stores and exit (`afterYield`). Since P3 (2026-09-07) the yield's
continuation passes its answer on, as `Prim.yieldNowWith` resumes with the void
value, so the erased trees are no longer literally equal — the `onExit` side
restores the answered exit, the `bind` side the unit its cleanup returns — and
the former `rfl` pin is the run comparison. This is the contract repair prompted
by the reference machine running cleanup after interruption only in the first
program. The store observer now erases control markers explicitly; separate raw
probes confirm that erasure retains yield, other fiber operations and live
frontiers.

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


D5 construction-data amendment (2026-09-06): the point also captures completed
fiber exits as first-order data. `Point.awaitExit` is shared by the compiler,
`inlineYield`, and `denoteR`: a join/await of a target already exited in that
captured view is a pure exit; otherwise it remains the existing runtime await
operation. An eager `exit` or generator head must see that same classification.
Eager child points retain the view. Refreshing source callbacks is a separate
runtime obligation of this repair; a fixed-view denotation is not a theorem
about arbitrary host construction timing.

Source-repairs §20 amendment (2026-09-07): a `forkScoped` node denotes as the
counted `Scope` service read (`FiberOp.ambientScope`, under the wrapper's
`onSuccess` guard) bound to `forkIn` on the handle it answers; the store observer
sees the read first and, answered with a handle, the `forkIn` of the child at the
node's options keyed by the point's fuel (`DenoteRContract` `scopedFork`,
`replyScope`). `inlineYield_eq_headExit` keeps its statement: neither compile
shape of a `withFiber` node is an immediate exit.
