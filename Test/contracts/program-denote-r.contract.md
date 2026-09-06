# Program denotation over stores and fibers

Status: FROZEN / GREEN in the working tree. The owner authorized the corrections
on 2026-09-06 after the scout's claims were checked against `c080063`.
Design and evidence: `docs/research/2026-09-06-w3-r2-continuation.md`.

Implementation: `src/Effect4/Program/DenoteR.lean`, with the answer and frontier
amendments in `src/Effect4/Program/Sched.lean`. Tests and dependency receipts:
`Test/Program/DenoteRContract.lean`, `Test/Program/DenoteRAxiomReport.lean`, and
the existing scheduler signature battery. All five obligations below are proved.
The final whole-tree gate passed 275 jobs, 269 modules / 38,328 declarations
at the unchanged semantic/test ceiling `[propext, Quot.sound]`.

## Frozen corrected meaning

`denoteR root n e p : Effects.Program RSig ExitV` is a bounded unfolding of
`e` at `p`. `n` bounds the recursive unfolding, independently of the compile
budget `p.fuel`. The compiler's actual address and environment conventions
remain authoritative. `Eff` is the only stored program representation.

`pending reason resumeAt` is a visible frontier operation, never a pure exit.
Its data records whether compile fuel, unfolding fuel, a choice, or support
for a source form is missing. It also records the program point, generator
program counter/environment/scan budget, or loop cursor. The later scheduler
must not answer a frontier with a default exit. The existing placeholder
handler is outside this meaning.

Body, winner and effect-join operations answer with `ExitV`. Async, scoped
forks and scope close also answer with exits because their computations can
fail. Value operations retain `Val`. A scoped node carries the allocated
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
   positive compile fuel. Choice consumes a Boolean but not compile fuel.
3. `inlineYield_eq_headExit` agrees with the compiler's immediate exit head.
4. `denoteR_straight`: for all `root`, `e`, `n`, `p`, if `Straight e = true`,
   `Agreement.depth e ≤ n` and `Agreement.depth e ≤ p.fuel`, then
   `denoteR root n e p = Effects.Program.inl (denote e p.env)`.
   This replaces the draft's false unconditional fuel claim. In the scout's
   special case `p.fuel = n`, only the depth bound is added.
5. `meaning_denoteR_straight`: under the same premises, interpreting the
   unfolded program with `rHandler` gives `meaning e p.env stores`. This
   corollary applies only after the straight restriction eliminates all
   fiber operations.

## Falsifiers and boundary

Retain `E4-SCHED-CE-002` (the scout's encoding claim disproved) and
`E4-SCHED-CE-003` (zero-fuel failure and unrestricted straight agreement
disproved). Finite batteries cover both choices, branch paths, fork addresses
and link keys, scope ids, success-valued errors versus failures, async
decoding, store updates before a failure/finalizer, malformed terms, generator
scope exit and break, inline versus resumed yield budgets, and loop cursors.

`RDEN-FB-HANDLER`: `rHandler` is a placeholder on fibers and frontiers.
`RDEN-FB-SCHEDULER`: R2 constructs the operation tree. It does not implement
the later scheduler's mask, scope, interruption, cancellation or fairness
rules, or prove any general relation to machine execution. Those rules and
the general machine simulation remain R3 and later obligations. The
straight restriction is the only interpretation theorem here.
`RDEN-FB-UNSUPPORTED`: program-kind operations and acquisition/release remain
frontiers, as they are in `compileEff`; this packet adds no support for them.

Gate: all batteries reachable from `Test/All.lean`, whole-tree
`lake build Effect4 Test`, no new axiom allowances. Expected ceiling:
`[propext, Quot.sound]`. No host equivalence or coverage increase is claimed.
