# W3 and R2 continuation

Base and current HEAD at entry: `c080063`. The owner resumed W3 and R2 with a
two-seat cap. The valid-input premise for W3 was already settled. The earlier
pause is historical. Commits remain the owner's responsibility under the
dispatch brief; neither seat stages, commits or pushes.

Final status: **W3 and corrected R2 are verified; paused before R3**. Base and
HEAD are both `c080063ba2f0075908057006fad4de4205cdd515`. The whole-tree gate,
forced runtime-census drift gate and diff whitespace check pass. Changes remain
unstaged and uncommitted for the owner.

## Finish criteria

W3: restore the parked files, repair the two proof sites without changing the
invariant or interpreter contract, audit excluded positions against their
runtime reads, retain adversarial batteries, wire all modules, and pass the
whole-tree gate at the existing axiom ceiling.

R2: amend the fiber answer family, check the proposed statements before
implementing the denotation, and record meaning changes with their witnesses.
The owner answered "Yes make the correction" to the concrete contract changes;
the authorized amendment below is now implemented and verified. R3 and the
simulation remain outside scope.

## Evidence already observed

The initial `LEAN_NUM_THREADS=3 lake build Effect4 Test` passed: 268 jobs,
262 modules / 35,224 declarations, ceiling `[propext, Quot.sound]`.
Log: `/private/tmp/effect4-w3-r2-baseline.log`.

The agreed dependent answer amendment passes the narrow build:
`LEAN_NUM_THREADS=3 lake build Effect4.Program.Sched Test.Program.SchedContract
Test.Program.SchedAxiomReport` (30 jobs). The store lift keeps its statement;
its axiom receipt remains `[propext, Quot.sound]`. Log:
`/private/tmp/effect4-r2-signature.log`. Later battery additions require a fresh run.

## R2 findings against the current source

1. The scout's alleged `reifyExitVal` collision is false. `Stores.lean` wraps
   successes in `Val.exitOk` and failures in `Val.exitErr`.
   `Test.Program.SchedContract.exit_encoding_distinguishes` and
   `exit_encoding_roundtrip` are checked universal proofs. The dependent answer
   amendment is retained as the requested direct exit interface, with its
   rationale corrected. Counterexample row: `E4-SCHED-CE-002`.
2. The proposed zero arm, `pure outsideExit`, contradicts the standing frontier
   rule. `Compile.frontier` is a suspension; neither exhausted fuel nor an
   unanswered choice is a failed exit. The proposed unrestricted
   `denoteR_straight` also fails at zero on `pSucceed`. Its checked witness is
   retained in `SchedContract`, row `E4-SCHED-CE-003`.
3. Compile fuel and a recursive unrolling budget are different quantities.
   `choose` extends the path and consumes one Boolean but keeps `Point.fuel`.
   `whileLoop` reuses its loop point across iterations. The generator resets
   its statement-walk budget from the saved point after a non-inline yield.
   Decreasing all these quantities together changes where execution stops.
4. The scout's direct exit-answer list is insufficient for a direct failure
   continuation: async completion can be a failure, and `forkScoped` fails
   when the ambient scope is absent. These require exit answers (or a separate
   explicit failure continuation). Ordinary `awaitAllFailFast` still returns
   its collected exit values; its name alone does not change the answer type.
5. The signature lacks `closeScope`, despite the existing machine arm. A scoped
   operation also needs the allocated scope id; `scoped bodyPoint` alone loses
   the result of `scopeMake`. `forkIn` needs the actual link key (`p.fuel`) as
   well as the child point and scope id. It cannot in general recover that key
   from a twice-decremented child point.

## R2 amendment — authorized by the owner

Keep `Eff` as the sole stored program representation and `Effects.Program` as
the semantic carrier. Keep `Point`, generator program counters, and cursor
values as data. Do not derive the denotation by interpreting compiled `Prim`.

Add a named frontier operation to `FiberOp`, with a first-order resume address
that can retain a program point, generator point/program counter/environment,
or loop point/cursor. The later term scheduler must leave this operation
unfinished when its missing fuel or choice has not been supplied. No frontier
is emitted as `pure (failure _)`. The placeholder handler remains explicitly
outside the fiber semantics.

Use a leading structural unrolling budget and retain compile fuel in `Point`.
The new denotation is a bounded unfolding; exhausting its own budget records
the residual address. The straight-line theorem requires both budgets to
cover `Agreement.depth e`; under the scout's `p.fuel = n`, this reduces to the
additional premise `Agreement.depth e ≤ n`. A general simulation at matching
decision tapes remains a later obligation; R2 must not claim it.

Extend the direct exit-answer family to async, scoped forks and scope close.
Carry the allocated scope id in the scoped operation and the link key in
`forkIn`. Retain `Val` for operations that actually deliver values, and `ExitV`
for body/winner/effect-join results. Update packet claim 2 and its shape tests
together.

The generator subdesign must distinguish inline yielded successes from
effects that merely have a pure denotation (notably `sync`). It must retain
`blockExit`/`loopExit`'s environment truncation, reset the statement-walk budget
at resumed yields, retain the advanced program counter, and stop at live
frontiers. Tests must cover nested branch scope, `breakLoop`, both kinds of
yield, failure, and exhaustion. The exact local equations are frozen before
their proof bodies are written.

Dependencies: corrected signature → frontier/resume carrier and arm equations
→ structural denotation → straight-line restriction → store interpretation
corollary. The term scheduler, machine simulation, host conformance and any
coverage increase remain outside this continuation.

## W3 review findings

The parked packet and native module header incorrectly said the accepted race
exit and live entrants were excluded. `Race.keys` already collects both, and
`fireObserver` passes both to `raceSettle`. The W3 seat is correcting the prose
and adding guards for dangling handles in those positions. The invariant and
theorem are unchanged. The excluded duplicate race winner and Deferred waiter
targets are now explicitly tested as exclusions, not described as validated
handles.

## Final verification and delivered obligations

| Command | Result | Log |
| --- | --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Machine.Runtime.HandlesAxiomReport` | Passed, 104 jobs; 68 guards and 23 explicit dependency receipts | `/private/tmp/effect4-w3-receipts.log` |
| `LEAN_NUM_THREADS=3 lake build Effect4.Program.DenoteR Test.Program.DenoteRContract Test.Program.DenoteRAxiomReport` | Passed, 32 jobs; 47 new finite guards and the universal statements below | `/private/tmp/effect4-r2-axioms.log` |
| `LEAN_NUM_THREADS=3 lake build Effect4 Test` | Passed, 275 jobs; all new modules reachable; 269 modules / 38,328 declarations audited | `/private/tmp/effect4-w3-r2-full-gate.log` |
| `LEAN_NUM_THREADS=3 scripts/check-effect-runtime-census.sh --force` | Passed; regenerated census and witness join agree | `/private/tmp/effect4-w3-r2-census.log` |
| `git diff --check` | Passed | Checked in the working tree |

Final gate tail:

```text
Effect4 module and axiom gate: checked 269 modules and 38328 declarations;
semantic/test axioms are [propext, Quot.sound]; exact implementation boundary
(7 module(s), 41 declaration(s)) additionally allows Classical.choice
Build completed successfully (275 jobs).
```

The existing implementation exceptions were not edited. A first R2 dependency
report caught `Classical.choice` in the zero-budget proof: `omega` had been
asked to close a program equality from contradictory arithmetic premises.
Proving `False` first and eliminating it removed that dependency; the exact
statement was unchanged. The final receipts are:

```text
'Effect4.Program.handles_minted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.inlineYield_eq_headExit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.denoteR_straight' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.meaning_denoteR_straight' depends on axioms: [propext, Quot.sound]
```

W3 closes C13 with its original collected-handle invariant, hook contract and
valid-answer premise. `load_minted` and `interpOf_keyBounded` connect the generic
frame-machine theorem to `Api.replay`. The restored native proof required more
repairs than the two originally visible machine errors; its complete history,
exclusion audit and checked interruption annotation are in
`2026-09-06-handles-repair.md`. No compiler, scheduler, store or API runtime
definition was changed for W3.

R2 exports `FrontierReason`, `ResumePoint`, the amended `FiberOp.answer`,
`pending`, `denoteAction`, `denoteAsync`, `inlineYield`, `denoteR`, `denoteGen`,
`denoteYield` and `denoteLoop`. Its checked arm equations are `denoteR_zero`,
`denoteR_compile_zero`, `denoteR_bind`, `denoteR_branch`, `denoteR_choose`,
`denoteR_withFiber`, `denoteR_gen` and `denoteR_whileLoop`.

The universal classifier equation is
`inlineYield e p = headExit (compileEff e p)`. The universal straight restriction
and its store interpretation corollary require `Straight e = true`,
`Agreement.depth e ≤ n` and `Agreement.depth e ≤ p.fuel`. The generator/loop,
scope, fork, async and address comparisons in the battery are finite probes;
they are not a general scheduler simulation.

## Changed files and pause boundary

New library modules: `src/Effect4/Machine/Handles.lean`,
`src/Effect4/Program/Handles.lean`, `src/Effect4/Program/DenoteR.lean`.
Amended library module: `src/Effect4/Program/Sched.lean`.

New batteries/reports: `Test/Machine/Runtime/HandlesContract.lean`,
`Test/Machine/Runtime/HandlesAxiomReport.lean`,
`Test/Program/DenoteRContract.lean`, `Test/Program/DenoteRAxiomReport.lean`.
Amended batteries/reports: `Test/Program/SchedContract.lean` and
`Test/Program/SchedAxiomReport.lean`.

New packets: `Test/contracts/machine-handles.contract.md` and
`Test/contracts/program-denote-r.contract.md`. Amended packet and register:
`Test/contracts/program-sched.contract.md`, `Test/Counterexamples/REGISTER.md`.
Root imports: `src/Effect4.lean`, `Test/All.lean`.

`git diff --stat` reports seven already-tracked files, 122 insertions and 27
deletions; the nine new files add 6,741 lines (including the restored W3 work).
Research records and `COORDINATION.md` are ignored working notes. The parked
W3 originals remain available. No generated file, axiom-gate allowance or
lake configuration was changed.

R3/R4 (the operational term scheduler), the general machine simulation and
host conformance remain open. In particular R2's placeholder handler gives
no fiber meaning, and its operation tree alone does not discharge the later
mask, finalization, cancellation or interruption obligations. No further lane
was started. The build lock was released after all checks.
