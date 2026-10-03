# R3/R4 implementation and contract correction

Status: finished and paused before R5. Full gate and forced census drift check
pass; the owner commits. Base and HEAD remain `c462cd1`, with unstaged work.

Base `c462cd1`, clean tracked tree at entry. The owner requested R3 and R4
together and approved the control-boundary correction during this run.

The existing worksheet owns the R3/R4 plan. This record owns the new finding
and its implementation receipt; `Test/contracts/program-runtime-r.contract.md`
will own the resulting runtime contract.

## Checked correction before implementation

`probes/p14_r3_cleanup_collision.lean` checked against the base with
`LEAN_NUM_THREADS=3 lake env lean -M 3072` (exit 0). `denoteR` assigned
definitionally equal terms to `onExit(yield, cleanupUnit)` and
`bind(yield, cleanupUnit)`. On the same evaluate/interrupt tape the reference
machine left one newly allocated Ref for the first and no Ref for the second.
Therefore the old term alone could not determine the required interrupted
observation. This is an information loss, not an evaluator proof gap.

The owner approved retaining handler/cleanup boundaries and replacing literal
straight-term equality with equality after erasing the control markers.
`Eff` remains canonical syntax, `RProgram` the existing semantic carrier.
`guard_ kind` carries first-order control data. Its `none` answer enters the
body; its `some exit` branch retains the continuation outside the boundary.
`unguard exit` exits a body through that saved continuation. `finishFinalizer`
ends the cleanup mask before the enclosing continuation executes. An erasure
handler answers the normal branches and leaves every store/fiber/frontier
operation intact. The theorem is about that explicit erasure.

## Dependency graph and acceptance

R1 body/control signature -> corrected R2 denotation and erasure equations ->
R3 direct store-shape denotations and term saved state/interpreter -> R4 local
evaluator -> existing generic loop/replay/observation. No duplicate loop or
general translation of named stored primitive programs is introduced.

The saved state must retain operation continuations as well as mask and async
cleanup frames. The scout's two-constructor stack only checked elaboration;
it could not resume a bound async operation. Continuations belong to the
existing higher-order semantic carrier, not stored source syntax.

Acceptance: structural equations, dependency receipts, finite runs against
the reference machine on identical decision tapes, unanswerable frontiers,
all test imports, full build at the existing trust ceiling, census drift
check. R5 and the general simulation are not asserted by R3/R4. Automatic
yield counts and step-for-step alignment require that later relation; finite
comparisons are not a proof for every scheduler context.

Reference battery: 75 guards across 14 families in
`probes/p15_r3_reference_cases.lean`, checked at budget 120 before the
implementation, then promoted to `Test/Program/RuntimeRReference.lean` with
those expectations unchanged. The neighboring probe markdown is historical.

## Implemented surface

- `Program/Sched.lean`: the three-constructor `Body`, continuation-slot kinds,
  entry/exit/cleanup-end operations and their dependent answers.
- `Program/DenoteR.lean`: retained control boundaries; erasure and its laws;
  the amended straight restriction and store-meaning corollary, under the
  same two depth hypotheses. Source-head classification remains unchanged.
- `Program/InterpR.lean`: five-field saved state, answer continuations, masks
  and cleanup frames; the core instance; direct finalizer, completion, close,
  race-settle and cancel shapes; the interpreter.
- `Program/EvaluateR.lean`: local term evaluation, saved-slot delivery and the
  evaluator instance. Every loop, observer, decision and dispatcher remains
  the existing generic machine code. Stateful sync keeps `answered`/`deliver`.
- `Program/RuntimeR.lean`: loader, replay, observations, sufficiency, behavior
  and the equations that pin the instance, including sufficient-command-budget
  independence with code/unfolding fuel fixed.

The scout was corrected in three further places. The saved stack must retain
answer continuations, not only mask/cancel data. The evaluator must use the
interpreter's addressed `.body` hook, because its global instance receives
the interpreter rather than a root expression argument. `Stores.progOf` has
compound alternatives beyond the six cited atomic cases; the implemented
direct shapes cover those this source/Completion profile actually synthesizes.
The decoder leaves arbitrary inserted store code at an unsupported frontier.

## Finite comparisons and the terminal-mask finding

`RuntimeRContract` has 32 complete comparisons at the original budget 120,
plus compile-zero checks and explicit terminal-mask pins (39 guards total).
Each comparison reads every exit and full store, replay outcome, all fibers'
parking/cause/deferred/context fields, allocation counters, and masks while
fibers are live. All these comparisons pass. Reference expectations remain
in their own 75-guard battery.

The initial eight disagreements were exclusively the mask bit after exit.
`Machine/Fibers.lean:963-964` discards the final pop state on
`FrameStep.finished`; the term evaluator retains it. Two cases pin false in
the reference and true in the term state. No exit, store or live-mask
expectation was changed. This is `E4-RTERM-CE-005` /
`RSTEP-FB-TERMINAL-MASK`, not whole-record equality or an implementation
repair. The fixed `Obs` excludes saved masks.

`RuntimeRShapesContract` has 32 guards: direct store-program shapes and
failure accounting; a 28-source fixture list covering straight handlers,
generators, branches, loops and malformed inputs; handler skipping across
masks; and the completing-sync interruption case. In that last case a resumed
waiter interrupts the completing parent, which skips Ref 99 and still creates
Ref 9 in cleanup. Both machines are checked against that literal expectation.

The two R1/R2 batteries have 81 guards; their reports have 49 receipts.
The runtime report has 37 receipts. Every inspected new receipt is empty,
`[propext]`, or `[propext, Quot.sound]`. These are finite executions and
declaration dependency receipts, not a universal frame/term simulation.

## Final verification receipt

All commands used the single `.lake/LANE.lock`, released on exit. No other
Lean driver was run concurrently. The reference/proof seat never staged,
committed or edited coordinator-owned root imports.

| command | result | log |
| --- | --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.SchedContract Test.Program.SchedAxiomReport Test.Program.DenoteRContract Test.Program.DenoteRAxiomReport` | passed, 34 jobs; 81 guards, 49 receipts, ceiling unchanged | `/private/tmp/effect4-r2-erasure-tests.log` |
| `LEAN_NUM_THREADS=3 lake build Test.Program.RuntimeRReference Test.Program.RuntimeRContract Test.Program.RuntimeRAxiomReport` | passed, 108 jobs; reference expectations unchanged; all new runtime dependencies within the ceiling | `/private/tmp/effect4-r3-runtime-contract.log` |
| `LEAN_NUM_THREADS=3 lake build Test.Program.RuntimeRShapesContract` | passed, 107 jobs, including the due-interruption cleanup case | `/private/tmp/effect4-r3-r4-shapes.log` |
| `LEAN_NUM_THREADS=3 lake build Effect4 Test` | passed, 282 jobs; gate checked 276 modules / 38,771 declarations; semantic/test `[propext, Quot.sound]`; unchanged implementation boundary of 7 modules / 41 exact declarations | `/private/tmp/effect4-r3-r4-full-gate.log` |
| `LEAN_NUM_THREADS=3 scripts/check-effect-runtime-census.sh --force` | passed; census source, ids, kinds, statement snapshots and witness join are current | `/private/tmp/effect4-r3-r4-census.log` |
| `git diff --check` | passed | no whitespace errors |

No compiler, reference-machine, store, public `Api`, generated file, lake
configuration or axiom allowance was changed. Root imports join all new
library/test modules; `docs/ARCHITECTURE.md` identifies their owner. Packets
and register rows record the changed denotation contract and named limits.

Remaining: R5's straight runtime theorem, general `CodeMeans`/`FrameMeans`/
`Sim` and its cost accounting, and any external host connection. In particular
the old strategy's raw straight-term equality, two-slot stack, `c = 2` sync
argument and equality of all terminal saved flags must not be reused. The
worksheets and strategy now point to the current contracts. No push or commit
was made, and no further lane is running.
