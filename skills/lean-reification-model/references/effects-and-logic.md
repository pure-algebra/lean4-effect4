# Effects, state, and logic

## The information contract of failure

Work out the result shape before proving cleanup laws. Compare a computation
that returns either an error or a value/state pair with one that always returns
state alongside either an error or a value. In the first shape, an error
discards the final state; in the second, it remains available. Transformer
order can select these different meanings.

Consider a body that registers a release action, changes state, and fails.
If all failing executions collapse to the same error value, a later finalizer
cannot recover which registration or state change happened. A proof tactic
cannot reconstruct information the carrier lost. Preserve the needed state,
provide an explicit trace from which to reconstruct it, or narrow the contract
through the proper decision process. Do not hide an accidental rollback.

Ordinary failure-short-circuiting bind also skips its suffix. A finalizer
attached as that suffix does not run on failure. Model the exit-aware cleanup
operation, including original and cleanup failures, registration order,
interruption, and exactly-once conditions actually promised.

A target able to implement catch may still be unable to implement finalization.
Typechecking a handler shows that it has the requested type, not that its target
retains the observations needed for the handler laws. A parameterized finalizer
oracle is an assumption; its law is not a proof of the host finalizer runtime.

## Sequencing carries history

A suffix can refer to values produced before it. Its meaning must receive the
prefix-produced environment/history, along with state and any relevant resource
context. Re-running the suffix from an empty environment changes the program.
For table languages, concatenation need not be monadic bind: an empty table may
be invalid even when `return` is valid in a separate proof carrier.

Use the existing project's composition theorem with all its premises. A
sequencing law about successful total runs, a partial-correctness law, and a
fixed-fuel runner equation are different obligations. The Foldlab examples
and local EffHOL specialization are recorded in
[the adaptation boundary](../../lean-reification/references/effhol.md).

## Choices and observations

List all decision sources before claiming determinism: operation answers,
scheduler selection, wake-up order, race ties, interrupts, clock reads, and
foreign responses as applicable. Separate enabled moves from the move a
policy or tape selects. If replay needs reproducibility, record the compatible
decisions and environmental inputs that determine the run.

An all-runs safety property, a possible successful run, and progress on every
fair run have different quantifiers. Do not obtain liveness by testing many
schedules or by selecting a favorable default scheduler. A finalizer that can
wait forever also needs assumptions for an eventual-release claim.

Observe losses deliberately. If a runtime represents only a flat collection
of causes, an ordered internal failure tree needs an explicit quotient or a
different target. Equality after that quotient proves nothing about the
discarded topology. Similarly, a state-summary model of parallel cleanup need
not model the interleaving of cleanup effects.

## Program logic

Define what a postcondition can see. Does it inspect only successful results,
all exits, final state, a trace, or an infinite behavior? Does a failed run
satisfy a success-only liberal condition vacuously? Does the total condition
require successful termination, any termination, or a declared allowed exit?

Choose universal or existential treatment of unresolved choices. Then state
return, sequencing, monotonicity, and the permitted reduction rules for that
choice. A decomposition into a liberal condition and totality must use the
same observation and outcome conventions on both sides. Read the exact
EffHOL adaptation record rather than deriving meaning from familiar symbols.
