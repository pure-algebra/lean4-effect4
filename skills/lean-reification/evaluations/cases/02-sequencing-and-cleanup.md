# Case 02: sequencing and cleanup

Use `$lean-reification-model` and `$lean-reification-breaker` to review the
following proposal. Produce a written model review and concrete distinguishing
cases only; no proof implementation or repository changes are requested.

A table program is a list of instructions. Running an empty table from an
empty answer history refuses. A successful instruction appends its answer to
history. `use 0` returns the first answer, but refuses if there is no answer.
`emit 9` appends and returns 9. `emit 4` appends and returns 4. Concatenated
tables execute with a single carried history. Refusal stops execution.

The existing liberal condition means: every successful run's returned value
satisfies Q; refusal satisfies the condition for every Q. The existing total
condition additionally requires success. A shipped auxiliary sequencing
theorem carries history and has the premise “initial history is nonempty or
the prefix is nonempty.” There is no shipped public liberal-append theorem.

The proposal is to import EffHOL's sequencing rule as the equation
“liberal(prefix ++ suffix, Q) = liberal(prefix, then liberal(suffix, Q)),”
where the nested suffix starts with a fresh empty history. It is intended to
hold for all table prefixes, including empty ones. A separate new public
modality would hide any mismatch with the existing logic.

The same proposal represents stateful computations as a function from state to
either an error or a value/final-state pair. A body sets state to 5 and raises
`bad`. Another sets state to 8 and raises the same `bad`. The specified cleanup
increments the state left by the body once and preserves the original error.
The proposed implementation uses ordinary error-short-circuiting bind to
append cleanup. The author says the target already supports catching `bad`,
so the cleanup theorem should follow too.

What survives review, what fails, and what are the smallest justified changes
to the contract or representation? Distinguish paper results, local proof
obligations, and witnesses deduced from this packet.
