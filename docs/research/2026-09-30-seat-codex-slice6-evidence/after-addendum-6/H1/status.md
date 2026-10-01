# H1: the revised step statement is refuted

Base: 57c93ba4. The temporary source candidate is retained in checked-source.patch and
checked-source/, with its exact hashes. It changes only the generated saved-code clause to
SavedPosition; stacks, interrupt provenance and all other data positions remain checked.
TerminalPosition recognizes a queued finish or published exit. QueueOk checks carried exits.
The full per-command boundary review is in candidate/README.md.

The original terminal witness is a positive control under this clause: terminal-2 passes,
with 28 axiom prints at [propext, Quot.sound] or less. It includes the historical refutation,
the revised input/output state and queue, the concrete successful delivery, and the published
exit saved-position boundary. This is a concrete control, not general command preservation.

queue-discard-2 also passes, with all 15 theorem prints at the ceiling. A root declared Unit
holds stale Nat 42 and is typed by its queued unit finish. A distinct worker has a typed
scope-exit callback for absent scope 0. The input TypedState and all nine QueueOk fields hold.
The worker's delivery halts with unknownScope(0); settle discards the entire queue. The root
is unchanged and has no published exit, so its terminal exemption disappears. For every
output world, the resulting state is untyped. Thus step_deliver_false proves the negation of
the revised StepPreserves statement. No reachable-program bug is claimed.

The retained failed runs are draft elaboration failures only: contract-1 record layout,
terminal-1 unfolding of expectOf, queue-discard-1 record layout/list simplification. The final
statements were not weakened to make their proofs pass. contract-2 builds all four candidate
modules; the 18 command obligations remain open, as does the reference code-site scan.

Original brief section 6 therefore stops H1. Do not mark CE-017, CE-018 or CE-019 repaired.
CE-019's positive control and new failure evidence are retained here for the coordinator.
The candidate is restored before continuing independent H2. No runtime amendment is applied.

Smallest requested ruling: specify how typed-state evidence survives global queue discard
when a fiber's type was carried by a pending finish. Decide the halted-state contract or retain
terminal-delivery evidence; the current queued/published-exit rule alone is insufficient.
A blanket halted-state exemption, runtime repair, reachability restriction or extra scope
protocol premise is a design amendment and was not silently added. H2's two-defect exclusion
does not by itself supply a scope-existence premise.

## Superseded stop

The subsequent owner instruction authorizes consistent resolution. See resolution/README.md,
resolved-source-1, final-direct, final-axioms, cases, and the top receipt for the landed
halt-aware current-code clause and exact existing dispatch premise. The original checked
refutation remains valid for its retained historical candidate.
