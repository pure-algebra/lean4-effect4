# Stored-program credit receipt

The formerly hidden finalizer credit now survives the actual stored-suspension command.
Whole-run custody preservation remains open.

Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the stored-suspension command clause of `Workers.Assertions.releases_step`.
Reach: every existing `ProgName`, selected actual fiber, supplied row table, and unchanged pending command suffix.
Limit: scope-entry uniqueness, other command clauses, and source ownership remain open.
Unlock: `Workers.Assertions.stored_suspend_custody_command` derives the release-debit assertion from actual credit transfer.

`MachineHiddenNameBefore.lean` checks the omitted `finalizerOf` credit at previous head `b8e5ba30`.
Its retained output checks both zero stored credit and nonzero interpreted credit when the source identity matches.
That source records earlier evidence; it does not compile against the extended projection.
`MachineHiddenName.lean` checks the corrected equation at the current projection.

`ReleaseCustody.Names.progCredits` follows every recursive program slot and every stored finalizer slot.
The continuation projection follows `seq` and `snapshotThen`.
The action projection follows forks, masking, and parallel close orders.
`Control.prog_of_credits` proves the exact interpretation equation for every stored program constructor.
`Control.stored_suspend_loop_funded` consumes that equation at the actual native command.
The existing lower callbacks retain their reservations.
The operation count, yield decision, row table, and pending suffix remain actual machine data.

The syntax has no executable `ProgName` fold in the current tree.
Lean rejects an executable use of its induction recursor.
Proposed traversal exemptions: `ReleaseCustody.Names.progCredits`, `contCredits`, and `actionCredits`.
Each projection follows the existing first-order syntax; no program carrier is introduced.
The coordinator owns the census registration.

Base: `b74ebab6f`.
Previous head: `b8e5ba30`.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Control` exits zero, with 344 jobs.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers.Assertions` exits zero, with 1065 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineHiddenName.lean` exits zero.
Its audit measures 627 declarations within `[propext, Quot.sound]`, with no planned goals.
The actual scenario reader exits zero; its audit measures 686 declarations, three planned goals, and two declarations modulo them.
The custody model exits zero; its audit measures 585 declarations, with no planned goals.
The selected one-job checks retain the same credit counts at parked and interrupted fuel cuts.
Those execution checks remain finite.
The original preservation goals remain unchanged.
The coordinator defers behavior gates until the major structures land.
No push occurs.
