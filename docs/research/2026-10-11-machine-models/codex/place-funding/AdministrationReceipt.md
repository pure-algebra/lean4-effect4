# Actual administrative callback premises

The two new callback premises now name the callbacks produced by actual commands.
All existing saved-stack theorem statements remain unchanged.

## Placement

1. Concept: scope-lifetime-finalization, requirement R11.
2. Question: this refinement serves Atomic.Cleanup.log_debits through PlaceFunding.command_funded.
   The unrestricted StackLedger.command_funded remains the first complete instance.
3. Reach: race registration pushes its actual cancel callback.
   Parallel-scope completion pushes its actual close callback and void cursor.
   The concrete Atomic instance checks these producers against its active note reservation.
4. Limits: the instance proves these local administrative premises only.
   It does not prove Atomic's evaluator, initial funding, or admitted-history log bound.
5. Unlock: discharge command assumptions without authorizing arbitrary note-bearing callbacks.

## Changed premises

Administration.cancel previously quantified over every callback name.
It now names cancelName applied to raceCancelName, the acting fiber identifier, and the actual token.
Administration.iterator previously quantified over every callback and cursor.
It now names closeDoneName and voidValue.
Commands reads those actual premises in its existing command proof.
LedgerRun projects the original universal Kept fields to those instances.

The finite control gives an arbitrary stored note callback one reservation.
Pushing it onto an empty Atomic frame increases the reservation from zero to one.
The control rejects the old broad new premise.
It does not reject any original command or history claim.

## Scope and measurement

Base: b20315515.
Three production files change: PlaceFunding.Control, PlaceFunding.Commands, and LedgerRun.
The source diff adds ten lines and removes six lines.
The 128 previously compared named headers remain unchanged.
No runtime, original scenario statement, root import, or source permission changes.

## Checks

The affected command fold, saved-stack consumer, and Atomic writer imports pass 1156 build jobs.
The concrete Atomic administrative instance and terminal-reply reading are checked privately.
The retained control is finite evidence about the broad new premise.
The production reader and eight-module audit are rerun before this refinement lands.

Source head: ca3032357.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.PlaceFunding.Commands Effect4.Laws.Program.LedgerFinalizer Test.Dogfood.Scenario.Atomic.WriterMachine
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachinePlacePromotionReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachinePlacePromotionAudit.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --root=/private/tmp -o /private/tmp/MachineAtomicAdministration.olean /private/tmp/MachineAtomicAdministration.lean
LEAN_PATH=/private/tmp:$LEAN_PATH LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachineAtomicAdministrationAudit.lean
```

The production audit passes 537 declarations within [propext, Quot.sound], with zero goals and zero modulo declarations.
The private instance audit passes 72 declarations at the same ceiling, with zero goals and zero modulo declarations.
Both reader logs contain no diagnostics.
The whitespace check passes.
The shared outer-history connector belongs to the coordinator's next slice.
