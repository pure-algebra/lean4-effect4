# Shared place funding pilot

The pilot compiles; the existing command proof is not replaced yet.
The original Atomic log debit remains open.

## Placement

Concept: scope-lifetime-finalization, R11.
Question: the shared funding structure serves Atomic.Cleanup.log_debits.
Reach: actual keyed replacement, store writes, trace issuance, existing paths, and owner installation.
The two instances read saved stacks, or Atomic active code and heap counts.
The pilot establishes no whole-history debit or source permission.
The next consumer replaces the existing stack-only command proof once.

## Source

Base: 13dcf111c9bd4a7bd0efe777b09ef2e3636264ee.
The files remain research probes.
They add no production module, planned goal, or original statement change.

Control uses the existing fiber identity, current code, saved code, and operation counter.
Metadata retains identity and code; its counter may decrease.
Imported resume and race code require actual source permission.
The saved-stack instance requires no restriction on imported code.
The Atomic instance requires zero active weight for imported code.

Store hooks retain their actual successful-write premises.
Atomic discharges them through the existing reference footprint laws.
Administrative event bounds read the existing Moves.administrative classification.
The first pilot explicitly assigns zero weight to races, commands, and detached tasks.
The external allowance composes additively; both current instances use zero.

The finite control excludes a raw note writer from TerminalReply.
It does not refute a whole-run funding claim.

## Checks

Commands run in the machine-fields worktree with LEAN_NUM_THREADS=3.

```sh
lake build Test.Dogfood.Scenario.Atomic.WriterMachine Effect4.Laws.Program.LedgerRun
lake env lean -DwarningAsError=true --root=/private/tmp -o /private/tmp/MachinePlaceFundingPilot.olean /private/tmp/MachinePlaceFundingPilot.lean
lake env lean -DwarningAsError=true --root=/private/tmp -o /private/tmp/MachinePlaceControl.olean /private/tmp/MachinePlaceControl.lean
```

The dependency build passes 1151 jobs.
Both probes pass with warnings treated as errors.
The audit imports their compiled modules through LEAN_PATH=/private/tmp:$LEAN_PATH.
It passes 80 declarations within [propext, Quot.sound], with zero planned goals or declarations modulo goals.

## Remaining work

Replace the existing stack command proof with one shared command fold.
Discharge Atomic permissions from actual ConfigurationAt and CommandsAt.
Compose actual native debit, forced yield, commands, and admitted replies.
Discharge initial funding and consume it in the unchanged Atomic log debit.
The current files do not claim those results.
