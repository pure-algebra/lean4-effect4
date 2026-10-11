# Actual host-prefix boundaries

Routing keeps its original statement. Its internal prefix helper now names the source and table fragment it requires.
The universal prefix connection remains open.

## Placement

Concept: translation-simulation, R6. Claim: `Run.CallTree.request_leads`, consumed by `Routing.unauthorized_calls_nothing`.
`SourceScope.ExternalOnly` uses the existing generated address census and excludes native operations.
`SourceScope.ConcreteReplies` requires closed answer and error columns in the actual row table.
Routing discharges both premises from its actual admitted build.

Concept: store-typing, R4. Claim: `cell-invariant-from-write-sites`.
`SourceScope.admitted_heap_history` extends the existing heap invariant across arbitrary actual host answers.
Its consumers are Routing's empty reference heap and hosted Queue cell assertions.
The proof reuses the existing source, cell, and history carriers.
These helpers establish neither progress nor an outside-host comparison.

## Checked boundaries

`E4-HOST-CE-011` retains an actual admitted delayed cell read.
Its journal contains no submitted exit, while its second external request contains the cell's value.
`E4-HOST-CE-012` retains an actual admitted specialized generic reply.
The session accepts the checked call instance, while the table-only tree refuses the same reply.
Both controls prove actual reachability and refute the former helper conclusion.
Neither control changes an original scenario statement.

## Landing

Base: `133d02642`.
Changed source modules: `Program.NativeHeapReplies`, `Program.HostSource`, `Run.CallTree`, `Routing.Calls`, and `Routing`.
Both controls join `Test.All` and the counterexample register.
The compiled alternative `ScopeSequentialAlternative.lean` remains research evidence only.
The landed source-strategy proof already carries that fact, so the alternative adds no library module.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Routing Test.Counterexamples.Machine.Runtime.HostRefPrefix Test.Counterexamples.Machine.Runtime.HostInstancePrefix Effect4.Laws`.
Result: successful; exact output is `HostSourceIntegrationBuild.log`.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/HostSourceAudit.lean`.
The new helpers and controls audit 740 declarations, with no planned dependencies.
The Routing chain audits 104 declarations, five modulo declarations, and one planned goal.
The exact output is `HostSourceAudit.out`.

The integrated source-strategy audit checks 1094 declarations with no planned dependencies.
`SequentialIntegrationAudit.out` retains that independent check.
The alternative's exact build output remains in `ScopeSequentialAlternativeBuild.out`.

## Remaining work

`CallTree.request_leads` still owes the actual session-to-tree connection under the repaired internal premises.
Whole-history custody, source uniqueness, application stages, and timeout history remain open.
No runtime definition changes; the prior behavior receipt still describes those gates.
The final generated proof graph refresh remains due.
