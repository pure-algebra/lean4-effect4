# Close the pending-waiter handshake

Base: `0f1f878bb21201e52740577c46327b63e7cebc5a`. The owner authorized independent
proof work while Claude handles M5/M6 and seat L handles layer construction.
The two production files below are unchanged between this base and Claude's
observed `c719c255` head. No operational definition or frozen proposition changes.

The target is `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`:
on the existing raw `Guard.Reachable` decision-prefix domain, each pending waiter
and each matching fiber occurrence either has the same parked token or its resume
is inert for every answer and command budget. Inertness observes exits and stores;
it is not a claim about trace equality, consumption, answer typing, ownership,
progress or fairness. There is no non-stuck or sufficient-fuel premise.

Proof graph: reachable fork-ledger invariant -> unique fiber IDs -> membership
agrees with lookup -> a mismatching resume leaves the machine unchanged ->
`ParkHandshake` -> the existing `.checked` ledger witness. The generic middle
facts belong beside `Inert` and `ParkHandshake`; the reachability connector stays
downstream in `Guard/Handshake.lean`. No new representation or trust exception.

Edit fence: `Laws/Machine/Handshake.lean`, `Laws/Program/Guard/Handshake.lean`,
`Test/Program/ParkHandshake.lean`; one Test/All import immediately after
`Test.Program.GuardFoldLift`; this plan and the receipt. Claude's Assembly,
Finish, scheduler, registry, generated reports and seat L's files stay untouched.

Done means: unchanged target statement; a checked ledger marker replaces wanted;
narrow builds and direct dependent checks pass; tests cover active and stale
guards, stuck states and zero budgets, and exhibit why duplicate IDs cannot be
dropped from the generic bridge; printed axiom footprints stay within
`[propext, Quot.sound]`. Record exact commands, source pin and remaining scope.
The named ledger target is the current consumer; no later theorem body is claimed
to use the handshake yet. Broader report regeneration belongs to integration.
