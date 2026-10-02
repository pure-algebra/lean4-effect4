# Pending-waiter handshake receipt

Before integration: this closes the existing literal M4 guard-or-inert goal,
without changing its statement. The current selected semantics report does not
list this goal; a later selection should link its checked witness and regenerate
on the merged head. The existing obligation ledger already records it. Pending ownership, captured
batches, due-work typing, progress and fairness remain separate. No execution or
compiler-lowering result follows from this proof.

Base: `0f1f878bb21201e52740577c46327b63e7cebc5a`.
Branch: `codex/park-handshake`, independent worktree
`/Users/pooks/.codex/worktrees/park-handshake/lean4-effect4`.
The containing commit is the proof head. No push or integration merge.

The owner authorized independent proof work while Claude and seat L continue
M5/M6 and layer work. The two production files are unchanged between the base
and Claude's subsequently inspected `9a2b76511f01f388d3865917c2a3b9b81fbd7c04`.
No Claude, Gemini or seat L file was edited. The sole shared-root edit is the
test import immediately after `Test.Program.GuardFoldLift` in `Test/All.lean`.

## What was proved

`Effect4.Program.Guard.M4Handshake.parkHandshake_reachable.checked` validates the
existing goal using `parkHandshake_of_reachable`. The pending-waiter projection,
`Inert`, `ParkHandshake` and the full original obligation declaration were
byte-compared against the base and are unchanged. No admission, non-stuck,
answer-type or sufficient-fuel premise was added.

The proof uses existing facts in this order:

1. `ForkLedger.Invariant.Native.reachable_corresponding` gives unique fiber IDs
   for every existing `Guard.Reachable` state.
2. `fiber_lookup_of_mem_nodup` connects an arbitrary member with the operational
   first-match lookup.
3. `drive_resume_unchanged_of_lookup_not_guard` proves equality of the whole
   machine for a mismatching token, for every budget and answer code.
4. `inert_of_lookup_not_guard` specializes that equality to the existing
   observation of fiber exits and stores.
5. `parkHandshake_of_fiberIds_nodup` supplies the literal guard-or-inert
   disjunction; the native witness obtains its uniqueness premise from step 1.

The existing ledger is the current consumer. No later theorem body is claimed
to depend on this newly closed goal. The stronger generic equality concerns a
single resume command; it does not extend the observation promised by M4.

## Checks and controls

All final commands exited 0 under Lean `v4.33.1`, warnings as errors, one compiler
thread, 6144 MiB compiler bound and 180-second process-group timeout:

- `lake build Effect4.Laws.Program.Guard.Handshake Test.Program.ParkHandshake`:
  three changed modules compiled; other dependencies replayed. The ledger prints
  `M4Handshake: 0 open, 1 proved, 1 total; ceiling 0`.
- `lake build Effect4.Laws`: its directly importing root rebuilt successfully.
  This is not a whole `Test` battery or trust-gate sweep.
- `lake env lean -j1 -M6144 -DwarningAsError=true Test/Program/ParkHandshake.lean`:
  matching guard, arbitrary-budget stale/unparked resumes, zero budget and stuck
  machine controls pass. A concrete duplicate-ID state changes observation on
  resume and fails `ParkHandshake`, showing why membership cannot replace lookup
  without uniqueness. That state is not claimed reachable.
- The printed footprints of the generic bridge, checked witness and test
  theorems use only `[propext, Quot.sound]`. The final witness's transitive
  footprint covers the private list helper and the existing reachability proof.
- The existing semantics check's artifact verifier was reused with only the
  `Effect4.Laws` and `Test.Program.ParkHandshake` targets. A no-build, no-cache,
  rehash preparation check passed, and resolved imported artifacts matched their
  saved output hashes. The verifier version, hashes and source fingerprints are
  retained in `handshake-artifacts.json`. Verification was repeated once to
  retain that detail separately from the command wrapper's receipt.
- `git diff --check`; independent source review found no changed contract or
  added premise. Earlier three elaboration/linter failures are retained as
  failures; no warning was suppressed to obtain the passing result.

No generator, installation, TypeScript compiler, operational definition, trust
exception or representation change was involved.

Changed paths: `src/Effect4/Laws/Machine/Handshake.lean`,
`src/Effect4/Laws/Program/Guard/Handshake.lean`,
`Test/Program/ParkHandshake.lean`, `Test/All.lean`, this receipt and the plan.

Exact commands, full logs, unchanged-contract hashes and prepared-artifact
verification are retained at
`/private/tmp/codex-second-eyes-2026-10-01/proof-graph-book/`:
`handshake-build-4.{log,json}`, `handshake-dependents.{log,json}`,
`handshake-test.{log,json}`, `handshake-frozen-contracts.json`,
`handshake-freshness.json`, `handshake-artifacts.json` and `handshake-freshness.py`.
