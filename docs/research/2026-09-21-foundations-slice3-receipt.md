# Foundations slice 3 receipt

Merge note: slice 3 is proved and checked; the supplied fix for slice 4's interrupt
contract is refuted. Keep the dependent residual/stack landing held. The checked controls
and exact reopening are in `2026-09-21-foundations-contract-preflight-amendment.md`.

Base: `641a0feabe8ff7c3899396cd2144380d6d8cf53c`.
Statement checkpoint: `cd769650`.
Head: the commit carrying this receipt (`git log -1 --format=%H -- <this path>`).
Branch: `codex/foundations-slices-3-4`; worktree `/private/tmp/effect4-foundations-slices`.
Nothing pushed. The original checkout and the coordinator's decisions register are unchanged.

## Changes and proof scope

`Typed/Validity.lean` declares exact world/machine support, closed ghost columns, stored
column typing, live park coverage, historical token bounds, and the root declaration.
Freshness follows from those clauses for references, promises and the global token supply.
Reference completions declared by a valid world name live cells. `initialWorld` supplies
valid empty tables for any term with closed declared root columns. This is a data witness;
it does not assert that an arbitrary root is source-admitted or its code is typed.

`World.leHost` adds preservation of existing external spellings to the existing world order.
Value and completion transport use the existing universal `hasTy_mono`; C1 completion
transport needs only reference-table extension and spelling extension, so it can be used
when constructing CellCompatible without circularly assuming that whole order. Heap and
promise transport project CellCompatible. No global WF or whole-world monotonicity is
claimed. `WorldWanted.park_extension` is now proved without changing its statement.

`Test/Program/TypedWorldValidity.lean` checks initial validity, exact support/freshness,
unbounded tokens, dangling completions, changed external spellings, an invalid new cell,
coarse nested/open-type false positives, and a real Bool allocation preserving an old Nat
cell. The allocation uses the existing `refMake_extension` theorem and actual syncOpStep.
It is a store/world result; the M3a certificate-program settling case remains separate.

The preflight adds three counterexample IDs: `E4-SCHED-CE-006`, `E4-SCHED-CE-007`,
`E4-TYPED-CE-003`. Their witnesses refute the new input proposal, not a proved production
law. `Typed/Contracts.lean`, runtime semantics and generated representations are unchanged.
They are universal saved-state equations / a universal strong-value-parameter control;
no decision-tape reachability claim is made for the interrupt witnesses.

## Gates and verification

The statement checkpoint reports M2Validity: 15 open, 0 proved, ceiling 15.
Final M2Validity: 0 open, 15 proved, ceiling 0.
Final WorldWanted: 0 open, 20 proved, ceiling 0 (was 1 open).
All sixteen proof names and their transitive axioms are in `final-audit.log`.
They stay within `[propext, Quot.sound]`.

- `lake build Effect4.Laws.Program.Typed.World Effect4.Laws.Program.Typed.Validity Test.Program.TypedWorldValidity Test.Counterexamples.Machine.Semantics.InterruptDelivery Test.Counterexamples.Machine.Semantics.StrongExitDefect`: exit 0, 363 jobs.
- `lake build Test.Counterexamples.Machine.Semantics.InterruptDelivery`: exit 0, including the proposed catch premises and ordinary handler result.
- `make build`: exit 0, 696 jobs; the module/axiom audit checks 475 modules and 66923 declarations.
- `make check`: exit 0; fresh Test root and generated-byte drift checks pass.
- `lake env lean -DwarningAsError=true docs/research/2026-09-21-foundations-slice3-evidence/FinalAudit.lean`: exit 0.

The default build retains the pre-existing exact implementation exceptions; this slice
adds none. No make check-full or external OCaml, C, JavaScript execution claim is made.
Logs, source hashes and the audit driver are retained in `2026-09-21-foundations-slice3-evidence/`.

Unique production ledger: **324 total; 315 proved; 9 open**.

- `Effect4.Api.M1Origin.source_fork_site`
- `Effect4.Api.TraceFacts.M1Trace.step_agrees`
- `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
- `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
- `Effect4.Api.M1Origin.source_two_race_sites`
- `Effect4.Api.M1Origin.source_forkScoped_site`
- `Effect4.Api.M1Origin.source_race_site`
- `Effect4.Api.M1Origin.source_forkIn_site`
- `Effect4.Run.M1Trace.observe_replace_trace`

These nine are the pre-existing obligations after closing park_extension. The unimplemented
M3a residual/control design is listed explicitly in the brief and amendment; it is not
misrepresented as a proved declaration or an empty-payload ledger entry.
