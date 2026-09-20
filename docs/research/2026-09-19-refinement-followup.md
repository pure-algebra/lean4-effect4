# Refinement follow-up, 2026-09-19

The earlier four tooling counterexamples are repaired, but two related field-ownership
counterexamples still pass the skeleton generator. Keep the current architecture and tighten
that accounting before extending it. The completion migration remains the right next machine
slice; its deletion list must retain the invalid-reference case. The transaction proposal must
keep an explicit proof connecting the existing standalone execution bound to an embedded attempt.

This reviews `f440492387d7a3cd601fb2bcb1aa80d6af2a21d8` through
`65b143a27e3b9c614cda8f21ffd63e40f88b54cf`. The last commit arrived during the review;
its trust-scanner and M1-plan changes are now landed, not drafts. The remaining working-copy
README changes were excluded. This report changes no source, contract, decision, or plan.
Its accompanying evidence is [retained here](2026-09-19-refinement-followup/manifest.json).

**What is now established.** The three original generator omissions have controls that project
the formerly missing clauses: the mixed value/child field, the one-constructor non-structure,
and the nested column owner. The parameterized stale `ProofWanted` marker is also rejected.
`make check-typed-state` passed at `3cb5805e` (251 jobs, including cached dependency replay).
The relevant generator and ledger sources are unchanged at `65b143a2`.

The plan now retains resume-input typing and interrupt provenance, requires typed-cell
compatibility in the world order, includes internal store operations in the protocol, and
places world data below the protocol and predicate assembly. These corrections address the
earlier architectural findings. `ProofGraph`, generated predicates, the existing proof bank,
and authored semantic obligations remain useful shared mechanisms. The concrete world,
completion migration, and preservation proofs remain future work; the generated skeleton is
not their completion certificate.

**1. P1 — coverage must follow fields, not global type or predicate names.**
In `src/Effect4/Laws/Auto/TypedStateDecl.lean:359–369`, a custom predicate on one field adds
its child's type to a global skipped set. All other occurrences of that type then escape the
final check. Separately, a column is considered covered if any emitted predicate has its name,
even when that predicate belongs to an unrelated store type.

The checked [OwnershipProbe.lean](2026-09-19-refinement-followup/OwnershipProbe.lean) contains
both cases. `FollowupSkippedOccurrence.ignores_unowned` constructs `ParentOk` using only the
custom predicate on `owned`; the sibling `unowned` has no check. In the second case, two stores
have a `Heap` row, but only store A is selected as owner. `FollowupColumnOwnership.ignores_b`
constructs `ParentOk` from A's column alone. Both declarations elaborate with no axioms, and
the printed predicates show the omission. This is an incomplete generated requirement, not a
Lean kernel failure. No missing clause in today's concrete machine skeleton was established.

The bounded repair belongs in the existing generator: record which field subtree each custom
predicate covers, and which selected owner discharges each column occurrence. Reject an
unowned occurrence even if a sibling is covered or another column shares its name. Keep the
two probes as focused controls; no new framework or serialization format is needed.

**2. P1 — completion data does not establish reference validity.**
Plan §14's M1 row (`2026-09-19-state-refinement-plan.md:696`) now deletes both
`STORES-FB-COMPLETION` and `E4-STORES-CE-003`. Deep-dive §10 endorses that deletion.
But the existing counterexample already uses `Completion.ofRefGet ⟨9⟩`: a valid Deferred can
store it while reference 9 does not exist, and `Stores.WF` still holds. I reran
`Test/Machine/Runtime/StoresLawsContract.lean`, including those guards, with exit 0.
`Machine/Completion.lean:28–30` restricts the completion's shape, not the existence or type
of its referenced cell.

M1 can delete the raw-program shape machinery and the whole shape-only `DeferredOk` predicate.
Translate CE003 to the new data representation and retain its validity boundary. Discharge
that boundary when the promise/handle invariant and its preservation theorem exist, or expand
M1 explicitly to include them. No second completion representation is required.

**3. P1 — the proved root budget still needs a transaction connector.**
Decision 84 and deep-dive §10 now cite `max (depth e) (2 * steps e + 6)` as sufficient to avoid
an attempt frontier. The useful existing theorem is `Sched.straight_sufficient`
(`Laws/Program/RuntimeR.lean:289–291`): it starts from `loadR e fuel` and runs
`[Api.evaluate, Api.flush]`. `loadR` starts a single root with empty stores.
`TypedProgram.run_sound` likewise concerns `Api.run`. Lower driver lemmas have stack and
quiet-store assumptions; they do not already cover an arbitrary live transaction context.

Reuse the bound and those lemmas, while retaining a wrapper-specific obligation for the
allowed outer continuation and stores, attempt entry/exit work, available or reserved budget,
and isolation conditions. The new Tx operations must fall under that result too. Computing a
number at admission does not establish that the running driver has that much work remaining.
This is a missing connection, not a refutation of the existing theorem or a reason to write
another size fold. Decision 84 remains open.

**4. P2 — separate the architecture map's measurements from its declared policy.**
The map is useful: Lean parses the imports, the proof and runtime roots are separate, and it
does not impose another semantic gate. However, `ArchitectureRoles.lean:111–112` puts all
Tools below OCaml5, while `docs/ARCHITECTURE.md:32–37` explicitly permits Tools drivers to
consume OCaml5. Six reported red imports follow that documented design. The accepted proposal
to separate shared descriptions from higher drivers resolves this; it has not landed yet.
The map's red rows are questions against its coarse ordering, not established defects.

Also label module existence as source presence, not proof completion. `pathOfModule` accepts
a directory alone, and the milestone caption contains fixed progress prose. Link completion
to the existing plan/ledger. The two empty directories reported at `3cb5805e` have been removed
from the later snapshot, resolving that observed discrepancy. The producer still renders local
empty-directory state, so future checkout debris can change a tracked report without a source
change; keep that hygiene information local or derive the tracked projection from tracked paths.

**5. P2 — retain the cheap counterchecks when retiring the slow trust self-test.**
The parser-based scanner fixes a real measurement problem: syntax kinds distinguish tactics
from binders and term-level control flow. Its current focused harness passed all 14 fixtures.
That harness discards `scanSource`'s proof-shape result and uses its default token-table branch.
The deleted `test-trust-gate.sh` was the only runner of the proof-shape ceiling control, among
other planted checks. Thus the 14 passing cases do not verify the main new counting behavior
or source-specific token reconstruction. No false acceptance in the replacement scanner was
established here.

Extend the existing one-process harness with positive and negative count assertions, the
retained proof-shape fixture, a macro-splice case, and one source-specific token-table case.
Exercise the ceiling with a small temporary pin. This retains focused evidence without
restoring the slow whole-tree mutation loop. `check-known-red.sh` also has no normal check-tools
caller now; if that policy is retained, give its stale-entry check an explicit owner. Its
current empty list makes this a future coverage gap, not a current false green.

**One research claim to reject explicitly.** The incoming M1 specification's §3 describes
constant-time prepend in Lean and constant-time native indexed OCaml storage. Lean allocation
already appends. `ocaml/engine/e4_store.ml` wraps `E4_table`, whose nonempty representation is
`Map.Make(Int)` (`e4_table.ml:3,21–28`). Keep the proposed `Arena` law interface, but do not
use that cost claim or finite host property tests as evidence of an array implementation or a
verified lowering. Deep-dive §10's broad “Confirmed” needs this qualification.

**Verification and scope.** Three read-only review seats checked the repairs, the architecture
map, and the M1 proposal independently. The coordinator ran the narrow typed-state build,
the two new omission witnesses, the existing store contract, and the 14-fixture source-scanner
harness serially in an isolated checkout. Exact commands, revisions, outputs, and hashes are
in the manifest. The omission witnesses use no axioms; the store contract's printed
declarations use at most `propext`. No fresh whole-tree axiom audit, architecture regeneration,
host benchmark, or target agreement result is claimed. The first ownership-probe draft had
a missing import and was discarded as evidence; the retained corrected input checked cleanly.

The next useful work remains small: repair field coverage, amend the M1 deletion boundary and
transaction proof claim, then land the completion-data migration with its representation
connector. Preserve the current single program representation and explicit lowering relations.
These findings call for more precise ownership and theorem statements, not another program IR
or another layer of general-purpose tooling.
