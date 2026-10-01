# D integration after C

The existing lift, guard re-derivation and native memo-ID user are already landed. Do not recreate them. The remaining three commits are the trace user, the ledger user, then the diagnostic move. No M6 instance is included. Source proposals here were staged without editing the repository or running Lean; root owns all compilation, axiom checks, message capture and commits.

The checked inputs are the root-owned files under `docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/D/probes/`. Root reports that `InvariantCandidate.lean` passes, that its axiom run prints 77 reports (27 with no axioms) within `[propext, Quot.sound]`, and that `TraceCandidate.lean` passes with 69 axiom results within that ceiling. The earlier draft axiom-file line count must not be reported as a measured theorem count.

`stage_slices.py` reads these inputs and stages three separate patches under `staged/`; it never applies a patch, writes repository files or invokes a build. `staged/manifest.json` records input and per-file hashes. `staged/final/` is the cumulative overlay for independent import/name review. Red fixture messages are explicitly marked placeholders until root captures the actual failures. The initial staged patches have now been handed to root; once a stage is applied, do not rerun the whole staging script against the partially changed tree. Refresh subsequent patches from the actually checked source if production proof repairs alter them.

## Existing work, verified by source reading

- `src/Effect4/Laws/Machine/Lift.lean` contains the three lifts and `MachineEdits` (eight outside-loop fields).
- `src/Effect4/Laws/Program/Guard/Core.lean` contains `foldl_lift`, `reachable_lift` and `reachable_lift_pure`.
- `src/Effect4/Laws/Program/Guard/Driver.lean:87–95` derives the contract from `driverContract_of_lift`; the four old history inductions are absent.
- `src/Effect4/Laws/Program/Guard/MemoIds.lean:447` proves `reachable_memoIdsOk` on raw native decision prefixes. `Guard.lean:6` imports it. The reference evaluator is explicitly not covered.

## Commit 1: trace user and bank

Exact source/test paths:

- `src/Effect4/Laws/Auto/RuleSets.lean`: add `Effect4.StepInv` to the existing bank declaration list after `Effect4.Fibers`; no duplicate bank declaration in the user module.
- `src/Effect4/Laws/Api/TraceOrigin.lean`: generic trace leaves, exact four-field `AgreesUpdates`, all eight `MachineEdits` fields, concrete native command coverage, `reachable_agrees_of`, actual proofs behind the existing obligation declarations and an `emit_with_bank` positive control. Preserve the obligation declarations; remove their two stale `#proof_wanted` commands, add explicit proof references, and lower `TraceFacts.M1Trace` ceiling from 2 to 0. The existing `load_agrees` obligation in Supervision gets its explicit reference here too.
- `Test/Machine/StepInvRulesRed.lean`: the same conditional-emit proposition with plain `aesop`, under `#guard_msgs (error)`, and a print of the source positive theorem's axioms. Capture the exact error; do not guess the message.
- `Test/All.lean`: import that fixture immediately after `Test.Program.TypedStateRulesRed`.

The trace observation is the ordered list of `(parent, child, daemon)` triples. It excludes source paths and does not establish semantic correctness of parents or flags. Both recordings can agree on wrong data. A blanket emission rule would be false; retain `NoFork events` on every emission lemma.

The production bank contains the checked trace normalizations for update, conditional emit, modify, races, arm/disarm, halt, state, tokens, middleware and fiber-list-only writes; `NoFork` literals/append/frame-map facts; the paired append equation `spawn_iff`. The root's successful repair additionally registers `emit_ok` as SAFE APPLY because conditional simp alone did not discharge the no-fork premise. Include its `List.filterMap_cons`/`nil` registrations from the checked input. General view transport, transitivity, and rules with unbound choices stay out of the bank.

Commands, serially, in the worktree:

```sh
lake build Effect4.Laws.Auto.RuleSets Effect4.Laws.Api.TraceOrigin
lake env lean -DwarningAsError=true Test/Machine/StepInvRulesRed.lean
lake build Test.Machine.StepInvRulesRed Test.Api.SupervisionContract
```

Before rewriting any existing bodies against this bank, use a retained research file importing `Effect4.Laws.Auto.Census` and the module to run `#auto_census Effect4.Laws.Api.TraceOrigin using aesop (rule_sets := [Effect4.StepInv])`. It takes a module name, not a declaration namespace. Record which goals search closes separately from the hand-written native cases. Adding the new proof user is not permission to refactor the already landed memo proof.

## Commit 2: ledger user

Exact paths:

- `src/Effect4/Laws/Machine/ForkLedgerInvariant.lean` (new), imports `Laws.Machine.ForkLedger` and `Laws.Machine.Lift`. Namespace `Effect4.Machine.ForkLedger.Invariant`. This holds the allocation view, its transport/freshness/append facts, generic machine leaves, outside-loop edits, and the normalization bank. It imports no API or Program reachability module.
- `src/Effect4/Laws/Program/Guard/ForkLedger.lean` (new), imports the generic module and `Guard.Core`. It holds load, the concrete native command proof, runFork/runCallback, decision/history instances and four public consequences, plus `update_with_bank`.
- `src/Effect4/Laws/Program/Guard.lean`: import the new native module immediately after `Guard.MemoIds`. This makes both new law modules reachable from the existing Laws root without changing the runtime root.
- `Test/Machine/StepInvRulesRed.lean`: add the corresponding plain-aesop omitted-bank update fixture, with its actual message and source positive axiom print.

Use the checked generic base; do not reconstruct it from the old uncompiled `/tmp/Effect4ForkLedgerInvariantDraft.lean`. Its `List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩` is supported by pinned Lean 4.33.1; `List.nodup_singleton` is absent from that toolchain's List source. Preserve the repaired parentheses around lambdas, explicit `m'` in map transport, and the early `DecidableEq` assumptions before interrupt edits.

The native draft's two measured corrections are retained: put `update_keeps_ids` into an explicitly shaped equality before rewriting, and carry the bumped `nextToken` machine before countdown's modify/emit. The generic invariant ignores trace; its emit fact needs no no-fork premise. A counter increment can repair an earlier false bound, so ledger allocation is forward preservation, not an iff/`Keeps` rule.

The four public results are: unique record children; fiber and record-child IDs below nextId; each record child present with distinct fiber IDs; nextId absent from both lists before allocation. These give the needed freshness premises for the already checked local lookup lemmas. Parent membership, parent/daemon/site correctness and old-field agreement for every run are not consequences of these four facts. Root allocations `Api.load`, `runFork` and `runCallback` get no fork record and are explicitly covered.

```sh
lake build Effect4.Laws.Machine.ForkLedgerInvariant Effect4.Laws.Program.Guard.ForkLedger
lake env lean -DwarningAsError=true Test/Machine/StepInvRulesRed.lean
lake build Effect4.Laws.Program.Guard Test.Machine.StepInvRulesRed
```

The 11 new ledger normalization facts are update, emit, modify, updateRace, arm, disarm, halt, state, nextToken, state+nextToken and middleware. `appendRoot_ok` and allocation helpers retain their premises; no unconstrained view transport is registered. The ledger red control uses `update`, whose ID-preservation equation is needed; an emit-only ledger control would reduce to its hypothesis even without the bank.

## Commit 3: diagnostic move

Exact paths:

- `src/Effect4/Laws/Api/Supervision.lean`: remove `forkedOf`; the trace-only theorem/obligation pairs; `originForks`, `Agrees`, `load_agrees`; and their four explicit diagnostic proof references. Keep interleaved source, allocation, lookup and status laws. Rewrite the header's group (a) to describe static sites and ledger entries.
- Delete `src/Effect4/Laws/Api/TraceOrigin.lean` after copying its now-checked diagnostic user.
- `Test/Api/TraceOrigin.lean` (new): own those moved definitions, paired declarations, references, and the checked trace user. Preserve existing declaration namespaces, so this is a module move rather than another statement renaming.
- `src/Effect4/Laws.lean`: remove the exact `import Effect4.Laws.Api.TraceOrigin` line.
- `Test/Api/SupervisionContract.lean`: replace its direct Laws.Supervision import with `Test.Api.TraceOrigin` (which imports that law module); the existing `Test.All` import of SupervisionContract makes the new Test module reachable.
- `Test/Machine/StepInvRulesRed.lean`: replace its source TraceOrigin import with `Test.Api.TraceOrigin`.

Moved trace pairs: `forkedOf_append`, `spawn_forked`, `start_forked`, `fork_forked`, `forkIn_forked`, `forkScoped_forked`, `forkScoped_none_forked`, `launchEntrant_forked`, `forkFinalizers_forked`, `action_fork_forked`, `action_forkIn_forked`, `action_forkScoped_forked`, `supervision_static` (actual proof `TraceFacts.supervision_static_flags`). Preserve `spawn_trace`, `spawn_child`, `spawn_nextId`, `M1Origin.spawn_fibers` and `spawn_fibers` in the library despite their interleaving with the moved text.

`Api.M1Trace.statusOf_replace_trace` and `fiberStatuses_replace_trace` stay in the library. A library gate remains for those two at ceiling 0; a Test gate for the same prefix includes the moved diagnostics at ceiling 0. `TraceFacts.M1Trace` retains its separate zero gate after relocation. No test import is added to library source, and the library must no longer mention `forkedOf`, `AgreesUpdates` or `TraceFacts.Agrees`.

```sh
lake build Effect4.Laws.Api.Supervision Effect4.Laws
lake build Test.Api.TraceOrigin Test.Api.SupervisionContract Test.Machine.StepInvRulesRed
lake env lean -DwarningAsError=true Test/Api/SupervisionContract.lean
lake env lean -DwarningAsError=true Test/Machine/StepInvRulesRed.lean
```

The current brief explicitly runs `make check` once at C step 5; that completed. D uses the named narrow builds, axiom checks and static closure checks. No architecture regeneration is authorized here. No AxiomGate allowlist entry is proposed: the RuleSets implementation module is already classified, and all new theorem terms remain at the normal ceiling.

## Evidence and row 94

For each user, retain exact narrow commands/results and axiom output; count actual printed results, not script lines. Print the two obligation backing proofs and `.checked` declarations, all native command/decision/history capstones, the ledger's four consequences, generic edits/spawn and the two positive bank controls. The original candidate appendices cover every drafted helper; production namespaces change, so an old `Draft.*` print list cannot be blindly reused. An imported module does not expose a private theorem's source alias: either print it in the same source probe or audit it through the public theorems that use it.

Row 94's comparison is measured: generic structural transport, singleton/nodup arithmetic, list induction and native wrapper selection were hand-written; leaf normalization and many command cases use the named bank; Lift supplies loop/decision/history recursion. Memo IDs separately has native store-hook proofs, whereas ledger/trace ignore arbitrary state replacement. None of this authorizes a statement-generating command or an M6 instance. The coordinator owns decision-register updates.
