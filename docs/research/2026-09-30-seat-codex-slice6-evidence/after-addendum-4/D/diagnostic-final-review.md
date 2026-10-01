# D diagnostic move: final read-only review

No scope blocker found. The patch passed `git apply --check /private/tmp/d-integration/staged/03-diagnostic-move/source.patch` (exit 0) while HEAD was `31e44efc` and the checked ledger work was uncommitted. During this review the parent committed the ledger as `4e9bfce7` and applied the move. The checks below were then repeated against that actual, uncommitted moved tree.

- The actual `Test/Machine/StepInvRulesRed.lean` is byte-for-byte equal to its committed ledger version except for `import Effect4.Laws.Api.TraceOrigin` becoming `import Test.Api.TraceOrigin`. Both checked failure messages and `(f : Guard.NFiber)` are preserved; no placeholders remain.
- The new `Test/Api/TraceOrigin.lean` contains the previous production TraceOrigin body verbatim after removing its imports. The already checked proof fixes and explicit proof references are retained.
- The live static import/root scan passed: no missing local imports, library-to-Test dependency, local cycle or diagnostic projection/agreement symbol left in the library. All Effect4/Test modules are reachable. The scanner's separate OCaml5 tool-root list is outside this check's two roots.
- The four moved Api.M1Trace proof references, the three load/step/reachable references, and both zero-ceiling diagnostic gates remain. Library Api.M1Trace still gates its two status observations. The relocation changes module ownership, not the propositions.
- The stale Test SupervisionContract sentence is now corrected in the actual tree to “The fork ledger records the parent, daemon flag and source path.” The source Supervision header likewise names static sites and ledger entries. No additional header repair is required for this move.

Do not copy the old mirrored `staged/03-diagnostic-move/Test/Machine/StepInvRulesRed.lean`: it still has the earlier placeholders and unqualified NFiber. The actual patch changes only the import and preserves the checked file, as verified above.

## Exact narrow verification

The parent now reports the four-target narrow build passed (317 jobs) and the complete 175-theorem production trust probe passed. No further builds are requested by this review. The exact applicable commands, for the receipt, are:

```sh
lake build Effect4.Laws.Api.Supervision Test.Api.TraceOrigin Test.Api.SupervisionContract Test.Machine.StepInvRulesRed
lake env lean -DwarningAsError=true Test/Api/SupervisionContract.lean
lake env lean -DwarningAsError=true Test/Machine/StepInvRulesRed.lean
lake env lean -DwarningAsError=true /private/tmp/d-ledger-review/axioms/ProductionTheorems.lean
```

Use the source-aware axiom inventory against the actual final files (175 authored theorems); refresh its source hashes if comments/import fixes moved lines. Count both “depends on axioms” and “does not depend on any axioms”. The checked invariant candidate covered all 77 theorems (50 with permitted axioms, 27 without); the trace candidate covered 69. Those candidate checks do not substitute for the final source-aware probe.

The static closure command run for this review was:

```sh
python3 /private/tmp/d-ledger-review/check_integration.py
```

The current brief's build rule (lines 57–58) says `make check` runs once at C step 5; the parent reports that run passed. Do not import architecture regeneration or another `make check` from the older plan into D. This move needs no OCaml regeneration, generated-file edit, new trust exception, decision-register edit or M6 instance. The old plan note at `/tmp/d-integration/plan.md` has been corrected accordingly.

No Lean, lake, builds, generators or worktree mutations were performed by this reviewer. Only read-only Git/Python checks and `/tmp` receipt corrections were made.

## Declaration and ownership inventory

Exactly 30 declarations leave `Laws/Api/Supervision.lean` and occur under their same names in `Test/Api/TraceOrigin.lean`:

- Three definitions: `Effect4.Api.TraceFacts.forkedOf`, `originForks`, `Agrees`.
- `Effect4.Api.TraceFacts.M1Trace.load_agrees`.
- Thirteen obligation/law pairs under `Effect4.Api`: `forkedOf_append`, `spawn_forked`, `start_forked`, `fork_forked`, `forkIn_forked`, `forkScoped_forked`, `forkScoped_none_forked`, `launchEntrant_forked`, `forkFinalizers_forked`, `action_fork_forked`, `action_forkIn_forked`, `action_forkScoped_forked`, `supervision_static`. Each obligation is `M1Trace.<name>`; each backing law has the same leaf name except the last, whose backing name remains `TraceFacts.supervision_static_flags`.

The already checked complete source TraceOrigin user moves with its two existing obligation declarations and proofs; the actual old body is retained verbatim apart from imports. Its proof helpers, exact four-field AgreesUpdates, native command traversal, paired append/no-fork bank registrations and positive control move together, so no diagnostic fact has two owners. `Effect4.StepInv` continues to be declared once in the library RuleSets module; the library ledger registrations and Test diagnostic registrations are consumers of that declaration.

The library retains `spawn_trace`, `spawn_child`, `spawn_nextId`, both `M1Origin.spawn_fibers`/`spawn_fibers`, all source connectors/lookup facts, and the two status-with-replaced-trace obligations. These remain independent of `forkedOf`/Agrees. The generic allocation module stays below Program reachability; the native invariant module consumes it and Guard.Core. Neither imports the diagnostic Test module.

The Laws root drops only its TraceOrigin import. Test SupervisionContract and StepInvRulesRed import the new Test owner; Test.All already reaches both consumers, so the new module is reachable without a new root-anchor edit. No runtime root, axiom allowlist, generated file or decision register changes are needed. This is the explicit move in addendum 2, item D.6, reiterated by addendum 4 C.3; no additional scope amendment is identified.
