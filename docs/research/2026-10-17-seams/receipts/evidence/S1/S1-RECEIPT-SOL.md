# S1 preparation receipt

The reached-state law changes proof status explicitly; `REACHED-VIEW-TRANSPORT.md` preserves its old statement and transport.
The current source has no added coherence premise on that reached-state observation.

## Ownership and patch order

Apply `S1-package.patch` after the frozen V1 packet and the coordinator's central V1 placement.
`S1-manifest.json` records its ten target source hashes.
`S1-frozen-inputs.json` records the canonical draft source hashes.
The agent changes no production file and creates no commit.
The coordinator owns placement, root imports, native generation, gates, and commits.
The S0 base and V1 freeze base are recorded in `V1-RECEIPT.md`.

## Behavior and retirement

The source session holds its source table without a stored expanded table.
The policy feed performs the actual checker requests through `Checked`.
The sealed Doc holds its origin, accepted history, session, and replay proof.
Its revision derives from accepted history length.
The same interpreter handles commit batches, drafts, reverts, and replay.
The replay state carries the undo ledger; it does not reconstruct undo from a projected source session.
The migrated tool stores the sealed Doc and learns checked traces.
The old Doc commit checks, undo, fork, and free revision field are removed.
An interim old FillSet caller publishes through `Doc.step`; S2 deletes that interim surface.
The preview Snapshot remains until S3b; it is not Doc persistence.

## Verification

The complete stage compilation passes, including both core modules and migrated Laws.
`Tools.Session`, `CheckCacheControls`, `SourceFeedControls`, `SourceDocumentControls`, and `FillSetControls` pass.
The logs live in `s1-full/logs`; `s1-full/order.json` records the dependency order.
The fresh audit log is `s1-full/audit.log`.
Its exact output is:

```text
#axiom_audit: 1203 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 13 planned goals
```

The audited modules are listed in `audit-stage.py` for S1.
The audit covers the changed core owners, document Laws, and finite batteries.
It establishes neither native execution nor host behavior.
The coordinator retains the production behavior gates.

Commands run from the production worktree:

```text
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s1
SEAMS_RESUME=Effect4.Laws.Program.SourceTable python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s1
SEAMS_RESUME=Effect4.Laws.Program.SourceDocument python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s1
SEAMS_RESUME=Tools.Session python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s1
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/verify-next.py
```

The final command first audits S1, then begins the separate S2 compilation.
The first stage succeeds; S2's first failure and repair remain separate evidence.
Earlier failed S1 logs retain ambiguous namespace, redundant tactic, and record-layout controls.

## Placed goals and status departures

The proposed R14 concept is `initial-algebras-folds`.
Each Laws file opens with its question, reach, exclusions, and consumer.
The coordinator must register the claims before production compilation.

Source-session goals: `feed_coherent`, `feed_keeps`, `feed_draft`, `feed_keepExact`, `feed_root`, `feed_undo`.
Reach goals: `Doc.coherent`, `SourceSession.replay_drafts_view`.
Document goals: `Doc.step_coherent`, `Doc.commit_sound`, `Doc.commit_one_keepExact`, `Doc.commit_single_sound`, `Doc.revert_program`.
The audit's two modulo declarations are `SourceSession.open_coherent` and `SourceSession.reached_view`.
The first uses V1's exact `Checked.ask_value`; the second uses the explicit `Doc.coherent` goal.
Previously proved raw reached-state claims therefore receive no silent proved status.
The old arbitrary draft-list fragment is retained through the explicit replay connector goal.

A kept local edit may accept beside an already refused root.
The finite control retains that behavior.
Positive-root commit claims therefore require the initial positive-root premise for keepExact.
No new operational refusal enforces that premise.
The conditional `SourceSession.view_eq` helper does not replace the unconditional reached-state claim.

## Finite acceptance evidence

The batteries exercise Loop1 rows 1–4, nested revert, late rollback, and empty commit refusal.
They exercise foreign and stale snapshots, root module keys, missing focus, references, and hole-row retention.
They retain root/local refusal distinctions and exact trace learning.
These are finite controls, separate from the open universal goals above.

## Frozen patch validation

The patch SHA-256 is `b78ae2b78b443ac0d50e1befdfdf89c721f4c7e796fe19a19f4c47e776f6e718`.
The incremental S1 and S2 patches apply successfully in the temporary `patch-check` tree.
All thirteen cumulative target source hashes match their manifests after application.
This check changes no production file.
