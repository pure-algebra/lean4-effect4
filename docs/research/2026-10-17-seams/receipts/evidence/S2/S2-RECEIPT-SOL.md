# S2 preparation receipt

The new publication agreement keeps the explicit positive-base and reference-free premises.
The old D1–D9 observations and proofs remain separate from the three new planned goals.

## Ownership and patch order

Apply `S2-package.patch` after the frozen S1 packet.
The patch changes six paths; `S2-manifest.json` records their target hashes.
`S2-frozen-inputs.json` records the canonical draft source hashes.
The agent changes no production file and creates no commit.
The coordinator owns central placement, reached roots, regeneration, native gates, and commits.
V1 and S1 packet files remain frozen and unchanged by S2 packaging.

## Implementation and cuts

The sealed pending set opens only from a Doc through `FillSet.open_`.
Its private constructor carries an exact submission-fold witness.
The anchor retains the snapshot and source session.
The checked add calls that anchor's keepExact feed and discards the returned session.
The outcomes preserve applied, collapsed, conflict, overlap, unknown-address, root, and certification refusal distinctions.
Publication builds one address-ordered commit.
The tool checks the snapshot, base sketch, and application, then resets only after a successful step.
The old empty/ofDoc factories and materializeDoc caller disappear.
The old raw `Program.materialize` and certification observations move to the Laws-only `FillReference` owner.
The D1–D9 proof bodies retain their original premises.

Suggestions use the same keepExact feed.
The old evaluateCandidate name is removed.
The mandatory candidate key remains concrete.
A root candidate uses the genuine candidate module key.
A missing typed part key below the root refuses before candidate construction.
`suggestOne` returns `Checked (Except FeedRefusal Suggestion)`.
`suggestPage` propagates that refusal; the existing optional top-level suggest result refuses with none.
No module key or commit-item index is fabricated for missing focus.
The checked trace remains the exact semantic dependency trace, without cost or hit metadata.

## Verification

The complete stage closure passes.
The changed FillSet, FillReference, D1–D9 Laws, suggestion caller, and Tools.Session compile.
The retained V1/S1 batteries and the expanded FillSetControls pass.
The per-module logs live in `s2-full/logs`; `s2-full/order.json` records the dependency order.
The fresh audit log is `s2-full/audit.log`.
Its exact output is:

```text
#axiom_audit: 1428 declarations within [propext, Quot.sound], 2 of them modulo planned goals; 16 planned goals
```

The audited module list is in `audit-stage.py` for S2.
The sixteen goals include S1's thirteen and S2's three.
The two modulo declarations remain the S1 opening and reached-state laws.
No core constructor depends on a planned goal.
The audit establishes neither native execution nor host behavior.
The coordinator retains production behavior gates and any actual reached native sealing work.

Commands run from the production worktree:

```text
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/verify-next.py
SEAMS_RESUME=Effect4.Laws.Program.FillReference python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s2
SEAMS_RESUME=Tools.Session python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-stage.py s2
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/audit-stage.py s2
```

The repeated narrow resumes retain the failed logs for the missing namespace, moved doc comment, and record layout.
The final resumed build and fresh audit both exit successfully.
No production compiler output is written through a dependency link.

## Placement and boundaries

`S2-PLACEMENT.md` records the five placement facts.
The three R14 planned goals are `kept_eq_certified`, `FillSet.add_wf`, and `FillSet.publish_eq_materialize`.
The concept is `initial-algebras-folds`.
The coordinator registers their exact claims before production compilation.

`kept_eq_certified` requires a coherent source, a nonroot address, and reference-free base and filling.
`publish_eq_materialize` additionally requires the exact anchor/source and an initially positive base check.
The old raw certification and materialization algorithms retain their original bodies under `FillReference`.
No initial-positive premise becomes a new operational refusal.
The earlier refuted statements remain in `S2BoundaryProbe.lean` and its logs.
Their corrected statement scopes remain explicit.

## Finite acceptance evidence

Loop2 exercises good/bad/good submissions, one publication, revert, and hole-row retention.
The controls exercise duplicate collapse, conflict, overlap, unknown address, root refusal, empty publication, foreign and stale snapshots.
They retain the separate-reference accepted/jointly-refused counterexample and raw-certification reference boundary.
They retain the positive-base publication boundary.
A same-identity, same-revision document with another base is rejected by the tool's full-anchor check.
The suggestion controls separate typed-root module keys from resolved nonroot paths without typed focus.
They compare root traces with the genuine module ask's dependency trace.
They require empty trace and no candidate for missing focus.
These are finite controls, separate from the universal planned goals.

## Frozen patch validation

The patch SHA-256 is `c489d0c8c73344c3da86c062f7bf7aa9bccf5a659dcbeabbf64e8e530ed72277`.
The incremental S1 and S2 patches apply successfully in the temporary `patch-check` tree.
All thirteen cumulative target source hashes match their manifests after application.
This check changes no production file.
