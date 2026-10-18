# V1 preparation receipt

The coordinator must retain the explicit proof-status regression of `Checked.ask_value` before landing.
Its exact statement now depends on the planned `Check.combine_deps` goal.
No core trace certificate depends on that goal.

## Base and ownership

The preparation uses S0 implementation `d46b1e6d6f184764a7ee1a00b01a800a45f35d33` and receipt `489e127a8b94f4796ff40ef4200080b5e83a94f2`.
The production worktree is `/Users/pooks/.codex/worktrees/seams/lean4-effect4`.
This agent changes temporary files only and creates no commit.
The coordinator owns production application, central placement, root imports, regeneration, native gates, and commits.

## Implementation

The checker decomposes module asks into their actual part asks.
It combines their full verdicts and retains those actual answers in the checked trace.
The validity proof uses the certified oracle's exactness independently of the decomposition goal.
The extension rule reuses positive compatible part answers through the pure support connector.
The explanation selects only an actual dependency with the exact placed refusal.
Aggregate refusals without such a match retain no invented local part.
The suggestion caller learns the checked trace through `Memo`.
The old `CheckCache.lookup` surface and cache-provenance output fields are removed.
`Run.Kit.check` and operational query answers use `Check.run`.

## Proof status and placement

`V1-PLACEMENT.md` records each obligation's concept, claim, reach, exclusions, and consumer.
`Check.combine_deps` and `Check.explain_replays` remain planned goals.
`Checked.ask_value` keeps its exact statement and is proved modulo `combine_deps`.
`Oracle.eq_uncached` and `Oracle.transparent` retain their core proofs.
Three placed Laws statements retain exact wrappers over renamed pure core helpers.
No core module imports Laws.

## Verification status

The complete affected closure passes with 71 modules in `v1-full/order.json`.
`Tools.Session`, `Tools.Query`, `Run.Kit`, and the retained control battery pass.
The narrow audit passes over the fourteen modules listed in `audit-v1.py`.
Its exact output is:

```text
#axiom_audit: 1801 declarations within [propext, Quot.sound], 1 of them modulo planned goals; 2 planned goals
```

The audit log is `v1-full/audit.log`.
Per-module build logs live in `v1-full/logs`.
The two planned goals are `combine_deps` and `explain_replays`.
The single declaration modulo a goal is the unchanged `Checked.ask_value` theorem.
The audit covers the moved core owners, changed Laws owners, CheckCache, and the battery.
It does not audit the broad unchanged caller graph or establish native behavior.
The coordinator retains the production gates for those boundaries.

The final patch is `V1-package.patch`, with seventeen paths.
Its SHA-256 is `53d59a115021e327eb7b9d91a944aedde55957601c77fa5228c5789edb91e651`.
`V1-manifest.json` records target source hashes.
`V1-baseline.json` records production and target source hashes per path.
The freeze base is production HEAD `0bb42e37d4fa99fd84979df03beb3dd0391a4e98`.
`git apply --check /private/tmp/seams-check-sol/V1-package.patch` passes at that base.
S1 and S2 patches remain separate, unverified drafts.

The final commands run from the production worktree:

```text
SEAMS_RESUME=Effect4.Laws.Program.CheckAgreement python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/build-v1.py
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-check-sol/audit-v1.py
```

The temporary compiler runner writes only below `v1-full`.
It unlinks each compilation target before writing, preserving production dependency artifacts.
Lean control checks remain finite evidence unless they apply an independently proved law.
No temporary Lean result establishes native execution or host behavior.
The trace records semantic answers, not cache hits or checker invocation counts.
Certified oracles yield identical traces for the same checked computation through `Oracle.eq_uncached`.
Any native invocation-count comparison is separate finite host evidence.
