# Second-eyes review — 2026-10-01 22:46 UTC wake

Integration observed first at `b46bb9c6`, then at `e7c1e4e4c933aeaab40be6f05e56c0faec448c78` while W1 merged. Read-only active repositories; no compiler, build, generator, installations or messages to Claude. One independent reviewer inspected D4's committed runtime change while the root executed an isolated Python checker probe and checked the W1 merge.

## Confirmed resolution: the invalid-revision false pass is repaired on W2

Reviewed the exact committed `scripts/lib/conservativity.py` at W2 `1d7d4ce9d96a2bd9c89b28db65a9778ee8a95304` (introduced in `9986a92b`). All **10 independently executed controls passed**: same-revision comparison with and without strict mode; deliberate golden drift rejected by C1; invalid base, invalid candidate and both invalid, each with and without strict mode, all rejected with exit 1 naming the invalid revisions and no PASS claim; restored golden plus a genuinely new vector accepted under strict mode. This distinguishes a failed revision lookup from a file genuinely absent at a valid historical revision.

Evidence: `2246-conservativity/results.json`, per-case logs, `provenance.json` and `run.py`. The script is copied byte-for-byte from the pinned commit; the Git fixture is wholly under this review directory. Each Python invocation had a 20-second timeout. No Lean or TypeScript was run. The tested implementation is still on W2's unmerged branch; this result resolves the specific false-pass defect, not all compatibility or runtime claims. Source resolution is at `scripts/lib/conservativity.py:125–140`; its own six regression controls at `:451–468`.

## U's missing-evidence finding is now part of the dispatch

Main `b46bb9c6` records the 22:16 finding in row182 and W2 amendment5 (`docs/research/2026-10-01-data-wave/brief-W2.md:110–117`). It explicitly requires complete sections and expected module coverage, a completeness footer, no error lines, and named refusal for empty/truncated/error logs. The original three missing-evidence controls must remain beside passing and real-violation controls. This is a correction to the assignment; implementation remains pending. Do not mark the U checker repaired merely because its brief is repaired.

## W1 merged, with its final annotation amendment recorded

W1 merged at `cdd62673`; the coordinator's `e7c1e4e4` records row128's scoped exactness result and amends row179 to erase `arbitrary`, a generator hint, as the ninth key. Compared the merge to the previously reviewed `03403dc8`: the codec and its proof module have no further changes; the schema bridge adds that key/renames the allowlist and updates descriptions, with unchanged general proof bodies. The final contract controls admit rc.112's persisted integer/natural documents and still refuse `parseOptions` and unknown keys (`Test/Codegen/SchemaGenerationContract.lean:340–380`). Existing seat host/Lean results are retained, not independently replayed this tick.

`AGENTS.md` now correctly states the schema result at `Bridge.schema` rather than unrestricted public `Ty.schema`, with the retraction premises. The K2 row also scopes it to the bridge. Minor documentation follow-up: the system-map §9 literature row still labels the pair `Ty.schema`/`ofSchema` while citing the bridge theorem; align that label with the explicit boundary already stated in AGENTS and §5. This does not change the proved theorem's scope.

## D4: no new runtime defect found, but reconcile the placement change

The independent static review of `1ba84f74` found no concrete defect in the committed step-one runtime change or its simulation statement. It changes successful public lone-finalizer close to unit on both machines and keeps failure propagation, state, empty/multiple cases and internal scoped cleanup intact. It uses the existing sequencing algebra in its typing proof. Dirty step-two work was deliberately excluded; no compiler replay was performed.

**Integration correction:** the brief at `docs/research/2026-10-01-landing/brief-D4.md:30–40` and row151 name the unsafe helper and say the public close stays unchanged. The actual commit deliberately changes the public close and preserves the unsafe helper because the latter is also used by scoped cleanup; the seat reports the literal brief placement added two counted cleanup operations. Reconcile the coordinator's brief/ruling references with that explicit placement adjustment before calling the handoff consistent. A stale Adequacy docstring names the old helper too. Separately, the evidence README's “same rows” Effect3 comparison covers three rows, not all five measured against rc.112. Both corrections and precise source references are in `2246-d4-review.md`. These are handoff/documentation findings on ongoing work, not evidence of a new runtime failure.

## Observation limits and continuation

The Mac remained locked; the fresh Claude computer-use attempt failed, so no current screenshot/accessibility state, live subagent status or command panel was available. Git shows continued work in D2/D4/J2 and multiple W2 commits, as well as W1's merge. See `2246-claude-activity.json` and timestamped `2246-worktrees.json`. General M5/M6/M7 completion is not inferred from these results, and the earlier scope-presence post repair remains distinct from scope-membership validity. The landing campaign remains active.
