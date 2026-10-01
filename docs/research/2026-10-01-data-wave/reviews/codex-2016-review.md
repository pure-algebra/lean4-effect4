# 20:16 independent review

Integration pin: `4bb22835b13b793e7b0c6fab4360ef2e91cc8ad3`, branch `refactor/phase1-phase3` (the Git branch named `main` is not the integration branch). Claude project/session confirmed by fresh screenshot and accessibility state. A single view-navigation Back action exposed the Background tasks overview; no messages, draft edits or task controls. J, D1 and S merged; the combined rebuild was visibly running. P, Q, D3, W0 and new probe U remain active. Main documentation and W1/W5 updates were being written during the review; distinguish those uncommitted edits from the pin.

## Tested finding: optional fields invalidate S's proposed branch-separation shortcut

[Schema S note, line 242](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-type-language-probe/S/note.md:242), repeated at line 623, correctly requires that no earlier branch's adapter accept a later branch's exact image. But its claimed sufficient test, that neither full field-name set is included in a later set, is false for optional fields. The same shortcut was also present in the coordinator's in-progress decisions row 122 when inspected; that edit was not yet committed.

The finite counterexample against the pinned vendored Effect rc.112 source uses these two branches in order:

- A: required numeric `a`, optional numeric `b`.
- B: required numeric `a`, optional numeric `c`.

The name sets `{a,b}` and `{a,c}` are incomparable. Input `{"a":1,"c":2}` is rejected by strict A and accepted by strict B. Strict union decoding returns both fields, while the default adapter accepts A after dropping `c` and returns only `{"a":1}`. Thus the proposed name-set check admits exactly the disagreement it is meant to exclude.

**Smallest correction:** retain the semantic non-shadowing premise. Remove the full-name-set shortcut from the note/register/dispatch. Distinct **required** literal tags remain a usable sufficient case (tested here). Any broader record-separation check must account for required versus optional fields and their value constraints, with a theorem connecting that check to non-shadowing. Do not change rc.112 branch selection silently.

Evidence: [probe](2016-optional-union/probe.mjs), [passing log](2016-optional-union/green.log), [deliberately false claim rejected](2016-optional-union/red.log), [restored log](2016-optional-union/restored.log), [commands and source provenance](2016-optional-union/verification.json), [runner](2016-optional-union/run.py). Green/red/restored exits 0/1/0; the red fails at the intended agreement assertion. A malformed required value is rejected; distinct tagged branches agree. Bun 1.4.2, runs 0.191/0.192/0.141 seconds; runtime-reported RSS 38–44 MB, not a peak measurement. Vendored sources unchanged against the pinned commit before and after. This is a finite host-runtime counterexample, not a Lean theorem or TypeScript type-check. No compiler process or build was run. OS memory-limit and process-monitor setup were unavailable in the sandbox; the fixed finite script used bun --smol and a 20-second subprocess timeout.

## Uncompiled candidate retained for the next bounded review

[Independent D1 source review](2016-d1-review.md) identifies a possible missing well-formed-reference premise between expanded `PointTyped` and the still-open unconditional `DenotesTyped` obligation. Runtime rejects a reference targeting another reference, while repeated expansion can resolve it. The public loader still rejects such malformed roots. No full counterexample was compiled, so this is not a confirmed theorem failure or user-program acceptance bug; do not amend the obligation without a measured probe. This differs from the receipt's acknowledged expansion fixed-point proof debt.

## Other status

The previous allocation/fork finding remains recorded as repaired; broader M5/M6/M7 work is ongoing. The earlier stability-summary and generation/compatibility distinctions remain open at the reviewed commit and are not repeated as new findings. D3's visible transcript labels proposed finish/launch counterexamples as awaiting checks, correctly; unfinished investigation is not a failed landing. S explicitly separates guarded exactness proofs from unproved plain-reader exactness, and its draft W1 handoff names that choice. No active repository or worktree was changed by this review.
