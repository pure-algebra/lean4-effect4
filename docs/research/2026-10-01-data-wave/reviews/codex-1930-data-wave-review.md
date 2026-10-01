# Data-wave dispatch review, 2026-10-01 19:30 UTC

**Starting the preparatory data work in parallel is consistent with the documented dependencies. Three limits should stay explicit: the v0 handler uses host-side decoding; Q's current generated laws omit the proposed cross-head rules; the eventual acceptance harness needs stronger comparison controls.** No blocker to dispatching the syntax-package work was found.

Read-only review of main `2bf570ca`, Q `6f0e9d7ac922f2c189eb59efa95c3aaf3a211703`, and the newly authored data-wave README/W0 brief. Main was clean on the initial metadata read. The coordinator was authoring dispatch documents during this review; those documents are interim instructions, not evidence of completed implementation. No compiler, generator, installation, repository edit, branch change, UI action or message to Claude's seats. One bounded reviewer examined R and the p2 milestone; its [report](1930-r-milestone-review.md) records the exact scope and locations.

## What is aligned

- Decision 165 now rules that records carry their canonical names in the existing value frames. This addresses the type-blind projection/reader ambiguity established by the earlier independent record review. The rule is recorded; the implementation remains future work.
- The new wave README sequences the value/type changes after D1 and assigns distinct law, generation, syntax-package and face work. W0's brief includes expression-key access, computed keys, optional fields, constructor calls, spread and generic class heritage; it covers the needs R names.
- R's note at 524–538 and the harness explicitly keep decode in the host. Therefore the handler-only p2 milestone can precede the later in-program decoder. This is not acceptance of the original layered p2 with in-program decoding. The current record harness still has empty components and correctly keeps acceptance at `none`.

## Q's success is for the structural family, not all proposed type rules

At pinned Q, `Q/probe/ProbeQW/Ty.lean:148–156` explicitly models no new non-congruence rule. Its new leaves do not introduce `undefined <= unit`. Generated `Q/generated/ProbeQW/TyView.lean:474–476,549–551` still characterizes order using only the literal-to-string rule, the unknown rule, and matching heads with related children. `Q/tools/Effect4Gen/View.lean:903–923` still fixes the six exceptional cases and computes the rest from the congruence rows.

**Source-level consequence, not a new compiled counterexample:** if proposed row 160's `undefined <= unit` rule is retained, the current generated different-head theorem cannot keep its statement. At that pair, both types are members, literal and unknown exceptions are false, and the heads differ; its conclusion requires the comparison to be false, while the new rule would require true. This is a statement/interface change, beyond merely renumbering the generated cases.

W2's current input column names Q alone while W4 receives P's type rules. Before freezing W2, join it to P's final cross-head rules and include an accepted cross-head case plus its rejected converse. A shared description of the exceptional rules would reduce repeat hard-coded changes. No numerical inclusions are presumed approved here; those depend on the profile and carrier decisions. This limitation is already acknowledged in Q's live work, so it is an integration requirement, not a claim that the ongoing probe failed.

## Strengthen W10's acceptance controls

1. `R/probes/P2RecordHarness.lean:354–368` calls the paired check proof that adaptation strips `createdAt`, but the Boolean only tests that adaptation returns something and strict decoding returns nothing. Compare the adapted value with the exact expected canonical named record, or encode it and compare with the expected reduced object. Keep rejecting controls for a retained extra field and an incorrect retained value. This concern is about that individual check's strength; it is not a demonstrated false acceptance of the complete handler run.
2. The same file's `canon` at 232–239 keeps the first duplicate name. `normJ` at 315–323 uses it, despite the comment at 455 saying only key order is ignored. On raw JSON lists, adding a later conflicting duplicate therefore disappears. Restrict the comparator to recursively duplicate-free objects, reject duplicates, or define sorting without deletion. If the landed encoder proves duplicate freedom, thread that premise into the acceptance boundary. The current three expected objects have unique keys; no wrong result on those fixtures is alleged.
3. `readBack` at 363–366 passes the printed syntax object directly to `Api.readModule`. It does not parse the rendered TypeScript text with `ts/eff/read.ts`. If acceptance includes the external reader, add that check; otherwise name the narrower syntax-object round trip. W8 schedules the external reader work, so this is a W10 acceptance-boundary clarification rather than evidence it has been omitted from the implementation plan.

These are bounded acceptance improvements to carry into W10, not reasons to stop W0 or the independent generator work. Keep the public milestone labelled “p2 handler with host decoding,” and do not count the narrower generator probe as checking the final full type order.

A final metadata read saw main advance to `3666695196ee72cd7df7d2aae28c6c8c9c6bc717`, clean. That later head was observed only; this report's source pins and in-progress document hashes above remain its review boundary.
