# PUB numbering repair review

No new actionable mismatch appears in the frozen repair at `a1d358a0`. Its source and retained results satisfy the coordinator’s six conditions.

This review does not accept staged main integration. Main starts at `3a2616f1` in the parent’s observation.

## Scope

The reviewed commits are `fa1507b5`, `9f7241dd`, and `a1d358a0`. Their branch also contains the coordinator’s integration `c957bfab`.

The monitor reads source and saved results. It runs no Lean, compiler, runtime, generator, build, or repository gate.

`source-and-evidence-hashes.json` retains twenty-nine sources and evidence copies with original paths. `data-comparison.json` records independent comparisons of retained JSON.

## The agreed repair

All declarations below are in `harness/truth/Truth.lean`, unless another path is named.

| Condition | Source and evidence | Status |
| --- | --- | --- |
| One first-sight rule | `Row.sight`, `firstSeen`, `numbering`, and `numberOf` use a child’s first fork row or its first start. | Matches the three `Recorder.see` sites in `harness/truth/run-truth.ts`. |
| Every compared fiber field | `Row.rename` covers both fork fields and every row owner. `reasonJson` and `valJson` cover interruptors, handles, nested values, and snapshots. | `runJson` and `runSyncJson` each use their own run’s numbering. |
| Other programs remain unchanged | Both retained manifests and result records preserve all 51 earlier programs except `pQueueOrder`. | Independently checked as complete JSON entries. The 47 previously committed entries also remain unchanged. |
| Real differences stay visible | Guards pin the original nine-row difference, accept a pure renaming, and reject reordered events. | Source controls remain present; saved elaboration and generation succeed. |
| Document the rule and its limits | `reduced` corrects the old assertion. `reduce` names the lost allocation-order observation and the joined-before-sight limit. | The coordinator accepts leaving `LANE.md` unchanged because it contains neither numbering nor a limits list. |
| Name the changed observation | The comparison no longer checks machine allocation order in any compared field. | Stated in `reduce` and the saved handback. |

The rule runs after `machineRows` projects the trace. Hidden detached forks therefore do not allocate observable numbers.

`scheduled` and `ran` rows do not create numbers. They retain their owner fields under the same map; priorities remain unchanged.

`pLateSeen` adds a measured exit control. Its result contains both the interruptor `2` and the helper handle `3` after renaming.

Snapshot handles also have positive and identity-map red guards. The new host program measures the interruptor and ordinary handle, not snapshots.

The raw `events`, `internal`, and `fibers` records retain machine identifiers. The source names why they are outside the numeric comparison.

The runner reads `fibers` only for the root’s parked verdict. Root identity remains zero. Tape fibers remain recorded but unconsumed by Lean’s tape decoder.

## Verified preservation

The baseline contains 47 programs; the failed scratch probe contains 52; the new lane contains 53.

All 47 baseline manifest and result entries are equal to the new entries. No tape file changes.

Against the failed scratch probe, exactly `pQueueOrder` changes. Every other existing manifest and result entry is equal.

Its result changes only `scheduleAgree` and the note explaining the old numbering difference. Its answer stays `[1,101,2]`.

The new `pLateSeen` entry is the sixth addition. The coordinator explicitly accepts it in the saved 12:33 message.

The recorder’s executable source is unchanged. Only its header comment changes, as authorized.

## Saved acceptance evidence

`truth-probe-3.log` names Bun 1.4.2, Effect 4.0.0-rc.112, and tsgo `7.0.0-dev.20260629.1`. Both runner and compiler exit zero.

`gen-truth-2.log` reports 52 matching programs and one signed divergence. That is 53 programs total; the existing U-01 divergence remains explicit.

`check-truth-2.log` records 23 host tests, zero failures, and nine signed-divergence controls without failures. The regenerated modules type-check.

`build-5.log` reports 990 jobs, 740 modules, and 87,684 declarations. It retains 24 planned goals and 11 declarations depending on goals.

These are seat-produced results, not monitor reruns. They establish bounded observations for the emitted expansion on rc.112, not native Queue agreement or a general wrapper proof.

## Accepted limits and integration work

A fiber joined before its first sight can expose a different exit-row order. The saved probe and source preserve this recorder limitation.

Literal interruptors, never-seen fibers, and numbers computed from identifiers retain their stated limits. The repair claims no solution for those domains.

The generated-corpus record reports 397 unchanged entries out of 400. The three changed entries are `g102`, `g204`, and `g246`.

The coordinator accepts that consequence and owns regeneration of the two affected corpus-result cells. The seat does not claim it ran `check-corpus`.

The coordinator also owns the two new Makefile prerequisites, release ledger refresh, contract wording, and integration checks. These pending items are already assigned.

The seat continues typing, faces, engine work, and its final receipt. This packet makes no claim that those later parts are complete.

## Disposition

No new advisory is needed. Preserve the known limits and check the coordinator’s later integration receipt.

The branch advances to `0338b004` during the final status read. That later commit is outside this frozen audit.
