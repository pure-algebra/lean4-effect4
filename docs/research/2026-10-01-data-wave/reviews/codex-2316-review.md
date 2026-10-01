# Second-eyes review — 2026-10-01 23:16 UTC wake

Reviewed U checker at W2 `d1e76a19a085d310ae41df3f62750f359424f8ec` (byte-identical at closing W2 `21249189`), D4 closed-row amendment `7690c6d2`, and selected coordinator corrections. Integration observed at `1089b1b3` initially, `68ddb9ed` at close. Active repositories stayed unchanged by this review.

## New measured gap: the repaired checker still ignores producer failures

The committed `scripts/check-ty-rule.py` **now rejects the original empty, error-only and truncated logs**, and its seven built-in controls pass. Its newly added `--tree` wrapper, however, calls each producer without inspecting `r.returncode` (`:224–228`). The aggregate mirror-log check only requires the three top-level scopes, so losing one of several Tools runs can still leave apparently sufficient evidence (`:133–143`). The fixture set is discovered with `glob`, with no check that each intended mirror fixture exists (`:233–234`).

Using an unchanged copy of the committed checker in an isolated temporary directory, substituted a small fake `lake` executable which emits controlled report text and returns specified exit codes. **No Lean, actual lake, generator or build ran.** The fake command is only fault injection at the subprocess boundary; it is not a fabricated record of actual Lean execution.

| Control | Expected checker exit | Actual |
| --- | --- | --- |
| Complete passing log | 0 | 0 |
| Real forbidden traversal in log | 1 | 1 |
| Empty/error-only/missing-gate inputs | 2 each | 2 each |
| Complete successful simulated producer suite | 0 | 0 |
| Main producer emits complete report, then exits7 | 2 | **0** |
| One Tools mirror producer exits7 silently; other producers succeed | 2 | **0** |
| One intended mirror fixture omitted from the isolated fixture directory | 2 | **0** |
| Omitted fixture restored, successful suite | 0 | 0 |

The two command-failure cases still print `0 violation(s)` and a success exit. The silently failed mirror case compares six mirror rows instead of seven without refusal. All runs are bounded to15seconds, serial. The source, fixtures, hashes, commands, per-case logs, fake-producer call log and results are under `2316-ty-rule/`; reproduce with `python3 .../2316-ty-rule/run.py` then `python3 .../2316-ty-rule/run-extra.py`. The latter temporarily moves only its isolated fixture copy and restores it in `finally`.

**Before acceptance use:** preserve producer logs but refuse immediately on every nonzero exit, naming the producer and status; verify the intended fixture/module inventory rather than accepting whatever a glob returns; keep these controls beside the prior missing-log controls. This is a specific checker evidence defect, not a new Lean theorem counterexample or proof that an actual build failed. It remains on W2's unmerged branch. Last-pass missing-log repair is real, but the entire evidence-production boundary is not yet closed.

## D4 amendment and earlier handoff corrections

Independent source review found no concrete defect in D4 `7690c6d2`: the empty requirement-row premise refers to the same checked program/root type, the reachable-state connector forwards it, and M7 retains both the premise and its separate empty host-table restriction. All three M7 conclusions remain unchanged. No proof of general M5/M6/M7 completion is inferred. Details: `2316-d4-review.md`; no independent compiler replay.

Main `296ad9fa` now explicitly supersedes the old unsafe-close placement with the public close in the brief and row151. Seat `1819fc16` corrects the stale helper docstring and narrows the Effect3 comparison to its three measured cases. The system-map schema literature row was also corrected to the bridge at main `9358b22f`. One minor historical wording slip remains in row151: the measured19→21 operation-count increase came from attempted voiding in the unsafe close used by scoped exits, whereas the appended explanation says “for the public path.” The review note records the exact replacement. This does not change the source result.

## Current activity and limits

Fresh screenshot and accessibility observations confirm the expected Claude project/session. Four visible code seats are finishing, and a derived-producer command was running. The coordinator is consolidating before starting the chapter-based documentation/formalization pass; nothing new is dispatched. D4's visible transcript is checking D2/D4 shared declaration placement, consistent with the known overlapping proof modules. The resource/process response is concrete: one seat per shared dependency group, at most two disjoint code seats, builds at integration instead of duplicate whole-root builds.

Git corroborates progress and stopping state: J2's receipt was integrated during this review; D2 now records its completed groups1–3 and explicitly owed remainder; D4 has its closed-row amendment and generated OCaml step committed; W2 has the checker and partial plain-block extras, with the rest not claimed finished. No changes or messages were made to Claude's work. See `2316-claude-activity.json` and `2316-worktrees.json`.

The campaign is still in integration, so the monitor continues. The proposed chapter map and future organization review are a new plan, not completed evidence that all semantic obligations have been enumerated. Earlier scope-post repair stays resolved separately from scope-membership validity and the remaining generic machine obligations.
