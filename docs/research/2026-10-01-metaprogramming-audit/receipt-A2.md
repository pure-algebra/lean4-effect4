# A2 receipt — reuse Lean’s simp-argument parser

**Before merging:** this slice changes five grammar declarations only. The existing tactic
fallbacks and every theorem statement/body are unchanged. The larger `simpArgs` production
would have admitted trailing commas; this change uses `simpArg` within the existing delimiters.

Branch base `8c9be258`; preceding A4 commit `45e9b532` (formerly `3640adcb`, rebased onto the
coordinator’s new base with unchanged source inputs). Implementation is this receipt’s commit.
Changed production file: `src/Effect4/Laws/Machine/Handles.lean`.
Controls: `Test/Machine/Runtime/HandlesContract.lean`, already reachable from Test.All.
Built-in source: Lean 4.33.1 `Init/Tactics.lean:703–710`.

## Tests

Exact commands and outputs are in `evidence-A2/`. All runs used one compiler, `-j1 -M4096`,
warnings as errors, with per-process bounds. Baseline and updated syntax controls both passed:
37 accepted forms and 20 refusals, covering all five grammars, empty/omitted lists, ordinary,
reversed, erased and star arguments, multiple arguments, and malformed/trailing-comma cases.
The first probe draft used a nonexistent Except.isError convenience; corrected to isOk before
taking either baseline or updated result. No production repair was needed.

Handles compilation exceeded its initial 180-second bound and was terminated cleanly; a
600-second bounded retry passed in 352.389 seconds. Its ledgers remain 9/1/9 proved, zero open.
All six non-umbrella direct consumers compiled: StoresValue, Program.Admit,
Program.Handles.Alphabet, Guard.FrameOwned, Typed.World and Machine.Folds.Val.
The existing HandlesContract battery, including the new grammar cases, passed.
An additional cache check compared 998 source/compiled-file hashes in the 347-module scoped
closure against their build receipts; zero mismatches. Rebuilt modules use their fresh command
receipts instead of stale traces. No full Laws-root/battery build or whole-tree gate ran.

No theorem was edited and no new theorem was introduced. The change is grammar reuse, not a
claim about runtime safety or about the currently unmeasured fallback arms. A3 remains a
separate instrumentation/proposal task; the tactic bodies stay exactly as before.
