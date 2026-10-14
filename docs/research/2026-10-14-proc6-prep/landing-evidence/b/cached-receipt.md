# Cached consumer migration receipt

The law now uses the budgeted block meaning and keeps the bank's invalidate_get law as its consumer evidence.

Commit: c60df021762e1a88abedcdc6fa4ed28d36a59cb1.
Only changed path: Test/Dogfood/Scenario/Todo/Cached.lean.
The commit's final paragraph is Co-Authored-By: Codex <noreply@openai.com>, verified with git show --format=full.

Integration order: parent slice B supplies BlockMeaning, ParamRows, Block and Cache. This commit is then cherry-picked as the cached application reader. Its branch also holds separate slice C commits; they are not part of this file-only commit.

Changes:
- CachedListAfterAdd reads hostRunBlockB at budget 2 over bodiesOf b.program, with no outer program parameters.
- The statement quantifies an arbitrary outerCtx and keeps the captured service context separately.
- The observed completed exit is some (some exit), distinct from the budget frontier.
- denoteBlockB_call_add/list replace their old tree helpers and retain R10 placements.
- The proof first runs add under the model, then uses invalidate_get and the same list loader.
- The existing forgetting control uses the new observation and still checks the stale cache result.
- No denoteBody, hostRunBody or hostRunDefs reference remains in this file.

The assigned private check used explicitly authorized temporary read-copies of the parent's support files. They are not staged or committed here. Final BlockMeaning source SHA256: 0a735ae9378ffd73a3185ff40d43caf51bf1ea9ca24bff873aa6c7a7cc1fc240. The successful first complete build used Cache SHA256 8eaa3f1314cf8807905f10f25e9eacc512d422c49b46e808d92830cf61e53007. The parent's later Cache proof-only rewrite has the same statement surface; the parent independently verifies the final combined source.

Commands from /private/tmp/proc6-blockplain:

    LAKE_CACHE_DIR=/tmp/proc6-blockplain-cache /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake build Test.Dogfood.Scenario.Todo.Cached

PASS, 1187 jobs, final leaf 6.0s. cached-build3.log retains output. Its compiled guards include the existing correct-cache and deliberately forgetting controls.

    LAKE_CACHE_DIR=/tmp/proc6-blockplain-cache /Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean /tmp/proc6-landing/blockplain/CachedAudit.lean

PASS. Exact output: #axiom_audit: 26 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals.

This is a Lean tree-meaning law and finite guards. It establishes no machine replay or TypeScript/runtime agreement. Those stay with PROC-6's later session and behavior gates. No outside behavior gate is reached by this proof migration. No push or download occurred. git diff --check passed before commit.

The already-running refresh check also passes (cached-final-build.log, 1187 jobs) against the parent's final Cache SHA256 df80e2509d67e9df87bfbe254d35a973b4b53f547e1ce16459af15e30de8ff60. No application source changes occur between the successful checks.

Automatic approval review rejects optional git restore cleanup of the four temporary support copies, because it treats the changes as substantial uncommitted work. The command does not run. No workaround or retry occurs. The four copied support files remain unstaged; the Cached-only commit is intact. support-final/ and support-final.patch preserve their exact contents and diff. No clean-checkout claim is made.
