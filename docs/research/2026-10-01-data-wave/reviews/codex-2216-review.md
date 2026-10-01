# Second-eyes review — 2026-10-01 22:16 UTC wake

Integration reviewed: `f1231fe9bf97c906191231f16e9bf8aeb1df3a19` on `refactor/phase1-phase3`. No active repository edits, builds, generators, compiler runs or messages to Claude. One bounded independent source reviewer checked W1 while the root checked U's new handoff.

## New measured finding: missing evidence passes the proposed traversal checker

U's `check-commit4-rule.py` returns success with `0 violation(s)` when given an empty log, a compiler-error-only log, or its own green fixture truncated before the exhaustive-match section. The unchanged green fixture succeeds, and changing one fold row into a forbidden recursive traversal correctly fails. This isolates missing-evidence validation from detection of ordinary violations.

The exact committed script and green fixture were copied from integration `f1231fe9` into `2216-ty-rule/`. Reproduce with `python3 /private/tmp/codex-second-eyes-2026-10-01/2216-ty-rule/run.py`. Each invocation has a five-second timeout. Commands, outputs and exit codes are in `results.json`; source revision and SHA-256 are in `provenance.json`. No Lean artifacts or host semantic assumptions are involved in this Python-only test.

| Input | Expected exit | Observed exit |
| --- | --- | --- |
| Existing green fixture | 0 | 0 |
| One forbidden traversal | 1 | 1 |
| Empty log | nonzero | 0 |
| Compiler error only | nonzero | 0 |
| Missing exhaustive-match section | nonzero | 0 |

Source: `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-type-language-probe/U/scripts/check-commit4-rule.py:38` initializes empty lists and ignores unrecognized lines; lines 57–84 declare success from absence of parsed violations. The defect is in a research checker, not an already-enabled production gate. It matters now because `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-wave/brief-W2.md:101` explicitly assigns promotion to `scripts/check-ty-rule.py`, for use by commit 4's acceptance check.

Recommendation before promotion: require successful evidence production and complete expected family/scope/section coverage, reject error or incomplete logs, and retain these missing-evidence controls beside the passing and real-violation controls. A fixed number of traversal rows is not the contract: removing hand traversals is the purpose of this work. Validate completeness separately from the number of violations. This is separate from Q's previously reported invalid-revision checker defect; Q's dispatch correction remains pending implementation.

## Meaningful resolution on W1's branch

At `03403dc87123627214bc13f9b3d33aaeefcd8eb9`, the earlier filter-annotation mismatch is repaired in the reader, normalizer and general exactness proof. Documentation-only check annotations are accepted; unknown and semantic annotations still refuse. Both accepting and rejecting controls exist. Exactness remains scoped to the named writer/normalizers and the encoder's successful domain. The broader normalizing public writer and old/new encoder-domain equality are not silently claimed.

Independent evidence: `2216-w1-review.md` names the exact source lines, theorems and controls. This tick was a committed-source review; execution results in W1's draft receipt are seat-reported, not independently rerun. W1 remains unmerged at the reviewed integration head.

## Activity and limits

A fresh Claude UI inspection failed because the Mac was locked and automatic unlock failed. No screenshot or accessibility snapshot was obtained; the last screenshot was not reused as current. Consequently live subagent progress and running commands could not be independently observed this wake.

Git still shows material activity: U merged; W1 committed; W2 committed variable-arity generation changes and continues editing; D2 added denotation lemmas; D4 and J2 have ongoing changes. Full timestamped correlation is in `2216-claude-activity.json` and `2216-worktrees.json`. D5's field census now tracks the five proposed state clauses; this is pending proof work, not evidence that all possible missing clauses have been ruled out. The specific scope-allocation post repair remains recorded as resolved; general M5/M6/M7, including M7's restricted scope, are not promoted to complete by this review. The campaign continues.
