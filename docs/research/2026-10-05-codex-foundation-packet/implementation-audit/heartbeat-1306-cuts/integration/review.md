# Recovery and mask census integration

No new actionable issue appears at frozen main `601ed7c5830d22154fdd68e0b7e062c67407b9dc`.
The monitor reads source and saved results. It runs no project command and edits no repository file.

## Compatibility recovery

Commit `6b2b5cda` adds one policy name: `harness/truth/corpus-results.tsv:g102`.
The policy's only other change is its explanatory comment. The comparator implementation stays unchanged.
The earlier packet independently found two changed cells, with every outcome unchanged.
This repair names the previously omitted row; `g246` was already named.

The retained first check refuses the unnamed `g102` change and exits 2.
The retained retry passes all four clauses and all 27 controls, then exits zero.
Its output calls the two permitted row changes “verdict moves.” Neither changed cell is an outcome column.
The retry compares the working tree against `3a2616f1`, before the repair commit.
The saved source and committed policy agree on the repaired entry.

The transcript records the human enabling permissions in Claude, followed by a successful shell probe.
This records recovery in that session. It grants no implementation permission to Codex.
Row 274 is now committed, resolving the filing left pending in the previous packet.

## Partial mask census

Commit `25b16272` adds `interrupt.uninterruptible-mask` with disposition `owned` and coverage `partial`.
It joins five existing witnesses. The source adds five census labels to their docstrings.
Removing those labels recovers the entire previous law module byte for byte.
No theorem statement, proof body, hypothesis, or proof status changes.

The monitor independently verifies the stored upstream span and generator digest without running the producer.
The span is `internal/effect.ts:4340-4352`; its digest is `276d40c762a093ac1d675da7e1a2b6146abc697e589bef4bebf10348c19b3691`.
Every previous census row remains identical.

The first narrow check fails because the coverage module lacks the witnesses' import.
The final source adds that import. The retained rerun verifies the projection and the join, then exits zero.
The subsequent default build completes 990 jobs and freshly builds `Test.All`.
Its audit checks 740 modules and 87,690 declarations, with 24 planned goals and 11 dependent declarations.
Semantic and test axioms remain limited to `propext` and `Quot.sound`.
The existing exact implementation boundary still permits `Classical.choice` in 17 modules and 23 declarations.

The sanctioned report records 138 census rows, two excluded, and denominator 136.
It records 132 green, three partial, zero absent, and one diverged.
The new row explicitly keeps both missing connections:

- No theorem relates an arbitrary compiled mask body to native `uninterruptibleMask` on a stated target observation.
- No run theorem gives restoration after an arbitrary nested body.

These measurements do not establish either missing connection.

## Dispatch and requirements

Tracked `docs/STATE.md` assigns MASKPOP to Claude's `seat/maskpop`, from `6b2b5cda`.
Its tracked brief requires a fixed base and an empty scratch stack for the pop theorem.
It excludes the lift to runs, completed exits, cleanup multiplicity, delivery, budgets, liveness, and host behavior.
Its consumers remain the later run lift, the waiting wrapper, and Semaphore's protected permit.
The saved dispatch result confirms that the Claude seat launched; it establishes no implementation result.

The same state document preserves Codex's read-only limit until the owner addresses Codex directly.
Nothing in this review changes that limit.

All thirteen requirement titles and ordered `openParts` lists exactly match the previous integration packet.
Each list also matches its registry declaration.
Both the complete registry and generated semantics report remain byte-identical to `3a2616f1`.
The census change closes no requirement or open proof obligation.

## Evidence boundary

`manifest.json` preserves source, patches, and original result logs with SHA256 hashes.
`tool-evidence.json` preserves exact command/result references and timestamps.
`result-lines.json` pins result lines without their terminating newline.
`requirements.json` preserves all thirteen unchanged lists.

The relevant retained completion times are:

| Result | UTC time | Transcript line |
| --- | --- | --- |
| Compatibility retry | 12:56:56.976 | 20447 |
| Explicit retry exit and document check | 12:57:06.207 | 20451 |
| Census retry | 13:02:28.929 | 20597 |
| Sanctioned census report | 13:02:40.965 | 20609 |
| Default build and fresh test-root audit | 13:03:38.849 | 20619 |
| Final state and dispatch filing; document check | 13:05:37.911 | 20692 |

Later seat work, the engine comparison, and MASKPOP's unfinished proof work are outside this review.
