# Ledger: Codex's review of the session composition plan, and where version 2 takes each finding

Status: ledger (history, not authority). Input: `codex-review.md`, read at main `ec39923a7` and
authoring `8984bd15e` with the uncommitted repair. Output: `plan.md` (version 2). The coordinator
reread the controls R1 to R7 in `review-probes/BranchControls.lean` and the wrapper proof in
`review-probes/CoreSketches.lean`. `review-probes/continued-results.json` records exit 0 for all
fifteen probe commands.

## The controls

| Control | Finding | Disposition | Plan place |
| --- | --- | --- | --- |
| R1 | an omission's revert restores the program and keeps the new hole row | adopted: the observation is named program-only | §3, S1 |
| R2 | a replay of edits alone leaves a stored replaced program unchecked | adopted: the proof field covers the validating transition | §3, S1 |
| R3 | two histories share identity and length with different sketches | adopted: a snapshot is its origin and history; the base guards stay | §3, §4, S2 |
| R4 | a mixed batch reports an error and keeps the accepted fill | adopted: per-item outcomes inside a successful answer | §6, S3a |
| R5 | a refused run command grows the journal and phases | adopted: a successful "played" answer carries the phases | §6, S3a |
| R6 | root-type agreement is too weak at dependent `bind` children | adopted: exact certification at the fixed base stays | §4 |
| R7 | equal canonical materializations do not make raw orders commute | adopted: D6 cited at its own strength | §4 |
| R8 | `locate` gives no place for an empty digest string | adopted: root path and reason as the fallback | §7, S3b |
| R9 | the translator refuses a request-dependent answer function | adopted: flat `Request` and `Answer` | §6, S0 |
| R10 | restoring a draft's program after an omission changes the checker's answer | adopted: checker restoration needs a signature-support premise | §3, S1 |
| R11 | the rendered schema and its digest miss wire-tag changes | adopted: the tag guard stays; C4 waits for `render` | §7; `docs/research/2026-10-17-ocaml-estate-review/cas/README.md` §3a |
| R12 | `Option Unit` prints `none` and `some ()` alike | adopted: no null alias in a field profile | §7, S3b |
| R13 | `Run.Kit.admit` omits formation by design | adopted: `start` calls `admitProgram` | §5, S4 |

## The verdicts on version 1

| Section | Verdict | Disposition |
| --- | --- | --- |
| opening and question | amend | §2 states reachability as an extra invariant |
| what was read | amend | §7: `read?` decides, `locate` diagnoses |
| findings 1 | holds | kept |
| findings 2 | amend | §3: the history invariant |
| findings 3 | holds | §12 places the tool's claims |
| findings 4 | amend | §2: free-monoid action and Mealy machine; §4: D6's strength |
| A | holds, amended | §2 |
| B | amend; blanket undo refuted | §3 |
| C | amend | §4 |
| D | amend; blanket refusal refuted | §6 |
| E | holds, amended | §9 |
| F | amend | §10: Z, S0, S5a, S4 before S3a, S3 split |
| G | holds, amended | §11 H3: the repair is a baseline, not the specification |
| H | recommendations | §11 |
| limits | amend | "What this plan does not establish" |

## The recommendations

| Review place | Recommendation | Disposition |
| --- | --- | --- |
| §3 reuse table | each piece reuses its named owner; the tool state is the one new module | adopted; the reuse table stands as the plan's owner list |
| §4.1 | share the shape and the list laws; the coalgebra stays an adapter in Laws | adopted, §2 |
| §4.2 | proof field over the validating replay; explicit revert selection | adopted, §3 |
| §4.3 | constructed witness; lifecycle table; rebase deferred with its requirements | adopted, §4 |
| §4.4 | one refusal wrapper; three outcome kinds; origins at start; distinct run identifiers | adopted, §5, §6 |
| §4.5 | `RespondsTo`, `serve_answers`; field profile; one representation per field; fixtures | adopted, §6, §7 |
| §4.6 | reuse `censusTheorems`, `auditedFacts`, the axiom walker; inventories in two environments | adopted, §9 |
| §4.7 | the canary first; whole-package abstraction; Base through `targetLibrary` | adopted, §8; Base as in the estate plan §2.7 |
| §4.7 table | `Core.Validated`, `Base.Result`, `Base.Comparator`, `Core.Stable_unit_test`, Incremental | adopted as implementation patterns; Incremental gets its own design pass after S3a, at the owner's steer |
| §4.8 | six claim groups, each placed in its slice | adopted, §12 |
| §6 | the revised slice order | adopted with slice Z added |
| §7 H1 to H4 | generated wire; append-only revert; hold integration; no module yet | adopted, §11 |

## Added by the coordinator

| Item | Reason |
| --- | --- |
| slice Z: commit the repair first | Codex notes the commit hash alone does not identify the tested repair |
| H5: who builds | the authoring branch belongs to the authoring coordinator's worktree |
| §8: `E4_host.serve` and `Tool.serve` kept distinct | two transitions share a name across the estate and the tool |
| S0 depends on D-11 | the native tool uses the estate plan's export model |
| the Incremental design pass | the owner asked for a deep pass before any integration, 2026-10-17 |
| slice Z: `Tools.View.Build.requests` sends a target | the repair refuses a targetless `fill`, and the build frames send one per sub-program (survey, read in the authoring worktree) |
| S4: one snapshot-to-`Built` declaration | the tool's `start` and `run` arms each assemble a `Built` by hand; only `start` sets `rowNames` (survey) |
