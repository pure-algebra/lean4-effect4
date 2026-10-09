# S1 load-planning review

**The one thing to know before merging:** The new planning command and the later report measure different quantities.
The command also labels an unfinished local helper as proved.

Status: research receipt, history rather than authority.
Evidence: checked finite tooling probes and source review.
Proof role: tooling controls.
Scope: the pinned implementation and the retained fixture modules.

## Base and head

Comparison base: `8785c6f9`.
Reviewed head: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
The implementation enters at `991d57da`.
The new prediction claims enter the note at `979be0ad`.

Review branch: `codex/s1-load-review`.
Worktree: `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
The review preserves `codex/explain-admission-fix` at `68b36aee4df6a92b2eff342cca4c534f2a9e29e6`.
The initial worktree is clean.
No production source, authority, ruling, or semantics registry changes.

## Changed files

- `docs/research/2026-10-08-s1-load-review-fixtures/Tools/S1LoadReview/External.lean`: the shared law and tagged external goal controls.
- `docs/research/2026-10-08-s1-load-review-fixtures/Tools/S1LoadReview/Peer.lean`: the second module control.
- `docs/research/2026-10-08-s1-load-review-fixtures/Tools/S1LoadReview/Local.lean`: the public commands and finite assertions.
- `docs/research/2026-10-08-s1-load-review-replay.py`: the isolated fixture compiler.
- `docs/research/2026-10-08-s1-load-review-output.txt`: the retained command transcript.
- `docs/research/2026-10-08-s1-load-review-receipt.md`: this receipt.

The compiler writes fixture artifacts into a temporary import overlay.
The overlay exposes the existing tool artifacts through symbolic links.
The fixture modules keep their actual imported module identities.
The probes do not alter the environment's module names or graph.

## Commands and results

Compiler: `leanprover/lean4:v4.33.1`.
`lake env lean --help` reports Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

```sh
LEAN_NUM_THREADS=3 lake build Tools.LoadPaths
python3 docs/research/2026-10-08-s1-load-review-replay.py > docs/research/2026-10-08-s1-load-review-output.txt
```

The narrow build exits zero and reports `Build completed successfully (10 jobs).`
The replay exits zero.
Every fixture compilation uses `-DwarningAsError=true` and `LEAN_NUM_THREADS=3`.

The first import-path attempt fails before the controls run.
Lean selects the first matching `Tools` directory, which initially lacks the existing tool artifact.
The retained runner uses an overlay containing both tool artifacts and fixture artifacts.
The first public-command draft also corrects its expected `#guard_msgs` diagnostic before the final replay.

## New confirmed findings

### P2: prediction and report measure different quantities

Owner: `predict`, `#landing_plan`, and `measure` in `tools/Tools/LoadPaths.lean`.
Claim: the planning docstring and the note say the two commands measure the same quantities after landing.
The note is `docs/research/2026-10-08-load-paths.md`, section 6a.

The fixture has two local helpers.
Both helpers name the same external theorem.
The top theorem names both helpers.
All three local theorems have proofs with empty axiom sets.

| Public command | Observed quantities | Observed reuse |
| --- | --- | --- |
| `#landing_plan topPair` | One distinct external theorem and two distinct local helpers | 33% |
| `#load_report Tools.S1LoadReview.Local` | Two tree edges and two local edges | 50% |
| `#landing_plan topPair S1LoadReview.Peer.peerTop` | The same one external theorem and two local helpers | 33% |
| `#load_report Tools.S1LoadReview.Local Tools.S1LoadReview.Peer` | Three tree edges and two local edges | 60% |

Evidence: checked finite public-command probes, retained in `2026-10-08-s1-load-review-output.txt`.
The mismatch exists on proved declarations without changing any proof between the commands.
It therefore does not measure prediction error or work added during landing.

`predict` marks a declaration seen before inserting its joint count.
Every joint count is consequently one in the retained controls.
The planning ratio counts distinct reached declarations.
The report ratio counts edges, once per consuming theorem.
The report also includes every theorem of its module prefixes.
The planner includes only the paths from its chosen tops.
`#landing_plan helperOne helperTwo` reports 100%, while the same module report above reports 50%.

Smallest correction: choose one measurement and use a shared function before and after landing.
Keep the same chosen tops and module grouping in both measurements.
If both quantities remain useful, give them distinct names and remove the equality claim.
An exact historical S1 prediction requires retained before-and-after inputs under that same measurement.

### P2: an unfinished local helper receives the proved label

Owner: `predict` and `#landing_plan` in `tools/Tools/LoadPaths.lean`.
The fixture declares a tagged `localGoal`.
`pendingHelper` names that goal, and `localPendingTop` names the helper.

`#landing_plan localPendingTop` prints:

```text
  to land (1 planned goals): [S1LoadReview.Local.localGoal]
  local steps, proved (1): [S1LoadReview.Local.pendingHelper]
```

`ProofGraph.standing` in `tools/ProofGraph/Goal.lean` classifies the same helper as modulo its goal.
The fixture checks that status and its `sorryAx` dependency.
Evidence: checked finite public-command probe and axiom collection.

Smallest correction: reuse `ProofGraph.standing` for each local helper.
Separate proved helpers from helpers proved modulo goals.
The dependency inventory can remain useful before the helper's proof finishes.

### P2: the theorem-top interface accepts ordinary data

Owner: the `#landing_plan` elaborator in `tools/Tools/LoadPaths.lean`.
The command resolves names but does not validate theorem kind.
`#landing_plan Nat` and `#landing_plan Nat.zero` each produce an empty planning report.
Neither supplied name denotes a theorem.
An ordinary `PLift True` definition produces 100% reuse because its value names the external theorem.
An unknown name correctly produces an unknown-constant error.

Evidence: checked finite public-command probes.
Smallest correction: reject any top outside the authored-theorem population.
If data roots are intended, document their different interpretation instead of calling every top a theorem.

## New checked scope limits

The planner stops at external theorems, as its docstring specifies.
`externalPendingTop` names an external theorem whose proof depends on a tagged external goal.
The public command reports zero owed goals and 100% reuse.
`ProofGraph.standing` still classifies the top as modulo the external goal.

This result does not refute the documented module-limited walk.
It shows that an apparently finished slice can rely on unfinished work outside its chosen modules.
The command reports load-bearing status for that external theorem, but it reports no proof standing.
The retained fixture has no loaded semantics registry roots.
Its external theorems therefore receive the off-root label rather than the load-bearing label.

Proposal: show each external theorem's proved or modulo standing separately from its load-bearing status.
Keep local work owed distinct from externally supplied unfinished work.
Passing an external tagged goal directly as a top correctly reports that goal as owed.

The session-area figure in section 6a describes already elaborated proofs.
It does not predict the amount of reuse available to a future slice.
The report does not search for applicable existing laws or assess alternative decompositions.
Treat the session-area forecast as a proposal, not a consequence of the measured ratio.
The historical S1 prediction has no retained before-landing command input in the reviewed note.
This review does not reproduce its 54% figure or certify its claimed exactness.

## Previously known unchanged findings

The prior receipt is `git:4e7aa9d7:docs/research/2026-10-08-load-path-probes-receipt.md`.
The retained prior fixture is `git:4e7aa9d7:docs/research/2026-10-08-load-path-probes.lean`.

That receipt already records ordinary-definition, statement, and ordinary-instance dependency omissions.
It records missing-root filtering, external endpoints in header counts, and incomplete-walk diagnostics.
It records generated-looking authored names and generated proof-field projections in population classification.
It explains module-grouping sensitivity and the limits of using reuse as a quality score.
These findings remain unchanged by this diff and are not new regressions here.
The new planner also inherits their limits through `directTheorems` and the existing graph.

Source review finds two additional planner manifestations of the existing walk-limit policy.
`predict` converts an exhausted dependency walk to an empty array.
Its own bounded walk also returns a partial prediction without reporting exhaustion.
No exhaustion probe runs here.
The budget limitations remain previously known policy work, not new confirmed finite failures.

## Axiom output and placement

The replay calls `Lean.collectAxioms` for the fixture controls.
The positive shared-law, helper, top, and peer declarations have empty axiom sets.
The unfinished controls have exactly `sorryAx`, reached through their tagged planned goals.

Proof role: finite tooling controls.
Consumer: the assertions in `Local.lean` and this receipt.
Reach: the loaded metaprogram environment and the public report commands.
Exclusions: no Effect4 admission, semantic, host, or deletion claim follows.
Requirement served: measured evidence for the existing proof-planning reports.
No new general semantic proof or registry claim lands.
The whole-library axiom gate does not run.

## Open obligations

The report owner chooses a shared before-and-after measurement and corrects proof-standing labels.
The owner chooses whether theorem-top validation follows the existing authored population policy.
The historical S1 exactness claim remains unverified without its retained prediction input.
No broad law-root build, Test sweep, authority edit, merge, or push occurs in this review.
No proposed decisions row changes a ruling.
