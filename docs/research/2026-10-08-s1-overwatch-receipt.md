# S1 overwatch: shared context and honest proof reports

The reviewed editing laws pass their scoped checks.
The query's new root answer cites an inapplicable structural law.
The new planning report mislabels unfinished work and measures reuse differently from the later report.

## Base, scope, and ownership

Comparison base: `8785c6f9`.
Reviewed head: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
S1a is `351fb3f9`; S1b is `991d57da`; the planning note changes at `979be0ad`.
Review branch: `codex/s1-query-overwatch`.
Worktree: `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.

The read-only session inspection selects the active repository session by activity and verifies its working directory.
Its identifier is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50`.
The inspection reads bounded tails and ignores internal thinking fields.
Claude starts the splice implementation after the reviewed landings.
Its active files include the core root and the core and law files for `Program/Typing/Splice`.
That work remains outside this completed-slice review.
No message is sent to Claude.

The review follows the codebase-design, Lean reification audit, and breaker skills.
The sole Eff representation and the core/law import boundary remain unchanged.
No production source, owner ruling, root import, or generated artifact changes.

## Confirmed findings

### S1-QUERY-01: the root focus cites a law that cannot cover a block

Priority: P2.
Owner: `Tools.Query.answer`, `tools/Tools/Query.lean`, introduced by S1a's new focus behavior.
Contract: a query names a law only after deciding that law's premises.

The query now uses `Sketch.focusAt` from `src/Effect4/Program/Sketch.lean`.
At the root of an admitted definition block, it returns the whole block and its module type.
It still names `focusAt_typed` from `src/Effect4/Laws/Program/Typing/Focus.lean`.
That law requires structural `focusAt` and concludes structural `HasTy`.
The structural checker refuses every definition block.
The named law therefore cannot justify this returned root focus.

The retained control checks an identity definition and its invocation.
The module check accepts it, and the query answers the root focus with `focusAt_typed`.
Structural `focusAt` answers none on that same root.
A plain program supplies the positive control; an invalid address supplies the refusal control.
The controls compile and use the public query function.

Consequence: a consumer can receive a proof label that does not cover the returned program.
This finding concerns proof attribution, not a false acceptance by the module checker.

Smallest correction: split root and part attribution.
At the root, use `Sketch.focusAt_nil` with the module-check premise and `checkModule_sound` where a typing conclusion is needed.
Inside a part, use `focusAt_typed` at the resolved part's signature and environment.
Retain the current no-law answer where the corresponding premise does not hold.

### S1-PLAN-01: the plan calls an unfinished helper proved

Priority: P2.
Owner: `predict` and `#landing_plan`, `tools/Tools/LoadPaths.lean`, added in `991d57da`.

A local helper depends on a tagged planned goal.
The public command lists the goal as owed but labels the helper under `local steps, proved`.
`ProofGraph.standing`, `tools/ProofGraph/Goal.lean`, correctly labels the same helper modulo that goal.
The retained control checks both outputs and the goal dependency.

Consequence: the planning display disagrees with the existing proof-status definition.
Smallest correction: use `ProofGraph.standing` for local helpers and external dependencies.
Keep proof standing separate from whether a semantics registry root uses a theorem.

### S1-PLAN-02: predicted and measured reuse count different things

Priority: P2.
Owner: `predict`, `#landing_plan`, and `measure`, `tools/Tools/LoadPaths.lean`.
The planning docstring and `docs/research/2026-10-08-load-paths.md` claim that both commands measure the same quantities after landing.

Two local helpers reuse one external theorem.
Their top theorem uses both helpers.
The plan reports 33 percent: one distinct external theorem against two local helpers.
The report returns 50 percent: two external uses against two local uses.
Adding another module gives 60 percent in the report while the plan remains at 33 percent.
The proof declarations do not change between those commands.

Consequence: the difference is a measurement mismatch, not prediction error or added work.
Smallest correction: share one measurement function and keep the selected roots and module grouping identical.
If both measurements remain useful, name them separately and remove the equality claim.

### S1-PLAN-03: ordinary data is accepted as a theorem top

Priority: P2.
Owner: the `#landing_plan` elaborator, `tools/Tools/LoadPaths.lean`.

The public command accepts `Nat`, `Nat.zero`, and a data definition.
The data definition receives a 100 percent reuse report because its value uses a theorem.
The command correctly refuses an unknown name.
It never checks that a resolved top belongs to the authored-theorem population.

Smallest correction: validate theorem kind before producing a theorem-planning report.
The retained fixtures exercise accepted theorem inputs, ordinary data, and the unknown-name refusal.

## Shared structure revealed by the examples

The existing Queue definition client in `Test/Program/PartsControls.lean` passes the focused battery.
Its calls need the enclosing definition signature, just like the smaller retained query witness.
The author should not reconstruct that context separately for each tool operation.

A remaining slot reader illustrates the cost.
`Tools.Query.slotsAt` still walks the whole program at the empty application's signature.
After a definition invocation, the new focus answers but the slot reader returns no slots.
The same slot-bearing program behind an inline value returns three slots.
The retained controls check both cases.
The S1 plan names check, table, and refusals; this is an extension gap, not an explicitly deferred regression.

The concrete consolidation is a resolved location shared by focus, slots, and filling checks.
It should reuse `Eff.partAt`, keep root module checking distinct from structural part checking, and store no new program syntax.
The following is proposed interface notation, not an implemented API:

```lean
let location := sketch.inspect app path
location.focus
location.slots
location.checkFilling replacement
```

The location owns the signature, environment, addressed node, and applicable proof scope.
This removes repeated context reconstruction from callers.
A shared proof-report analysis likewise owns theorem kind, proof standing, dependency uses, and selected roots.
The planning and reporting commands should render that common result.

## Verification

The root runs:

```sh
LEAN_NUM_THREADS=3 lake build Tools.Query Test.Program.QueryControls
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-s1-query-review-probe.lean
```

The narrow build exits zero and reports 773 jobs.
The retained query probe exits zero; its source contains 24 finite guards.
Its output is `2026-10-08-s1-query-review-output.txt` beside this receipt.
The first research draft misses a Wire namespace import; the corrected draft supplies it and passes.
That draft failure is not detector evidence.

The independent Sketch review is commit `9460913f56168bdce7408ec136b1abcff98dc60d` on `codex/s1-sketch-review`.
Its receipt is `git:9460913f:docs/research/2026-10-08-s1-sketch-review/receipt.md`.
Its narrow build reports 857 jobs.
Its 51 finite guards and five existing-law readers pass.
The scoped axiom check covers all 365 declarations of the two changed law modules, including generated declarations.
It finds no missing declaration and reaches only `[propext, Quot.sound]`.
The root separately replays that scoped audit and reproduces the retained output exactly.

The independent planning review is commit `3b31c6c2` on `codex/s1-load-review`.
Its receipt is `git:3b31c6c2:docs/research/2026-10-08-s1-load-review-receipt.md`.
It retains the public-command fixtures, compiler runner, and full output.
The root separately replays the runner and reproduces the retained output exactly.
The positive fixture proofs have empty axiom sets.
The unfinished fixture controls reach `sorryAx` only through their deliberately tagged planned goals.
Those fixture goals are test inputs, not added Effect4 claims.

## Limits and checkpoint

The substantive S1a and S1b review now reaches `979be0ad`.
No confirmed Sketch or Parts implementation defect is found within the reviewed statements and controls.
The findings above remain open in the query and planning reports.
The ongoing splice implementation is observed, not accepted by this review.

Filled-block conservativity remains explicitly open.
A root block-to-block fill can check, but the existing fill theorem requires a structurally checked filling.
Neither boundary is reported as an S1 regression.
The plan's external-dependency walk deliberately stops at external theorems.
An external theorem can therefore hide unfinished work; this is a checked scope limit, not an omitted local-goal defect.
Earlier unchanged load-report findings remain in the planning review's historical references.

The explanation exception repair remains on the isolated preparation branch at `8bb77baa`; it is not in the reviewed primary head.
PartitionedSemaphore remains a checked preparation packet at that same branch, not a production module.
The current library has its initial Stream profile, with Pull, Channel, and the larger Stream/Sink stack still ahead.
The next module work must retain partial reservation, cancellation settlement, and synchronous wake delivery.
Those shared waiting behaviors serve the semaphore, PubSub, and streaming work.

No full sweep, whole-library axiom gate, merge, push, production repair, or TypeScript check runs in this review.
