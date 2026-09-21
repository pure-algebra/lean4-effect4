# Foundations review verification receipt

The coordinator must know before dispatch: the pending
`Effect4.Program.Sched.M1Origin.actionAt_raceAll` proposition is false as declared.
The nearby theorem includes a source-location hypothesis that the obligation omits.
A checked counterexample is retained here; the production statement and its open marker
remain unchanged. This is a specification amendment to review, not a false accepted theorem.

Base and reviewed head: `10d5c009` on `refactor/phase1-phase3`.
Context range: `15cb510e..10d5c009`; focused final closure commits: `b2bf4cca`, `16090306`.
Initial worktree changes: modified `docs/STATE.md`, untracked
`docs/core/post-phase-c-synthesis.md`. The latter is preserved exactly as
`synthesis-as-received.md`. The research copy of the supplied synthesis was not overwritten.
No commit or push; no changes to source, Test, tooling, generated runtime or frozen declarations.

## Checked results

| Check | Result | Scope |
| --- | --- | --- |
| `lake build Effect4.Laws.Program.Typed.World Effect4.Laws.Run Effect4.Laws.Program.Guard.TraceOrigin` | exit 0, 345 jobs | Warm dependency build; diagnostics were replayed. Not a fresh whole-ledger search or trust sweep. |
| `lake env lean /tmp/Effect4FoundationProbe.lean` | exit 0 | Fresh kernel reflection and four theorem checks; retained source/log here. |
| `lake env lean /tmp/Effect4MemoProbe.lean` | exit 0 | Seven checked finite/arbitrary-store controls; retained source/log here. |
| `lake env lean /tmp/Effect4RaceObligationProbe.lean` | exit 0 | Three theorems, including negation of the actual instantiated frozen obligation's `.statement`; retained source/log here. |

Rerun the corresponding `.lean` paths in this directory with `lake env lean` from repository
root. They import current compiled modules. If relevant production source changes, build those
modules first. The probes are research files, not modules wired into Test.All.

### FoundationProbe

Kernel print confirms Preds has twelve fields and `Lean.isClass … Preds = false`.
RSavedOk's current/stack checks are independent. TaskOk and CmdOk discard resume target/token;
CaptureOk carries only env/context checks.

Theorems `resume_target_erased`, `command_target_erased`, `capture_location_erased` each print
`[propext]`. They quantify over every predicate bundle/world/expectation and the substituted
fields, so the information loss cannot be repaired by choosing a different predicate body
within the same erased arguments. This is not a proof that a separate strengthened machine
invariant cannot restore the missing relation; that is the proposed repair.

`conditional_not_monotone` has no axioms. The empty table satisfies a conditional lookup
predicate; an extending table introduces a false declaration. Coverage/support premises are
therefore owed wherever such predicates are claimed monotone. This theorem is a small model
of that variance claim, not a counterexample to the already proved World.le preorder.

### MemoProbe

No axioms: `ids_unique_before`, `ids_not_unique_after`, `identity_write_copies_first_map`,
`duplicate_ids_below_supply`.
`[propext]`: `fork_collision_step`, `identity_write_changes_duplicate_world`,
`actual_complete_differs_from_deleted_write`.

These witnesses are representable arbitrary Stores values, not claimed reachable from loadR.
They show that unique IDs alone are not preserved without an allocation-supply bound, that a
bound alone does not establish uniqueness, and that deleting the write changes an unrestricted
store operation. Initialization/preservation/reachability and the invariant-restricted old/new
connector are still unproved work; the probe does not claim otherwise.

### RaceObligationProbe

All three print `[propext]`: `decoded`, `frozen_raceAll_counterexample`,
`universal_missing_premise_false`. Root `.withFiber (.raceAll .nil)` at `rootPoint 0` decodes
to a race action with empty entrants and site `[0,0]`. The frozen obligation permits unrelated
`a = .getId`, then requires `a = .raceAll es`, which is impossible.

The smallest proposed amendment adds the actual source-location hypothesis explicitly to the
obligation, preserving its relation to `a`, in the same binder position as the backing theorem.
The amendment slice should register the counterexample in Test/Counterexamples/REGISTER.md
when promoting it to the production battery, inspect the adjacent three action obligations,
and retain old/refuted and new/checked statements separately in the receipt. This review does
not make that declaration-changing amendment or silently shrink the statement's domain.

## Inconclusive work, not acceptance evidence

An exploratory broad theorem-reference comparison was stopped (exit 130) after it failed to
produce useful progress promptly. A revised per-reference heartbeat-capped comparison was
also stopped (exit 130). Their source files are retained for diagnosis; **neither establishes
an exact-match total or a list of statements that would close**. A namesake validation pass
is not needed to establish the checked missing-premise defect. The plan consequently makes
no promise of 31 immediate closures.

The exploratory probes initially encountered unknown names, a dependent-structure proof that
needed reconstruction, and meta-program inference/lifting errors. Those attempts are not
proof evidence. The accepted logs listed above are from the corrected runs and contain no
`sorryAx` or errors. In particular, the capture relation was proved by reconstructing its two
fields, not by treating differently indexed structures as definitionally equal.

## Validation policy and remaining boundaries

No new CI lane or permanent gate was added. No OCaml build, generator, runtime-coverage census,
full Test build, full trust audit or repository sweep was run. The old receipt's coverage
numbers remain historical and are not republished as a current verified runtime total.
The new semantic/issue inventories are planning snapshots, not implementation coverage gates.
Focused theorem probes settle the structural questions; future work reuses existing checks
at the semantic changes they actually reach.

The full review and proposed sequence is `docs/core/post-phase-c-synthesis.md`.
`sha256.json` pins the retained input/probe/log files present when first saved; it does not
claim to hash itself or later planning inventories.

## Planning completeness and final document checks

The retained `semantic-inventory/` covers 452 pinned TypeScript source files and gives an
exact disjoint family assignment to all 137 root modules. Its saved consistency report checks
paths, source hashes, parsed name counts, syntax diagnostics and unresolved export-star
records. This is syntax and planning evidence; per-export/overload semantic analysis remains
planned work.

`design-issue-map.md`, `.json` and `.tsv` retain 194 records: 88 decisions, 101 design issues
and five Config questions. The full original status and required outcome remain in the JSON,
with workstream, contract prerequisites and next action. Historical recorded settlements are
not recast as freshly verified implementations. The map does not ratify decisions.

`review-consistency.json` records the final one-time checks: exact register ID coverage,
unique records, nonempty planning fields, correct source anchors, preserved original evidence
hashes, 14 accepted axiom reports with no errors/sorryAx, resolving document links, docs-only
Git changes and `git diff --check`. All passed. No new recurring check is installed.

The final protocol-design review adds an explicit construction dependency: source/body
admission precedes operation contracts and residual typing. Allocation certificates must
share the chosen type between precondition, postcondition and continuation. These are
source-grounded design obligations, not claimed compiled replacement definitions; settle
their shape on allocation/read-or-await and addressed fork/mask before broad expansion.
