# HO-3b proof completion review

Repair two helper proofs before merging this draft.
The cycle-aware audit rejects their dependency on `Classical.choice`.
The isolated replacement proofs pass the prescribed axiom boundary without changing either statement.
[repair.patch](repair.patch) contains the proposed two-line repair.

## Reviewed state

Base: `000bcd7ad68e7bbbe4f3478831982a7f9f2f1a42`, branch `claude/ho3`.
Comparison: review commit `0a29433ac412fe875bae18a57330ac96f88b0876`.
The owner has no new landing at the captured checkpoint.
`owner-draft.json` retains the reviewed working changes.
`checkpoint.json` records ownership, findings, and the comparison.

Only `src/Effect4/Laws/Codegen/PrintTyped.lean` and `src/Effect4/Laws/Codegen/PrintReadable.lean` change after the previous packet within this review's source scope.
The executable sources retain their previous bytes.
Claude reports a successful law build, then repairs batteries affected by earlier context changes.
That report remains distinct from the independent checks here.
Those later battery edits are outside this review.

## Confirmed finding: HO3b-TRUST-01

Evidence status: checked axiom-boundary failure on the captured working draft.
Proof role: compatibility.
Scope: the existing R8 reconstruction claims and their imported proof dependencies.

`rowPrint_inv` and `rowDom_inv` in `src/Effect4/Laws/Codegen/ReadPrint.lean` reach `Classical.choice` through `Pi.instNonempty` and `Classical.ofNonempty`.
The audit reports 43 affected declarations among 5535 inspected declarations.
The affected consumers include `read_print`, `readTyped_printTyped`, and `Api.printModule_roundTrip`.
The claim audit also rejects `eraseJoinArgs_printTyped`.

This result violates the project's trust rule.
It does not establish a false theorem or a runtime mismatch.
Both changed proof modules compile successfully.
A successful build does not replace the axiom gate.

## Smallest repair

Both invocation conclusions quantify a callback function.
The generic function `Nonempty` instance obtains its result through `Classical.ofNonempty`.
Supply a constructive local instance before proof search in each helper.

```lean
-- rowPrint_inv
letI : Nonempty (Carrier .effs) := ⟨fun _ => .ok []⟩

-- rowDom_inv
letI : Nonempty (Dom .effs) := ⟨fun _ => none⟩
```

These local proof witnesses change no program, API, or emitted TypeScript.
The hypotheses and conclusions remain identical.
[Repair.lean](Repair.lean) checks the alternatives against the owner's current definitions.
[REPAIR-PLAN.md](REPAIR-PLAN.md) places both helpers and names their consumers.

Splitting the selected row and its output before proof search does not suffice.
[SplitControl.lean](SplitControl.lean) retains that failing control.
The passing replacement audit checks 58 declarations within `[propext, Quot.sound]`, with no planned goals.
The original failing audit remains in [audit.log](audit.log).

Apply the patch in the owner worktree after reviewing it.
Rebuild `Effect4.Laws.Codegen.ReadPrint` and its changed proof consumers.
Repeat [Audit.lean](Audit.lean) against the resulting artifacts.
The isolated helper audit does not establish that the rebuilt downstream graph passes.

## Source review

The independent source review finds no dropped public premise in the inspected proof changes.
`source-review.json` records a GPT-6.1 Sol review and six unchanged public theorem statements.
The statements still require readable source, lawful spelling, and successful TypeScript printing where applicable.
The later axiom gate supplies the separate trust finding above.

`print_node` in `src/Effect4/Laws/Codegen/PrintReadable.lean` obtains callback prints from its existing child induction.
`childEnv_template_depth` in `src/Effect4/Laws/Codegen/PrintTyped.lean` now covers invocations through shared depth data.
Its proof no longer excludes invocation nodes.
The invocation erasure proof uses `siteFocused_child` from the same file.
Its recursive assumptions apply to smaller printed children.
They do not assume the parent conclusion.

[PROOF-DAG.md](PROOF-DAG.md) gives the dependency outline.
[PLAN.md](PLAN.md) records the five placement points for the existing claims.
This review introduces no registry claim or planned goal.

## Verification

| Check | Result | Evidence |
| --- | --- | --- |
| Rebuild `PrintReadable` from copied source | Pass | `initial-attempt.json` |
| First `PrintTyped` rebuild | Timeout after 240 seconds | `initial-attempt.json` |
| Retried `PrintTyped` rebuild | Pass after 433.217 seconds | `checked-results.json` |
| Cycle-aware audit of affected proof modules | Rejects two root dependencies and their consumers | `audit.log` |
| Split-only helper control | Compiles; audit rejects both helpers | `repair-controls.json` |
| Constructive helper replacement | Compiles; audit passes | `repair-controls.json` |
| Statement comparison | Both replacement statements match the originals | `repair-statements.json` |
| Audited input hashes after verification | Unchanged | `inputs-after.json`, `final-source-check.json` |

The first retry detects changes only in two build trace logs.
`drift-before-retry.json` retains that comparison.
The final build and audit observe no source or compiled-input change.

Run the retained repair controls from this review worktree:

```sh
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-2122/run_repair.py
```

The runner uses the owner's compiled definitions and this worktree's matching dependency packages.
It compiles separate probe modules and checks both expected audit outcomes.
It refuses unexpected outcomes or changed recorded inputs.

## Remaining work and limits

The findings in [the previous packet](../followup-2016/README.md) remain unchanged.
The new proof graph does not repair `HO3b-SPINE-01` or `HO3b-TERM-01`.
The reconstruction claims permit a printer refusal because successful printing remains a premise.

Repair the empty callback list before claiming the widened checked printing surface works.
Keep its empty tail free of invented typing contexts.
Then check the affected target and runtime gates before landing.

This review does not establish TypeScript acceptance, runtime agreement, or successful printing of every checked program.
It adds no machine typing, substitution, host meaning, or scheduling claim.
It leaves production files, owner rulings, and the active session unchanged.
It runs no full sweep and performs no merge or push.
