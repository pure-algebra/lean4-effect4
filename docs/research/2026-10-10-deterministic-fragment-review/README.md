# A checked fragment for schedule-independent results

Give authors ordinary programs and one optional analysis.
Infer resource identities, accesses, and conflicts from the existing `Eff`.
Keep typing, fragment support, and machine evidence separate.

This packet proposes a finite parallel phase as the first useful fragment.
Workers can return ordinary data.
They can use private cells, shared read-only cells, or shared addition updates that return unit.
The parent joins every worker before inspecting their shared cells.

The executable analysis passes its finite controls.
No theorem yet connects its successful result to every supported machine run.
Keep that distinction visible in the editor.

## Read this packet

| File | Purpose |
| --- | --- |
| [DESIGN.md](DESIGN.md) | The fragment, author interface, judgments, editor behavior, and shared data |
| [PROOF-DAG.md](PROOF-DAG.md) | Proposed statements, five-point placement, dependencies, and existing consumers |
| [REVIEW.md](REVIEW.md) | Corrections to the random-descent application and the landing order |
| [LITERATURE.md](LITERATURE.md) | Verified primary sources and their limits |
| [RECEIPT.md](RECEIPT.md) | Reviewed commits, ownership, commands, results, and open work |
| [PLAN.md](PLAN.md) | Finishing criteria and placement recorded before the probes |
| [probes/Fragment.lean](probes/Fragment.lean) | Fold-based executable fragment analysis |
| [probes/Controls.lean](probes/Controls.lean) | Author examples and bounded machine comparisons |
| [probes/LiveView.lean](probes/LiveView.lean) | Typed refusals, holes, exact input identity, and an actual editor change |
| [probes/PromiseControls.lean](probes/PromiseControls.lean) | Promise dependency and step-count controls |

## What the probes establish

`Controls.out` records seven accepted author programs and seventeen refused author programs.
All twenty-four pass ordinary authoring elaboration and program typing.
The refusals therefore express fragment restrictions, not failures of ordinary typing.
Some refused programs can still have schedule-independent results.

For each accepted program, the probe explores two fire tapes.
It also explores 255 tapes with at most two inserted preemption verdicts.
The depth bound is twelve decisions, after the initial evaluation.
The command fuel is 400.
Every retained decision has a sufficient-budget receipt.
Every endpoint finishes and agrees on `Machine.obs`: every fiber exit and the entire store.
These are finite checks of the seven programs.

A negative control returns `[1, 2]` or `[2, 1]` while leaving the same final cell value, `2`.
Commuting final writes therefore do not justify returning their intermediate answers.

The editor probe changes one alias while keeping its type.
`EditSession.feed` reports a typing-table splice.
The fragment analysis changes from accepted to refused because the alias now creates a shared write conflict.
This is a checked reason to invalidate more than the repainted typing subtree.

## Recommendation for Claude

Land the generic random-descent theorem with its full premises.
Develop the syntactic fragment beside it, without waiting for a general machine-name quotient.
Expose the fragment as analysis of `Api.Typed`, not another authoring language.
Prove final observations agree before displaying a certified result.
Keep completion, fire counts, preemption, and host behavior as separate obligations.
