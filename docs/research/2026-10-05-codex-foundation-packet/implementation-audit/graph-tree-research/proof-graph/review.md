# The graph used by the proof report

Evidence: source review at `cbd2ec5793006fd1279121c5104bfdbdc065ea40` and eight finite Python controls.
No Lean command ran. No current report was shown to exhaust a traversal budget.

## What already exists

`ProofGraph.Plan.buildPlan` in `tools/ProofGraph/Plan.lean` derives statuses from actual dependencies.
`ProofGraph.reachedAxioms` in `tools/ProofGraph/Axioms.lean` uses explicit frames and a memo.
Its stop predicate turns named goals into leaves. Each memo belongs to one environment and stop predicate.
`Tools.Semantics.reachThrough` in `tools/Tools/Semantics.lean` visits each report node once and returns its unfinished queue.
That renderer's earlier shared-descendant omission is repaired. The new review does not reopen it.

The graph records theorem dependencies. It does not describe program control flow or establish an execution property.
`requirements` in `tools/Tools/SemanticsRegistry.lean` keeps R1–R13 and their unstated `openParts`.
A shared helper's fan-out may guide scheduling. It does not measure proof difficulty or semantic importance.

## A small follow-up in the existing traversal

`ProofGraph.Plan.walk` has a fixed loop bound of 10,000,000 stack pops.
After the loop, it returns `nearest`, lemma counts and definition counts, even when `stack` is nonempty.
Repeated dependency entries also consume pops before the `seen` check skips them.
The renderer and axiom traversal already have explicit exhaustion results; this private walk lacks one.

The finite mirror substitutes a small budget to expose the branch.
At budget 2, the chain `a → b → goal` returns no nearest node, with `goal` still pending.
At budget 3, the goal appears. Shared-descendant, cycle and stop-cut controls pass.
This is a source-level reporting risk. It is not evidence that today's graph is truncated or that kernel proofs are unsound.
Standing and `restsOn` come from the separate axiom collector; this walk's risk concerns nearest edges and brought-in counts.

Smallest correction: fail visibly if the final stack is nonempty. Retain a bounded exhausted control beside a sufficient-budget control.
If the bound becomes structural, derive it from the visited declarations and dependency entries, not node count alone.
The comments claiming that no finite environment can exhaust a fixed bound should describe an engineering limit instead.

Placement: proof reporting under decisions row 203. Consumer: nearest-node diagrams and brought-in counts.
Required property: a successful report contains every in-scope dependency reached before a selected stop node.
Hypotheses: fixed loaded environment, fixed roots, fixed scope and stop predicate.
Observation: the nearest-node set and counts, or explicit exhaustion.
Exclusions: semantic necessity, execution reachability, proof search completeness and kernel soundness.
Immediate prerequisite: expose the current unfinished-stack case in the existing test seam.

## Useful graph API without a new ledger

Keep the existing Plan nodes and measured dependencies as the sole evidence owner.
A slice view may show its changed roots, reached goals and affected R rows.
The view must include each affected requirement's `openParts`, even when no graph node states them.
Use a fresh memo after changing the environment or stop set.
Label associations separately from measured paths. A missing path does not prove semantic independence.

## Reproduction

Run `python3 proof-graph/probe.py` from this packet's root.
`probe-output.json` retains the result. `source-hashes.json` binds the reviewed declarations.
