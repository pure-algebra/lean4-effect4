# Proof graph traversal follow-up

Accept the traversal correction in `0373bcf6`, inspected at clean HEAD `11e655c1`.
The bounded review found no new concrete issue in the revised traversal.

`reachThrough` in `tools/Tools/Semantics.lean` removes duplicate starting names.
Each visit appends only distinct names absent from both the reached list and pending queue.
Each iteration therefore visits one new name, including when the graph contains cycles.
The function returns its remaining queue when the budget ends.

`renderPlan` bounds visits by all distinct node and edge names, plus the number of starting names.
That bound covers every name its `nearestOf` lookup can introduce.
Its Markdown output explicitly reports any pending names.
This resolves the original omission of the leaf below a shared dependency.

`checkReach` in `tools/Drivers/SemanticsControls.lean` includes four controls.
They cover the original witness, a chain, repeated starts, and a short budget with pending work.
Those source controls were inspected, not executed here.

An isolated Python mirror passed eight synthetic cases against their expected results.
Additional cases cover a zero budget, cycles, duplicate sibling edges, and names outside the node list.
The former algorithm still omits the witness's leaf, while its chain control succeeds.
The revised mirror also matches an independent traversal on all 13 retained requirement graphs, with no pending names.
The installed Lean source confirms that `List.eraseDups` keeps each first occurrence.

Evidence status: source inspection and finite Python checks, not Lean execution or a proof of the implementation.
Python version: 3.13.14.
`reach-followup.py` and `reach-followup.json` retain inputs, results, and inspected source hashes.
No build, generator, installation, or repository write ran.
