# Host-call design review plan

Review `docs/research/2026-10-09-host-calls-and-cleanup.md` against the pinned code and current authority documents.
Keep production files and owner rulings unchanged.

The review finishes when each proposed interface has a source comparison and each decisive suspected defect has a bounded control.
Record the proof obligations, their existing consumers, and the smallest corrective design.
Keep proposed obligations separate from proved theorems.

The finite probes cover these questions:

1. Does H8 alone connect a bounded host driver to the meaning under a total handler?
2. Does the battery's handler admit the same generic replies as the session?
3. Can the proposed await fields be read before binding and after application?
4. Does an immediate answer keep the same visible trace as park and resume?

The parent owns the one Lean process in this worktree.
Three GPT-6.1 Sol agents review lifecycle, proof structure, and OCaml lowering independently.
