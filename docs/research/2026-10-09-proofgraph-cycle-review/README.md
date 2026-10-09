# Proof dependency cycle review

The cycle repair passes the independent Lean controls. The new exact-dependency helper still omits dependencies in an axiom's type.
The isolated one-case correction passes its controls. Apply that correction before extending the helper's exactness claim.

## Pins and scope

| Item | Value |
| --- | --- |
| Review base | `62a62a602818400b7222948a7b93891901c55259` |
| Reviewed landing | `bd65164b9fbe0803bde474bb7e12b1849a9673d8` |
| Snapshot source hash | `2b4040047c63c22fa2eed38b4e1fb50c2865e4567a38e6f7028e353cbfc4e43f` |
| Evidence status | Finite Lean probes and source inspection |
| Proof role | Validation of the dependency reporting tool |
| Scope | Declaration dependencies, cycle caching, selected leaves, and interrupted traversal |
| Host boundary | Unchanged |

`snapshot.json` records the capture time and hashes. The landed collector bytes equal the tested source snapshot.
The isolated worktree remains at the review base. No production file changes during this review.

The primary session is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50.jsonl` under the repository-specific Claude directory.
The bounded recent tail identifies the repository as its working directory. The review reads no thinking fields.
Claude reports a larger comparison and starts a full sweep. This review does not reproduce either report.

## Resolved cycle omission

`ProofGraph.reachedAxioms` (`tools/ProofGraph/Axioms.lean`) previously cached unfinished cycle members as if their dependencies were known.
An inductive type and its constructors form a cycle. One constructor can reach a leaf through its sibling.
The old cache omits that leaf when the first constructor finishes early.

`Probe.lean` reproduces the omission against the landed base. One control selects a named leaf, as the goal traversal does.
Another control reaches `Classical.choice` through a sibling's type. The old cached answer omits `Classical.choice`.
This control shows that the collector can omit a reachable axiom. It does not establish that the whole-library gate accepted a forbidden declaration.

The new traversal stores each cycle member only after the entire component finishes.
The copied landing passes 17 selected-leaf roots and three axiom-bearing roots. Every retained cache entry matches fresh reachability.
The controls cover reversed root order, two selected leaves, mutual inductives, and clean roots.

The fresh oracle uses an independent worklist with no shared answers across roots.
It shares the constant extractor except that it visits axiom types. This limits its independence for other edge-policy errors.
The native Lean axiom-type control supplies a separate oracle for that case.

An additional control replaces the traversal budget with four steps in both copied implementations.
Both traversals return no answer. The old cache omits reachable leaves. The new cache contains only answers matching fresh reachability.
The new traversal resumes from that cache and reports the expected dependencies.
The four-step control tests interruption handling. It does not reach the production billion-step limit.

## Remaining axiom-type omission

`ProofGraph.usedConstantsOf` (`tools/ProofGraph/Axioms.lean`) returns no dependency for `axiomInfo`.
Pinned Lean 4.33.1 visits the axiom's type in `Lean.CollectAxioms.collect` (`Lean/Util/CollectAxioms.lean` in the toolchain sources).

The probe constructs local environment data with `A : Type` and `a : A` as axioms.
No synthetic declaration enters the compiling environment. The landed candidate reports only `a`. Lean reports both `A` and `a`.
The omission predates the cycle repair.

The smallest correction replaces the axiom case with this branch:

```lean
| .axiomInfo v => v.type.getUsedConstants
```

`AxiomTypes.lean` tests that correction. The corrected extractor reports both dependencies.
It also stops at a selected leaf and matches the three policy leaves: `propext`, `Quot.sound`, and `Classical.choice`.
The correction exists only in the isolated probe.

This omission does not demonstrate false acceptance under the current axiom policy. A custom outer axiom already causes refusal.
`ProofGraph.buildPlan` (`tools/ProofGraph/Plan.lean`) and `Tools.Semantics.declaration` (`tools/Tools/Semantics.lean`) check the resulting axiom array.
`ProofGraph.ProofRef.validate` (`tools/ProofGraph/Proof.lean`) checks that array too.

## Interface limits

Keep the existing shared dependency collector. This review establishes no need for another graph representation or a public configuration layer.

The sufficient cache contract requires a fixed environment, a fixed stop predicate, and previously valid entries.
Document all three premises beside `AxiomMemo` (`tools/ProofGraph/Axioms.lean`).

`ProofGraph.exactAxioms` (`tools/ProofGraph/Axioms.lean`) requires all checked declaration bodies and a known root.
Its current consumers establish root existence. Their ordinary imports load the private module data.
Restricted imports can withhold theorem bodies. The collector can then report a theorem name as an axiom and cause refusal.
This is an unsupported environment profile, not a reproduced regression in today's callers.

The finite budget is an engineering bound. Replace the claim that no finite environment reaches it.
The array unions and cached dependency arrays also prevent an unconditional linear-time claim.
State the reuse benefit without claiming a bound this implementation has not established.

## Verification

All commands run in `/Users/pooks/.codex/worktrees/module-design-review/lean4-effect4`.
Each Lean process uses `LEAN_NUM_THREADS=3`. The commands run sequentially.

| Command | Result | Evidence |
| --- | --- | --- |
| `LEAN_NUM_THREADS=3 lake build ProofGraph.Axioms` | Exit 0, two jobs | Tool output from this review |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-09-proofgraph-cycle-review/Probe.lean` | Exit 0 | `probe.log`, `result.json` |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-09-proofgraph-cycle-review/AxiomTypes.lean` | Exit 0 | `axiom-types.log`, `axiom-types-result.json` |

The first probe attempt has two harness errors: misplaced documentation and an unavailable comparison instance. The corrected probe passes. `attempt1-probe.log` retains that failed attempt.
No new library theorem enters this slice. No axiom-gate sweep runs in this worktree.
The raw synthetic axiom output is `[CycleSynthetic.a]` for the landing and `[CycleSynthetic.A, CycleSynthetic.a]` for Lean.
These checks do not prove the graph algorithm for arbitrary environments. They do not establish runtime, compiler, or host agreement.

The GPT-6.1 Sol agent independently reviews cycle handling and consumer contracts.
Its translated finite graph tests agree with fresh reachability. This receipt relies on the retained Lean probes for reproduced results.

## Checkpoint

| Finding | State at reviewed landing | Next action |
| --- | --- | --- |
| Cycle members omit reachable dependencies | Resolved in retained finite controls | Retain the committed cycle control |
| Interrupted traversal poisons the cache | Resolved in retained four-step controls | Keep unfinished components outside the cache |
| Axiom-type dependencies omitted | Open, predates this landing | Apply the tested extractor correction |
| Environment and budget contract wording | Open documentation cleanup | State the supported environment and finite limit |

The cleanup PR remains open. Its check state has no new conclusion at this checkpoint.
The next overwatch run starts at `bd65164b9fbe0803bde474bb7e12b1849a9673d8` and compares these outstanding findings.
