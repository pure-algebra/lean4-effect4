# REFS brief and linked-install guard review

Snapshot: `6e629bb4578c9cd116d97aa92d4b31d44b5c5757`.
Role: bounded source scout. Evidence: committed sources and retained coordinator output.
The REFS brief is committed at `7a6e53ea`; dispatch and implementation are outside this review.

No new false obligation or implementation defect was found.
The brief carries the earlier bound, ranking and runtime-sharing corrections.
The useful new guidance is one small path-fold helper and a dependency direction.

## Reuse the whole-subtree inclusion

`Node.yieldAt_subset_of_at` includes one addressed node's immediate yield in the root fold.
`Node.foldList_child` already includes a child's whole fold in its parent's fold.
The REFS target-membership step can use the following generalization directly.

Proposed, uncompiled statement:

```lean
-- In Effect4.Program.Node, beside yieldAt_subset_of_at.
theorem foldList_subset_of_at {Op α : Type} (y : PathYield Op α) :
    ∀ (path : List Nat) (n m : Node Op) (p : List Nat),
      Node.at_ n path = some m →
      foldList y (p ++ path) m ⊆ foldList y p n
```

The proof follows the existing path induction of `yieldAt_subset_of_at`.
The empty path is reflexive inclusion.
The child case composes the induction hypothesis with `foldList_child`, using the same append equalities.
No new program traversal or graph representation is needed.

Instantiate it with `refYield`, root `.eff root`, and the target's addressed `.layer layer`.
It places every member of `layer.refSites target` in `root.refSites []`.
Thus this membership step does not first need the converse from collected sites to addressed nodes.
The separate statement that nested original sites precede the caller still needs its path-order proof.
This helper does not establish that order or the expansion bound by itself.

Placement: `initial-algebras-folds`, helper of proposed `reference-expansion-complete`, serving R5.
Consumer: the membership half of `target_refs_prior` in the planned ReferenceExpansion proof.
Premise: successful `Node.at_`; the operation alphabet and yield carrier remain arbitrary.
Observation: inclusion of the addressed subtree's collected yields at the corresponding absolute paths.
Exclusions: reference validity, typing, worlds, run behavior, layer identity and target execution.
Prerequisite: the existing generated path folds and `Node.foldList_child`.
No new registry claim is needed for this helper.

## Keep the proof's imports below its consumers

`ReferenceTyping` currently owns `expandRefs_eq_self_of_refSites_nil` and `typeOfProgram_expandRefs`.
`ExpandFix` imports `ReferenceTyping` and adds facts derived from typing.
Both proposed consumers need the new completeness theorem.

Keep `ReferenceExpansion` below `ReferenceTyping` and `CheckedTyping`.
Use `PathFold`, `PathOrder` and the existing core expansion in that foundational proof.
Do not import `ReferenceTyping` or `ExpandFix` into the new module merely to obtain a convenience lemma.
That would obstruct the planned consumer dependency.
If a reference-free identity fact is needed, move its unchanged structural owner lower or keep the rank statement valid for every sufficient round count.
Choose that small placement in the required design note.
The current brief does not mandate a cyclic import; this is preventive reuse guidance.

After completeness, keep the existing consumer proofs short.
`typeOfProgram_expandRefs` can derive its old `hempty` locally and reuse its fixed-point and reference-free well-formedness facts.
`checkTypedProgram_of_hasTy` can derive its old `expanded` locally and retain the same `HasTy` premise and completeness proof.
The checker's equation unfolds the same executable tests; no new acceptance policy follows.

The brief correctly retains reference well-formedness and the exact `refSites.length + 1` bound.
It includes the empty-reference case and the growing diamond control.
It keeps execution redirection, shared memo identity, R8 agreement and `lower_refines_build` outside the theorem.
No new store/world invariant is required for this syntactic property.
Earlier original-occurrence ranking guidance is already consumed and need not be repeated as a finding.

## Linked-install guard

`6e629bb4` tests `-L ts/eff/node_modules` before either deletion or installation.
For an existing or dangling symbolic link, the branch prints a message and leaves the link and target untouched.
It also skips `touch`, so it does not mutate the linked target's timestamp.
For a nonlink path, deletion, frozen-lockfile installation and marker update remain sequenced with `&&`.
The guard establishes shared-install ownership; it does not establish the linked dependency version or completeness.
An outdated link may cause the keep-message to recur. That does not cause an installation.

The exact saved command and output are in `make-evidence.json`.
The linked scratch case prints the keep-message and retains the link.
The no-folder case invokes an echo stand-in for Bun, not an actual installer.
The stand-in creates no directory; the final `touch` therefore creates a regular marker file.
The next attempted fresh-directory setup fails at `mkdir`, so that scratch case never reaches Make.
The real coordinator folder's separate `make -n` result is “up to date.”

Those observations support the linked-case repair and ordinary up-to-date-folder path.
They do not establish a successful fresh installation or an independently tested stale-directory installation.
No new installation, Make execution or cleanup was performed by this monitor.
The incomplete scratch directory control is an evidence limit, not a demonstrated guard defect.
