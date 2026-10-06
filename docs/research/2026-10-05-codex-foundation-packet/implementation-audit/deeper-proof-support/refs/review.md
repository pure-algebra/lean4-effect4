# REFS proof support

Evidence status: source review and retained probe evidence. New helper statements and proof bodies are uncompiled proposals.

The final reviewed scratch cut is probe5 and its retained result at 10:57:28Z. The seat already implements the rank route below. Do not dispatch it again. The only remaining recorded trust failure is localized to the empty-list lemma; the seat is already repairing it.

## Frozen source and observed progress

The seat is clean at `b199c15f783a05dd50a0d28c1d446df2957fb255` when captured. The design note and ReferenceExpansion module are not present at that cut. Scratch probes are separate from committed source.

The source and retained outputs are hashed in `source-hashes.json` and `retained-tool-results.json`. This review runs no Lean, build, generator, target, or runtime command.

- Probe1 leaves `expandAlgebra` projections unreduced. Marking imported definitions reducible is refused. This is not a false theorem.
- Probe2 confirms `cata_layers.induct`, with seven motives. The attempted `.mutual_induct` names do not exist.
- Probe3 introduces a local reducible algebra alias, with a definitional equality to `EffAlgebra.onRef`. Its substitution theorem reports `[propext]`.
- Probe3 still has an unused simp-argument error under warning-as-error. It is not a fully accepted file.
- Probe4 removes that argument and contains the subtree inclusion, shift, round, path-rank, and prior-site steps.
- Probe4's retained diagnostic is an application mismatch for `Option.noConfusion h` in `Node.at_of_layerAt`. The impossible branch has `h : none = some l`.

Use `cases h` for that branch. `Node.layerAt_eq_some_iff` in `Laws/Program/References.lean` also states the connector. No extra import is needed for this local repair.

The command pipelines truncate outputs and do not preserve Lean's exit as their shell exit. The explicit diagnostics establish pending acceptance. They do not establish success.

## Rank route: independently reviewed, already adopted in probe5

The active draft already defines `Path.rank xs site` by counting paths before `site`. It proves candidate lemmas `rank_lt_length` and `rank_lt_rank`.

The invariant should retain an original occurrence for each remaining reference. It should not rank the reference's current output path.

```lean
RankBound root k e :=
  ∀ current target, (current, target) ∈ e.refSites [] →
    ∃ source, (source, target) ∈ root.refSites [] ∧
      Path.rank ((root.refSites []).map Prod.fst) source < k
```

The proposed one-round statement is:

```lean
root.layerRefsWF = true →
RankBound root (k + 1) e →
RankBound root k (Eff.expandRound (.eff root) e)
```

It holds for arbitrary intermediate syntax `e` satisfying the invariant. It does not assert that `e` remains reference-well-formed relative to itself.

The proof has one list step:

1. Rewrite membership through draft `Eff.refSites_expandRound` and `List.mem_flatMap`.
2. Obtain the original `(source, target)` from `RankBound`.
3. Use draft `layerRefsWF_mem` to obtain the original target layer and its lookup equation.
4. Rewrite the replacement's `getD` with that equation.
5. Use draft `LayerTerm.refSites_append layer current []` to recover a relative path.
6. Rebase only the occurrence path to `target ++ relative`. Leave the target of that reference unchanged.
7. Apply draft `target_refs_prior` to obtain original membership and an occurrence before `source`.
8. Apply draft `Path.rank_lt_rank`, using original membership mapped through `Prod.fst`. Close the natural-number budget with `omega`.

The proof never compares an expanded occurrence path against the original source path. Copying changes the former.

Initialization uses `rank_lt_length`. A zero budget permits no reference. An induction on the list of rounds consumes one budget unit per element.

State that list lemma for arbitrary `steps : List Nat`; their values are ignored by the implementation. Specialize to `List.range n`, whose length is `n`.

This proves the exact count bound, then the implementation's count-plus-one bound. It needs no distinctness premise on the original path list. Duplicate expansion can increase the number of sites while every provenance rank decreases.

## Placement before proof work

The REFS brief proposes `reference-expansion-complete` under `initial-algebras-folds`, requirement R5. That claim is absent from this frozen seat registry. The coordinator owns its addition.

| Proposed helper | Concept and required property | Question and role | Reach and exclusions | Consumer and requirement |
| --- | --- | --- | --- | --- |
| RankBound one-round decrease | Initial algebras and folds; finite reference expansion | Helper of proposed reference-expansion-complete | Arbitrary alphabet, fixed original root, root.layerRefsWF, exact provenance bound; no typing or runtime claim | Exact round bound, then expanded_refs_nil_of_wf; R5 |
| Budget consumption over foldl | Same finite expansion property | Helper of the same claim | Fixed root and well-formedness; initial budget includes steps.length; no scheduler interpretation | Existing expandRefs list fold; R5 |
| Exact round bound | Same finite expansion property | Intermediate bound for the same claim | Number of rounds at least original reference count; no allocation-size bound | Public completeness and the two checker consumers; R5 |
| Optional family_induction | Initial algebras and folds; structural induction over the generated view | Helper beneath hom-eq-cata-eff and a consumer's placed claim | Every finite family node and predicate closed under listed children; not induction over runtime edges | Generic fold proofs; concrete Supervision migration below. It closes no requirement alone |

The public theorem keeps its one premise: `root.layerRefsWF = true`. The checker consumers retain all declarative typing premises. No runtime layer-sharing or lowering theorem follows.

## Optional infrastructure with an existing consumer

`candidate.lean` contains an uncompiled `family_induction` proof. It packages `size_pos` and `size_child_lt` from `Laws/Program/Size.lean`.

Its exact interface is:

```lean
(P : (fam : EffFam) → EffSelfCarrier Op fam → Prop)
(step : ∀ fam e,
  (∀ fam' c, ArgF.child fam' c ∈ (view fam e).2 → P fam' c) → P fam e)
→ ∀ fam e, P fam e
```

The proof uses natural-number induction on the existing size bound. It names no syntax constructor. It introduces no new tree, traversal, alphabet, or semantic relation.

There is a concrete existing migration: `supervision_child_flag_bounded` in `Laws/Api/Supervision.lean` repeats this induction. Keep its node step and `mem_childReaders`; discharge recursive child obligations through the new principle.

The migrated public `supervision_child_flag` should keep its exact statement. Remove the duplicated bounded induction only after that migration checks. The helper belongs beside `size_child_lt`, with Supervision as its first actual caller.

REFS can use this principle for a generic view proof. However, its current substitution block already works past projection reduction. Do not require a rewrite to this principle before reference completeness.

## Do not promise a missing fusion API

The Eff family has generated `EffHom` and `hom_eq_cata_*`. Its generic view has `cata_build`, `build_view`, and `ArgF.fold`.

The ready-made `cata_fusion_ty` and commuting-square generator path are for Ty's one-member extras. There is no corresponding public Eff fusion theorem in this frozen source.

A future Eff fusion addition can derive from EffHom and the existing uniqueness theorem. It requires one square for each constructor, with every family carrier respected. Do not hand-maintain another constructor table or claim the Ty theorem already applies.

The near-term REFS slice needs no generator change. Its remaining proof concerns finite provenance, not missing initial-algebra semantics.

## Discriminating acceptance

Keep the brief's real-program controls: no references, a chain, nested sibling targets, and a diamond with temporary growth.

Add statement checks for the budget-zero and exact-count boundaries. These controls test off-by-one errors; the universal theorem still needs its proof.

A wrong invariant ranks current copied paths. A wrong shift changes the referenced target as well as the occurrence path. Reject both against nested targets.

A wrong bound measures each expanded tree's reference count and assumes it decreases. The diamond control rejects that assumption.

For family_induction, retain the Supervision statement and axiom output. Include a child-bearing generic predicate so an induction principle that ignores children cannot close the consumer.

No proof is claimed from this review. The final probe5 trust result below supersedes probe4's diagnostic. The top theorem and consumers remain the active seat's work.


## Final frozen trust review: probe5

Probe5 repairs the impossible branch using `cases h`. It implements `RefsWithin root k e` with elapsed rounds added to the original occurrence rank. This is the same provenance route described above, expressed with an increasing elapsed-round count.

Its actual statements preserve the contract:

- The top theorem quantifies over every operation alphabet and has only `root.layerRefsWF = true` as its premise.
- The round bound accepts any list of rounds with length at least the original reference count.
- `typeOfProgram_expandRefs'` removes only `hempty` and retains well-formed references.
- `checkTypedProgram_of_hasTy'` removes only `expanded` and retains the declarative typing derivation on the expanded program.
- No theorem claims runtime layer-sharing, scope, type formation, or target execution.

The retained first probe5 run reports `Classical.choice` in the top and both consumer proofs. Its plan-status check explicitly refuses that axiom. This is successful detection, not acceptance.

The diagnostic rerun isolates the dependency to `refSites_nil_of_refsWithin`, which uses `List.eq_nil_iff_forall_not_mem`. That library lemma itself reports `Classical.choice` on the pinned toolchain.

All queried rank, path, inclusion, substitution, shift, provenance and round-budget helpers report only the permitted axioms. The existing reference-free fixed-point helpers also stay within the ceiling.

The smallest repair is a case split on `e.refSites []`. The nil case is reflexivity. The cons case instantiates the bound at the head, then `omega` contradicts the exhausted budget. The parent reports this repair is already underway. Do not send it as new implementation work.

The next decisive receipt contains a fresh result for the repaired file, the top theorem and both consumers' axiom queries, and plan status. It must restore the final plan-status query, which the diagnostic-only rerun removed. A passing diagnostic rerun alone does not replace the previously failing acceptance query.

The optional family-induction helper is not a REFS prerequisite now. Supervision remains a real migration consumer, but defer that cleanup unless the owner selects it. No generator or fusion campaign is needed to complete this proof.
