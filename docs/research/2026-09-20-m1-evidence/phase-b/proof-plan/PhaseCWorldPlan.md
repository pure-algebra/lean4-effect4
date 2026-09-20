# Phase C World proof plan

Read-only source review, 2026-09-20. This is a proof organization plan, not proof evidence. No Lean, lake, proof search, or live source edit was performed. The baseline census must finish before proof work begins. New helper statements must receive explicit Obligation/#proof_wanted entries and a retained pending snapshot before proof attempts.

## Scope and source anchors

Paths below are relative to /Users/pooks/Dev/lean4-effect4.

- `src/Effect4/Laws/Program/Typed/World.lean:48`: ghost-table carriers; :52 World; :58 TableExtends; :62 tableInsert.
- `World.lean:67`: ValueOk reads the actual external allocation spellings; :73 CompletionOk; :83 HeapCell; :88 PromiseCell.
- `World.lean:93`: generated HeapTable column; :97 PromiseTable; :102 HeapCoverage; :105 PromiseCoverage.
- `World.lean:110`: HeapTypedAt; :114 PromiseTypedAt; :120 CellCompatible; :124 World.le.
- `World.lean:130`: addFiber; :133 addRef; :136 addPromise.
- `World.lean:144–267`: 19 WorldWanted statements; :272–296 data and five WorldControlWanted statements. The final gates remain commented at :303–304 in the reviewed source.
- `src/Effect4/Laws/Program/Typed/TypedStateDecl.lean:336`: the column generator emits exactly `∀ i v, values[i]? = some v → leaf w (keyConstructor i) v`; it registers generated columns as norm unfold in Effect4.TypedState at :339.
- `src/Effect4/Laws/Machine/Arena.lean:9`: Arena operations; :16 LawfulArena; :33 list instance; :49–89 the ten pending Arena obligations.
- `src/Effect4/Laws/Machine/StoresLaws.lean:43`: the length/existence store order; :53 reflexivity; :57 transitivity; :544 deferredMake equation; :731 memoBuild equation; :851 syncOpStep_le.
- `src/Effect4/Laws/Machine/Handles.lean:868`: base World; :910 base World.le; :1059 reflexivity; :1061 transitivity; :1092 le_of_state.
- `src/Effect4/Machine/Stores.lean:845`: refPeek; :879 refMake appends; :1099 DeferredStore.make; :1103 cellAt; :1939 deferredMake step; :2003 memoBuild step.
- `src/Effect4/Program/Typed.lean:34`: Val.hasTy; :37 nat admission ignores allocation spellings; :50 external handles read the indexed exact spelling.
- `src/Effect4/Laws/Program/Progress.lean:72`: old Stores.HeapNat uses default-empty allocation admission.
- `src/Effect4/Laws/Effects/Protocol.lean:30`: WorldOrder requires le, refl, and trans, with no validity or antisymmetry condition.
- `src/Effect4/Laws/Program/Typed/ForkSource.lean:28`: the frozen source_fork_extension contract.
- `src/Effect4/Machine/Fibers.lean:271`: RunFiber.make; :630 emit changes trace only; :924–940 spawn constructs and appends the child, returning its id.

## Statement assessment

No concrete false statement was found among the 19 WorldWanted statements, five World controls, or source_fork_extension. This is source-derived assessment only, not checked proof or an exhaustive counterexample search.

The order preserves each old keywise typing judgment, rather than asserting either world's validity. Therefore arbitrary invalid worlds can relate to themselves. A ghost table is a function to Option, so lookup uniqueness provides the bridge from the existential typed-at witnesses in the coverage equivalences back to every conditional column leaf.

The three allocation contracts have actual syncOpStep premises. All three steps leave external spellings unchanged. This is stronger than the length-only external part of Stores.le and is the correct hypothesis for the local value/completion transport needed here.

## Dependency order

1. Table operations: table_refl, table_trans, insert_extends, insert_here, insert_other.
2. Order: order_refl, order_trans, protocol_order, heap_typed_at_mono, promise_typed_at_mono; ref_completion_inv is independent and definitional.
3. Generated columns: heap_coverage_iff, promise_coverage_iff, heapNat_iff.
4. Arena/list allocation support and the completion transport described below.
5. fork_extension; then refMake_extension; then the common promise allocation helper and its deferredMake/memoBuild callers.
6. Five World controls, heapNotMonotone, and the downstream source_fork_extension.

Arena's allocation support needs only LawfulArena/list_lawful and the deferred allocator/read connectors. World's extension proofs need not wait for generic toList_poke or toList_alloc unless the actual residual goals justify that dependency. World currently does not import Arena; using the shared Arena fact would add only that lower Laws dependency. Do not import Guard or the reference interpreter into World.

## Frozen hypotheses to preserve

- insert_extends: `table key = none`. No assumption about the table elsewhere.
- insert_other: `other ≠ key`.
- order_refl/order_trans/protocol_order: arbitrary worlds, with no validity premise.
- heap_coverage_iff and promise_coverage_iff: arbitrary world; both the conditional column and separate coverage are present on the left.
- heapNat_iff: `∀ cell value, refPeek w.state.refs cell = some value → w.Ρ cell = some .nat`. Ghost entries outside the allocated heap are unconstrained.
- fork_extension: `w.Γ id = none`; there is no requirement that id is absent from w.ids and no nodup conclusion.
- refMake_extension: `syncOpStep (.refMake value) w.state = some (state, Val.cell key)`, `w.Ρ key = none`, and `ValueOk w ty value`.
- deferredMake_extension: `syncOpStep .deferredMake w.state = some (state, Val.promise key)` and `w.Π key = none`.
- memoBuild_extension: `syncOpStep (.memoBuild layer memoMap) w.state = some (state, answer)` and `w.Π w.state.deferreds.make.1 = none`. The fresh promise key is make.1; answer is the layer scope. There is no memo miss or store-WF premise in this typing contract.
- source_fork_extension: exact source lookup and successful Checker.check at `(site.child 0).path`, `w.state = m.state`, `w.ids = m.fibers.map (fun f => f.id)`, and `w.Γ ⟨m.nextId⟩ = none`. It claims child membership, not uniqueness or lookup-by-id, so no new machine-WF assumption is suggested.

## Small reusable facts to consider after the baseline

These are proposed statements, not new frozen obligations and not attempted proofs. Add only those the initial bank residuals require.

1. **Allocation lookup inversion.** For `[Arena σ α] [LawfulArena σ α]`, a lookup
   `Arena.peek (Arena.alloc s fresh).2 i = some value`
   implies
   `(i < Arena.size s ∧ Arena.peek s i = some value) ∨
    (i = Arena.size s ∧ value = fresh)`.
   It follows from dense, size_alloc, peek_alloc_old and peek_alloc_new. A list-specialized version is enough if the generic fact adds no measured reuse. This is an inversion, suitable for safe destruct in Effect4.Stores.

2. **Nat admission is allocation-independent.** For arbitrary value and allocation table,
   `Val.hasTy value .nat allocated = Val.hasTy value .nat []`.
   This bridges HeapTable at actual spellings to the existing HeapNat predicate without a general admission theorem.

3. **Completion transport under exact external spellings.** Hypotheses:
   `newer.state.externals.allocated = old.state.externals.allocated` and
   `TableExtends old.Ρ newer.Ρ`.
   Conclusion: `CompletionOk old types completion → CompletionOk newer types completion`.
   The success/failure cases use the identical admission function; ofRefGet transports the existing Ρ lookup. Do not replace these premises by World.le or Stores.le.

4. **Common promise-allocation extension.** Parameters w, state, types; define key := w.state.deferreds.make.1. Premises:
   - `state.refs = w.state.refs`;
   - `state.deferreds = w.state.deferreds.make.2`;
   - `state.externals.allocated = w.state.externals.allocated`;
   - `w.state.le state`;
   - `w.Π key = none`.
   Conclusion is exactly the six-conjunct promise extension bundle: w.le addPromise, the fresh PromiseTypedAt, and preservation implications for both columns and both coverage predicates. No validity, existing coverage, memo miss, or old pending-cell premise belongs in this helper. DeferredStore.make creates the new cell with completion none.

The actual deferredMake and memoBuild equations supply the common helper's state premises. Reuse syncOpStep_le for memo's scopes, memo maps and nextName; do not duplicate those preservation arguments. A fresh Ref changes Ρ, so its existing-promise branch uses completion transport above.

## Traps to avoid

- HeapTypedAt and PromiseTypedAt may hold vacuously at unallocated ghost keys. For a lookup after allocation, the fresh branch must use the frozen table-freshness premise to rule out an old declaration at that exact key. An old-in-bounds lookup lemma alone does not cover this case.
- Preserve separate coverage implications; do not smuggle coverage into the conditional leaf definitions.
- Due work is a separate generated PromiseTable predicate, not a cell in ghost Π and not typed using the resumed fiber's final Γ.
- Reflected or generated column facts should be consumed directly. Obtain unchanged-field frame support through #frame_rules, not handwritten frame transports.
- TableExtends/order transitivity belongs in a local call, not an unrestricted bank rule that invents an intermediate table/world.
- The source-fork obligation can exhibit the child that spawn itself appended. Stronger Guard spawn-child-lookup lemmas carry unrelated prerequisites and would raise the module's floor.
- No global World.le → ValueOk monotonicity. Source-derived counterexample to that tempting extra claim: empty heaps/promises and empty ghost tables, same ids, external tables ["A"] and ["B"]. Length-based store growth and all empty compatibility clauses hold, while external handle zero changes membership at `.handle "A"`. This is not a counterexample to any live obligation and has not been executed as a control.

## Search and evidence discipline

Run the requested fresh before-fill #auto_census first. Reuse only trust-admissible searched terms. Register allocation equations/inversions in Effect4.Stores and World/table/column facts in Effect4.TypedState, selecting both only at connectors. Keep generic transitivity local. Freeze each genuinely new helper statement before its proof attempt. Retain original wanted snapshots; remove live wanted markers only for obligations the instrument actually closes. Run final gates and bank census with the unchanged stated caps. No final ceiling-zero claim is made by this plan.
