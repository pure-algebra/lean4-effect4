# Deferred / Arena: Phase C proof preparation

Read-only source inspection against the current tree and Lean 4.33.1. No compiler,
search, proof body, bank edit or frozen-statement amendment. Run the Phase B baseline
first; the order below applies only to obligations search leaves open.

## Existing support and gaps

The current `Effect4.Stores` bank in `Laws/Machine/CompletionData.lean:9–20` contains
DeferredStore make/cellAt/setCell/isDone/poll/register/complete/drainDue definitions,
Owed.mapCode waiter/token/mode equations, and `store_lookup_lt` as safe forward.
It does **not** yet include cancel, wakeBatch, mapCode's code equation, identity or
composition. `StoresLaws.lean:2052` adds completed-cell length and concrete sync rows,
but those are downstream and specialized to Completion. Do not import StoresLaws
back into Refinement/CompletionData just to reuse them.

The core ten Deferred operations are generic in κ (`Machine/Stores.lean:1094–1178`).
The twelve old census witnesses and the current write/read theorem are specialized
to Completion (`:1183–1292`): useful specifications, not generic κ proofs. WakeList
state is unchanged by the proposed code map. Its register/cancel/wakeAll/runBatch
implementation should therefore stay opaque in these naturality proofs.

## Deferred statement-to-helper map

| Frozen family | Existing local facts | Small reusable additions / rule shape |
| --- | --- | --- |
| cell/store map identity + composition (4) | Option.map_id, Option.map_map; List.map_id, List.map_map | Owed.mapCode_code, mapCode_id, mapCode_comp; cell/store projection equations. Orient identity/composition toward one map and register norm simp. |
| make/cellAt/setCell (3) | List.length_map, map_append, getElem?_map, map_set | Map projection equations plus the existing generic operation equations; norm simp. `map_set` covers missing keys as well as live keys. |
| isDone/poll (2) | Option.isSome_map, map_map; prior cellAt naturality | Normalize through the cellAt equation; no Completion case analysis. |
| register/cancel (2) | prior cellAt/setCell equations; Option.map_some/map_none | Lookup-none/some and completion-none/some cases only. Code mapping does not alter wake; add cancel's defining equation to the store bank. |
| complete/wakeBatch (2) | List.map_append/map_map and setCell naturality | One reusable mapped-owed-constructor/list equation preserves waiter, token and mode while applying f only to code. Add wakeBatch's equation; no WakeList policy split. |
| drainDue (1) | List.map_nil, due projection | Direct pair/record normalization using the original Owed.mapCode due mapping. |
| completionPrim_injective | Completion has two constructors; Prim.ofExit_asExit? (`Frames.lean:630`), completionPrim definition (`Stores.lean:1813`) | Small constructor-disjointness/inversion fact; safe destruct of a concrete equality. Success/failure/refGet occupy different Prim constructors. |
| deferredOk_iff_image | List.mem_map, forall_mem_map; Option.map_eq_some_iff | A constructive finite-list preimage lemma, plus cell and owed preimage lemmas retaining all non-code fields. For cell none choose a none cell; for cell some or owed code use the supplied witness. Structural list induction avoids Classical.choice or a decoder. Register only usable image introduction/inversion facts, not unconstrained existential search. |
| ten Projects seats | the ten already proved naturality equations; Projects has step + keeps | Apply those equations through the state-first pair adapters. WF=True is trivial. Do not duplicate operation proofs or add an operation alphabet. |
| four Factors seats | existential factorization definition; function composition | Chosen observation witness and composition. Keep factors_trans local to a call because an unconstrained middle observation would create metavariables. |
| memoEntry_keys | Handles.lean:790 defines `[scope, promise] ++ finalizer.keys`; List.mem_append/mem_cons | A small membership rule; it stays in Handles. No generic-map import cycle. |

Possible new support statements should receive their own wanted markers before any
proof attempt. After each residual, add only the missing small fact and retry;
this plan is not evidence that any particular search closes.

## Arena order and helper families

1. **List lawful instance (10 fields, one frozen instance obligation).** All ten
   fields match existing List behavior. Empty/size/allocation use length_nil,
   length_append, getElem?_append_left/right; dense uses the general
   `isSome_getElem?`; poke uses length_set, getElem?_set_self, getElem?_set_ne,
   set_eq_of_length_le. The last lemma is essential: an absent write is identity.
   First prove the obligation; only then install the lawful instance. No axiom or
   temporary admitted instance is needed.
2. **Projection length and lookup.** `List.filterMap_length_eq_length` plus
   LawfulArena.dense, List.mem_range and length_range gives the length result.
   A reusable finite-index helper is the likely remaining work: if f is present
   exactly below n, then `((List.range n).filterMap f)[i]? = f i` for every i.
   This yields peek_toList without changing the frozen toList definition. The
   inspected List library has filterMap append/cons facts and range_succ, but no
   directly named dense filterMap-range lookup theorem was found. Keep this one
   focused support obligation rather than writing six separate traversals.
3. **Projection list/empty/poke/alloc.** With lookup established, List.ext_getElem?
   reduces list equality to lookups. Use lawful peek equations and the existing
   List.set/append lookup facts; handle in-range/out-of-range explicitly. Register
   the resulting projection equations as norm simp in one consistent direction.
   Avoid making list extensionality an unrestricted global search rule.
4. **Generic ref kernel (4) and heap Projects (1).** Introduce the small
   toList/writeBackA connector using toList_poke and the two Option cases. Combine
   with Option.map_bind/map_map and peek_toList for toList_refStepOf. The list
   specialization is definitional. Then reuse **existing** refStepOf_length and
   refStepOf_keeps (`RefKernel.lean:124,147`) instead of reproving heap preservation:
   a useful bridge is `v ∈ Arena.toList s ↔ ∃ i, Arena.peek s i = some v`, from
   List.mem_iff_getElem? and peek_toList. Successful option-step inversions fit safe
   destruct; concrete length/property consequences fit safe forward. Projects
   finally reuses this connector with Prod.swap and WF=True.
5. **Deferred-as-arena seats (3) and red seats (2).** The three Deferred adapters
   are their actual generic definitions under instArenaList. The red seats are
   fixed finite witnesses: insertion at absent index changes [], and sparseScopes
   has key 2 but no key 0 while its entry length is 1. They need no universal
   ScopeStore-as-Arena claim.

Register concrete equations/inversions after they close; keep general transitivity,
extensionality and existential choices out of the global bank. The list lawful
constructor is a finite local structure goal, not a reason to add a broad rule that
searches for arbitrary lawful carriers.

## Exact library anchors

All library paths below are relative to
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`.

- Init/Data/List/Lemmas.lean:229 getElem?_eq_some_iff; 294 ext_getElem?;
  479/485 mem_of_getElem?/mem_iff_getElem?; 618/643 set self/other;
  684 set_eq_of_length_le; 1089 getElem?_map; 1125/1134 mem_map/forall_mem_map;
  1206 map_set; 1252 map_map; 1465 filterMap_length_eq_length;
  1526 filterMap_append; 1627/1633 append lookup; 1853 map_append.
- Init/Data/List/Basic.lean:94 length_set; 631 length_append.
- Init/Data/List/Range.lean:162 length_range; 182 range_succ;
  Init/Data/List/Nat/Range.lean:244 mem_range.
- Init/GetElem.lean:199 getElem?_eq_none_iff; 257 isSome_getElem?;
  371 List.getElem?_eq_none.
- Init/Data/Option/Lemmas.lean:209 bind_eq_some_iff; 291 map_eq_some_iff;
  297 isSome_map; 336 map_map; 528 bind_map; 531 map_bind.
- Machine/Wake.lean:97–115 Owed record, mapCode and its three existing projections.

No concrete false frozen statement was found in this inspection. This is a source
check, not a proof or elaboration result. In particular, image witnesses constrain
only actual stored codes; Arena projection does not assert carrier extensionality;
and ScopeStore remains the explicit negative density example.
