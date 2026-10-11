# Goals packet: the store invariants of the atomic scenario

Family `store-invariants`. Requirement R4, concept `store-typing`. Goals `bounded`, `counted` and
`committed` of `Test/Dogfood/Scenario/Atomic.lean`, on the program `shop`. This note is a
working draft; later commits on the branch complete it.

## First: what the coordinator must know

- `bounded` rests on one general law that the tree does not have: the cell invariant from
  write sites (`heap_sites_keep`). The rest is a cheap census of the shop's 31 write sites.
- `counted` and `committed` follow from no one-cell invariant. They need each request's
  position in its code, as a ghost stage. The probe proves the algebra from the stages to both
  goals; the stages themselves are one program-specific planned goal (`shop_stages`).
- No goal of the family is false, as far as this probe found.

## Status of the probe

`Probe.lean` compiles with `lake env lean` in the worktree. `#plan_status` reports:

| Declaration | Standing |
| --- | --- |
| `family_modulo` (`Bounded ∧ Counted ∧ Committed`) | modulo `heap_sites_keep`, `shop_sites_used`, `shop_stages` |
| `bounded_modulo` | modulo `heap_sites_keep`, `shop_sites_used` |
| `counted_modulo`, `committed_modulo` | modulo `shop_stages` |
| `reached_history`, `history_keeps`, `counted_of_fit`, `committed_of_fit` | proved |
