# ORG cleanup and base laws: receipt (2026-10-09)

**The one thing to know before merging:** the checker is now natural in its base path
(`checker-base-natural`), and 28 groups of statement-identical copies are resolved: one copy
is gone, or derives from the other. Every gate is green at the head, and no theorem statement changed.

The work follows seat ORG's ranked proposals
([theory map](2026-10-08-seat-ORG-theory-map.md) §7) and its scratch proofs
(`seat-ORG/OrgMeasure3.lean`, `OrgConnectors.lean`, under the coordinator's temporary
directory). The base is `2d3e85fe`, and the head is the commit that adds this receipt.

## What landed

| Commit | Change | Placement |
| --- | --- | --- |
| `92f51a62` | `Node.at_replaceAt_below` (L3); `foldMapAt_*_base` and `foldMapAt_*_hom` over the seven sorts (L5, L6) | `address-composes`; new claim `path-fold-natural` (compatibility, R14) |
| `92f51a62` | the seven `foldMapAt_*_paths_shift` lose their own induction; each is an instance of L5 and L6 (C6) | steps of `annotate-table` |
| `92f51a62` | `Agreement.Node.at_append` and `Typed.node_at_child` derive from the address laws (C1, C2); ReadLeaf's `bind_eq_ok` and `map_eq_ok` are `Laws.Auto`'s (C5) | no new claim |
| `7b73d59c` | `Checker.check_rebase` and its six siblings (L7); `tableAt_rebase` (L8); the `Except` facts in `Laws/Auto/ExceptMap.lean` | new claim `checker-base-natural` (compatibility, R14) |
| this commit | 28 duplicate groups resolved: one copy deleted and its uses moved to the original, or made a corollary | no new claim |

The duplicate groups come from seat ORG's `#org_duplicates`, rerun at `7b73d59c` with two more
columns: whether one member already uses the other, and which member's module imports the
other's. It found 49 groups.

- **Resolved (28).** The copy in the importing module goes, or the copy with no use goes:
  - the typed print's whole `inst*_congr` family (one mutual induction, six groups) and
    `splitHeadTypes_targets_nonempty`;
  - Pool's two reply-normal copies and Agreement's `compileEff_zero`;
  - `Typed.subN_never` (25 uses, now on the registered `Bounds.subN_never`) and
    `Typed.mem_zip_self`;
  - `Typed.complete_cells_length`, `exitOk_failure_error` and `failureFits_cause`;
  - `commandOwner_rupdate`, `seq_typed_sameError` and `subN_list_exitOf`;
  - the simulation's `point_refresh` and `bool_eq_false_of_not`;
  - AnswerDecision's `prepareExternalAnswer_sites` and `TyView`'s `sizeOf_field_lt_record`;
  - with no use: `sub_sound`, `machineTyped_of_configTyped`, `Semaphore.Model.request_equal`,
    `fresh_forks_without_parent` and ReadLeaf's `toDigitsCore_append`.

  `interruptedAt_update_mark` names its fiber, so it stays as a one-line corollary.
- **Already derived (12).** One member's proof is the other, as for `bind_eq_ok`. The finder
  reads statements only, so it still lists them. One of them, `putNode_fresh_closed`, has no
  use. It is in a core store module, whose edit rebuilds the core, so it waits for the next
  core change.
- **Left (9).** The members stand in unrelated modules:
  - the three `Bool` facts sit in the `Laws.Auto` rule bank beside their `Constructive` twins;
    a bank's members are a search's rules, so they stay;
  - two pairs in Pool and Semaphore are general facts of a carrier's shape;
  - four pairs in the guard and the denotation need a shared home first, which the theory
    map's rank 4 names.

## Commands and results

| Command | Result |
| --- | --- |
| `scratch/lean-slot.sh make gen-semantics` at each commit | exit 0; goal gate: 31 planned goals, 14 declarations rest on goals |
| `scratch/lean-slot.sh make check-proof-style` | pass; three baseline entries left with C1 and C5, one with AnswerDecision's copy |
| `make check-docs`, `make check-language` | pass |

The axiom gate holds every new theorem to `[propext, Quot.sound]`. `generated/semantics.md`
reads `path-fold-natural` and `checker-base-natural` as proved.

## Open

- L9 (`rebaseRefs` keeps `layerRefsWF`) and L10 (`Node.childEnv` by its reads) are not stated.
- Ranks 5 to 9 of the theory map are open: a program in the store, the lowering census, search
  by address, the store's claims, and row positions.
- `Laws/Program/Address.lean` still says the checker's base law is not stated. Its next edit
  corrects the line, since a docstring edit there rebuilds the law graph.

No evidence here is bounded or host-only.
