# 2026-10-17 Math seat, D3 follow-up: receipt

Status: receipt (history, not authority). Seat: math and formalization, the one Lean seat.
Base: `453bb0f75` on `seat/d3`. Head: the commit that adds this receipt, on `seat/d3`, not pushed.
The landing it follows is `docs/research/2026-10-17-d3/README.md`; its receipt's open obligations
3 and 4 close here.

The one thing to know first: `fold_of` took a field-list sibling's traversed list to be the
first list of products that holds a family member. A declaration table, `List (String × Ty)`, is
such a list, so a sibling with the table as a fixed parameter failed. The parameter count was
never the cause: two fixed parameters already worked.

## What landed

| File | Change |
| --- | --- |
| `src/Effect4/Program/FoldOf.lean` | `memberOf?` reads the binder that the structural recursion descends on (`Lean.Meta.getStructuralRecArgPos?`) first, and keeps its three passes as the fallback |
| `src/Effect4/Laws/Program/Typed/Membership.lean` | `fold_of Effect4.Program.Typed.FitsAt`: the algebra `FitsAt.alg`, its homomorphism witness, `FitsAt.eq_cata`, `fittersAt.eq_foldr` and `itemFittersAt.eq_foldr`; `fittersAt_eq_map` and `itemFittersAt_eq_map` read the generated connectors in place of an induction on the list |
| `src/Effect4/Laws/Program/Typed/ListFold.lean` | `ListFoldRules` at a table: `typing` reads `Checker.listOfIn sig.types`; `typed`, `preserved` and `step` take `TyDecls.Within sig.types w.types`; `fold_typed_atomic_update` takes no premise on the table |

Placement. The three rows serve concept `store-typing` and the claim `fold-typed-atomic-update`
(R4); the fold of `FitsAt` serves the traversal discipline (`docs/core/traversal-census.md`). Reach:
every typing signature, and every world whose table holds the signature's. Not established: generic laws
of a fold over a `Prop` carrier. So the inductions of `fits_map`, `fits_live`, `fits_sub` and
`fits_normalize` stay written over `FitsAt` (the D3 note's S2).

## Commands and results

| Command | Result |
| --- | --- |
| `lake env lean` on a probe of two fixed parameters with a table (`FoldProbe.P1`, `P2`) | refused before the change; accepted after it |
| `LEAN_NUM_THREADS=2 lake build Effect4 Effect4.Laws` | `Build completed successfully (1371 jobs)`: every `fold_of` of the tree elaborates under the new rule |
| `make batteries-touched BASE=453bb0f75` | no battery reached: the selector reads declaration references, and no battery names a changed one |
| `LEAN_NUM_THREADS=2 lake build Test.Program.FoldFamilySelection Test.Program.FoldContract`, the batteries that run `fold_of` | `Build completed successfully` |
| `#axiom_audit Effect4.Laws.Program.Typed.Membership Effect4.Laws.Program.Typed.ListFold` | 852 declarations within [propext, Quot.sound], 0 planned goals; `Effect4.Program.FoldOf` is meta code that `Test/Audit/AxiomGate.lean` exempts by name, as at the base |
| `python3 scripts/check-language.py --strict` on this receipt | `PASS` |

## Open obligations

1. Generic laws of a fold over a `Prop` carrier: monotonicity in the oracle, and the order. Then the
   hand inductions over `FitsAt` become their instances (the D3 note's S2).

## Bounded evidence

- The batteries ran are the touched ones.
