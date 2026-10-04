# Raw handles through string-map atoms

Base: the checked record proofs at `5acfed51`, with map source `bc781486` and generated inventory `8f7077fd`.
The coordinator retains the pending OCaml manual patch and owns its integrated checks.

## Placement

Concept: Residual Program Typing in `docs/core/semantics.md`.
Role: helpers for the semantics registry claim `straight-meaning-typed`.
The immediate consumers are `nativeAtom_keys` and `RawHandles.nativeAtom_handles` in `src/Effect4/Laws/Program/Handles/Term.lean`.
The raw term law feeds `Denote.evalTerm_validIn`, then `sound`, then `meaning_typed` in `src/Effect4/Laws/Program/MeaningSound.lean`.
That theorem requires `Straight` and successful native typing from an empty environment.
It concludes `ExitHasTy` in the produced stores from empty initial stores.
The decoded-key route feeds `Handles.Hooks` and `Handles.Layer` separately for R4.
This slice retains their statements and every existing premise.

The raw observation is `Store.Val.handles`, including unknown kind bytes and exact allocation indices.
Every successful map operation returns only raw handles from its supplied values.
The subset forgets ordering and multiplicity.
The statements require actual operation success, with no typing, canonicality, or registered-input premise.
Decisions rows 125, 166, and 197 bound the string-map representation and duplicate handling.

These helpers establish no allocation existence, scheduler progress, liveness, or OCaml simulation.
The host boundary remains in `docs/core/host-boundary.md`.
They serve R3 and R4. They do not supply a direct premise of the M7 exit-handle theorem.

Reader reconstruction helpers also serve Store Typing & Value Membership and the `denote-typed` claim.
`Typed.MapValues` consumes their exact successful-reader equations and forward reconstruction equations.
Those helpers retain malformed-input refusal and do not supply a membership judgment by themselves.

## Files and checks

- `src/Effect4/Laws/Machine/Map.lean`: reader reconstruction and raw handle subsets.
- `src/Effect4/Laws/Program/Handles/Term.lean`: new map atom cases only.
- `Test/Program/MapHandles.lean`: raw-byte controls and axiom queries.

The coordinator owns root imports, generated files, and all source semantics.
The typing seat owns native and world-indexed map membership proofs.
The Lean slot stays serialized.
Narrow checks compile the new helper module, the handle consumer, and the focused fixture.
All queried theorem axioms must stay within `[propext, Quot.sound]`.
The fixture remains finite evidence and changes no theorem statement.
