# Raw handles through string-map atoms

Base: the checked record proofs at `5acfed51`, with map source `bc781486` and generated inventory `8f7077fd`.
The coordinator retains the pending OCaml manual patch and owns its integrated checks.

## Placement

Concept: Scope Lifetime & Finalization in `docs/core/semantics.md`.
Role: helpers for the semantics registry claim `m7-exit-handles-valid`.
The immediate consumers are `nativeAtom_keys` and `RawHandles.nativeAtom_handles` in `src/Effect4/Laws/Program/Handles/Term.lean`.
Their existing term laws feed registration and the native value invariant.
This slice retains their statements and every existing premise.

The raw observation is `Store.Val.handles`, including unknown kind bytes and exact allocation indices.
Every successful map operation returns only raw handles from its supplied values.
The subset forgets ordering and multiplicity.
The statements require actual operation success, with no typing, canonicality, or registered-input premise.
Decisions rows 125, 166, and 197 bound the string-map representation and duplicate handling.

These helpers establish no allocation existence, scheduler progress, liveness, or OCaml simulation.
The host boundary remains in `docs/core/host-boundary.md`.
They serve R3 and the existing M6 to M7 handle-validity route.

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
