# String-map operations

Implementation is authorized on `codex/data-admission`, from local head `2d6534e9`.
The coordinator's tracked `maps-tuples-brief.md` at `d69a28da` supplies the contract and five-part proof placements.
Decision row 197 settles last-occurrence construction and the two-variable update result.
This seat implements only the six map atoms.

## Source and proof contract

The machine carrier stays a list of `Store.Val.pair` entries with string keys.
Ordinary entry pairs remain `Store.Val.list [key, value]`.
The two entry readers keep those images distinct.
Output maps use `Field.canonBy Field.bytesKey` for sorted, distinct keys.
Construction reverses supplied entries first, so the existing first-occurrence canonicalizer retains the last supplied value.
Update places the replacement first, before canonicalization.
Key and entry extraction retain the canonical UTF-8 order.
Lookup wraps presence in an outer option and never inspects the stored value for absence.

The raw readers refuse wrong frames, malformed entries and nonstring keys.
They need no stored proof field. Typed callers supply the existing map membership premises.
Construction and update restore canonical order even if a raw input list is not ordered.
No raw-reader success is itself a typing certificate.

The atom schemes are the six typing signatures in the coordinator's brief.
`mapSet` uses separate type variables for old and new values and returns their union.
No new custom scheme, term constructor, type constructor or membership judgment is added.
Target preludes use own-property operations and an explicit UTF-8 key comparator.
They remain finite target evidence, outside the Lean evaluation proofs.

## Exact ownership

- `Machine/Map.lean`: value readers, writers and operations.
- `Machine/Term.lean`: appended native atoms, rows, name lookup and evaluation cases only.
- `Program/NativeAtom.lean`: map schemes and their source descriptions.
- `Laws/Program/Typed/MapValues.lean`: reusable value and list helpers below both typing proof families.
- `Laws/Program/Typed.lean`: coarse result membership and evaluation existence cases.
- `Laws/Program/Typed/Membership.lean`: world-indexed result membership cases.
- `Laws/Program/Typed/Denotation.lean`: world-indexed evaluation existence cases.
- `Laws/Program/Handles/Term.lean` and a dedicated map helper module, unless the coordinator delegates these files separately.
- Focused map tests, this brief and receipts.

The coordinator owns root imports, decisions, generated inventories and preludes, target checks and policy measurements.
The pending record formation fixture is already handed to the coordinator and remains outside this slice.

## Required properties and consumers

Value-reader reconstruction, lookup membership, canonical output membership and entry conversion are helpers for `denote-typed`.
Their concept is Store Typing & Value Membership; their direct consumers are `NativeAtom.Sound`, `Typed.AtomFits` and term progress.
They retain every existing typing, substitution and world premise.
They establish actual pure-term result membership and evaluation existence, serving M5 and R3.
They establish neither scheduler progress nor host execution.

Successful raw map operations produce only handles already present in their inputs.
This is a helper for `m7-exit-handles-valid` under Scope Lifetime & Finalization.
Its direct consumers are `nativeAtom_keys` and `evalTerm_keys`; it serves the existing M6/M7 path and R3.
It adds neither handle allocation nor finalization guarantees.

## Stages and done criteria

First check `Machine.Term` and raw operation controls, then commit the source checkpoint.
The coordinator regenerates AtomInventory and returns its commit.
Then check schemes, all three typing consumers, handle tracing and focused fixtures with axiom queries.
The coordinator regenerates PreludeAtoms after the schemes land.

Controls cover empty maps, each insertion position, overwrite, missing and present undefined values, nested options and handles.
They distinguish map-entry pairs from ordinary pairs and verify last-occurrence construction.
They also distinguish integer-looking keys and the UTF-8 order of non-BMP strings.
Finish with explicit commits, narrow command results, axiom output and any remaining target or codec boundary.
