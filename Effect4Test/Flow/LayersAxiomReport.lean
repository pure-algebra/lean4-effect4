import Effect4.Layer.LayerFamily

/-!
# `Layers` handler kernel dependency report

Lowering lane L3. The family is a signature, a memo-map handler and the traced
face that renders it, plus the eight clauses that handler is pinned by. What
this report is for is the *ceiling*: the handler and its clauses must sit inside
`propext` and `Quot.sound`, so that no golden of `generated/traces/layer/` is
underwritten by `Classical.choice` — the family lives under `Effect4/` and is
audited by `#effect4_axiom_gate` like any other module there, with no
exemption.

Every declaration listed below is authored in `Effect4/Layer/LayerFamily.lean`;
the `effect_signature`, `effect_atoms` and `effect_program` elaborators that
emit the rest are admitted in the gate's `targetImplementationModules` as
`Effect4.Meta.Derive`, and nothing of their output is admitted with them.

The eight clauses replace the six the four-row family carried (`freshOf`,
`layerBase`, `build_constructs`, `build_memoizes`, `build_memo_hit`,
`build_fresh_ignores_memo`, `build_after_close_is_not_memoized`). Every fact
those stated survives: the memo hit is `buildBase_memo_hit`, the miss is
`buildBase_miss_constructs`, `fresh`'s private memo map is the `.fresh` arm of
`buildMany` and is shown by the `freshRebuild` rows, and
`build_after_close_is_not_memoized` is now `close_empties_every_memo_map` plus
`buildBase_after_close_is_not_live`, which is the same fact stated over the
memo map rather than over a table keyed by layer id.
-/

/-! ## The store -/

#print axioms Effect4.LayerFamily.declare_takes_the_next_handle
#print axioms Effect4.LayerFamily.memoChain_starts_at_the_map

/-! ## The build -/

#print axioms Effect4.LayerFamily.buildBase_memo_hit
#print axioms Effect4.LayerFamily.buildBase_miss_constructs
#print axioms Effect4.LayerFamily.buildBase_after_close_is_not_live

/-! ## The close -/

#print axioms Effect4.LayerFamily.close_releases_in_reverse
#print axioms Effect4.LayerFamily.close_is_terminal
#print axioms Effect4.LayerFamily.close_empties_every_memo_map

/-! ## The family the DSL emits, and the handler over it -/

#print axioms Effect4.LayerFamily.Layers
#print axioms Effect4.LayerFamily.Layers.rows
#print axioms Effect4.LayerFamily.Layers.encodeParam
#print axioms Effect4.LayerFamily.Layers.encodeAnswer
#print axioms Effect4.LayerFamily.Layers.traced
#print axioms Effect4.LayerFamily.layersLive
#print axioms Effect4.LayerFamily.buildMany
#print axioms Effect4.LayerFamily.layerGoldenLog
#print axioms Effect4.LayerFamily.layerPrograms
