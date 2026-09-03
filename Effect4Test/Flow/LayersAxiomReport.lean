import Effect4.Layer.LayerFamily

/-!
# `Layers` handler kernel dependency report

Packet M4. The family is a signature, a memo-table handler and the traced face
that renders it, plus the eight clauses that handler is pinned by. What this
report is for is the *ceiling*: the handler and its clauses must sit inside
`propext` and `Quot.sound`, so that no golden of `generated/traces/layer/` is
underwritten by `Classical.choice` — the family lives under `Effect4/` and is
audited by `#effect4_axiom_gate` like any other module there, with no
exemption.

Every declaration listed below is authored in `Effect4/Layer/LayerFamily.lean`;
the `effect_signature` and `effect_program` elaborators that emit the rest are
admitted in the gate's `targetImplementationModules` as `Effect4.Meta.Derive`,
and nothing of their output is admitted with them.
-/

#print axioms Effect4.LayerFamily.build_constructs
#print axioms Effect4.LayerFamily.build_memoizes
#print axioms Effect4.LayerFamily.build_memo_hit
#print axioms Effect4.LayerFamily.build_fresh_ignores_memo
#print axioms Effect4.LayerFamily.build_after_close_is_not_live
#print axioms Effect4.LayerFamily.build_after_close_is_not_memoized
#print axioms Effect4.LayerFamily.close_releases_in_reverse
#print axioms Effect4.LayerFamily.close_is_terminal
