import Effect4.Context.ContextFamily

/-!
# `Contexts` handler kernel dependency report

Lowering lane L3. The family is a signature, a key-table handler over
`Effect4.ServiceKey`, and the traced face that renders it, plus the eight
clauses that handler is pinned by. What this report is for is the *ceiling*:
the handler and its clauses must sit inside `propext` and `Quot.sound`, so that
no golden this family will own is underwritten by `Classical.choice` — it lives
under `Effect4/` and is audited by `#effect4_axiom_gate` like any other module
there, with no exemption.

Every declaration listed below is authored in
`Effect4/Context/ContextFamily.lean`; the `effect_signature` and
`effect_program` elaborators that emit the rest are admitted in the gate's
`targetImplementationModules` as `Effect4.Meta.Derive`, and nothing of their
output is admitted with them. `Effect4/Context/Key.lean`'s own receipts are
`Effect4Test/Environment/ContextKeyAssurance.lean` and are not repeated here.
-/

/-! ## Key identity is the pair -/

#print axioms Effect4.ContextFamily.declareKey_is_by_the_pair
#print axioms Effect4.ContextFamily.minted_keys_conflict

/-! ## The bindings -/

#print axioms Effect4.ContextFamily.bind_replaces_in_place
#print axioms Effect4.ContextFamily.lookup_bind_self
#print axioms Effect4.ContextFamily.lookup_other

/-! ## The reference defaults -/

#print axioms Effect4.ContextFamily.maxOps_default
#print axioms Effect4.ContextFamily.preventYield_default
#print axioms Effect4.ContextFamily.objectReferences_have_no_default

/-! ## The family the DSL emits, and the handler over it -/

#print axioms Effect4.ContextFamily.Contexts
#print axioms Effect4.ContextFamily.Contexts.rows
#print axioms Effect4.ContextFamily.Contexts.encodeParam
#print axioms Effect4.ContextFamily.Contexts.encodeAnswer
#print axioms Effect4.ContextFamily.Contexts.tracedExcept
#print axioms Effect4.ContextFamily.contextsLive
#print axioms Effect4.ContextFamily.contextGoldenLog
#print axioms Effect4.ContextFamily.contextPrograms
