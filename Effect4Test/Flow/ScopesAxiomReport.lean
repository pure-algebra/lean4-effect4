import Effect4.Runtime.ScopeFamily

/-!
# `Scopes` handler kernel dependency report

Lowering lane L3. The family is a signature, a scope-store handler over the
frozen `Effect4/Runtime/Scope.lean` state machine, and the traced face that
renders it, plus the six clauses that handler is pinned by. What this report is
for is the *ceiling*: the handler and its clauses must sit inside `propext` and
`Quot.sound`, so that no golden of `generated/traces/scope/` is underwritten by
`Classical.choice` — the family lives under `Effect4/` now and is audited by
`#effect4_axiom_gate` like any other module there, with no exemption. Before
this packet the same handler was declared inside `harness/trace/Generate.lean`,
which is a script and was audited by nothing.

Every declaration listed below is authored in
`Effect4/Runtime/ScopeFamily.lean`; the `effect_signature`, `effect_atoms` and
`effect_program` elaborators that emit the rest are admitted in the gate's
`targetImplementationModules` as `Effect4.Meta.Derive`, and nothing of their
output is admitted with them. `Effect4/Runtime/Scope.lean`'s own receipts are
`Effect4Test/Runtime/ScopeAxiomReport.lean` and are not repeated here.
-/

/-! ## The fork linkage — `SCOPE-FB-FINALIZER-MEANING`, closed -/

#print axioms Effect4.ScopeFamily.fork_registers_the_linkage_names
#print axioms Effect4.ScopeFamily.close_cascades_to_the_child

/-! ## The close -/

#print axioms Effect4.ScopeFamily.close_writes_the_parent_state_first
#print axioms Effect4.ScopeFamily.closeOrder_is_the_keys

/-! ## The fiber linkage -/

#print axioms Effect4.ScopeFamily.linkFiber_closed_scope
#print axioms Effect4.ScopeFamily.linkFiber_names

/-! ## The family the DSL emits, and the handler over it -/

#print axioms Effect4.ScopeFamily.Scopes
#print axioms Effect4.ScopeFamily.Scopes.rows
#print axioms Effect4.ScopeFamily.Scopes.encodeParam
#print axioms Effect4.ScopeFamily.Scopes.encodeAnswer
#print axioms Effect4.ScopeFamily.Scopes.traced
#print axioms Effect4.ScopeFamily.scopesLive
#print axioms Effect4.ScopeFamily.scopeGoldenLog
#print axioms Effect4.ScopeFamily.scopePrograms
