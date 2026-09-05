import Effect4.Surface.Observability

/-!
Fresh kernel dependency report for the observability surface
(`Effect4/Surface/Observability.lean`; plan `docs/research/2026-09-04-production-standards-spike.md`
§3 rows 4–6, lane L5).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound`; the gate (`Test/Audit/AxiomGate.lean`)
enforces it, this file is the human-readable receipt. The five `String`-facing header parsers
(`parseHexId`, `w3c`, `b3`, `xb3`, `fromHeaders`) reach `Classical.choice` through
`String.toList`/`splitOn` and are pinned by exact name in the gate's choice list; the
structured codec and its round trip are not among them.
-/

-- O1: the records' injective codes.
#print axioms Effect4.Surface.Observability.spanKindCode_inj
#print axioms Effect4.Surface.Observability.statusCodeNumber_inj
#print axioms Effect4.Surface.Observability.logLevelOrdinal_inj

-- O2: the exporters' configuration row and its residual.
#print axioms Effect4.Surface.Observability.observabilityReads
#print axioms Effect4.Surface.Observability.required_nil_never_absent
#print axioms Effect4.Surface.Observability.observability_required
#print axioms Effect4.Surface.Observability.obsResidual_empty_of_subset
#print axioms Effect4.Surface.Observability.observability_absent_names_missing

-- O3: trace-context propagation, the structured codec.
#print axioms Effect4.Surface.Observability.encodeW3c
#print axioms Effect4.Surface.Observability.decodeW3c
#print axioms Effect4.Surface.Observability.decodeW3c_encodeW3c
#print axioms Effect4.Surface.Observability.encodeW3c_length
#print axioms Effect4.Surface.Observability.decodeW3c_version_ne
#print axioms Effect4.Surface.Observability.toHeaders
