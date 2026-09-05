import Effect4.Program.Config

/-!
Fresh kernel dependency report for the configuration algebra
(`Effect4/Program/Config.lean`; plan `docs/research/2026-09-04-production-standards-spike.md`
§4 and §10).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound` or below; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
The two measured fences are recorded beside the theorems that met them: a `String`
traversal (`toNat?`, `toUpper`, `splitOn`, `toList`, `length`) reaches `Classical.choice`,
so the scalar codecs are a supplied `Scalars` hook; and `Row.diff_eq_empty_iff_subset`
instantiated at `Nat` reaches `Classical.choice` through core's order instances, so the
requirement row is `Row ServiceKey`.
-/

-- C1: providers, `load`, `mapInput`, `orElse`, `nested`.
#print axioms Effect4.Program.Config.load_source
#print axioms Effect4.Program.Config.load_make
#print axioms Effect4.Program.Config.load_orElse
#print axioms Effect4.Program.Config.orElse_assoc
#print axioms Effect4.Program.Config.orElse_empty_left
#print axioms Effect4.Program.Config.orElse_empty_right
#print axioms Effect4.Program.Config.orElse_idem
#print axioms Effect4.Program.Config.mapInput_mapInput
#print axioms Effect4.Program.Config.mapInput_id
#print axioms Effect4.Program.Config.mapInput_orElse
#print axioms Effect4.Program.Config.nested_nested
#print axioms Effect4.Program.Config.load_mapInput_fresh
#print axioms Effect4.Program.Config.load_nested_fresh
#print axioms Effect4.Program.Config.load_mapInput_orElse

-- C2: the reader and its combinators.
#print axioms Effect4.Program.Config.eval
#print axioms Effect4.Program.Config.eval_withDefault_absent
#print axioms Effect4.Program.Config.eval_withDefault_resolved
#print axioms Effect4.Program.Config.eval_orElse_absent
#print axioms Effect4.Program.Config.eval_orElse_failure
#print axioms Effect4.Program.Config.recover_no_input
#print axioms Effect4.Program.Config.eval_option_absent
#print axioms Effect4.Program.Config.eval_nested
#print axioms Effect4.Program.Config.eval_nested_transfer
#print axioms Effect4.Program.Config.eval_nested_eq_provider_nested

-- C3: string substitution with fuel.
#print axioms Effect4.Program.Config.expand
#print axioms Effect4.Program.Config.expand_lit
#print axioms Effect4.Program.Config.expand_ref_self_refused
#print axioms Effect4.Program.Config.expand_fuel_mono

-- C4: the configuration requirement row.
#print axioms Effect4.Program.Config.absent_names_missing
#print axioms Effect4.Program.Config.residual_empty_of_subset
#print axioms Effect4.Row.diff_eq_empty_iff_subset
