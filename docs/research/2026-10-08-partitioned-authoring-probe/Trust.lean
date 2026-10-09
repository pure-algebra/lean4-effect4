import docs.research.«2026-10-08-partitioned-authoring-probe».Probe
import ProofGraph.Audit
import ProofGraph.Axioms

/-! Research-only scoped audit. This file does not run the whole-library gate.
It checks every saved probe declaration, including deriving-generated declarations.
The audit reuses the whole-library gate's declaration facts and dependency walker. -/

#print axioms Research.PartitionedAuthoring.Model.Counts.modeled_checked
#print axioms Research.PartitionedAuthoring.Model.Counts.modeled_to_of
#print axioms Research.PartitionedAuthoring.Model.Counts.modeled_of_to
#print axioms Research.PartitionedAuthoring.initial_eval
#print axioms Research.PartitionedAuthoring.available_eval
#print axioms Research.PartitionedAuthoring.tryTake_eval
#print axioms Research.PartitionedAuthoring.reserve_eval
#print axioms Research.PartitionedAuthoring.initial_reads
#print axioms Research.PartitionedAuthoring.available_reads
#print axioms Research.PartitionedAuthoring.tryTake_reads
#print axioms Research.PartitionedAuthoring.reserve_reads
#print axioms Research.PartitionedAuthoring.initial_types
#print axioms Research.PartitionedAuthoring.available_types
#print axioms Research.PartitionedAuthoring.tryTake_types
#print axioms Research.PartitionedAuthoring.reserve_types

open Lean Elab Command in
elab "#probe_trust" : command => do
  let env ← getEnv
  if env.header.isModule then throwError "Scoped audit requires a non-module root"
  let targets := #[`docs.research.«2026-10-08-partitioned-authoring-probe».Model,
    `docs.research.«2026-10-08-partitioned-authoring-probe».Probe]
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env targets.contains
  unless missing.isEmpty do throwError "Missing declarations: {missing}"
  if facts.isEmpty then throwError "Probe module audit is empty"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "Disallowed declaration shape: {fact.name}"
  let (reached, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let allow := #[``propext, ``Quot.sound]
  let mut seen : Array Name := #[]
  for (fact, result) in facts.zip reached do
    let some axioms := result | throwError "Unfinished axiom walk: {fact.name}"
    for dependency in axioms do
      unless allow.contains dependency do throwError "Disallowed axiom {dependency} in {fact.name}"
      unless seen.contains dependency do seen := seen.push dependency
  logInfo m!"Scoped probe audit: {facts.size} declarations; reached axioms {seen}; allowlist {allow}"

#probe_trust
