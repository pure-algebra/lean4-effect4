#!/usr/bin/env python3
"""Extract the actual private admission source into a finite Lean harness."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--label', required=True)
parser.add_argument('--policy', choices=['old', 'revised'], required=True)
parser.add_argument('--certificate', choices=['clean', 'mutant'], required=True)
args = parser.parse_args()
source = Path('Test/Audit/AxiomGate.lean').read_text()
if args.policy == 'old':
    import subprocess
    source = subprocess.check_output(['git', 'show', '8785c6f9:Test/Audit/AxiomGate.lean']).decode()

blocks = {
    'ceilings_and_admissions': source[source.index('private def allowedAxioms'):source.index('/-- Resolve each')],
    'ancestors': source[source.index('private def sameModuleAncestors'):source.index('private def belongsToAuditedTree')],
    'admitted': source[source.index('  let admitted (declaration : Name)'):source.index('  let t4 ←')],
    'bound_and_check': source[source.index('    let bound :='):source.index('  let t5 ←')],
}
manifest = {
    'source': 'Test/Audit/AxiomGate.lean',
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'blocks_sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k,v in blocks.items()},
    'policy': args.policy,
    'certificate': args.certificate,
    'adaptations': [
        'Copy top-level declarations and ancestor functions without changing their text.',
        'Indent local admitted and bound/check blocks inside a scoped CoreM reader.',
        'Use public exact admissions; private Config exemptions cannot admit an Explain name.',
        'Load a separately compiled Explain module with unchanged production source and an appended derived-certificate fixture.',
        'Change only the fixture Nat model value for the choice mutant.',
    ],
}
header = '''import Lean
import ProofGraph.Audit
import ProofGraph.Axioms
import ProofGraph.Goal
import Effect4
import Effect4.Laws.Author.Explain

/-! Finite source-extracted admission reader. Its JSON manifest pins every copied block.
This checks admission and axiom filtering only, not the full gate or module closure. -/

namespace ExplainAdmissionProbe
open Lean Elab Command
open ProofGraph.Audit (moduleOf?)

'''
check = '''
def checkDeclaration (environment : Environment) (declaration : Name) (axioms : Array Name) : CoreM Unit := do
  let exactImplementationDeclarations := choiceImplementationDeclarations
'''
check += blocks['admitted']
check += '''  let isGoal := ProofGraph.isGoal environment
'''
check += '\n'.join(line[2:] if line.startswith('  ') else line
                   for line in blocks['bound_and_check'].splitlines()) + '\n'
measurement = '''
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filterMap fun (n, _) =>
    if moduleOf? env n == some `Effect4.Laws.Author.Explain then some n else none).toArray
  let (reached, _) := ProofGraph.reachedAxiomsMany env names {}
  let mut choice : Array Name := #[]
  let mut certs : Array Name := #[]
  for (n, ax) in names.zip reached do
    let some ax := ax | throwError "measurement exhausted its budget at {n}"
    if ax.contains ``Classical.choice then choice := choice.push n
    if ["modeled_checked", "modeled_to_of", "modeled_of_to"].contains n.getString! then
      certs := certs.push n
    liftCoreM <| checkDeclaration env n ax
  logInfo m!"PASS every actual Explain declaration satisfies the extracted policy: {names.size} declarations"
  logInfo m!"MEASURE actual choice reachers: {choice.size}"
  for n in choice.qsort (fun a b => a.toString < b.toString) do logInfo m!"CHOICE {n}"
  let exact := choiceImplementationDeclarations.filter (`Tools.Explain).isPrefixOf
  logInfo m!"MEASURE exact Explain roots: {exact.length}"
  if !OLD_POLICY then
    unless exact.length == 24 do throwError "unexpected exact root count"
    for n in exact do
      let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
      unless (ax.getD #[]).contains ``Classical.choice do throwError "stale exact Explain root: {n}"
      if (env.find? n) matches some (.thmInfo _) then throwError "exact root admits a theorem: {n}"
    let inherited := choice.filter fun n => !exact.contains n
    logInfo m!"PASS {inherited.size} non-root reporting declarations use existing ancestor admissions"
  logInfo m!"MEASURE derived certificates: {certs.size}"
  unless certs.size == 12 do throwError "unexpected certificate count"
  for n in certs.qsort (fun a b => a.toString < b.toString) do
    let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
    logInfo m!"CERTIFICATE {n}: {ax}"
    let oldAllowed := (moduleOf? env n).any choiceImplementationModules.contains
    if oldAllowed != OLD_POLICY then throwError "unexpected certificate module admission"
  let reporter := ``Tools.Explain.render
  let (ax, _) := (ProofGraph.reachedAxioms env reporter).run {}
  unless (ax.getD #[]).contains ``Classical.choice do throwError "positive reporter uses no choice"
  liftCoreM <| checkDeclaration env reporter (ax.getD #[])
  logInfo "PASS positive reporting declaration remains admitted"

end ExplainAdmissionProbe

open Lean Elab Command in
run_cmd do
  let previous ← searchPathRef.get
  searchPathRef.set (System.FilePath.mk "FIXTURE_ROOT" :: previous)
  let env ← importModules #[{ module := `Effect4.Laws.Author.Explain }] (← getOptions)
  searchPathRef.set previous
  let n := `Tools.Explain.AdmissionControl.modeled_checked
  unless ProofGraph.Audit.moduleOf? env n == some `Effect4.Laws.Author.Explain do
    throwError "fixture certificate has the wrong module owner"
  let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
  let some ax := ax | throwError "fixture walk exhausted its budget"
  unless (ax.contains ``Classical.choice) == MUTANT do throwError "fixture has the wrong axiom set: {ax}"
  logInfo m!"FIXTURE {n}: {ax}"
  let refusal ← try
      liftCoreM <| ExplainAdmissionProbe.checkDeclaration env n ax
      pure none
    catch ex => pure (some ex.toMessageData)
  match refusal with
  | none =>
    if EXPECT_REFUSAL then throwError "certificate choice mutant escaped the policy"
    logInfo "PASS fixture certificate accepted"
  | some message =>
    unless EXPECT_REFUSAL do throwError "unexpected refusal: {message}"
    logInfo m!"PASS certificate choice mutant rejected by the extracted policy: {message}"
'''
measurement = measurement.replace('OLD_POLICY', 'true' if args.policy == 'old' else 'false')
measurement = measurement.replace('MUTANT', 'true' if args.certificate == 'mutant' else 'false')
measurement = measurement.replace('EXPECT_REFUSAL', 'true' if args.policy == 'revised' and args.certificate == 'mutant' else 'false')
model = 'Classical.choice (show Nonempty (Effect4.Schema.Modeled Nat) from ⟨inferInstance⟩)' if args.certificate == 'mutant' else 'inferInstance'
fixture_root = Path('docs/research/2026-10-08-explain-admission-probe-fixture-' + args.certificate)
fixture = fixture_root / 'Effect4/Laws/Author/Explain.lean'
fixture.parent.mkdir(parents=True, exist_ok=True)
# Lean chooses a search-path root by the leading module component.
# Link missing Effect4 siblings to the narrow build; preserve the fixture's own files.
def link_missing(built, destination):
    for item in built.iterdir():
        if destination.parts[-3:] == ('Effect4', 'Laws', 'Author') and item.name.startswith('Explain.'):
            continue
        target = destination / item.name
        if target.exists():
            if item.is_dir() and target.is_dir() and not target.is_symlink():
                link_missing(item, target)
        else:
            target.symlink_to(item.resolve(), target_is_directory=item.is_dir())
link_missing(Path('.lake/build/lib/lean/Effect4'), fixture_root / 'Effect4')
production = Path('src/Effect4/Laws/Author/Explain.lean').read_text()
fixture.write_text(production + """
namespace Tools.Explain
noncomputable section
@[instance_reducible] def probeNatModel : Effect4.Schema.Modeled Nat := MODEL_VALUE
local instance : Effect4.Schema.Modeled Nat := probeNatModel
structure AdmissionControl where
  count : Nat
  deriving Inhabited, Effect4.Schema.Modeled
end
end Tools.Explain
""".replace('MODEL_VALUE', model))
measurement = measurement.replace('FIXTURE_ROOT', str(fixture_root))
manifest['fixture_production_sha256'] = hashlib.sha256(production.encode()).hexdigest()
manifest['fixture_source_sha256'] = hashlib.sha256(fixture.read_bytes()).hexdigest()
root = Path('docs/research/2026-10-08-explain-admission-probe-' + args.label)
root.with_suffix('.lean').write_text(header + blocks['ceilings_and_admissions'] + blocks['ancestors'] + check + measurement)
root.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(root.with_suffix('.lean'))
print('extracted source SHA256', manifest['source_sha256'])
