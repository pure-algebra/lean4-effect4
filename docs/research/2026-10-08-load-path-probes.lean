import Tools.LoadPaths

/-!
Finite controls for Tools.LoadPaths at 01c83fbc.

These are metaprogram behavior controls, not Effect4 semantic claims.
Placement: tooling evidence; consumer: the checks below and the audit receipt.
Reach: the loaded fixture and directTheorems/buildGraph/measure only.
Exclusion: no admission, semantic, host, or deletion claim follows.
Requirement served: measured evidence for the existing proof-graph reports.
No production theorem or registry entry changes.
-/
namespace LoadPathProbe
open Lean Elab Command Tools.LoadPaths

/-- An authored theorem with a generated-looking name tests the population filter. -/
theorem instSizeOfControl : True := True.intro

/-- Positive control: a proof named directly remains visible. -/
theorem directSeed : True := True.intro

theorem directConsumer : True := directSeed

/-- Negative control: the same proof hidden behind an authored definition. -/
theorem wrappedSeed : True := True.intro

def proofWrapper : PLift True := ⟨wrappedSeed⟩

theorem wrappedConsumer : True := proofWrapper.down

/-- Type dependency control: the statement names this seed, while the proof does not. -/
theorem typeSeed : True := True.intro

def indexedStatement (_ : True) : Prop := True

theorem typeConsumer : indexedStatement typeSeed := True.intro

/-- An ordinary type-class instance also carries proof data. -/
theorem instanceSeed : True := True.intro

class HasEvidence : Type where
  evidence : True

instance : HasEvidence := ⟨instanceSeed⟩

theorem instanceConsumer : True := HasEvidence.evidence

/-- A root uses a theorem from Lean's library. -/
theorem coreConsumer : 0 < 1 := Nat.zero_lt_succ 0

run_cmd do
  for n in [``directSeed, ``directConsumer, ``wrappedSeed, ``wrappedConsumer,
      ``typeSeed, ``typeConsumer, ``instanceSeed, ``instanceConsumer,
      ``coreConsumer, ``instSizeOfControl] do
    let axioms ← Lean.collectAxioms n
    unless axioms.isEmpty do throwError "probe declaration {n} depends on {axioms}"
  logInfo "PASS first ten fixture theorem declarations have empty axiom sets"
  let original ← getEnv
  -- Report source-module identity without adding an import or production module.
  let env := original.setMainModule `Tools.LoadPathsProbe
  unless (env.find? ``instSizeOfControl matches some (.thmInfo _)) do
    throwError "authored naming control is not a theorem"
  unless authoredTheorem env ``instSizeOfControl == false do
    throwError "generated-name prefix no longer excludes authored theorem"
  logInfo "PASS authored instSizeOfControl theorem excluded by generated-name spelling"
  let direct := directTheorems env ``directConsumer
  let wrapped := directTheorems env ``wrappedConsumer
  let typeOnly := directTheorems env ``typeConsumer
  unless direct.any (·.contains ``directSeed) do
    throwError "positive control lost the direct theorem"
  unless wrapped.any (·.contains ``wrappedSeed) == false do
    throwError "ordinary proof wrapper no longer hides seed; expected finding has changed"
  let some wrapper := env.find? ``proofWrapper | throwError "missing wrapper"
  unless wrapper.value?.any (·.getUsedConstants.contains ``wrappedSeed) do
    throwError "wrapper does not actually depend on seed"
  let some consumer := env.find? ``typeConsumer | throwError "missing type consumer"
  unless consumer.type.getUsedConstants.contains ``typeSeed do
    throwError "type consumer statement does not depend on seed"
  unless typeOnly.any (·.contains ``typeSeed) == false do
    throwError "type-only seed unexpectedly visible; expected finding has changed"
  unless env.isProjectionFn ``HasEvidence.evidence do
    throwError "expected generated structure projection"
  unless authoredTheorem env ``HasEvidence.evidence do
    throwError "generated proof-field projection no longer counted as authored"
  logInfo "PASS generated proof-field projection counted as authored theorem"
  let g := buildGraph env
  let rs := #[``directConsumer, ``wrappedConsumer, ``typeConsumer, ``instanceConsumer, ``coreConsumer]
  let load := loadBearing g rs
  unless load.contains ``directSeed do throwError "positive root lost direct seed"
  unless load.contains ``wrappedSeed == false do throwError "wrapped root unexpectedly reaches seed"
  unless load.contains ``typeSeed == false do throwError "type root unexpectedly reaches seed"
  let instanceDeps := directTheorems env ``instanceConsumer
  unless Meta.isInstanceCore env ``instHasEvidence do
    throwError "control instance not registered"
  let some instanceInfo := env.find? ``instHasEvidence | throwError "missing instance"
  unless (instanceInfo.value? (allowOpaque := true)).any (·.getUsedConstants.contains ``instanceSeed) do
    throwError "instance does not actually depend on seed"
  let some instanceUse := env.find? ``instanceConsumer | throwError "missing instance consumer"
  unless (instanceUse.value? (allowOpaque := true)).any (·.getUsedConstants.contains ``instHasEvidence) do
    throwError "consumer does not actually name the instance"
  unless instanceDeps.any (·.contains ``instanceSeed) == false do
    throwError "instance's seed unexpectedly visible; expected finding has changed"
  let graphLoadCount := load.toArray.filter (g.deps.contains ·) |>.size
  unless load.size > graphLoadCount do
    throwError "external root endpoint no longer inflates header count"
  logInfo s!"PASS header count includes nonmembers: {load.size} reached names, {graphLoadCount} graph members"
  let report := measure env g rs load [`Tools.LoadPathsProbe]
  unless report.unconsumed.contains ``wrappedSeed do
    throwError "expected unconsumed label on wrapper's actual seed"
  unless report.unconsumed.contains ``typeSeed do
    throwError "expected unconsumed label on statement's actual seed"
  unless report.instances == 0 do
    throwError "ordinary def instance unexpectedly counted"
  unless report.unconsumed.contains ``instanceSeed do
    throwError "instance's actual seed unexpectedly consumed"
  logInfo s!"PASS actual class-instance consumer hidden: {instanceDeps}; instance edges {report.instances}"
  logInfo s!"PASS direct theorem visible: {direct}"
  logInfo s!"PASS authored proof wrapper hides dependency: {wrapped}"
  logInfo s!"PASS statement-only dependency hidden: {typeOnly}"
  logInfo "PASS wrapped/type seeds labelled unconsumed despite actual consumers"
  let claimed := Tools.Semantics.registry.claims.filterMap fun cl =>
    match cl.pointer with
    | .witness n | .refutedBy _ n => some n
    | _ => none
  let registered := claimed ++ Tools.Semantics.registry.requirements.flatMap (·.top)
  let missing := registered.filter (!env.contains ·)
  unless !missing.isEmpty do throwError "minimal fixture unexpectedly resolves all roots"
  logInfo s!"PASS missing registry names are silently omitted: {missing.length} names, {roots env |>.size} retained roots"

/-- Restoration names the existing seed directly, after the negative checks. -/
theorem wrappedRestored : True := wrappedSeed

run_cmd do
  let axioms ← Lean.collectAxioms ``wrappedRestored
  unless axioms.isEmpty do throwError "restoration depends on {axioms}"
  let env := (← getEnv).setMainModule `Tools.LoadPathsProbe
  let restored := directTheorems env ``wrappedRestored
  unless restored.any (·.contains ``wrappedSeed) do
    throwError "restored direct proof does not reveal seed"
  let g := buildGraph env
  unless (g.usedBy.getD ``wrappedSeed #[]).contains ``wrappedRestored do
    throwError "rebuilt graph does not record restored consumer"
  let rs := #[``wrappedRestored]
  let load := loadBearing g rs
  unless load.contains ``wrappedSeed do throwError "restored root does not reach seed"
  let report := measure env g rs load [`Tools.LoadPathsProbe]
  unless report.unconsumed.contains ``wrappedSeed == false do
    throwError "restored actual graph still labels seed unconsumed"
  logInfo s!"PASS direct restoration reveals dependency: {restored}"
  logInfo "PASS rebuilt actual graph counts restored seed as consumed and load-bearing"
  logInfo "PASS restoration theorem has empty axiom set"

end LoadPathProbe
