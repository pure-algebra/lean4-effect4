import Test.Dogfood.Scenario
import ProofGraph.Plan
import ProofGraph.Registry

/-!
# The scenario gate: a scenario's record checked against the proof graph

`#scenario_gate` and `#scenario_reach`, at the foot of a scenario battery, check each record of
`Test/Dogfood/Scenario.lean` against the environment, the `@[semantics]` placements, the semantics
registry (`tools/ProofGraph/Registry.lean`) and the planning graph (`tools/ProofGraph/Plan.lean`).
They read tools, so they stand here and not in the scenarios' shared driver, which imports entry
modules only (decisions row 332, cutover slice C4). The declarations keep their namespace.
-/

namespace Test.Dogfood.Scenario

/-- Whether the semantics registry (`tools/ProofGraph/Registry.lean`) places a declaration of
a module. A requirement lists it as a top node, or a registry claim points at it, or its module
is a default module of a concept: an untagged theorem of that module inherits the concept. -/
def registered (name module : Lean.Name) : Bool :=
  let registry := Tools.Semantics.registry
  registry.requirements.any (·.top.contains name) ||
    registry.claims.any (fun claim =>
      match claim.pointer with
      | .witness witness => witness == name
      | .refutedBy _ witness => witness == name
      | _ => false) ||
    registry.concepts.any (·.defaultModules.contains module)

/-- `#scenario_gate S₁ … Sₙ`, at the foot of a battery, checks each scenario's record against the
environment. It plays each named run once and judges each control on the runs that the control
reads. It fails, naming every finding, when:

* the program or the observation does not resolve to a declaration;
* the claim, a clause's claim or a law's claim does not resolve to a theorem or a planned goal;
* such a claim has no placement. A declaration of a battery carries its own at a requirement
  (`@[semantics "concept" (requirement := Rn)]`, decisions row 207). Any other declaration
  carries `@[semantics …]`, or the semantics registry places it (`registered`);
* the claim's proof does not reach an assembled clause. The measure is the planning graph
  (`ProofGraph.buildPlan`, `tools/ProofGraph/Plan.lean`) over the placed claims and their placed
  clauses. A planned goal is reached when the claim rests on it (`Node.restsOn`). A theorem is
  reached when the walk from the claim's proof reaches it through the batteries' declarations
  (`Node.nearest`);
* the claim rests on a planned goal that no clause names;
* a clause or a law has no green control, or no red control (`Scenario.problems`);
* the record lists one run's name twice (`Scenario.problems`);
* no control reads a named run of the record (`Scenario.unread`, `Scenario.problems`);
* a control names no clause and no law of its scenario, reads a run that the record does not
  list, or fails (`Scenario.problems`).

An associated law gets no dependency check: the record claims none. A claim with no placement
stays out of the plan, and the gate measures no dependency of it or on it. The plan refuses a
node above the semantic axiom ceiling by an error of its own, which fails the command
(`Test/Audit/ProofGraphPlan.lean` holds that control). The command builds one plan, with an axiom
memo of its own. It expands to one `run_cmd`, which leaves no declaration. The check reads the
environment, and no reader of the environment stays under the axiom ceiling
(`Test/Audit/AxiomGate.lean`). -/
syntax (name := scenarioGate) "#scenario_gate " ident+ : command

/-- `#scenario_reach S₁ … Sₙ` runs the checks of `#scenario_gate` on the declarations, the
placements and the dependencies, and not the checks of each record as data
(`Scenario.problems`): it plays no run. A red control of the dependency check reads a record
whose runs and controls a green `#scenario_gate` has already judged. -/
syntax (name := scenarioReach) "#scenario_reach " ident+ : command

open Lean in
/-- The expansion of both commands: `records` adds the checks of each record as data. -/
def scenarioGateExpansion (scenarios : Array (TSyntax `term)) (records : Bool) :
    MacroM (TSyntax `command) :=
  `(run_cmd Lean.Elab.Command.liftTermElabM do
      let env ← Lean.getEnv
      let scenarios : List Test.Dogfood.Scenario.Scenario := [$scenarios,*]
      let unplaced := fun (name : Lean.Name) =>
        let module := Effect4.Laws.Auto.semanticsModule env name
        let tag := Effect4.Laws.Auto.semanticsAttribute.getParam? env name
        if !((env.find? name) matches some (.thmInfo _)) then
          some s!"the claim {name} is no theorem and no planned goal"
        else if (`Test).isPrefixOf module then
          if (tag.bind (·.requirement)).isSome then none
          else some s!"the claim {name} has no placement at a requirement"
        else if tag.isSome || Test.Dogfood.Scenario.registered name module then none
        else some s!"the claim {name} has no placement: no semantics attribute and no row of the semantics registry"
      let placed := fun (name : Lean.Name) => (unplaced name).isNone
      let nodes := (scenarios.flatMap fun scenario =>
        if placed scenario.claim then
          scenario.claim :: (scenario.clauses.map (·.claim)).filter placed
        else []).eraseDups
      let plan ← if nodes.isEmpty then pure { nodes := #[] }
        else ProofGraph.buildPlan [`Test] nodes.toArray (← IO.mkRef {})
      let mut findings : Array String := #[]
      for scenario in scenarios do
        for name in scenario.declarations do
          unless env.contains name do
            findings := findings.push s!"{scenario.name}: {name} does not resolve to a declaration"
        for name in scenario.claims do
          if let some finding := unplaced name then
            findings := findings.push s!"{scenario.name}: {finding}"
        if placed scenario.claim then
          let mut reached : Array Lean.Name := #[scenario.claim]
          for _ in plan.nodes do
            for node in plan.nodes do
              if reached.contains node.name then
                for next in node.nearest ++ node.restsOn do
                  unless reached.contains next do reached := reached.push next
          for clause in scenario.clauses do
            if placed clause.claim && !reached.contains clause.claim then
              findings := findings.push
                s!"{scenario.name}: the proof of {scenario.claim} does not reach the clause \"{clause.name}\" ({clause.claim})"
          for goal in ((plan.find? scenario.claim).map (·.restsOn)).getD #[] do
            unless scenario.clauses.any (·.claim == goal) do
              findings := findings.push
                s!"{scenario.name}: the claim {scenario.claim} rests on the planned goal {goal}, which no clause names"
        if $(quote records) then findings := findings ++ scenario.problems.toArray
      unless findings.isEmpty do
        throwError (String.intercalate "\n" findings.toList))

open Lean in
@[macro scenarioGate] def expandScenarioGate : Macro := fun stx =>
  scenarioGateExpansion (stx[1].getArgs.map (⟨·⟩)) true

open Lean in
@[macro scenarioReach] def expandScenarioReach : Macro := fun stx =>
  scenarioGateExpansion (stx[1].getArgs.map (⟨·⟩)) false

end Test.Dogfood.Scenario
