import Test.Audit.Explain
import Test.Program.LatchRegistration
import Test.Program.LatchSteps
import Test.Program.PoolData
import Test.Program.PoolSteps
import Test.Program.QueueData
import Test.Program.QueueSteps
import Test.Program.SemaphoreData
import Test.Program.SemaphoreSteps
import Test.Program.StepConstruction
import Test.Program.StepConstructors
import Test.Program.StepFolds
import Test.Program.StepInputs
import Test.Program.StepLanguage
import Test.Program.StepLists
import Test.Program.StepTuples
import Test.Schema.Identity
import Test.Schema.Modeled
import Effect4
import Effect4.Laws
import Effect4.Laws.Modules.Cons
import Effect4.Laws.Modules.Construction
import Effect4.Laws.Modules.Latch.Model
import Effect4.Laws.Modules.Latch.Registration
import Effect4.Laws.Modules.Latch.Steps
import Effect4.Laws.Modules.Option
import Effect4.Laws.Modules.Pool.Data
import Effect4.Laws.Modules.Pool.Ops
import Effect4.Laws.Modules.Pool.Passes
import Effect4.Laws.Modules.Pool.Reading
import Effect4.Laws.Modules.Pool.Steps
import Effect4.Laws.Modules.Pool.Typing
import Effect4.Laws.Modules.Queue.Data
import Effect4.Laws.Modules.Queue.OfferData
import Effect4.Laws.Modules.Queue.Ops
import Effect4.Laws.Modules.Queue.Passes
import Effect4.Laws.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Typing
import Effect4.Laws.Modules.Semaphore.Data
import Effect4.Laws.Modules.Semaphore.Ops
import Effect4.Laws.Modules.Semaphore.Steps
import Effect4.Laws.Modules.Semaphore.Typing
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Step.Annotations
import Effect4.Laws.Modules.Step.ErasedCompiler
import Effect4.Laws.Modules.Step.Lists
import Effect4.Laws.Modules.Step.Rename
import Effect4.Laws.Modules.Step.Requirements
import Effect4.Laws.Modules.Step.Scope
import Effect4.Laws.Modules.Tuples
import Effect4.Laws.Schema.Identity
import Effect4.Modules.Latch.Registration
import Effect4.Modules.Latch.Steps
import Effect4.Modules.Pool.Cell
import Effect4.Modules.Pool.Data
import Effect4.Modules.Pool.Passes
import Effect4.Modules.Pool.Steps
import Effect4.Modules.Queue.Cell
import Effect4.Modules.Queue.Data
import Effect4.Modules.Queue.Steps
import Effect4.Modules.Semaphore.Cell
import Effect4.Modules.Semaphore.Data
import Effect4.Modules.Semaphore.Steps
import Effect4.Modules.Step
import Effect4.Modules.Step.Inputs
import Effect4.Modules.Step.Lists
import Effect4.Modules.Step.Rename
import Effect4.Schema.Identity
import Effect4.Schema.Modeled
import Effect4.Store.Carrier.Image.Containers
import ProofGraph.Audit
import ProofGraph.Axioms

/-! Targeted trust audit for the module foundation.
The selected sources changed from integration base 1253079c.
Root closure and elaborator metadata use separate checks. No full battery runs here. -/

open Lean
set_option maxHeartbeats 4000000
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[
    `Test.Audit.Explain,
    `Test.Program.LatchRegistration,
    `Test.Program.LatchSteps,
    `Test.Program.PoolData,
    `Test.Program.PoolSteps,
    `Test.Program.QueueData,
    `Test.Program.QueueSteps,
    `Test.Program.SemaphoreData,
    `Test.Program.SemaphoreSteps,
    `Test.Program.StepConstruction,
    `Test.Program.StepConstructors,
    `Test.Program.StepFolds,
    `Test.Program.StepInputs,
    `Test.Program.StepLanguage,
    `Test.Program.StepLists,
    `Test.Program.StepTuples,
    `Test.Schema.Identity,
    `Test.Schema.Modeled,
    `Effect4,
    `Effect4.Laws,
    `Effect4.Laws.Modules.Cons,
    `Effect4.Laws.Modules.Construction,
    `Effect4.Laws.Modules.Latch.Model,
    `Effect4.Laws.Modules.Latch.Registration,
    `Effect4.Laws.Modules.Latch.Steps,
    `Effect4.Laws.Modules.Option,
    `Effect4.Laws.Modules.Pool.Data,
    `Effect4.Laws.Modules.Pool.Ops,
    `Effect4.Laws.Modules.Pool.Passes,
    `Effect4.Laws.Modules.Pool.Reading,
    `Effect4.Laws.Modules.Pool.Steps,
    `Effect4.Laws.Modules.Pool.Typing,
    `Effect4.Laws.Modules.Queue.Data,
    `Effect4.Laws.Modules.Queue.OfferData,
    `Effect4.Laws.Modules.Queue.Ops,
    `Effect4.Laws.Modules.Queue.Passes,
    `Effect4.Laws.Modules.Queue.Steps,
    `Effect4.Laws.Modules.Queue.Typing,
    `Effect4.Laws.Modules.Semaphore.Data,
    `Effect4.Laws.Modules.Semaphore.Ops,
    `Effect4.Laws.Modules.Semaphore.Steps,
    `Effect4.Laws.Modules.Semaphore.Typing,
    `Effect4.Laws.Modules.Step,
    `Effect4.Laws.Modules.Step.Annotations,
    `Effect4.Laws.Modules.Step.ErasedCompiler,
    `Effect4.Laws.Modules.Step.Lists,
    `Effect4.Laws.Modules.Step.Rename,
    `Effect4.Laws.Modules.Step.Requirements,
    `Effect4.Laws.Modules.Step.Scope,
    `Effect4.Laws.Modules.Tuples,
    `Effect4.Laws.Schema.Identity,
    `Effect4.Modules.Latch.Registration,
    `Effect4.Modules.Latch.Steps,
    `Effect4.Modules.Pool.Cell,
    `Effect4.Modules.Pool.Data,
    `Effect4.Modules.Pool.Passes,
    `Effect4.Modules.Pool.Steps,
    `Effect4.Modules.Queue.Cell,
    `Effect4.Modules.Queue.Data,
    `Effect4.Modules.Queue.Steps,
    `Effect4.Modules.Semaphore.Cell,
    `Effect4.Modules.Semaphore.Data,
    `Effect4.Modules.Semaphore.Steps,
    `Effect4.Modules.Step,
    `Effect4.Modules.Step.Inputs,
    `Effect4.Modules.Step.Lists,
    `Effect4.Modules.Step.Rename,
    `Effect4.Schema.Identity,
    `Effect4.Schema.Modeled,
    `Effect4.Store.Carrier.Image.Containers]
  for module in selected do
    unless env.header.moduleNames.contains module do throwError "selected module not loaded: {module}"
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env selected.contains
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  let facts := facts.filter (fun fact => !fact.safeRecursor)
  let (reached, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let mut failures : Array String := #[]
  for (fact, result) in facts.zip reached do
    let some axioms := result | throwError "axiom traversal exhausted at {fact.name}"
    let extra := axioms.filter (fun name => name != ``propext && name != ``Quot.sound)
    unless extra.isEmpty do failures := failures.push s!"unapproved axioms at {fact.name}: {extra}"
    if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern || fact.implementedBy || fact.bodilessOpaque then
      failures := failures.push s!"unapproved declaration form at {fact.name}"
  unless failures.isEmpty do throwError "{String.intercalate "\n" failures.toList}"
  logInfo m!"checked {facts.size} declarations in {selected.size} changed modules; only permitted proof dependencies"
